import * as THREE from 'three';
import { lv95ToWgs84, convexHullLv95ToWgs84 } from './geo.js';

const WASM_PATH = 'https://cdn.jsdelivr.net/npm/web-ifc@0.0.51/';

let _ifcApi = null;

async function getApi() {
  if (_ifcApi) return _ifcApi;
  const { IfcAPI } = await import('https://esm.sh/web-ifc@0.0.51');
  const api = new IfcAPI();
  api.SetWasmPath(WASM_PATH);
  await api.Init();
  _ifcApi = api;
  return api;
}

// Parse IFCMAPCONVERSION to get LV95 georeferencing offset
function parseMapConversion(api, modelId) {
  try {
    const ids = api.GetLineIDsWithType(modelId, api.IFCMAPCONVERSION);
    if (!ids || ids.size() === 0) return null;
    const line = api.GetLine(modelId, ids.get(0));
    return {
      eastings: line.Eastings?.value ?? 0,
      northings: line.Northings?.value ?? 0,
      height: line.OrthogonalHeight?.value ?? 0,
      xAxisAbscissa: line.XAxisAbscissa?.value ?? 1,
      xAxisOrdinate: line.XAxisOrdinate?.value ?? 0,
    };
  } catch {
    return null;
  }
}

// Load IFC file, return meshes for Three.js and georef info
export async function loadIfc(buffer, onProgress) {
  const api = await getApi();

  const bytes = new Uint8Array(buffer);
  const modelId = api.OpenModel(bytes, {
    COORDINATE_TO_ORIGIN: false,
    USE_FAST_BOOLS: true,
  });

  const mapConversion = parseMapConversion(api, modelId);

  const meshes = [];
  let processed = 0;

  // Single pass – progress based on byte offset approximation
  api.StreamAllMeshes(modelId, (flatMesh) => {
    processed++;
    if (onProgress) onProgress(Math.min(processed / 200, 0.99));

    for (let i = 0; i < flatMesh.geometries.size(); i++) {
      const placedGeom = flatMesh.geometries.get(i);
      const geom = api.GetGeometry(modelId, placedGeom.geometryExpressID);

      const verts = api.GetVertices(geom);
      const idxs = api.GetIndices(geom);

      if (!verts || !idxs || verts.length === 0 || idxs.length === 0) continue;

      // Each vertex has 6 floats: x,y,z, nx,ny,nz
      const positions = new Float32Array(idxs.length * 3);
      const normals = new Float32Array(idxs.length * 3);

      for (let j = 0; j < idxs.length; j++) {
        const vIdx = idxs[j] * 6;
        positions[j * 3]     = verts[vIdx];
        positions[j * 3 + 1] = verts[vIdx + 1];
        positions[j * 3 + 2] = verts[vIdx + 2];
        normals[j * 3]       = verts[vIdx + 3];
        normals[j * 3 + 1]   = verts[vIdx + 4];
        normals[j * 3 + 2]   = verts[vIdx + 5];
      }

      const bufGeo = new THREE.BufferGeometry();
      bufGeo.setAttribute('position', new THREE.BufferAttribute(positions, 3));
      bufGeo.setAttribute('normal', new THREE.BufferAttribute(normals, 3));

      // Apply placement transform (column-major 4x4)
      const t = placedGeom.flatTransformation;
      const mat4 = new THREE.Matrix4().set(
        t[0],  t[4],  t[8],  t[12],
        t[1],  t[5],  t[9],  t[13],
        t[2],  t[6],  t[10], t[14],
        t[3],  t[7],  t[11], t[15]
      );
      bufGeo.applyMatrix4(mat4);

      const { r, g, b } = placedGeom.color;
      meshes.push({ geometry: bufGeo, color: new THREE.Color(r, g, b) });

      api.FreeGeometry(geom);
    }
  });

  api.CloseModel(modelId);

  return { meshes, mapConversion };
}

// Convert IFC meshes into scene coordinates.
// mapConversion: { eastings, northings, xAxisAbscissa, xAxisOrdinate }
// originE, originN: scene origin in LV95
// Returns array of { geometry (transformed), color }
export function transformIfcToScene(meshes, mapConversion, originE, originN) {
  const east = mapConversion?.eastings ?? originE;
  const north = mapConversion?.northings ?? originN;
  const ax = mapConversion?.xAxisAbscissa ?? 1;
  const ay = mapConversion?.xAxisOrdinate ?? 0;

  // Rotation angle from LV95 X-axis
  const angle = Math.atan2(ay, ax);

  // Build transform: IFC local → scene XZ
  // scene X = (ifc_X * cos(a) - ifc_Y * sin(a)) + (east - originE)
  // scene Z = -(ifc_X * sin(a) + ifc_Y * cos(a)) - (north - originN)  [Z = -North]
  // scene Y = ifc_Z (elevation)
  const dE = east - originE;
  const dN = -(north - originN); // negative because scene Z = -LV95_North

  const result = [];
  for (const { geometry, color } of meshes) {
    const pos = geometry.attributes.position;
    const newPos = new Float32Array(pos.count * 3);

    for (let i = 0; i < pos.count; i++) {
      const ix = pos.getX(i);
      const iy = pos.getY(i);
      const iz = pos.getZ(i);

      // IFC Y-up: X=East, Y=North, Z=up → scene X=East, Y=up, Z=-North
      const sx = ix * Math.cos(angle) - iy * Math.sin(angle) + dE;
      const sy = iz; // IFC Z = elevation = scene Y
      const sz = -(ix * Math.sin(angle) + iy * Math.cos(angle)) + dN;

      newPos[i * 3]     = sx;
      newPos[i * 3 + 1] = sy;
      newPos[i * 3 + 2] = sz;
    }

    const geo = new THREE.BufferGeometry();
    geo.setAttribute('position', new THREE.BufferAttribute(newPos, 3));
    if (geometry.attributes.normal) {
      geo.setAttribute('normal', geometry.attributes.normal.clone());
    }
    result.push({ geometry: geo, color });
  }

  return result;
}

// Extract building footprint (ground level points) as LV95 coordinates
// Returns a GeoJSON Feature<Polygon> or null
export function extractFootprintWgs84(meshes, mapConversion, originE, originN) {
  const east = mapConversion?.eastings ?? originE;
  const north = mapConversion?.northings ?? originN;
  const ax = mapConversion?.xAxisAbscissa ?? 1;
  const ay = mapConversion?.xAxisOrdinate ?? 0;
  const angle = Math.atan2(ay, ax);

  const lv95Pts = [];

  for (const { geometry } of meshes) {
    const pos = geometry.attributes.position;
    for (let i = 0; i < pos.count; i++) {
      const ix = pos.getX(i), iy = pos.getY(i);
      const e = ix * Math.cos(angle) - iy * Math.sin(angle) + east;
      const n = ix * Math.sin(angle) + iy * Math.cos(angle) + north;
      lv95Pts.push([e, n]);
    }
  }

  if (lv95Pts.length < 3) return null;
  return convexHullLv95ToWgs84(lv95Pts, lv95ToWgs84);
}
