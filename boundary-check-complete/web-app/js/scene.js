import * as THREE from 'three';
import { OrbitControls } from 'three/addons/controls/OrbitControls.js';
import { ringToScene } from './geo.js';

const MAT = {
  parcel:    new THREE.MeshLambertMaterial({ color: 0x22c55e, transparent: true, opacity: .85, side: THREE.DoubleSide }),
  parcelEdge:new THREE.LineBasicMaterial({ color: 0x4ade80, linewidth: 2 }),
  neighbor:  new THREE.MeshLambertMaterial({ color: 0x3b82f6, transparent: true, opacity: .4, side: THREE.DoubleSide }),
  neighborEdge: new THREE.LineBasicMaterial({ color: 0x60a5fa }),
  gross:     new THREE.MeshLambertMaterial({ color: 0xf59e0b, transparent: true, opacity: .22, side: THREE.DoubleSide }),
  klein:     new THREE.MeshLambertMaterial({ color: 0xef4444, transparent: true, opacity: .18, side: THREE.DoubleSide }),
  violation: new THREE.MeshLambertMaterial({ color: 0xef4444, transparent: true, opacity: .7, side: THREE.DoubleSide }),
  building:  new THREE.MeshLambertMaterial({ color: 0xe2e8f0, transparent: true, opacity: .9, side: THREE.DoubleSide }),
  ground:    new THREE.MeshLambertMaterial({ color: 0x1e2a38 }),
};

function makeShape(xzPairs) {
  const shape = new THREE.Shape();
  shape.moveTo(xzPairs[0][0], xzPairs[0][1]);
  for (let i = 1; i < xzPairs.length; i++) shape.lineTo(xzPairs[i][0], xzPairs[i][1]);
  shape.closePath();
  return shape;
}

function extrudeMesh(shape, mat, depth = 0.15) {
  const geo = new THREE.ExtrudeGeometry(shape, { depth, bevelEnabled: false });
  const mesh = new THREE.Mesh(geo, mat);
  // Shape is in XY plane; rotate -90° around X so it lies flat in XZ (ground plane)
  mesh.rotation.x = -Math.PI / 2;
  return mesh;
}

function shapeEdge(xzPairs) {
  const pts = xzPairs.map(([x, z]) => new THREE.Vector3(x, 0.3, z));
  pts.push(pts[0]);
  return new THREE.BufferGeometry().setFromPoints(pts);
}

export class Scene3D {
  constructor(canvas) {
    this.canvas = canvas;
    this.originE = 0;
    this.originN = 0;
    this.wireframe = false;
    this._parcelBounds = null; // {minX, maxX, minZ, maxZ}

    this._setupRenderer();
    this._setupScene();
    this._setupCamera();
    this._setupLights();
    this._setupGround();
    this._setupControls();
    this._animate();

    window.addEventListener('resize', () => this.resize());
  }

  _setupRenderer() {
    this.renderer = new THREE.WebGLRenderer({ canvas: this.canvas, antialias: true, alpha: false, preserveDrawingBuffer: true });
    this.renderer.setPixelRatio(Math.min(window.devicePixelRatio, 2));
    this.renderer.shadowMap.enabled = true;
    this.renderer.shadowMap.type = THREE.PCFSoftShadowMap;
    this.renderer.setClearColor(0x0d1117);
    this.resize();
  }

  _setupScene() {
    this.scene = new THREE.Scene();
    this.scene.fog = new THREE.Fog(0x0d1117, 800, 2000);
    this.groups = {
      parcel:    new THREE.Group(),
      neighbors: new THREE.Group(),
      zones:     new THREE.Group(),
      building:  new THREE.Group(),
      violations:new THREE.Group(),
    };
    Object.values(this.groups).forEach(g => this.scene.add(g));
  }

  _setupCamera() {
    const w = this.canvas.clientWidth, h = this.canvas.clientHeight;
    this.camera = new THREE.PerspectiveCamera(45, w / h, 0.1, 5000);
    this.camera.position.set(0, 150, 200);
    this.camera.lookAt(0, 0, 0);
  }

  _setupLights() {
    this.scene.add(new THREE.AmbientLight(0xffffff, 0.6));
    const sun = new THREE.DirectionalLight(0xfff5e0, 1.0);
    sun.position.set(200, 400, 100);
    sun.castShadow = true;
    sun.shadow.mapSize.set(2048, 2048);
    sun.shadow.camera.near = 1;
    sun.shadow.camera.far = 2000;
    sun.shadow.camera.left = -500;
    sun.shadow.camera.right = 500;
    sun.shadow.camera.top = 500;
    sun.shadow.camera.bottom = -500;
    this.scene.add(sun);
    this.scene.add(new THREE.HemisphereLight(0x87ceeb, 0x334155, 0.4));
  }

  _setupGround() {
    const geo = new THREE.PlaneGeometry(2000, 2000);
    const mesh = new THREE.Mesh(geo, MAT.ground);
    mesh.rotation.x = -Math.PI / 2;
    mesh.receiveShadow = true;
    this.scene.add(mesh);

    // Grid helper
    const grid = new THREE.GridHelper(2000, 100, 0x1e293b, 0x1e293b);
    grid.position.y = 0.05;
    this.scene.add(grid);
  }

  _setupControls() {
    this.controls = new OrbitControls(this.camera, this.renderer.domElement);
    this.controls.enableDamping = true;
    this.controls.dampingFactor = 0.08;
    this.controls.minDistance = 5;
    this.controls.maxDistance = 2000;
    this.controls.maxPolarAngle = Math.PI / 2 - 0.02;
  }

  _animate() {
    requestAnimationFrame(() => this._animate());
    this.controls.update();
    this.renderer.render(this.scene, this.camera);
  }

  resize() {
    const w = this.canvas.clientWidth, h = this.canvas.clientHeight;
    if (w === 0 || h === 0) return;
    this.renderer.setSize(w, h, false);
    if (this.camera) {
      this.camera.aspect = w / h;
      this.camera.updateProjectionMatrix();
    }
  }

  // ── Parcel ──────────────────────────────────────────────────────────────
  setParcel(feature, originE, originN) {
    this.originE = originE;
    this.originN = originN;
    this._clearGroup('parcel');

    const ring = feature.geometry.coordinates[0];
    const xz = ringToScene(ring, originE, originN);

    // Track bounds for camera
    const xs = xz.map(p => p[0]), zs = xz.map(p => p[1]);
    this._parcelBounds = { minX: Math.min(...xs), maxX: Math.max(...xs), minZ: Math.min(...zs), maxZ: Math.max(...zs) };

    const shape = makeShape(xz);
    const mesh = extrudeMesh(shape, MAT.parcel, 0.12);
    mesh.castShadow = true;
    mesh.receiveShadow = true;
    this.groups.parcel.add(mesh);

    const edge = new THREE.Line(shapeEdge(xz), MAT.parcelEdge);
    this.groups.parcel.add(edge);

    this.resetCamera();
  }

  // ── Neighbors ───────────────────────────────────────────────────────────
  setNeighbors(features) {
    this._clearGroup('neighbors');
    for (const f of features) {
      if (!f.geometry?.coordinates?.[0]) continue;
      const xz = ringToScene(f.geometry.coordinates[0], this.originE, this.originN);
      if (xz.length < 3) continue;
      const shape = makeShape(xz);
      const mesh = extrudeMesh(shape, MAT.neighbor, 0.08);
      mesh.receiveShadow = true;
      this.groups.neighbors.add(mesh);
      const edge = new THREE.Line(shapeEdge(xz), MAT.neighborEdge);
      this.groups.neighbors.add(edge);
    }
  }

  // ── Boundary zones ──────────────────────────────────────────────────────
  showBoundaryZones(parcelFeature, grossM, kleinM) {
    this._clearGroup('zones');
    this._clearGroup('violations');

    const addZone = (turfPoly, mat, yOffset = 0.05) => {
      if (!turfPoly) return;
      const coords = turfPoly.geometry.type === 'Polygon'
        ? turfPoly.geometry.coordinates
        : turfPoly.geometry.coordinates[0];
      const ring = Array.isArray(coords[0][0]) ? coords[0] : coords;
      const xz = ringToScene(ring, this.originE, this.originN);
      if (xz.length < 3) return;
      const shape = makeShape(xz);
      const mesh = extrudeMesh(shape, mat, 0.1);
      mesh.position.y = yOffset;
      this.groups.zones.add(mesh);
    };

    try {
      const grossOuter = turf.buffer(parcelFeature, -(grossM - 0.01), { units: 'meters' });
      const kleinOuter = turf.buffer(parcelFeature, -(kleinM - 0.01), { units: 'meters' });
      const grossRing = turf.difference(parcelFeature, grossOuter || parcelFeature);
      const kleinRing = grossOuter ? turf.difference(grossOuter, kleinOuter || grossOuter) : null;
      addZone(grossRing, MAT.gross);
      if (kleinRing) addZone(kleinRing, MAT.klein, 0.06);
    } catch { /* turf may fail for degenerate polygons */ }
  }

  // ── IFC building ─────────────────────────────────────────────────────────
  clearBuilding() { this._clearGroup('building'); }

  addBuildingMesh(bufferGeo, color) {
    const mat = new THREE.MeshLambertMaterial({
      color: color || 0xe2e8f0,
      transparent: true, opacity: 0.88,
      side: THREE.DoubleSide,
    });
    const mesh = new THREE.Mesh(bufferGeo, mat);
    mesh.castShadow = true;
    this.groups.building.add(mesh);
  }

  // ── Violations ───────────────────────────────────────────────────────────
  showViolationPoint(point, radius = 3) {
    const geo = new THREE.SphereGeometry(radius, 12, 8);
    const mesh = new THREE.Mesh(geo, MAT.violation);
    mesh.position.set(point.x, 2, point.z);
    this.groups.violations.add(mesh);
  }

  // ── Camera ───────────────────────────────────────────────────────────────
  resetCamera() {
    if (!this._parcelBounds) {
      this.camera.position.set(0, 150, 200);
      this.controls.target.set(0, 0, 0);
    } else {
      const b = this._parcelBounds;
      const cx = (b.minX + b.maxX) / 2;
      const cz = (b.minZ + b.maxZ) / 2;
      const size = Math.max(b.maxX - b.minX, b.maxZ - b.minZ);
      this.camera.position.set(cx, size * 1.2, cz + size * 1.0);
      this.controls.target.set(cx, 0, cz);
    }
    this.controls.update();
  }

  setTopView() {
    if (!this._parcelBounds) return;
    const b = this._parcelBounds;
    const cx = (b.minX + b.maxX) / 2;
    const cz = (b.minZ + b.maxZ) / 2;
    const size = Math.max(b.maxX - b.minX, b.maxZ - b.minZ);
    this.camera.position.set(cx, size * 2, cz + 0.001);
    this.controls.target.set(cx, 0, cz);
    this.controls.update();
  }

  toggleWireframe() {
    this.wireframe = !this.wireframe;
    Object.values(MAT).forEach(m => { if (m.wireframe !== undefined) m.wireframe = this.wireframe; });
  }

  _clearGroup(name) {
    const g = this.groups[name];
    while (g.children.length > 0) {
      const c = g.children[0];
      c.geometry?.dispose();
      g.remove(c);
    }
  }
}
