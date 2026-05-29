// Swiss coordinate conversion (LV95 / EPSG:2056 ↔ WGS84)
// Approximation formula from swisstopo – accurate to ~1 m

export function wgs84ToLv95(lon, lat) {
  const lat_aux = (lat * 3600 - 169028.66) / 10000;
  const lon_aux = (lon * 3600 - 26782.5) / 10000;
  const e = 2600072.37
    + 211455.93 * lon_aux
    - 10938.51 * lon_aux * lat_aux
    - 0.36 * lon_aux * lat_aux ** 2
    - 44.54 * lon_aux ** 3;
  const n = 1200147.07
    + 308807.95 * lat_aux
    + 3745.25 * lon_aux ** 2
    + 76.63 * lat_aux ** 2
    - 194.56 * lon_aux ** 2 * lat_aux
    + 119.79 * lat_aux ** 3;
  return [e, n];
}

export function lv95ToWgs84(e, n) {
  const e_aux = (e - 2600000) / 1000000;
  const n_aux = (n - 1200000) / 1000000;
  const lon = (2.6779094
    + 4.728982 * e_aux
    + 0.791484 * e_aux * n_aux
    + 0.1306 * e_aux * n_aux ** 2
    - 0.0436 * e_aux ** 3) * 100 / 36;
  const lat = (16.9023892
    + 3.238272 * n_aux
    - 0.270978 * e_aux ** 2
    - 0.002528 * n_aux ** 2
    - 0.0447 * e_aux ** 2 * n_aux
    - 0.0140 * n_aux ** 3) * 100 / 36;
  return [lon, lat];
}

// Convert a GeoJSON ring [[lon,lat],...] → LV95 [[e,n],...]
export function ringToLv95(ring) {
  return ring.map(([lon, lat]) => wgs84ToLv95(lon, lat));
}

// Centroid of a GeoJSON polygon feature in LV95
export function parcelCentroidLv95(feature) {
  const ring = feature.geometry.coordinates[0];
  const lv = ring.map(([lon, lat]) => wgs84ToLv95(lon, lat));
  const e = lv.reduce((s, p) => s + p[0], 0) / lv.length;
  const n = lv.reduce((s, p) => s + p[1], 0) / lv.length;
  return [e, n];
}

// Convert LV95 point to Three.js scene coords (origin in LV95)
// Three.js: X=East, Y=up, Z=South (right-hand Y-up)
export function lv95ToScene(e, n, originE, originN) {
  return { x: e - originE, y: 0, z: -(n - originN) };
}

// Convert a GeoJSON ring (WGS84) to scene XZ pairs
export function ringToScene(ring, originE, originN) {
  return ring.map(([lon, lat]) => {
    const [e, n] = wgs84ToLv95(lon, lat);
    return [e - originE, -(n - originN)];
  });
}

// Area of a GeoJSON polygon ring in m² (shoelace in LV95 metres)
export function ringAreaM2(ring) {
  const lv = ring.map(([lon, lat]) => wgs84ToLv95(lon, lat));
  let area = 0;
  for (let i = 0, j = lv.length - 1; i < lv.length; j = i++) {
    area += (lv[j][0] + lv[i][0]) * (lv[j][1] - lv[i][1]);
  }
  return Math.abs(area / 2);
}

// Bounding box of a GeoJSON feature in WGS84 [minLon, minLat, maxLon, maxLat]
export function featureBbox(feature) {
  const coords = feature.geometry.coordinates[0];
  let minLon = Infinity, minLat = Infinity, maxLon = -Infinity, maxLat = -Infinity;
  for (const [lon, lat] of coords) {
    if (lon < minLon) minLon = lon;
    if (lat < minLat) minLat = lat;
    if (lon > maxLon) maxLon = lon;
    if (lat > maxLat) maxLat = lat;
  }
  return [minLon, minLat, maxLon, maxLat];
}

// Expand a WGS84 bbox by metres (approx)
export function expandBbox(bbox, metres) {
  const deg = metres / 111320;
  return [bbox[0] - deg, bbox[1] - deg, bbox[2] + deg, bbox[3] + deg];
}

// Convex hull of LV95 points → GeoJSON Feature<Polygon> in WGS84
// Uses turf.js (global) for the hull computation
export function convexHullLv95ToWgs84(lv95Points, lv95ToWgs84fn) {
  if (!lv95Points || lv95Points.length < 3) return null;
  const wgsPts = lv95Points.map(([e, n]) => {
    const [lon, lat] = lv95ToWgs84fn(e, n);
    return turf.point([lon, lat]);
  });
  const fc = turf.featureCollection(wgsPts);
  return turf.convex(fc);
}
