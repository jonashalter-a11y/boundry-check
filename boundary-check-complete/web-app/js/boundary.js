// Boundary distance check using turf.js (global)
// Computes minimum distance from building footprint to parcel boundary
// and detects violations against gross/klein Grenzabstand.

// parcelFeature:   GeoJSON Feature<Polygon> – target parcel (WGS84)
// buildingFeature: GeoJSON Feature<Polygon> – building footprint (WGS84)
// grossM, kleinM:  required distances in metres
export function runBoundaryCheck(parcelFeature, buildingFeature, grossM, kleinM) {
  const results = [];

  // Get parcel boundary as a LineString
  const parcelLine = turf.polygonToLine(parcelFeature);

  // Sample points along the building outline
  const buildingLine = turf.polygonToLine(buildingFeature);
  const totalLen = turf.length(buildingLine, { units: 'meters' });
  const sampleInterval = Math.max(0.1, totalLen / 200); // at most 200 sample points
  const samples = [];
  for (let d = 0; d <= totalLen; d += sampleInterval) {
    samples.push(turf.along(buildingLine, d, { units: 'meters' }));
  }

  let minDist = Infinity;
  let minPt = null;

  for (const pt of samples) {
    const nearest = turf.nearestPointOnLine(parcelLine, pt, { units: 'meters' });
    const dist = nearest.properties.dist;
    if (dist < minDist) {
      minDist = dist;
      minPt = pt;
    }
  }

  const ok_gross = minDist >= grossM;
  const ok_klein = minDist >= kleinM;

  if (!ok_gross) {
    results.push({
      type: 'gross',
      required: grossM,
      actual: minDist,
      point: minPt,
    });
  } else if (!ok_klein) {
    results.push({
      type: 'klein',
      required: kleinM,
      actual: minDist,
      point: minPt,
    });
  }

  // Per-boundary-segment analysis
  const segments = [];
  const ring = parcelFeature.geometry.coordinates[0];
  for (let i = 0; i < ring.length - 1; i++) {
    const seg = turf.lineString([ring[i], ring[i + 1]]);
    let segMin = Infinity;
    for (const pt of samples) {
      const near = turf.nearestPointOnLine(seg, pt, { units: 'meters' });
      if (near.properties.dist < segMin) segMin = near.properties.dist;
    }
    segments.push({ index: i, dist: segMin });
  }

  return {
    ok: results.length === 0,
    minDistance: minDist,
    violations: results,
    segments,
  };
}

