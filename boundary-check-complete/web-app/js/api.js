import { wgs84ToLv95, expandBbox } from './geo.js';

const GEOADMIN_SEARCH = 'https://api3.geo.admin.ch/rest/services/ech/SearchServer';
const GEOADMIN_IDENTIFY = 'https://api3.geo.admin.ch/rest/services/all/MapServer/identify';
const GEOADMIN_FIND = 'https://api3.geo.admin.ch/rest/services/ech/MapServer/find';
const WFS_URL = 'https://wfs.geo.admin.ch/';

export const OEREB_ENDPOINTS = {
  AG: 'https://api.geo.ag.ch/v2/oereb',
  AI: 'https://oereb.ai.ch/ktai/wsgi/oereb',
  AR: 'https://oereb.ar.ch/ktar/wsgi/oereb',
  BE: 'https://www.oereb2.apps.be.ch',
  BL: 'https://oereb.geo.bl.ch',
  BS: 'https://api.oereb.bs.ch',
  FR: 'https://maps.fr.ch/RDPPF_ws/RdppfSVC.svc',
  GE: 'https://ge.ch/terecadastrews/RdppfSVC.svc',
  GL: 'https://map.geo.gl.ch/oereb',
  GR: 'https://oereb.geo.gr.ch/oereb',
  JU: 'https://geo.jura.ch/crdppf_server',
  LU: 'https://svc.geo.lu.ch/oereb',
  NE: 'https://oereb.gis-daten.ch/oereb',
  SG: 'https://oereb.geo.sg.ch/ktsg/wsgi/oereb',
  SH: 'https://oereb.geo.sh.ch',
  SO: 'https://geo.so.ch/api/oereb',
  SZ: 'https://map.geo.sz.ch/oereb',
  TG: 'https://map.geo.tg.ch/services/oereb',
  TI: 'https://crdpp.geo.ti.ch/oereb2',
  UR: 'https://prozessor-oereb.ur.ch/oereb',
  VD: 'https://www.rdppf.vd.ch/ws/RdppfSVC.svc',
  VS: 'https://rdppf.apps.vs.ch',
  ZG: 'https://oereb.zg.ch/ors',
  ZH: 'https://maps.zh.ch/oereb/v2',
};

// Cantons confirmed to support CORS (from our test)
export const CORS_CANTONS = new Set(['AG', 'BE', 'FR', 'SO', 'TG', 'TI', 'UR', 'ZG', 'ZH']);

async function fetchJson(url) {
  const r = await fetch(url);
  if (!r.ok) throw new Error(`HTTP ${r.status}: ${url}`);
  return r.json();
}

// Address autocomplete
export async function searchAddress(query) {
  const url = `${GEOADMIN_SEARCH}?searchText=${encodeURIComponent(query)}&type=locations&sr=4326&limit=8&lang=de`;
  const data = await fetchJson(url);
  return (data.results || []).map(r => ({
    label: (r.attrs.label || r.attrs.detail || '').replace(/<[^>]+>/g, ''),
    lat: r.attrs.y,
    lon: r.attrs.x,
  }));
}

// Identify parcel by clicking on map
export async function identifyParcel(lng, lat, bounds, size) {
  const ext = `${bounds.getWest()},${bounds.getSouth()},${bounds.getEast()},${bounds.getNorth()}`;
  const img = `${size.x},${size.y},96`;
  const url = `${GEOADMIN_IDENTIFY}?geometry=${lng},${lat}&geometryType=esriGeometryPoint` +
    `&layers=all:ch.swisstopo-vd.amtliche-vermessung&mapExtent=${ext}&imageDisplay=${img}` +
    `&sr=4326&tolerance=10&returnGeometry=true&geometryFormat=geojson`;
  const data = await fetchJson(url);
  return data.results?.[0] || null;
}

// Find parcel by EGRID (two-step: locations search → identify)
export async function findParcelByEgrid(egrid) {
  // Step 1: get approximate coordinates from the locations index
  const searchUrl = `${GEOADMIN_SEARCH}?searchText=${encodeURIComponent(egrid)}&type=locations&sr=4326&limit=5&lang=de`;
  const searchData = await fetchJson(searchUrl);
  // Accept any result – SearchServer returns parcel as first hit for EGRID strings
  const hit = (searchData.results || [])[0];
  if (!hit?.attrs?.y) return null;

  const lat = hit.attrs.y, lon = hit.attrs.x;

  // Step 2: identify the parcel polygon at those coordinates
  const d = 0.002;
  const ext = `${lon-d},${lat-d},${lon+d},${lat+d}`;
  const identUrl = `${GEOADMIN_IDENTIFY}?geometry=${lon},${lat}` +
    `&geometryType=esriGeometryPoint` +
    `&layers=all:ch.swisstopo-vd.amtliche-vermessung` +
    `&mapExtent=${ext}&imageDisplay=800,600,96` +
    `&sr=4326&tolerance=5&returnGeometry=true&geometryFormat=geojson`;
  const identData = await fetchJson(identUrl);
  return identData.results?.[0] || null;
}

// Extract parcel attributes from a raw result feature
export function parseParcelAttrs(feature) {
  const attr = feature.properties || feature.attributes || {};
  let egrid = '', canton = '', nr = '';
  for (const [k, v] of Object.entries(attr)) {
    const kl = k.toLowerCase();
    if (!egrid && (kl.includes('egrid') || kl.includes('egris'))) egrid = String(v || '');
    if (!canton && (kl === 'ak' || kl === 'kanton' || kl === 'kt' || kl === 'canton')) canton = String(v || '');
    if (!nr && (kl === 'number' || kl === 'nummer' || kl === 'name')) nr = String(v || '');
  }
  return { egrid, canton, nr };
}

// Fetch neighboring parcels via WFS bbox query
export async function fetchNeighborParcels(bbox) {
  // bbox in WGS84 [minLon, minLat, maxLon, maxLat]
  const expanded = expandBbox(bbox, 5);
  const [minLon, minLat, maxLon, maxLat] = expanded;
  // Convert bbox corners to LV95 for WFS
  const [minE, minN] = wgs84ToLv95(minLon, minLat);
  const [maxE, maxN] = wgs84ToLv95(maxLon, maxLat);

  const url = `${WFS_URL}?SERVICE=WFS&VERSION=2.0.0&REQUEST=GetFeature` +
    `&TYPENAMES=ch.swisstopo-vd.amtliche-vermessung` +
    `&outputFormat=application/json` +
    `&BBOX=${minE},${minN},${maxE},${maxN},EPSG:2056` +
    `&COUNT=80`;

  try {
    const data = await fetchJson(url);
    return data.features || [];
  } catch {
    return [];
  }
}

// Parse OEREB XML response
export function parseOerebXml(xmlText) {
  const NS = {
    extract: 'http://schemas.geo.admin.ch/V_D/OeREB/2.0/Extract',
    data: 'http://schemas.geo.admin.ch/V_D/OeREB/2.0/ExtractData',
  };

  let doc;
  try {
    doc = new DOMParser().parseFromString(xmlText, 'text/xml');
  } catch {
    return null;
  }

  if (!xmlText.includes('GetExtractByIdResponse')) return null;

  function txt(el, xpath) {
    if (!el) return null;
    const parts = xpath.split('/');
    let cur = el;
    for (const part of parts) {
      const [prefix, local] = part.split(':');
      const ns = NS[prefix] || '';
      const found = [...cur.children].find(c => c.localName === local && c.namespaceURI === ns);
      if (!found) return null;
      cur = found;
    }
    return cur.textContent?.trim() || null;
  }

  function queryAll(el, localName) {
    return [...el.getElementsByTagNameNS(NS.data, localName)];
  }

  const reEl = doc.getElementsByTagNameNS(NS.data, 'RealEstate')[0];
  const municipality = reEl
    ? txt(reEl, 'data:Municipality/data:Name/data:LocalisedText/data:Text')
    : null;

  const agg = new Map();
  for (const r of queryAll(doc, 'RestrictionOnLandownership')) {
    const themeCode = txt(r, 'data:Theme/data:Code') || '';
    const themeText = txt(r, 'data:Theme/data:Text/data:LocalisedText/data:Text') || '';
    const legendText = txt(r, 'data:LegendText/data:LocalisedText/data:Text') || '';
    if (!legendText) continue;

    const lawStatus = txt(r, 'data:Lawstatus/data:Code');
    const rawArea = txt(r, 'data:AreaShare');
    const rawPct = txt(r, 'data:PartInPercent');
    const area = rawArea && /^\d+$/.test(rawArea) ? parseInt(rawArea) : null;
    const pct = rawPct ? parseFloat(rawPct) : null;

    const key = `${themeCode}::${legendText}::${lawStatus}`;
    if (agg.has(key)) {
      const ex = agg.get(key);
      if (area != null) ex.area_share = (ex.area_share || 0) + area;
      if (pct != null) ex.part_in_percent = (ex.part_in_percent || 0) + pct;
    } else {
      agg.set(key, { legend_text: legendText, theme_code: themeCode, theme_text: themeText, law_status: lawStatus, area_share: area, part_in_percent: pct });
    }
  }

  const zones = [...agg.values()]
    .filter(z => (z.area_share || 0) > 0 || (z.part_in_percent || 0) > 0)
    .sort((a, b) => {
      const an = a.theme_code.toLowerCase().includes('nutzungsplanung');
      const bn = b.theme_code.toLowerCase().includes('nutzungsplanung');
      if (an !== bn) return an ? -1 : 1;
      return (b.area_share || 0) - (a.area_share || 0);
    });

  return { zones, municipality };
}

// Fetch OEREB data – tries canton directly, falls back to proxy
export async function fetchOereb(egrid, canton, proxyUrl) {
  const endpoints = canton && OEREB_ENDPOINTS[canton]
    ? [[canton, OEREB_ENDPOINTS[canton]], ...Object.entries(OEREB_ENDPOINTS).filter(([c]) => c !== canton)]
    : Object.entries(OEREB_ENDPOINTS);

  for (const [c, base] of endpoints) {
    const target = `${base.replace(/\/$/, '')}/extract/xml/?EGRID=${egrid}`;
    let xml = null;

    if (CORS_CANTONS.has(c)) {
      try {
        const r = await fetch(target, { headers: { Accept: 'application/xml,text/xml' } });
        if (r.ok) xml = await r.text();
      } catch { /* ignore */ }
    } else if (proxyUrl) {
      try {
        const proxied = `${proxyUrl.replace(/\/$/, '')}?url=${encodeURIComponent(target)}`;
        const r = await fetch(proxied);
        if (r.ok) xml = await r.text();
      } catch { /* ignore */ }
    }

    if (xml) {
      const result = parseOerebXml(xml);
      if (result && result.zones.length > 0) return result;
    }
  }
  return null;
}
