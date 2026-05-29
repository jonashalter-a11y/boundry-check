// Vercel Serverless Function – OEREB CORS Proxy
// Automatically deployed at /api/proxy when hosted on Vercel

const ALLOWED_HOSTS = new Set([
  'api.geo.ag.ch',
  'oereb.ai.ch',
  'oereb.ar.ch',
  'www.oereb2.apps.be.ch',
  'oereb.geo.bl.ch',
  'api.oereb.bs.ch',
  'maps.fr.ch',
  'ge.ch',
  'map.geo.gl.ch',
  'oereb.geo.gr.ch',
  'geo.jura.ch',
  'svc.geo.lu.ch',
  'oereb.gis-daten.ch',
  'oereb.geo.sg.ch',
  'oereb.geo.sh.ch',
  'geo.so.ch',
  'map.geo.sz.ch',
  'map.geo.tg.ch',
  'crdpp.geo.ti.ch',
  'prozessor-oereb.ur.ch',
  'www.rdppf.vd.ch',
  'rdppf.apps.vs.ch',
  'oereb.zg.ch',
  'maps.zh.ch',
]);

const CORS = {
  'Access-Control-Allow-Origin': '*',
  'Access-Control-Allow-Methods': 'GET, OPTIONS',
  'Access-Control-Allow-Headers': 'Content-Type, Accept',
};

export default async function handler(req, res) {
  // CORS preflight
  Object.entries(CORS).forEach(([k, v]) => res.setHeader(k, v));

  if (req.method === 'OPTIONS') {
    return res.status(204).end();
  }
  if (req.method !== 'GET') {
    return res.status(405).json({ error: 'Method not allowed' });
  }

  const targetUrl = req.query.url;
  if (!targetUrl) {
    return res.status(400).json({ error: 'Missing ?url= parameter' });
  }

  let parsed;
  try {
    parsed = new URL(targetUrl);
  } catch {
    return res.status(400).json({ error: 'Invalid URL' });
  }

  if (!ALLOWED_HOSTS.has(parsed.hostname)) {
    return res.status(403).json({ error: `Host not allowed: ${parsed.hostname}` });
  }

  try {
    const upstream = await fetch(targetUrl, {
      headers: {
        Accept: 'application/xml,text/xml;q=0.9,*/*;q=0.1',
        'User-Agent': 'GrenzcheckWebApp/1.0',
      },
    });

    const xml = await upstream.text();
    res.setHeader('Content-Type', upstream.headers.get('content-type') || 'application/xml');
    res.setHeader('Cache-Control', 'public, max-age=3600');
    return res.status(upstream.status).send(xml);
  } catch (err) {
    return res.status(502).json({ error: `Upstream fetch failed: ${err.message}` });
  }
}
