// Cloudflare Worker – OEREB CORS Proxy
// Deploy: npx wrangler deploy
// Oder: Cloudflare Dashboard → Workers → neuen Worker erstellen → Code einfügen

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

const CORS_HEADERS = {
  'Access-Control-Allow-Origin': '*',
  'Access-Control-Allow-Methods': 'GET, OPTIONS',
  'Access-Control-Allow-Headers': 'Content-Type, Accept',
};

export default {
  async fetch(request, env, ctx) {
    // Handle CORS preflight
    if (request.method === 'OPTIONS') {
      return new Response(null, { status: 204, headers: CORS_HEADERS });
    }

    if (request.method !== 'GET') {
      return new Response('Method not allowed', { status: 405, headers: CORS_HEADERS });
    }

    const url = new URL(request.url);
    const targetUrl = url.searchParams.get('url');

    if (!targetUrl) {
      return new Response(JSON.stringify({ error: 'Missing ?url= parameter' }), {
        status: 400,
        headers: { ...CORS_HEADERS, 'Content-Type': 'application/json' },
      });
    }

    let targetParsed;
    try {
      targetParsed = new URL(targetUrl);
    } catch {
      return new Response(JSON.stringify({ error: 'Invalid URL' }), {
        status: 400,
        headers: { ...CORS_HEADERS, 'Content-Type': 'application/json' },
      });
    }

    if (!ALLOWED_HOSTS.has(targetParsed.hostname)) {
      return new Response(JSON.stringify({ error: `Host not allowed: ${targetParsed.hostname}` }), {
        status: 403,
        headers: { ...CORS_HEADERS, 'Content-Type': 'application/json' },
      });
    }

    try {
      const upstream = await fetch(targetUrl, {
        headers: {
          'Accept': 'application/xml,text/xml;q=0.9,*/*;q=0.1',
          'User-Agent': 'GrenzcheckWebApp/1.0',
        },
        cf: { cacheTtl: 3600 }, // Cache OEREB responses for 1h at edge
      });

      const contentType = upstream.headers.get('Content-Type') || 'application/xml';

      return new Response(upstream.body, {
        status: upstream.status,
        headers: {
          ...CORS_HEADERS,
          'Content-Type': contentType,
          'Cache-Control': 'public, max-age=3600',
        },
      });
    } catch (err) {
      return new Response(JSON.stringify({ error: `Upstream fetch failed: ${err.message}` }), {
        status: 502,
        headers: { ...CORS_HEADERS, 'Content-Type': 'application/json' },
      });
    }
  },
};
