import { Scene3D } from './scene.js';
import { loadIfc, transformIfcToScene, extractFootprintWgs84 } from './ifc.js';
import {
  searchAddress, identifyParcel, findParcelByEgrid,
  fetchNeighborParcels, fetchOereb, parseParcelAttrs
} from './api.js';
import {
  parcelCentroidLv95, featureBbox, ringAreaM2, wgs84ToLv95
} from './geo.js';
import { runBoundaryCheck } from './boundary.js';

// ── Re-export convexHullLv95ToWgs84 for ifc.js ──────────────────────────────
// (geo.js exports it; ifc.js imports directly from geo.js – no action needed)

class App {
  constructor() {
    this.map = null;
    this.scene = null;
    this.currentView = '2d';

    // State
    this.parcelFeature = null;
    this.neighborFeatures = [];
    this.ifcMeshes = null;
    this.ifcMapConv = null;
    this.originE = 0;
    this.originN = 0;
    this.currentEgrid = '';
    this.currentCanton = '';

    // Leaflet layers
    this._parcelLayer = null;
    this._neighborLayer = null;
    this._zoneGrossLayer = null;
    this._zoneKleinLayer = null;

    this._initMap();
    this._initScene();
    this._bindAll();
    this.setView('2d');
  }

  // ── Map ─────────────────────────────────────────────────────────────────
  _initMap() {
    this.map = L.map('map', { zoomControl: true }).setView([46.8, 8.22], 8);

    L.tileLayer('https://wmts.geo.admin.ch/1.0.0/ch.swisstopo.pixelkarte-farbe/default/current/3857/{z}/{x}/{y}.jpeg', {
      attribution: '© swisstopo',
      maxZoom: 20,
    }).addTo(this.map);


    this.map.on('click', e => this._onMapClick(e.latlng.lng, e.latlng.lat));
    this.map.on('mousemove', e => {
      document.getElementById('coord-bar').textContent =
        `${e.latlng.lat.toFixed(5)}, ${e.latlng.lng.toFixed(5)}`;
    });
  }

  // ── Scene ────────────────────────────────────────────────────────────────
  _initScene() {
    const canvas = document.getElementById('three-canvas');
    // Scene is initialised on first switch to 3D to avoid wasted GPU when not needed
    this._scenePending = true;
    this._canvas = canvas;
  }

  _ensureScene() {
    if (!this.scene) {
      this.scene = new Scene3D(this._canvas);
      document.getElementById('sc-reset').onclick = () => this.scene.resetCamera();
      document.getElementById('sc-top').onclick = () => this.scene.setTopView();
      document.getElementById('sc-wire').onclick = () => this.scene.toggleWireframe();
    }
  }

  // ── Events ────────────────────────────────────────────────────────────────
  _bindAll() {
    // EGRID
    document.getElementById('btn-egrid').onclick = () => {
      const v = document.getElementById('egrid-input').value.trim().toUpperCase();
      if (v) this._loadParcelByEgrid(v);
    };
    document.getElementById('egrid-input').onkeydown = e => {
      if (e.key === 'Enter') document.getElementById('btn-egrid').click();
    };

    // Address search
    const addrIn = document.getElementById('addr-input');
    const addrDrop = document.getElementById('addr-drop');
    let addrTimer;
    addrIn.oninput = () => {
      clearTimeout(addrTimer);
      addrTimer = setTimeout(() => this._searchAddr(addrIn.value.trim()), 350);
    };
    addrIn.onkeydown = e => {
      if (e.key === 'Enter') { clearTimeout(addrTimer); this._searchAddr(addrIn.value.trim()); }
      if (e.key === 'Escape') addrDrop.classList.add('hidden');
    };
    document.getElementById('btn-addr').onclick = () => {
      clearTimeout(addrTimer); this._searchAddr(addrIn.value.trim());
    };

    // IFC file
    const ifcInput = document.getElementById('ifc-input');
    ifcInput.onchange = e => { if (e.target.files[0]) this._loadIfc(e.target.files[0]); };

    // Drag & drop
    const dz = document.getElementById('drop-zone');
    dz.ondragover = e => { e.preventDefault(); dz.classList.add('over'); };
    dz.ondragleave = () => dz.classList.remove('over');
    dz.ondrop = e => {
      e.preventDefault(); dz.classList.remove('over');
      const f = e.dataTransfer.files[0];
      if (f && f.name.endsWith('.ifc')) this._loadIfc(f);
    };

    // Grenzcheck
    document.getElementById('btn-check').onclick = () => this._runCheck();

    // OEREB
    document.getElementById('btn-oereb').onclick = () => this._loadOereb();

    // PDF
    document.getElementById('btn-pdf').onclick = () => this._exportPdf();
  }

  // ── View toggle ──────────────────────────────────────────────────────────
  setView(mode) {
    this.currentView = mode;
    document.getElementById('map-wrap').classList.toggle('hidden', mode !== '2d');
    document.getElementById('scene-wrap').classList.toggle('hidden', mode !== '3d');
    document.getElementById('vbtn-2d').classList.toggle('active', mode === '2d');
    document.getElementById('vbtn-3d').classList.toggle('active', mode === '3d');

    if (mode === '3d') {
      this._ensureScene();
      // Trigger resize so canvas fills container
      setTimeout(() => this.scene?.resize(), 50);
    }
    if (mode === '2d') {
      setTimeout(() => this.map.invalidateSize(), 50);
    }
  }

  // ── Status ───────────────────────────────────────────────────────────────
  _status(msg, loading = false, loadingText = '') {
    document.getElementById('status-text').textContent = msg;
    const spinner = document.getElementById('spinner');
    const spinText = document.getElementById('spin-text');
    spinner.classList.toggle('hidden', !loading);
    spinText.textContent = loadingText;
  }

  _setDot(id, state) {
    const el = document.getElementById(id);
    el.textContent = state === 'ok' ? '✓' : state === 'err' ? '✗' : '○';
    el.className = 'step-dot ' + (state || '');
  }

  // ── Parcel loading ────────────────────────────────────────────────────────
  async _onMapClick(lng, lat) {
    this._status('Suche Parzelle …', true, 'identify');
    try {
      const bounds = this.map.getBounds();
      const size = this.map.getSize();
      const feature = await identifyParcel(lng, lat, bounds, size);
      if (!feature) { this._status('Keine Parzelle an dieser Stelle gefunden.'); return; }
      await this._setParcel(feature);
    } catch (err) {
      this._status('Fehler: ' + err.message);
      this._setDot('dot-parcel', 'err');
    }
  }

  async _loadParcelByEgrid(egrid) {
    this._status(`Lade Parzelle ${egrid} …`, true, 'EGRID lookup');
    try {
      const feature = await findParcelByEgrid(egrid);
      if (!feature) { this._status(`EGRID ${egrid} nicht gefunden.`); return; }
      await this._setParcel(feature);
    } catch (err) {
      this._status('Fehler: ' + err.message);
      this._setDot('dot-parcel', 'err');
    }
  }

  async _setParcel(feature) {
    // Normalise geometry – API may return Feature or raw result
    if (!feature.geometry && feature.geometryType) {
      feature = { type: 'Feature', geometry: feature.geometry || feature, properties: feature.properties || feature.attributes || {} };
    }
    if (!feature.geometry?.coordinates) { this._status('Ungültige Parzellen-Geometrie.'); return; }

    const attrs = parseParcelAttrs(feature);
    this.currentEgrid = attrs.egrid;
    this.currentCanton = attrs.canton;
    this.parcelFeature = feature;

    const [originE, originN] = parcelCentroidLv95(feature);
    this.originE = originE;
    this.originN = originN;

    const area = ringAreaM2(feature.geometry.coordinates[0]);

    // Update parcel card
    document.getElementById('pc-egrid').textContent = attrs.egrid || '—';
    document.getElementById('pc-canton').textContent = attrs.canton || '—';
    document.getElementById('pc-nr').textContent = attrs.nr || '—';
    document.getElementById('pc-area').textContent = area > 0 ? `${Math.round(area).toLocaleString('de-CH')} m²` : '—';
    document.getElementById('parcel-card').classList.remove('hidden');
    this._setDot('dot-parcel', 'ok');

    // Map: show parcel
    if (this._parcelLayer) this.map.removeLayer(this._parcelLayer);
    this._parcelLayer = L.geoJSON(feature, { className: 'parcel-highlight' }).addTo(this.map);
    this.map.fitBounds(this._parcelLayer.getBounds(), { padding: [60, 60] });

    // Fetch neighbors
    this._status('Lade Nachbarparzellen …', true, 'WFS');
    const bbox = featureBbox(feature);
    const neighborRaw = await fetchNeighborParcels(bbox);
    // Filter out the target parcel itself (by EGRID if available)
    this.neighborFeatures = neighborRaw.filter(f => {
      const a = parseParcelAttrs(f);
      return a.egrid !== attrs.egrid && a.egrid !== '';
    });

    if (this._neighborLayer) this.map.removeLayer(this._neighborLayer);
    if (this.neighborFeatures.length > 0) {
      this._neighborLayer = L.geoJSON({ type: 'FeatureCollection', features: this.neighborFeatures }, {
        className: 'neighbor-highlight',
      }).addTo(this.map);
    }

    // 3D scene (if active)
    if (this.scene) {
      this.scene.setParcel(feature, originE, originN);
      this.scene.setNeighbors(this.neighborFeatures);
    }

    this._status(`Parzelle geladen (${Math.round(area).toLocaleString('de-CH')} m²)`);

    // If IFC is already loaded, re-apply georef
    if (this.ifcMeshes && this.scene) this._applyIfcToScene();
  }

  // ── Address search ────────────────────────────────────────────────────────
  async _searchAddr(q) {
    const drop = document.getElementById('addr-drop');
    if (q.length < 2) { drop.classList.add('hidden'); return; }
    try {
      const results = await searchAddress(q);
      drop.innerHTML = results.length
        ? results.map((r, i) => `<div class="ac-item" data-i="${i}">${r.label}</div>`).join('')
        : '<div class="ac-item">Keine Ergebnisse</div>';
      drop.classList.remove('hidden');
      drop.querySelectorAll('.ac-item[data-i]').forEach(el => {
        el.onclick = () => {
          const r = results[+el.dataset.i];
          document.getElementById('addr-input').value = r.label;
          drop.classList.add('hidden');
          this.map.setView([r.lat, r.lon], 17);
        };
      });
    } catch { drop.classList.add('hidden'); }
  }

  // ── IFC loading ───────────────────────────────────────────────────────────
  async _loadIfc(file) {
    this._status(`Lade IFC: ${file.name} …`, true, 'Parsing');
    document.getElementById('ifc-prog-wrap').hidden = false;
    document.getElementById('ic-name').textContent = file.name;
    document.getElementById('ifc-card').classList.remove('hidden');
    this._setDot('dot-ifc', '');

    try {
      const buffer = await file.arrayBuffer();
      const { meshes, mapConversion } = await loadIfc(buffer, (p) => {
        document.getElementById('ifc-prog').style.width = `${Math.round(p * 100)}%`;
        this._status(`IFC parsen: ${Math.round(p * 100)}%`, true, 'web-ifc');
      });

      this.ifcMeshes = meshes;
      this.ifcMapConv = mapConversion;

      document.getElementById('ic-count').textContent = meshes.length.toLocaleString('de-CH');
      document.getElementById('ic-georef').textContent = mapConversion
        ? `E ${Math.round(mapConversion.eastings).toLocaleString('de-CH')}, N ${Math.round(mapConversion.northings).toLocaleString('de-CH')}`
        : 'Nicht gefunden (Parzellenmitte)';
      document.getElementById('ifc-prog-wrap').hidden = true;
      this._setDot('dot-ifc', 'ok');

      this._ensureScene();
      this._applyIfcToScene();

      this.setView('3d');
      this._status(`IFC geladen – ${meshes.length} Geometrien`);
    } catch (err) {
      this._status('IFC Fehler: ' + err.message);
      this._setDot('dot-ifc', 'err');
      console.error(err);
    }
  }

  _applyIfcToScene() {
    if (!this.scene || !this.ifcMeshes) return;
    this.scene.clearBuilding();

    const originE = this.ifcMapConv?.eastings ?? this.originE;
    const originN = this.ifcMapConv?.northings ?? this.originN;
    const useOriginE = this.originE || originE;
    const useOriginN = this.originN || originN;

    const transformed = transformIfcToScene(this.ifcMeshes, this.ifcMapConv, useOriginE, useOriginN);
    for (const { geometry, color } of transformed) {
      this.scene.addBuildingMesh(geometry, color);
    }
  }

  // ── Boundary check ────────────────────────────────────────────────────────
  async _runCheck() {
    if (!this.parcelFeature) {
      alert('Bitte zuerst eine Parzelle laden.');
      return;
    }

    const grossM = parseFloat(document.getElementById('p-gross').value) || 6;
    const kleinM = parseFloat(document.getElementById('p-klein').value) || 3;

    let buildingFeature = null;

    // Try to get building footprint from IFC
    if (this.ifcMeshes && this.ifcMeshes.length > 0) {
      buildingFeature = extractFootprintWgs84(this.ifcMeshes, this.ifcMapConv, this.originE, this.originN);
    }

    const resultEl = document.getElementById('check-result');
    resultEl.classList.remove('hidden', 'result-ok', 'result-viol');

    // Always show boundary zones on map and in 3D
    this._showZonesOnMap(grossM, kleinM);
    this._ensureScene();
    if (this.scene && this.parcelFeature) {
      this.scene.showBoundaryZones(this.parcelFeature, grossM, kleinM);
    }
    this.setView('3d');

    if (!buildingFeature) {
      resultEl.innerHTML = `
        <div style="color:var(--text2)">
          <strong>Zonen visualisiert</strong><br>
          Kein IFC-Modell geladen – Grenzabstandszonen werden angezeigt,
          aber keine Verletzungsprüfung möglich.
          <br><br>
          🟠 Grosser GA: ${grossM} m<br>
          🔴 Kleiner GA: ${kleinM} m
        </div>`;
      this._setDot('dot-check', '');
      this._status('Grenzabstandszonen angezeigt (kein IFC geladen)');
      return;
    }

    this._status('Prüfe Grenzabstände …', true, 'Berechnung');

    try {
      const result = runBoundaryCheck(this.parcelFeature, buildingFeature, grossM, kleinM);

      if (result.ok) {
        resultEl.classList.add('result-ok');
        resultEl.innerHTML = `
          <div class="ok-item">✅ Grenzabstand eingehalten</div>
          <div style="margin-top:6px;color:var(--text2)">
            Minimalabstand: <strong>${result.minDistance.toFixed(2)} m</strong><br>
            Grosser GA (${grossM} m): ✓<br>
            Kleiner GA (${kleinM} m): ✓
          </div>`;
        this._setDot('dot-check', 'ok');
        this._status('✅ Grenzabstand eingehalten');
      } else {
        resultEl.classList.add('result-viol');
        const v = result.violations[0];
        resultEl.innerHTML = `
          <div class="viol-item">❌ Grenzabstandsverletzung!</div>
          <div style="margin-top:6px">
            Geforderter ${v.type === 'gross' ? 'Grosser' : 'Kleiner'} GA: <strong>${v.required} m</strong><br>
            Tatsächlicher Abstand: <strong style="color:var(--error)">${v.actual.toFixed(2)} m</strong><br>
            Unterschreitung: <strong style="color:var(--error)">${(v.required - v.actual).toFixed(2)} m</strong>
          </div>`;
        this._setDot('dot-check', 'err');
        this._status('❌ Grenzabstandsverletzung festgestellt');

        // Show violation point in 3D
        if (this.scene && v.point) {
          const [lon, lat] = v.point.geometry.coordinates;
          const [e, n] = wgs84ToLv95(lon, lat);
          this.scene.showViolationPoint({ x: e - this.originE, z: -(n - this.originN) });
        }
      }
    } catch (err) {
      resultEl.innerHTML = `<div style="color:var(--text2)">Berechnungsfehler: ${err.message}</div>`;
      this._status('Fehler bei Grenzcheck: ' + err.message);
      console.error(err);
    }
  }

  _showZonesOnMap(grossM, kleinM) {
    if (!this.parcelFeature) return;
    if (this._zoneGrossLayer) this.map.removeLayer(this._zoneGrossLayer);
    if (this._zoneKleinLayer) this.map.removeLayer(this._zoneKleinLayer);
    try {
      const inner = turf.buffer(this.parcelFeature, -grossM, { units: 'meters' });
      const ring = inner ? turf.difference(this.parcelFeature, inner) : this.parcelFeature;
      if (ring) this._zoneGrossLayer = L.geoJSON(ring, { className: 'zone-gross' }).addTo(this.map);

      if (inner) {
        const inner2 = turf.buffer(this.parcelFeature, -kleinM, { units: 'meters' });
        const ring2 = inner2 ? turf.difference(inner, inner2) : inner;
        if (ring2) this._zoneKleinLayer = L.geoJSON(ring2, { className: 'zone-klein' }).addTo(this.map);
      }
    } catch { /* turf failure on small parcels */ }
  }

  // ── OEREB ────────────────────────────────────────────────────────────────
  async _loadOereb() {
    if (!this.currentEgrid) { alert('Bitte zuerst eine Parzelle laden.'); return; }
    this._status('Lade OEREB-Daten …', true, 'XML');
    this._setDot('dot-oereb', '');

    // On Vercel (or any non-localhost host) use the built-in /api/proxy.
    // On localhost fall back to whatever the user typed in (or empty).
    const isHosted = !['localhost', '127.0.0.1', ''].includes(window.location.hostname);
    const proxyUrl = isHosted
      ? '/api/proxy'
      : (document.getElementById('proxy-url').value.trim() || '');

    try {
      const result = await fetchOereb(this.currentEgrid, this.currentCanton, proxyUrl);

      const listEl = document.getElementById('oereb-list');
      listEl.classList.remove('hidden');

      if (!result || result.zones.length === 0) {
        listEl.innerHTML = `<div class="zone-item" style="color:var(--text2)">Keine OEREB-Zonen gefunden${!proxyUrl ? ' (kein CORS-Proxy konfiguriert)' : ''}.</div>`;
        this._setDot('dot-oereb', 'err');
        this._status('OEREB: Keine Daten gefunden');
        return;
      }

      listEl.innerHTML = result.zones.slice(0, 15).map(z => {
        const isNutz = z.theme_code.toLowerCase().includes('nutzungsplanung');
        const meta = [
          z.theme_text && !isNutz ? z.theme_text : null,
          z.area_share ? `${z.area_share.toLocaleString('de-CH')} m²` : null,
          z.part_in_percent ? `${z.part_in_percent.toFixed(1)} %` : null,
        ].filter(Boolean).join(' · ');
        return `<div class="zone-item ${isNutz ? 'zone-nutzung' : 'zone-other'}">
          <div class="zone-name">${z.legend_text}</div>
          ${meta ? `<div class="zone-meta">${meta}</div>` : ''}
        </div>`;
      }).join('');

      if (result.municipality) {
        listEl.insertAdjacentHTML('afterbegin', `<div class="zone-item" style="background:none;border-left:none;padding-left:0"><b>📍 ${result.municipality}</b></div>`);
      }

      this._setDot('dot-oereb', 'ok');
      this._status(`OEREB: ${result.zones.length} Zonen geladen`);
    } catch (err) {
      this._status('OEREB Fehler: ' + err.message);
      this._setDot('dot-oereb', 'err');
      console.error(err);
    }
  }

  // ── PDF Export ────────────────────────────────────────────────────────────
  async _exportPdf() {
    const { jsPDF } = window.jspdf;
    const doc = new jsPDF({ orientation: 'portrait', unit: 'mm', format: 'a4' });

    const now = new Date().toLocaleDateString('de-CH', { day: '2-digit', month: '2-digit', year: 'numeric' });
    const egrid = this.currentEgrid || '—';
    const canton = this.currentCanton || '—';
    const grossM = document.getElementById('p-gross').value;
    const kleinM = document.getElementById('p-klein').value;

    // Header
    doc.setFillColor(37, 99, 235);
    doc.rect(0, 0, 210, 28, 'F');
    doc.setTextColor(255, 255, 255);
    doc.setFontSize(20);
    doc.setFont(undefined, 'bold');
    doc.text('Grenzabstandsprüfung', 14, 14);
    doc.setFontSize(10);
    doc.setFont(undefined, 'normal');
    doc.text('Baurecht Schweiz – Automatischer Grenzcheck', 14, 21);

    doc.setTextColor(0, 0, 0);
    let y = 38;

    const section = (title) => {
      doc.setFillColor(243, 244, 246);
      doc.rect(14, y - 5, 182, 8, 'F');
      doc.setFont(undefined, 'bold');
      doc.setFontSize(11);
      doc.text(title, 16, y);
      doc.setFont(undefined, 'normal');
      doc.setFontSize(10);
      y += 8;
    };

    const row = (label, value) => {
      doc.setTextColor(100, 116, 139);
      doc.text(label, 16, y);
      doc.setTextColor(0, 0, 0);
      doc.text(String(value), 70, y);
      y += 7;
    };

    section('Parzelle');
    row('EGRID', egrid);
    row('Kanton', canton);
    row('Parzellennummer', document.getElementById('pc-nr').textContent);
    row('Fläche', document.getElementById('pc-area').textContent);
    y += 4;

    section('Grenzabstandsparameter');
    row('Grosser Grenzabstand', `${grossM} m`);
    row('Kleiner Grenzabstand', `${kleinM} m`);
    y += 4;

    const resultEl = document.getElementById('check-result');
    section('Prüfresultat');
    if (!resultEl.classList.contains('hidden')) {
      const txt = resultEl.innerText.replace(/\n+/g, ' ').trim();
      doc.setFontSize(9);
      const lines = doc.splitTextToSize(txt, 170);
      doc.text(lines, 16, y);
      y += lines.length * 5 + 4;
    } else {
      doc.text('Noch kein Grenzcheck durchgeführt.', 16, y);
      y += 10;
    }

    // OEREB zones
    const oerebEl = document.getElementById('oereb-list');
    if (!oerebEl.classList.contains('hidden') && oerebEl.children.length > 0) {
      y += 4;
      section('OEREB-Nutzungszonen');
      for (const item of oerebEl.querySelectorAll('.zone-item')) {
        if (y > 270) { doc.addPage(); y = 20; }
        doc.setFontSize(9);
        const name = item.querySelector('.zone-name')?.textContent || '';
        const meta = item.querySelector('.zone-meta')?.textContent || '';
        doc.setFont(undefined, 'bold');
        doc.text(name, 16, y);
        doc.setFont(undefined, 'normal');
        if (meta) { doc.setTextColor(100, 116, 139); doc.text(meta, 100, y); doc.setTextColor(0,0,0); }
        y += 6;
      }
    }

    // Footer
    const pages = doc.internal.getNumberOfPages();
    for (let i = 1; i <= pages; i++) {
      doc.setPage(i);
      doc.setFontSize(8);
      doc.setTextColor(150, 150, 150);
      doc.text(`Erstellt: ${now} · Grenzcheck Web-App · Seite ${i}/${pages}`, 14, 290);
    }

    const filename = `grenzcheck_${egrid}_${now.replace(/\./g, '')}.pdf`;
    doc.save(filename);

    this._setDot('dot-export', 'ok');
    this._status(`PDF gespeichert: ${filename}`);
  }
}

// Boot
window.app = new App();
