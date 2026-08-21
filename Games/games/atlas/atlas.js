// atlas.js — a living map. A 2-parameter slice table(x,y) = clamp(A +
// x(B-A) + y(C-A)) over three anchor tables is progressively surveyed and
// painted: a dense base sweep fills the visible frontier within about a
// second, then finer detail grows toward the viewport, color boundaries,
// and hot ground. Full diegesis (DESIGN.md): the play surface never speaks
// the solution domain — colors, an icon+heat tooltip, and three plain
// buttons are the whole interaction. Every raw number lives behind the
// single "the ledger" affordance, never on the map itself.
(function () {
  'use strict';

  // ---- domain / quadtree constants -----------------------------------
  const DOMAIN_MIN = -8, DOMAIN_MAX = 24, DOMAIN_SIZE = DOMAIN_MAX - DOMAIN_MIN;
  const BASE_N = 128; // -> 0.25-unit base cells, so the default viewport tiles ~16 across immediately
  const MAX_LEVEL = 6;
  const MAX_CELLS = 20000;
  const AUTO_REFINE_LEVEL = 1; // guaranteed extra pass over on-screen cells before hotness-driven refinement
  const MIN_SCREEN_PX_FOR_SPLIT = 18;
  const BATCH_SIZE_REPLAY = 64; // replay is near-free (library only) -- sweep fast
  const BATCH_SIZE_QUICK = 4; // quick now exercises all five families at ~200ms/table -- small batches keep the first paint under a second
  const FAST_REQUEUE_MS = 15; // back-to-back while there's a backlog (still single-flight = polite)
  const IDLE_POLL_MS = 400; // relaxed watch for viewport moves once caught up
  const VIEWPORT_MARGIN_FACTOR = 0.6; // pre-scout a little beyond the visible edge
  const DEFAULT_VIEW_HALF_SPAN = 2.0; // -> default viewport ~[-1.5, 2.5]^2 centered at (0.5, 0.5)
  const HEAT_GAUGE_CAP = 2; // the heat gauge / dots show [0, HEAT_GAUGE_CAP * eps_kill] as [0,1]

  // Fiction personas for the five attack families -- weather/predator
  // iconography per the redesign brief, loosely coordinated across games:
  // icons match breeder's phenotype creatures (js/creature.js), hues match
  // standoff's antagonist colours (js/scene.js ANTAGONISTS), names are
  // atlas's own cartography-flavoured spin on the same five entities. The
  // raw `label` (engine's verbatim attack name) is shown only in the ledger.
  // Muted "ink pigment" saturations -- vivid enough to tell apart on paper,
  // never neon.
  const PERSONAS = {
    library_replay: { hue: 210, sat: 22, label: 'library replay', icon: '\u{1F47B}', name: 'The Ghost Trail' },
    stationary: { hue: 32, sat: 58, label: 'stationary', icon: '\u{1F577}️', name: 'The Waiting Spider' },
    one_quitter_cyclic: { hue: 130, sat: 40, label: 'one-quitter cyclic', icon: '\u{1F43A}', name: 'The Relay Wolves' },
    two_quitter_periodic: { hue: 5, sat: 52, label: 'two-quitter periodic', icon: '\u{1F985}', name: 'The Twin Eagles' },
    general_periodic: { hue: 265, sat: 36, label: 'general periodic', icon: '\u{1F40D}', name: 'The Drifting Snake' },
  };

  // ---- DOM ------------------------------------------------------------
  const canvas = document.getElementById('mapCanvas');
  const ctx = canvas.getContext('2d');
  const tooltipEl = document.getElementById('tooltip');
  const heatMarkerEl = document.getElementById('heatMarker');
  const paintShimmerEl = document.getElementById('paintShimmer');
  const inspectorCardEl = document.getElementById('inspectorCard');
  const icRoamsIconEl = document.getElementById('icRoamsIcon');
  const icRoamsNameEl = document.getElementById('icRoamsName');
  const icGaugeMarkerEl = document.getElementById('icGaugeMarker');
  const actRigEl = document.getElementById('actRig');
  const actAttackEl = document.getElementById('actAttack');
  const actClaimEl = document.getElementById('actClaim');
  const sliceBtn = document.getElementById('sliceBtn');
  const slicePopover = document.getElementById('slicePopover');
  const selA = document.getElementById('selA');
  const selB = document.getElementById('selB');
  const selC = document.getElementById('selC');
  const chkFilters = document.getElementById('chkFilters');
  const btnResetView = document.getElementById('btnResetView');
  const btnPaste = document.getElementById('btnPaste');
  const pasteDialog = document.getElementById('pasteDialog');
  const pasteText = document.getElementById('pasteText');
  const pasteSlot = document.getElementById('pasteSlot');
  const pasteName = document.getElementById('pasteName');
  const pasteCancel = document.getElementById('pasteCancel');
  const pasteApply = document.getElementById('pasteApply');
  const pasteErrorEl = document.getElementById('pasteError');
  const mockBadge = document.getElementById('mockBadge');
  const hoodBtn = document.getElementById('hoodBtn');
  const hoodEl = document.getElementById('hood');
  const hoodClose = document.getElementById('hoodClose');
  const hoodBody = document.getElementById('hoodBody');
  const coachEl = document.getElementById('coach');
  const toastEl = document.getElementById('toast');
  const miniA = document.getElementById('miniA'), miniB = document.getElementById('miniB'), miniC = document.getElementById('miniC');

  // ---- math helpers -----------------------------------------------------
  function clamp4(v) { return Math.max(-4, Math.min(4, v)); }

  function sliceTable(A, B, C, x, y) {
    const t = new Array(16);
    for (let s = 0; s < 16; s++) {
      if (s === 0) { t[s] = [0, 0, 0, 0]; continue; }
      const row = new Array(4);
      for (let p = 0; p < 4; p++) {
        const a = A[s][p], b = B[s][p], c = C[s][p];
        row[p] = clamp4(a + x * (b - a) + y * (c - a));
      }
      t[s] = row;
    }
    return t;
  }

  function subsetLabel(mask) {
    if (mask === 0) return '∅';
    const parts = [];
    for (let i = 0; i < 4; i++) if (mask & (1 << i)) parts.push(i + 1);
    return '{' + parts.join(',') + '}';
  }

  // DESIGN.md: non-finite floats are sanitized server-side to a 1e9/-1e9/null
  // sentinel scheme; any score >= 1e9 means "nothing found by this attack",
  // not a real exploitability value, and must never be shown or tracked as one.
  function isSentinelScore(s) { return s == null || !isFinite(s) || s >= 1e9; }
  function formatScore(s) { return isSentinelScore(s) ? 'no result' : s.toFixed(4); }

  function hashInt(str) {
    let h = 0x811c9dc5;
    for (let i = 0; i < str.length; i++) { h ^= str.charCodeAt(i); h = Math.imul(h, 0x01000193); }
    return h >>> 0;
  }

  function mulberry32(seed) {
    let a = seed;
    return function () {
      a |= 0; a = (a + 0x6D2B79F5) | 0;
      let t = Math.imul(a ^ (a >>> 15), 1 | a);
      t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
      return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
    };
  }

  // ---- quadtree ---------------------------------------------------------
  const grid = new Map(); // key -> cell
  function cellKey(level, i, j) { return level + ':' + i + ':' + j; }
  function cellSize(level) { return DOMAIN_SIZE / (BASE_N * Math.pow(2, level)); }

  function makeCell(level, i, j) {
    const size = cellSize(level);
    const x0 = DOMAIN_MIN + i * size, y0 = DOMAIN_MIN + j * size;
    return {
      key: cellKey(level, i, j), level, i, j, x0, y0, size,
      cx: x0 + size / 2, cy: y0 + size / 2,
      childrenKeys: null,
      status: 'fog', // fog | pending-replay | pending-quick | killed | hot | unresolved
      score: null, binding_attack: null, sourceLevel: null,
      filterPass: null, filterPending: false,
      isBoundary: false, submitted: false, claimTier: null, claimStatus: null, areaCounted: false,
    };
  }

  function getOrCreateCell(level, i, j) {
    const k = cellKey(level, i, j);
    let c = grid.get(k);
    if (!c) { c = makeCell(level, i, j); grid.set(k, c); }
    return c;
  }

  function subdivide(cell) {
    if (cell.childrenKeys || cell.level >= MAX_LEVEL || grid.size > MAX_CELLS) return;
    const kids = [];
    for (let di = 0; di < 2; di++) {
      for (let dj = 0; dj < 2; dj++) {
        const child = getOrCreateCell(cell.level + 1, cell.i * 2 + di, cell.j * 2 + dj);
        kids.push(child.key);
      }
    }
    cell.childrenKeys = kids;
  }

  function ensurePath(level, i, j) {
    if (level === 0) return getOrCreateCell(0, i, j);
    const parent = ensurePath(level - 1, Math.floor(i / 2), Math.floor(j / 2));
    if (!parent.childrenKeys) subdivide(parent);
    return getOrCreateCell(level, i, j);
  }

  function cellRect(cell) { return { x0: cell.x0, y0: cell.y0, x1: cell.x0 + cell.size, y1: cell.y0 + cell.size }; }
  function rectsIntersect(a, b) { return a.x0 < b.x1 && a.x1 > b.x0 && a.y0 < b.y1 && a.y1 > b.y0; }
  function clampInt(v, lo, hi) { return Math.max(lo, Math.min(hi, v)); }

  function collectVisibleLeaves() {
    const view = currentViewRect();
    const out = [];
    function walk(cell) {
      if (!cell || !rectsIntersect(cellRect(cell), view)) return;
      if (cell.childrenKeys) {
        for (const ck of cell.childrenKeys) walk(grid.get(ck));
      } else {
        out.push(cell);
      }
    }
    const size0 = cellSize(0);
    const i0 = clampInt(Math.floor((view.x0 - DOMAIN_MIN) / size0), 0, BASE_N - 1);
    const i1 = clampInt(Math.ceil((view.x1 - DOMAIN_MIN) / size0), 0, BASE_N - 1);
    const j0 = clampInt(Math.floor((view.y0 - DOMAIN_MIN) / size0), 0, BASE_N - 1);
    const j1 = clampInt(Math.ceil((view.y1 - DOMAIN_MIN) / size0), 0, BASE_N - 1);
    for (let i = i0; i <= i1; i++) {
      for (let j = j0; j <= j1; j++) walk(grid.get(cellKey(0, i, j)));
    }
    return out;
  }

  function findLeafAt(x, y) {
    if (x < DOMAIN_MIN || x >= DOMAIN_MAX || y < DOMAIN_MIN || y >= DOMAIN_MAX) return null;
    const size0 = cellSize(0);
    const i = Math.floor((x - DOMAIN_MIN) / size0);
    const j = Math.floor((y - DOMAIN_MIN) / size0);
    let cell = grid.get(cellKey(0, i, j));
    if (!cell) return null;
    while (cell.childrenKeys) {
      const midx = cell.x0 + cell.size / 2, midy = cell.y0 + cell.size / 2;
      const di = x >= midx ? 1 : 0, dj = y >= midy ? 1 : 0;
      const child = grid.get(cellKey(cell.level + 1, cell.i * 2 + di, cell.j * 2 + dj));
      if (!child) break;
      cell = child;
    }
    return cell;
  }

  function neighborCell(cell, dx, dy) { return grid.get(cellKey(cell.level, cell.i + dx, cell.j + dy)); }

  function checkBoundary(cell) {
    if (cell.status !== 'killed') return;
    [[1, 0], [-1, 0], [0, 1], [0, -1]].forEach(([dx, dy]) => {
      const n = neighborCell(cell, dx, dy);
      if (n && n.status === 'killed' && n.binding_attack !== cell.binding_attack) {
        cell.isBoundary = true;
        n.isBoundary = true;
      }
    });
  }

  // Ensures level-0 coverage (and queues replay for any newly-created fog
  // cell) across the current viewport plus a margin, so panning/zooming
  // never outruns the base sweep. Lazy and viewport-driven -- the visible
  // fraction of the domain is all that's ever touched.
  function ensureBaseCoverage() {
    if (!anchors.A || grid.size > MAX_CELLS) return;
    const view = currentViewRect();
    const span = Math.max(view.x1 - view.x0, view.y1 - view.y0);
    const margin = span * VIEWPORT_MARGIN_FACTOR;
    const size0 = cellSize(0);
    const i0 = clampInt(Math.floor((view.x0 - margin - DOMAIN_MIN) / size0), 0, BASE_N - 1);
    const i1 = clampInt(Math.ceil((view.x1 + margin - DOMAIN_MIN) / size0), 0, BASE_N - 1);
    const j0 = clampInt(Math.floor((view.y0 - margin - DOMAIN_MIN) / size0), 0, BASE_N - 1);
    const j1 = clampInt(Math.ceil((view.y1 + margin - DOMAIN_MIN) / size0), 0, BASE_N - 1);
    for (let i = i0; i <= i1; i++) {
      for (let j = j0; j <= j1; j++) {
        const c = getOrCreateCell(0, i, j);
        if (c.status === 'fog') enqueueReplay(c);
      }
    }
  }

  // ---- camera -------------------------------------------------------------
  let cam = { x: 0.5, y: 0.5, scale: 100 };

  function worldToScreen(x, y) {
    const w = canvas.clientWidth, h = canvas.clientHeight;
    return { x: w / 2 + (x - cam.x) * cam.scale, y: h / 2 - (y - cam.y) * cam.scale };
  }
  function screenToWorld(sx, sy) {
    const w = canvas.clientWidth, h = canvas.clientHeight;
    return { x: cam.x + (sx - w / 2) / cam.scale, y: cam.y - (sy - h / 2) / cam.scale };
  }
  function currentViewRect() {
    const w = canvas.clientWidth, h = canvas.clientHeight;
    const halfW = w / 2 / cam.scale, halfH = h / 2 / cam.scale;
    return { x0: cam.x - halfW, y0: cam.y - halfH, x1: cam.x + halfW, y1: cam.y + halfH };
  }
  function intersectsViewport(cell) { return rectsIntersect(cellRect(cell), currentViewRect()); }
  function cellScreenSize(cell) { return cell.size * cam.scale; }

  function resizeCanvas() {
    const rect = canvas.getBoundingClientRect();
    const dpr = window.devicePixelRatio || 1;
    canvas.width = Math.max(1, Math.round(rect.width * dpr));
    canvas.height = Math.max(1, Math.round(rect.height * dpr));
    ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
  }
  window.addEventListener('resize', resizeCanvas);

  // ---- state ----------------------------------------------------------
  const state = {
    hottest: null,
    areaMapped: parseFloat(localStorage.getItem('atlas:areaMapped') || '0'),
    selected: null,
  };
  let anchors = { A: null, B: null, C: null };
  const anchorOptions = new Map(); // id -> {id, name, table, source, known_score}
  let filterOverlayOn = false;

  function anchorTable(cell) {
    return sliceTable(anchors.A.table, anchors.B.table, anchors.C.table, cell.cx, cell.cy);
  }
  function sliceHashId() {
    return Atlas.Api.fnv1a(anchors.A.id + '|' + anchors.B.id + '|' + anchors.C.id);
  }

  // ---- scheduler ----------------------------------------------------------
  const qReplay = [];
  const qQuick = [];
  const queuedSet = new Set();
  let schedulerBusy = false;
  let paused = false;
  let backoffTimer = null;
  let tickTimer = null;
  let consecutiveErrors = 0;

  function enqueueReplay(cell) {
    if (cell.status !== 'fog' || queuedSet.has(cell.key)) return;
    queuedSet.add(cell.key);
    cell.status = 'pending-replay';
    qReplay.push(cell.key);
  }
  function enqueueQuick(cell) {
    if (queuedSet.has(cell.key)) return;
    queuedSet.add(cell.key);
    cell.status = 'pending-quick';
    qQuick.push(cell.key);
  }

  function popBatch(queueArr, n) {
    queueArr.sort((ka, kb) => {
      const ca = grid.get(ka), cb = grid.get(kb);
      const pa = ca && intersectsViewport(ca) ? 0 : 1;
      const pb = cb && intersectsViewport(cb) ? 0 : 1;
      return pa - pb;
    });
    return queueArr.splice(0, n);
  }

  function noteHotScore(score, binding_attack, cell, level) {
    if (isSentinelScore(score)) return; // "nothing found by this attack", not a real number
    if (!state.hottest || score > state.hottest.score) {
      state.hottest = { score, binding_attack, x: cell.cx, y: cell.cy, level };
      const pos = Math.max(0, Math.min(1, score / (HEAT_GAUGE_CAP * Atlas.Api.EPS_KILL)));
      heatMarkerEl.style.left = (pos * 100) + '%';
    }
  }
  function noteAreaMapped(cell) {
    if (cell.areaCounted) return;
    cell.areaCounted = true;
    state.areaMapped += cell.size * cell.size;
    localStorage.setItem('atlas:areaMapped', String(state.areaMapped));
  }

  function maybeSubdivide(cell) {
    if (cell.level >= MAX_LEVEL || grid.size > MAX_CELLS) return;
    if (!intersectsViewport(cell)) return;
    const px = cellScreenSize(cell);
    if (px <= MIN_SCREEN_PX_FOR_SPLIT) return;
    const eps = Atlas.Api.EPS_KILL;
    const hot = cell.status === 'hot' || (cell.status === 'killed' && (eps - cell.score) < 0.35 * eps);
    const shouldSplit = cell.level < AUTO_REFINE_LEVEL || hot || cell.isBoundary;
    if (!shouldSplit) return;
    subdivide(cell);
    if (cell.childrenKeys) cell.childrenKeys.forEach((k) => enqueueReplay(grid.get(k)));
  }

  function applyResult(cell, level, r) {
    cell.sourceLevel = level;
    cell.score = r.score;
    cell.binding_attack = r.binding_attack;
    noteHotScore(r.score, r.binding_attack, cell, level); // no-ops on a sentinel score
    const sentinel = isSentinelScore(r.score);
    const killed = !sentinel && r.score < Atlas.Api.EPS_KILL;
    if (killed) {
      cell.status = 'killed';
    } else if (level === 'replay') {
      enqueueQuick(cell);
      return; // still fog-ish until quick resolves; no area credit yet
    } else if (sentinel) {
      // The attack pipeline found nothing usable at this level (empty
      // library, degenerate optimization, etc). This is NOT a survivor --
      // render it like fog, never as a hot cell.
      cell.status = 'unresolved';
    } else {
      cell.status = 'hot';
    }
    spawnPing(cell);
    noteAreaMapped(cell);
    checkBoundary(cell);
    maybeSubdivide(cell);
  }

  function scheduleTick(delay) {
    clearTimeout(tickTimer);
    tickTimer = setTimeout(runTick, delay);
  }

  async function runTick() {
    if (paused) return; // handleFetchError's backoff timer reschedules on expiry
    if (schedulerBusy) return;
    housekeeping();
    let keys, level, batchSize;
    if (qReplay.length) { batchSize = BATCH_SIZE_REPLAY; keys = popBatch(qReplay, batchSize); level = 'replay'; }
    else if (qQuick.length) { batchSize = BATCH_SIZE_QUICK; keys = popBatch(qQuick, batchSize); level = 'quick'; }
    else { scheduleTick(IDLE_POLL_MS); return; }
    const cells = keys.map((k) => grid.get(k)).filter(Boolean);
    if (!cells.length) { scheduleTick(FAST_REQUEUE_MS); return; }
    cells.forEach((c) => queuedSet.delete(c.key));
    schedulerBusy = true;
    updateShimmer();
    try {
      const tables = cells.map((c) => anchorTable(c));
      const resp = await Atlas.Api.attackBatch(tables, level);
      resp.results.forEach((r, idx) => applyResult(cells[idx], level, r));
      persistSliceCache();
      consecutiveErrors = 0;
      scheduleTick(FAST_REQUEUE_MS);
    } catch (e) {
      cells.forEach((c) => {
        c.status = 'fog';
        if (level === 'replay') enqueueReplay(c); else enqueueQuick(c);
      });
      handleFetchError(e); // sets paused + its own backoff timer that resumes scheduleTick
    } finally {
      schedulerBusy = false;
      updateShimmer();
    }
  }

  function handleFetchError(e) {
    consecutiveErrors++;
    if (e && e.isBusy) toast('The map office is swamped -- trying again shortly.');
    else if (e && e.isNetwork) toast('Lost the line to the map office -- retrying quietly.');
    else toast('Something did not read right out there: ' + (e && e.message ? e.message : 'unknown'), true);
    paused = true;
    const wait = Math.min(20000, 500 * Math.pow(2, Math.min(6, consecutiveErrors)));
    clearTimeout(backoffTimer);
    backoffTimer = setTimeout(() => {
      paused = false;
      consecutiveErrors = Math.max(0, consecutiveErrors - 1);
      scheduleTick(0);
    }, wait);
    updateShimmer();
  }

  // Called every tick (not just once at resolution time) so panning or
  // zooming into an already-resolved coarse region keeps refining it, and
  // so the base sweep keeps pace with wherever the player looks.
  function housekeeping() {
    ensureBaseCoverage();
    collectVisibleLeaves().forEach((cell) => {
      if (cell.status === 'killed' || cell.status === 'hot') maybeSubdivide(cell);
    });
    updateShimmer();
  }
  function updateShimmer() {
    const active = schedulerBusy || qReplay.length > 0 || qQuick.length > 0;
    paintShimmerEl.classList.toggle('hidden', !active);
  }

  // ---- lazy filter overlay -------------------------------------------
  // DESIGN.md: filter keys are the engine's verbatim names, treated as
  // opaque labels -- only the leading "N_" ordinal is a stable part of the
  // contract. "Barren ground" is gated on filters 1-5 only (filter 6 is a
  // heuristic equilibrium screen, not a structural gate).
  let filterInFlight = 0;
  function filterOrdinal(name) {
    const m = /^(\d+)_/.exec(name);
    return m ? parseInt(m[1], 10) : null;
  }
  function filtersOverallPass(r) {
    return Object.keys(r.filters).every((name) => {
      const ord = filterOrdinal(name);
      if (ord === null || ord >= 6) return true;
      return !!(r.filters[name] && r.filters[name].pass);
    });
  }
  function fetchVisibleFilters() {
    if (!anchors.A || !filterOverlayOn) return;
    const leaves = collectVisibleLeaves().filter((c) => c.filterPass === null && !c.filterPending);
    const todo = leaves.slice(0, Math.max(0, 6 - filterInFlight));
    todo.forEach(async (cell) => {
      cell.filterPending = true;
      filterInFlight++;
      try {
        const r = await Atlas.Api.filters(anchorTable(cell));
        cell.filterPass = filtersOverallPass(r);
      } catch (e) {
        cell.filterPass = null;
      } finally {
        cell.filterPending = false;
        filterInFlight--;
      }
    });
  }

  // ---- persistence ------------------------------------------------------
  function persistSliceCache() {
    const cells = {};
    grid.forEach((c, key) => {
      if (c.status === 'killed' || c.status === 'hot' || c.status === 'unresolved') {
        cells[key] = {
          status: c.status, score: c.score, binding_attack: c.binding_attack,
          sourceLevel: c.sourceLevel, filterPass: c.filterPass, isBoundary: c.isBoundary,
          submitted: c.submitted, claimTier: c.claimTier, claimStatus: c.claimStatus,
        };
      }
    });
    try {
      localStorage.setItem('atlas:cache:' + sliceHashId(), JSON.stringify({ cells }));
    } catch (e) { /* best-effort cache; quota errors are non-fatal */ }
  }

  function hydrateCache() {
    let raw;
    try { raw = localStorage.getItem('atlas:cache:' + sliceHashId()); } catch (e) { return; }
    if (!raw) return;
    let data;
    try { data = JSON.parse(raw); } catch (e) { return; }
    if (!data || !data.cells) return;
    Object.entries(data.cells).forEach(([key, v]) => {
      const parts = key.split(':').map(Number);
      const cell = ensurePath(parts[0], parts[1], parts[2]);
      Object.assign(cell, v);
      cell.areaCounted = true; // already counted globally when first mapped
      if (cell.status === 'killed') checkBoundary(cell);
    });
  }

  function resetSlice() {
    grid.clear();
    qReplay.length = 0;
    qQuick.length = 0;
    queuedSet.clear();
    hydrateCache();
    ensureBaseCoverage();
    closeSelection();
    scheduleTick(0);
  }

  // ---- rendering: survey-chart parchment -----------------------------------
  // Committed material (matching the portal's own atlas poster tile,
  // Games/portal/portal.css ".scene-atlas"): warm aged paper, ink-toned
  // marks, a printed grid. Unscouted ground is a thin wash of the bare
  // paper; a resolved patch is an opaque ink stamp; the act of resolving
  // itself gets a brief ink-blot ping so painting the fog reads as an
  // active survey, not a batch job finishing.
  let hatchPattern = null;
  function getHatchPattern() {
    if (hatchPattern) return hatchPattern;
    const pc = document.createElement('canvas'); pc.width = 8; pc.height = 8;
    const pctx = pc.getContext('2d');
    pctx.strokeStyle = 'rgba(58,47,34,0.4)';
    pctx.lineWidth = 1.4;
    [[0, 8, 8, 0], [-2, 2, 2, -2], [6, 10, 10, 6]].forEach(([x0, y0, x1, y1]) => {
      pctx.beginPath(); pctx.moveTo(x0, y0); pctx.lineTo(x1, y1); pctx.stroke();
    });
    hatchPattern = ctx.createPattern(pc, 'repeat');
    return hatchPattern;
  }

  function drawFog(sx, sy, sw, sh, cell) {
    const pending = cell.status !== 'fog';
    const t = performance.now() / 1000;
    const wobble = pending ? 0.05 * Math.sin(t * 4 + cell.i + cell.j) : 0;
    ctx.fillStyle = 'hsla(42,30%,' + (pending ? 62 : 68) + '%,' + (0.4 + wobble) + ')';
    ctx.fillRect(sx, sy, sw, sh);
  }

  function drawGrain(sx, sy, sw, sh, seedKey, strength) {
    const rng = mulberry32(hashInt(seedKey));
    const n = Math.round(2 + strength * 10);
    ctx.save();
    ctx.beginPath(); ctx.rect(sx, sy, sw, sh); ctx.clip();
    for (let k = 0; k < n; k++) {
      const rx = sx + rng() * sw, ry = sy + rng() * sh;
      const rr = 0.5 + rng() * Math.max(1, Math.min(sw, sh) * 0.14);
      ctx.fillStyle = rng() > 0.5 ? 'rgba(58,47,34,0.32)' : 'rgba(255,248,227,0.3)';
      ctx.beginPath(); ctx.arc(rx, ry, rr, 0, Math.PI * 2); ctx.fill();
    }
    ctx.restore();
  }

  function drawKilled(sx, sy, sw, sh, cell) {
    const info = PERSONAS[cell.binding_attack] || PERSONAS.library_replay;
    const eps = Atlas.Api.EPS_KILL;
    const margin = Math.max(0, eps - cell.score);
    const conf = Math.min(1, margin / eps); // 0 near-threshold .. 1 deep kill
    const alpha = 0.55 + 0.35 * conf;
    const light = 56 - 26 * conf; // near-threshold = pale ink wash, deep = solid stamp
    ctx.fillStyle = 'hsla(' + info.hue + ',' + info.sat + '%,' + light + '%,' + alpha + ')';
    ctx.fillRect(sx, sy, sw, sh);
    if (conf < 0.92 && sw > 5 && sh > 5) drawGrain(sx, sy, sw, sh, cell.key, 1 - conf);
    if (cell.submitted) {
      ctx.fillStyle = '#2c2318';
      ctx.beginPath(); ctx.arc(sx + sw - 6, sy + 6, 3, 0, Math.PI * 2); ctx.fill();
    }
  }

  function drawHot(sx, sy, sw, sh, cell) {
    const t = performance.now() / 1000;
    const seedPhase = (hashInt(cell.key) % 628) / 100;
    const pulse = 0.5 + 0.5 * Math.sin(t * 2.2 + seedPhase);
    ctx.fillStyle = 'hsla(36, 80%, 46%, ' + (0.4 + 0.14 * pulse) + ')';
    ctx.fillRect(sx, sy, sw, sh);
    const cx = sx + sw / 2, cy = sy + sh / 2;
    const r = Math.max(sw, sh) * (0.55 + 0.15 * pulse);
    const grad = ctx.createRadialGradient(cx, cy, 0, cx, cy, r);
    grad.addColorStop(0, 'hsla(42,95%,58%,' + (0.5 + 0.2 * pulse) + ')');
    grad.addColorStop(1, 'hsla(42,95%,50%,0)');
    ctx.fillStyle = grad;
    ctx.fillRect(sx, sy, sw, sh);
  }

  function drawCell(cell) {
    const p0 = worldToScreen(cell.x0, cell.y0 + cell.size);
    const p1 = worldToScreen(cell.x0 + cell.size, cell.y0);
    const sx = Math.min(p0.x, p1.x), sy = Math.min(p0.y, p1.y);
    const sw = Math.abs(p1.x - p0.x), sh = Math.abs(p1.y - p0.y);
    if (sw < 0.3 || sh < 0.3) return;

    if (cell.status === 'killed') drawKilled(sx, sy, sw, sh, cell);
    else if (cell.status === 'hot') drawHot(sx, sy, sw, sh, cell);
    else drawFog(sx, sy, sw, sh, cell); // fog, pending-*, and unresolved all read as unscouted

    if (filterOverlayOn && cell.filterPass === false) {
      ctx.fillStyle = getHatchPattern();
      ctx.fillRect(sx, sy, sw, sh);
    }
    if (cell.isBoundary) {
      ctx.strokeStyle = 'rgba(58,47,34,0.55)';
      ctx.lineWidth = 1;
      ctx.strokeRect(sx + 0.5, sy + 0.5, sw - 1, sh - 1);
    }
  }

  function drawSelection() {
    const cell = state.selected;
    if (!cell) return;
    const p0 = worldToScreen(cell.x0, cell.y0 + cell.size);
    const p1 = worldToScreen(cell.x0 + cell.size, cell.y0);
    const sx = Math.min(p0.x, p1.x), sy = Math.min(p0.y, p1.y);
    const sw = Math.abs(p1.x - p0.x), sh = Math.abs(p1.y - p0.y);
    const t = performance.now() / 1000;
    const pulse = 0.6 + 0.4 * Math.sin(t * 3);
    ctx.strokeStyle = 'rgba(44,35,24,' + (0.55 + 0.3 * pulse) + ')';
    ctx.lineWidth = 2;
    ctx.strokeRect(sx + 1, sy + 1, Math.max(0, sw - 2), Math.max(0, sh - 2));
  }

  // A printed survey grid in world space (so it pans/zooms with the paper,
  // not the screen), with the integer lines through the anchors drawn a
  // touch darker.
  function drawChartGrid() {
    const view = currentViewRect();
    const step = 0.5;
    const x0 = Math.floor(view.x0 / step) * step, x1 = Math.ceil(view.x1 / step) * step;
    const y0 = Math.floor(view.y0 / step) * step, y1 = Math.ceil(view.y1 / step) * step;
    ctx.save();
    ctx.lineWidth = 1;
    for (let x = x0; x <= x1; x += step) {
      ctx.strokeStyle = Math.abs(x % 1) < 1e-6 ? 'rgba(58,47,34,0.16)' : 'rgba(58,47,34,0.07)';
      const p0 = worldToScreen(x, view.y0), p1 = worldToScreen(x, view.y1);
      ctx.beginPath(); ctx.moveTo(p0.x, p0.y); ctx.lineTo(p1.x, p1.y); ctx.stroke();
    }
    for (let y = y0; y <= y1; y += step) {
      ctx.strokeStyle = Math.abs(y % 1) < 1e-6 ? 'rgba(58,47,34,0.16)' : 'rgba(58,47,34,0.07)';
      const p0 = worldToScreen(view.x0, y), p1 = worldToScreen(view.x1, y);
      ctx.beginPath(); ctx.moveTo(p0.x, p0.y); ctx.lineTo(p1.x, p1.y); ctx.stroke();
    }
    ctx.restore();
  }

  let pings = [];
  function spawnPing(cell) { pings.push({ x: cell.cx, y: cell.cy, t0: performance.now() }); }
  function drawPings() {
    const now = performance.now();
    pings = pings.filter((p) => now - p.t0 < 700);
    pings.forEach((p) => {
      const age = (now - p.t0) / 700;
      const s = worldToScreen(p.x, p.y);
      ctx.strokeStyle = 'rgba(58,47,34,' + (0.5 * (1 - age)) + ')';
      ctx.lineWidth = 1.5;
      ctx.beginPath(); ctx.arc(s.x, s.y, 4 + age * 26, 0, Math.PI * 2); ctx.stroke();
    });
  }
  // A slow rotating survey-sweep line, matching the portal poster's own
  // ".scene-atlas .sweep" exactly: a thin fading ink line from the scope's
  // center, not a glowing wedge.
  function drawChartSweep() {
    const w = canvas.clientWidth, h = canvas.clientHeight;
    const cx = w / 2, cy = h / 2;
    const maxR = Math.hypot(w, h) / 2;
    ctx.save();
    ctx.strokeStyle = 'rgba(58,47,34,0.08)';
    ctx.lineWidth = 1;
    for (let r = maxR * 0.22; r < maxR; r += maxR * 0.22) {
      ctx.beginPath(); ctx.arc(cx, cy, r, 0, Math.PI * 2); ctx.stroke();
    }
    const t = performance.now() / 1000;
    const angle = (t * 0.14) % (Math.PI * 2);
    ctx.translate(cx, cy);
    ctx.rotate(angle);
    const beam = ctx.createLinearGradient(0, 0, 0, -maxR * 0.44);
    beam.addColorStop(0, 'rgba(58,47,34,0.5)');
    beam.addColorStop(1, 'rgba(58,47,34,0)');
    ctx.strokeStyle = beam;
    ctx.lineWidth = 1.5;
    ctx.beginPath(); ctx.moveTo(0, 0); ctx.lineTo(0, -maxR * 0.44); ctx.stroke();
    ctx.restore();
  }

  function render() {
    const w = canvas.clientWidth, h = canvas.clientHeight;
    const paper = ctx.createLinearGradient(0, 0, w * 0.35, h);
    paper.addColorStop(0, '#e6d8ab');
    paper.addColorStop(0.9, '#c9b98a');
    ctx.fillStyle = paper;
    ctx.fillRect(0, 0, w, h);
    if (anchors.A && anchors.B && anchors.C) {
      drawChartGrid();
      collectVisibleLeaves().forEach(drawCell);
      drawPings();
      drawSelection();
    }
    drawChartSweep();
    requestAnimationFrame(render);
  }

  // ---- interaction ------------------------------------------------------
  let dragging = false, dragLast = null, dragMoved = false;
  canvas.addEventListener('mousedown', (e) => {
    dragging = true; dragMoved = false; dragLast = { x: e.clientX, y: e.clientY };
    canvas.classList.add('dragging');
  });
  window.addEventListener('mousemove', (e) => {
    if (dragging) {
      const dx = e.clientX - dragLast.x, dy = e.clientY - dragLast.y;
      if (Math.abs(dx) + Math.abs(dy) > 2) {
        if (!dragMoved) closeSelection(); // panning deselects -- avoids a stale floating bar
        dragMoved = true;
      }
      dragLast = { x: e.clientX, y: e.clientY };
      cam.x -= dx / cam.scale;
      cam.y += dy / cam.scale;
    }
    handleHover(e);
  });
  window.addEventListener('mouseup', () => { dragging = false; canvas.classList.remove('dragging'); });
  canvas.addEventListener('mouseleave', () => { tooltipEl.classList.add('hidden'); });
  canvas.addEventListener('wheel', (e) => {
    e.preventDefault();
    const rect = canvas.getBoundingClientRect();
    const ox = e.clientX - rect.left, oy = e.clientY - rect.top;
    const before = screenToWorld(ox, oy);
    const factor = Math.exp(-e.deltaY * 0.0016);
    cam.scale = Math.max(20, Math.min(4000, cam.scale * factor));
    const after = screenToWorld(ox, oy);
    cam.x += before.x - after.x;
    cam.y += before.y - after.y;
  }, { passive: false });
  canvas.addEventListener('click', (e) => {
    if (dragMoved) { dragMoved = false; return; }
    if (!anchors.A) return;
    const rect = canvas.getBoundingClientRect();
    const w = screenToWorld(e.clientX - rect.left, e.clientY - rect.top);
    const cell = findLeafAt(w.x, w.y);
    if (cell) selectCell(cell, e.clientX, e.clientY);
    else closeSelection();
  });

  // heat dots: 0-5 filled dots, purely visual, no numbers
  function heatDots(score) {
    const pos = Math.max(0, Math.min(1, score / (HEAT_GAUGE_CAP * Atlas.Api.EPS_KILL)));
    return Math.round(pos * 5);
  }
  function tooltipHtml(cell) {
    let icon = '\u{1F32B}️'; // fog
    if (cell.status === 'killed') icon = (PERSONAS[cell.binding_attack] || {}).icon || '\u{1F3F3}';
    else if (cell.status === 'hot') icon = '\u{1F525}';
    else if (cell.status === 'unresolved') icon = '❔';
    let dots = '';
    if ((cell.status === 'killed' || cell.status === 'hot') && !isSentinelScore(cell.score)) {
      const n = heatDots(cell.score);
      dots = '<span class="t-heat">' + [0, 1, 2, 3, 4].map((i) => '<span class="' + (i < n ? 'lit' : '') + '">●</span>').join('') + '</span>';
    }
    return '<span>' + icon + '</span>' + dots;
  }

  function handleHover(e) {
    const rect = canvas.getBoundingClientRect();
    const sx = e.clientX - rect.left, sy = e.clientY - rect.top;
    if (!anchors.A || sx < 0 || sy < 0 || sx > rect.width || sy > rect.height) {
      tooltipEl.classList.add('hidden');
      return;
    }
    const w = screenToWorld(sx, sy);
    const cell = findLeafAt(w.x, w.y);
    if (!cell) { tooltipEl.classList.add('hidden'); return; }
    tooltipEl.classList.remove('hidden');
    tooltipEl.style.left = (sx + 16) + 'px';
    tooltipEl.style.top = (sy + 12) + 'px';
    tooltipEl.innerHTML = tooltipHtml(cell);
  }

  // ---- selection / inspector card ----------------------------------------
  // "what roams there": icon + fiction name only, for the card the player
  // opens deliberately by tapping a patch (the passing tooltip stays
  // icon-only). No raw attack name, no number, anywhere on this surface.
  function roamsInfo(cell) {
    if (cell.status === 'killed') {
      const p = PERSONAS[cell.binding_attack] || PERSONAS.library_replay;
      return { icon: p.icon, name: p.name };
    }
    if (cell.status === 'hot') return { icon: '\u{1F525}', name: 'still wild' };
    if (cell.status === 'unresolved') return { icon: '❔', name: 'unclear' };
    return { icon: '\u{1F32B}️', name: 'uncharted' };
  }
  function updateCardGauge(cell) {
    if ((cell.status === 'killed' || cell.status === 'hot') && !isSentinelScore(cell.score)) {
      const pos = Math.max(0, Math.min(1, cell.score / (HEAT_GAUGE_CAP * Atlas.Api.EPS_KILL)));
      icGaugeMarkerEl.style.left = (pos * 100) + '%';
      icGaugeMarkerEl.classList.remove('hidden');
    } else {
      icGaugeMarkerEl.classList.add('hidden');
    }
  }
  function positionInspectorCard(clientX, clientY) {
    const rect = canvas.getBoundingClientRect();
    const x = clamp4range(clientX - rect.left, 90, rect.width - 90);
    const y = Math.max(clientY - rect.top - 70, 8);
    inspectorCardEl.style.left = x + 'px';
    inspectorCardEl.style.top = y + 'px';
  }
  function clamp4range(v, lo, hi) { return Math.max(lo, Math.min(hi, v)); }

  function selectCell(cell, clientX, clientY) {
    state.selected = cell;
    positionInspectorCard(clientX, clientY);
    const info = roamsInfo(cell);
    icRoamsIconEl.textContent = info.icon;
    icRoamsNameEl.textContent = info.name;
    updateCardGauge(cell);
    inspectorCardEl.classList.remove('hidden');
    dismissCoach();
    if (!hoodEl.classList.contains('hidden')) renderHood();
  }
  function closeSelection() {
    if (!state.selected) return;
    state.selected = null;
    inspectorCardEl.classList.add('hidden');
    if (!hoodEl.classList.contains('hidden')) renderHood();
  }

  actRigEl.addEventListener('click', () => {
    if (!state.selected) return;
    window.location.href = '/standoff/?table=' + Atlas.Api.b64urlEncode(anchorTable(state.selected));
  });
  actAttackEl.addEventListener('click', () => {
    if (!state.selected) return;
    window.location.href = '/sequencer/?table=' + Atlas.Api.b64urlEncode(anchorTable(state.selected));
  });
  actClaimEl.addEventListener('click', () => { claimSelected(); });

  function claimToastText(tier) {
    const stars = { exact: '⭐⭐⭐', 'numerical-wide': '⭐⭐', 'numerical-narrow': '⭐' }[tier];
    return stars ? ('Claimed ' + stars) : 'Staked -- still being read';
  }

  async function claimSelected() {
    const cell = state.selected;
    if (!cell || !anchors.A) return;
    const table = anchorTable(cell);
    try {
      const r = await Atlas.Api.postCandidate({
        table, game: 'atlas', session: Atlas.Api.sessionId(),
        provenance: {
          slice: { A: anchors.A.id, B: anchors.B.id, C: anchors.C.id },
          x: cell.cx, y: cell.cy, level: cell.level, cell: cell.key, found_via: cell.sourceLevel || null,
        },
      });
      cell.submitted = true;
      cell.claimTier = (r.record && r.record.tier) || null;
      cell.claimStatus = (r.record && r.record.status) || null;
      persistSliceCache();
      toast(claimToastText(cell.claimTier));
      if (!hoodEl.classList.contains('hidden')) renderHood();
    } catch (e) {
      toast('That claim did not take: ' + e.message, true);
      handleFetchError(e);
    }
  }

  // ---- the ledger (the ONE affordance for raw domain data) ---------------
  function renderTableHtml(table) {
    let html = '<table><tr><th>land</th><th>p1</th><th>p2</th><th>p3</th><th>p4</th></tr>';
    for (let s = 0; s < 16; s++) {
      html += '<tr><td class="coal">' + subsetLabel(s) + '</td>'
        + table[s].map((v) => '<td>' + v.toFixed(2) + '</td>').join('') + '</tr>';
    }
    return html + '</table>';
  }
  function statusWord(cell) {
    if (cell.status === 'killed') return 'killed';
    if (cell.status === 'hot') return 'survivor (still hot)';
    if (cell.status === 'unresolved') return 'no result from this attack';
    return 'not attacked yet';
  }
  function legendHtml() {
    return Object.values(PERSONAS).map((info) =>
      '<div class="legend-row"><span class="swatch" style="background:hsl(' + info.hue + ',' + info.sat + '%,45%)"></span>'
      + info.icon + ' ' + info.name + ' &mdash; ' + info.label + '</div>'
    ).join('')
      + '<div class="legend-row"><span class="swatch" style="background:hsl(220,15%,24%)"></span>\u{1F32B}️ unmapped ground</div>'
      + '<div class="legend-row">\u{1F525} a glowing patch survived the quick sweep &mdash; still hot, not a counterexample</div>';
  }
  function esc(s) {
    return String(s).replace(/[&<>"]/g, (c) => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;' }[c]));
  }
  function renderHood() {
    let html = '';
    html += '<div class="h-section"><div class="h-label">the slice in view</div>'
      + 'A: ' + esc(anchors.A.name) + '<br>B: ' + esc(anchors.B.name) + '<br>C: ' + esc(anchors.C.name) + '</div>';
    if (state.selected) {
      const cell = state.selected;
      const table = anchorTable(cell);
      html += '<div class="h-section"><div class="h-label">location on the slice</div>'
        + 'x=' + cell.cx.toFixed(4) + ', y=' + cell.cy.toFixed(4)
        + ' &middot; cell ' + cell.size.toFixed(4) + ' &middot; level ' + cell.level + '</div>';
      html += '<div class="h-section"><div class="h-label">evaluation</div>';
      if (cell.score != null) {
        const info = cell.binding_attack ? PERSONAS[cell.binding_attack] : null;
        html += 'score ' + formatScore(cell.score) + (info ? ' &mdash; ' + info.label : '')
          + ' &middot; level ' + (cell.sourceLevel || 'unattacked') + '<br>status: ' + statusWord(cell);
      } else {
        html += 'not attacked yet';
      }
      if (cell.claimTier || cell.claimStatus) {
        html += '<br>claimed &mdash; tier ' + (cell.claimTier || 'pending') + ', status ' + (cell.claimStatus || '?');
      }
      html += '</div>';
      html += '<div class="h-section"><div class="h-label">table (coalition-bitmask indexed)</div>' + renderTableHtml(table) + '</div>';
    } else {
      html += '<div class="h-section"><div class="h-label">this session</div>'
        + 'hottest score found: ' + (state.hottest ? formatScore(state.hottest.score) : 'none yet') + '<br>'
        + 'ground charted: ' + state.areaMapped.toFixed(2) + ' square units</div>';
    }
    html += '<div class="h-section"><div class="h-label">what the colors mean</div>' + legendHtml() + '</div>';
    html += '<div class="h-section"><div class="h-label">subspace restriction</div>'
      + 'Every table on this map sits on the 2-parameter plane through the three anchors above &mdash; '
      + 'chosen because a plane is what a person can see and paint, never a claim that counterexamples '
      + 'live on a plane. Every claim staked here records these anchors and the (x, y) coordinate. '
      + 'See the game README for the full statement.</div>';
    html += '<div class="h-section"><div class="h-label">what a claim is evidence of</div>'
      + 'A "killed" table failed every profile the attack battery tried at the level it was tested '
      + 'at &mdash; numerical evidence, re-verified by the server before being recorded, never a proof. '
      + 'A table that survived is evidence of bounded search effort only, never a counterexample.</div>';
    hoodBody.innerHTML = html;
  }

  hoodBtn.addEventListener('click', () => { hoodEl.classList.remove('hidden'); renderHood(); });
  hoodClose.addEventListener('click', () => hoodEl.classList.add('hidden'));

  // ---- coach mark (first-use hint, shown once) ---------------------------
  function maybeShowCoach() {
    if (localStorage.getItem('atlas:coachSeen')) return;
    coachEl.textContent = 'Tap warm ground, then rig it, attack it, or claim it.';
    coachEl.classList.remove('hidden');
    setTimeout(dismissCoach, 5200);
  }
  function dismissCoach() {
    if (coachEl.classList.contains('hidden')) return;
    coachEl.classList.add('hidden');
    localStorage.setItem('atlas:coachSeen', '1');
  }

  // ---- toast --------------------------------------------------------------
  let toastTimer = null;
  function toast(message, bad) {
    toastEl.textContent = message;
    toastEl.className = 'toast' + (bad ? ' bad' : '');
    clearTimeout(toastTimer);
    toastTimer = setTimeout(() => toastEl.classList.add('hidden'), 4200);
  }

  // ---- thumbnails (a cheap honest visual fingerprint of a table) ---------
  function renderThumbnail(table, canvasEl) {
    const c2 = canvasEl.getContext('2d');
    const w = canvasEl.width, h = canvasEl.height;
    const cw = w / 4, ch = h / 4;
    for (let r = 0; r < 4; r++) {
      for (let col = 0; col < 4; col++) {
        const idx = r * 4 + col; // coalition bitmask index 0..15
        const row = table[idx];
        const mag = row.reduce((a, b) => a + Math.abs(b), 0) / 4;
        const sign = row.reduce((a, b) => a + b, 0);
        const hue = sign >= 0 ? 200 : 8;
        const light = 20 + Math.min(55, mag * 14);
        c2.fillStyle = 'hsl(' + hue + ',55%,' + light + '%)';
        c2.fillRect(col * cw, r * ch, cw, ch);
      }
    }
  }
  function refreshThumbnails() {
    if (!anchors.A) return;
    renderThumbnail(anchors.A.table, miniA); renderThumbnail(anchors.A.table, popoverThumb('A'));
    renderThumbnail(anchors.B.table, miniB); renderThumbnail(anchors.B.table, popoverThumb('B'));
    renderThumbnail(anchors.C.table, miniC); renderThumbnail(anchors.C.table, popoverThumb('C'));
  }
  function popoverThumb(slot) {
    return document.querySelector('.slot-row[data-slot="' + slot + '"] .thumb');
  }

  // ---- anchor selection / slice picker ------------------------------------
  function populateSelects() {
    [selA, selB, selC].forEach((sel) => {
      const currentVal = sel.value;
      sel.innerHTML = '';
      const curatedGroup = document.createElement('optgroup'); curatedGroup.label = 'storied lands';
      const candGroup = document.createElement('optgroup'); candGroup.label = 'staked lands';
      const customGroup = document.createElement('optgroup'); customGroup.label = 'pasted lands';
      anchorOptions.forEach((opt) => {
        const o = document.createElement('option'); o.value = opt.id; o.textContent = opt.name;
        if (opt.source === 'curated') curatedGroup.appendChild(o);
        else if (opt.source === 'candidate') candGroup.appendChild(o);
        else customGroup.appendChild(o);
      });
      if (customGroup.children.length) sel.appendChild(customGroup);
      if (curatedGroup.children.length) sel.appendChild(curatedGroup);
      if (candGroup.children.length) sel.appendChild(candGroup);
      if (currentVal && anchorOptions.has(currentVal)) sel.value = currentVal;
    });
  }

  function applyUrlOverrides() {
    const p = new URLSearchParams(location.search);
    const overrides = {};
    ['a', 'b', 'c'].forEach((key, idx) => {
      const raw = p.get(key) || (idx === 0 ? p.get('table') : null);
      if (!raw) return;
      try {
        const table = Atlas.Api.b64urlDecode(raw);
        const id = 'url:' + key + ':' + Atlas.Api.fnv1a(raw);
        anchorOptions.set(id, { id, name: 'from URL (' + key.toUpperCase() + ')', table, source: 'custom' });
        overrides[key] = id;
      } catch (e) {
        toast('That map link did not read.', true);
      }
    });
    return overrides;
  }

  function chooseDefaults(overrides) {
    overrides = overrides || {};
    const ids = [...anchorOptions.keys()];
    const seedId = ids.find((id) => /solan/i.test(anchorOptions.get(id).name)) || ids[0];
    const others = ids.filter((id) => id !== seedId);
    const fallbacks = { a: seedId, b: others[0] || seedId, c: others[1] || others[0] || seedId };
    [['a', selA], ['b', selB], ['c', selC]].forEach(([key, sel]) => {
      const val = overrides[key] || fallbacks[key];
      if (val) sel.value = val;
    });
  }

  async function loadAnchorSources() {
    try {
      const [curatedResp, candResp] = await Promise.all([
        Atlas.Api.getCuratedTables(),
        Atlas.Api.getCandidates(50),
      ]);
      (curatedResp.tables || []).forEach((t) => anchorOptions.set(t.id, {
        id: t.id, name: t.name || t.id, table: t.table, source: 'curated', known_score: t.known_score,
      }));
      (candResp.candidates || []).forEach((c) => anchorOptions.set(c.id, {
        id: c.id, name: 'staked ' + c.id.slice(0, 8) + (c.game ? ' [' + c.game + ']' : ''),
        table: c.table, source: 'candidate',
      }));
    } catch (e) {
      handleFetchError(e);
    }
    const overrides = applyUrlOverrides();
    populateSelects();
    chooseDefaults(overrides);
    applySelection();
  }

  function applySelection() {
    const a = anchorOptions.get(selA.value), b = anchorOptions.get(selB.value), c = anchorOptions.get(selC.value);
    if (!a || !b || !c) return;
    anchors = { A: a, B: b, C: c };
    refreshThumbnails();
    resetSlice();
  }
  [selA, selB, selC].forEach((sel) => sel.addEventListener('change', applySelection));

  function applyPaste() {
    const raw = pasteText.value.trim();
    pasteErrorEl.classList.add('hidden');
    let table;
    try {
      table = JSON.parse(raw);
    } catch (e) {
      try { table = Atlas.Api.b64urlDecode(raw); } catch (e2) {
        pasteErrorEl.textContent = 'Could not read that as a table or a map link.';
        pasteErrorEl.classList.remove('hidden');
        return;
      }
    }
    if (!Array.isArray(table) || table.length !== 16 || table.some((r) => !Array.isArray(r) || r.length !== 4)) {
      pasteErrorEl.textContent = 'Expected a 16x4 table (coalition-bitmask indexed).';
      pasteErrorEl.classList.remove('hidden');
      return;
    }
    table = table.map((row, idx) => idx === 0 ? [0, 0, 0, 0] : row.map((v) => clamp4(Number(v) || 0)));
    const name = pasteName.value.trim() || 'a pasted land';
    const id = 'custom:' + Atlas.Api.fnv1a(JSON.stringify(table) + name + Date.now());
    anchorOptions.set(id, { id, name, table, source: 'custom' });
    const slot = pasteSlot.value;
    const sel = { A: selA, B: selB, C: selC }[slot];
    populateSelects();
    sel.value = id;
    pasteDialog.classList.add('hidden');
    pasteText.value = '';
    applySelection();
  }

  // ---- wiring / init --------------------------------------------------
  function wireUi() {
    chkFilters.addEventListener('change', () => { filterOverlayOn = chkFilters.checked; });
    btnResetView.addEventListener('click', () => {
      cam.x = 0.5; cam.y = 0.5;
      cam.scale = Math.min(canvas.clientWidth, canvas.clientHeight) / (2 * DEFAULT_VIEW_HALF_SPAN);
    });
    sliceBtn.addEventListener('click', (e) => {
      e.stopPropagation();
      slicePopover.classList.toggle('hidden');
    });
    document.addEventListener('click', (e) => {
      if (!slicePopover.classList.contains('hidden') && !slicePopover.contains(e.target) && e.target !== sliceBtn) {
        slicePopover.classList.add('hidden');
      }
    });
    btnPaste.addEventListener('click', () => pasteDialog.classList.remove('hidden'));
    pasteCancel.addEventListener('click', () => pasteDialog.classList.add('hidden'));
    pasteApply.addEventListener('click', applyPaste);
    if (Atlas.Api.MOCK) mockBadge.classList.remove('hidden');
  }

  function init() {
    resizeCanvas();
    cam = { x: 0.5, y: 0.5, scale: Math.min(canvas.clientWidth, canvas.clientHeight) / (2 * DEFAULT_VIEW_HALF_SPAN) };
    wireUi();
    loadAnchorSources(); // auto-picks defaults, kicks off the sweep -- zero configuration required
    requestAnimationFrame(render);
    setInterval(fetchVisibleFilters, 500);
    setTimeout(maybeShowCoach, 700);
  }

  document.addEventListener('DOMContentLoaded', init);
})();
