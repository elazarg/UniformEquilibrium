// Orchestration. Full diegesis on the play surface: no game-theory words, no
// raw numbers, no coalition tables anywhere except inside the ledger panel
// (#hoodBtn/#hood), the portal's one consistent out-of-fiction door (see
// Games/DESIGN.md's "Full diegesis" rule). A single always-visible goal
// element (#goal) is the one exception to "nothing persistent on the play
// surface" per DESIGN.md's "the goal is always visible" rule — it stays
// fiction-pure (pen/lab vocabulary only, a ring gauge instead of a number).

import { Api, ApiError, IS_MOCK } from './api.js';
import { spawnCandidates, LATTICE_STEP } from './genetics.js';
import { renderCreatureSVG, tierOf, EPS_KILL, PREDATOR_ICON } from './creature.js';
import { loadState, saveState, clearState, renderLineageStrip } from './lineage.js';
import { decodeTableParam, hashTable, blankTable } from './util.js';

const el = (id) => document.getElementById(id);
const grid = el('grid');
const husksEl = el('husks');
const breedBtn = el('breedBtn');
const coachEl = el('coach');
const lineageEl = el('lineage');
const goalEl = el('goal');
const goalTextEl = el('goalText');
const goalRingFillEl = el('goalRingFill');
const hoodBtn = el('hoodBtn');
const hoodEl = el('hood');
const hoodCloseBtn = el('hoodClose');
const hoodStatsEl = el('hoodStats');
const hoodSpecimensEl = el('hoodSpecimens');
const hoodDeathsEl = el('hoodDeaths');
const resetBtn = el('resetBtn');
const mockBadge = el('mockBadge');
const labCounter = el('labCounter');
const toastEl = el('toast');

const COACH_KEY = 'breeder.coachSeen';
const HUSK_CAP = 14;
const GOAL_DEFAULT = 'breed one the lab will take';
const GOAL_CELEBRATE = 'the lab wants more';
const RING_R = 13;
const RING_C = 2 * Math.PI * RING_R;

const state = {
  generation: 0,
  offspring: [], // [{id, table, score, bindingAttack, op, submitted}]
  selectedParents: [], // up to 2 offspring ids
  moves: [], // [{generation, op, parentHashes}]
  championPath: [], // [{table, score, generation, op}]
  lastDeaths: {},
  bestSinceLastLab: null, // strongest unclaimed score this session; goal-ring progress
  busy: false,
};

let submittedHashSet = new Set();

// -------------------------------------------------------------- storage --

function persist() {
  saveState({
    generation: state.generation,
    offspring: state.offspring,
    moves: state.moves,
    championPath: state.championPath,
    submittedHashes: [...submittedHashSet],
    bestSinceLastLab: state.bestSinceLastLab,
  });
}

// ---------------------------------------------------------------- toast --

function showToast(message, kind = '') {
  toastEl.textContent = message;
  toastEl.className = `toast show${kind ? ' ' + kind : ''}`;
  clearTimeout(showToast._t);
  showToast._t = setTimeout(() => {
    toastEl.className = 'toast hidden';
  }, 4200);
}

function errMsg(e) {
  if (e instanceof ApiError) return e.message;
  return 'Something went wrong.';
}

// A real score that isn't the "nothing found" sentinel (DESIGN.md: non-finite
// floats are sanitized to 1e9 server-side).
function isRealScore(s) {
  return s != null && s < 1e9;
}

// ------------------------------------------------------------- coach mark --

function maybeShowCoach() {
  if (localStorage.getItem(COACH_KEY)) return;
  coachEl.textContent = 'pick the ones you like';
  coachEl.classList.remove('hidden');
  setTimeout(dismissCoach, 6000);
}

function dismissCoach() {
  if (coachEl.classList.contains('hidden')) return;
  coachEl.classList.add('hidden');
  localStorage.setItem(COACH_KEY, '1');
}

// -------------------------------------------------------------- husks -----

function renderHusks(deaths) {
  state.lastDeaths = deaths || {};
  const total = Object.values(state.lastDeaths).reduce((a, b) => a + b, 0);
  husksEl.innerHTML = '\u{1F940}'.repeat(Math.min(total, HUSK_CAP)); // 🥀 wilted flower
}

// ------------------------------------------------------------ lab pips ----

function renderLabPips() {
  const n = submittedHashSet.size;
  if (!n) {
    labCounter.classList.add('hidden');
    labCounter.textContent = '';
    return;
  }
  labCounter.title = `${n} specimen${n === 1 ? '' : 's'} taken to the lab this session`;
  labCounter.textContent = '\u{1F9EA}'.repeat(Math.min(n, 8)); // 🧪
  labCounter.classList.remove('hidden');
}

// ---------------------------------------------------------------- goal ----
// Always-visible in-fiction objective (DESIGN.md "the goal is always
// visible"). Progress is a threshold ring only — never a number — tracking
// this session's strongest specimen not yet taken. A successful submission
// celebrates the ring, then re-arms for the next one.

function updateGoalRing(fraction) {
  const f = Math.max(0, Math.min(1, fraction));
  goalRingFillEl.style.strokeDasharray = `${RING_C}`;
  goalRingFillEl.style.strokeDashoffset = `${RING_C * (1 - f)}`;
  goalEl.classList.toggle('near', f >= 1);
}

// Recomputes the ring from the strongest currently-displayed, not-yet-taken
// specimen. Never touches the goal text — that's celebrateGoal's job alone,
// so a celebration message isn't clobbered mid-display.
function updateGoalProgress() {
  for (const o of state.offspring) {
    if (o.submitted || !isRealScore(o.score)) continue;
    if (state.bestSinceLastLab == null || o.score > state.bestSinceLastLab) {
      state.bestSinceLastLab = o.score;
    }
  }
  updateGoalRing(state.bestSinceLastLab == null ? 0 : state.bestSinceLastLab / EPS_KILL);
}

function celebrateGoal() {
  goalEl.classList.add('celebrate');
  goalTextEl.textContent = GOAL_CELEBRATE;
  state.bestSinceLastLab = null;
  updateGoalProgress();
  clearTimeout(celebrateGoal._t);
  celebrateGoal._t = setTimeout(() => {
    goalEl.classList.remove('celebrate');
    goalTextEl.textContent = GOAL_DEFAULT;
  }, 3200);
}

// -------------------------------------------------------------- filters ---

function recordDeath(deaths, res, networked) {
  if (networked) {
    deaths['_unreachable'] = (deaths['_unreachable'] || 0) + 1;
    return;
  }
  const f = (res && res.filters) || {};
  const failedName = Object.keys(f).find((k) => f[k] && f[k].pass === false && !k.startsWith('all_'));
  deaths[failedName || 'unknown'] = (deaths[failedName || 'unknown'] || 0) + 1;
}

async function safeFilters(table) {
  try {
    const res = await Api.filters(table);
    return { res, networked: false };
  } catch (e) {
    return { res: null, networked: true, error: e };
  }
}

// Tries seed tables directly first (curated stock, an injected ?table=, or
// the parents a player just picked), then fills remaining slots by spawning
// mutants/crossovers and checking each via POST /api/filters, discarding
// illegal ones silently. Stops early on a network failure.
async function generateLegalOffspring(seedTables, spawnPool, maxSlots = 9) {
  const deaths = {};
  const legal = [];
  let unreachable = false;

  if (seedTables && seedTables.length) {
    for (const t of seedTables) {
      if (legal.length >= maxSlots) break;
      const { res, networked } = await safeFilters(t);
      if (networked) {
        unreachable = true;
        break;
      }
      if (res.pass) legal.push(t);
      else recordDeath(deaths, res, false);
    }
  }

  let attempts = 0;
  const maxAttempts = 400;
  const seed = Date.now() ^ Math.floor(Math.random() * 1e9);
  while (!unreachable && legal.length < maxSlots && attempts < maxAttempts) {
    const need = maxSlots - legal.length;
    const batch = spawnCandidates(spawnPool, seed + attempts, need);
    attempts += batch.length;
    const results = await Promise.all(batch.map((t) => safeFilters(t)));
    for (let i = 0; i < batch.length; i++) {
      if (legal.length >= maxSlots) break;
      const { res, networked } = results[i];
      if (networked) {
        unreachable = true;
        break;
      }
      if (res.pass) legal.push(batch[i]);
      else recordDeath(deaths, res, false);
    }
  }
  return { legal, deaths, attempts, unreachable };
}

// ---------------------------------------------------------------- champ ---

function updateChampion(offspring) {
  let improved = false;
  for (const o of offspring) {
    if (!isRealScore(o.score)) continue;
    const best = state.championPath[state.championPath.length - 1];
    if (!best || o.score > best.score) {
      state.championPath.push({ table: o.table, score: o.score, generation: state.generation, op: o.op });
      improved = true;
    }
  }
  if (improved) renderLineage();
}

function renderLineage() {
  renderLineageStrip(lineageEl, state.championPath, (table, score) =>
    renderCreatureSVG(table, { score })
  );
}

// ----------------------------------------------------------- auto-submit --

async function checkAutoSubmit(offspring) {
  for (const o of offspring) {
    if (!isRealScore(o.score) || o.score <= EPS_KILL) continue;
    const h = hashTable(o.table);
    if (submittedHashSet.has(h)) continue;
    submittedHashSet.add(h);
    renderLabPips();
    try {
      const standard = await Api.attack(o.table, 'standard');
      if (isRealScore(standard && standard.score) && standard.score > EPS_KILL) {
        const provenance = {
          moves: state.moves.slice(),
          generation: state.generation,
          op: o.op,
          quick_score: o.score,
          standard_score: standard.score,
          // DESIGN.md subspace-restriction clause: mutation/crossover writes
          // are confined to a 1/8 lattice (see genetics.js). Stamped on every
          // submission so the research side knows which region was searched;
          // never treat this as coverage of the unrestricted table space.
          subspace: { lattice: LATTICE_STEP },
        };
        await Api.submitCandidate(o.table, provenance);
        o.submitted = true;
        markSubmitted(o.id);
        renderLeadingBadge();
        celebrateGoal();
        showToast('This one is being taken to the lab.', 'good');
      }
    } catch (e) {
      showToast(errMsg(e), 'warn');
    }
    persist();
  }
}

function markSubmitted(id) {
  const cell = grid.querySelector(`.cell[data-id="${id}"] .lab-badge`);
  if (cell) cell.classList.add('show');
}

// ------------------------------------------------------------ generation --

function nextId() {
  return Math.random().toString(36).slice(2, 10);
}

async function runGeneration({ seedTables = [], spawnPool, opLabel }) {
  state.busy = true;
  grid.classList.add('busy');
  try {
    const { legal, deaths, unreachable } = await generateLegalOffspring(seedTables, spawnPool);
    renderHusks(deaths);
    if (unreachable) showToast('The pen went quiet for a moment.', 'warn');

    let scores = legal.map(() => null);
    if (legal.length) {
      try {
        const resp = await Api.attackBatch(legal, 'quick');
        scores = resp.results;
      } catch (e) {
        showToast(errMsg(e), 'warn');
      }
    }

    if (opLabel !== 'seed') state.generation += 1;
    state.offspring = legal.map((table, i) => ({
      id: nextId(),
      table,
      score: scores[i] ? scores[i].score : null,
      bindingAttack: scores[i] ? scores[i].binding_attack : null,
      op: opLabel,
      submitted: false,
    }));
    state.selectedParents = [];
    renderGrid();
    updateChampion(state.offspring);
    updateGoalProgress();
    persist();
    checkAutoSubmit(state.offspring);
  } catch (e) {
    showToast(errMsg(e), 'warn');
  } finally {
    state.busy = false;
    grid.classList.remove('busy');
  }
}

// ----------------------------------------------------------- selection ---

function toggleSelect(id) {
  dismissCoach();
  const idx = state.selectedParents.indexOf(id);
  if (idx >= 0) {
    state.selectedParents.splice(idx, 1);
  } else {
    if (state.selectedParents.length >= 2) state.selectedParents.shift();
    state.selectedParents.push(id);
  }
  renderGrid();
  updateBreedFab();
}

function updateBreedFab() {
  const n = state.selectedParents.length;
  breedBtn.classList.toggle('hidden', n === 0);
  breedBtn.classList.toggle('show', n > 0);
  breedBtn.textContent = n === 2 ? 'cross-breed' : n === 1 ? 'breed' : '';
}

// The strongest not-yet-taken specimen currently on display — the per-cell
// aspiration cue that pairs with the goal ring.
function computeLeadingId() {
  let bestId = null;
  let bestScore = -Infinity;
  for (const o of state.offspring) {
    if (o.submitted || !isRealScore(o.score)) continue;
    if (o.score > bestScore) {
      bestScore = o.score;
      bestId = o.id;
    }
  }
  return bestId;
}

function renderLeadingBadge() {
  const leadingId = computeLeadingId();
  grid.querySelectorAll('.cell').forEach((cell) => {
    const badge = cell.querySelector('.leading-badge');
    if (badge) badge.classList.toggle('show', cell.dataset.id === leadingId);
  });
}

function renderGrid() {
  grid.innerHTML = '';
  const leadingId = computeLeadingId();
  state.offspring.forEach((o) => {
    const cell = document.createElement('div');
    cell.className = 'cell' + (state.selectedParents.includes(o.id) ? ' selected' : '');
    cell.dataset.id = o.id;
    cell.innerHTML = `
      <div class="creature-wrap">${renderCreatureSVG(o.table, { score: o.score, bindingAttack: o.bindingAttack })}</div>
      <div class="lab-badge${o.submitted ? ' show' : ''}" title="the lab wants this one">\u{1F9EA}</div>
      <div class="leading-badge${o.id === leadingId ? ' show' : ''}" title="the strongest so far">&#x2726;</div>`;
    cell.addEventListener('click', () => toggleSelect(o.id));
    grid.appendChild(cell);
  });
}

// ----------------------------------------------------------------- hood --

function tierWord(score) {
  const t = tierOf(score);
  return t === 'thriving' ? 'thriving' : t === 'wary' ? 'wary' : t === 'critical' ? 'about to fall' : 'unscored';
}

async function openHood() {
  hoodEl.classList.remove('hidden');
  hoodStatsEl.innerHTML = '<div class="num-grid"><span class="k">reaching the lab…</span></div>';
  try {
    const s = await Api.stats();
    hoodStatsEl.innerHTML = `
      <div class="k">candidates recorded</div><div class="v">${s.candidates}</div>
      <div class="k">confirmed kills</div><div class="v">${s.kills}</div>
      <div class="k">library profiles</div><div class="v">${s.library_profiles}</div>
      <div class="k">best score seen</div><div class="v">${s.best_score != null ? s.best_score.toFixed(4) : '—'}</div>
      <div class="k">this pen's generation</div><div class="v">${state.generation}</div>`;
  } catch (e) {
    hoodStatsEl.innerHTML = `<div class="k">${errMsg(e)}</div>`;
  }

  hoodSpecimensEl.innerHTML =
    '<div class="section-label">this pen</div>' +
    state.offspring
      .map((o) => {
        const scoreText = isRealScore(o.score) ? o.score.toFixed(4) : 'unscored';
        const attackText = o.bindingAttack ? o.bindingAttack.replace(/_/g, ' ') : '—';
        const tableJson = JSON.stringify(o.table.map((row) => row.map((v) => Math.round(v * 1000) / 1000)));
        return `<div class="specimen-row">
          <div class="thumb">${renderCreatureSVG(o.table, { score: o.score, bindingAttack: o.bindingAttack })}</div>
          <div class="fields">
            <span class="num">score ${scoreText} &middot; ${tierWord(o.score)}</span>
            <span>binding attack: ${attackText}${o.submitted ? ' <span class="lab">&middot; taken to the lab</span>' : ''}</span>
            <details><summary>raw table</summary><pre>${tableJson}</pre></details>
          </div>
        </div>`;
      })
      .join('');

  const deathEntries = Object.entries(state.lastDeaths);
  hoodDeathsEl.innerHTML = deathEntries.length
    ? '<div class="section-label">this round\'s rejections</div>' +
      deathEntries
        .map(([k, v]) => {
          const label = k === '_unreachable' ? 'connection lost' : k.replace(/^\d+_/, '').replace(/_/g, ' ');
          return `<div class="death-row"><span>${label}</span><span>${v}</span></div>`;
        })
        .join('')
    : '';
}

function closeHood() {
  hoodEl.classList.add('hidden');
}

// -------------------------------------------------------------- bootstrap -

async function bootstrap() {
  mockBadge.classList.toggle('hidden', !IS_MOCK);

  const saved = loadState();
  if (saved && saved.offspring && saved.offspring.length) {
    state.generation = saved.generation;
    state.offspring = saved.offspring;
    state.moves = saved.moves || [];
    state.championPath = saved.championPath || [];
    state.bestSinceLastLab = saved.bestSinceLastLab ?? null;
    submittedHashSet = new Set(saved.submittedHashes || []);
    renderGrid();
    renderLineage();
    renderLabPips();
    updateGoalProgress();
    maybeShowCoach();
    return;
  }

  const params = new URLSearchParams(location.search);
  const injected = params.get('table') ? decodeTableParam(params.get('table')) : null;

  let pool = [];
  try {
    const curated = await Api.curated();
    pool = (curated.tables || []).map((t) => t.table);
  } catch (e) {
    showToast('The pen is quiet — starting from scratch.', 'warn');
  }
  const seeds = injected ? [injected, ...pool] : pool;
  const spawnPool = seeds.length ? seeds : [blankTable()];
  await runGeneration({ seedTables: seeds, spawnPool, opLabel: 'seed' });
  maybeShowCoach();
}

breedBtn.addEventListener('click', () => {
  const parents = state.selectedParents
    .map((id) => state.offspring.find((o) => o.id === id))
    .filter(Boolean);
  if (!parents.length) return;
  const label = parents.length === 2 ? 'crossbreed' : 'mutate';
  state.moves.push({
    generation: state.generation,
    op: label,
    parentHashes: parents.map((p) => hashTable(p.table)),
  });
  const tables = parents.map((p) => p.table);
  runGeneration({ seedTables: [], spawnPool: tables, opLabel: label });
});

hoodBtn.addEventListener('click', openHood);
hoodCloseBtn.addEventListener('click', closeHood);
hoodEl.addEventListener('click', (e) => {
  if (e.target === hoodEl) closeHood();
});
document.addEventListener('keydown', (e) => {
  if (e.key === 'Escape') closeHood();
});

resetBtn.addEventListener('click', () => {
  if (!confirm('Start a fresh pen? The current litter and lineage will be cleared.')) return;
  clearState();
  state.generation = 0;
  state.offspring = [];
  state.selectedParents = [];
  state.moves = [];
  state.championPath = [];
  state.lastDeaths = {};
  state.bestSinceLastLab = null;
  submittedHashSet = new Set();
  lineageEl.innerHTML = '';
  husksEl.innerHTML = '';
  clearTimeout(celebrateGoal._t);
  goalEl.classList.remove('celebrate');
  goalTextEl.textContent = GOAL_DEFAULT;
  updateGoalRing(0);
  closeHood();
  bootstrap();
});

bootstrap();
