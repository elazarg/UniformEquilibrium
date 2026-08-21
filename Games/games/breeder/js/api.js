// Wire access to the portal server, per Games/DESIGN.md "HTTP API". Every
// recorded score in this game comes from here (or, under ?mock=1, from the
// canned stand-ins below) — client math elsewhere (tablemath.js, creature.js)
// only drives feel and legality pre-checks, never the ledger.

import { uuid, hashTable, mulberry32, clamp } from './util.js';
import { mockFilters } from './filters-mock.js';
import { viableOwnersOf, coreOf, r } from './tablemath.js';

export const IS_MOCK = new URLSearchParams(location.search).get('mock') === '1';

export const SESSION_ID = (() => {
  const key = 'breeder.session';
  let s = sessionStorage.getItem(key);
  if (!s) {
    s = uuid();
    sessionStorage.setItem(key, s);
  }
  return s;
})();

// Message strings are player-facing (shown in toasts), so they stay in the
// pen/lab fiction and never mention HTTP status codes or server jargon; the
// real status and any server-supplied detail are kept on the error object
// for the hood panel, never printed to the play surface.
export class ApiError extends Error {
  constructor(message, status, detail) {
    super(message);
    this.status = status;
    this.detail = detail;
  }
}

async function realFetch(path, opts) {
  let res;
  try {
    res = await fetch(path, opts);
  } catch (e) {
    throw new ApiError('The lab went quiet — no connection.', 0);
  }
  if (res.status === 503) {
    throw new ApiError('The lab is busy right now — try again shortly.', 503);
  }
  if (!res.ok) {
    let detail = null;
    try {
      const j = await res.json();
      if (j && j.error) detail = j.error;
    } catch (e) {
      /* body wasn't JSON */
    }
    throw new ApiError('Something in the lab hiccuped.', res.status, detail);
  }
  return res.json();
}

// ---- mock mode -------------------------------------------------------

const ATTACK_NAMES = [
  'library_replay',
  'stationary',
  'one_quitter_cyclic',
  'two_quitter_periodic',
  'general_periodic',
];

function mockAttackResult(table, level) {
  const rng = mulberry32(hashTable(table) ^ 0x9e3779b9);
  const owners = viableOwnersOf(table).length;
  const core = coreOf(table).length;
  const diag = [0, 1, 2, 3].map((i) => r(table, 1 << i, i));
  const spread = Math.max(...diag) - Math.min(...diag);
  let base = 0.01 + 0.02 * owners + 0.015 * core + 0.01 * spread;
  base = clamp(base * (0.5 + rng()), 0, 0.5);
  const breakdown = {};
  let best = Infinity;
  let bindingAttack = ATTACK_NAMES[0];
  for (const name of ATTACK_NAMES) {
    const ex = base * (0.6 + rng() * 0.9);
    breakdown[name] = { exploitability: ex, profile: { period: 1, hazards: [[0.1, 0.1, 0.1, 0.1]] } };
    if (ex < best) {
      best = ex;
      bindingAttack = name;
    }
  }
  return {
    score: best,
    binding_attack: bindingAttack,
    level,
    elapsed: level === 'quick' ? 0.05 : level === 'standard' ? 0.3 : 0.01,
    breakdown,
  };
}

// Faithful conversions (player-1-indexed {S} keys -> 0-indexed 16x4 arrays)
// of the Solan-Vieille seed and the three chain-best tables recorded in
// Experiments/singleton_collision_candidate_search/results.json, copied here
// as literal data (read-only source) so ?mock=1 has real seed stock without
// a server.
const MOCK_CURATED = [
  {
    id: 'seed-solan-vieille',
    name: 'Solan–Vieille (2001) seed',
    known_score: 2.5823483152498383e-5,
    note: 'Boundary calibration table: admits a period-2 two-quitter approximate equilibrium.',
    table: [
      [0, 0, 0, 0],
      [1, 4, 0, 0],
      [4, 1, 0, 0],
      [1, 1, 1, 1],
      [0, 0, 1, 4],
      [1, 1, 1, 0],
      [0, 1, 1, 1],
      [1, 0, 0, 0],
      [0, 0, 4, 1],
      [1, 0, 1, 1],
      [1, 1, 0, 1],
      [0, 1, 0, 0],
      [1, 1, 1, 1],
      [0, 0, 0, 1],
      [0, 0, 1, 0],
      [-1, -1, -1, -1],
    ],
  },
  {
    id: 'chain-40-best',
    name: 'Chain 40 best',
    known_score: 0.026251910874971363,
    note: 'Search-time survivor; killed under deep re-attack (two_quitter_periodic).',
    table: [
      [0, 0, 0, 0],
      [0.6433857932106202, 4, 0, 0],
      [4, 1.2077010962635069, -0.03543777681974557, 0],
      [1, 0.8341100811933869, 1.8202783832855616, 1.1062624333237796],
      [0.1262970589396285, 0, 1, 3.916381382380527],
      [1, 1, 1.1429015789967056, 0.3775733506822927],
      [-0.0264967231243467, 0.7416384263528223, 0.9930427623384119, 1],
      [1, 0, 0, 0.07609981099854121],
      [0, 0, 4, 1],
      [1.2457816851726764, -0.540199813292627, 1, 2.413944554714562],
      [1.3499021017752009, 1.067926723495971, 0.08445384454650513, 1],
      [0.618379623653601, 0.9800753644600574, 0, 0.31610438121586343],
      [0.5848968658753035, 1, 0.9470614774004995, 0.8038229881704566],
      [0.3405228058292062, 0.017261887144623653, 0, 2.021165202639615],
      [0, -0.4350523412460954, 1, 0],
      [-0.8398628076663845, -1, -1.0079554720454458, -1],
    ],
  },
  {
    id: 'chain-41-best',
    name: 'Chain 41 best',
    known_score: 0.0301031043470954,
    note: 'Search-time survivor; killed under deep re-attack (two_quitter_periodic).',
    table: [
      [0, 0, 0, 0],
      [0.14088578039453103, 4, 0.2560742395197606, 0],
      [4, 1, -0.06963924292612295, 1.6113084111726972],
      [0.8760231951868297, 1.1697634473561809, 1, 0.3358666769060037],
      [0, 0, 1, 3.2264726094111436],
      [1, 2.5290258166317976, 1, -0.2517898506886465],
      [-0.4532823345990258, 1, 0.5276521457784837, 1],
      [1, 0, 0, 0],
      [-0.4875696888253538, 0, 4, 1],
      [1, 0, 0.948270402596473, 1.0939966163996537],
      [1.53177402366574, 0.8222256392162389, 0, 1],
      [-0.5921605700818082, 0.3252691566026462, 0, 0],
      [1, 1.2319717635935268, 1.3697978652839313, 1],
      [0, 0, -0.20229448987368764, 0.9060398130834263],
      [0, 0, 1.0784815917320643, 0.05041534064924471],
      [-1.155202738084032, -0.42152506637299897, -1, -1.2762473268160173],
    ],
  },
  {
    id: 'chain-42-best',
    name: 'Chain 42 best',
    known_score: 0.027203021120874915,
    note: 'Search-time survivor; killed under deep re-attack (two_quitter_periodic).',
    table: [
      [0, 0, 0, 0],
      [1, 4, 0, 0],
      [4, 1, -0.5042531300894738, -0.21927599765558553],
      [1.2826800746280194, 1, 1.0866714868766487, 1],
      [0.41660429139359517, -0.22065004519750417, 1.238977382950853, 4],
      [1, 1.119530476852402, 0.6913308342566303, 0.1599721120973764],
      [0, 1.1389631027299605, 1, 1.0259766909259131],
      [0.7191575741050164, -0.06899830615027372, 0.3823707470994439, -0.6286025947173418],
      [0, -0.43397748738009884, 4, 0.9574466043900509],
      [1, 0, 1.0124458495289532, 1.3458661097418902],
      [1.4717875024431462, 1, -0.12299666785797378, 1.1140501008180728],
      [0.013802164697242311, 1.1777410511425097, 0.26284223953002966, 0.3173104189739232],
      [1.0149105117115416, 0.6560126187897822, 1, 2.4710124879894186],
      [0, -0.9999977151798239, -0.053424793252276594, 1],
      [0, 0, 1, 0.23431125547481313],
      [-0.7569085994475804, -1, -0.9095770784985023, -0.49938307784760017],
    ],
  },
];

function mockRoute(path, body) {
  if (path === '/api/filters') {
    return Promise.resolve(mockFilters(body.table));
  }
  if (path === '/api/attack') {
    if (body.level === 'deep') {
      return Promise.resolve({ job: 'mock-job-' + hashTable(body.table).toString(16) });
    }
    return Promise.resolve(mockAttackResult(body.table, body.level));
  }
  if (path === '/api/attack_batch') {
    return Promise.resolve({ results: body.tables.map((t) => mockAttackResult(t, body.level)) });
  }
  if (path === '/api/tables/curated') {
    return Promise.resolve({ tables: MOCK_CURATED });
  }
  if (path === '/api/candidates') {
    const id = 'mock-' + uuid();
    return Promise.resolve({
      id,
      record: {
        id,
        created: new Date().toISOString(),
        table: body.table,
        game: body.game,
        session: body.session,
        provenance: body.provenance,
        tier: 'unattacked',
        status: 'proposed',
      },
    });
  }
  if (path === '/api/stats') {
    return Promise.resolve({
      candidates: 17,
      best_score: 0.0301,
      library_profiles: 6,
      kills: 4,
      games: ['standoff', 'sequencer', 'breeder', 'atlas'],
    });
  }
  return Promise.reject(new ApiError(`No mock route for ${path}`, 501));
}

function post(path, body) {
  if (IS_MOCK) return mockRoute(path, body);
  return realFetch(path, {
    method: 'POST',
    headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify(body),
  });
}

function get(path) {
  if (IS_MOCK) return mockRoute(path, null);
  return realFetch(path);
}

export const Api = {
  filters: (table) => post('/api/filters', { table }),
  attack: (table, level) => post('/api/attack', { table, level }),
  attackBatch: (tables, level) => post('/api/attack_batch', { tables, level }),
  curated: () => get('/api/tables/curated'),
  submitCandidate: (table, provenance) =>
    post('/api/candidates', { table, game: 'breeder', session: SESSION_ID, provenance }),
  stats: () => get('/api/stats'),
};
