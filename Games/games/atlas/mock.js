// mock.js — synthetic field generator for ?mock=1. Everything here is
// clearly-labeled demo data: smooth deterministic functions of table content
// so the map has a plausible hot/cold structure, never real math and never
// claimed as such.
(function () {
  'use strict';

  // Solan-Vieille (2001) Section 3 seed table, coalition-bitmask indexed
  // (bit i set = player i+1 quits), row 0 all zero. Values from
  // Experiments/singleton_collision_candidate_search/README.md.
  const SEED_TABLE = [
    [0, 0, 0, 0],     // {}
    [1, 4, 0, 0],     // {1}
    [4, 1, 0, 0],     // {2}
    [1, 1, 1, 1],     // {1,2}
    [0, 0, 1, 4],     // {3}
    [1, 1, 1, 0],     // {1,3}
    [0, 1, 1, 1],     // {2,3}
    [1, 0, 0, 0],     // {1,2,3}
    [0, 0, 4, 1],     // {4}
    [1, 0, 1, 1],     // {1,4}
    [1, 1, 0, 1],     // {2,4}
    [0, 1, 0, 0],     // {1,2,4}
    [1, 1, 1, 1],     // {3,4}
    [0, 0, 0, 1],     // {1,3,4}
    [0, 0, 1, 0],     // {2,3,4}
    [-1, -1, -1, -1], // {1,2,3,4}
  ];

  function perturb(table, salt) {
    return table.map((row, idx) => row.map((v, p) => {
      if (idx === 0) return 0;
      const d = Math.sin((idx * 4 + p + 1) * 0.71 + salt) * 0.6;
      return Math.max(-4, Math.min(4, v + d));
    }));
  }

  const CHAIN_A = perturb(SEED_TABLE, 1.3);
  const CHAIN_B = perturb(SEED_TABLE, 2.9);

  const CURATED = [
    {
      id: 'seed-solan-vieille', name: 'Solan-Vieille (2001) seed', table: SEED_TABLE,
      known_score: 0.041,
      note: 'Boundary seed; known approximate equilibrium via a period-2 two-quitter repair (mock value).',
    },
    {
      id: 'mock-chain-a', name: 'Chain best A (mock)', table: CHAIN_A, known_score: 0.153,
      note: 'Synthetic stand-in for a chain-best table. Demo data only.',
    },
    {
      id: 'mock-chain-b', name: 'Chain best B (mock)', table: CHAIN_B, known_score: 0.089,
      note: 'Synthetic stand-in for a chain-best table. Demo data only.',
    },
  ];

  function delay(ms) { return new Promise((res) => setTimeout(res, ms)); }

  function tableFeature(table, k) {
    let s = 0;
    for (let idx = 0; idx < 16; idx++) {
      for (let p = 0; p < 4; p++) {
        s += table[idx][p] * Math.sin((idx * 4 + p + 1) * 0.19 + k * 1.71);
      }
    }
    return s;
  }

  const ATTACK_NAMES = [
    'library_replay', 'stationary', 'one_quitter_cyclic',
    'two_quitter_periodic', 'general_periodic',
  ];

  function mockScore(table, level) {
    const s = tableFeature(table, 0.37);
    let raw = 0.5 + 0.5 * Math.sin(s * 0.15);
    raw *= 0.5 + 0.5 * Math.cos(s * 0.083 + 1.3);
    const levelFactor = { replay: 1.0, quick: 0.5, standard: 0.32, deep: 0.18 }[level] || 1.0;
    return Math.max(0, raw * levelFactor * 0.85);
  }

  function mockBindingAttack(table, level) {
    if (level === 'replay') return 'library_replay';
    const allowed = level === 'quick' ? ['library_replay', 'stationary'] : ATTACK_NAMES;
    let best = -Infinity;
    let name = allowed[0];
    allowed.forEach((n, k) => {
      const v = Math.sin(tableFeature(table, k * 2.1 + 0.5) * 0.1);
      if (v > best) { best = v; name = n; }
    });
    return name;
  }

  function oneResult(table, level) {
    const score = mockScore(table, level);
    const binding_attack = mockBindingAttack(table, level);
    const breakdown = {};
    breakdown[binding_attack] = { exploitability: score, profile: { period: 1, hazards: [[0.1, 0.1, 0.1, 0.1]] } };
    return {
      score, binding_attack, level,
      elapsed: 0.001 + Math.random() * 0.01,
      breakdown,
    };
  }

  let jobCounter = 0;
  const jobs = new Map();

  const Mock = {
    async getCuratedTables() {
      await delay(120);
      return { tables: CURATED };
    },

    async getCandidates(limit) {
      await delay(100);
      const n = Math.min(limit || 50, 6);
      const list = [];
      for (let i = 0; i < n; i++) {
        list.push({
          id: 'mock-cand-' + i,
          created: new Date(Date.now() - i * 3600e3).toISOString(),
          table: perturb(SEED_TABLE, 5 + i * 0.7),
          game: ['breeder', 'standoff', 'sequencer'][i % 3],
          session: 'mock-session',
          tier: 'survivor-quick',
          status: 'proposed',
          score: 0.05 + 0.02 * i,
        });
      }
      return { candidates: list };
    },

    async attackBatch(tables, level) {
      await delay(60 + tables.length * 2);
      return { results: tables.map((t) => oneResult(t, level)) };
    },

    async attack(table, level) {
      if (level === 'deep') {
        const id = 'mock-job-' + (++jobCounter);
        jobs.set(id, { status: 'running', startedAt: Date.now() });
        setTimeout(() => { jobs.set(id, { status: 'done', result: oneResult(table, 'deep') }); }, 1500);
        return { job: id };
      }
      await delay(150 + (level === 'standard' ? 400 : 60));
      return oneResult(table, level);
    },

    async getJob(id) {
      await delay(80);
      const j = jobs.get(id);
      if (!j) return { status: 'error', result: { error: 'unknown job' } };
      return j;
    },

    async filters(table) {
      await delay(70);
      const s = tableFeature(table, 9.1);
      const core = Math.sin(s * 0.05) > -0.2; // rough synthetic legality band
      const names = [
        '1_toggle_instability', '2_viable_owner', '3_collider_preemptor',
        '4_preemption_cycle', '5_iterated_normal_core', '6_no_lcp_solution',
      ];
      const filters = {};
      let pass = true;
      names.forEach((n, k) => {
        const p = (core || k >= 5) && Math.sin(s * 0.07 + k) > -0.3;
        filters[n] = { pass: p };
        if (!p && k < 5) pass = false; // filters 1-5 gate the "structurally dead" overlay
      });
      return { pass, filters };
    },

    async postCandidate(payload) {
      await delay(200);
      const id = 'mock-submit-' + Date.now();
      const score = mockScore(payload.table, 'standard');
      const tier = score < 0.01 ? 'numerical-wide' : score < 0.02 ? 'numerical-narrow' : 'survivor-standard';
      return {
        id,
        record: {
          id,
          created: new Date().toISOString(),
          table: payload.table,
          game: payload.game,
          session: payload.session,
          provenance: payload.provenance,
          evaluation: oneResult(payload.table, 'standard'),
          tier,
          status: score < 0.02 ? 'killed' : 'proposed',
          killed_by: null,
        },
      };
    },
  };

  window.Atlas = window.Atlas || {};
  window.Atlas.Mock = Mock;
})();
