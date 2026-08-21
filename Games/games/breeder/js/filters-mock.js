// Best-effort client-side port of the six necessary-condition filters
// described in
// Experiments/singleton_collision_candidate_search/README.md, for ?mock=1
// only — there is no server to ask in mock mode. This is NOT the authoritative
// engine (Games/engine/filters.py is): real play always calls
// POST /api/filters and trusts its answer, never this file's.

import { MARGIN, r, edgesOf, viableOwnersOf, coreOf, hasOwnerCycle } from './tablemath.js';

function filter1(table, g) {
  const bad = [];
  for (let S = 0; S < 16; S++) {
    let ok = false;
    for (let i = 0; i < 4; i++) {
      const Sp = S | (1 << i);
      const Sm = S & ~(1 << i);
      const cur = r(table, S, i);
      if (Math.max(r(table, Sp, i), r(table, Sm, i)) >= cur + g) {
        ok = true;
        break;
      }
    }
    if (!ok) bad.push(S);
  }
  return { pass: bad.length === 0, stable_coalitions: bad };
}

function filter2(table, g) {
  const owners = [];
  for (let i = 0; i < 4; i++) if (r(table, 1 << i, i) >= g) owners.push(i);
  return { pass: owners.length > 0, owners };
}

function filter3(table, g) {
  const detail = {};
  let pass = true;
  for (const i of viableOwnersOf(table, g)) {
    const colliders = [];
    const preemptors = [];
    for (let j = 0; j < 4; j++) {
      if (j === i) continue;
      if (r(table, (1 << i) | (1 << j), j) >= r(table, 1 << i, j) + g) colliders.push(j);
      if (r(table, 1 << j, j) >= r(table, 1 << i, j) + g) preemptors.push(j);
    }
    detail[i] = { colliders, preemptors };
    if (colliders.length === 0 || preemptors.length === 0) pass = false;
  }
  return { pass, detail };
}

function filter4(table, g) {
  const e = edgesOf(table, g);
  const owners = viableOwnersOf(table, g);
  const heads = new Set();
  for (const i of Object.keys(e)) for (const j of e[i]) heads.add(j);
  let pass = true;
  for (const i of owners) if ((e[i] || []).length === 0) pass = false;
  for (const j of heads) if ((e[j] || []).length === 0) pass = false;
  if (!hasOwnerCycle(table, g)) pass = false;
  return { pass, detail: { edges: e } };
}

function filter5(table) {
  const core = coreOf(table);
  return { pass: core.length === 4, detail: { core } };
}

function solveSquare(A, b) {
  const n = A.length;
  if (n === 0) return [];
  const M = A.map((row, i) => [...row, b[i]]);
  for (let col = 0; col < n; col++) {
    let piv = col;
    for (let row = col + 1; row < n; row++) {
      if (Math.abs(M[row][col]) > Math.abs(M[piv][col])) piv = row;
    }
    if (Math.abs(M[piv][col]) < 1e-12) return null;
    [M[col], M[piv]] = [M[piv], M[col]];
    for (let row = 0; row < n; row++) {
      if (row === col) continue;
      const f = M[row][col] / M[col][col];
      for (let c = col; c <= n; c++) M[row][c] -= f * M[col][c];
    }
  }
  return M.map((row, i) => row[n] / row[i]);
}

function nonemptySubsets(arr) {
  const out = [];
  const n = arr.length;
  for (let mask = 1; mask < 1 << n; mask++) {
    out.push(arr.filter((_, i) => mask & (1 << i)));
  }
  return out;
}

function filter6(table, g) {
  const core = coreOf(table);
  for (const S of nonemptySubsets(core)) {
    const A = S.map((i) => S.map((j) => r(table, 1 << j, i)));
    const b = S.map((i) => r(table, 1 << i, i));
    const lambda = solveSquare(A, b);
    if (!lambda) continue;
    const lambda0 = 1 - lambda.reduce((a, x) => a + x, 0);
    if (lambda.some((x) => x < -1e-7) || lambda0 < -1e-7) continue;
    if (lambda0 > 1e-7 && S.some((i) => r(table, 1 << i, i) > 0)) continue;
    let ok = true;
    for (let i = 0; i < 4 && ok; i++) {
      const Mi = S.reduce((acc, j, idx) => acc + lambda[idx] * r(table, 1 << j, i), 0);
      if (core.includes(i)) {
        if (Mi < r(table, 1 << i, i) - 1e-7) ok = false;
      } else if (Mi < Math.max(0, r(table, 1 << i, i)) - 1e-7) {
        ok = false;
      }
    }
    if (ok) return { pass: false, detail: { solution: { support: S, lambda, lambda0 } } };
  }
  return { pass: true, detail: { solution: null } };
}

export function mockFilters(table, g = MARGIN) {
  const f1 = filter1(table, g);
  const f2 = filter2(table, g);
  const f3 = filter3(table, g);
  const f4 = filter4(table, g);
  const f5 = filter5(table);
  const f6 = filter6(table, g);
  const all15 = f1.pass && f2.pass && f3.pass && f4.pass && f5.pass;
  const all16 = all15 && f6.pass;
  return {
    pass: all16,
    filters: {
      '1_toggle_instability': f1,
      '2_viable_owner': f2,
      '3_collider_and_preemptor': f3,
      '4_preemption_cycle': f4,
      '5_iterated_normal_core': f5,
      '6_no_lcp_solution': f6,
      all_1_to_5: all15,
      all_1_to_6: all16,
    },
  };
}
