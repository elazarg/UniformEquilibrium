// Structural readings of a wire-format table (16 rows of 4, index = coalition
// bitmask, bit i set = player i quits). These are the same structural notions
// the phenotype in creature.js and the mock filters in filters-mock.js both
// key off, ported from the filter definitions in
// Experiments/singleton_collision_candidate_search/README.md. They are a
// convenience reading for rendering and for ?mock=1, never the authority on
// legality or score — that is always POST /api/filters and POST /api/attack.

export const MARGIN = 0.1;

export function r(table, mask, i) {
  return table[mask][i];
}

export function cellSign(v) {
  return v > 1e-9 ? 1 : v < -1e-9 ? -1 : 0;
}

// Preemption digraph: edge i -> j when player j's solo-self payoff beats
// what i would pay j, by margin g. Shapes the creature's limb tendrils.
export function edgesOf(table, g = MARGIN) {
  const e = { 0: [], 1: [], 2: [], 3: [] };
  for (let i = 0; i < 4; i++) {
    for (let j = 0; j < 4; j++) {
      if (i === j) continue;
      if (r(table, 1 << j, j) >= r(table, 1 << i, j) + g) e[i].push(j);
    }
  }
  return e;
}

export function viableOwnersOf(table, g = MARGIN) {
  const out = [];
  for (let i = 0; i < 4; i++) if (r(table, 1 << i, i) > -g) out.push(i);
  return out;
}

// Iterated normal-player removal (filter 5's core), used both for the mock
// LCP screen and for the creature's eye count / vitality reading.
export function coreOf(table) {
  let T = new Set([0, 1, 2, 3]);
  let changed = true;
  while (changed) {
    changed = false;
    for (const i of [...T]) {
      const normal = [...T].some(
        (j) => j !== i && r(table, 1 << j, i) - r(table, 1 << i, i) <= 0
      );
      if (!normal) {
        T.delete(i);
        changed = true;
      }
    }
  }
  return [...T].sort((a, b) => a - b);
}

function reachable(e, start) {
  const seen = new Set([start]);
  const stack = [start];
  while (stack.length) {
    const n = stack.pop();
    for (const m of e[n] || []) {
      if (!seen.has(m)) {
        seen.add(m);
        stack.push(m);
      }
    }
  }
  return seen;
}

function onCycle(e, node) {
  for (const m of e[node] || []) {
    if (m === node) return true;
    if (reachable(e, m).has(node)) return true;
  }
  return false;
}

// True when some viable owner can reach a node that lies on a directed
// cycle of the preemption digraph — the structural condition filter 4
// requires. Drives the creature's rotating halo.
export function hasOwnerCycle(table, g = MARGIN) {
  const e = edgesOf(table, g);
  const owners = viableOwnersOf(table, g);
  return owners.some((i) => [...reachable(e, i)].some((n) => onCycle(e, n)));
}
