// Structural mutation and crossover operators over the wire-format table
// (16x4, row 0 fixed at zero). Mirrors the shape of the proposal step in
// Experiments/singleton_collision_candidate_search.py (small entry
// perturbations, occasional larger jump) plus two extra operators named in
// the design brief: collision strengthening and role permutation. This file
// only produces candidates; legality is decided by POST /api/filters
// (or its ?mock=1 stand-in), never here.
//
// Subspace restriction (DESIGN.md "subspace restriction is allowed — with a
// reason"): every value this file WRITES is snapped to a 1/8 lattice
// (LATTICE_STEP below) — mutation deltas and blended crossover values move in
// visible discrete steps rather than continuous noise. Reason: it is a
// deliberate search-quality and experience trade documented in README.md —
// offspring stay phenotypically close to their parents (the same table
// structure -> same-shaped creature mapping degrades if a "mutant" can jump
// arbitrarily far in one step), so a lineage reads as a visible, browsable
// family rather than unrelated tables that happen to sit next to each other
// in the grid. Curated seed tables and whole-row-inherited crossover rows
// keep their original precision unmodified — the lattice applies only to
// freshly generated values, never to what a player starts from. Every
// auto-submitted candidate stamps this restriction into its provenance (see
// app.js) so the ledger and any downstream reader can see the region that
// was actually searched; it is never presented as covering the full space.

import { clamp, cloneTable, mulberry32 } from './util.js';

export const LATTICE_STEP = 0.125; // 1/8

function snap(v) {
  return clamp(Math.round(v / LATTICE_STEP) * LATTICE_STEP);
}

function popcount(m) {
  let c = 0;
  while (m) {
    c += m & 1;
    m >>= 1;
  }
  return c;
}

// A signed integer step count with a discrete, roughly-triangular
// distribution favoring small magnitudes (difference of two uniform draws
// over 0..range-1), so most touches are small nudges and large jumps stay
// rare without needing a continuous Gaussian.
function smallSteps(rng, range) {
  return Math.floor(rng() * range) - Math.floor(rng() * range);
}

// Perturbs a handful of table entries by a whole number of lattice steps,
// clamped to [-4, 4]. Row 0 (the empty coalition) is never touched.
export function mutateRows(table, rng, { maxSteps = 3, jumpSteps = 14, jumpProb = 0.18 } = {}) {
  const t = cloneTable(table);
  const k = 1 + Math.floor(rng() * 6); // touch 1..6 entries — tighter than a full reroll
  for (let n = 0; n < k; n++) {
    const mask = 1 + Math.floor(rng() * 15); // never row 0
    const p = Math.floor(rng() * 4);
    const range = rng() < jumpProb ? jumpSteps : maxSteps;
    const steps = smallSteps(rng, range) || 1; // never a no-op touch
    t[mask][p] = snap(t[mask][p] + steps * LATTICE_STEP);
  }
  return t;
}

// Push one member of a chosen coalition to clearly win that collision —
// a stronger preemption reading, i.e. an edge into the digraph that shapes
// the creature's limbs. The push is a positive whole number of lattice steps.
export function strengthenCollision(table, rng) {
  const t = cloneTable(table);
  const coalitions = [];
  for (let m = 1; m < 16; m++) if (popcount(m) >= 2) coalitions.push(m);
  const S = coalitions[Math.floor(rng() * coalitions.length)];
  const members = [0, 1, 2, 3].filter((i) => S & (1 << i));
  const i = members[Math.floor(rng() * members.length)];
  const steps = 3 + Math.floor(rng() * 8); // 3..10 steps, i.e. +0.375..+1.25
  t[S][i] = snap(t[S][i] + steps * LATTICE_STEP);
  return t;
}

// Relabel the four players by a random permutation, remapping both the
// coalition bitmask and the payoff column consistently. A structurally
// identical table under relabeling should (and does) render as a similarly
// shaped creature, since the phenotype is keyed off structure, not player
// index. Pure relabeling moves no value, so nothing needs lattice snapping.
export function permuteRoles(table, rng) {
  const perm = [0, 1, 2, 3];
  for (let i = 3; i > 0; i--) {
    const j = Math.floor(rng() * (i + 1));
    [perm[i], perm[j]] = [perm[j], perm[i]];
  }
  const t = Array.from({ length: 16 }, () => [0, 0, 0, 0]);
  for (let S = 0; S < 16; S++) {
    let S2 = 0;
    for (let i = 0; i < 4; i++) if (S & (1 << i)) S2 |= 1 << perm[i];
    for (let i = 0; i < 4; i++) t[S2][perm[i]] = table[S][i];
  }
  return t;
}

// Mixes coalition rows of two parents: per nonempty coalition, either
// inherit one parent's row whole (original precision preserved — this is
// not a freshly generated value) or blend the two by averaging and snapping
// to the lattice, so joint collision structure sometimes carries over intact
// and sometimes softens onto the same discrete grid mutation uses.
export function crossover(tableA, tableB, rng, { blendProb = 0.25 } = {}) {
  const t = Array.from({ length: 16 }, () => [0, 0, 0, 0]);
  for (let S = 1; S < 16; S++) {
    if (rng() < blendProb) {
      for (let i = 0; i < 4; i++) t[S][i] = snap((tableA[S][i] + tableB[S][i]) / 2);
    } else {
      t[S] = (rng() < 0.5 ? tableA[S] : tableB[S]).slice();
    }
  }
  return t;
}

// Produces `count` pre-filter candidate tables from a pool of 1-2 parent
// tables, mixing operators across the batch for variety within a generation.
// Deterministic in `seed` so a given attempt is reproducible for debugging.
export function spawnCandidates(parents, seed, count) {
  const rng = mulberry32(seed >>> 0);
  const out = [];
  for (let k = 0; k < count; k++) {
    let base;
    if (parents.length >= 2 && rng() < 0.65) {
      base = crossover(parents[0], parents[1], rng);
    } else {
      base = parents[Math.floor(rng() * parents.length)];
    }
    const roll = rng();
    if (roll < 0.15) base = permuteRoles(base, rng);
    else if (roll < 0.35) base = strengthenCollision(base, rng);
    base = mutateRows(base, rng);
    out.push(base);
  }
  return out;
}
