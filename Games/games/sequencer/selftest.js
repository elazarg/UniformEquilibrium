// Self-check for the in-browser evaluator port.  Runs identically in node
// (tools/run_selftest.js) and in the browser (selftest.html).
//
// Three independent kinds of evidence:
//   * parity with hard-coded vectors whose expected values were produced by
//     the reference experiment script (see vectors.js);
//   * the identities the reference checks on random instances -- non-negative
//     exploitability, the on-path decomposition, and period-one agreement with
//     a separately written stationary closed form;
//   * shape checks on the degenerate cases (no absorption anywhere, certain
//     absorption).

import {
  N,
  evaluate,
  phaseData,
  cyclicSolve,
  stationaryClosedForm,
} from "./evaluator.js";
import { VECTORS } from "./vectors.js";

const PARITY_TOL = 1e-9;

function relError(got, want) {
  const scale = Math.max(1, Math.abs(want));
  return Math.abs(got - want) / scale;
}

function mulberry32(seed) {
  let a = seed >>> 0;
  return function next() {
    a = (a + 0x6d2b79f5) >>> 0;
    let t = a;
    t = Math.imul(t ^ (t >>> 15), t | 1);
    t ^= t + Math.imul(t ^ (t >>> 7), t | 61);
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}

function randomTable(rng) {
  const rows = [];
  for (let mask = 0; mask < 16; mask += 1) {
    const row = [];
    for (let i = 0; i < N; i += 1) {
      row.push(mask === 0 ? 0 : -4 + 8 * rng());
    }
    rows.push(row);
  }
  return rows;
}

export function checkVectors() {
  let worstValue = 0;
  let worstPerPlayer = 0;
  let worstOnPath = 0;
  let worstResponse = 0;
  let policyMismatches = 0;
  const failures = [];
  for (const vector of VECTORS) {
    const { table, profile, expected } = vector;
    const got = evaluate(table, profile.hazards);
    const period = profile.period;
    let local = 0;
    local = Math.max(local, relError(got.exploitability, expected.exploitability));
    worstValue = Math.max(worstValue, local);
    for (let i = 0; i < N; i += 1) {
      const perPlayer = relError(got.per_player[i], expected.per_player[i]);
      worstPerPlayer = Math.max(worstPerPlayer, perPlayer);
      local = Math.max(local, perPlayer);
      for (let t = 0; t < period; t += 1) {
        const onPath = relError(got.on_path_phases[i][t], expected.on_path[i][t]);
        const response = relError(
          got.best_response[i][t],
          expected.best_response[i][t],
        );
        worstOnPath = Math.max(worstOnPath, onPath);
        worstResponse = Math.max(worstResponse, response);
        local = Math.max(local, onPath, response);
        if (got.best_policy[i][t] !== expected.best_policy[i][t]) {
          policyMismatches += 1;
        }
      }
    }
    if (!(local < PARITY_TOL)) {
      failures.push({ name: vector.name, error: local });
    }
  }
  return {
    name: "vector parity vs the reference script",
    vectors: VECTORS.length,
    max_exploitability_error: worstValue,
    max_per_player_error: worstPerPlayer,
    max_on_path_error: worstOnPath,
    max_best_response_error: worstResponse,
    argmax_policy_mismatches: policyMismatches,
    failures,
    passed: failures.length === 0 && policyMismatches === 0,
  };
}

export function checkIdentities(trials = 400, seed = 7) {
  const rng = mulberry32(seed);
  let decomposition = 0;
  let negativity = 0;
  let stationaryGap = 0;
  let stationaryTrials = 0;
  for (let trial = 0; trial < trials; trial += 1) {
    const table = randomTable(rng);
    const period = 1 + Math.floor(rng() * 8);
    const tiny = trial % 2 === 1;
    const draw = () => (tiny ? Math.pow(10, -20 * rng()) : rng());
    const hazards = [];
    for (let t = 0; t < period; t += 1) {
      const row = [];
      for (let i = 0; i < N; i += 1) row.push(draw());
      hazards.push(row);
    }
    const report = evaluate(table, hazards);
    negativity = Math.max(negativity, -report.exploitability);
    const data = hazards.map((row) => phaseData(table, row));
    for (let i = 0; i < N; i += 1) {
      for (let t = 0; t < period; t += 1) {
        const rate = hazards[t][i];
        const follower = report.on_path_phases[i][(t + 1) % period];
        const branch =
          rate * data[t].quitNow[i] +
          (1 - rate) *
            (data[t].othersAbsorbed[i] +
              (1 - data[t].othersAbsorption[i]) * follower);
        decomposition = Math.max(
          decomposition,
          Math.abs(report.on_path_phases[i][t] - branch),
        );
      }
    }
    if (period === 1 && !tiny) {
      stationaryTrials += 1;
      const closed = stationaryClosedForm(table, hazards[0]);
      stationaryGap = Math.max(
        stationaryGap,
        Math.abs(closed - report.exploitability),
      );
    }
  }
  return {
    name: "randomized identities",
    trials,
    rng_seed: seed,
    on_path_decomposition_max_error: decomposition,
    max_negative_exploitability: negativity,
    stationary_closed_form_trials: stationaryTrials,
    stationary_closed_form_max_error: stationaryGap,
    passed:
      decomposition < 1e-9 && negativity < 1e-9 && stationaryGap < 1e-9,
  };
}

export function checkDegenerate() {
  const notes = [];
  let passed = true;
  const table = [];
  for (let mask = 0; mask < 16; mask += 1) {
    table.push(mask === 0 ? [0, 0, 0, 0] : [1, 2, 3, 4]);
  }
  const idle = evaluate(table, [[0, 0, 0, 0], [0, 0, 0, 0]]);
  const idleOnPath = idle.on_path_phases.every((row) => row.every((v) => v === 0));
  notes.push({ case: "no absorption anywhere", on_path_all_zero: idleOnPath });
  passed = passed && idleOnPath;

  // With zero absorption around the cycle the reference returns head 0 and
  // then back-substitutes, so cyclic_solve([1,2],[0,0]) is [0,2] and not [0,0].
  // On path the constants vanish together with the absorption, so this only
  // ever shows up on artificial inputs; it is pinned here because any drift
  // from it would be drift from the reference.
  const idleCycle = cyclicSolve([0, 0], [0, 0]).every((v) => v === 0);
  const pinned = cyclicSolve([1, 2], [0, 0]);
  const pinnedOk = pinned[0] === 0 && pinned[1] === 2;
  notes.push({
    case: "cyclicSolve with zero absorption",
    zero_constants_give_zero: idleCycle,
    reference_back_substitution: pinned,
  });
  passed = passed && idleCycle && pinnedOk;

  const certain = evaluate(table, [[1, 1, 1, 1]]);
  const certainOnPath = certain.on_path_phases.map((row) => row[0]);
  const certainOk =
    Math.abs(certainOnPath[0] - 1) < 1e-12 && Math.abs(certainOnPath[3] - 4) < 1e-12;
  notes.push({ case: "everybody quits at once", on_path: certainOnPath });
  passed = passed && certainOk;

  const sub = evaluate(table, [[1e-18, 0, 0, 0]]);
  const subOk = Math.abs(sub.on_path_phases[0][0] - 1) < 1e-9;
  notes.push({
    case: "single sub-epsilon hazard still absorbs",
    on_path_player_1: sub.on_path_phases[0][0],
  });
  passed = passed && subOk;

  return { name: "degenerate shapes", notes, passed };
}

export function runSelfTest() {
  const checks = [checkVectors(), checkIdentities(), checkDegenerate()];
  return { checks, passed: checks.every((check) => check.passed) };
}
