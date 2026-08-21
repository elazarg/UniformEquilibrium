// Exact evaluator for periodic per-stage hazard profiles in four-player
// quitting games.  This is a line-by-line port of the reference experiment
// script
//   Experiments/singleton_collision_candidate_search/singleton_collision_candidate_search.py
// (functions `cyclic_solve`, `stage_absorption`, `phase_data`,
// `periodic_exploitability`, `stationary_closed_form`).
//
// It exists to drive interaction-rate feedback in the browser.  It never
// writes the ledger: every recorded number comes from the server engine.

export const N = 4;
export const PLAYERS = [0, 1, 2, 3];
export const MASK_COUNT = 1 << N;
export const EPS_KILL = 0.02;

// Solve V_t = constants[t] + (1 - hazards[t]) * V_{t+1} on a cycle.
//
// Phases carry their absorption probability, not their survival factor.  The
// killing profiles push hazards far below machine epsilon, where 1 - hazard
// rounds to exactly 1 and the hazard is annihilated while the numerator still
// carries its true value.  Total absorption around the cycle is therefore
// -expm1(sum log1p(-hazard)), which keeps full relative accuracy however small
// the hazards are.  Absorption counts as absent only when it is exactly zero;
// then the cycle never ends and the value is the never-absorbed payoff of zero.
export function cyclicSolve(constants, hazards) {
  const period = constants.length;
  let logSurvival = 0;
  let numerator = 0;
  let certain = false;
  for (let k = 0; k < period; k += 1) {
    numerator += Math.exp(logSurvival) * constants[k];
    const hazard = hazards[k];
    if (hazard >= 1) {
      certain = true;
      break;
    }
    if (hazard > 0) logSurvival += Math.log1p(-hazard);
  }
  const absorption = certain ? 1 : -Math.expm1(logSurvival);
  const head = absorption > 0 ? numerator / absorption : 0;
  const values = new Array(period).fill(0);
  values[0] = head;
  for (let t = period - 1; t > 0; t -= 1) {
    const follower = t + 1 < period ? values[t + 1] : head;
    values[t] = constants[t] + (1 - hazards[t]) * follower;
  }
  return values;
}

// Probability that somebody other than `skip` (null for nobody) quits in one
// stage, in the log form so that sub-epsilon hazards survive.
export function stageAbsorption(hazard, skip) {
  let logSurvival = 0;
  for (let i = 0; i < N; i += 1) {
    if (i === skip) continue;
    const rate = hazard[i];
    if (rate >= 1) return 1;
    if (rate > 0) logSurvival += Math.log1p(-rate);
  }
  return -Math.expm1(logSurvival);
}

// Per-phase quantities of a periodic independent-hazard stage:
//   absorption         probability somebody quits
//   absorbed[j]        expected absorbed payoff of j, on path
//   quitNow[i]         payoff to i of quitting this stage, collisions exact
//   othersAbsorbed[i]  i continues and the others absorb
//   othersAbsorption[i]probability some opponent of i quits
export function phaseData(table, hazard) {
  const complement = [];
  for (let i = 0; i < N; i += 1) complement.push(1 - hazard[i]);
  const probability = new Array(MASK_COUNT).fill(0);
  for (let mask = 0; mask < MASK_COUNT; mask += 1) {
    let value = 1;
    for (let i = 0; i < N; i += 1) {
      value *= (mask >> i) & 1 ? hazard[i] : complement[i];
    }
    probability[mask] = value;
  }
  const absorbed = new Array(N).fill(0);
  for (let mask = 1; mask < MASK_COUNT; mask += 1) {
    const weight = probability[mask];
    if (weight === 0) continue;
    const row = table[mask];
    for (let j = 0; j < N; j += 1) absorbed[j] += weight * row[j];
  }
  const quitNow = new Array(N).fill(0);
  const othersAbsorbed = new Array(N).fill(0);
  for (let i = 0; i < N; i += 1) {
    const bit = 1 << i;
    for (let mask = 0; mask < MASK_COUNT; mask += 1) {
      if (mask & bit) continue;
      let weight = 1;
      for (let j = 0; j < N; j += 1) {
        if (j === i) continue;
        weight *= (mask >> j) & 1 ? hazard[j] : complement[j];
      }
      if (weight === 0) continue;
      quitNow[i] += weight * table[mask | bit][i];
      if (mask) othersAbsorbed[i] += weight * table[mask][i];
    }
  }
  const othersAbsorption = [];
  for (let i = 0; i < N; i += 1) othersAbsorption.push(stageAbsorption(hazard, i));
  return {
    absorption: stageAbsorption(hazard, null),
    absorbed,
    quitNow,
    othersAbsorbed,
    othersAbsorption,
  };
}

// Full evaluation of a periodic hazard profile.
//
// On-path values solve the periodic absorption recursion.  Each deviator faces
// a finite phase-indexed optimal-stopping problem whose value is the maximum
// over the 2^P deterministic phase-indexed stopping policies; that maximum is
// attained by a deterministic Markov policy, so the enumeration is exact up to
// floating point.  Ties keep the lowest policy index, matching the reference.
export function evaluate(table, hazards) {
  const period = hazards.length;
  const data = [];
  for (let t = 0; t < period; t += 1) data.push(phaseData(table, hazards[t]));
  const stage = data.map((d) => d.absorption);
  const onPath = [];
  for (let j = 0; j < N; j += 1) {
    const constants = [];
    for (let t = 0; t < period; t += 1) constants.push(data[t].absorbed[j]);
    onPath.push(cyclicSolve(constants, stage));
  }
  const bestResponse = [];
  const bestPolicy = [];
  const perPlayer = [];
  const bestDeviations = [];
  const constants = new Array(period);
  const policyHazards = new Array(period);
  for (let i = 0; i < N; i += 1) {
    const responses = new Array(period).fill(-Infinity);
    const policies = new Array(period).fill(0);
    for (let policy = 0; policy < 1 << period; policy += 1) {
      for (let t = 0; t < period; t += 1) {
        if ((policy >> t) & 1) {
          constants[t] = data[t].quitNow[i];
          policyHazards[t] = 1;
        } else {
          constants[t] = data[t].othersAbsorbed[i];
          policyHazards[t] = data[t].othersAbsorption[i];
        }
      }
      const values = cyclicSolve(constants, policyHazards);
      for (let t = 0; t < period; t += 1) {
        if (values[t] > responses[t]) {
          responses[t] = values[t];
          policies[t] = policy;
        }
      }
    }
    let gap = -Infinity;
    let phase = 0;
    for (let t = 0; t < period; t += 1) {
      const here = responses[t] - onPath[i][t];
      if (here > gap) {
        gap = here;
        phase = t;
      }
    }
    bestResponse.push(responses);
    bestPolicy.push(policies);
    perPlayer.push(gap);
    const strikes = [];
    for (let t = 0; t < period; t += 1) {
      strikes.push(Boolean((policies[phase] >> t) & 1));
    }
    bestDeviations.push({
      player: i,
      value: responses[phase],
      phase,
      gap,
      policy: strikes,
    });
  }
  let exploitability = -Infinity;
  for (let i = 0; i < N; i += 1) {
    if (perPlayer[i] > exploitability) exploitability = perPlayer[i];
  }
  return {
    exploitability,
    per_player: perPlayer,
    on_path: onPath.map((row) => row[0]),
    on_path_phases: onPath,
    best_response: bestResponse,
    best_policy: bestPolicy,
    best_deviations: bestDeviations,
  };
}

export function periodicExploitability(table, hazards) {
  return evaluate(table, hazards).exploitability;
}

// Exploitability of a stationary profile, written out independently.  This
// duplicates no code from `evaluate` on purpose: it exists only so the
// self-check compares two separate derivations.
export function stationaryClosedForm(table, rates) {
  let survive = 1;
  for (let i = 0; i < N; i += 1) survive *= 1 - rates[i];
  let value = new Array(N).fill(0);
  for (let mask = 1; mask < MASK_COUNT; mask += 1) {
    let weight = 1;
    for (let i = 0; i < N; i += 1) {
      weight *= (mask >> i) & 1 ? rates[i] : 1 - rates[i];
    }
    for (let j = 0; j < N; j += 1) value[j] += weight * table[mask][j];
  }
  if (survive < 1) {
    value = value.map((v) => v / (1 - survive));
  } else {
    value = new Array(N).fill(0);
  }
  let worst = -Infinity;
  for (let i = 0; i < N; i += 1) {
    const bit = 1 << i;
    let quitNow = 0;
    let neverNumerator = 0;
    let absorbing = 0;
    for (let mask = 0; mask < MASK_COUNT; mask += 1) {
      if (mask & bit) continue;
      let weight = 1;
      for (let j = 0; j < N; j += 1) {
        if (j === i) continue;
        weight *= (mask >> j) & 1 ? rates[j] : 1 - rates[j];
      }
      quitNow += weight * table[mask | bit][i];
      if (mask) {
        neverNumerator += weight * table[mask][i];
        absorbing += weight;
      }
    }
    const never = absorbing > 1e-15 ? neverNumerator / absorbing : 0;
    worst = Math.max(worst, Math.max(quitNow, never) - value[i]);
  }
  return worst;
}

// Table helpers shared by the game surface.

export function maskLabel(mask) {
  const members = [];
  for (let i = 0; i < N; i += 1) if ((mask >> i) & 1) members.push(String(i + 1));
  return members.length ? `{${members.join(",")}}` : "{}";
}

export function validTable(table) {
  if (!Array.isArray(table) || table.length !== MASK_COUNT) return false;
  for (let mask = 0; mask < MASK_COUNT; mask += 1) {
    const row = table[mask];
    if (!Array.isArray(row) || row.length !== N) return false;
    for (let i = 0; i < N; i += 1) {
      if (typeof row[i] !== "number" || !Number.isFinite(row[i])) return false;
      if (mask === 0 && row[i] !== 0) return false;
    }
  }
  return true;
}
