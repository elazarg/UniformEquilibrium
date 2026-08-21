/* standoff — in-browser port of the exact periodic evaluator, the structural
 * filters, and a small local attack battery.
 *
 * HONESTY NOTE. Everything in this file exists to make the *animation* feel
 * instant and to power ?mock=1. No number produced here is ever recorded.
 * Scores that reach the ledger come from POST /api/attack and POST
 * /api/candidates, computed by the shared Python engine. Anything on screen
 * that came from this file is labelled a "hunch".
 *
 * The math follows
 * Experiments/singleton_collision_candidate_search/singleton_collision_candidate_search.py
 * (functions cyclic_solve, phase_data, periodic_exploitability, filters 1-5).
 */
(function (root) {
  'use strict';

  var N = 4;
  var MASKS = 16;
  var EPS_KILL = 0.02;
  var MARGIN = 0.1;
  var LO = -4.0, HI = 4.0;

  /* standoff plays on a quarter lattice: money in this saloon comes in bits,
   * and a bit is an eighth of a dollar, so a quarter is "two bits". This is a
   * deliberate restriction of the search space to a sublattice of [-4,4]^64 —
   * see the README, and note that every submission records it under
   * provenance.subspace. It is never a claim of coverage. */
  var LATTICE = 0.25;

  function snap(value) {
    var v = Math.round(value / LATTICE) * LATTICE;
    if (v < LO) v = LO;
    if (v > HI) v = HI;
    // Kill -0 and float dust so table hashes stay stable.
    return v === 0 ? 0 : Number(v.toFixed(2));
  }

  function isOnLattice(table) {
    for (var m = 0; m < MASKS; m++) {
      for (var i = 0; i < N; i++) {
        var q = table[m][i] / LATTICE;
        if (Math.abs(q - Math.round(q)) > 1e-9) return false;
      }
    }
    return true;
  }

  function snapTable(table) {
    for (var m = 0; m < MASKS; m++) {
      for (var i = 0; i < N; i++) table[m][i] = m === 0 ? 0 : snap(table[m][i]);
    }
    return table;
  }

  // ---------------------------------------------------------------- table --

  function zeroTable() {
    var t = [];
    for (var m = 0; m < MASKS; m++) t.push([0, 0, 0, 0]);
    return t;
  }

  function cloneTable(table) {
    var t = [];
    for (var m = 0; m < MASKS; m++) t.push(table[m].slice());
    return t;
  }

  function clampTable(table) {
    for (var m = 0; m < MASKS; m++) {
      for (var i = 0; i < N; i++) {
        var v = table[m][i];
        if (!isFinite(v)) v = 0;
        table[m][i] = v < LO ? LO : (v > HI ? HI : v);
      }
    }
    for (var j = 0; j < N; j++) table[0][j] = 0;
    return table;
  }

  function validTable(table) {
    if (!Array.isArray(table) || table.length !== MASKS) return false;
    for (var m = 0; m < MASKS; m++) {
      var row = table[m];
      if (!Array.isArray(row) || row.length !== N) return false;
      for (var i = 0; i < N; i++) {
        if (typeof row[i] !== 'number' || !isFinite(row[i])) return false;
        if (row[i] < LO - 1e-9 || row[i] > HI + 1e-9) return false;
      }
    }
    for (var k = 0; k < N; k++) if (Math.abs(table[0][k]) > 1e-12) return false;
    return true;
  }

  function solo(table, i) { return table[1 << i][i]; }

  function tableHash(table) {
    // FNV-1a over the rounded entries; only used for local caching.
    var h = 0x811c9dc5;
    for (var m = 0; m < MASKS; m++) {
      for (var i = 0; i < N; i++) {
        var s = table[m][i].toFixed(6);
        for (var k = 0; k < s.length; k++) {
          h ^= s.charCodeAt(k);
          h = (h * 0x01000193) >>> 0;
        }
      }
    }
    return h.toString(16);
  }

  function permuteTable(table, perm) {
    // perm[i] = index whose old payoffs player i receives.
    var out = zeroTable();
    for (var m = 0; m < MASKS; m++) {
      var src = 0;
      for (var i = 0; i < N; i++) if (m >> i & 1) src |= 1 << perm[i];
      for (var j = 0; j < N; j++) out[m][j] = table[src][perm[j]];
    }
    return out;
  }

  // ------------------------------------------------------------ evaluator --

  function cyclicSolve(constants, hazards, out) {
    var P = constants.length;
    var logSurvival = 0.0, numerator = 0.0, certain = false, k;
    for (k = 0; k < P; k++) {
      numerator += Math.exp(logSurvival) * constants[k];
      var hazard = hazards[k];
      if (hazard >= 1.0) { certain = true; break; }
      if (hazard > 0.0) logSurvival += Math.log1p(-hazard);
    }
    var absorption = certain ? 1.0 : -Math.expm1(logSurvival);
    var head = absorption > 0.0 ? numerator / absorption : 0.0;
    var values = out || new Float64Array(P);
    values[0] = head;
    for (var t = P - 1; t > 0; t--) {
      var follower = (t + 1 < P) ? values[t + 1] : head;
      values[t] = constants[t] + (1.0 - hazards[t]) * follower;
    }
    return values;
  }

  function stageAbsorption(hazard, skip) {
    var logSurvival = 0.0;
    for (var i = 0; i < N; i++) {
      if (i === skip) continue;
      var rate = hazard[i];
      if (rate >= 1.0) return 1.0;
      if (rate > 0.0) logSurvival += Math.log1p(-rate);
    }
    return -Math.expm1(logSurvival);
  }

  function phaseData(table, hazard) {
    var comp = [1 - hazard[0], 1 - hazard[1], 1 - hazard[2], 1 - hazard[3]];
    var prob = new Float64Array(MASKS);
    var m, i, j, w;
    for (m = 0; m < MASKS; m++) {
      w = 1.0;
      for (i = 0; i < N; i++) w *= (m >> i & 1) ? hazard[i] : comp[i];
      prob[m] = w;
    }
    var absorbed = [0, 0, 0, 0];
    for (m = 1; m < MASKS; m++) {
      w = prob[m];
      if (w === 0.0) continue;
      var row = table[m];
      for (j = 0; j < N; j++) absorbed[j] += w * row[j];
    }
    var quitNow = [0, 0, 0, 0];
    var othersAbsorbed = [0, 0, 0, 0];
    for (i = 0; i < N; i++) {
      var bit = 1 << i;
      for (m = 0; m < MASKS; m++) {
        if (m & bit) continue;
        w = 1.0;
        for (j = 0; j < N; j++) {
          if (j === i) continue;
          w *= (m >> j & 1) ? hazard[j] : comp[j];
        }
        if (w === 0.0) continue;
        quitNow[i] += w * table[m | bit][i];
        if (m) othersAbsorbed[i] += w * table[m][i];
      }
    }
    return {
      absorption: stageAbsorption(hazard, -1),
      absorbed: absorbed,
      quitNow: quitNow,
      othersAbsorbed: othersAbsorbed,
      othersAbsorption: [
        stageAbsorption(hazard, 0), stageAbsorption(hazard, 1),
        stageAbsorption(hazard, 2), stageAbsorption(hazard, 3)
      ]
    };
  }

  /* Full detail: on-path values, per-player gaps, best deviating policies.
   * Mirrors periodic_exploitability but keeps the argmax policy per player. */
  function evaluateDetailed(table, hazards) {
    var P = hazards.length, t, i, policy;
    var data = [];
    for (t = 0; t < P; t++) data.push(phaseData(table, hazards[t]));
    var stageHaz = new Float64Array(P);
    for (t = 0; t < P; t++) stageHaz[t] = data[t].absorption;

    var onPath = [];
    for (i = 0; i < N; i++) {
      var consts = new Float64Array(P);
      for (t = 0; t < P; t++) consts[t] = data[t].absorbed[i];
      onPath.push(Array.prototype.slice.call(cyclicSolve(consts, stageHaz)));
    }

    var worst = -Infinity, worstPlayer = 0;
    var perPlayer = [], deviations = [];
    var c = new Float64Array(P), h = new Float64Array(P);
    for (i = 0; i < N; i++) {
      var best = new Float64Array(P), bestPolicy = new Int32Array(P);
      for (t = 0; t < P; t++) best[t] = -Infinity;
      for (policy = 0; policy < (1 << P); policy++) {
        for (t = 0; t < P; t++) {
          if (policy >> t & 1) { c[t] = data[t].quitNow[i]; h[t] = 1.0; }
          else { c[t] = data[t].othersAbsorbed[i]; h[t] = data[t].othersAbsorption[i]; }
        }
        var values = cyclicSolve(c, h);
        for (t = 0; t < P; t++) {
          if (values[t] > best[t]) { best[t] = values[t]; bestPolicy[t] = policy; }
        }
      }
      var gap = -Infinity, gapPhase = 0;
      for (t = 0; t < P; t++) {
        var g = best[t] - onPath[i][t];
        if (g > gap) { gap = g; gapPhase = t; }
      }
      perPlayer.push(gap);
      var pol = [];
      for (t = 0; t < P; t++) pol.push(!!(bestPolicy[gapPhase] >> t & 1));
      deviations.push({ player: i, value: best[gapPhase], policy: pol, phase: gapPhase });
      if (gap > worst) { worst = gap; worstPlayer = i; }
    }
    return {
      exploitability: worst,
      worst_player: worstPlayer,
      per_player: perPlayer,
      on_path: onPath.map(function (v) { return v[0]; }),
      on_path_phases: onPath,
      best_deviations: deviations
    };
  }

  /* Allocation-light hot path used by the local battery. */
  function exploitability(table, hazards) {
    var P = hazards.length, t, i, policy;
    var data = new Array(P);
    for (t = 0; t < P; t++) data[t] = phaseData(table, hazards[t]);
    var stageHaz = new Float64Array(P);
    for (t = 0; t < P; t++) stageHaz[t] = data[t].absorption;
    var consts = new Float64Array(P);
    var onPath = new Array(N);
    for (i = 0; i < N; i++) {
      for (t = 0; t < P; t++) consts[t] = data[t].absorbed[i];
      onPath[i] = Array.prototype.slice.call(cyclicSolve(consts, stageHaz));
    }
    var worst = -Infinity;
    var c = new Float64Array(P), h = new Float64Array(P);
    var best = new Float64Array(P);
    var limit = 1 << P;
    for (i = 0; i < N; i++) {
      for (t = 0; t < P; t++) best[t] = -Infinity;
      for (policy = 0; policy < limit; policy++) {
        for (t = 0; t < P; t++) {
          if (policy >> t & 1) { c[t] = data[t].quitNow[i]; h[t] = 1.0; }
          else { c[t] = data[t].othersAbsorbed[i]; h[t] = data[t].othersAbsorption[i]; }
        }
        var values = cyclicSolve(c, h);
        for (t = 0; t < P; t++) if (values[t] > best[t]) best[t] = values[t];
      }
      for (t = 0; t < P; t++) {
        var gap = best[t] - onPath[i][t];
        if (gap > worst) worst = gap;
      }
    }
    return worst;
  }

  // --------------------------------------------------------------- filters --

  /* Canonical filter keys, as emitted by run_filters in the reference script.
   * Server responses are read through normalizeFilters, which keys on the
   * leading digit, so a differently spelled server key still lands here. */
  var FILTER_KEYS = [
    '1_toggle_instability', '2_viable_owner', '3_collider_and_preemptor',
    '4_preemption_cycle', '5_iterated_normal_core', '6_no_lcp_solution'
  ];

  var FILTER_TITLES = {
    '1_toggle_instability': 'Toggle instability',
    '2_viable_owner': 'Viable owner',
    '3_collider_and_preemptor': 'Collider and preemptor',
    '4_preemption_cycle': 'Preemption cycle',
    '5_iterated_normal_core': 'Iterated normal core',
    '6_no_lcp_solution': 'LCP screen'
  };

  function normalizeFilters(filters) {
    var out = {};
    if (!filters) return out;
    for (var key in filters) {
      var digit = /^([1-6])_/.exec(key);
      if (!digit) continue;
      out[FILTER_KEYS[Number(digit[1]) - 1]] = filters[key];
    }
    return out;
  }

  function filterToggle(table, margin) {
    var stable = [];
    for (var m = 0; m < MASKS; m++) {
      var found = false;
      for (var i = 0; i < N; i++) {
        var up = table[m | (1 << i)][i];
        var down = table[m & ~(1 << i)][i];
        if (Math.max(up, down) >= table[m][i] + margin) { found = true; break; }
      }
      if (!found) stable.push(m);
    }
    return { pass: stable.length === 0, stable_coalitions: stable };
  }

  function filterViableOwner(table, margin) {
    var owners = [];
    for (var i = 0; i < N; i++) if (solo(table, i) >= margin) owners.push(i + 1);
    return { pass: owners.length > 0, owners: owners };
  }

  function viableOwners(table, margin) {
    var out = [];
    for (var i = 0; i < N; i++) if (solo(table, i) > -margin) out.push(i);
    return out;
  }

  function filterColliderPreemptor(table, margin) {
    var detail = {}, ok = true;
    var owners = viableOwners(table, margin);
    for (var k = 0; k < owners.length; k++) {
      var i = owners[k], colliders = [], preemptors = [];
      for (var j = 0; j < N; j++) {
        if (j === i) continue;
        if (table[(1 << i) | (1 << j)][j] >= table[1 << i][j] + margin) colliders.push(j + 1);
        if (solo(table, j) >= table[1 << i][j] + margin) preemptors.push(j + 1);
      }
      detail[String(i + 1)] = { colliders: colliders, preemptors: preemptors };
      if (!colliders.length || !preemptors.length) ok = false;
    }
    return { pass: ok, detail: detail, owners: owners };
  }

  function preemptionEdges(table, margin) {
    var edges = [];
    for (var i = 0; i < N; i++) {
      var out = [];
      for (var j = 0; j < N; j++) {
        if (j === i) continue;
        if (solo(table, j) >= table[1 << i][j] + margin) out.push(j);
      }
      edges.push(out);
    }
    return edges;
  }

  function filterPreemptionCycle(table, margin) {
    var edges = preemptionEdges(table, margin);
    var owners = viableOwners(table, margin);
    var closure = true, i, j;
    for (i = 0; i < owners.length; i++) if (!edges[owners[i]].length) closure = false;
    if (closure) {
      for (i = 0; i < N && closure; i++) {
        for (j = 0; j < edges[i].length; j++) {
          if (!edges[edges[i][j]].length) { closure = false; break; }
        }
      }
    }
    var reported = {};
    for (var e = 0; e < N; e++) {
      reported[String(e + 1)] = edges[e].map(function (x) { return x + 1; });
    }
    if (!closure) {
      return { pass: false, edges: reported, closure: false, cycle: null };
    }

    var reachable = {}, stack = owners.slice();
    while (stack.length) {
      var node = stack.pop();
      if (reachable[node]) continue;
      reachable[node] = true;
      stack = stack.concat(edges[node]);
    }
    var colour = {}, found = null;
    for (var key in reachable) colour[key] = 0;

    function visit(node, path) {
      colour[node] = 1;
      for (var k = 0; k < edges[node].length; k++) {
        var next = edges[node][k];
        if (!reachable[next]) continue;
        if (colour[next] === 1) {
          found = path.slice(path.indexOf(next)).concat([next]);
          return true;
        }
        if (colour[next] === 0 && visit(next, path.concat([next]))) return true;
      }
      colour[node] = 2;
      return false;
    }
    for (var o = 0; o < owners.length; o++) {
      if (colour[owners[o]] === 0 && visit(owners[o], [owners[o]])) break;
    }
    return {
      pass: !!found,
      edges: reported,
      closure: true,
      cycle: found ? found.map(function (x) { return x + 1; }) : null
    };
  }

  function normalizedMatrix(table) {
    var m = [];
    for (var i = 0; i < N; i++) {
      var row = [];
      for (var j = 0; j < N; j++) row.push(table[1 << j][i] - solo(table, i));
      m.push(row);
    }
    return m;
  }

  function iteratedNormalCore(table) {
    var matrix = normalizedMatrix(table);
    var survivors = [0, 1, 2, 3];
    for (;;) {
      var keep = [];
      for (var a = 0; a < survivors.length; a++) {
        var i = survivors[a], normal = false;
        for (var b = 0; b < survivors.length; b++) {
          var j = survivors[b];
          if (j !== i && matrix[i][j] <= 0.0) { normal = true; break; }
        }
        if (normal) keep.push(i);
      }
      if (keep.length === survivors.length) return survivors;
      survivors = keep;
      if (!survivors.length) return [];
    }
  }

  function filterNormalCore(table) {
    var core = iteratedNormalCore(table);
    return {
      pass: core.length >= 4,
      core: core.map(function (i) { return i + 1; }),
      size: core.length
    };
  }

  /* Filters 1-5 only. Filter 6 (the LCP screen) is left to the server; it is a
   * heuristic screen and the client never needs it to gate a move. */
  function runFilters(table, margin) {
    margin = margin === undefined ? MARGIN : margin;
    var f = {
      '1_toggle_instability': filterToggle(table, margin),
      '2_viable_owner': filterViableOwner(table, margin),
      '3_collider_and_preemptor': filterColliderPreemptor(table, margin),
      '4_preemption_cycle': filterPreemptionCycle(table, margin),
      '5_iterated_normal_core': filterNormalCore(table)
    };
    var pass = true;
    for (var k in f) if (!f[k].pass) pass = false;
    return { pass: pass, filters: f };
  }

  var NAMES = ['Cassidy', 'Boone', 'Delacroix', 'Rye'];

  /* Short, in-fiction reason for the first failing filter. Player-facing.
   *
   * Reads both shapes: the client's runFilters output, which puts detail
   * fields directly on the entry, and the server's, which nests them under
   * `detail` (as run_filters does in the reference script). A filter that is
   * missing or shaped unexpectedly is skipped rather than crashing the turn. */
  function houseObjection(result) {
    var f = (result && result.filters) || {};
    var i;

    function entry(key) { return f[key] || null; }
    function failed(key) {
      var e = entry(key);
      return e && e.pass === false;
    }
    function detail(key) {
      var e = entry(key);
      if (!e) return {};
      return (e.detail && typeof e.detail === 'object') ? e.detail : e;
    }

    if (failed('1_toggle_instability')) {
      var stable = detail('1_toggle_instability').stable_coalitions;
      if (stable && stable.length) {
        var mask = stable[0];
        var who = mask === 0 ? 'nobody at all' : coalitionName(mask);
        return 'Somebody settles. With ' + who + ' holding, no one at that table ' +
          'gets an itch worth ' + MARGIN.toFixed(2) + '.';
      }
      return 'Somebody at that table would just sit content. The house needs ' +
        'everybody itching.';
    }
    if (failed('2_viable_owner')) {
      return 'Nobody has a hand worth drawing on. The night just ends.';
    }
    if (failed('3_collider_and_preemptor')) {
      var d = detail('3_collider_and_preemptor');
      for (i in d) {
        var row = d[i];
        if (!row || typeof row !== 'object') continue;
        var name = NAMES[Number(i) - 1];
        if (row.colliders && !row.colliders.length) {
          return (name || 'Somebody') + ' has nobody who gains by crashing into his draw.';
        }
        if (row.preemptors && !row.preemptors.length) {
          return 'Nobody wants to beat ' + (name || 'him') + ' to the draw.';
        }
      }
      return 'The grudges do not close up: somebody has no one to crash into, ' +
        'or no one racing him to it.';
    }
    if (failed('4_preemption_cycle')) {
      if (detail('4_preemption_cycle').closure === false) {
        return 'The who-beats-whom chain runs into a dead end. Someone has nobody to fear.';
      }
      return 'Nobody chases anybody in a circle. The chase has an end, so the night has an end.';
    }
    if (failed('5_iterated_normal_core')) {
      var core = detail('5_iterated_normal_core').core || [];
      var out = [];
      for (i = 0; i < N; i++) if (core.indexOf(i + 1) < 0) out.push(NAMES[i]);
      if (out.length === 1) {
        return out[0] + ' drops out of the argument. A three-hand table is ' +
          'already solved business.';
      }
      if (out.length === 2 || out.length === 3) {
        return out.slice(0, -1).join(', ') + ' and ' + out[out.length - 1] +
          ' drop out of the argument. What is left is already solved business.';
      }
      return 'Nobody is left arguing with anybody. That is already solved business.';
    }
    if (failed('6_no_lcp_solution')) {
      return 'The house found a split all four of them would shake on. ' +
        'That is a settled table, whatever else it looks like.';
    }
    return 'The house has no objection.';
  }

  function coalitionName(mask) {
    var out = [];
    for (var i = 0; i < N; i++) if (mask >> i & 1) out.push(NAMES[i]);
    if (!out.length) return 'nobody';
    if (out.length === 1) return out[0];
    return out.slice(0, -1).join(', ') + ' and ' + out[out.length - 1];
  }

  // ---------------------------------------------------- optimizer helpers --

  function sigmoid(z) {
    if (z >= 0) return 1 / (1 + Math.exp(-Math.min(z, 60)));
    var e = Math.exp(Math.max(z, -60));
    return e / (1 + e);
  }

  function nelderMead(objective, start, step, maxIter, tol) {
    step = step === undefined ? 1.0 : step;
    maxIter = maxIter === undefined ? 120 : maxIter;
    tol = tol === undefined ? 1e-10 : tol;
    var size = start.length, i, j, k;
    var simplex = [start.slice()];
    for (i = 0; i < size; i++) {
      var point = start.slice();
      point[i] += step;
      simplex.push(point);
    }
    var values = simplex.map(objective);
    for (var iter = 0; iter < maxIter; iter++) {
      var order = [];
      for (k = 0; k <= size; k++) order.push(k);
      order.sort(function (a, b) { return values[a] - values[b]; });
      simplex = order.map(function (k) { return simplex[k]; });
      values = order.map(function (k) { return values[k]; });
      if (values[size] - values[0] < tol) break;
      var centroid = [];
      for (j = 0; j < size; j++) {
        var s = 0;
        for (k = 0; k < size; k++) s += simplex[k][j];
        centroid.push(s / size);
      }
      var worst = simplex[size];
      var reflected = [], expanded = [], contracted = [];
      for (j = 0; j < size; j++) reflected.push(centroid[j] + (centroid[j] - worst[j]));
      var vr = objective(reflected);
      if (vr < values[0]) {
        for (j = 0; j < size; j++) expanded.push(centroid[j] + 2 * (centroid[j] - worst[j]));
        var ve = objective(expanded);
        if (ve < vr) { simplex[size] = expanded; values[size] = ve; }
        else { simplex[size] = reflected; values[size] = vr; }
      } else if (vr < values[size - 1]) {
        simplex[size] = reflected; values[size] = vr;
      } else {
        for (j = 0; j < size; j++) contracted.push(centroid[j] + 0.5 * (worst[j] - centroid[j]));
        var vc = objective(contracted);
        if (vc < values[size]) { simplex[size] = contracted; values[size] = vc; }
        else {
          var best = simplex[0];
          for (k = 1; k <= size; k++) {
            var pt = [];
            for (j = 0; j < size; j++) pt.push(best[j] + 0.5 * (simplex[k][j] - best[j]));
            simplex[k] = pt;
            values[k] = objective(pt);
          }
        }
      }
    }
    var bi = 0;
    for (k = 1; k <= size; k++) if (values[k] < values[bi]) bi = k;
    return { point: simplex[bi], value: values[bi] };
  }

  function mulberry32(seed) {
    var a = seed >>> 0;
    return function () {
      a |= 0; a = (a + 0x6D2B79F5) | 0;
      var t = Math.imul(a ^ (a >>> 15), 1 | a);
      t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
      return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
    };
  }

  // -------------------------------------------------- local attack battery --
  // Used only for ?mock=1 and for hover "hunches". Deliberately much weaker
  // than the engine battery: fewer starts, smaller periods.

  var STATIONARY_GRID = [0.0, 0.02, 0.1, 0.3, 0.6, 1.0];

  function profileOf(hazards) {
    return { period: hazards.length, hazards: hazards.map(function (r) { return r.slice(); }) };
  }

  function attackStationary(table, budget) {
    var best = Infinity, bestRates = [0, 0, 0, 0];
    var a, b, c, d, rates;
    for (a = 0; a < 6; a++) for (b = 0; b < 6; b++) for (c = 0; c < 6; c++) for (d = 0; d < 6; d++) {
      rates = [STATIONARY_GRID[a], STATIONARY_GRID[b], STATIONARY_GRID[c], STATIONARY_GRID[d]];
      var v = exploitability(table, [rates]);
      if (v < best) { best = v; bestRates = rates; }
    }
    var starts = budget === 'wide' ? [bestRates, [0.02, 0.02, 0.02, 0.02], [0.3, 0.3, 0.3, 0.3],
      [0.1, 0.5, 0.1, 0.5], [0.5, 0.1, 0.5, 0.1]] : [bestRates, [0.05, 0.05, 0.05, 0.05]];
    for (var s = 0; s < starts.length; s++) {
      var z = starts[s].map(function (x) {
        var y = Math.min(Math.max(x, 1e-6), 1 - 1e-6);
        return Math.log(y / (1 - y));
      });
      var res = nelderMead(function (v) {
        return exploitability(table, [v.map(sigmoid)]);
      }, z, 1.0, budget === 'wide' ? 160 : 80);
      if (res.value < best) { best = res.value; bestRates = res.point.map(sigmoid); }
    }
    return { exploitability: best, profile: profileOf([bestRates]) };
  }

  function cyclicOrders() {
    // All cycles on subsets of size 2..4 up to rotation (20 of them).
    var out = [];
    var subsets = [];
    for (var m = 1; m < 16; m++) {
      var members = [];
      for (var i = 0; i < N; i++) if (m >> i & 1) members.push(i);
      if (members.length >= 2) subsets.push(members);
    }
    subsets.forEach(function (members) {
      permutations(members.slice(1)).forEach(function (rest) {
        out.push([members[0]].concat(rest));
      });
    });
    return out;
  }

  function permutations(arr) {
    if (arr.length <= 1) return [arr.slice()];
    var out = [];
    for (var i = 0; i < arr.length; i++) {
      var rest = arr.slice(0, i).concat(arr.slice(i + 1));
      permutations(rest).forEach(function (p) { out.push([arr[i]].concat(p)); });
    }
    return out;
  }

  var CYCLIC_ORDERS = cyclicOrders();

  function hazardsFromCycle(order, rates) {
    var out = [];
    for (var k = 0; k < order.length; k++) {
      var row = [0, 0, 0, 0];
      row[order[k]] = rates[k];
      out.push(row);
    }
    return out;
  }

  function attackOneQuitter(table, budget) {
    var best = Infinity, bestHaz = null;
    var starts = budget === 'wide' ? [0.02, 0.1, 0.4, 0.8] : [0.1, 0.5];
    for (var o = 0; o < CYCLIC_ORDERS.length; o++) {
      var order = CYCLIC_ORDERS[o], m = order.length;
      for (var s = 0; s < starts.length; s++) {
        var z = [];
        for (var k = 0; k < m; k++) {
          var y = starts[s];
          z.push(Math.log(y / (1 - y)));
        }
        var res = nelderMead(function (v) {
          return exploitability(table, hazardsFromCycle(order, v.map(sigmoid)));
        }, z, 1.0, budget === 'wide' ? 120 : 50);
        if (res.value < best) {
          best = res.value;
          bestHaz = hazardsFromCycle(order, res.point.map(sigmoid));
        }
      }
    }
    return { exploitability: best, profile: profileOf(bestHaz), cycle: null };
  }

  function pairSchedules(period) {
    var pairs = [];
    for (var i = 0; i < N; i++) for (var j = i + 1; j < N; j++) pairs.push([i, j]);
    var out = [];
    function build(prefix) {
      if (prefix.length === period) {
        // keep only lexicographically minimal rotation
        for (var r = 1; r < period; r++) {
          var rot = prefix.slice(r).concat(prefix.slice(0, r));
          if (key(rot) < key(prefix)) return;
        }
        out.push(prefix.slice());
        return;
      }
      for (var p = 0; p < pairs.length; p++) build(prefix.concat([pairs[p]]));
    }
    function key(sched) {
      return sched.map(function (p) { return p[0] + '' + p[1]; }).join('-');
    }
    build([]);
    return out;
  }

  var PAIR_SCHEDULES_2 = pairSchedules(2);
  var PAIR_SCHEDULES_3 = pairSchedules(3);

  function hazardsFromPairs(schedule, rates) {
    var out = [];
    for (var t = 0; t < schedule.length; t++) {
      var row = [0, 0, 0, 0];
      row[schedule[t][0]] = rates[2 * t];
      row[schedule[t][1]] = rates[2 * t + 1];
      out.push(row);
    }
    return out;
  }

  function attackTwoQuitter(table, budget) {
    var best = Infinity, bestHaz = null;
    var schedules = budget === 'wide'
      ? PAIR_SCHEDULES_2.concat(PAIR_SCHEDULES_3)
      : PAIR_SCHEDULES_2.concat(PAIR_SCHEDULES_3);
    var starts = budget === 'wide' ? [0.05, 0.3, 0.5] : [0.25];
    for (var s = 0; s < schedules.length; s++) {
      var sched = schedules[s];
      for (var st = 0; st < starts.length; st++) {
        var z = [];
        for (var k = 0; k < 2 * sched.length; k++) {
          var y = starts[st];
          z.push(Math.log(y / (1 - y)));
        }
        var res = nelderMead(function (v) {
          return exploitability(table, hazardsFromPairs(sched, v.map(sigmoid)));
        }, z, 1.0, budget === 'wide' ? 140 : 60);
        if (res.value < best) {
          best = res.value;
          bestHaz = hazardsFromPairs(sched, res.point.map(sigmoid));
        }
      }
    }
    return { exploitability: best, profile: profileOf(bestHaz) };
  }

  function attackGeneralPeriodic(table, budget) {
    var best = Infinity, bestHaz = null;
    var periods = budget === 'wide' ? [1, 2, 3, 4] : [1, 2];
    var starts = budget === 'wide' ? [0.02, 0.08, 0.25, 0.5, 0.8] : [0.08, 0.4];
    var rng = mulberry32(0x5eed);
    for (var p = 0; p < periods.length; p++) {
      var P = periods[p];
      for (var s = 0; s < starts.length; s++) {
        var z = [];
        for (var k = 0; k < 4 * P; k++) {
          var y = starts[s];
          z.push(Math.log(y / (1 - y)));
        }
        var res = nelderMead(function (v) {
          return exploitability(table, unpackGeneral(v, P));
        }, z, 1.0, budget === 'wide' ? 160 : 60);
        if (res.value < best) { best = res.value; bestHaz = unpackGeneral(res.point, P); }
      }
      if (budget === 'wide') {
        for (var r = 0; r < 2; r++) {
          var z2 = [];
          for (var k2 = 0; k2 < 4 * P; k2++) z2.push((rng() * 6) - 4);
          var res2 = nelderMead(function (v) {
            return exploitability(table, unpackGeneral(v, P));
          }, z2, 1.0, 140);
          if (res2.value < best) { best = res2.value; bestHaz = unpackGeneral(res2.point, P); }
        }
      }
    }
    return { exploitability: best, profile: profileOf(bestHaz) };
  }

  function unpackGeneral(v, P) {
    var out = [];
    for (var t = 0; t < P; t++) {
      var row = [];
      for (var i = 0; i < N; i++) row.push(sigmoid(v[4 * t + i]));
      out.push(row);
    }
    return out;
  }

  /* A deliberately cheap stationary probe, for the hover reading on a card.
   * It searches one attack family on a coarse grid and nothing else, so it is
   * an upper bound from a weak search: a low hunch is a warning, a high hunch
   * promises nothing. Never recorded, never shown without the word "hunch". */
  var HUNCH_GRID = [0.0, 0.05, 0.2, 0.5, 1.0];

  function hunch(table) {
    var best = Infinity;
    for (var a = 0; a < 5; a++) {
      for (var b = 0; b < 5; b++) {
        for (var c = 0; c < 5; c++) {
          for (var d = 0; d < 5; d++) {
            var v = exploitability(table, [[HUNCH_GRID[a], HUNCH_GRID[b],
              HUNCH_GRID[c], HUNCH_GRID[d]]]);
            if (v < best) best = v;
          }
        }
      }
    }
    return best;
  }

  function libraryReplay(table, profiles) {
    var best = Infinity, bestProfile = null, bestEntry = null;
    for (var k = 0; k < profiles.length; k++) {
      var entry = profiles[k];
      var prof = entry.profile || entry;
      if (!prof || !prof.hazards || !prof.hazards.length) continue;
      var v;
      try { v = exploitability(table, prof.hazards); } catch (e) { continue; }
      if (v < best) { best = v; bestProfile = prof; bestEntry = entry; }
    }
    if (bestProfile === null) return { exploitability: Infinity, profile: null, entry: null };
    return { exploitability: best, profile: bestProfile, entry: bestEntry };
  }

  root.SOEval = {
    N: N, MASKS: MASKS, EPS_KILL: EPS_KILL, MARGIN: MARGIN, LO: LO, HI: HI,
    LATTICE: LATTICE, snap: snap, snapTable: snapTable, isOnLattice: isOnLattice,
    NAMES: NAMES, FILTER_TITLES: FILTER_TITLES,
    zeroTable: zeroTable, cloneTable: cloneTable, clampTable: clampTable,
    validTable: validTable, solo: solo, tableHash: tableHash,
    permuteTable: permuteTable, coalitionName: coalitionName,
    cyclicSolve: cyclicSolve, phaseData: phaseData,
    evaluateDetailed: evaluateDetailed, exploitability: exploitability,
    runFilters: runFilters, houseObjection: houseObjection,
    FILTER_KEYS: FILTER_KEYS, normalizeFilters: normalizeFilters,
    preemptionEdges: preemptionEdges, iteratedNormalCore: iteratedNormalCore,
    nelderMead: nelderMead, sigmoid: sigmoid, mulberry32: mulberry32,
    hunch: hunch,
    attackStationary: attackStationary, attackOneQuitter: attackOneQuitter,
    attackTwoQuitter: attackTwoQuitter, attackGeneralPeriodic: attackGeneralPeriodic,
    libraryReplay: libraryReplay
  };
})(window);
