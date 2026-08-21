/* standoff — the fixer's deck.
 *
 * Every round deals a hand of pre-rolled cards. Pre-rolling matters: a card
 * whose target and noise are already fixed has one determined resulting table,
 * so its legality under filters 1-5 can be shown before the player commits.
 * Illegal cards stay face-up with the house's objection printed on them.
 */
(function (root) {
  'use strict';

  var E = root.SOEval;
  var NAMES = E.NAMES;

  /* Money in this saloon comes in bits. Every card moves stakes by a whole
   * number of quarters, so a run is legible, memorable, and reproducible;
   * see the README on the sublattice restriction. */
  var Q = E.LATTICE;

  var NUMBER_WORDS = ['no', 'one', 'two', 'three', 'four', 'five', 'six',
    'seven', 'eight', 'nine', 'ten'];

  /* "two bits" is a quarter, the way it always was. */
  function bits(amount) {
    var quarters = Math.round(Math.abs(amount) / Q);
    if (!quarters) return 'nothing';
    var dollars = Math.floor(quarters / 4), rest = quarters % 4;
    var small = { 1: 'two bits', 2: 'four bits', 3: 'six bits' };
    var parts = [];
    if (dollars) {
      parts.push(dollars === 1 ? 'a dollar'
        : (NUMBER_WORDS[dollars] || 'a stack of') + ' dollars');
    }
    if (rest) parts.push(small[rest]);
    return parts.join(' and ');
  }

  /* A whole number of quarters, drawn from `lo`..`hi` inclusive. */
  function quarters(rng, lo, hi) {
    return (lo + Math.floor(rng() * (hi - lo + 1))) * Q;
  }

  /* A small signed jostle in quarters, weighted toward the middle. */
  function jostle(rng, span) {
    var a = Math.floor(rng() * (span + 1)), b = Math.floor(rng() * (span + 1));
    return (a - b) * Q;
  }

  function pick(rng, arr) { return arr[Math.floor(rng() * arr.length) % arr.length]; }

  function pairsList() {
    var out = [];
    for (var i = 0; i < 4; i++) for (var j = i + 1; j < 4; j++) out.push([i, j]);
    return out;
  }

  function membersOf(mask) {
    var out = [];
    for (var i = 0; i < 4; i++) if (mask >> i & 1) out.push(i);
    return out;
  }

  function withTable(table, mutate) {
    var next = E.cloneTable(table);
    mutate(next);
    // Snapping keeps the whole run on the lattice even after a scaling move.
    return E.snapTable(E.clampTable(next));
  }

  /* ---- card archetypes -------------------------------------------------- */

  var ARCHETYPES = [
    {
      kind: 'grudge',
      weight: 3,
      build: function (rng) {
        var pair = pick(rng, pairsList());
        var amount = quarters(rng, 1, 3);
        return {
          title: 'Stoke a Grudge',
          subtitle: NAMES[pair[0]] + ' & ' + NAMES[pair[1]],
          cost: 2,
          flavour: 'Tell each of them the other is about to move on his pot. ' +
            'Now if they both go for it at the same moment, they both come out ahead.',
          targets: { players: pair, pairs: [pair] },
          blurb: 'a sweeter payday if they both go at once — ' + bits(amount) + ' more',
          detail: 'collision reward for {' + NAMES[pair[0]] + ',' + NAMES[pair[1]] +
            '} up ' + amount.toFixed(2),
          apply: function (table) {
            return withTable(table, function (t) {
              var mask = (1 << pair[0]) | (1 << pair[1]);
              t[mask][pair[0]] += amount;
              t[mask][pair[1]] += amount;
            });
          }
        };
      }
    },
    {
      kind: 'rumour',
      weight: 3,
      build: function (rng) {
        var mask = 1 + Math.floor(rng() * 15);
        var span = rng() < 0.25 ? 3 : 1;
        var noise = [jostle(rng, span), jostle(rng, span), jostle(rng, span),
          jostle(rng, span)];
        var who = E.coalitionName(mask);
        return {
          title: 'Spread a Rumour',
          subtitle: 'about ' + who,
          cost: 1,
          flavour: 'Nobody in this room has read the ledger in a year. ' +
            'Let the bar decide what that hand is worth tonight.',
          targets: { players: membersOf(mask), pairs: [] },
          blurb: 'nobody checks what that hand is really worth',
          detail: 'row {' + who + '} jostled by quarters [' +
            noise.map(function (n) { return (n / Q).toFixed(0); }).join(',') + ']',
          apply: function (table) {
            return withTable(table, function (t) {
              for (var i = 0; i < 4; i++) t[mask][i] += noise[i];
            });
          }
        };
      }
    },
    {
      kind: 'seats',
      weight: 2,
      build: function (rng) {
        var pair = pick(rng, pairsList());
        var perm = [0, 1, 2, 3];
        perm[pair[0]] = pair[1];
        perm[pair[1]] = pair[0];
        return {
          title: 'Swap Seats',
          subtitle: NAMES[pair[0]] + ' <-> ' + NAMES[pair[1]],
          cost: 1,
          swap: pair,
          flavour: 'Same money, new chairs. Careful: this changes nothing about ' +
            'how good the table is — but the gang wrote its old tricks down ' +
            'against the old seating, and a remembered draw aimed at the wrong ' +
            'chair finds nobody.',
          targets: { players: pair, pairs: [pair] },
          blurb: NAMES[pair[0]] + ' and ' + NAMES[pair[1]] + ' trade chairs',
          detail: 'seats ' + NAMES[pair[0]] + ' and ' + NAMES[pair[1]] + ' exchanged',
          apply: function (table) { return E.clampTable(E.permuteTable(table, perm)); }
        };
      }
    },
    {
      kind: 'sweeten',
      weight: 3,
      build: function (rng) {
        var who = Math.floor(rng() * 4);
        var amount = quarters(rng, 1, 3);
        return {
          title: 'Sweeten a Solo Draw',
          subtitle: NAMES[who],
          cost: 1,
          flavour: 'Quietly raise what ' + NAMES[who] + ' collects if he moves ' +
            'first and alone. He will start eyeing the door.',
          targets: { players: [who], pairs: [] },
          blurb: NAMES[who] + '\u2019s lone payday gets fatter by ' + bits(amount),
          detail: NAMES[who] + ' solo draw +' + amount.toFixed(2),
          apply: function (table) {
            return withTable(table, function (t) { t[1 << who][who] += amount; });
          }
        };
      }
    },
    {
      kind: 'sour',
      weight: 2,
      build: function (rng) {
        var who = Math.floor(rng() * 4);
        var amount = quarters(rng, 1, 3);
        return {
          title: 'Sour a Solo Draw',
          subtitle: NAMES[who],
          cost: 1,
          flavour: 'Shave what ' + NAMES[who] + ' gets for going it alone. ' +
            'Push him too far and he stops caring altogether.',
          targets: { players: [who], pairs: [] },
          blurb: NAMES[who] + '\u2019s lone payday gets thinner by ' + bits(amount),
          detail: NAMES[who] + ' solo draw -' + amount.toFixed(2),
          apply: function (table) {
            return withTable(table, function (t) { t[1 << who][who] -= amount; });
          }
        };
      }
    },
    {
      kind: 'shave',
      weight: 3,
      build: function (rng) {
        var who = Math.floor(rng() * 4);
        var amount = quarters(rng, 1, 2);
        return {
          title: 'Shave the Odds',
          subtitle: 'everyone but ' + NAMES[who],
          cost: 1,
          flavour: 'Make it hurt to be sitting there when ' + NAMES[who] +
            ' collects. The other three will want to beat him to it.',
          targets: { players: [0, 1, 2, 3].filter(function (i) { return i !== who; }),
                     pairs: [] },
          blurb: 'the other three are out ' + bits(amount) + ' when ' +
            NAMES[who] + ' collects',
          detail: 'others lose ' + amount.toFixed(2) + ' when ' + NAMES[who] + ' draws alone',
          apply: function (table) {
            return withTable(table, function (t) {
              for (var j = 0; j < 4; j++) if (j !== who) t[1 << who][j] -= amount;
            });
          }
        };
      }
    },
    {
      kind: 'pit',
      weight: 2,
      build: function (rng) {
        var amount = quarters(rng, 1, 3);
        return {
          title: 'Deepen the Pit',
          subtitle: 'if all four go',
          cost: 1,
          flavour: 'If everybody draws at once, everybody bleeds. ' +
            'Nobody wants to be in that pile, which is exactly why they keep ' +
            'trying to get out of it first.',
          targets: { players: [], pairs: [], pot: true },
          blurb: 'the four-way pile costs everyone another ' + bits(amount),
          detail: 'all-quit row -' + amount.toFixed(2),
          apply: function (table) {
            return withTable(table, function (t) {
              for (var j = 0; j < 4; j++) t[15][j] -= amount;
            });
          }
        };
      }
    },
    {
      kind: 'pact',
      weight: 2,
      build: function (rng) {
        var pair = pick(rng, pairsList());
        var up = quarters(rng, 1, 2), down = quarters(rng, 1, 1);
        return {
          title: 'Broker a Pact',
          subtitle: NAMES[pair[0]] + ' + ' + NAMES[pair[1]],
          cost: 2,
          flavour: 'Two of them agree to move together — and each agrees that ' +
            'being left behind by the other is a disaster. Pacts like this are ' +
            'exactly what the Paired Draw is looking for, so spend it knowing that.',
          targets: { players: pair, pairs: [pair] },
          blurb: bits(up) + ' richer together, ' + bits(down) + ' poorer left behind',
          detail: 'pair row +' + up.toFixed(2) + ', left-behind payoff -' + down.toFixed(2),
          apply: function (table) {
            return withTable(table, function (t) {
              var mask = (1 << pair[0]) | (1 << pair[1]);
              t[mask][pair[0]] += up;
              t[mask][pair[1]] += up;
              t[1 << pair[0]][pair[1]] -= down;
              t[1 << pair[1]][pair[0]] -= down;
            });
          }
        };
      }
    },
    {
      kind: 'escalate',
      weight: 2,
      build: function (rng) {
        var step = quarters(rng, 1, 1);
        return {
          title: 'Raise the House Limit',
          subtitle: 'the whole room',
          cost: 2,
          flavour: 'Every stake in the room moves a notch further from nothing. ' +
            'The same argument, louder.',
          targets: { players: [0, 1, 2, 3], pairs: [], pot: true },
          blurb: 'every stake in the room grows by ' + bits(step),
          detail: 'every nonzero entry pushed ' + (step / Q).toFixed(0) +
            ' quarter(s) away from zero',
          apply: function (table) {
            return withTable(table, function (t) {
              for (var m = 1; m < 16; m++) {
                for (var j = 0; j < 4; j++) {
                  if (t[m][j] > 0) t[m][j] += step;
                  else if (t[m][j] < 0) t[m][j] -= step;
                }
              }
            });
          }
        };
      }
    },
    {
      kind: 'threesome',
      weight: 2,
      build: function (rng) {
        var triples = [7, 11, 13, 14];
        var mask = pick(rng, triples);
        var members = membersOf(mask);
        var victim = pick(rng, members);
        var amount = quarters(rng, 1, 3);
        return {
          title: 'Poison the Threesome',
          subtitle: NAMES[victim] + ' in a crowd of three',
          cost: 1,
          flavour: NAMES[victim] + ' finds out the hard way that being one of ' +
            'three is worse than being one of two.',
          targets: { players: members, pairs: [] },
          blurb: NAMES[victim] + ' is out ' + bits(amount) + ' for being one of three',
          detail: NAMES[victim] + ' loses ' + amount.toFixed(2) + ' in row {' +
            E.coalitionName(mask) + '}',
          apply: function (table) {
            return withTable(table, function (t) { t[mask][victim] -= amount; });
          }
        };
      }
    }
  ];

  /* The read-the-tell card: only dealt once the player has actually seen a
   * killing schedule. It perturbs the rows that schedule leaned on. */
  function bluffCard(rng, lastKill) {
    var hazards = lastKill.profile.hazards;
    var weights = new Float64Array(16);
    for (var t = 0; t < hazards.length; t++) {
      var haz = hazards[t];
      for (var m = 1; m < 16; m++) {
        var w = 1;
        for (var i = 0; i < 4; i++) w *= (m >> i & 1) ? haz[i] : (1 - haz[i]);
        weights[m] += w / hazards.length;
      }
    }
    var order = [];
    for (var k = 1; k < 16; k++) order.push(k);
    order.sort(function (a, b) { return weights[b] - weights[a]; });
    var hot = order.slice(0, 2);
    var noise = [];
    for (var n = 0; n < hot.length * 4; n++) noise.push(jostle(rng, 2));
    var members = [];
    hot.forEach(function (m) {
      membersOf(m).forEach(function (p) { if (members.indexOf(p) < 0) members.push(p); });
    });
    return {
      kind: 'bluff',
      title: 'Call the Bluff',
      subtitle: 'against ' + lastKill.antagonistName,
      cost: 2,
      flavour: 'You watched how they timed it. Move the money they were ' +
        'counting on — the arrangement they found was leaning on {' +
        E.coalitionName(hot[0]) + '} more than anything else.',
      targets: { players: members, pairs: [] },
      blurb: 'move the money they were counting on',
      detail: 'rows {' + hot.map(E.coalitionName).join('}, {') + '} jostled by quarters [' +
        noise.map(function (n) { return (n / Q).toFixed(0); }).join(',') + '] after a kill',
      apply: function (table) {
        return withTable(table, function (t) {
          hot.forEach(function (m, idx) {
            for (var i = 0; i < 4; i++) t[m][i] += noise[idx * 4 + i];
          });
        });
      }
    };
  }

  /* Deal a hand. `lastKill` may be null. Legality is evaluated against the
   * current table with the client port of filters 1-5; the server re-checks on
   * commit via POST /api/filters. */
  function dealHand(rng, table, size, lastKill) {
    var pool = [];
    ARCHETYPES.forEach(function (arch) {
      for (var w = 0; w < arch.weight; w++) pool.push(arch);
    });
    var hand = [];
    var usedKinds = {};
    var guard = 0;
    while (hand.length < size && guard++ < 400) {
      var arch = pick(rng, pool);
      if (usedKinds[arch.kind] && rng() < 0.85) continue;
      usedKinds[arch.kind] = true;
      var card = arch.build(rng);
      card.kind = arch.kind;
      hand.push(card);
    }
    if (lastKill && lastKill.profile && lastKill.profile.hazards) {
      hand[hand.length - 1] = bluffCard(rng, lastKill);
    }
    hand.forEach(function (card, index) {
      card.id = 'card-' + index + '-' + Math.floor(rng() * 1e6).toString(36);
      annotate(card, table);
    });
    return hand;
  }

  /* Attach the resulting table, its legality, and the house's objection. */
  function annotate(card, table) {
    card.result = card.apply(table);
    var verdict = E.runFilters(card.result, E.MARGIN);
    card.legal = verdict.pass;
    card.objection = verdict.pass ? null : E.houseObjection(verdict);
    card.filters = verdict.filters;
    return card;
  }

  root.SOMoves = {
    bits: bits,
    dealHand: dealHand,
    annotate: annotate,
    ARCHETYPES: ARCHETYPES,

    /* A legal random perturbation of a table, for the "shuffle the deck"
     * start option. Rejection-samples until filters 1-5 hold. */
    randomLegalPerturbation: function (rng, table, tries, minHunch) {
      tries = tries || 300;
      for (var attempt = 0; attempt < tries; attempt++) {
        var next = E.snapTable(E.cloneTable(table));
        var count = 1 + Math.floor(rng() * 8);
        for (var c = 0; c < count; c++) {
          var mask = 1 + Math.floor(rng() * 15);
          var who = Math.floor(rng() * 4);
          next[mask][who] += jostle(rng, rng() < 0.2 ? 3 : 1);
        }
        E.snapTable(E.clampTable(next));
        if (!E.runFilters(next, E.MARGIN).pass) continue;
        // Optional playability screen: a coarse stationary probe, so a run does
        // not open on a table the weakest possible gang settles immediately.
        if (minHunch && E.hunch(next) < minHunch) continue;
        return next;
      }
      return E.cloneTable(table);
    }
  };
})(window);
