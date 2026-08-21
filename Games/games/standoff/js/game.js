/* standoff — the run.
 *
 * A run is five rounds and a boss. Each round: deal a hand of structural
 * cards, spend edit points, ring the bell, and take the waves in the order the
 * engine battery orders them — cheapest first. Survive round five and the
 * Marshal (the deep re-attack, run as a background job) comes for the table.
 *
 * Which numbers are whose:
 *   - every exploitability that moves the nerve bar comes from POST /api/attack;
 *   - the client evaluator is used for card legality previews and for the beat
 *     animation only, and anything it produces is labelled a hunch;
 *   - the recorded score is whatever the server computes at POST /api/candidates.
 */
(function (root) {
  'use strict';

  var E = root.SOEval;
  var API = root.SOApi;
  var Audio = root.SOAudio;
  var Scene = root.SOScene;
  var Moves = root.SOMoves;
  var ANTAG = Scene.ANTAGONISTS;

  var EPS_KILL = E.EPS_KILL;
  var TARGET = E.MARGIN;          // g = 0.1, the margin a real counterexample would need
  var BEST_KEY = 'standoff:personal-best';

  var ROUNDS = [
    {
      name: 'First bell',
      budget: 4,
      waves: ['library_replay', 'stationary'],
      brief: 'Word is out that you are rigging a table. The gang sends what it ' +
        'has lying around.'
    },
    {
      name: 'Second bell',
      budget: 4,
      waves: ['library_replay', 'stationary', 'one_quitter_cyclic'],
      brief: 'The Kettlemans heard. They will try taking turns.'
    },
    {
      name: 'Third bell',
      budget: 3,
      waves: ['library_replay', 'stationary', 'one_quitter_cyclic', 'general_periodic'],
      brief: 'Somebody unpredictable is drinking at the bar.'
    },
    {
      name: 'Fourth bell',
      budget: 3,
      waves: ['library_replay', 'stationary', 'one_quitter_cyclic', 'general_periodic',
        'two_quitter_periodic'],
      brief: 'The Paired Draw is in town. This is the one that empties rooms.'
    },
    {
      name: 'Last call',
      budget: 3,
      waves: ['library_replay', 'stationary', 'one_quitter_cyclic', 'general_periodic',
        'two_quitter_periodic'],
      brief: 'Everyone at once, and then the Marshal.',
      final: true
    }
  ];

  function uuid() {
    if (root.crypto && root.crypto.randomUUID) return root.crypto.randomUUID();
    var bytes = new Uint8Array(16);
    (root.crypto || { getRandomValues: function (b) {
      for (var i = 0; i < b.length; i++) b[i] = Math.floor(Math.random() * 256);
    } }).getRandomValues(bytes);
    bytes[6] = (bytes[6] & 0x0f) | 0x40;
    bytes[8] = (bytes[8] & 0x3f) | 0x80;
    var hex = Array.prototype.map.call(bytes, function (b) {
      return ('0' + b.toString(16)).slice(-2);
    }).join('');
    return [hex.slice(0, 8), hex.slice(8, 12), hex.slice(12, 16), hex.slice(16, 20),
      hex.slice(20)].join('-');
  }

  function sleep(ms) {
    return new Promise(function (resolve) { setTimeout(resolve, ms); });
  }

  /* Run frames for `ms`, firing the schedule's beats into the audio. */
  function animateFor(ms) {
    return new Promise(function (resolve) {
      var t0 = performance.now();
      var step = function () {
        var beat = Scene.tickBeat();
        if (beat) {
          for (var i = 0; i < 4; i++) {
            var hazard = beat.hazards[i];
            if (hazard > 0.10 && Math.random() < Math.min(1, hazard * 1.2)) Audio.draw(i);
          }
        }
        if (performance.now() - t0 >= ms) resolve();
        else requestAnimationFrame(step);
      };
      requestAnimationFrame(step);
    });
  }

  /* Payoffs are clamped to [-4, 4], so a real exploitability cannot exceed 8.
   * The engine reports a large sentinel when an attack had nothing to try —
   * an empty attacker library, most often — and that is a missing reading, not
   * a wide margin. */
  var NO_READ = 10;

  function isReading(value) {
    return typeof value === 'number' && isFinite(value) && value < NO_READ;
  }

  /* A short human-readable name for whichever stored profile the library
   * replay matched. The engine reports it as
   * {"id": <profile id>, "source": {game, session, table_id|table}}; older or
   * simpler shapes (a bare string, a note, an id) are accepted too, and a
   * missing one just yields null. */
  function describeSource(entry) {
    if (!entry) return null;
    var raw = entry.source;
    if (typeof raw === 'string' && raw) return raw;
    if (raw && typeof raw === 'object') {
      var id = raw.id || raw.profile_id || null;
      var origin = raw.source && typeof raw.source === 'object' ? raw.source : null;
      var where = null;
      if (origin) {
        if (origin.game === 'standoff') where = 'off an earlier table of yours';
        else if (origin.game) where = 'out of a ' + origin.game + ' run';
      }
      var label = id ? 'the schedule filed as ' + shortId(id) : 'an unnamed schedule';
      return where ? label + ', ' + where : label;
    }
    if (typeof entry.note === 'string' && entry.note) return entry.note;
    var fallback = entry.profile_id || entry.id;
    return fallback ? 'the schedule filed as ' + shortId(fallback) : null;
  }

  function shortId(id) {
    var text = String(id);
    return text.length > 10 ? text.slice(0, 8) : text;
  }

  function healthOf(exploitability) {
    if (exploitability === null || exploitability === undefined) return 1;
    if (!isFinite(exploitability)) return 1;
    return Math.max(0, Math.min(1, (exploitability - EPS_KILL) / (TARGET - EPS_KILL)));
  }

  /* Every reading the player is given is one of these phrases. The numbers
   * behind them live in the ledger, never on the play surface. */
  function moodPhrase(value) {
    if (value === null || value === undefined || !isFinite(value)) {
      return 'nobody has called yet';
    }
    var health = healthOf(value);
    if (health <= 0) return 'settled — the argument is over';
    if (health < 0.18) return 'a hair from settling';
    if (health < 0.45) return 'they very nearly had it';
    if (health < 0.75) return 'holding, but somebody is close';
    return 'restless — nowhere near settling';
  }

  /* How close a single caller came, said out loud. */
  function callerPhrase(value) {
    var health = healthOf(value);
    if (health < 0.18) return 'came within a whisker of talking them round';
    if (health < 0.45) return 'got closer than you would like';
    if (health < 0.75) return 'made a decent try of it';
    return 'never got anywhere near it';
  }

  /* What a man stands to take for drawing first and alone. */
  function soloPhrase(value) {
    if (value >= 1.5) return 'has a fat stack riding on drawing first.';
    if (value >= 0.5) return 'does well for himself if he moves first.';
    if (value >= 0.1) return 'gets a little something for moving first.';
    if (value > -0.1) return 'gains nothing much either way.';
    return 'would be paying for the privilege of drawing first.';
  }

  var Game = {
    ROUNDS: ROUNDS,
    ANTAG: ANTAG,
    EPS_KILL: EPS_KILL,
    TARGET: TARGET,
    ui: null,
    state: null,
    busy: false,

    /* ------------------------------------------------------------ start -- */

    newRun: function (options) {
      options = options || {};
      var seed = (Date.now() ^ Math.floor(Math.random() * 0xffffff)) >>> 0;
      // Start on the lattice when that is legal; if snapping would offend the
      // house, begin where the table actually is. Either way every committed
      // edit snaps the whole table, and what is finally submitted is checked
      // rather than assumed.
      var raw = E.clampTable(E.cloneTable(options.table));
      var snapped = E.snapTable(E.cloneTable(raw));
      var startOnLattice = E.runFilters(snapped, E.MARGIN).pass;
      this.state = {
        session: uuid(),
        rng: E.mulberry32(seed),
        seed: seed,
        table: startOnLattice ? snapped : raw,
        startedOnLattice: startOnLattice,
        origin: options.origin || { kind: 'curated', id: options.id || null,
                                    name: options.name || 'unnamed table' },
        round: 0,
        budget: ROUNDS[0].budget,
        spent: 0,
        hand: [],
        trace: [],
        roundResults: [],
        runningMin: null,      // engine min over the waves of the current round
        bestSurviving: null,   // best round margin actually survived this run
        lastKill: null,
        reloads: 1,
        checkpoint: null,
        finished: false
      };
      Scene.clearCorpses();
      Scene.clearWave();
      Scene.setTable(this.state.table);
      Scene.setHealth(1, null, false);
      this.beginRound();
    },

    beginRound: function () {
      var state = this.state;
      var config = ROUNDS[state.round];
      state.budget = config.budget;
      state.spent = 0;
      state.runningMin = null;
      state.checkpoint = E.cloneTable(state.table);
      state.hand = Moves.dealHand(state.rng, state.table, 5, state.lastKill);
      Scene.setPhase('editing');
      Scene.clearWave();
      Scene.setTable(state.table);
      // The table has changed since the last bell, so last round's margin says
      // nothing about it. Start the round with no reading rather than a stale one.
      Scene.setHealth(1, null, false);
      this.ui.resetCallers();
      this.ui.renderRound();
      this.ui.say(config.brief);
    },

    /* ------------------------------------------------------------- cards -- */

    canPlay: function (card) {
      var state = this.state;
      if (this.busy || !state || state.finished) return false;
      if (card.spent) return false;
      if (!card.legal) return false;
      return card.cost <= (state.budget - state.spent);
    },

    playCard: function (card) {
      var self = this;
      var state = this.state;
      if (card.spent) return;
      if (!card.legal) {
        Audio.deny();
        this.ui.toast(card.objection, true);
        return;
      }
      if (card.cost > state.budget - state.spent) {
        Audio.deny();
        this.ui.toast('Not enough left in the kitty for that one.', true);
        return;
      }
      this.busy = true;
      var candidate = card.result;

      // The client already checked filters 1-5; the server is the authority on
      // whether the table is legal, so confirm before committing the edit.
      API.patient(function () { return API.filters(candidate); }, function () {
        self.ui.say('The house is slow to answer...');
      }).then(function (verdict) {
        if (!verdict.pass) {
          Audio.deny();
          var filters = E.normalizeFilters(verdict.filters);
          var objection = E.houseObjection({ filters: filters });
          card.legal = false;
          card.objection = objection;
          self.ui.toast('The house looked again: ' + objection, true);
          self.ui.renderHand();
          self.busy = false;
          return;
        }
        state.table = candidate;
        state.spent += card.cost;
        card.spent = true;
        state.trace.push({
          round: state.round + 1,
          kind: card.kind,
          title: card.title,
          detail: card.detail
        });
        Audio.chipDown();
        if (card.swap) Scene.swapSeats(card.swap[0], card.swap[1]);
        Scene.setTable(state.table);
        Scene.setHighlight({ players: [], pairs: [] });

        // Re-price the remaining hand against the new table.
        state.hand.forEach(function (other) {
          if (!other.spent) Moves.annotate(other, state.table);
        });
        self.ui.renderHand();
        self.ui.renderRound();
        self.ui.say(card.title + ': ' + card.detail + '.');
        self.busy = false;
      }, function (err) {
        self.busy = false;
        Audio.deny();
        self.ui.toast('The house did not answer: ' + err.message, true);
      });
    },

    /* ------------------------------------------------------------- waves -- */

    ringBell: function () {
      if (this.busy || !this.state || this.state.finished) return;
      var self = this;
      var state = this.state;
      var config = ROUNDS[state.round];
      this.busy = true;
      Scene.setPhase('waves');
      Audio.unlock();
      Audio.bell();
      this.ui.renderRound();
      this.ui.say('You ring the bell. The room goes quiet.');

      var roster = config.waves.slice();
      var levels = [];
      roster.forEach(function (key) {
        var level = ANTAG[key].level;
        if (levels.indexOf(level) < 0) levels.push(level);
      });

      var results = {};
      var killedBy = null;

      var runLevel = function (index) {
        if (index >= levels.length || killedBy) return Promise.resolve();
        var level = levels[index];
        var pending = roster.filter(function (key) { return ANTAG[key].level === level; });
        self.ui.say(self.levelLine(level, pending));
        return API.patient(function () { return API.attack(state.table, level); },
          function () { self.ui.say('The saloon is not open yet. The engine is still warming up...'); })
          .then(function (response) {
            results[level] = response;
            return pending.reduce(function (chain, key) {
              return chain.then(function () {
                if (killedBy) return null;
                var entry = response.breakdown && response.breakdown[key];
                return self.presentWave(key, entry, response).then(function (verdict) {
                  if (verdict === 'killed') {
                    killedBy = { key: key, entry: entry, response: response };
                  }
                });
              });
            }, Promise.resolve());
          })
          .then(function () { return runLevel(index + 1); });
      };

      runLevel(0).then(function () {
        if (killedBy) return self.tableSettled(killedBy);
        return self.roundSurvived(results, roster);
      }).catch(function (err) {
        self.busy = false;
        self.ui.toast('The night broke off: ' + (err.message || err), true);
        self.ui.say('Trouble with the house. Ring again when you are ready.');
        Scene.setPhase('editing');
        self.ui.renderRound();
      });
    },

    levelLine: function (level, pending) {
      var names = pending.map(function (k) { return ANTAG[k].name; }).join(', ');
      if (level === 'replay') return 'Cheapest first: ' + names + ' — no thinking required.';
      if (level === 'quick') return 'A short look from ' + names + '.';
      return 'The expensive callers now: ' + names + '.';
    },

    /* One wave: arrival, its schedule beating out on the table, then verdict. */
    presentWave: function (key, entry, response) {
      var self = this;
      var state = this.state;
      var info = ANTAG[key];
      this.ui.markCaller(key, 'active');

      if (!entry || !isReading(entry.exploitability)) {
        // Either the server did not report this attack at this level, or it
        // reported the "nothing to try" sentinel. Say so plainly rather than
        // inventing a verdict, and leave the running minimum alone.
        this.ui.markCaller(key, 'skipped', null);
        var why;
        if (!entry) {
          why = info.name + ' never showed. The house had no read on that one.';
        } else if (key === 'library_replay') {
          why = 'The Ghosts drift through and find nothing to repeat — the book ' +
            'is still empty. Every table you settle fills a page of it.';
        } else {
          why = info.name + ' had nothing to try. No reading from that one.';
        }
        this.ui.say(why);
        Scene.beginWave(key, null);
        Audio.sting(key);
        return sleep(1200).then(function () { Scene.clearWave(); });
      }

      var value = entry.exploitability;
      Scene.beginWave(key, entry.profile, key === 'two_quitter_periodic' ? 560 : 640);
      Audio.sting(key);
      Scene.shake(key === 'two_quitter_periodic' ? 8 : 3);
      this.ui.say(info.name + ' — ' + info.tell);

      return sleep(700).then(function () {
        return animateFor(key === 'library_replay' ? 1200 : 1700);
      }).then(function () {
        var previous = state.runningMin;
        var next = (previous === null) ? value : Math.min(previous, value);
        state.runningMin = next;
        var killed = next <= EPS_KILL;
        Scene.setHealth(healthOf(next), next, !!response.mock);
        if (self.ui.noteReading) self.ui.noteReading(value, !!response.mock, next);
        self.ui.markCaller(key, killed ? 'killed' : 'held', value);
        Scene.endWave(killed ? 'killed' : 'held');
        Scene.wave.verdictAt = performance.now();

        if (killed) {
          self.ui.say(info.name + ' found it. The four of them shake on it, ' +
            'nobody wants to be first out, and the night is over.');
          Audio.kill();
          Scene.shake(26);
          Scene.flashColour('#d1453f', 0.5);
          return sleep(1200).then(function () { return 'killed'; });
        }
        Audio.hold();
        Audio.heartbeat(1 - healthOf(next));
        Scene.flashColour(info.colour, 0.10);
        self.ui.say(info.name + ' walks out — ' + callerPhrase(value) +
          (value > next ? ', though somebody earlier came closer' : '') + '.');
        return sleep(750).then(function () {
          Scene.clearWave();
          return 'held';
        });
      });
    },

    /* --------------------------------------------------------- outcomes -- */

    roundSurvived: function (results, roster) {
      var self = this;
      var state = this.state;
      var config = ROUNDS[state.round];
      var margin = state.runningMin;
      state.roundResults.push({
        round: state.round + 1,
        waves: roster,
        min_exploitability: margin,
        levels: Object.keys(results)
      });
      if (margin !== null && (state.bestSurviving === null || margin > state.bestSurviving)) {
        state.bestSurviving = margin;
      }
      this.rememberBest(state.bestSurviving);
      Audio.victory();
      this.ui.renderRound();

      if (config.final) return this.bossFight();

      state.round += 1;
      this.busy = false;
      this.ui.say('The room clears. You have until the next bell.');
      return sleep(1200).then(function () {
        self.beginRound();
        return null;
      });
    },

    tableSettled: function (killedBy) {
      var self = this;
      var state = this.state;
      var info = ANTAG[killedBy.key];
      var entry = killedBy.entry;
      state.lastKill = {
        key: killedBy.key,
        antagonistName: info.name,
        profile: entry.profile,
        exploitability: entry.exploitability,
        source: describeSource(entry)
      };
      // Everyone quiets down: show who folded first under that schedule.
      var hazards = entry.profile && entry.profile.hazards;
      if (hazards) {
        var busiest = 0, bestSum = -1;
        for (var i = 0; i < 4; i++) {
          var sum = 0;
          for (var t = 0; t < hazards.length; t++) sum += hazards[t][i];
          if (sum > bestSum) { bestSum = sum; busiest = i; }
        }
        Scene.fell(busiest);
      }
      this.busy = false;
      state.finished = true;

      // The gang keeps every profile that ever worked. Submitting it is what
      // makes the next run harder, and it is the honest thing to record.
      var learn = Promise.resolve(null);
      if (entry.profile && entry.profile.hazards) {
        learn = API.submitProfile(entry.profile, {
          game: 'standoff',
          session: state.session,
          table: state.table
        }).catch(function () { return null; });
      }
      return learn.then(function (stored) {
        return self.ui.showDeath(killedBy, stored);
      });
    },

    /* --------------------------------------------------------- boss fight -- */

    bossFight: function () {
      var self = this;
      var state = this.state;
      Scene.setPhase('boss');
      Scene.beginWave('boss', null);
      Scene.setBoss(0);
      Audio.sting('boss');
      Audio.startDrone();
      this.ui.showBoss({ elapsed: 0, status: 'sending' });

      return API.patient(function () { return API.attack(state.table, 'deep'); },
        function () { self.ui.showBoss({ elapsed: 0, status: 'warming' }); })
        .then(function (response) {
          if (!response.job) {
            // Server answered synchronously; treat it as a finished job.
            return response;
          }
          return API.awaitJob(response.job, function (elapsed) {
            var progress = Math.min(0.96, elapsed / 45);
            Scene.setBoss(progress);
            Audio.setDroneIntensity(progress);
            self.ui.showBoss({ elapsed: elapsed, status: 'running' });
          });
        })
        .then(function (result) {
          Scene.setBoss(1);
          Audio.stopDrone();
          var score = result.score;
          if (!isReading(score)) {
            throw new API.ApiError('the Marshal came back with nothing readable', 500);
          }
          if (score <= EPS_KILL) {
            var binding = result.binding_attack;
            var entry = (result.breakdown && result.breakdown[binding]) ||
              { exploitability: score, profile: null };
            Audio.kill();
            Scene.shake(30);
            Scene.flashColour('#d1453f', 0.6);
            return self.tableSettled({
              key: binding && ANTAG[binding] ? binding : 'boss',
              entry: entry,
              response: result,
              boss: true
            });
          }
          state.runningMin = Math.min(state.runningMin === null ? score : state.runningMin, score);
          state.bestSurviving = Math.max(state.bestSurviving || 0, score);
          Audio.victory();
          Scene.clearWave();
          Scene.setHealth(healthOf(score), score, !!result.mock);
          return self.submitSurvivor(result);
        })
        .catch(function (err) {
          Audio.stopDrone();
          self.busy = false;
          self.ui.toast('The Marshal never reported back: ' + (err.message || err), true);
          self.ui.showBossFailure(err);
        });
    },

    submitSurvivor: function (deepResult) {
      var self = this;
      var state = this.state;
      this.ui.showSubmitting();
      var payload = {
        table: state.table,
        game: 'standoff',
        session: state.session,
        provenance: {
          origin: state.origin,
          run_seed: state.seed,
          subspace: {
            lattice: '1/4',
            range: [E.LO, E.HI],
            holds: E.isOnLattice(state.table),
            started_on_lattice: state.startedOnLattice,
            note: 'standoff restricts play to the quarter sublattice of ' +
              '[-4,4] so that edits read as card play and runs are ' +
              'reproducible. This is a restriction of the search, not ' +
              'coverage of it: tables off this lattice were never examined.'
          },
          rounds: state.roundResults,
          action_trace: state.trace,
          client_deep_result: {
            score: deepResult.score,
            binding_attack: deepResult.binding_attack,
            level: deepResult.level || 'deep',
            mock: !!deepResult.mock
          },
          note: 'standoff run: survived five bells and the deep re-attack as ' +
            'presented in-game; the recorded evaluation below is the server\'s.'
        }
      };
      return API.patient(function () { return API.submitCandidate(payload); })
        .then(function (response) {
          state.finished = true;
          self.busy = false;
          self.rememberBest(state.bestSurviving);
          return self.ui.showVictory(response, deepResult);
        }, function (err) {
          state.finished = true;
          self.busy = false;
          self.ui.toast('The table survived but the ledger refused it: ' +
            (err.message || err), true);
          return self.ui.showVictory(null, deepResult, err);
        });
    },

    /* -------------------------------------------------------- second wind -- */

    reload: function () {
      var state = this.state;
      if (!state || state.reloads <= 0 || !state.checkpoint) return false;
      state.reloads -= 1;
      state.table = state.checkpoint;
      state.finished = false;
      state.runningMin = null;
      Scene.clearCorpses();
      Scene.clearWave();
      Scene.setTable(state.table);
      this.busy = false;
      this.beginRound();
      Audio.card();
      this.ui.say('You palm the deck back. One more time, and this is the last ' +
        'time the house looks away.');
      return true;
    },

    /* ------------------------------------------------------------- score -- */

    personalBest: function () {
      try {
        var raw = root.localStorage.getItem(BEST_KEY);
        return raw === null ? null : Number(raw);
      } catch (e) { return null; }
    },

    rememberBest: function (value) {
      if (typeof value !== 'number' || !isFinite(value)) return;
      try {
        var current = this.personalBest();
        if (current === null || value > current) {
          root.localStorage.setItem(BEST_KEY, String(value));
        }
      } catch (e) { /* private mode; the run still counts on screen */ }
    },

    healthOf: healthOf,
    isReading: isReading,
    describeSource: describeSource,
    moodPhrase: moodPhrase,
    callerPhrase: callerPhrase,
    soloPhrase: soloPhrase,
    uuid: uuid,
    sleep: sleep
  };

  root.SOGame = Game;
})(window);
