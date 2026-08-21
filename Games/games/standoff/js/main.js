/* standoff — DOM layer: the hand, the nerve gauge, the overlays, and boot.
 *
 * Full diegesis is the rule here: nothing on the play surface states a number,
 * a threshold, or a word from the mathematics. Every reading is carried by the
 * gauge, by colour and motion, and by what the room says. The one exception is
 * the ledger, which holds the real table, the real
 * figures, and the honesty statement in full.
 */
(function (root) {
  'use strict';

  var E = root.SOEval;
  var API = root.SOApi;
  var Audio = root.SOAudio;
  var Scene = root.SOScene;
  var Moves = root.SOMoves;
  var Game = root.SOGame;
  var ANTAG = Scene.ANTAGONISTS;

  var el = function (id) { return document.getElementById(id); };
  var dom = {};
  var stats = { library_profiles: null, candidates: null, best_score: null };
  var curatedCache = [];
  var stripHandle = null;
  var toastTimer = null;
  var COACH_KEY = 'standoff:coached';

  /* Everything the fiction deliberately does not say, kept for the ledger. */
  var ledger = {
    reading: null, hearsay: false, roundWorst: null, bestRun: null,
    lastKill: null, tier: null, recordId: null, deepScore: null
  };

  function text(node, value) { node.textContent = value; }

  function make(tag, className, content) {
    var node = document.createElement(tag);
    if (className) node.className = className;
    if (content !== undefined) node.textContent = content;
    return node;
  }

  function fmt(value, digits) {
    if (value === null || value === undefined || !isFinite(value)) return '—';
    return Number(value).toFixed(digits === undefined ? 4 : digits);
  }

  function fmtSmall(value) {
    if (value === null || value === undefined || !isFinite(value)) return '—';
    var v = Number(value);
    if (v !== 0 && Math.abs(v) < 1e-4) return v.toExponential(2);
    return v.toFixed(5);
  }

  // ------------------------------------------------------------ nerve gauge --

  /* No readout. The bar is the instrument: its length is how far the table is
   * from settling, its grain and shiver are how nearly the last caller got
   * there, and the two marks are the best this run and the best ever. */
  function drawNerve() {
    var canvas = dom.nerve;
    if (!canvas) return requestAnimationFrame(drawNerve);
    var rect = canvas.getBoundingClientRect();
    var dpr = Math.min(root.devicePixelRatio || 1, 2);
    if (canvas.width !== Math.round(rect.width * dpr)) {
      canvas.width = Math.round(rect.width * dpr);
      canvas.height = Math.round(22 * dpr);
    }
    var ctx = canvas.getContext('2d');
    ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
    var w = rect.width, h = 22, top = 5, bar = 11;
    ctx.clearRect(0, 0, w, h);

    var health = Scene.health;
    var value = Scene.exploitability;
    var known = value !== null && value !== undefined && isFinite(value);
    var closeness = known ? 1 - health : 0;
    var shiver = closeness * closeness * 2.6;

    ctx.save();
    if (shiver > 0.05 && !Scene.reduceMotion) {
      ctx.translate((Math.random() - 0.5) * shiver, (Math.random() - 0.5) * shiver * 0.5);
    }

    ctx.fillStyle = 'rgba(255,255,255,0.05)';
    ctx.fillRect(0, top, w, bar);

    var filled = w * health;
    var grad = ctx.createLinearGradient(0, 0, w, 0);
    grad.addColorStop(0, '#d1453f');
    grad.addColorStop(0.42, '#e8b25f');
    grad.addColorStop(1, '#7fc79a');
    ctx.fillStyle = grad;
    ctx.globalAlpha = known ? 1 : 0.22;
    ctx.fillRect(0, top, filled, bar);
    ctx.globalAlpha = 1;

    if (closeness > 0.02) {
      var grains = Math.floor(closeness * closeness * 300);
      ctx.fillStyle = 'rgba(0,0,0,0.55)';
      for (var g = 0; g < grains; g++) {
        ctx.fillRect(Math.random() * Math.max(filled, 6), top + Math.random() * bar, 1.6, 1.6);
      }
      ctx.fillStyle = 'rgba(255,220,210,0.32)';
      for (var s = 0; s < grains / 3; s++) {
        ctx.fillRect(Math.random() * w, top + Math.random() * bar, 1.2, 1.2);
      }
    }

    // The edge the table must not fall past, and the far end worth reaching.
    ctx.fillStyle = 'rgba(209,69,63,0.95)';
    ctx.fillRect(0, 1, 2, h - 2);
    ctx.fillStyle = 'rgba(127,199,154,0.65)';
    ctx.fillRect(w - 2, 1, 2, h - 2);

    // A notch for the best the table held tonight.
    var state = Game.state;
    if (state && state.bestSurviving !== null) {
      markAt(ctx, w * Game.healthOf(state.bestSurviving), top, bar, 'notch');
    }
    // A medal for the best ever, so a run has something to beat.
    var best = Game.personalBest();
    if (best !== null) markAt(ctx, w * Game.healthOf(best), top, bar, 'medal');
    ctx.restore();

    text(dom.nerveNote, known ? Game.moodPhrase(value) : 'nobody has called yet');
    requestAnimationFrame(drawNerve);
  }

  function markAt(ctx, x, top, bar, kind) {
    ctx.save();
    if (kind === 'medal') {
      ctx.fillStyle = '#f4e08a';
      ctx.shadowColor = 'rgba(244,224,138,0.9)';
      ctx.shadowBlur = 7;
      ctx.beginPath();
      for (var i = 0; i < 10; i++) {
        var ang = (Math.PI / 5) * i - Math.PI / 2;
        var rad = i % 2 ? 1.9 : 4.6;
        ctx[i ? 'lineTo' : 'moveTo'](x + Math.cos(ang) * rad, top + bar / 2 + Math.sin(ang) * rad);
      }
      ctx.closePath();
      ctx.fill();
    } else {
      ctx.fillStyle = 'rgba(236,223,201,0.92)';
      ctx.beginPath();
      ctx.moveTo(x, top - 4);
      ctx.lineTo(x - 3.5, top - 0.5);
      ctx.lineTo(x + 3.5, top - 0.5);
      ctx.closePath();
      ctx.fill();
      ctx.fillRect(x - 0.6, top, 1.2, bar);
    }
    ctx.restore();
  }

  // ------------------------------------------------------------ timing strip --

  /* The killing schedule as what it is: who reaches for the iron on which
   * beat. Dot size carries the eagerness; no figures are printed. */
  function renderStrip(canvas, profile, colour) {
    if (stripHandle) { cancelAnimationFrame(stripHandle); stripHandle = null; }
    if (!canvas || !profile || !profile.hazards || !profile.hazards.length) return;
    var hazards = profile.hazards;
    var P = hazards.length;
    var dpr = Math.min(root.devicePixelRatio || 1, 2);
    var start = performance.now();
    var beatMs = 620;

    var step = function () {
      var rect = canvas.getBoundingClientRect();
      var w = Math.max(200, rect.width), h = 128;
      if (canvas.width !== Math.round(w * dpr)) {
        canvas.width = Math.round(w * dpr);
        canvas.height = Math.round(h * dpr);
      }
      var ctx = canvas.getContext('2d');
      ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
      ctx.clearRect(0, 0, w, h);

      var left = 82, top = 16, rowH = 24;
      var colW = (w - left - 12) / P;
      var head = ((performance.now() - start) / beatMs) % P;

      for (var t = 0; t < P; t++) {
        ctx.fillStyle = (t % 2) ? 'rgba(255,255,255,0.03)' : 'rgba(255,255,255,0.05)';
        ctx.fillRect(left + t * colW, top - 8, colW - 2, rowH * 4 + 8);
      }

      for (var i = 0; i < 4; i++) {
        var y = top + i * rowH + 8;
        ctx.fillStyle = 'rgba(236,223,201,0.68)';
        ctx.font = '10px ui-monospace, monospace';
        ctx.textAlign = 'right';
        ctx.fillText(E.NAMES[i], left - 10, y + 4);
        for (var b = 0; b < P; b++) {
          var hazard = hazards[b][i];
          var cx = left + b * colW + colW / 2;
          ctx.beginPath();
          ctx.arc(cx, y, 8, 0, Math.PI * 2);
          ctx.strokeStyle = 'rgba(255,255,255,0.10)';
          ctx.lineWidth = 1;
          ctx.stroke();
          if (hazard > 0.001) {
            var live = Math.abs(head - b) < 0.5 || Math.abs(head - b - P) < 0.5;
            ctx.fillStyle = colour;
            ctx.globalAlpha = 0.22 + 0.78 * Math.min(1, hazard) * (live ? 1 : 0.55);
            ctx.beginPath();
            ctx.arc(cx, y, 2.5 + 6 * Math.min(1, hazard), 0, Math.PI * 2);
            ctx.fill();
            ctx.globalAlpha = 1;
          }
        }
      }

      var hx = left + head * colW + colW / 2;
      ctx.strokeStyle = 'rgba(255,255,255,0.35)';
      ctx.lineWidth = 1.5;
      ctx.beginPath();
      ctx.moveTo(hx, top - 8); ctx.lineTo(hx, top + rowH * 4);
      ctx.stroke();

      stripHandle = requestAnimationFrame(step);
    };
    stripHandle = requestAnimationFrame(step);
  }

  function describeSchedule(profile) {
    if (!profile || !profile.hazards) return 'No timing came back with that one.';
    var hazards = profile.hazards, P = hazards.length;
    var activePerBeat = hazards.map(function (row) {
      return row.map(function (h, i) { return { i: i, h: h }; })
        .filter(function (x) { return x.h > 0.02; });
    });
    var maxCount = Math.max.apply(null, activePerBeat.map(function (a) { return a.length; }));
    var lead = 'The same ' + (P === 1 ? 'single beat' : P + '-beat figure') + ', over and over. ';
    if (P === 1) {
      return lead + 'Nobody waits for anybody — every one of them carries the same ' +
        'itch every beat, and that alone is enough to hold the table still.';
    }
    if (maxCount === 1) {
      var order = activePerBeat.map(function (a) {
        return a.length ? E.NAMES[a[0].i] : 'nobody';
      });
      return lead + 'One man a beat: ' + order.join(' → ') + ', then round again. ' +
        'They take turns, so nobody has cause to jump the queue.';
    }
    if (maxCount === 2) {
      var pairs = activePerBeat.map(function (a) {
        return a.length === 2 ? (E.NAMES[a[0].i] + ' + ' + E.NAMES[a[1].i])
          : a.map(function (x) { return E.NAMES[x.i]; }).join(' + ') || 'nobody';
      });
      return lead + 'Two at a time, alternating: ' + pairs.join(', then ') + '. ' +
        'Each pair covers for the other, and the grudges you stoked are exactly ' +
        'what holds it together.';
    }
    return lead + 'All four moving every beat, each on his own clock. Loose — but ' +
      'it fits your table.';
  }

  // ----------------------------------------------------------------- overlay --

  function closeOverlay() {
    dom.overlay.classList.add('hidden');
    dom.overlay.innerHTML = '';
    if (stripHandle) { cancelAnimationFrame(stripHandle); stripHandle = null; }
  }

  function sheet(builder) {
    if (stripHandle) { cancelAnimationFrame(stripHandle); stripHandle = null; }
    dom.overlay.innerHTML = '';
    var node = make('div', 'sheet');
    builder(node);
    dom.overlay.appendChild(node);
    dom.overlay.classList.remove('hidden');
    return node;
  }

  function button(label, className, handler) {
    var node = make('button', className, label);
    node.type = 'button';
    node.addEventListener('click', function () { Audio.click(); handler(); });
    return node;
  }

  function ledgerButton() {
    return button('the clerk\u2019s ledger', 'big quiet', function () {
      dom.hood.classList.remove('hidden');
      renderHood();
    });
  }

  function pipRow(filled, total) {
    var row = make('div', 'bells');
    for (var i = 0; i < total; i++) {
      var pip = make('i');
      if (i < filled) pip.className = 'rung';
      row.appendChild(pip);
    }
    return row;
  }

  // ---------------------------------------------------------------------- UI --

  var UI = {
    say: function (message) { text(dom.ticker, message || ''); },

    toast: function (message, bad) {
      dom.toast.textContent = message;
      dom.toast.className = 'toast' + (bad ? ' bad' : '');
      if (toastTimer) clearTimeout(toastTimer);
      toastTimer = setTimeout(function () { dom.toast.classList.add('hidden'); }, 4200);
    },

    renderRound: function () {
      var state = Game.state;
      if (!state) return;
      var config = Game.ROUNDS[state.round];
      text(dom.bellName, config.name);

      dom.bells.innerHTML = '';
      for (var b = 0; b < Game.ROUNDS.length; b++) {
        var pip = make('i');
        if (b < state.round) pip.className = 'rung';
        else if (b === state.round) pip.className = 'now';
        dom.bells.appendChild(pip);
      }

      dom.budgetPips.innerHTML = '';
      for (var k = 0; k < state.budget; k++) {
        var chip = make('i');
        if (k < state.spent) chip.className = 'spent';
        dom.budgetPips.appendChild(chip);
      }

      this.renderTricks();
      this.renderCallers();
      this.renderHand();
      dom.bellBtn.disabled = Scene.phase !== 'editing' || state.finished;
      text(dom.bellSub, Scene.phase === 'editing' ? 'let them in' : 'they are already here');
      ledger.bestRun = state.bestSurviving;
      if (!dom.hood.classList.contains('hidden')) renderHood();
    },

    renderTricks: function () {
      var n = stats.library_profiles;
      text(dom.tricksLabel, n === null
        ? 'the gang is still counting its tricks'
        : 'the gang knows ' + n + ' trick' + (n === 1 ? '' : 's'));
    },

    /* Callers live in the scene: waiting in the doorway, and as portrait chips.
     * No roster, no sentences — their names are learned by watching them. */
    renderCallers: function () {
      var state = Game.state;
      if (!state) return;
      var config = Game.ROUNDS[state.round];
      var all = ['library_replay', 'stationary', 'one_quitter_cyclic',
        'general_periodic', 'two_quitter_periodic'];
      Scene.setCallers(all.map(function (key) {
        var known = Scene.callers.filter(function (c) { return c.key === key; })[0];
        var inRound = config.waves.indexOf(key) >= 0;
        var state2 = inRound ? 'pending' : 'locked';
        if (known && inRound && ['active', 'held', 'settled', 'skipped']
            .indexOf(known.state) >= 0) {
          state2 = known.state;
        }
        return { key: key, state: state2 };
      }));
    },

    markCaller: function (key, status, value) {
      var map = { active: 'active', held: 'held', killed: 'settled', skipped: 'skipped' };
      Scene.setCallerState(key, map[status] || 'pending');
    },

    resetCallers: function () { Scene.setCallers([]); },

    renderHand: function () {
      var state = Game.state;
      dom.hand.innerHTML = '';
      if (!state) return;
      var spotlight = shouldCoach() ? firstPlayable(state.hand) : null;
      state.hand.forEach(function (card) {
        var node = make('button', 'card' + (card.legal ? '' : ' illegal') +
          (card.spent ? ' spent' : '') + (card === spotlight ? ' spotlight' : ''));
        node.type = 'button';
        node.disabled = !Game.canPlay(card);
        node.appendChild(make('div', 'card-title', card.title));
        node.appendChild(make('div', 'card-sub', card.subtitle || ''));
        node.appendChild(make('div', 'card-flavour', card.flavour));
        if (card.legal) {
          node.appendChild(make('div', 'card-detail', card.blurb || ''));
        } else {
          node.appendChild(make('div', 'card-stamp', 'THE HOUSE SAYS NO'));
          node.appendChild(make('div', 'card-objection', card.objection || ''));
        }
        var cost = make('div', 'card-cost');
        for (var c = 0; c < card.cost; c++) cost.appendChild(make('span', 'coin', '●'));
        node.appendChild(cost);
        node.addEventListener('mouseenter', function () {
          Scene.setHighlight({
            players: card.targets.players || [],
            pairs: card.targets.pairs || [],
            pot: !!card.targets.pot
          });
          UI.say(card.legal ? readCard(card) : 'The house: ' + card.objection);
        });
        node.addEventListener('mouseleave', function () {
          Scene.setHighlight({ players: [], pairs: [], pot: false });
        });
        node.addEventListener('click', function () {
          if (card.spent) return;
          Audio.card();
          Game.playCard(card);
        });
        dom.hand.appendChild(node);
      });
      if (spotlight) showCoach('play a card, then ring the bell');
      else hideCoach();
    },

    /* ------------------------------------------------------------- screens -- */

    showPicker: function () {
      sheet(function (node) {
        node.appendChild(make('h1', null, 'DEAL AGAIN'));
        node.appendChild(make('p', 'lead',
          'Pick the table you want to work tonight, or let the room shuffle one.'));
        var list = make('div', 'pick-list');
        curatedCache.forEach(function (entry) {
          var pick = make('button', 'pick');
          pick.type = 'button';
          pick.appendChild(make('div', 'pick-name', tableLabel(entry)));
          pick.appendChild(make('div', 'pick-note', tableNote(entry)));
          pick.addEventListener('click', function () {
            Audio.unlock(); Audio.click();
            closeOverlay();
            startRun(entry);
          });
          list.appendChild(pick);
        });
        var shuffle = make('button', 'pick');
        shuffle.type = 'button';
        shuffle.appendChild(make('div', 'pick-name', 'Shuffle a fresh deck'));
        shuffle.appendChild(make('div', 'pick-note',
          'A jostled version of one of the above, screened so at least the ' +
          'laziest gang cannot settle it on sight.'));
        shuffle.addEventListener('click', function () {
          Audio.unlock(); Audio.click();
          closeOverlay();
          startShuffled();
        });
        list.appendChild(shuffle);
        node.appendChild(list);
        var row = make('div', 'row');
        row.appendChild(button('never mind', 'big quiet', function () { closeOverlay(); }));
        node.appendChild(row);
      });
    },

    showDeath: function (killedBy, stored) {
      var state = Game.state;
      var info = ANTAG[killedBy.key] || ANTAG.boss;
      var entry = killedBy.entry;
      Scene.setPhase('dead');
      Audio.stopDrone();
      ledger.lastKill = {
        who: info.name, attack: killedBy.key,
        exploitability: entry.exploitability, boss: !!killedBy.boss
      };
      if (stored) {
        stats.library_profiles = (stats.library_profiles || 0) + 1;
        refreshStats();
      }
      UI.renderTricks();

      sheet(function (node) {
        node.appendChild(make('h1', 'bad', 'THE TABLE SETTLES'));
        node.appendChild(make('p', 'lead',
          (killedBy.boss ? 'The Marshal took his time and found it. ' : '') +
          info.name + ' found an arrangement all four of them can live with.'));
        node.appendChild(make('p', null, info.tell));
        if (killedBy.key === 'library_replay') {
          var origin = state.lastKill && state.lastKill.source;
          node.appendChild(make('p', null, origin
            ? 'They did not have to think: that figure is already in the book — ' +
              origin + '. Somebody rigged a table like yours before.'
            : 'They did not have to think. That figure was already in the book ' +
              'from an earlier table.'));
        }

        node.appendChild(make('h2', null, 'HOW THEY TIMED IT'));
        var canvas = make('canvas', 'strip');
        canvas.height = 128;
        node.appendChild(canvas);
        node.appendChild(make('div', 'strip-legend',
          'bigger dot, hungrier man on that beat'));
        node.appendChild(make('p', null, describeSchedule(entry.profile)));

        var bells = make('p', null);
        bells.appendChild(document.createTextNode('bells you rang and survived:  '));
        bells.appendChild(pipRow(state.round, Game.ROUNDS.length));
        bells.style.display = 'flex';
        bells.style.alignItems = 'center';
        bells.style.gap = '10px';
        node.appendChild(bells);

        node.appendChild(make('p', 'fine', stored
          ? 'The gang copied that timing into their own book. It is the first ' +
            'thing they will try against your next table.'
          : 'Nobody copied it down, so nobody learned anything from this one.'));

        var row = make('div', 'row');
        if (state.reloads > 0) {
          row.appendChild(button('PALM THE DECK BACK', 'big', function () {
            closeOverlay();
            Game.reload();
          }));
        }
        row.appendChild(button('DEAL AGAIN', state.reloads > 0 ? 'big quiet' : 'big',
          function () { closeOverlay(); startFresh(); }));
        row.appendChild(ledgerButton());
        row.appendChild(button('out into the street', 'big quiet', function () {
          root.location.href = '/';
        }));
        node.appendChild(row);

        renderStrip(canvas, entry.profile, info.colour);
      });
    },

    showBoss: function (progress) {
      var lines = [
        'The room empties out. Nobody wants to be here for this.',
        'He is reading the sheet. All of it.',
        'He tries a rhythm, discards it, tries another.',
        'Upstairs, the piano stops.',
        'He has been at it a while now.',
        'Still going. He does not look tired.'
      ];
      var index = Math.min(lines.length - 1, Math.floor(progress.elapsed / 7));
      sheet(function (node) {
        node.appendChild(make('h1', null, 'THE MARSHAL'));
        node.appendChild(make('p', 'lead', progress.status === 'warming'
          ? 'The saloon is still opening up. He waits by the door.'
          : ANTAG.boss.tell));
        var status = make('p', null);
        status.appendChild(make('span', 'spinner'));
        status.appendChild(document.createTextNode('  ' + lines[index]));
        node.appendChild(status);
        node.appendChild(make('p', 'fine',
          'He will try everything the gang can afford to try, and more besides. ' +
          'Tables have walked past every caller tonight and lost this one.'));
      });
    },

    showBossFailure: function (err) {
      ledger.lastKill = null;
      sheet(function (node) {
        node.appendChild(make('h1', 'bad', 'HE NEVER CAME BACK'));
        node.appendChild(make('p', 'lead',
          'No word from the Marshal, so the night has no verdict and nothing ' +
          'was written down.'));
        node.appendChild(make('p', 'fine', String(err && err.message ? err.message : err)));
        var row = make('div', 'row');
        row.appendChild(button('DEAL AGAIN', 'big', function () {
          closeOverlay(); startFresh();
        }));
        node.appendChild(row);
      });
    },

    showSubmitting: function () {
      sheet(function (node) {
        node.appendChild(make('h1', 'good', 'THE TABLE HOLDS'));
        node.appendChild(make('p', 'lead',
          'The Marshal walks out without a figure. Your table is still restless.'));
        var status = make('p', null);
        status.appendChild(make('span', 'spinner'));
        status.appendChild(document.createTextNode('  Walking it over to the clerk...'));
        node.appendChild(status);
      });
    },

    showVictory: function (response, deepResult, err) {
      var state = Game.state;
      var record = response && response.record;
      ledger.tier = record ? record.tier : null;
      ledger.recordId = record ? record.id : null;
      ledger.deepScore = deepResult ? deepResult.score : null;
      ledger.recordedScore = record && record.evaluation ? record.evaluation.score : null;
      Scene.setPhase('won');

      sheet(function (node) {
        node.appendChild(make('h1', 'good', 'THE TABLE HOLDS'));
        node.appendChild(make('p', 'lead',
          'Every bell, and the Marshal after them, and not one of them could ' +
          'talk the other three into settling. The clerk takes down the sheet ' +
          'and files it.'));

        var bells = make('p', null);
        bells.appendChild(document.createTextNode('a clean night:  '));
        bells.appendChild(pipRow(Game.ROUNDS.length, Game.ROUNDS.length));
        bells.style.display = 'flex';
        bells.style.alignItems = 'center';
        bells.style.gap = '10px';
        node.appendChild(bells);

        node.appendChild(make('p', null,
          'At its steadiest tonight the table was ' +
          Game.moodPhrase(state.bestSurviving) +
          (Game.personalBest() !== null && state.bestSurviving >= Game.personalBest()
            ? '. The steadiest you have ever rigged.' : '.')));

        if (err) {
          node.appendChild(make('p', 'fine',
            'The clerk would not take it (' + (err.message || err) +
            '), so tonight left no record.'));
        } else if (API.mock) {
          node.appendChild(make('p', 'fine',
            'Practice night: the clerk is not in, and nothing you did here was ' +
            'written down anywhere.'));
        }

        node.appendChild(make('h2', null, 'HOW YOU RIGGED IT'));
        node.appendChild(make('p', 'fine', traceStory(state.trace)));

        var row = make('div', 'row');
        row.appendChild(button('DEAL AGAIN', 'big', function () {
          closeOverlay(); startFresh();
        }));
        row.appendChild(ledgerButton());
        row.appendChild(button('pass the sheet along', 'big quiet', function () {
          root.location.href = '/sequencer/?table=' + encodeTable(state.table) +
            (API.mock ? '&mock=1' : '');
        }));
        row.appendChild(button('out into the street', 'big quiet', function () {
          root.location.href = '/';
        }));
        node.appendChild(row);
      });
    },

    /* Called by the run so the ledger can hold what the fiction will not say. */
    noteReading: function (value, hearsay, roundWorst) {
      ledger.reading = value;
      ledger.hearsay = !!hearsay;
      ledger.roundWorst = roundWorst;
      if (!dom.hood.classList.contains('hidden')) renderHood();
    }
  };

  /* The fixer's gut on a card. A feel, never a figure. */
  function readCard(card) {
    if (card.hunch === undefined) card.hunch = E.hunch(card.result);
    var value = card.hunch;
    var mood;
    if (value <= Game.EPS_KILL) mood = 'even a lazy gang settles that in one beat';
    else if (value < 0.05) mood = 'that leaves them uncomfortably close';
    else if (value < 0.12) mood = 'that keeps them itchy';
    else mood = 'that would have them at each other all night';
    return 'Your gut on ' + card.title.toLowerCase() + ': ' + mood + '.';
  }

  /* The run's edits, told by which bell they were made before. */
  function traceStory(trace) {
    if (!trace.length) return 'You never touched the sheet.';
    var buckets = [];
    trace.forEach(function (entry) {
      var name = (Game.ROUNDS[entry.round - 1] || {}).name || 'that bell';
      var last = buckets[buckets.length - 1];
      if (last && last.name === name) last.titles.push(entry.title);
      else buckets.push({ name: name, titles: [entry.title] });
    });
    return buckets.map(function (b) {
      return b.name.toLowerCase() + ' — ' + b.titles.join(', ');
    }).join(' · ');
  }

  function firstPlayable(hand) {
    for (var i = 0; i < hand.length; i++) if (Game.canPlay(hand[i])) return hand[i];
    return null;
  }

  // ------------------------------------------------------------- coach mark --

  function coached() {
    try { return root.localStorage.getItem(COACH_KEY) === '1'; }
    catch (e) { return true; }
  }

  function markCoached() {
    try { root.localStorage.setItem(COACH_KEY, '1'); } catch (e) { /* private mode */ }
  }

  /* Only on the very first visit, and only until the first bell is rung. */
  function shouldCoach() {
    var state = Game.state;
    return !coached() && !!state && state.round === 0 && state.spent === 0 &&
      Scene.phase === 'editing';
  }

  function showCoach(message) {
    text(dom.coach, message);
    dom.coach.classList.remove('hidden');
  }

  function hideCoach() { dom.coach.classList.add('hidden'); }

  // ------------------------------------------------------------- hood/ledger --

  var HONESTY = 'What a survivor is: a table that a bounded, local search over a ' +
    'handful of profile families — a library replay, a stationary grid, ' +
    'one-quitter cycles, general periodic hazards, and two-quitter schedules, ' +
    'each with finitely many local optimizations — failed to settle. That is a ' +
    'record of search effort. It is not a proof that no settling profile exists, ' +
    'and it says nothing about profiles outside those families. Every apparent ' +
    'survivor in the recorded experiment turned out to be an optimizer artifact ' +
    'once it was attacked harder. Scores shown here come from the portal engine; ' +
    'the score actually recorded is the one the server computes when a table is ' +
    'submitted.';

  function renderHood() {
    var state = Game.state;
    if (!state) return;

    var nums = dom.hoodNumbers;
    nums.innerHTML = '';
    nums.appendChild(make('h2', null, 'TONIGHT\u2019S ENTRIES'));
    var grid = make('div', 'num-grid');
    function row(key, value) {
      grid.appendChild(make('div', 'k', key));
      grid.appendChild(make('div', 'v', value));
    }
    // The clerk records what the saloon renames, including the restriction.
    row('sheet from', (state.origin && (state.origin.name || state.origin.id)) || '—');
    if (state.origin && state.origin.id) row('curated id', state.origin.id);
    row('subspace', 'quarter lattice of [-4, 4]' +
      (E.isOnLattice(state.table) ? '' : ' — this sheet is currently off it'));
    row('kill threshold (eps_kill)', fmt(Game.EPS_KILL, 2));
    row('target margin (g)', fmt(Game.TARGET, 2));
    row('last reading' + (ledger.hearsay ? ' (mock)' : ''), fmtSmall(ledger.reading));
    row('worst this round', fmtSmall(state.runningMin));
    row('best margin survived this run', fmtSmall(state.bestSurviving));
    row('personal best', fmtSmall(Game.personalBest()));
    if (ledger.lastKill) {
      row('killed by', ledger.lastKill.attack +
        (ledger.lastKill.boss ? ' (deep re-attack)' : ''));
      row('killing exploitability', fmtSmall(ledger.lastKill.exploitability));
    }
    if (ledger.deepScore !== null && ledger.deepScore !== undefined) {
      row('deep re-attack score', fmtSmall(ledger.deepScore));
    }
    if (ledger.recordedScore !== null && ledger.recordedScore !== undefined) {
      row('recorded score (server)', fmtSmall(ledger.recordedScore));
    }
    if (ledger.tier) row('evidence tier', ledger.tier);
    if (ledger.recordId) row('record id', ledger.recordId);
    row('session', state.session);
    nums.appendChild(grid);

    var table = state.table;
    var wrap = dom.hoodTable;
    wrap.innerHTML = '';
    wrap.appendChild(make('h2', null, 'THE REWARD TABLE'));
    var t = make('table');
    var head = make('tr');
    head.appendChild(make('th', null, 'coalition'));
    head.appendChild(make('th', null, 'mask'));
    E.NAMES.forEach(function (name) { head.appendChild(make('th', null, name)); });
    t.appendChild(head);
    for (var m = 0; m < 16; m++) {
      var tr = make('tr');
      tr.appendChild(make('td', 'coal', m === 0 ? '(nobody)' : E.coalitionName(m)));
      tr.appendChild(make('td', null, String(m)));
      for (var i = 0; i < 4; i++) tr.appendChild(make('td', null, table[m][i].toFixed(3)));
      t.appendChild(tr);
    }
    wrap.appendChild(t);

    var verdict = E.runFilters(table, E.MARGIN);
    dom.hoodFilters.innerHTML = '';
    dom.hoodFilters.appendChild(make('h2', null, 'FILTERS 1-5 (client copy)'));
    E.FILTER_KEYS.slice(0, 5).forEach(function (key) {
      var f = verdict.filters[key];
      var line = make('div', 'f-row');
      line.appendChild(make('span', f.pass ? 'f-ok' : 'f-no', f.pass ? 'pass' : 'FAIL'));
      line.appendChild(make('span', null, E.FILTER_TITLES[key]));
      dom.hoodFilters.appendChild(line);
    });
    dom.hoodFilters.appendChild(make('p', 'hood-note',
      'Filter 6 (the LCP screen) is only ever evaluated by the server. These ' +
      'five are the client copy used to grey out cards instantly; the server ' +
      're-checks every committed edit.'));

    dom.hoodHonesty.innerHTML = '';
    dom.hoodHonesty.appendChild(make('p', 'honesty', HONESTY));
  }

  // -------------------------------------------------------------- boot bits --

  /* The saloon has its own names for the decks it keeps. The server's id and
   * name still travel in the submission provenance and are shown in the
   * ledger; they are never printed on the play surface, because there is no
   * guarantee they read as fiction. */
  var NICKNAMES = {
    'solan_vieille_seed': ['The House Deck',
      'The one the old-timers still argue about. Everything balances, and ' +
      'that is exactly the trouble: a pair of them can settle it in two beats.'],
    'chain_40': ['Marlowe\u2019s Ledger',
      'Rigged by a patient man over a long winter. It held up for a while.'],
    'chain_41': ['The Long Con',
      'Survived a whole night of questioning before somebody took it apart.'],
    'chain_42': ['Ashfield Pot',
      'The last deck anybody in this town bothered to write down.']
  };
  NICKNAMES['solan-vieille'] = NICKNAMES['solan_vieille_seed'];
  NICKNAMES['chain-40'] = NICKNAMES['chain_40'];
  NICKNAMES['chain-41'] = NICKNAMES['chain_41'];
  NICKNAMES['chain-42'] = NICKNAMES['chain_42'];

  var STRANGER_NAMES = [
    'The Widow\u2019s Hand', 'Six Mile Deck', 'The Quartermaster',
    'Bellweather\u2019s Pot', 'The Tin Star', 'Coldwater Split',
    'The Drover\u2019s Cut', 'Hollis Deck'
  ];

  function nickname(entry) {
    var known = NICKNAMES[entry.id];
    if (known) return known;
    var hash = 0, id = String(entry.id || entry.name || '');
    for (var i = 0; i < id.length; i++) hash = (hash * 31 + id.charCodeAt(i)) >>> 0;
    return [STRANGER_NAMES[hash % STRANGER_NAMES.length],
      'Nobody around here will say where this one came from.'];
  }

  function tableLabel(entry) { return nickname(entry)[0]; }
  function tableNote(entry) { return nickname(entry)[1]; }

  function decodeTable(param) {
    var normalized = param.replace(/-/g, '+').replace(/_/g, '/');
    while (normalized.length % 4) normalized += '=';
    var parsed = JSON.parse(decodeURIComponent(escape(root.atob(normalized))));
    var table = parsed && parsed.table ? parsed.table : parsed;
    if (!E.validTable(table)) throw new Error('not a legal 16x4 table');
    return table;
  }

  function encodeTable(table) {
    return root.btoa(unescape(encodeURIComponent(JSON.stringify(table))))
      .replace(/\+/g, '-').replace(/\//g, '_').replace(/=+$/, '');
  }

  function refreshStats() {
    return API.stats().then(function (payload) {
      stats = payload;
      UI.renderTricks();
      return payload;
    }, function () { return null; });
  }

  function resetForRun() {
    closeOverlay();
    UI.resetCallers();
    Scene.clearCorpses();
    Scene.clearWave();
    Scene.setHealth(1, null, false);
    ledger = { reading: null, hearsay: false, roundWorst: null, bestRun: null,
      lastKill: null, tier: null, recordId: null, deepScore: null };
  }

  function startRun(entry) {
    resetForRun();
    Game.newRun({
      table: entry.table,
      origin: { kind: 'curated', id: entry.id, name: entry.name }
    });
  }

  function startShuffled() {
    resetForRun();
    var rng = E.mulberry32((Date.now() ^ 0x9e3779b9) >>> 0);
    var base = curatedCache[Math.floor(rng() * curatedCache.length) % curatedCache.length];
    Game.newRun({
      table: Moves.randomLegalPerturbation(rng, base.table, 400, 0.035),
      origin: { kind: 'perturbation', id: base.id, name: 'jostled ' + tableLabel(base) }
    });
  }

  /* A fresh run with no questions asked: the room is always already dealt. */
  function startFresh() {
    if (!curatedCache.length) { boot(); return; }
    var pick = curatedCache[Math.floor(Math.random() * curatedCache.length)];
    startRun(pick);
  }

  var bootToken = 0;

  function boot() {
    var token = ++bootToken;
    var current = function () { return token === bootToken; };
    resetForRun();

    var params = new URLSearchParams(root.location.search);
    var handed = null;
    if (params.get('table')) {
      try { handed = decodeTable(params.get('table')); }
      catch (err) { UI.toast('That handed-in table did not read: ' + err.message, true); }
    }

    sheet(function (node) {
      node.appendChild(make('h1', null, 'STANDOFF'));
      var status = make('p', 'lead');
      status.appendChild(make('span', 'spinner'));
      status.appendChild(document.createTextNode('  Opening the saloon...'));
      node.appendChild(status);
    });

    refreshStats();
    API.patient(function () { return API.curated(); }, function () {
      if (!current()) return;
      sheet(function (node) {
        node.appendChild(make('h1', null, 'STANDOFF'));
        var status = make('p', 'lead');
        status.appendChild(make('span', 'spinner'));
        status.appendChild(document.createTextNode(
          '  The piano player is still tuning. The doors open the moment the ' +
          'house is ready.'));
        node.appendChild(status);
      });
    }).then(function (payload) {
      if (!current()) return;
      curatedCache = (payload && payload.tables) || [];
      if (!curatedCache.length) {
        throw new API.ApiError('the house has no tables on file', 500);
      }
      // No empty state: the run starts dealt, with a hand and a live bell.
      if (handed) {
        resetForRun();
        Game.newRun({
          table: handed,
          origin: { kind: 'handed-in', id: null, name: 'handed in via ?table=' }
        });
        UI.say('Somebody slid you a payout sheet from another room. Work it.');
      } else {
        startFresh();
      }
    }, function (err) {
      if (!current()) return;
      sheet(function (node) {
        node.appendChild(make('h1', 'bad', 'THE SALOON IS SHUT'));
        node.appendChild(make('p', 'lead',
          'No answer from the house: ' + (err.message || err) + '.'));
        node.appendChild(make('p', 'fine',
          'Start the portal server with python3 Games/serve.py, or reload this ' +
          'page with ?mock=1 to play against canned data offline.'));
        var row = make('div', 'row');
        row.appendChild(button('TRY AGAIN', 'big', function () { boot(); }));
        row.appendChild(button('play offline (mock)', 'big quiet', function () {
          var url = new URL(root.location.href);
          url.searchParams.set('mock', '1');
          root.location.href = url.toString();
        }));
        node.appendChild(row);
      });
    });
  }

  // ------------------------------------------------------------------- wire --

  function start() {
    ['stage', 'nerve', 'nerveNote', 'bells', 'bellName', 'tricksLabel', 'ticker',
      'coach', 'overlay', 'hand', 'budgetPips', 'bellBtn', 'bellSub', 'hood',
      'hoodNumbers', 'hoodTable', 'hoodFilters', 'hoodHonesty', 'toast',
      'soundBtn', 'hoodBtn', 'rerollBtn', 'hoodClose'
    ].forEach(function (id) { dom[id] = el(id); });

    Game.ui = UI;
    Scene.init(dom.stage);
    requestAnimationFrame(drawNerve);

    dom.bellBtn.addEventListener('click', function () {
      Audio.unlock();
      markCoached();
      hideCoach();
      Game.ringBell();
      UI.renderRound();
    });
    if (!Audio.isAvailable()) {
      dom.soundBtn.disabled = true;
      text(dom.soundBtn, '\u266a \u2014');
    } else {
      dom.soundBtn.addEventListener('click', function () {
        Audio.setEnabled(!Audio.isEnabled());
        text(dom.soundBtn, '\u266a ' + (Audio.isEnabled() ? 'on' : 'off'));
      });
    }
    dom.hoodBtn.addEventListener('click', function () {
      dom.hood.classList.toggle('hidden');
      if (!dom.hood.classList.contains('hidden')) renderHood();
    });
    dom.hoodClose.addEventListener('click', function () {
      dom.hood.classList.add('hidden');
    });
    dom.rerollBtn.addEventListener('click', function () {
      if (curatedCache.length) UI.showPicker();
      else boot();
    });
    document.addEventListener('keydown', function (event) {
      if (event.key === 'Enter' && !dom.bellBtn.disabled) dom.bellBtn.click();
      if (event.key >= '1' && event.key <= '5' && Game.state) {
        var card = Game.state.hand[Number(event.key) - 1];
        if (card && Game.canPlay(card)) { Audio.card(); Game.playCard(card); }
      }
      if (event.key === 'h') dom.hoodBtn.click();
    });

    Scene.seatClick = function (hit) {
      var state = Game.state;
      if (!state) return;
      UI.say(E.NAMES[hit.index] + ' ' + Game.soloPhrase(E.solo(state.table, hit.index)));
    };
    Scene.callerHover = function (key) {
      if (!key) return;
      var info = ANTAG[key];
      if (info) UI.say(info.tell);
    };

    if (API.mock) {
      document.body.appendChild(make('div', 'mock-flag', 'PRACTICE NIGHT — nothing is written down'));
    }

    boot();
  }

  if (document.readyState === 'loading') {
    document.addEventListener('DOMContentLoaded', start);
  } else {
    start();
  }
})(window);
