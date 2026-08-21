/* standoff — the saloon stage.
 *
 * Everything the player reads about the table is drawn here as saloon
 * furniture: chip stacks are solo draws, cords between chairs are collision
 * stakes, thin arrows are who-beats-whom-to-the-draw. The 16x4 matrix exists
 * only behind "the ledger" affordance.
 */
(function (root) {
  'use strict';

  var E = root.SOEval;

  var ANTAGONISTS = {
    library_replay: {
      key: 'library_replay',
      name: 'The Ghosts',
      subtitle: 'every trick the gang already knows',
      colour: '#cfd8e3',
      glow: 'rgba(207,216,227,0.55)',
      tell: 'They do not aim. They repeat a draw somebody already wrote down.',
      level: 'replay'
    },
    stationary: {
      key: 'stationary',
      name: 'Clay Stillwell',
      subtitle: 'the Statue',
      colour: '#e8b25f',
      glow: 'rgba(232,178,95,0.5)',
      tell: 'Same odds every single beat. He never changes his mind, so you never learn anything new about him.',
      level: 'quick'
    },
    one_quitter_cyclic: {
      key: 'one_quitter_cyclic',
      name: 'The Kettleman Carousel',
      subtitle: 'they take turns',
      colour: '#6fce97',
      glow: 'rgba(111,206,151,0.5)',
      tell: 'One man draws per beat and the turn passes around the table like a bottle.',
      level: 'standard'
    },
    general_periodic: {
      key: 'general_periodic',
      name: 'The Drifter',
      subtitle: 'no pattern you can name',
      colour: '#b58cf0',
      glow: 'rgba(181,140,240,0.5)',
      tell: 'Every man on his own private clock. Loose, unreadable, and usually not the one that kills you.',
      level: 'standard'
    },
    two_quitter_periodic: {
      key: 'two_quitter_periodic',
      name: 'The Paired Draw',
      subtitle: 'two at a time, and they alternate',
      colour: '#e0534f',
      glow: 'rgba(224,83,79,0.6)',
      tell: 'Two of them draw together, then the other two. It is the oldest repair in the book and it is the one that empties this room.',
      level: 'standard'
    },
    boss: {
      key: 'boss',
      name: 'The Marshal',
      subtitle: 'takes his time',
      colour: '#f2f0e6',
      glow: 'rgba(242,240,230,0.7)',
      tell: 'He does not hurry and he does not stop. He will try everything the gang can afford to try.',
      level: 'deep'
    }
  };

  var SEATS = [
    { x: -0.30, y: -0.22, face: 1 },
    { x: 0.30, y: -0.22, face: -1 },
    { x: 0.34, y: 0.20, face: -1 },
    { x: -0.34, y: 0.20, face: 1 }
  ];

  var PAIRS = [];
  for (var pi = 0; pi < 4; pi++) {
    for (var pj = pi + 1; pj < 4; pj++) PAIRS.push([pi, pj]);
  }

  function lerp(a, b, t) { return a + (b - a) * t; }
  function clamp(v, lo, hi) { return v < lo ? lo : (v > hi ? hi : v); }
  function ease(t) { return t < 0.5 ? 2 * t * t : 1 - Math.pow(-2 * t + 2, 2) / 2; }

  /* A guttering wick: never quite steady, never obviously periodic. */
  function flicker(time) {
    return 0.88 +
      0.06 * Math.sin(time / 210) +
      0.04 * Math.sin(time / 97 + 1.7) +
      0.03 * Math.sin(time / 43 + 0.4);
  }

  /* Slow tobacco haze. Positions are fixed at construction and drift; the
   * puffs wrap, so the room is never without smoke. */
  var SMOKE = [];
  for (var sp = 0; sp < 9; sp++) {
    SMOKE.push({
      x: (sp * 137 % 100) / 100,
      y: 0.12 + ((sp * 61) % 55) / 100 * 0.9,
      r: 0.18 + ((sp * 29) % 40) / 100 * 0.30,
      vx: 0.004 + ((sp * 17) % 30) / 10000,
      vy: -0.0016 - ((sp * 11) % 20) / 40000,
      phase: sp * 1.31
    });
  }

  function roundRect(ctx, x, y, w, h, r) {
    ctx.beginPath();
    ctx.moveTo(x + r, y);
    ctx.arcTo(x + w, y, x + w, y + h, r);
    ctx.arcTo(x + w, y + h, x, y + h, r);
    ctx.arcTo(x, y + h, x, y, r);
    ctx.arcTo(x, y, x + w, y, r);
    ctx.closePath();
  }

  var Scene = {
    ANTAGONISTS: ANTAGONISTS,
    canvas: null, ctx: null,
    width: 0, height: 0, dpr: 1,
    table: null,
    highlight: { players: [], pairs: [], pot: false },
    health: 1, exploitability: null, hearsay: false,
    phase: 'idle',
    wave: null,
    bossProgress: 0,
    schedule: null,
    shakeAmount: 0,
    flash: null,
    seatClick: null,
    callerHover: null,
    started: 0,
    reduceMotion: false,
    lastBeat: -1,
    onBeat: null,
    ghostTable: null,
    swap: null,
    corpses: [],
    callers: [],          // [{key, state}] — who is outside, and how they left
    hoveredCaller: null,
    chipBoxes: [],

    init: function (canvas) {
      this.canvas = canvas;
      this.ctx = canvas.getContext('2d');
      this.started = performance.now();
      this.reduceMotion = !!(root.matchMedia &&
        root.matchMedia('(prefers-reduced-motion: reduce)').matches);
      var self = this;
      root.addEventListener('resize', function () { self.resize(); });
      canvas.addEventListener('mousemove', function (event) {
        var hit = self.hitTest(event);
        canvas.style.cursor = hit ? 'pointer' : 'default';
        var key = (hit && hit.type === 'caller') ? hit.key : null;
        if (key !== self.hoveredCaller) {
          self.hoveredCaller = key;
          if (self.callerHover) self.callerHover(key);
        }
      });
      canvas.addEventListener('mouseleave', function () {
        if (self.hoveredCaller !== null) {
          self.hoveredCaller = null;
          if (self.callerHover) self.callerHover(null);
        }
      });
      canvas.addEventListener('click', function (event) {
        var hit = self.hitTest(event);
        if (hit && self.seatClick) self.seatClick(hit);
      });
      this.resize();
      var frame = function (time) { self.draw(time); requestAnimationFrame(frame); };
      requestAnimationFrame(frame);
    },

    resize: function () {
      var rect = this.canvas.getBoundingClientRect();
      this.dpr = Math.min(root.devicePixelRatio || 1, 2);
      this.width = Math.max(320, rect.width);
      this.height = Math.max(240, rect.height);
      this.canvas.width = Math.round(this.width * this.dpr);
      this.canvas.height = Math.round(this.height * this.dpr);
    },

    seatPoint: function (index) {
      var cx = this.width / 2;
      var cy = this.height * 0.55;
      var radius = Math.min(this.width * 0.42, this.height * 0.62);
      return {
        x: cx + SEATS[index].x * radius * 2.05,
        y: cy + SEATS[index].y * radius * 1.75,
        face: SEATS[index].face
      };
    },

    hitTest: function (event) {
      var rect = this.canvas.getBoundingClientRect();
      var x = event.clientX - rect.left, y = event.clientY - rect.top;
      for (var c = 0; c < this.chipBoxes.length; c++) {
        var box = this.chipBoxes[c];
        if (x >= box.x && x <= box.x + box.w && y >= box.y && y <= box.y + box.h) {
          return { type: 'caller', key: box.key, state: box.state };
        }
      }
      for (var i = 0; i < 4; i++) {
        var p = this.seatPoint(i);
        if (Math.hypot(x - p.x, y - p.y) < 52) return { type: 'seat', index: i };
      }
      return null;
    },

    /* Tonight's callers, in arrival order. Drawn as figures waiting in the
     * doorway and as a strip of portrait chips — never as a written roster. */
    setCallers: function (roster) {
      this.callers = roster.map(function (entry) {
        return { key: entry.key, state: entry.state };
      });
    },
    setCallerState: function (key, state) {
      for (var i = 0; i < this.callers.length; i++) {
        if (this.callers[i].key === key) this.callers[i].state = state;
      }
    },

    setTable: function (table) { this.table = table; },
    setGhost: function (table) { this.ghostTable = table; },
    setHighlight: function (highlight) {
      this.highlight = highlight || { players: [], pairs: [], pot: false };
    },
    setPhase: function (phase) { this.phase = phase; },
    setHealth: function (frac, exploitability, hearsay) {
      this.health = clamp(frac, 0, 1);
      this.exploitability = exploitability;
      this.hearsay = !!hearsay;
    },
    setBoss: function (progress) { this.bossProgress = clamp(progress, 0, 1); },
    shake: function (amount) {
      if (this.reduceMotion) return;
      this.shakeAmount = Math.max(this.shakeAmount, amount);
    },
    flashColour: function (colour, strength) {
      this.flash = { colour: colour, strength: strength, at: performance.now() };
    },
    swapSeats: function (a, b) { this.swap = { a: a, b: b, at: performance.now() }; },
    fell: function (player) {
      this.corpses.push({ player: player, at: performance.now() });
    },
    clearCorpses: function () { this.corpses = []; },

    beginWave: function (key, profile, beatDuration) {
      this.wave = { key: key, at: performance.now(), verdict: null };
      if (profile && profile.hazards && profile.hazards.length) {
        this.schedule = {
          hazards: profile.hazards,
          period: profile.hazards.length,
          at: performance.now(),
          beat: beatDuration || 620
        };
        this.lastBeat = -1;
      } else {
        this.schedule = null;
      }
    },
    endWave: function (verdict) {
      if (this.wave) this.wave.verdict = verdict;
    },
    clearWave: function () { this.wave = null; this.schedule = null; },

    // ------------------------------------------------------------- drawing --

    draw: function (time) {
      var ctx = this.ctx;
      if (!ctx) return;
      var rect = this.canvas.getBoundingClientRect();
      if (Math.abs(rect.width - this.width) > 1 || Math.abs(rect.height - this.height) > 1) {
        this.resize();
      }
      ctx.save();
      ctx.setTransform(this.dpr, 0, 0, this.dpr, 0, 0);

      var shake = this.shakeAmount;
      if (shake > 0.05) {
        ctx.translate((Math.random() - 0.5) * shake, (Math.random() - 0.5) * shake);
        this.shakeAmount *= 0.86;
      } else {
        this.shakeAmount = 0;
      }

      this.drawRoom(time);
      this.drawQueue(time);
      this.drawTable(time);
      if (this.table) {
        this.drawTethers(time);
        this.drawPreemption(time);
        this.drawPot(time);
      }
      this.drawGunslingers(time);
      if (this.wave) this.drawAntagonist(time);
      this.drawSmoke(time);
      this.drawLampFall(time);
      this.drawChips(time);
      this.drawVerdictBanner(time);
      this.drawFlash(time);
      ctx.restore();
    },

    drawRoom: function (time) {
      var ctx = this.ctx, w = this.width, h = this.height;
      var sky = ctx.createLinearGradient(0, 0, 0, h);
      sky.addColorStop(0, '#191218');
      sky.addColorStop(0.55, '#241a19');
      sky.addColorStop(1, '#120d0e');
      ctx.fillStyle = sky;
      ctx.fillRect(0, 0, w, h);

      // Wall planks.
      ctx.save();
      ctx.globalAlpha = 0.28;
      for (var y = 0; y < h * 0.6; y += 26) {
        ctx.fillStyle = (Math.floor(y / 26) % 2) ? '#2b1f1b' : '#241a17';
        ctx.fillRect(0, y, w, 24);
      }
      ctx.restore();

      // Window with night outside.
      var wx = w * 0.06, wy = h * 0.10, ww = Math.min(160, w * 0.18), wh = ww * 0.72;
      ctx.fillStyle = '#0d1626';
      ctx.fillRect(wx, wy, ww, wh);
      ctx.strokeStyle = '#3a2a20';
      ctx.lineWidth = 5;
      ctx.strokeRect(wx, wy, ww, wh);
      ctx.beginPath();
      ctx.moveTo(wx + ww / 2, wy); ctx.lineTo(wx + ww / 2, wy + wh);
      ctx.moveTo(wx, wy + wh / 2); ctx.lineTo(wx + ww, wy + wh / 2);
      ctx.lineWidth = 3; ctx.stroke();
      ctx.fillStyle = 'rgba(220,230,255,0.75)';
      for (var s = 0; s < 7; s++) {
        var sx = wx + 12 + ((s * 37) % (ww - 20));
        var sy = wy + 10 + ((s * 53) % (wh - 18));
        var twinkle = 0.4 + 0.6 * Math.abs(Math.sin(time / 900 + s));
        ctx.globalAlpha = twinkle;
        ctx.fillRect(sx, sy, 2, 2);
      }
      ctx.globalAlpha = 1;

      // Swinging door on the right — where callers arrive.
      var dx = w * 0.90, dy = h * 0.12, dw = Math.min(120, w * 0.14), dh = h * 0.42;
      ctx.fillStyle = '#0a0708';
      ctx.fillRect(dx - dw / 2, dy, dw, dh);
      ctx.fillStyle = '#33241c';
      ctx.fillRect(dx - dw / 2, dy + dh * 0.28, dw, dh * 0.42);
      ctx.strokeStyle = '#1a1210';
      ctx.lineWidth = 2;
      ctx.beginPath();
      ctx.moveTo(dx, dy + dh * 0.28); ctx.lineTo(dx, dy + dh * 0.70);
      ctx.stroke();

      // Hanging lantern.
      var lx = w / 2, ly = h * 0.13;
      var swing = this.reduceMotion ? 0 : Math.sin(time / 1700) * 6;
      ctx.strokeStyle = '#261c17';
      ctx.lineWidth = 2;
      ctx.beginPath(); ctx.moveTo(lx, 0); ctx.lineTo(lx + swing, ly); ctx.stroke();
      var wick = this.reduceMotion ? 1 : flicker(time);
      var glow = ctx.createRadialGradient(lx + swing, ly + 10, 8, lx + swing, ly + 10,
        Math.max(w, h) * 0.62 * wick);
      var warmth = (this.wave ? 0.16 : 0.24) * wick;
      glow.addColorStop(0, 'rgba(255,205,130,' + (warmth + 0.30) + ')');
      glow.addColorStop(0.35, 'rgba(255,180,100,' + warmth * 0.5 + ')');
      glow.addColorStop(1, 'rgba(0,0,0,0)');
      ctx.fillStyle = glow;
      ctx.fillRect(0, 0, w, h);
      ctx.fillStyle = '#f6d089';
      ctx.beginPath();
      ctx.ellipse(lx + swing, ly + 12, 11 * wick, 15 * wick, 0, 0, Math.PI * 2);
      ctx.fill();
      ctx.strokeStyle = '#4a3524';
      ctx.lineWidth = 3;
      ctx.beginPath();
      ctx.ellipse(lx + swing, ly + 12, 16, 20, 0, 0, Math.PI * 2);
      ctx.stroke();

      // Floor.
      ctx.fillStyle = '#1a1210';
      ctx.fillRect(0, h * 0.72, w, h * 0.28);
      ctx.globalAlpha = 0.3;
      for (var fx = 0; fx < w; fx += 44) {
        ctx.strokeStyle = '#0d0908';
        ctx.lineWidth = 2;
        ctx.beginPath();
        ctx.moveTo(fx, h * 0.72); ctx.lineTo(fx - 30, h); ctx.stroke();
      }
      ctx.globalAlpha = 1;
    },

    /* Who is waiting outside. Backlit shapes crowding the doorway, one per
     * caller still to come tonight; they thin out as the night goes on. The
     * player learns who these are by watching them come in, never by reading
     * a list. */
    drawQueue: function (time) {
      if (!this.callers.length) return;
      var ctx = this.ctx, w = this.width, h = this.height;
      var doorX = w * 0.90, doorY = h * 0.12, doorH = h * 0.42;
      var waiting = this.callers.filter(function (c) {
        return c.state === 'pending' || c.state === 'active';
      });
      if (!waiting.length) return;

      ctx.save();
      // Clip to the doorway so the crowd reads as being outside it.
      var dw = Math.min(120, w * 0.14);
      ctx.beginPath();
      ctx.rect(doorX - dw / 2, doorY, dw, doorH);
      ctx.clip();

      // Night behind them.
      var night = ctx.createLinearGradient(0, doorY, 0, doorY + doorH);
      night.addColorStop(0, 'rgba(24,34,54,0.9)');
      night.addColorStop(1, 'rgba(8,10,16,0.95)');
      ctx.fillStyle = night;
      ctx.fillRect(doorX - dw / 2, doorY, dw, doorH);

      for (var k = waiting.length - 1; k >= 0; k--) {
        var caller = waiting[k];
        var info = ANTAGONISTS[caller.key];
        if (!info) continue;
        var depth = k / Math.max(1, waiting.length);
        var scale = 0.30 - depth * 0.09;
        var sway = this.reduceMotion ? 0 : Math.sin(time / 1300 + k * 2.1) * 3;
        var lit = caller.state === 'active' ||
          (this.hoveredCaller && this.hoveredCaller === caller.key);
        ctx.save();
        ctx.translate(doorX + (k - waiting.length / 2) * 15 + sway,
          doorY + doorH * 0.74 - depth * 6);
        ctx.scale(scale, scale);
        ctx.globalAlpha = lit ? 0.95 : (0.50 - depth * 0.16);
        this.silhouette(ctx, lit ? info.colour : '#0a0d14');
        if (lit) {
          ctx.globalAlpha = 0.5;
          ctx.shadowColor = info.glow;
          ctx.shadowBlur = 40;
          this.silhouette(ctx, info.colour);
        }
        ctx.restore();
      }
      ctx.restore();

      // Doorway spill so the crowd is legible against the frame.
      ctx.save();
      var spill = ctx.createRadialGradient(doorX, doorY + doorH * 0.6, 4,
        doorX, doorY + doorH * 0.6, dw * 1.6);
      spill.addColorStop(0, 'rgba(120,150,200,0.10)');
      spill.addColorStop(1, 'rgba(0,0,0,0)');
      ctx.fillStyle = spill;
      ctx.fillRect(doorX - dw * 2, doorY - 20, dw * 4, doorH + 40);
      ctx.restore();
    },

    /* A strip of portrait chips: colour, shape, and state. No names, no
     * sentences — hovering one puts its tell in the ticker instead. */
    drawChips: function (time) {
      this.chipBoxes = [];
      if (!this.callers.length) return;
      var ctx = this.ctx;
      var x0 = 16, y0 = 16, size = 30, gap = 7;
      for (var k = 0; k < this.callers.length; k++) {
        var caller = this.callers[k];
        var info = ANTAGONISTS[caller.key];
        if (!info) continue;
        var x = x0 + k * (size + gap), y = y0;
        this.chipBoxes.push({ x: x, y: y, w: size, h: size + 6,
          key: caller.key, state: caller.state });

        var state = caller.state;
        var alpha = state === 'locked' ? 0.18
          : (state === 'pending' ? 0.55 : 1);
        var hovered = this.hoveredCaller === caller.key;
        ctx.save();
        ctx.globalAlpha = alpha;

        ctx.fillStyle = 'rgba(10,7,8,0.66)';
        ctx.strokeStyle = state === 'active' ? info.colour : 'rgba(232,178,95,0.22)';
        ctx.lineWidth = state === 'active' ? 2 : 1;
        roundRect(ctx, x, y, size, size, 3);
        ctx.fill();
        ctx.stroke();

        if (state === 'active') {
          ctx.shadowColor = info.glow;
          ctx.shadowBlur = 14 + 6 * Math.sin(time / 220);
        }
        // Mini portrait: hat and shoulders, in the caller's colour.
        ctx.save();
        ctx.translate(x + size / 2, y + size * 0.72);
        ctx.scale(0.20, 0.20);
        this.silhouette(ctx, state === 'locked' ? '#6b6259' : info.colour,
          hovered ? 1 : 0.92);
        ctx.restore();
        ctx.shadowBlur = 0;

        // Outcome mark under the chip: a notch that stays, not a word.
        if (state === 'held' || state === 'settled' || state === 'skipped') {
          ctx.fillStyle = state === 'held' ? 'rgba(127,199,154,0.9)'
            : (state === 'settled' ? 'rgba(209,69,63,0.95)' : 'rgba(236,223,201,0.3)');
          if (state === 'settled') {
            ctx.fillRect(x, y + size + 2, size, 3);
            ctx.globalAlpha = alpha * 0.5;
            ctx.fillRect(x - 1, y - 1, size + 2, size + 2);
          } else if (state === 'held') {
            ctx.fillRect(x + size * 0.22, y + size + 2, size * 0.56, 3);
          } else {
            ctx.fillRect(x + size * 0.42, y + size + 2, size * 0.16, 3);
          }
        }
        ctx.restore();
      }
    },

    drawTable: function (time) {
      var ctx = this.ctx, w = this.width, h = this.height;
      var cx = w / 2, cy = h * 0.55;
      var rx = Math.min(w * 0.30, 300), ry = rx * 0.44;
      ctx.save();
      ctx.fillStyle = 'rgba(0,0,0,0.5)';
      ctx.beginPath();
      ctx.ellipse(cx, cy + 16, rx * 1.06, ry * 1.06, 0, 0, Math.PI * 2);
      ctx.fill();
      var wood = ctx.createLinearGradient(cx, cy - ry, cx, cy + ry);
      wood.addColorStop(0, '#4a3324');
      wood.addColorStop(1, '#2c1d15');
      ctx.fillStyle = wood;
      ctx.beginPath();
      ctx.ellipse(cx, cy, rx, ry, 0, 0, Math.PI * 2);
      ctx.fill();
      var felt = ctx.createRadialGradient(cx, cy - ry * 0.3, ry * 0.1, cx, cy, rx * 0.94);
      felt.addColorStop(0, '#2f6046');
      felt.addColorStop(1, '#17362a');
      ctx.fillStyle = felt;
      ctx.beginPath();
      ctx.ellipse(cx, cy, rx * 0.9, ry * 0.86, 0, 0, Math.PI * 2);
      ctx.fill();
      ctx.restore();
      this.tableGeom = { cx: cx, cy: cy, rx: rx, ry: ry };
    },

    /* Grudge cords: for each pair, how much both gain by drawing together. */
    drawTethers: function (time) {
      var ctx = this.ctx, table = this.table;
      for (var k = 0; k < PAIRS.length; k++) {
        var i = PAIRS[k][0], j = PAIRS[k][1];
        var mask = (1 << i) | (1 << j);
        var joint = (table[mask][i] + table[mask][j]) / 2;
        var alone = (E.solo(table, i) + E.solo(table, j)) / 2;
        var gain = joint - alone;
        var pa = this.seatPoint(i), pb = this.seatPoint(j);
        var strength = clamp(Math.abs(gain) / 2.2, 0.04, 1);
        var hot = gain >= 0;
        var lit = this.isPairLit(i, j);
        ctx.save();
        ctx.lineWidth = 1 + strength * 5 * (lit ? 1.7 : 1);
        ctx.globalAlpha = (0.16 + strength * 0.55) * (lit ? 1 : 0.72);
        ctx.strokeStyle = hot ? '#e9b96b' : '#7fa9d6';
        if (lit) {
          ctx.shadowColor = hot ? 'rgba(255,190,110,0.9)' : 'rgba(140,190,255,0.9)';
          ctx.shadowBlur = 16;
        }
        var mx = (pa.x + pb.x) / 2;
        var my = (pa.y + pb.y) / 2;
        var sag = 18 + strength * 22;
        var wobble = this.reduceMotion ? 0 : Math.sin(time / 700 + k) * 3 * strength;
        ctx.beginPath();
        ctx.moveTo(pa.x, pa.y + 24);
        ctx.quadraticCurveTo(mx, my + sag + wobble, pb.x, pb.y + 24);
        ctx.stroke();
        if (!hot) {
          ctx.setLineDash([4, 6]);
          ctx.globalAlpha *= 0.8;
          ctx.stroke();
        }
        ctx.restore();
      }
    },

    isPairLit: function (i, j) {
      var pairs = this.highlight.pairs || [];
      for (var k = 0; k < pairs.length; k++) {
        var p = pairs[k];
        if ((p[0] === i && p[1] === j) || (p[0] === j && p[1] === i)) return true;
      }
      return false;
    },

    /* Who beats whom to the draw: filter-4 preemption digraph. */
    drawPreemption: function (time) {
      var ctx = this.ctx;
      var edges = E.preemptionEdges(this.table, E.MARGIN);
      for (var i = 0; i < 4; i++) {
        for (var k = 0; k < edges[i].length; k++) {
          var j = edges[i][k];
          var pa = this.seatPoint(i), pb = this.seatPoint(j);
          var dx = pb.x - pa.x, dy = pb.y - pa.y;
          var len = Math.hypot(dx, dy) || 1;
          var ux = dx / len, uy = dy / len;
          var ax = pa.x + ux * 42, ay = pa.y + uy * 42 - 8;
          var bx = pb.x - ux * 46, by = pb.y - uy * 46 - 8;
          var march = this.reduceMotion ? 0 : (time / 60) % 14;
          ctx.save();
          ctx.strokeStyle = 'rgba(226,120,90,0.55)';
          ctx.lineWidth = 1.6;
          ctx.setLineDash([6, 8]);
          ctx.lineDashOffset = -march;
          ctx.beginPath();
          ctx.moveTo(ax, ay); ctx.lineTo(bx, by);
          ctx.stroke();
          ctx.setLineDash([]);
          ctx.fillStyle = 'rgba(226,120,90,0.75)';
          ctx.beginPath();
          ctx.moveTo(bx, by);
          ctx.lineTo(bx - ux * 10 - uy * 5, by - uy * 10 + ux * 5);
          ctx.lineTo(bx - ux * 10 + uy * 5, by - uy * 10 - ux * 5);
          ctx.closePath();
          ctx.fill();
          ctx.restore();
        }
      }
    },

    /* The pot: what everybody gets if all four draw at once. */
    drawPot: function (time) {
      var ctx = this.ctx, g = this.tableGeom;
      if (!g) return;
      var row = this.table[15];
      var total = (row[0] + row[1] + row[2] + row[3]) / 4;
      var bad = total < 0;
      var pulse = this.highlight.pot ? 1 + 0.12 * Math.sin(time / 160) : 1;
      ctx.save();
      ctx.translate(g.cx, g.cy);
      ctx.scale(pulse, pulse);
      var radius = 26 + clamp(Math.abs(total) * 7, 0, 20);
      var grad = ctx.createRadialGradient(0, -6, 3, 0, 0, radius);
      if (bad) {
        grad.addColorStop(0, 'rgba(190,60,55,0.95)');
        grad.addColorStop(1, 'rgba(60,12,14,0.15)');
      } else {
        grad.addColorStop(0, 'rgba(245,205,120,0.95)');
        grad.addColorStop(1, 'rgba(120,80,25,0.15)');
      }
      ctx.fillStyle = grad;
      ctx.beginPath();
      ctx.ellipse(0, 0, radius, radius * 0.55, 0, 0, Math.PI * 2);
      ctx.fill();
      ctx.fillStyle = bad ? 'rgba(255,214,210,0.9)' : 'rgba(60,38,10,0.9)';
      ctx.font = '600 12px ui-monospace, monospace';
      ctx.textAlign = 'center';
      ctx.fillText(bad ? 'EVERYBODY BLEEDS' : 'SPLIT POT', 0, radius * 0.55 + 16);
      ctx.restore();
    },

    drawGunslingers: function (time) {
      for (var i = 0; i < 4; i++) this.drawGunslinger(i, time);
    },

    drawGunslinger: function (index, time) {
      var ctx = this.ctx;
      var p = this.seatPoint(index);
      var table = this.table;
      var lit = (this.highlight.players || []).indexOf(index) >= 0;
      var palette = ['#d8b98a', '#a8c7e0', '#c9a6d8', '#9fd0b0'][index];
      if (this.swap) {
        var st = (performance.now() - this.swap.at) / 700;
        if (st >= 1) { this.swap = null; }
        else if (this.swap.a === index || this.swap.b === index) {
          var other = this.seatPoint(this.swap.a === index ? this.swap.b : this.swap.a);
          var arc = Math.sin(st * Math.PI);
          p = { x: lerp(p.x, other.x, arc * 0.5), y: lerp(p.y, other.y, arc * 0.5) - arc * 18,
                face: p.face };
        }
      }
      var dead = null;
      for (var c = 0; c < this.corpses.length; c++) {
        if (this.corpses[c].player === index) dead = this.corpses[c];
      }

      ctx.save();
      ctx.translate(p.x, p.y);
      if (dead) {
        var dt = clamp((performance.now() - dead.at) / 900, 0, 1);
        ctx.rotate(ease(dt) * (p.face > 0 ? -1 : 1) * 1.15);
        ctx.globalAlpha = 1 - 0.35 * dt;
      }
      var breathe = this.reduceMotion ? 0 : Math.sin(time / 1100 + index * 1.7) * 1.6;

      if (lit) {
        var halo = ctx.createRadialGradient(0, 0, 6, 0, 0, 74);
        halo.addColorStop(0, 'rgba(255,235,190,0.35)');
        halo.addColorStop(1, 'rgba(255,235,190,0)');
        ctx.fillStyle = halo;
        ctx.beginPath(); ctx.arc(0, 0, 74, 0, Math.PI * 2); ctx.fill();
      }

      // Draw meter: how likely this one is to go for it on the current beat.
      var hazard = this.currentHazard(index);
      if (hazard !== null) {
        ctx.save();
        ctx.rotate(-Math.PI / 2);
        ctx.lineWidth = 5;
        ctx.strokeStyle = 'rgba(255,255,255,0.10)';
        ctx.beginPath(); ctx.arc(0, 0, 46, 0, Math.PI * 2); ctx.stroke();
        var wave = this.wave && ANTAGONISTS[this.wave.key];
        ctx.strokeStyle = wave ? wave.colour : '#e8b25f';
        ctx.shadowColor = wave ? wave.glow : 'rgba(232,178,95,0.6)';
        ctx.shadowBlur = 12;
        ctx.beginPath();
        ctx.arc(0, 0, 46, 0, Math.PI * 2 * clamp(hazard, 0, 1));
        ctx.stroke();
        ctx.restore();
      }

      // Body.
      ctx.save();
      ctx.scale(p.face, 1);
      ctx.fillStyle = 'rgba(0,0,0,0.55)';
      ctx.beginPath();
      ctx.moveTo(-26, 34 + breathe);
      ctx.quadraticCurveTo(-30, -4 + breathe, -12, -14 + breathe);
      ctx.lineTo(12, -14 + breathe);
      ctx.quadraticCurveTo(30, -4 + breathe, 26, 34 + breathe);
      ctx.closePath();
      ctx.fill();
      // Coat highlight.
      ctx.fillStyle = 'rgba(255,255,255,0.05)';
      ctx.fillRect(-8, -10 + breathe, 5, 42);
      // Head.
      ctx.fillStyle = '#1a1113';
      ctx.beginPath();
      ctx.arc(0, -26 + breathe, 12, 0, Math.PI * 2);
      ctx.fill();
      // Hat.
      ctx.fillStyle = '#120c0d';
      ctx.beginPath();
      ctx.ellipse(0, -34 + breathe, 25, 6, 0, 0, Math.PI * 2);
      ctx.fill();
      ctx.beginPath();
      ctx.moveTo(-13, -34 + breathe);
      ctx.quadraticCurveTo(-11, -50 + breathe, 0, -50 + breathe);
      ctx.quadraticCurveTo(11, -50 + breathe, 13, -34 + breathe);
      ctx.closePath();
      ctx.fill();
      ctx.fillStyle = palette;
      ctx.fillRect(-13, -38 + breathe, 26, 3);
      // Eyes under the brim.
      ctx.fillStyle = 'rgba(255,225,180,0.9)';
      ctx.fillRect(3, -28 + breathe, 4, 2);
      ctx.restore();

      // Chip stack: this one's solo draw.
      if (table) {
        var value = E.solo(table, index);
        var stackX = -p.face * 40;
        var chips = Math.min(9, Math.round(Math.abs(value) * 2.4));
        if (value >= 0) {
          for (var k = 0; k < chips; k++) {
            ctx.fillStyle = k % 2 ? '#e6c168' : '#c99f45';
            ctx.beginPath();
            ctx.ellipse(stackX, 34 - k * 4.2, 13, 5, 0, 0, Math.PI * 2);
            ctx.fill();
            ctx.strokeStyle = 'rgba(0,0,0,0.4)';
            ctx.lineWidth = 1;
            ctx.stroke();
          }
          if (!chips) {
            ctx.strokeStyle = 'rgba(230,193,104,0.5)';
            ctx.setLineDash([3, 3]);
            ctx.beginPath();
            ctx.ellipse(stackX, 34, 13, 5, 0, 0, Math.PI * 2);
            ctx.stroke();
            ctx.setLineDash([]);
          }
        } else {
          ctx.fillStyle = '#8d3b3b';
          ctx.fillRect(stackX - 13, 26, 26, 12);
          ctx.fillStyle = 'rgba(255,220,215,0.85)';
          ctx.font = '600 9px ui-monospace, monospace';
          ctx.textAlign = 'center';
          ctx.fillText('IOU', stackX, 35);
        }
      }

      // Name plate.
      ctx.fillStyle = lit ? '#ffe9bd' : 'rgba(226,213,190,0.62)';
      ctx.font = (lit ? '600 ' : '') + '12px ui-monospace, monospace';
      ctx.textAlign = 'center';
      ctx.fillText(E.NAMES[index].toUpperCase(), 0, 56);
      ctx.restore();

      // Muzzle flash on a beat where this one draws.
      var flash = this.drawFlashFor(index);
      if (flash > 0) {
        ctx.save();
        ctx.translate(p.x + p.face * 30, p.y + 6);
        ctx.globalAlpha = flash;
        var fg = ctx.createRadialGradient(0, 0, 1, 0, 0, 34);
        fg.addColorStop(0, 'rgba(255,250,220,0.95)');
        fg.addColorStop(0.4, 'rgba(255,190,90,0.65)');
        fg.addColorStop(1, 'rgba(255,140,40,0)');
        ctx.fillStyle = fg;
        ctx.beginPath(); ctx.arc(0, 0, 34, 0, Math.PI * 2); ctx.fill();
        ctx.restore();
      }
    },

    currentHazard: function (index) {
      if (!this.schedule) return null;
      var elapsed = performance.now() - this.schedule.at;
      var beat = Math.floor(elapsed / this.schedule.beat) % this.schedule.period;
      var within = (elapsed % this.schedule.beat) / this.schedule.beat;
      var hazard = this.schedule.hazards[beat][index];
      // Fill through the beat, then snap back.
      return hazard * Math.min(1, within * 1.6);
    },

    drawFlashFor: function (index) {
      if (!this.schedule) return 0;
      var elapsed = performance.now() - this.schedule.at;
      var beatIndex = Math.floor(elapsed / this.schedule.beat);
      var beat = beatIndex % this.schedule.period;
      var within = (elapsed % this.schedule.beat) / this.schedule.beat;
      if (within < 0.62) return 0;
      var hazard = this.schedule.hazards[beat][index];
      if (hazard < 0.05) return 0;
      var t = (within - 0.62) / 0.38;
      return Math.max(0, (1 - t)) * clamp(hazard * 1.4, 0, 1);
    },

    /* Beat clock hook so audio can fire in step with the animation. */
    tickBeat: function () {
      if (!this.schedule) return null;
      var elapsed = performance.now() - this.schedule.at;
      var beatIndex = Math.floor(elapsed / this.schedule.beat);
      if (beatIndex === this.lastBeat) return null;
      this.lastBeat = beatIndex;
      return { index: beatIndex, phase: beatIndex % this.schedule.period,
               hazards: this.schedule.hazards[beatIndex % this.schedule.period] };
    },

    drawAntagonist: function (time) {
      var ctx = this.ctx, w = this.width, h = this.height;
      var info = ANTAGONISTS[this.wave.key];
      if (!info) return;
      var age = (performance.now() - this.wave.at) / 1000;
      var entry = clamp(age / 0.8, 0, 1);

      // Colour wash.
      ctx.save();
      ctx.globalCompositeOperation = 'screen';
      var wash = ctx.createLinearGradient(w, 0, w * 0.2, h);
      wash.addColorStop(0, info.glow.replace(/[\d.]+\)$/, (0.20 * entry) + ')'));
      wash.addColorStop(1, 'rgba(0,0,0,0)');
      ctx.fillStyle = wash;
      ctx.fillRect(0, 0, w, h);
      ctx.restore();

      var doorX = w * 0.90;
      var walk = this.wave.key === 'boss' ? this.bossProgress : 1;
      var x = lerp(doorX, w * 0.74, ease(entry) * (this.wave.key === 'boss' ? walk : 1));
      var y = h * 0.52;
      var scale = this.wave.key === 'boss' ? lerp(0.85, 1.35, walk) : 1;

      ctx.save();
      ctx.globalAlpha = entry;
      ctx.translate(x, y);
      ctx.scale(scale, scale);

      switch (this.wave.key) {
        case 'library_replay':
          for (var g = 0; g < 4; g++) {
            var drift = this.reduceMotion ? 0 : Math.sin(time / 900 + g * 1.9) * 12;
            ctx.save();
            ctx.globalAlpha = entry * (0.34 - g * 0.06);
            ctx.translate(-g * 16 + drift, -g * 9);
            this.silhouette(ctx, info.colour);
            ctx.restore();
          }
          break;
        case 'stationary':
          this.silhouette(ctx, info.colour, 0.5 * entry);
          var swing = Math.sin(time / 520) * 0.5;
          ctx.strokeStyle = info.colour;
          ctx.globalAlpha = entry * 0.85;
          ctx.lineWidth = 2;
          ctx.beginPath();
          ctx.moveTo(0, -34);
          ctx.lineTo(Math.sin(swing) * 34, -34 + Math.cos(swing) * 40);
          ctx.stroke();
          ctx.fillStyle = info.colour;
          ctx.beginPath();
          ctx.arc(Math.sin(swing) * 34, -34 + Math.cos(swing) * 40, 5, 0, Math.PI * 2);
          ctx.fill();
          break;
        case 'one_quitter_cyclic':
          this.silhouette(ctx, info.colour, 0.5 * entry);
          ctx.save();
          ctx.rotate(time / 700);
          for (var r = 0; r < 4; r++) {
            ctx.rotate(Math.PI / 2);
            ctx.globalAlpha = entry * (r === 0 ? 0.95 : 0.35);
            ctx.fillStyle = info.colour;
            ctx.beginPath(); ctx.arc(0, -46, 6, 0, Math.PI * 2); ctx.fill();
          }
          ctx.restore();
          break;
        case 'general_periodic':
          for (var d = 0; d < 3; d++) {
            ctx.save();
            var jx = (Math.random() - 0.5) * 7, jy = (Math.random() - 0.5) * 7;
            ctx.translate(jx, jy);
            ctx.globalAlpha = entry * 0.28;
            this.silhouette(ctx, info.colour);
            ctx.restore();
          }
          break;
        case 'two_quitter_periodic':
          var beatPulse = 1 + 0.06 * Math.sin(time / 260) + 0.04 * Math.sin(time / 130);
          ctx.save(); ctx.scale(beatPulse, beatPulse);
          ctx.save(); ctx.translate(-24, 0); this.silhouette(ctx, info.colour, entry * 0.8);
          ctx.restore();
          ctx.save(); ctx.translate(24, -4); this.silhouette(ctx, info.colour, entry * 0.8);
          ctx.restore();
          ctx.restore();
          break;
        case 'boss':
          this.silhouette(ctx, info.colour, entry * 0.9);
          // Star badge.
          ctx.save();
          ctx.translate(-10, -6);
          ctx.fillStyle = '#f4e08a';
          ctx.globalAlpha = entry * (0.6 + 0.4 * Math.abs(Math.sin(time / 380)));
          ctx.beginPath();
          for (var sIdx = 0; sIdx < 10; sIdx++) {
            var ang = (Math.PI / 5) * sIdx - Math.PI / 2;
            var rad = sIdx % 2 ? 3.5 : 8;
            ctx[sIdx ? 'lineTo' : 'moveTo'](Math.cos(ang) * rad, Math.sin(ang) * rad);
          }
          ctx.closePath(); ctx.fill();
          ctx.restore();
          break;
      }
      ctx.restore();

      // Caption.
      ctx.save();
      ctx.globalAlpha = entry;
      ctx.textAlign = 'right';
      ctx.fillStyle = info.colour;
      ctx.font = '600 16px "Courier New", ui-monospace, monospace';
      ctx.fillText(info.name.toUpperCase(), w - 18, h * 0.80);
      ctx.font = '12px "Courier New", ui-monospace, monospace';
      ctx.globalAlpha = entry * 0.75;
      ctx.fillText(info.subtitle, w - 18, h * 0.80 + 18);
      ctx.restore();
    },

    silhouette: function (ctx, colour, alpha) {
      ctx.save();
      if (alpha !== undefined) ctx.globalAlpha *= alpha;
      ctx.fillStyle = colour;
      ctx.globalAlpha *= 0.55;
      ctx.beginPath();
      ctx.moveTo(-30, 62);
      ctx.quadraticCurveTo(-36, -6, -14, -18);
      ctx.lineTo(14, -18);
      ctx.quadraticCurveTo(36, -6, 30, 62);
      ctx.closePath();
      ctx.fill();
      ctx.beginPath(); ctx.arc(0, -32, 13, 0, Math.PI * 2); ctx.fill();
      ctx.beginPath(); ctx.ellipse(0, -41, 29, 7, 0, 0, Math.PI * 2); ctx.fill();
      ctx.beginPath();
      ctx.moveTo(-15, -41);
      ctx.quadraticCurveTo(-13, -60, 0, -60);
      ctx.quadraticCurveTo(13, -60, 15, -41);
      ctx.closePath();
      ctx.fill();
      ctx.restore();
    },

    /* Haze between the player and the table. Kept faint: it is atmosphere,
     * never something that hides a reading. */
    drawSmoke: function (time) {
      var ctx = this.ctx, w = this.width, h = this.height;
      var seconds = time / 1000;
      ctx.save();
      ctx.globalCompositeOperation = 'screen';
      for (var k = 0; k < SMOKE.length; k++) {
        var puff = SMOKE[k];
        var drift = this.reduceMotion ? 0 : seconds;
        var x = (((puff.x + puff.vx * drift) % 1) + 1) % 1;
        var y = (((puff.y + puff.vy * drift) % 1) + 1) % 1;
        var breathe = this.reduceMotion ? 1
          : 1 + 0.16 * Math.sin(seconds * 0.22 + puff.phase);
        var radius = puff.r * Math.min(w, h) * breathe;
        var cx = x * w, cy = y * h * 0.85;
        var grad = ctx.createRadialGradient(cx, cy, 0, cx, cy, radius);
        grad.addColorStop(0, 'rgba(214, 198, 170, 0.052)');
        grad.addColorStop(0.55, 'rgba(198, 180, 150, 0.024)');
        grad.addColorStop(1, 'rgba(0, 0, 0, 0)');
        ctx.fillStyle = grad;
        ctx.beginPath();
        ctx.ellipse(cx, cy, radius, radius * 0.62, 0, 0, Math.PI * 2);
        ctx.fill();
      }
      ctx.restore();
    },

    /* Lamplight falls off into the corners; the room has no other light. */
    drawLampFall: function (time) {
      var ctx = this.ctx, w = this.width, h = this.height;
      var wick = this.reduceMotion ? 0.9 : flicker(time);
      ctx.save();
      var fall = ctx.createRadialGradient(
        w / 2, h * 0.36, Math.min(w, h) * 0.12,
        w / 2, h * 0.42, Math.max(w, h) * 0.78);
      fall.addColorStop(0, 'rgba(0,0,0,0)');
      fall.addColorStop(0.55, 'rgba(10, 5, 2, ' + (0.20 * (2 - wick)).toFixed(3) + ')');
      fall.addColorStop(1, 'rgba(6, 3, 1, ' + (0.80 * (2 - wick)).toFixed(3) + ')');
      ctx.fillStyle = fall;
      ctx.fillRect(0, 0, w, h);
      ctx.restore();
    },

    drawVerdictBanner: function (time) {
      if (!this.wave || !this.wave.verdict) return;
      var ctx = this.ctx, w = this.width, h = this.height;
      var age = (performance.now() - (this.wave.verdictAt || this.wave.at)) / 1000;
      var info = ANTAGONISTS[this.wave.key];
      var held = this.wave.verdict === 'held';
      ctx.save();
      ctx.globalAlpha = clamp(1.4 - age * 0.35, 0, 1);
      ctx.textAlign = 'center';
      ctx.font = '700 34px "Courier New", ui-monospace, monospace';
      ctx.fillStyle = held ? 'rgba(220,238,214,0.92)' : 'rgba(255,190,180,0.95)';
      ctx.shadowColor = held ? 'rgba(120,220,150,0.6)' : 'rgba(230,60,50,0.8)';
      ctx.shadowBlur = 22;
      ctx.fillText(held ? 'NOBODY SETTLES' : 'THE TABLE SETTLES', w / 2, h * 0.30);
      ctx.font = '13px "Courier New", ui-monospace, monospace';
      ctx.shadowBlur = 0;
      ctx.globalAlpha *= 0.8;
      ctx.fillStyle = info ? info.colour : '#ddd';
      ctx.fillText(held ? (info ? info.name + ' walks out empty-handed' : '')
        : (info ? info.name + ' found the arrangement' : ''), w / 2, h * 0.30 + 22);
      ctx.restore();
    },

    drawFlash: function (time) {
      if (!this.flash) return;
      var age = (performance.now() - this.flash.at) / 320;
      if (age >= 1) { this.flash = null; return; }
      var ctx = this.ctx;
      ctx.save();
      ctx.globalAlpha = (1 - age) * this.flash.strength;
      ctx.fillStyle = this.flash.colour;
      ctx.fillRect(0, 0, this.width, this.height);
      ctx.restore();
    }
  };

  root.SOScene = Scene;
})(window);
