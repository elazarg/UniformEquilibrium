/* standoff — synthesized saloon audio. No audio files; everything is built
 * from oscillators and noise buffers at load time. Muted until the first user
 * gesture, per browser autoplay policy. */
(function (root) {
  'use strict';

  var ctx = null;
  var master = null;
  var enabled = true;
  var noiseBuffer = null;
  var droneNodes = null;

  function ensure() {
    if (ctx) return ctx;
    var Ctor = root.AudioContext || root.webkitAudioContext;
    if (!Ctor) { enabled = false; return null; }
    ctx = new Ctor();
    master = ctx.createGain();
    master.gain.value = 0.5;
    master.connect(ctx.destination);
    var length = Math.floor(ctx.sampleRate * 2);
    noiseBuffer = ctx.createBuffer(1, length, ctx.sampleRate);
    var data = noiseBuffer.getChannelData(0);
    for (var i = 0; i < length; i++) data[i] = Math.random() * 2 - 1;
    return ctx;
  }

  function now() { return ctx ? ctx.currentTime : 0; }

  function tone(opts) {
    if (!enabled || !ensure()) return;
    var t0 = now() + (opts.delay || 0);
    var osc = ctx.createOscillator();
    var gain = ctx.createGain();
    osc.type = opts.type || 'sine';
    osc.frequency.setValueAtTime(opts.freq, t0);
    if (opts.to) osc.frequency.exponentialRampToValueAtTime(Math.max(1, opts.to), t0 + opts.dur);
    gain.gain.setValueAtTime(0.0001, t0);
    gain.gain.exponentialRampToValueAtTime(opts.gain || 0.2, t0 + (opts.attack || 0.008));
    gain.gain.exponentialRampToValueAtTime(0.0001, t0 + opts.dur);
    var tail = gain;
    if (opts.filter) {
      var biquad = ctx.createBiquadFilter();
      biquad.type = 'lowpass';
      biquad.frequency.value = opts.filter;
      gain.connect(biquad);
      tail = biquad;
    }
    osc.connect(gain);
    tail.connect(master);
    osc.start(t0);
    osc.stop(t0 + opts.dur + 0.05);
  }

  function noise(opts) {
    if (!enabled || !ensure()) return;
    var t0 = now() + (opts.delay || 0);
    var src = ctx.createBufferSource();
    src.buffer = noiseBuffer;
    src.loop = true;
    var biquad = ctx.createBiquadFilter();
    biquad.type = opts.filterType || 'bandpass';
    biquad.frequency.setValueAtTime(opts.freq || 900, t0);
    if (opts.freqTo) {
      biquad.frequency.exponentialRampToValueAtTime(Math.max(20, opts.freqTo), t0 + opts.dur);
    }
    biquad.Q.value = opts.q || 1;
    var gain = ctx.createGain();
    gain.gain.setValueAtTime(0.0001, t0);
    gain.gain.exponentialRampToValueAtTime(opts.gain || 0.2, t0 + (opts.attack || 0.005));
    gain.gain.exponentialRampToValueAtTime(0.0001, t0 + opts.dur);
    src.connect(biquad); biquad.connect(gain); gain.connect(master);
    src.start(t0);
    src.stop(t0 + opts.dur + 0.05);
  }

  var Audio = {
    unlock: function () {
      var c = ensure();
      if (c && c.state === 'suspended') c.resume();
    },
    setEnabled: function (value) {
      enabled = !!value;
      if (!enabled) Audio.stopDrone();
      else Audio.unlock();
    },
    isEnabled: function () { return enabled; },
    /* False when the browser gives us no AudioContext at all. */
    isAvailable: function () {
      return !!(root.AudioContext || root.webkitAudioContext);
    },

    click: function () { tone({ type: 'triangle', freq: 520, to: 380, dur: 0.06, gain: 0.10 }); },
    deny: function () {
      tone({ type: 'sawtooth', freq: 150, to: 90, dur: 0.18, gain: 0.13, filter: 700 });
    },
    chipDown: function () {
      tone({ type: 'square', freq: 900, to: 500, dur: 0.05, gain: 0.07 });
      noise({ freq: 2600, dur: 0.07, gain: 0.06, q: 2 });
    },
    card: function () {
      noise({ freq: 1800, freqTo: 600, dur: 0.14, gain: 0.08, q: 0.7 });
    },

    /* The bell that ends the editing phase. */
    bell: function () {
      [1, 2.76, 5.4].forEach(function (ratio, index) {
        tone({
          type: 'sine', freq: 520 * ratio, dur: 2.2 - index * 0.5,
          gain: 0.20 / (index + 1), attack: 0.004
        });
      });
      noise({ freq: 3200, dur: 0.4, gain: 0.05, q: 3 });
    },

    /* Per-antagonist arrival sting. `key` is the attack name. */
    sting: function (key) {
      switch (key) {
        case 'library_replay':
          tone({ type: 'sine', freq: 330, to: 300, dur: 1.4, gain: 0.09 });
          tone({ type: 'sine', freq: 331.7, to: 301, dur: 1.4, gain: 0.09, delay: 0.03 });
          noise({ freq: 500, freqTo: 220, dur: 1.2, gain: 0.05, q: 0.5 });
          break;
        case 'stationary':
          tone({ type: 'square', freq: 196, dur: 0.9, gain: 0.13, filter: 900 });
          for (var k = 0; k < 4; k++) {
            tone({ type: 'triangle', freq: 1200, dur: 0.05, gain: 0.07, delay: k * 0.24 });
          }
          break;
        case 'one_quitter_cyclic':
          for (var j = 0; j < 4; j++) {
            tone({
              type: 'triangle', freq: 440 * Math.pow(2, j / 12), dur: 0.16,
              gain: 0.11, delay: j * 0.13
            });
          }
          noise({ freq: 1500, freqTo: 400, dur: 0.6, gain: 0.05 });
          break;
        case 'general_periodic':
          [0, 0.07, 0.19, 0.26, 0.41].forEach(function (d, i) {
            tone({
              type: 'sawtooth', freq: 210 + i * 47, to: 180 + i * 30,
              dur: 0.3, gain: 0.07, filter: 1400, delay: d
            });
          });
          break;
        case 'two_quitter_periodic':
          tone({ type: 'sine', freq: 88, to: 62, dur: 1.6, gain: 0.26 });
          tone({ type: 'sine', freq: 132, to: 93, dur: 1.6, gain: 0.16 });
          noise({ freq: 220, freqTo: 90, dur: 1.8, gain: 0.10, q: 0.4 });
          break;
        case 'boss':
          tone({ type: 'sine', freq: 55, dur: 3.2, gain: 0.24 });
          tone({ type: 'sawtooth', freq: 110, to: 104, dur: 3.0, gain: 0.07, filter: 400 });
          break;
        default:
          tone({ type: 'sine', freq: 300, dur: 0.5, gain: 0.1 });
      }
    },

    /* A gunslinger draws. `pitch` separates the four voices. */
    draw: function (player) {
      var base = [92, 108, 124, 140][player % 4];
      noise({ freq: 2200, freqTo: 220, dur: 0.22, gain: 0.20, q: 0.6 });
      tone({ type: 'sine', freq: base, to: base * 0.45, dur: 0.3, gain: 0.22 });
    },

    /* Survived a wave. */
    hold: function () {
      tone({ type: 'triangle', freq: 392, dur: 0.4, gain: 0.10 });
      tone({ type: 'triangle', freq: 588, dur: 0.5, gain: 0.08, delay: 0.09 });
    },

    kill: function () {
      tone({ type: 'sawtooth', freq: 180, to: 40, dur: 1.8, gain: 0.24, filter: 900 });
      noise({ freq: 900, freqTo: 80, dur: 2.0, gain: 0.16, q: 0.4 });
    },

    victory: function () {
      [392, 494, 587, 784].forEach(function (freq, index) {
        tone({ type: 'triangle', freq: freq, dur: 1.1, gain: 0.12, delay: index * 0.13 });
      });
    },

    /* Low tension drone while the deep attack runs; `intensity` in [0,1]. */
    startDrone: function () {
      if (!enabled || !ensure() || droneNodes) return;
      var osc = ctx.createOscillator();
      var sub = ctx.createOscillator();
      var gain = ctx.createGain();
      osc.type = 'sawtooth'; osc.frequency.value = 58;
      sub.type = 'sine'; sub.frequency.value = 29;
      var lp = ctx.createBiquadFilter();
      lp.type = 'lowpass'; lp.frequency.value = 260;
      gain.gain.value = 0.0001;
      gain.gain.exponentialRampToValueAtTime(0.05, now() + 1.4);
      osc.connect(lp); sub.connect(lp); lp.connect(gain); gain.connect(master);
      osc.start(); sub.start();
      droneNodes = { osc: osc, sub: sub, gain: gain, lp: lp };
    },
    setDroneIntensity: function (value) {
      if (!droneNodes) return;
      var v = Math.max(0, Math.min(1, value));
      droneNodes.gain.gain.setTargetAtTime(0.04 + 0.09 * v, now(), 0.6);
      droneNodes.lp.frequency.setTargetAtTime(240 + 700 * v, now(), 0.8);
    },
    stopDrone: function () {
      if (!droneNodes) return;
      var nodes = droneNodes;
      droneNodes = null;
      try {
        nodes.gain.gain.setTargetAtTime(0.0001, now(), 0.25);
        nodes.osc.stop(now() + 1.2);
        nodes.sub.stop(now() + 1.2);
      } catch (e) { /* already stopped */ }
    },

    /* Heartbeat used while a wave is resolving. */
    heartbeat: function (strength) {
      var gain = 0.08 + 0.16 * Math.max(0, Math.min(1, strength));
      tone({ type: 'sine', freq: 62, to: 44, dur: 0.20, gain: gain });
      tone({ type: 'sine', freq: 58, to: 40, dur: 0.24, gain: gain * 0.7, delay: 0.19 });
    }
  };

  root.SOAudio = Audio;
})(window);
