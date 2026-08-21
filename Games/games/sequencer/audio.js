// The machine's voice. Synthesised entirely with WebAudio; no files, no CDNs.
//
// Two layers carry information:
//   * four percussive voices, one per channel, whose loudness and brightness
//     follow that channel's hazard at the current step, so the pattern you
//     hear is the pattern you drew;
//   * a two-oscillator drone whose detuning is the total tension. High tension
//     beats fast and sounds rough; as the tension falls towards the kill
//     threshold the beating slows to a stop and a fifth fades in, so tuning
//     into consonance and locking the groove are literally the same act.
//
// Every audible quantity is duplicated on screen: the meters are the ground
// truth and the sound is a second channel, never the only one.

const STEP_SECONDS = 0.3;
const LOOKAHEAD_MS = 25;
const SCHEDULE_AHEAD = 0.12;
const BASE_HZ = 110;

export class Machine {
  constructor() {
    this.ctx = null;
    this.master = null;
    this.drone = null;
    this.noise = null;
    this.running = false;
    this.muted = false;
    this.hits = true;
    this.timer = null;
    this.blocked = false;
    this.nextStep = 0;
    this.phase = 0;
    this.period = 1;
    this.hazards = [[0, 0, 0, 0]];
    this.tension = 1;
    this.onStep = () => {};
    this.onHit = () => {};
  }

  // WebAudio contexts may only start from a user gesture, so the machine runs
  // on a wall clock and the voices join in as soon as one arrives.
  ensure() {
    if (this.ctx) {
      if (this.ctx.state === "suspended") this.ctx.resume();
      return;
    }
    if (this.blocked) return;
    const Ctx = window.AudioContext || window.webkitAudioContext;
    if (!Ctx) {
      this.blocked = true;
      return;
    }
    try {
      this.ctx = new Ctx();
    } catch {
      this.blocked = true; // no audio here; the visual transport carries on
      return;
    }
    this.master = this.ctx.createGain();
    this.master.gain.value = this.muted ? 0 : 0.9;
    this.master.connect(this.ctx.destination);

    const length = Math.floor(this.ctx.sampleRate);
    this.noise = this.ctx.createBuffer(1, length, this.ctx.sampleRate);
    const data = this.noise.getChannelData(0);
    for (let i = 0; i < length; i += 1) data[i] = Math.random() * 2 - 1;

    const filter = this.ctx.createBiquadFilter();
    filter.type = "lowpass";
    filter.frequency.value = 900;
    const gain = this.ctx.createGain();
    gain.gain.value = 0.0;
    const low = this.ctx.createOscillator();
    const high = this.ctx.createOscillator();
    const fifth = this.ctx.createOscillator();
    const fifthGain = this.ctx.createGain();
    low.type = "sine";
    high.type = "sine";
    fifth.type = "sine";
    low.frequency.value = BASE_HZ;
    high.frequency.value = BASE_HZ;
    fifth.frequency.value = BASE_HZ * 1.5;
    fifthGain.gain.value = 0;
    low.connect(filter);
    high.connect(filter);
    fifth.connect(fifthGain);
    fifthGain.connect(filter);
    filter.connect(gain);
    gain.connect(this.master);
    low.start();
    high.start();
    fifth.start();
    this.drone = { low, high, fifth, fifthGain, filter, gain };
    this.applyTension();
  }

  setMuted(muted) {
    this.muted = muted;
    if (!muted) this.ensure();
    if (this.master) {
      this.master.gain.setTargetAtTime(muted ? 0 : 0.9, this.ctx.currentTime, 0.02);
    }
  }

  setHits(on) {
    this.hits = on;
  }

  setProfile(hazards) {
    this.hazards = hazards;
    this.period = hazards.length;
    if (this.phase >= this.period) this.phase = 0;
  }

  // tension is the current total exploitability.
  setTension(tension) {
    this.tension = Number.isFinite(tension) ? Math.max(0, tension) : 0;
    this.applyTension();
  }

  applyTension() {
    if (!this.ctx || !this.drone) return;
    if (this.ctx.state !== "running") return;
    const now = this.ctx.currentTime;
    const beat = 14 * (1 - Math.exp(-1.2 * this.tension));
    const consonance = Math.exp(-this.tension * 14); // ~1 only very near a kill
    this.drone.high.frequency.setTargetAtTime(BASE_HZ + beat, now, 0.05);
    this.drone.fifthGain.gain.setTargetAtTime(0.35 * consonance, now, 0.15);
    this.drone.filter.frequency.setTargetAtTime(
      500 + 2600 * Math.exp(-this.tension * 1.5),
      now,
      0.08,
    );
    this.drone.gain.gain.setTargetAtTime(this.running ? 0.09 : 0.0, now, 0.1);
  }

  // The visual transport does not wait for audio: it runs on performance.now()
  // and the voices are scheduled only while an audio context is actually
  // running, which is what lets the machine idle audibly-silent but visibly
  // alive before the first user gesture unlocks sound.
  start() {
    if (this.running) return;
    this.running = true;
    this.nextStep = performance.now() / 1000 + 0.05;
    this.applyTension();
    this.timer = window.setInterval(() => this.pump(), LOOKAHEAD_MS);
  }

  stop() {
    this.running = false;
    if (this.timer !== null) window.clearInterval(this.timer);
    this.timer = null;
    this.applyTension();
  }

  audible() {
    return Boolean(this.ctx) && this.ctx.state === "running";
  }

  pump() {
    if (!this.running) return;
    const wall = performance.now() / 1000;
    while (this.nextStep < wall + SCHEDULE_AHEAD) {
      const lead = Math.max(0, this.nextStep - wall);
      const phase = this.phase;
      if (this.audible()) this.scheduleStep(phase, this.ctx.currentTime + lead);
      window.setTimeout(() => this.onStep(phase), lead * 1000);
      this.phase = (this.phase + 1) % this.period;
      this.nextStep += STEP_SECONDS;
    }
  }

  // Called on the first real user gesture; harmless afterwards.
  unlock() {
    this.ensure();
    if (this.ctx && this.ctx.state === "suspended") this.ctx.resume();
    this.applyTension();
  }

  scheduleStep(phase, time) {
    const row = this.hazards[phase] || [0, 0, 0, 0];
    for (let player = 0; player < 4; player += 1) {
      const hazard = row[player];
      if (!(hazard > 0)) continue;
      // Loudness follows the log position of the hazard, so a 1e-3 bar is
      // quiet but clearly present rather than inaudible.
      const level = Math.min(1, Math.max(0, 1 + Math.log10(hazard) / 6));
      this.voice(player, time, level);
      if (this.hits && Math.random() < hazard) {
        this.strike(time, player);
        const lag = Math.max(0, (time - this.ctx.currentTime) * 1000);
        window.setTimeout(() => this.onHit(phase, player), lag);
      }
    }
  }

  voice(player, time, level) {
    const ctx = this.ctx;
    const amp = ctx.createGain();
    const peak = 0.02 + 0.32 * level;
    amp.gain.setValueAtTime(0.0001, time);
    amp.gain.exponentialRampToValueAtTime(peak, time + 0.008);
    amp.connect(this.master);
    if (player === 3) {
      const source = ctx.createBufferSource();
      source.buffer = this.noise;
      const filter = ctx.createBiquadFilter();
      filter.type = "highpass";
      filter.frequency.value = 4000 + 4000 * level;
      source.connect(filter);
      filter.connect(amp);
      amp.gain.exponentialRampToValueAtTime(0.0001, time + 0.05 + 0.05 * level);
      source.start(time);
      source.stop(time + 0.16);
      return;
    }
    const osc = ctx.createOscillator();
    const filter = ctx.createBiquadFilter();
    filter.type = "lowpass";
    filter.frequency.value = 300 + 3000 * level;
    if (player === 0) {
      osc.type = "sine";
      osc.frequency.setValueAtTime(150, time);
      osc.frequency.exponentialRampToValueAtTime(48, time + 0.09);
      amp.gain.exponentialRampToValueAtTime(0.0001, time + 0.22);
    } else if (player === 1) {
      osc.type = "triangle";
      osc.frequency.setValueAtTime(196, time);
      osc.frequency.exponentialRampToValueAtTime(140, time + 0.12);
      amp.gain.exponentialRampToValueAtTime(0.0001, time + 0.24);
    } else {
      osc.type = "square";
      osc.frequency.setValueAtTime(392, time);
      amp.gain.exponentialRampToValueAtTime(0.0001, time + 0.16);
    }
    osc.connect(filter);
    filter.connect(amp);
    osc.start(time);
    osc.stop(time + 0.35);
  }

  // A realised quit: the loop would have ended right here.
  strike(time, player) {
    const ctx = this.ctx;
    const osc = ctx.createOscillator();
    const amp = ctx.createGain();
    osc.type = "sawtooth";
    osc.frequency.setValueAtTime(880 + 220 * player, time);
    osc.frequency.exponentialRampToValueAtTime(220, time + 0.12);
    amp.gain.setValueAtTime(0.0001, time);
    amp.gain.exponentialRampToValueAtTime(0.08, time + 0.005);
    amp.gain.exponentialRampToValueAtTime(0.0001, time + 0.18);
    osc.connect(amp);
    amp.connect(this.master);
    osc.start(time);
    osc.stop(time + 0.2);
  }

  // Played once when a groove locks.
  chime() {
    this.ensure();
    if (!this.audible()) return;
    const ctx = this.ctx;
    const time = ctx.currentTime + 0.02;
    [0, 4, 7, 12].forEach((semitone, index) => {
      const osc = ctx.createOscillator();
      const amp = ctx.createGain();
      osc.type = "sine";
      osc.frequency.value = 220 * Math.pow(2, semitone / 12);
      const at = time + index * 0.07;
      amp.gain.setValueAtTime(0.0001, at);
      amp.gain.exponentialRampToValueAtTime(0.22, at + 0.01);
      amp.gain.exponentialRampToValueAtTime(0.0001, at + 0.9);
      osc.connect(amp);
      amp.connect(this.master);
      osc.start(at);
      osc.stop(at + 1.0);
    });
  }
}
