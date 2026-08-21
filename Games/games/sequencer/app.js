// The sequencer play surface.
//
// The machine is the display: colour, vibration, lamps, motion and sound carry
// every reading a player needs. Raw numbers, the reward table, tiers and the
// honesty statement live behind the ledger tab, which is the only place this
// game speaks the research language.
//
// Live feedback comes from evaluator.js, an exact port of the reference
// evaluator, recomputed on every interaction. The server engine is called at
// rest to confirm a settled room and is the only thing that ever records
// anything.

import { evaluate, EPS_KILL, N, validTable, maskLabel } from "./evaluator.js";
import { api, ApiError, MOCK, QUERY } from "./api.js";
import { MOCK_CURATED } from "./mockdata.js";
import { Machine } from "./audio.js";

// --- fiction ------------------------------------------------------------- //

const CHANNELS = ["Rye", "Boone", "Cass", "Wren"];

const ROOM_ADJECTIVES = [
  "Copper", "Slow", "Quiet", "Iron", "Amber", "Hollow", "Late", "Salt",
  "Glass", "Ember", "Grey", "Tin", "Velvet", "Cold", "Long", "Dusty",
];
const ROOM_NOUNS = [
  "Standoff", "Parlour", "Siding", "Bell", "Circuit", "Landing", "Yard",
  "Hour", "Signal", "Shift", "Junction", "Watch", "Corner", "Wire",
  "Chorus", "Room",
];

function hashText(text) {
  let hash = 5381;
  for (let i = 0; i < text.length; i += 1) {
    hash = ((hash * 33) ^ text.charCodeAt(i)) >>> 0;
  }
  return hash;
}

function tableKey(table) {
  return `t${hashText(JSON.stringify(table)).toString(36)}`;
}

// Rooms are named from the table itself, so the same room always answers to
// the same name and the player never has to read an identifier.
function roomName(table) {
  const hash = hashText(JSON.stringify(table));
  const adjective = ROOM_ADJECTIVES[hash % ROOM_ADJECTIVES.length];
  const noun = ROOM_NOUNS[(hash >>> 8) % ROOM_NOUNS.length];
  return `The ${adjective} ${noun}`;
}

// --- hazard <-> bar position -------------------------------------------- //
//
// Real settling patterns run from about 1 down to a thousandth and below, so
// the bar is logarithmic over six decades and the bottom of the travel is
// silence. Coarse dragging crosses the whole range; the fine modifiers slow it
// down by six and by twenty-five.

const DECADES = 6;
const HMIN = Math.pow(10, -DECADES);
const OFF_ZONE = 0.008;

function hazardToPosition(hazard) {
  if (!(hazard > 0)) return 0;
  if (hazard >= 1) return 1;
  if (hazard <= HMIN) return OFF_ZONE;
  return Math.max(OFF_ZONE, 1 + Math.log10(hazard) / DECADES);
}

function positionToHazard(position) {
  if (position <= OFF_ZONE) return 0;
  if (position >= 1) return 1;
  return Math.pow(10, DECADES * (position - 1));
}

function formatNumber(value) {
  if (!Number.isFinite(value)) return "—";
  if (value === 0) return "0";
  if (Math.abs(value) >= 0.001) return value.toFixed(6).replace(/0+$/, "").replace(/\.$/, "");
  return value.toExponential(3);
}

// The API sanitizes non-finite floats: inf becomes 1e9, -inf becomes -1e9 and
// nan becomes null. None of those are values, so they must never reach a
// gauge, a comparison against the settling threshold, or a difficulty ranking.
const NOT_A_VALUE = 1e9;

function serverScore(value) {
  if (typeof value !== "number" || !Number.isFinite(value)) return null;
  if (Math.abs(value) >= NOT_A_VALUE) return null;
  return value;
}

// Gauge position: log scale from 1e-4 to 4, with the settling line at a fixed
// notch, so "is the arc past the notch" is the whole reading.
function gaugeFraction(gap) {
  const low = -4;
  const high = Math.log10(4);
  if (!(gap > 0)) return 0;
  const at = Math.log10(gap);
  return Math.min(1, Math.max(0, (at - low) / (high - low)));
}

const NOTCH = gaugeFraction(EPS_KILL);
const GAUGE_LENGTH = 2 * Math.PI * 20; // the gauge circle's circumference

// --- state --------------------------------------------------------------- //

const state = {
  target: null,
  profile: { period: 2, hazards: [] },
  report: null,
  selected: { player: 0, phase: 0 },
  session:
    window.crypto && window.crypto.randomUUID
      ? window.crypto.randomUUID()
      : `sess-${Math.random().toString(36).slice(2)}`,
  started: 0,
  edits: 0,
  bestLocal: Infinity,
  lockedValue: null,
  confirmTimer: null,
  confirming: false,
  lockedProfileKey: null,
  attract: true,
  playing: false,
  record: {
    confirmed: null,
    hardened: null,
    submissionId: null,
    proposalId: null,
    lastError: null,
  },
};

const machine = new Machine();

const el = (id) => document.getElementById(id);
const dom = {
  frame: el("frame"),
  grid: el("grid"),
  caption: el("caption"),
  period: el("period"),
  periodOut: el("period-out"),
  targetName: el("target-name"),
  propose: el("propose"),
  status: el("status"),
  coach: el("coach"),
  tip: el("tip"),
  tether: el("tether"),
  tetherLine: el("tether-line"),
  halo: el("halo"),
  run: el("run"),
  runGlyph: el("run-glyph"),
  goal: el("goal"),
  goalText: el("goal-text"),
  gaugeArc: document.querySelector(".gauge-arc"),
  cellValue: el("cell-value"),
  editorLabel: el("editor-label"),
  mockFlag: el("mock-flag"),
  netFlag: el("net-flag"),
  targetsDialog: el("targets"),
  curatedList: el("curated-list"),
  candidateList: el("candidate-list"),
  handin: el("handin"),
  handinError: el("handin-error"),
  lockDialog: el("lock"),
  lockTitle: el("lock-title"),
  lockBody: el("lock-body"),
  lockResult: el("lock-result"),
  ledgerDialog: el("ledger"),
  ledgerRoom: el("ledger-room"),
  ledgerProfile: el("ledger-profile"),
  ledgerRecord: el("ledger-record"),
  progress: el("progress"),
};

function escapeHtml(text) {
  return String(text).replace(/[&<>"']/g, (ch) => {
    return { "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;", "'": "&#39;" }[ch];
  });
}

// The wire format is a 16-row array indexed by coalition mask. Payloads that
// travelled through the experiment's own JSON use coalition labels instead, so
// accept that shape too rather than silently dropping a room someone handed in.
function coerceTable(value) {
  if (validTable(value)) return value;
  if (!value || typeof value !== "object" || Array.isArray(value)) return null;
  const rows = [];
  for (let mask = 0; mask < 16; mask += 1) rows.push([0, 0, 0, 0]);
  let seen = 0;
  for (const [label, payoff] of Object.entries(value)) {
    const members = String(label).replace(/[{}\s]/g, "").split(",").filter(Boolean);
    if (!members.length || !Array.isArray(payoff) || payoff.length !== N) return null;
    let mask = 0;
    for (const member of members) {
      const index = Number(member) - 1;
      if (!Number.isInteger(index) || index < 0 || index >= N) return null;
      mask |= 1 << index;
    }
    if (mask === 0) continue;
    rows[mask] = payoff.map(Number);
    seen += 1;
  }
  if (!seen || !validTable(rows)) return null;
  return rows;
}

// --- progression --------------------------------------------------------- //

const STORE_KEY = "sequencer.progress.v1";
const COACH_KEY = "sequencer.coached.v1";

function loadProgress() {
  try {
    const parsed = JSON.parse(window.localStorage.getItem(STORE_KEY) || "");
    return {
      grooves: parsed.grooves || 0,
      fastestMs: parsed.fastestMs || null,
      hardest: parsed.hardest || null,
      killed: parsed.killed || {},
    };
  } catch {
    return { grooves: 0, fastestMs: null, hardest: null, killed: {} };
  }
}

function saveProgress() {
  try {
    window.localStorage.setItem(STORE_KEY, JSON.stringify(progress));
  } catch {
    /* private mode: progression is a nicety, not a record */
  }
}

let progress = loadProgress();

// --- grid ---------------------------------------------------------------- //

function blankHazards(period) {
  const rows = [];
  for (let t = 0; t < period; t += 1) rows.push([0, 0, 0, 0]);
  return rows;
}

function setPeriod(period) {
  const old = state.profile.hazards;
  const rows = blankHazards(period);
  for (let t = 0; t < Math.min(period, old.length); t += 1) rows[t] = old[t].slice();
  state.profile = { period, hazards: rows };
  if (state.selected.phase >= period) state.selected.phase = period - 1;
  dom.periodOut.textContent = String(period);
  if (dom.period.value !== String(period)) dom.period.value = String(period);
  buildGrid();
  refresh();
}

function buildGrid() {
  const period = state.profile.period;
  dom.grid.style.setProperty("--steps", String(period));
  dom.grid.innerHTML = "";

  const head = document.createElement("div");
  head.className = "track head";
  head.appendChild(document.createElement("div"));
  const heads = document.createElement("div");
  heads.className = "steps";
  for (let t = 0; t < period; t += 1) {
    const mark = document.createElement("div");
    mark.className = "step-head";
    mark.dataset.phase = String(t);
    mark.textContent = "•";
    heads.appendChild(mark);
  }
  head.appendChild(heads);
  dom.grid.appendChild(head);

  for (let player = 0; player < N; player += 1) {
    const track = document.createElement("div");
    track.className = `track p${player}`;
    track.dataset.player = String(player);
    const strip = document.createElement("div");
    strip.className = "strip";
    strip.innerHTML =
      '<span class="lamp"></span>' +
      `<span class="strip-name">${CHANNELS[player]}</span>`;
    track.appendChild(strip);
    const lane = document.createElement("div");
    lane.className = "steps";
    for (let t = 0; t < period; t += 1) {
      const cell = document.createElement("button");
      cell.type = "button";
      cell.className = "cell";
      cell.dataset.player = String(player);
      cell.dataset.phase = String(t);
      cell.setAttribute(
        "aria-label",
        `${CHANNELS[player]}, step ${t + 1}`,
      );
      cell.innerHTML =
        '<span class="fill"></span><span class="band"></span>' +
        '<span class="ghost-mark"></span><span class="spark"></span>';
      lane.appendChild(cell);
    }
    track.appendChild(lane);
    dom.grid.appendChild(track);
  }
  paintCells();
}

function cellAt(player, phase) {
  return dom.grid.querySelector(`.cell[data-player="${player}"][data-phase="${phase}"]`);
}

function paintCells() {
  const hazards = state.profile.hazards;
  for (let player = 0; player < N; player += 1) {
    for (let t = 0; t < state.profile.period; t += 1) {
      const cell = cellAt(player, t);
      if (!cell) continue;
      const hazard = hazards[t][player];
      cell.style.setProperty("--level", String(hazardToPosition(hazard)));
      cell.classList.toggle("off", hazard === 0);
      cell.classList.toggle(
        "selected",
        state.selected.player === player && state.selected.phase === t,
      );
    }
  }
  const { player, phase } = state.selected;
  dom.editorLabel.textContent = `${CHANNELS[player]}, step ${phase + 1}`;
  if (document.activeElement !== dom.cellValue) {
    // Full precision in the box, so retyping what you see never rounds the
    // hazard you already have.
    const hazard = state.profile.hazards[phase][player];
    dom.cellValue.value = hazard === 0 ? "off" : String(hazard);
  }
}

function setHazard(phase, player, hazard) {
  const clamped = Math.min(1, Math.max(0, hazard));
  if (state.profile.hazards[phase][player] === clamped) return;
  state.profile.hazards[phase][player] = clamped;
  takeControl();
  state.edits += 1;
  if (state.started === 0) state.started = performance.now();
  refresh();
}

function nudgePosition(phase, player, delta) {
  const current = state.profile.hazards[phase][player];
  const position = hazardToPosition(current) + delta;
  setHazard(phase, player, positionToHazard(Math.min(1, Math.max(0, position))));
}

// --- attract mode, coaching, first-use hints ----------------------------- //

// The machine is already playing when the page opens. The first touch of a
// cell hands it over to the player and retires the nudge.
function takeControl() {
  if (!state.attract) return;
  state.attract = false;
  dismissCoach();
}

function showCoach(text) {
  dom.coach.textContent = text;
  dom.coach.hidden = false;
  window.setTimeout(dismissCoach, 9000);
}

function dismissCoach() {
  if (dom.coach.hidden) return;
  dom.coach.classList.add("fading");
  window.setTimeout(() => {
    dom.coach.hidden = true;
    dom.coach.classList.remove("fading");
  }, 700);
}

let tipShown = false;

function showTip(cell) {
  if (tipShown) return;
  tipShown = true;
  const box = cell.getBoundingClientRect();
  const frame = dom.frame.getBoundingClientRect();
  dom.tip.textContent = "drag — pull sideways for a steadier hand";
  dom.tip.hidden = false;
  dom.tip.style.left = `${box.left - frame.left + box.width / 2}px`;
  dom.tip.style.top = `${box.top - frame.top - 30}px`;
  dom.tip.style.transform = "translateX(-50%)";
  window.setTimeout(() => {
    dom.tip.classList.add("fading");
    window.setTimeout(() => {
      dom.tip.hidden = true;
      dom.tip.classList.remove("fading");
    }, 600);
  }, 3200);
}

// --- interaction --------------------------------------------------------- //

let drag = null;

// Pull-away granularity.
//
// While dragging a bar, how far the pointer has strayed sideways from the slot
// sets how much of your movement lands: full gain over the slot itself, and a
// tenth of it for every PULL_DECADE pixels you pull away, so a steady hand is
// something you reach for mid-gesture rather than a key you have to know
// about. The modifiers still work and multiply on top of it.
const PULL_DECADE = 200;
const PULL_FLOOR = 0.001;

function pullGain(clientX) {
  if (!drag) return 1;
  const box = drag.cell.getBoundingClientRect();
  const centre = box.left + box.width / 2;
  const outside = Math.max(0, Math.abs(clientX - centre) - box.width / 2);
  return Math.max(PULL_FLOOR, Math.pow(10, -outside / PULL_DECADE));
}

function gainFor(event) {
  let gain = pullGain(event.clientX);
  if (event.shiftKey) gain *= 0.16;
  else if (event.altKey || event.ctrlKey || event.metaKey) gain *= 0.04;
  return gain;
}

function select(player, phase) {
  state.selected = { player, phase };
  paintCells();
}

dom.grid.addEventListener("pointerover", (event) => {
  const cell = event.target.closest(".cell");
  if (cell) showTip(cell);
});

// The halo is the tool's size: full over a slot, closing down as the hand
// steadies. On hover it is only a hint that the tool has a size at all.
function haloRadius(gain) {
  return 7 + 25 * Math.max(0, Math.min(1, gain));
}

function showReach(clientX, clientY, gain, hovering) {
  const frame = dom.frame.getBoundingClientRect();
  const x = clientX - frame.left;
  const y = clientY - frame.top;
  const radius = haloRadius(gain);
  dom.halo.hidden = false;
  dom.halo.classList.toggle("hovering", Boolean(hovering));
  dom.halo.style.left = `${x}px`;
  dom.halo.style.top = `${y}px`;
  dom.halo.style.width = `${radius * 2}px`;
  dom.halo.style.height = `${radius * 2}px`;
  if (hovering || !drag) {
    dom.tether.hidden = true;
    return;
  }
  const cell = drag.cell.getBoundingClientRect();
  dom.tether.hidden = false;
  dom.tetherLine.setAttribute("x1", String(cell.left + cell.width / 2 - frame.left));
  dom.tetherLine.setAttribute("y1", String(y));
  dom.tetherLine.setAttribute("x2", String(x));
  dom.tetherLine.setAttribute("y2", String(y));
}

function hideReach() {
  dom.halo.hidden = true;
  dom.tether.hidden = true;
  dom.grid.querySelectorAll(".cell.tuning").forEach((cell) => {
    cell.classList.remove("tuning");
  });
}

// Light the decade the bar is working in, so the scale you are on is visible
// while you are on it.
function markBand(cell, hazard) {
  const position = hazardToPosition(hazard);
  const band = Math.min(5, Math.max(0, Math.floor((1 - position) * DECADES)));
  cell.style.setProperty("--band-top", String(band / DECADES));
}

dom.grid.addEventListener("pointermove", (event) => {
  if (drag) return;
  const cell = event.target.closest(".cell");
  if (cell) showReach(event.clientX, event.clientY, 1, true);
  else hideReach();
});

dom.grid.addEventListener("pointerleave", () => {
  if (drag) return; // a drag may wander off the grid and still be live
  hideReach();
});

dom.grid.addEventListener("pointerdown", (event) => {
  const cell = event.target.closest(".cell");
  if (!cell) return;
  event.preventDefault();
  cell.focus();
  const player = Number(cell.dataset.player);
  const phase = Number(cell.dataset.phase);
  select(player, phase);
  takeControl();
  drag = {
    cell,
    player,
    phase,
    lastY: event.clientY,
    height: cell.clientHeight || 88,
    pointerId: event.pointerId,
  };
  try {
    cell.setPointerCapture(event.pointerId);
  } catch {
    // Capture is a convenience; the window listeners below keep the gesture.
  }
  cell.classList.add("tuning");
  markBand(cell, state.profile.hazards[phase][player]);
  showReach(event.clientX, event.clientY, gainFor(event), false);
});

window.addEventListener("pointermove", (event) => {
  if (!drag) return;
  const gain = gainFor(event);
  const delta = ((drag.lastY - event.clientY) / drag.height) * gain;
  drag.lastY = event.clientY;
  nudgePosition(drag.phase, drag.player, delta);
  markBand(drag.cell, state.profile.hazards[drag.phase][drag.player]);
  showReach(event.clientX, event.clientY, gain, false);
});

function endDrag() {
  hideReach();
  if (!drag) return;
  try {
    if (drag.cell.hasPointerCapture && drag.cell.hasPointerCapture(drag.pointerId)) {
      drag.cell.releasePointerCapture(drag.pointerId);
    }
  } catch {
    /* nothing to release */
  }
  drag = null;
}

window.addEventListener("pointerup", endDrag);
window.addEventListener("pointercancel", endDrag);

dom.grid.addEventListener(
  "wheel",
  (event) => {
    const cell = event.target.closest(".cell");
    if (!cell) return;
    event.preventDefault();
    const player = Number(cell.dataset.player);
    const phase = Number(cell.dataset.phase);
    select(player, phase);
    const step = event.shiftKey ? 0.004 : 0.02;
    nudgePosition(phase, player, event.deltaY < 0 ? step : -step);
  },
  { passive: false },
);

dom.grid.addEventListener("dblclick", (event) => {
  const cell = event.target.closest(".cell");
  if (!cell) return;
  const player = Number(cell.dataset.player);
  const phase = Number(cell.dataset.phase);
  setHazard(phase, player, state.profile.hazards[phase][player] === 0 ? 0.05 : 0);
});

dom.grid.addEventListener("keydown", (event) => {
  const cell = event.target.closest(".cell");
  if (!cell) return;
  const player = Number(cell.dataset.player);
  const phase = Number(cell.dataset.phase);
  const fine = event.shiftKey ? 0.004 : event.altKey ? 0.001 : 0.02;
  const current = state.profile.hazards[phase][player];
  const keys = {
    ArrowUp: () => nudgePosition(phase, player, fine),
    ArrowDown: () => nudgePosition(phase, player, -fine),
    PageUp: () => setHazard(phase, player, current === 0 ? HMIN : current * 2),
    PageDown: () => setHazard(phase, player, current / 2),
    Home: () => setHazard(phase, player, 0),
    End: () => setHazard(phase, player, 1),
  };
  if (keys[event.key]) {
    event.preventDefault();
    select(player, phase);
    keys[event.key]();
    return;
  }
  const moves = {
    ArrowLeft: [player, (phase - 1 + state.profile.period) % state.profile.period],
    ArrowRight: [player, (phase + 1) % state.profile.period],
  };
  if (moves[event.key]) {
    event.preventDefault();
    const [p, t] = moves[event.key];
    select(p, t);
    cellAt(p, t).focus();
  }
});

dom.cellValue.addEventListener("change", () => {
  const { player, phase } = state.selected;
  const text = dom.cellValue.value.trim().toLowerCase();
  if (text === "off" || text === "") {
    setHazard(phase, player, 0);
  } else {
    const parsed = Number(text);
    if (Number.isFinite(parsed)) setHazard(phase, player, parsed);
  }
  paintCells();
});

el("halve").addEventListener("click", () => {
  const { player, phase } = state.selected;
  setHazard(phase, player, state.profile.hazards[phase][player] / 2);
});
el("double").addEventListener("click", () => {
  const { player, phase } = state.selected;
  const current = state.profile.hazards[phase][player];
  setHazard(phase, player, current === 0 ? HMIN : current * 2);
});
el("zero").addEventListener("click", () => {
  const { player, phase } = state.selected;
  setHazard(phase, player, 0);
});

// --- patterns ------------------------------------------------------------ //

function applyPattern(build) {
  state.profile.hazards = build(state.profile.period);
  takeControl();
  state.edits += 1;
  if (state.started === 0) state.started = performance.now();
  paintCells();
  refresh();
}

el("preset-clear").addEventListener("click", () => applyPattern(blankHazards));
el("preset-pair").addEventListener("click", () => {
  if (state.profile.period < 2) setPeriod(2);
  applyPattern((period) => {
    const rows = blankHazards(period);
    for (let t = 0; t < period; t += 1) {
      const pair = t % 2 === 0 ? [0, 2] : [1, 3];
      rows[t][pair[0]] = 0.05;
      rows[t][pair[1]] = 0.05;
    }
    return rows;
  });
});
el("preset-solo").addEventListener("click", () => {
  applyPattern((period) => {
    const rows = blankHazards(period);
    for (let t = 0; t < period; t += 1) rows[t][t % N] = 0.05;
    return rows;
  });
});
el("preset-random").addEventListener("click", () => {
  applyPattern((period) => {
    const rows = blankHazards(period);
    for (let t = 0; t < period; t += 1) {
      for (let i = 0; i < N; i += 1) {
        rows[t][i] =
          Math.random() < 0.45 ? positionToHazard(0.45 + 0.55 * Math.random()) : 0;
      }
    }
    return rows;
  });
});
el("preset-fine").addEventListener("click", () => {
  applyPattern((period) =>
    state.profile.hazards.slice(0, period).map((row) => row.map((h) => h / 2)),
  );
});

// --- the machine as the display ------------------------------------------ //

function profileKey() {
  return JSON.stringify(state.profile.hazards);
}

function refresh() {
  paintCells();
  if (!state.target) return;
  const report = evaluate(state.target.table, state.profile.hazards);
  state.report = report;
  if (report.exploitability < state.bestLocal) state.bestLocal = report.exploitability;
  machine.setProfile(state.profile.hazards);
  machine.setTension(report.exploitability);
  render(report);
  scheduleConfirm();
  if (dom.ledgerDialog.open) renderLedger();
}

function render(report) {
  const arc = gaugeFraction(report.exploitability);
  const settled = report.exploitability <= EPS_KILL;
  const heat = settled ? 0 : arcHeat(arc);

  dom.frame.style.setProperty("--tension", String(Math.max(0, Math.min(1, heat))));
  dom.run.style.setProperty("--arc", String(arc));
  dom.run.style.setProperty("--notch", String(NOTCH));
  dom.run.style.setProperty("--tension", String(Math.max(0, Math.min(1, heat))));
  // The needle's own colour, mixed here rather than in CSS: an SVG filter that
  // references a colour function silently drops the stroke in some engines.
  dom.run.style.setProperty("--arc-color", vuColour(heat));
  // Drive the needle length from here: a unitless calc() on stroke-dashoffset
  // is resolved inconsistently, and a needle that silently reads empty is
  // worse than no needle at all.
  if (dom.gaugeArc) {
    dom.gaugeArc.setAttribute(
      "stroke-dashoffset",
      (GAUGE_LENGTH * (1 - arc)).toFixed(2),
    );
  }
  renderGoal(arc, settled);

  let worst = 0;
  for (let i = 1; i < N; i += 1) {
    if (report.per_player[i] > report.per_player[worst]) worst = i;
  }
  const deviation = report.best_deviations[worst];
  const strikes = [];
  deviation.policy.forEach((strike, t) => {
    if (strike) strikes.push(t + 1);
  });

  dom.grid.querySelectorAll(".track").forEach((track) => {
    if (!track.dataset.player) return;
    const player = Number(track.dataset.player);
    const gain = gaugeFraction(report.per_player[player]);
    track.style.setProperty("--gain", gain.toFixed(3));
    track.classList.toggle("binding", player === worst && !settled);
  });

  dom.grid.querySelectorAll(".cell").forEach((cell) => {
    const player = Number(cell.dataset.player);
    const phase = Number(cell.dataset.phase);
    const strike = !settled && player === worst && deviation.policy[phase];
    cell.classList.toggle("ghosted", Boolean(strike));
    cell.classList.toggle("ghost-track", !settled && player === worst);
  });

  const who = `<b class="p${worst}">${CHANNELS[worst]}</b>`;
  dom.caption.classList.toggle("settled", settled);
  if (settled) {
    dom.caption.innerHTML = "Nobody wants to move. Hold it there.";
  } else if (strikes.length === 1) {
    dom.caption.innerHTML = `${who} breaks on ${strikes[0]}.`;
  } else if (strikes.length > 1) {
    const list = `${strikes.slice(0, -1).join(", ")} and ${strikes[strikes.length - 1]}`;
    dom.caption.innerHTML = `${who} breaks on ${list}.`;
  } else {
    dom.caption.innerHTML = `${who} would rather wait it out.`;
  }
}

// The standing objective. It never leaves the panel, it carries its own
// needle, and it changes state as the needle comes down to the notch, so a
// player looking at a cold screen can read both the aim and the progress
// toward it.
function renderGoal(arc, settled) {
  dom.goal.style.setProperty("--arc", String(arc));
  dom.goal.style.setProperty("--notch", String(NOTCH));
  dom.goal.style.setProperty("--arc-color", vuColour(settled ? 0 : arcHeat(arc)));
  const shelved = Boolean(state.record.submissionId);
  const near = !settled && arc <= NOTCH * 1.3;
  dom.goal.classList.toggle("done", settled);
  dom.goal.classList.toggle("near", near);
  if (shelved && settled) {
    dom.goalText.textContent = "on the shelf — take another room";
  } else if (settled) {
    dom.goalText.textContent = "the room is quiet — cut it to brass";
  } else if (near) {
    dom.goalText.textContent = "almost — the room is settling";
  } else {
    dom.goalText.textContent = "settle the room — bring the needle to the notch";
  }
}

// how far above the notch the needle sits, as 0..1
function arcHeat(arc) {
  return Math.max(0, Math.min(1, arc / Math.max(NOTCH, 1e-9) - 1 + 0.35));
}

// phosphor green at rest, hot orange when the room is coming apart
function vuColour(heat) {
  const calm = [99, 240, 168];
  const hot = [255, 106, 77];
  const mix = Math.max(0, Math.min(1, heat));
  const channel = (i) => Math.round(calm[i] + (hot[i] - calm[i]) * mix);
  return `rgb(${channel(0)}, ${channel(1)}, ${channel(2)})`;
}

function setStatus(text, kind = "") {
  dom.status.textContent = text;
  dom.status.className = `status ${kind}`;
}

function showNetworkIssue(error) {
  state.record.lastError = `${error.kind}: ${error.message}`;
  dom.netFlag.hidden = false;
  dom.netFlag.textContent =
    error.kind === "offline"
      ? "the wire is down"
      : error.kind === "unavailable"
        ? "the house is busy"
        : "the house refused that";
  if (dom.ledgerDialog.open) renderLedger();
}

function clearNetworkIssue() {
  state.record.lastError = null;
  dom.netFlag.hidden = true;
  dom.netFlag.textContent = "";
}

// --- confirmation and the settle ----------------------------------------- //

function scheduleConfirm() {
  if (state.confirmTimer !== null) window.clearTimeout(state.confirmTimer);
  state.confirmTimer = null;
  if (!state.report || state.report.exploitability > EPS_KILL) return;
  state.confirmTimer = window.setTimeout(confirmAtRest, 450);
}

async function confirmAtRest() {
  if (state.confirming || !state.target || !state.report) return;
  const key = profileKey();
  if (key === state.lockedProfileKey) return;
  state.confirming = true;
  setStatus("the house is listening…", "busy");
  try {
    const response = await api.evaluate(state.target.table, {
      period: state.profile.period,
      hazards: state.profile.hazards,
    });
    clearNetworkIssue();
    const value = serverScore(response.exploitability);
    // Stamped with the groove it was measured for: hardening replaces the
    // groove, and a reading must never look newer than it is.
    state.record.confirmed = value === null ? null : { value, key };
    if (value === null) {
      setStatus("the house could not read the room — nothing was written down", "warn");
    } else if (value <= EPS_KILL) {
      settle(value, key, Math.abs(value - state.report.exploitability));
    } else {
      setStatus("the house says someone would still move — keep tuning", "warn");
    }
  } catch (error) {
    if (error instanceof ApiError) {
      showNetworkIssue(error);
      setStatus("the house never answered — nothing was written down", "warn");
    } else {
      throw error;
    }
  } finally {
    state.confirming = false;
    if (dom.ledgerDialog.open) renderLedger();
  }
}

function tierFor(value) {
  return value < 0.5 * EPS_KILL ? "numerical-wide" : "numerical-narrow";
}

function settle(value, key, drift) {
  state.lockedProfileKey = key;
  state.lockedValue = value;
  state.record.drift = drift;
  state.record.hardened = null;
  state.record.submissionId = null;
  const elapsed = state.started ? performance.now() - state.started : 0;
  machine.chime();

  dom.lockTitle.textContent = "the room settles";
  el("lock-submit").textContent = "cut it to brass";
  dom.lockBody.innerHTML =
    `Four hands, and not one of them would rather move. ` +
    `<b>${escapeHtml(state.target.name)}</b> is quiet.` +
    (MOCK
      ? " This was a rehearsal, so nothing will be written down."
      : " The house listened and agrees.");
  dom.lockResult.textContent = "";
  el("lock-submit").disabled = false;
  if (!dom.lockDialog.open) dom.lockDialog.showModal();
  setStatus("the room settles", "good");

  progress.grooves += 1;
  // A groove carried over from the previous room can settle a new one on load;
  // that still counts, but it is not a time worth recording.
  if (state.edits > 0 && elapsed > 0) {
    if (progress.fastestMs === null || elapsed < progress.fastestMs) {
      progress.fastestMs = elapsed;
    }
  }
  const score = state.target.known_score;
  if (typeof score === "number" && (!progress.hardest || score > progress.hardest.score)) {
    progress.hardest = { name: state.target.name, score };
  }
  progress.killed[tableKey(state.target.table)] = {
    name: state.target.name,
    at: new Date().toISOString(),
    exploitability: value,
  };
  saveProgress();
  renderTargetLists();
  if (dom.ledgerDialog.open) renderLedger();
}

el("lock-close").addEventListener("click", () => dom.lockDialog.close());
el("lock-ledger").addEventListener("click", () => {
  dom.lockDialog.close();
  openLedger();
});

// Seal: harden, then submit.
//
// The engine snaps the hazards to small denominators and redoes the whole
// evaluation in exact rational arithmetic. When the snapped groove still
// settles the room, that snapped groove — not the floats the player dragged
// out — is what enters the library.
el("lock-submit").addEventListener("click", async () => {
  const button = el("lock-submit");
  button.disabled = true;
  dom.lockResult.textContent = "the engraver is checking the groove…";
  const original = {
    period: state.profile.period,
    hazards: state.profile.hazards.map((row) => row.slice()),
  };
  const source = {
    game: "sequencer",
    session: state.session,
    trace: {
      edits: state.edits,
      elapsed_ms: Math.round(state.started ? performance.now() - state.started : 0),
      period: state.profile.period,
      client_exploitability: state.report ? state.report.exploitability : null,
      server_exploitability: state.lockedValue,
      target_kind: state.target.kind,
    },
  };
  if (state.target.id && state.target.kind !== "handin") {
    source.table_id = state.target.id;
  } else {
    source.table = state.target.table;
  }
  try {
    let hardened = null;
    try {
      hardened = await api.harden(state.target.table, original);
    } catch (error) {
      if (!(error instanceof ApiError) || error.status >= 500) throw error;
      hardened = null; // no rational-snap route here; plain submission it is
    }
    let profile = original;
    let note;
    const snapped = hardened ? validProfile(hardened.profile) : null;
    if (hardened && hardened.kills && snapped) {
      profile = snapped;
      applyProfile(snapped);
      source.trace.hardened = true;
      source.trace.snap_denominator = hardened.denominator;
      note =
        "Cut to brass: the groove holds even with the dials rounded to the " +
        "notches, so it will play true on any machine.";
    } else if (hardened) {
      source.trace.hardened = false;
      source.trace.snap_denominator = hardened.denominator || null;
      note =
        "It would not take the brass — rounded to the notches the room breaks " +
        "up again, so your groove goes on the shelf exactly as you played it.";
    } else {
      source.trace.hardened = null;
      note = "No engraver on this bench, so the groove goes up as you played it.";
    }
    state.record.hardened = hardened;
    let result;
    try {
      result = await api.submitProfile(profile, source);
    } catch (error) {
      if (error instanceof ApiError && error.kind === "bad-request") {
        // Some servers validate the source shape strictly; retry minimal.
        const minimal = { game: source.game, session: source.session };
        if (source.table_id) minimal.table_id = source.table_id;
        else minimal.table = source.table;
        result = await api.submitProfile(profile, minimal);
      } else {
        throw error;
      }
    }
    state.record.submissionId = result.id || null;
    if (state.report) render(state.report);
    dom.lockResult.textContent =
      `${note} It is on the shelf now, and every room the house opens from here` +
      ` on gets tried against it.` +
      (MOCK ? " (Rehearsal: nothing was actually written down.)" : "");
    dom.lockTitle.textContent = "cut to brass";
    clearNetworkIssue();
  } catch (error) {
    if (error instanceof ApiError) {
      showNetworkIssue(error);
      dom.lockResult.textContent = "The bench is shut — nothing was cut or shelved.";
      button.disabled = false;
      return;
    }
    throw error;
  }
  if (dom.ledgerDialog.open) renderLedger();
});

function validProfile(profile) {
  if (!profile || !Array.isArray(profile.hazards)) return null;
  const hazards = profile.hazards;
  const period = Number(profile.period || hazards.length);
  if (!Number.isInteger(period) || period < 1 || period > 8) return null;
  if (hazards.length !== period) return null;
  const rows = [];
  for (const row of hazards) {
    if (!Array.isArray(row) || row.length !== N) return null;
    const clean = [];
    for (const value of row) {
      if (typeof value !== "number" || !Number.isFinite(value)) return null;
      if (value < 0 || value > 1) return null;
      clean.push(value);
    }
    rows.push(clean);
  }
  return { period, hazards: rows };
}

// Load a groove the server handed back. The room is already settled, so the
// new pattern must not be treated as a fresh settling.
function applyProfile(profile) {
  state.profile = {
    period: profile.period,
    hazards: profile.hazards.map((row) => row.slice()),
  };
  if (state.selected.phase >= profile.period) state.selected.phase = profile.period - 1;
  dom.period.value = String(profile.period);
  dom.periodOut.textContent = String(profile.period);
  buildGrid();
  refresh();
  state.lockedProfileKey = profileKey();
}

// --- rooms --------------------------------------------------------------- //

let curated = [];
let candidates = [];

function loadTarget(target) {
  state.target = target;
  state.started = 0;
  state.edits = 0;
  state.bestLocal = Infinity;
  state.lockedProfileKey = null;
  state.lockedValue = null;
  state.record.confirmed = null;
  state.record.hardened = null;
  state.record.submissionId = null;
  dom.targetName.textContent = target.name;
  // A room handed in from elsewhere is not in the house's books yet, so this
  // is the only place it can be shown to them.
  dom.propose.hidden = target.kind !== "handin";
  dom.propose.disabled = false;
  setStatus("");
  refresh();
}

function decodeTablePayload(text) {
  const trimmed = text.trim();
  if (!trimmed) throw new Error("nothing to load");
  let json = trimmed;
  if (!trimmed.startsWith("[") && !trimmed.startsWith("{")) {
    const padded = trimmed.replace(/-/g, "+").replace(/_/g, "/");
    json = window.atob(padded + "=".repeat((4 - (padded.length % 4)) % 4));
  }
  const parsed = JSON.parse(json);
  const table = coerceTable(Array.isArray(parsed) ? parsed : parsed.table || parsed);
  if (!table) throw new Error("that is not a room");
  return {
    id: (parsed && parsed.id) || null,
    real_name: (parsed && parsed.name) || "hand-in",
    name: roomName(table),
    table,
    note: (parsed && parsed.note) || "handed in from another game",
    known_score: null,
    kind: "handin",
  };
}

dom.handin.addEventListener("keydown", (event) => {
  if (event.key !== "Enter") return;
  event.preventDefault();
  try {
    const target = decodeTablePayload(dom.handin.value);
    dom.handinError.textContent = "";
    dom.targetsDialog.close();
    loadTarget(target);
  } catch (error) {
    dom.handinError.textContent = error.message;
  }
});

function scoreOf(entry) {
  if (!entry) return -Infinity;
  const evaluated = entry.evaluation ? serverScore(entry.evaluation.score) : null;
  if (evaluated !== null) return evaluated;
  const known = serverScore(entry.known_score);
  return known === null ? -Infinity : known;
}

// Difficulty as heat, never as a number: five pips over the range of floors
// the portal actually produces.
function heatPips(score) {
  if (!Number.isFinite(score)) return null;
  const low = -6;
  const high = Math.log10(0.05);
  const at = Math.min(1, Math.max(0, (Math.log10(Math.max(score, 1e-9)) - low) / (high - low)));
  return 1 + Math.round(at * 4);
}

function roomCard(spec) {
  const card = document.createElement("button");
  card.type = "button";
  card.className = `card${spec.wanted ? " wanted" : ""}${spec.settled ? " settled" : ""}`;
  const pips = heatPips(spec.score);
  let heat = "";
  for (let i = 1; i <= 5; i += 1) {
    heat += `<span class="pip${pips !== null && i <= pips ? " on" : ""}"></span>`;
  }
  // One corner tag only: a named one if the room has earned it, otherwise
  // "new" when nobody has taken its measure yet.
  const tag = spec.tag || (pips === null ? "new" : "");
  card.innerHTML =
    `<span class="card-name">${escapeHtml(spec.name)}</span>` +
    `<span class="card-heat">${heat}</span>` +
    (tag ? `<span class="card-tag">${escapeHtml(tag)}</span>` : "");
  card.addEventListener("click", () => {
    dom.targetsDialog.close();
    loadTarget(spec.target);
  });
  return card;
}

function renderTargetLists() {
  const ranked = candidates.slice().sort((a, b) => scoreOf(b) - scoreOf(a));
  dom.curatedList.innerHTML = "";
  curated
    .slice()
    .sort((a, b) => scoreOf(a) - scoreOf(b))
    .forEach((entry, index) => {
      const floor = scoreOf(entry);
      dom.curatedList.appendChild(
        roomCard({
          name: roomName(entry.table),
          score: floor,
          tag: index === 0 ? "warm-up" : "",
          settled: Boolean(progress.killed[tableKey(entry.table)]),
          target: {
            id: entry.id,
            real_name: entry.name,
            name: roomName(entry.table),
            table: entry.table,
            note: entry.note,
            known_score: Number.isFinite(floor) ? floor : null,
            kind: "curated",
          },
        }),
      );
    });

  dom.candidateList.innerHTML = "";
  dom.candidateList.classList.toggle(
    "divided",
    dom.curatedList.children.length > 0 && ranked.length > 0,
  );
  ranked.forEach((entry, index) => {
    const floor = scoreOf(entry);
    dom.candidateList.appendChild(
      roomCard({
        name: roomName(entry.table),
        score: floor,
        wanted: index === 0,
        tag: index === 0 ? "bounty" : entry.status === "killed" ? "quiet" : "",
        settled: Boolean(progress.killed[tableKey(entry.table)]),
        target: {
          id: entry.id,
          real_name: `candidate ${entry.id}`,
          name: roomName(entry.table),
          table: entry.table,
          note: `${entry.game || "unknown"} · tier ${entry.tier || "unattacked"} · status ${
            entry.status || "proposed"
          }`,
          known_score: Number.isFinite(floor) ? floor : null,
          kind: "candidate",
        },
      }),
    );
  });
}

function normalizeEntries(entries) {
  return (entries || [])
    .map((entry) => ({ ...entry, table: coerceTable(entry.table) }))
    .filter((entry) => entry.table !== null);
}

async function loadRooms() {
  try {
    curated = normalizeEntries((await api.curated()).tables);
    clearNetworkIssue();
  } catch (error) {
    if (error instanceof ApiError) showNetworkIssue(error);
    else throw error;
  }
  try {
    candidates = normalizeEntries((await api.candidates(50)).candidates);
  } catch (error) {
    if (error instanceof ApiError) showNetworkIssue(error);
    else throw error;
  }
  renderTargetLists();
  if (state.target) return;
  if (curated.length) {
    const entry = curated[0];
    const floor = scoreOf(entry);
    loadTarget({
      id: entry.id,
      real_name: entry.name,
      name: roomName(entry.table),
      table: entry.table,
      note: entry.note,
      known_score: Number.isFinite(floor) ? floor : null,
      kind: "curated",
    });
    return;
  }
  // The machine never opens on an empty stage. With no rooms from the house,
  // it plays a room bundled with the page; nothing about it can be recorded,
  // which is exactly what the unreachable house already means.
  const fallback = MOCK_CURATED[0];
  loadTarget({
    id: null,
    real_name: `${fallback.name} (bundled copy, no connection)`,
    name: roomName(fallback.table),
    table: fallback.table,
    note: "bundled with the page because the house did not answer",
    known_score: null,
    kind: "fallback",
  });
}

el("targets-open").addEventListener("click", () => {
  renderTargetLists();
  dom.targetsDialog.showModal();
});

dom.propose.addEventListener("click", async () => {
  if (!state.target) return;
  dom.propose.disabled = true;
  setStatus("posting the bounty…", "busy");
  try {
    const response = await api.proposeCandidate(state.target.table, state.session, {
      origin: state.target.note || "hand-in",
      best_client_exploitability: Number.isFinite(state.bestLocal) ? state.bestLocal : null,
      edits: state.edits,
      period: state.profile.period,
      elapsed_ms: Math.round(state.started ? performance.now() - state.started : 0),
    });
    state.record.proposalId = response.id || null;
    clearNetworkIssue();
    setStatus(
      "bounty posted — the room is on the board for everyone now" +
        (MOCK ? " (rehearsal: nothing was actually written)" : ""),
      "good",
    );
  } catch (error) {
    if (error instanceof ApiError) {
      showNetworkIssue(error);
      setStatus("the board would not take the bounty just now", "warn");
      dom.propose.disabled = false;
    } else {
      throw error;
    }
  }
  if (dom.ledgerDialog.open) renderLedger();
});

// --- the ledger ---------------------------------------------------------- //

function numGrid(pairs) {
  return (
    '<div class="num-grid">' +
    pairs
      .map(
        ([label, value]) =>
          `<div><span>${escapeHtml(label)}</span><b>${escapeHtml(String(value))}</b></div>`,
      )
      .join("") +
    "</div>"
  );
}

function renderLedger() {
  const target = state.target;
  if (target) {
    let matrix =
      '<table class="matrix"><tr><th>coalition</th><th>1</th><th>2</th>' +
      "<th>3</th><th>4</th></tr>";
    for (let mask = 1; mask < 16; mask += 1) {
      matrix += `<tr><th>${escapeHtml(maskLabel(mask))}</th>`;
      for (let i = 0; i < N; i += 1) {
        const value = target.table[mask][i];
        matrix += `<td${value === 0 ? ' class="zero"' : ""}>${formatNumber(value)}</td>`;
      }
      matrix += "</tr>";
    }
    matrix += "</table>";
    dom.ledgerRoom.innerHTML =
      numGrid([
        ["shown as", target.name],
        ["real name", target.real_name || target.id || "—"],
        ["id", target.id || "(not in the ledger)"],
        ["source", target.kind],
        ["recorded attack floor", Number.isFinite(target.known_score)
          ? formatNumber(target.known_score)
          : "not recorded"],
      ]) +
      `<p class="legend">${escapeHtml(target.note || "")}</p>` +
      matrix;
  } else {
    dom.ledgerRoom.textContent = "no room loaded";
  }

  const report = state.report;
  if (report) {
    const rows = state.profile.hazards
      .map(
        (row, t) =>
          `<tr><th>step ${t + 1}</th>` +
          row.map((h) => `<td>${formatNumber(h)}</td>`).join("") +
          "</tr>",
      )
      .join("");
    const deviations = report.best_deviations
      .map((d) => {
        const steps = d.policy
          .map((strike, t) => (strike ? t + 1 : null))
          .filter((t) => t !== null);
        return [
          `${CHANNELS[d.player]} (player ${d.player + 1}) gain`,
          `${formatNumber(d.gap)} — quits at ${steps.length ? steps.join(",") : "never"}`,
        ];
      });
    dom.ledgerProfile.innerHTML =
      `<table class="matrix"><tr><th>period ${state.profile.period}</th>` +
      CHANNELS.map((name) => `<th>${name}</th>`).join("") +
      `</tr>${rows}</table>` +
      numGrid([
        ["exploitability (client)", formatNumber(report.exploitability)],
        ["best found this room", Number.isFinite(state.bestLocal)
          ? formatNumber(state.bestLocal)
          : "—"],
        ...report.on_path.map((value, i) => [
          `on-path value, ${CHANNELS[i]}`,
          formatNumber(value),
        ]),
        ...deviations,
      ]) +
      '<p class="legend">These come from the in-browser evaluator and drive ' +
      "feel only. The kill threshold is 0.02.</p>";
  } else {
    dom.ledgerProfile.textContent = "—";
  }

  const record = state.record;
  const confirmed = record.confirmed;
  const hardened = record.hardened;
  const stale = confirmed && confirmed.key !== profileKey();
  const pairs = [
    ["mode", MOCK ? "rehearsal (?mock=1) — nothing is recorded" : "live server"],
    ["server exploitability", confirmed
      ? `${formatNumber(confirmed.value)}${stale ? " (measured before hardening)" : ""}`
      : "not confirmed"],
    ["evidence tier", hardened && hardened.kills
      ? "exact (rational-snapped, re-verified exactly)"
      : confirmed
        ? `${tierFor(confirmed.value)} or stronger`
        : "—"],
    ["client vs server drift", Number.isFinite(record.drift) ? record.drift.toExponential(2) : "—"],
    ["snap denominator", hardened && hardened.denominator ? hardened.denominator : "—"],
    ["exact exploitability", hardened && hardened.exploitability_exact
      ? hardened.exploitability_exact
      : "—"],
    ["library profile id", record.submissionId || "not submitted"],
    ["proposed candidate id", record.proposalId || "—"],
    ["session", state.session],
    ["last error", record.lastError || "none"],
  ];
  dom.ledgerRecord.innerHTML =
    numGrid(pairs) +
    '<p class="legend">Only the server engine writes the ledger. A settled ' +
    "room means one profile holds this table below the kill threshold — " +
    "bounded numerical evidence that the table is not a counterexample, never " +
    "a theorem, and never a statement about profiles other than this one.</p>";

  const fastest =
    progress.fastestMs === null ? "—" : `${(progress.fastestMs / 1000).toFixed(1)} s`;
  const hardest = progress.hardest
    ? `${progress.hardest.name} (floor ${formatNumber(progress.hardest.score)})`
    : "—";
  dom.progress.innerHTML = "";
  [
    ["rooms settled", String(progress.grooves)],
    ["fastest settle", fastest],
    ["hardest room settled", hardest],
  ].forEach(([label, value]) => {
    const item = document.createElement("li");
    item.innerHTML = `<span>${escapeHtml(label)}</span><b>${escapeHtml(value)}</b>`;
    dom.progress.appendChild(item);
  });
}

function openLedger() {
  renderLedger();
  dom.ledgerDialog.showModal();
}

el("ledger-open").addEventListener("click", openLedger);

// --- transport ----------------------------------------------------------- //

dom.run.addEventListener("click", () => {
  state.playing = !state.playing;
  dom.run.setAttribute("aria-pressed", String(state.playing));
  dom.runGlyph.textContent = state.playing ? "■" : "▶";
  if (state.playing) {
    machine.setProfile(state.profile.hazards);
    if (state.report) machine.setTension(state.report.exploitability);
    machine.start();
  } else {
    machine.stop();
    dom.grid.querySelectorAll(".step-head, .cell").forEach((node) => {
      node.classList.remove("now");
    });
  }
});

const muteButton = el("mute");
muteButton.addEventListener("click", () => {
  const muted = muteButton.getAttribute("aria-pressed") === "false";
  muteButton.setAttribute("aria-pressed", String(muted));
  muteButton.textContent = muted ? "🔇" : "🔊";
  machine.setMuted(muted);
});

const hitsButton = el("hits");
hitsButton.addEventListener("click", () => {
  const on = hitsButton.getAttribute("aria-pressed") === "false";
  hitsButton.setAttribute("aria-pressed", String(on));
  machine.setHits(on);
});

machine.onStep = (phase) => {
  dom.grid.querySelectorAll(".step-head").forEach((mark) => {
    mark.classList.toggle("now", Number(mark.dataset.phase) === phase);
  });
  dom.grid.querySelectorAll(".cell").forEach((cell) => {
    cell.classList.toggle("now", Number(cell.dataset.phase) === phase);
  });
};

machine.onHit = (phase, player) => {
  const cell = cellAt(player, phase);
  if (!cell) return;
  cell.classList.remove("hit");
  void cell.offsetWidth;
  cell.classList.add("hit");
  jolt();
};

// A single short judder when a channel actually fires. Discrete, never
// continuous, and silent for readers who asked for reduced motion.
let joltTimer = null;
function jolt() {
  if (window.matchMedia && window.matchMedia("(prefers-reduced-motion: reduce)").matches) {
    return;
  }
  dom.frame.classList.remove("jolt");
  void dom.frame.offsetWidth;
  dom.frame.classList.add("jolt");
  if (joltTimer !== null) window.clearTimeout(joltTimer);
  joltTimer = window.setTimeout(() => dom.frame.classList.remove("jolt"), 200);
}

dom.period.addEventListener("input", () => {
  takeControl();
  setPeriod(Number(dom.period.value));
});

// WebAudio may only start from a user gesture; the machine runs regardless and
// the voices join at the first touch anywhere on the page.
["pointerdown", "keydown"].forEach((type) => {
  window.addEventListener(type, () => machine.unlock(), { once: true });
});

// --- boot ---------------------------------------------------------------- //

// A pattern with a pulse to it that leaves the room plainly unsettled: the
// machine is already playing something when the page opens.
function attractPattern() {
  return [
    [0.05, 0, 0.05, 0],
    [0, 0.02, 0, 0],
    [0, 0.05, 0, 0.05],
    [0.01, 0, 0.02, 0],
  ];
}

// Anything that escapes is recorded for the ledger and said once, in fiction,
// rather than left as a dead panel.
window.addEventListener("error", (event) => {
  state.record.lastError = `uncaught: ${event.message}`;
  if (dom.ledgerDialog && dom.ledgerDialog.open) renderLedger();
});
window.addEventListener("unhandledrejection", (event) => {
  state.record.lastError = `unhandled rejection: ${event.reason}`;
  if (dom.ledgerDialog && dom.ledgerDialog.open) renderLedger();
});

function boot() {
  dom.mockFlag.hidden = !MOCK;
  dom.run.style.setProperty("--notch", String(NOTCH));
  state.profile = { period: 4, hazards: attractPattern() };
  dom.period.value = "4";
  dom.periodOut.textContent = "4";
  buildGrid();

  const handed = QUERY.get("table");
  if (handed) {
    try {
      loadTarget(decodeTablePayload(handed));
    } catch {
      setStatus("that room could not be read", "warn");
    }
  }

  state.playing = true;
  machine.setProfile(state.profile.hazards);
  machine.start();

  let coached = false;
  try {
    coached = window.localStorage.getItem(COACH_KEY) === "1";
  } catch {
    coached = false;
  }
  if (!coached) {
    showCoach("find the groove nobody wants to break");
    try {
      window.localStorage.setItem(COACH_KEY, "1");
    } catch {
      /* private mode */
    }
  }

  loadRooms();
}

// The machine must come up even if something in the opening sequence throws:
// a blank panel is the one state that tells the player nothing at all.
try {
  boot();
  window.__sequencerBooted = true;
} catch (error) {
  state.record.lastError = `boot: ${error && error.message ? error.message : error}`;
  try {
    if (!dom.grid.querySelector(".cell")) buildGrid();
    machine.setProfile(state.profile.hazards);
    machine.start();
    state.playing = true;
    window.__sequencerBooted = true;
  } catch {
    /* the inline watchdog in index.html takes it from here */
  }
  setStatus("the bench came up short — the room may not be the one you meant", "warn");
}
