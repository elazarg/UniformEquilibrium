// Phenotype: table structure -> procedural SVG organism. Deterministic in
// the table's contents (see hashTable) so the same table always draws the
// same creature, and structurally similar tables draw similarly, because
// every visual channel is read off the same structural notions a player is
// implicitly searching over:
//   - preemption digraph (tablemath.edgesOf)  -> limb tendrils, fork count,
//     thickness, and the rotating halo when an owner reaches a cycle
//     (filter 4's condition).
//   - solo-self reward magnitude/sign per player -> limb length and hue.
//   - overall reward magnitude                   -> body size.
//   - size-3 coalition sign patterns              -> skin spot texture.
//   - viable-owner count (filter 2)               -> eye count.
//   - quick-attack score vs. the kill line         -> tier (thriving / wary
//     / critical), which drives breathing rate and the grain/wobble/beat
//     confidence rendering called for by DESIGN.md. Never rendered as "this
//     is a counterexample" — only as a fitness reading of one attack level.
//   - binding attack name                          -> a small predator badge.

import { clamp, hashTable, mulberry32 } from './util.js';
import { r, edgesOf, viableOwnersOf, cellSign, hasOwnerCycle } from './tablemath.js';

export const EPS_KILL = 0.02;

export const PREDATOR_ICON = {
  library_replay: '\u{1F47B}', // ghost - the cheapest, already-known attacker
  stationary: '\u{1F577}️', // spider - sits and waits at fixed rates
  one_quitter_cyclic: '\u{1F43A}', // wolf - stalks a single scheduled quitter
  two_quitter_periodic: '\u{1F985}', // eagle - the Solan-Vieille repair shape
  general_periodic: '\u{1F40D}', // snake - unstructured periodic search
};

// Non-finite floats are sanitized server-side to a 1e9 sentinel meaning
// "nothing found by this attack", never a real value (see DESIGN.md HTTP API
// section) — treat that the same as no score at all.
export function tierOf(score) {
  if (score == null || score >= 1e9) return 'unknown';
  if (score < EPS_KILL) return 'critical';
  if (score < 4 * EPS_KILL) return 'wary';
  return 'thriving';
}

export function tierLabel(tier) {
  switch (tier) {
    case 'thriving':
      return 'thriving';
    case 'wary':
      return 'wary';
    case 'critical':
      return 'about to fall';
    default:
      return 'unscored';
  }
}

function hueFor(v) {
  // v in [-4, 4]; 0 -> green (140), +4 -> yellow-green (60), -4 -> blue (220)
  return clamp(140 - 20 * v, 0, 300);
}

function limbGeometry(cx, cy, angleDeg, len, forks, rng) {
  const rad = (angleDeg * Math.PI) / 180;
  const tipX = cx + Math.cos(rad) * len;
  const tipY = cy + Math.sin(rad) * len;
  const midX = cx + Math.cos(rad) * len * 0.55 + (rng() - 0.5) * 6;
  const midY = cy + Math.sin(rad) * len * 0.55 + (rng() - 0.5) * 6;
  const d = `M ${cx.toFixed(1)} ${cy.toFixed(1)} Q ${midX.toFixed(1)} ${midY.toFixed(1)} ${tipX.toFixed(1)} ${tipY.toFixed(1)}`;
  let forkSvg = '';
  for (let k = 0; k < forks; k++) {
    const spread = (k - (forks - 1) / 2) * 22;
    const fRad = ((angleDeg + spread) * Math.PI) / 180;
    const fx = tipX + Math.cos(fRad) * (len * 0.28);
    const fy = tipY + Math.sin(fRad) * (len * 0.28);
    forkSvg += `<line x1="${tipX.toFixed(1)}" y1="${tipY.toFixed(1)}" x2="${fx.toFixed(1)}" y2="${fy.toFixed(1)}" stroke-linecap="round"/>`;
  }
  return { d, tipX, tipY, forkSvg };
}

export function renderCreatureSVG(table, meta = {}) {
  const { score = null, bindingAttack = null } = meta;
  const seed = hashTable(table);
  const rng = mulberry32(seed);
  const e = edgesOf(table);
  const owners = viableOwnersOf(table);
  const tier = tierOf(score);

  const cx = 100;
  const cy = 108;
  const diag = [0, 1, 2, 3].map((i) => r(table, 1 << i, i));
  const avgAbs = diag.reduce((a, v) => a + Math.abs(v), 0) / 4;
  const bodyR = clamp(24 + 5 * avgAbs, 20, 46);
  const bodyHue = hueFor(diag.reduce((a, v) => a + v, 0) / 4);
  const vitality = clamp(
    (owners.length / 4) * 0.5 + (hasOwnerCycle(table) ? 0.5 : 0),
    0,
    1
  );

  const droop = tier === 'critical' ? 8 : 0;
  const limbAngles = [-90, 0, 90, 180]; // players 0..3 at N, E, S, W
  let limbsSvg = '';
  const tips = [];
  for (let i = 0; i < 4; i++) {
    const val = diag[i];
    const outDeg = (e[i] || []).length;
    const inDeg = [0, 1, 2, 3].filter((j) => j !== i && (e[j] || []).includes(i)).length;
    const lenBase = clamp(22 + 6 * Math.abs(val), 18, 52);
    const len = tier === 'critical' ? lenBase * 0.78 : lenBase;
    const thickness = clamp(3 + 1.6 * inDeg, 3, 10);
    const hue = hueFor(val);
    const angle = limbAngles[i] + droop;
    const { d, tipX, tipY, forkSvg } = limbGeometry(cx, cy, angle, len, outDeg, rng);
    tips.push([tipX, tipY]);
    limbsSvg += `<g class="limb" stroke="hsl(${hue.toFixed(0)},62%,45%)" fill="none">
      <path d="${d}" stroke-width="${thickness.toFixed(1)}" stroke-linecap="round"/>
      <g stroke-width="${Math.max(1.4, thickness * 0.5).toFixed(1)}">${forkSvg}</g>
      <circle cx="${tipX.toFixed(1)}" cy="${tipY.toFixed(1)}" r="${(thickness * 0.55).toFixed(1)}" fill="hsl(${hue.toFixed(0)},70%,55%)" stroke="none"/>
    </g>`;
  }

  let tendrilsSvg = '';
  for (let i = 0; i < 4; i++) {
    for (const j of e[i] || []) {
      const [x1, y1] = tips[i];
      const [x2, y2] = tips[j];
      tendrilsSvg += `<line x1="${x1.toFixed(1)}" y1="${y1.toFixed(1)}" x2="${x2.toFixed(1)}" y2="${y2.toFixed(1)}" stroke="hsla(${bodyHue.toFixed(0)},60%,60%,0.35)" stroke-width="1.2" stroke-dasharray="2 3"/>`;
    }
  }

  const triMasks = [7, 11, 13, 14]; // the four size-3 coalitions
  const patterns = new Set(triMasks.map((m) => table[m].map(cellSign).join('')));
  const spotCount = patterns.size;
  let spotsSvg = '';
  for (let k = 0; k < spotCount; k++) {
    const a = (k / spotCount) * Math.PI * 2 + rng() * 0.5;
    const rr = bodyR * 0.55;
    const sx = cx + Math.cos(a) * rr;
    const sy = cy + Math.sin(a) * rr * 0.8;
    spotsSvg += `<circle cx="${sx.toFixed(1)}" cy="${sy.toFixed(1)}" r="${(2.3 + rng() * 1.4).toFixed(1)}" fill="hsla(${bodyHue.toFixed(0)},50%,25%,0.4)"/>`;
  }

  const eyeCount = Math.max(1, owners.length);
  let eyesSvg = '';
  for (let k = 0; k < eyeCount; k++) {
    const spread = (eyeCount - 1) * 6;
    const ex = cx - spread / 2 + k * 6;
    eyesSvg += `<circle cx="${ex.toFixed(1)}" cy="${(cy - bodyR * 0.4).toFixed(1)}" r="2" fill="#141414"/>`;
  }

  const haloSvg = hasOwnerCycle(table)
    ? `<circle class="halo" cx="${cx}" cy="${cy}" r="${(bodyR + 14).toFixed(1)}" fill="none" stroke="hsla(${bodyHue.toFixed(0)},80%,62%,0.5)" stroke-width="1.5" stroke-dasharray="4 5"/>`
    : '';

  const predatorIcon = bindingAttack ? PREDATOR_ICON[bindingAttack] || '❓' : '';
  const bodyLight = 36 + vitality * 20;

  return `<svg class="creature-svg tier-${tier}" viewBox="0 0 200 216" data-tier="${tier}" role="img" aria-label="specimen">
    <g class="breathe">
      ${haloSvg}
      ${tendrilsSvg}
      ${limbsSvg}
      <ellipse cx="${cx}" cy="${cy}" rx="${bodyR.toFixed(1)}" ry="${(bodyR * 0.86).toFixed(1)}"
        fill="hsl(${bodyHue.toFixed(0)},52%,${bodyLight.toFixed(0)}%)"
        stroke="hsl(${bodyHue.toFixed(0)},58%,22%)" stroke-width="2"/>
      ${spotsSvg}
      ${eyesSvg}
    </g>
    ${predatorIcon ? `<text class="predator-badge" x="178" y="206" font-size="18" text-anchor="middle">${predatorIcon}</text>` : ''}
  </svg>`;
}
