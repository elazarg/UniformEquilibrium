# Whole-packet gate: participant-only gadget impossibility

Reviewer: `CODEX_EULER`

Packet reviewed:
[`PARTICIPANT_ONLY_GADGET_IMPOSSIBILITY.md`](../formalized/PARTICIPANT_ONLY_GADGET_IMPOSSIBILITY.md)

Verdict: **PASS**.  This is a complete unrestricted-strategy-class theorem
with two independent falsification reviews, and it satisfies every item of
`exports/README.md`.

## Mathematical audit

In the finite one-shot binary game, pure Continue pays zero against every
opponent action because an absorbing coalition then omits the player; the
all-Continue outcome also pays zero.  Thus the displayed complementarity in
terms of the pure-Quit value `Q_i` is exact.

For stationary repetition, the recursion is

```text
V_i=q_i Q_i+rho V_i.
```

If no hazard is sure, every positive hazard is interior and has `Q_i=0`; if a
hazard is sure, `rho=0` and all three complementarity cases apply
coordinatewise; if `rho=1`, all hazards vanish and every `Q_i<=0`.  Hence
`V_i=max(0,Q_i)` in every case, including a unique active player.

Against the stationary opponents, a deterministic Quit time `t` pays
`rho_-i^t Q_i` and Never pays zero.  Opponent absorption while the player
Continues also pays zero.  Pure-time extremality therefore bounds every
randomized and history-dependent behavioral deviation by `max(0,Q_i)=V_i`.
The stationary profile is an exact all-behavior terminal Nash profile, and
the checked endpoint consumer supplies a uniform-equilibrium payoff.

Zeroing passive coordinates changes both a prescribed payoff and every
unilateral-deviation payoff by at most the empty-safe finite maximum `delta`.
The gain changes by at most `2 delta`, so the quantitative terminal-gap
corollary is exact.

## Export criteria

The pointwise participant-only predicate is an arbitrary-table adapter, not a
supplied equilibrium certificate.  The theorem rules out the entire named
participant-only `INCENTIVE_GADGET` architecture and gives the quantitative
passive-reward escape, so it meets the question's accepted negative-answer
form.  The probability/information audit covers independent stationary
actions, repeated live histories, Never, ties, and unrestricted unilateral
behavior.  Boundary tests cover `rho=0`, `rho=1`, a unique active player,
negative Quit values, the one-player empty passive index, and the sharp
two-sided perturbation factor.

The source audit correctly identifies finite Nash selection, pure-time
extremality, and the exact-terminal-Nash consumer as checked background; a
narrow search found no stronger declaration for all participant-only reward
tables.  The two independent falsification reviews are linked, the Lean
handoff does not encode the conclusion as data, and all nonclaims are exact.

All five earlier repairs are present in the assembled documents, including
the empty-safe definition of `delta` and the formerly missing completion and
empty-coalition qualifications.
