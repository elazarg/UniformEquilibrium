# Review of Proposition 10 in `CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION`

Reviewer: `CODEX_GAUSS`

Status: `VALID` as ordinary mathematics; not checked in Lean.

## Claim checked

I audited the diffuse refusal-punishment construction in Section 13.  Distinct
players `o,k` satisfy

`r({o,i})_i <= r({o})_i` for every `i != o`,

`r({k})_o <= s_o = r({o})_o`.

Player `o` Quits surely at date zero.  If everyone instead Continues at that
date, `k` uses the uniform stopping law on `{1,...,L}`.  The claim is that the
prescribed target is the fixed vector `r({o})` and the complete unilateral
terminal debt is at most

`Delta/L`, where `Delta=max(0,r({o,k})_o-s_o)`.

## Outsider deviations and agency

For an outsider `i != o`, only its date-zero action can matter against the
prescribed profile.  Continuing yields `r({o})_i`; Quitting produces exactly
the collision `{o,i}` and yields no more by the first hypothesis.  Absorption
then makes every later component of the replacement strategy irrelevant.

This includes the punisher `k`.  There is no circular incentive argument:
when `k` is the unilateral deviator, `o` still Quits at date zero and the
punishment branch is never reached.  When `o` is the unilateral deviator,
`k` is not deviating and its prescribed punishment law remains available.
The construction therefore respects unilateral agency exactly.

## Owner calculation

Conditional on refusing at date zero, let `tau` be `k`'s uniform stopping time
on `{1,...,L}`.  Against a deterministic owner time `t` in the same window,

- `tau<t` gives the owner `r({k})_o <= s_o`;
- `tau=t` gives `r({o,k})_o`; and
- `tau>t` gives `s_o`.

The equality event has probability exactly `1/L`, so the pure-time payoff is
at most

`s_o + max(0,r({o,k})_o-s_o)/L = s_o+Delta/L`.

A time after the window or Never sees `k` Quit first and gives at most `s_o`.
Time zero itself gives exactly `s_o`.  These cases also cover a replacement
strategy which randomizes between immediate quitting and refusal.

The use of behavioral pure-time extremality is appropriate: against the fixed
opponents, the unique live-history hazard induces a stopping law, and the
payoff of any behavioral replacement is its mixture of deterministic finite
times and Never.  Thus no adaptive or history-dependent owner deviation
exceeds the displayed pure-time supremum.  The result is an upper bound; the
actual debt can be smaller than `Delta/L`.

## Information and timing

The punishment does not require observation of a private action or a public
random device.  The game remains live at date one exactly when every player
Continued at date zero.  Under the prescribed outsiders, that public survival
event identifies the owner's refusal.  The hazard realization of the uniform
law uses only `k`'s private behavioral randomization along the subsequent live
history.  Whether one describes it as a private planned time or by its hazard
sequence, its stopping law is uniform and the collision atom is exactly
`1/L`.

All off-path cases are exhausted: an outsider deviation cannot reach the
refusal branch because the prescribed owner still Quits, while an owner
deviation reaches a branch on which every nonowner except `k` Continues and
`k` follows the stated finite clock.

## Fixed target and semantic consumer

On the prescribed path the terminal coalition is `{o}`, so the payoff vector
is literally `r({o})` for every `L`.  For any requested positive terminal
error, choose `L` with `Delta/L` below that error (any `L` works when
`Delta=0`).  Because every selected profile pays **exactly** the displayed
target, the named checked fixed-target theorem
`quittingGame_isUniformEquilibriumPayoff_of_terminalTargetAcceptance`
(`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`)
then supplies the uniform-payoff conclusion with that same target.  The
target-free equivalence
`quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
would prove existence but would not by itself preserve `r({o})`; it is not the
consumer for this stronger fixed-target statement.
No extra finite-horizon threshold is asserted by the ordinary proof; it is
provided by that checked terminal-to-uniform consumer.

## Padding and minimal hypothesis tests

For Proposition 9's padded table, choose `o=j` and punisher `k`.  The active
outsider inequality is `r({j,k})_k=0<=2=r({j})_k`, the owner refusal inequality
is `r({k})_j=-1=s_j`, and each dummy has date-zero collision payoff `-1` versus
target coordinate zero.  The target is `(2,-1,0,...,0)` and the same `1/L`
bound therefore works for every padded cardinality claimed.

Each raw inequality is load-bearing for this literal construction:

- Without the outsider collision inequality, take two players `o,k` with
  `r({o})=(0,0)`, `r({k})=(0,0)`, and `r({o,k})=(0,1)`.  The owner-refusal
  condition holds and `Delta=0`, but `k` gains one by joining at date zero.
- Without `r({k})_o<=s_o`, take
  `r({o})=(0,0)`, `r({k})=(1,0)`, and `r({o,k})=(0,0)`.  The outsider
  condition and `Delta=0` hold, but the owner gains one by refusing forever.
- Distinctness of `o,k` is an agency condition, not notation.  A player's
  prescribed off-path strategy is replaced when that same player deviates,
  so the owner cannot serve as its own punisher.
- If the punishment date is deterministic and
  `r({o,k})_o>s_o`, the owner can collide at that known date and retain the
  whole collision gain.  Uniform diffusion is what reduces this gain by
  `1/L`; it is unnecessary only when `Delta=0`.

The construction can overlap a pure sure-exit profile when the singleton
already deters refusal, but it does not assume `s_o>=0` and therefore is not
merely the sure-exit-set consumer in disguise.  The source search reported in
the note is appropriately qualified: no inspected diffuse-clock declaration
is claimed as the producer, and no literature novelty is asserted.

I found no substantive mathematical objection.
