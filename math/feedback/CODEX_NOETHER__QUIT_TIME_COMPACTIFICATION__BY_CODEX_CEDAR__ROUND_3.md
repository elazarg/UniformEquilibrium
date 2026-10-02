# Second independent review of Proposition 10 in
# `CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION`

Reviewer: `CODEX_CEDAR`

Status: `VALID` as ordinary mathematics, including unrestricted behavioral
deviations and the literal fixed target.  It is an explicit quantitative
realization of the known instant-punishment boundary, not a new
conjecture-facing existence class.  No Lean formalization is claimed.

## Exact claim audited

Let `o` and `k` be distinct.  Assume

`r({o,i})_i <= r({o})_i` for every `i != o`,

and

`r({k})_o <= s_o = r({o})_o`.

Player `o` Quits surely at date zero.  Conditional on public survival through
that date, `k` uses the behavioral hazard whose stopping law is uniform on
`{1,...,L}`, while every other prescribed player Continues forever.  Put

`Delta=max(0,r({o,k})_o-s_o)`.

The claim is that the prescribed terminal payoff is exactly `r({o})`, the
terminal Nash debt against every unilateral behavioral deviation is at most
`Delta/L`, and the fixed target `r({o})` is consequently a uniform-equilibrium
payoff.

## Direct deviation audit

For an outsider `i != o`, the prescribed owner still Quits at date zero when
`i` alone changes strategy.  Hence only `i`'s date-zero action matters.
Continuing gives `r({o})_i`; Quitting gives `r({o,i})_i`, which is no larger by
hypothesis.  Randomizing between these actions is their convex combination,
and every later component is behind certain absorption.  This includes the
punisher `k`: its off-path clock is not an additional source of agency when
`k` itself is the unilateral deviator.

When `o` deviates, write `tau` for `k`'s uniform time.  A deterministic owner
time `t` has the following payoffs.

- At `t=0`, the payoff is `s_o`.
- For `1<=t<=L`, the events `tau<t`, `tau=t`, and `tau>t` pay respectively
  `r({k})_o`, `r({o,k})_o`, and `s_o`.  Only the tie can exceed `s_o`, and it
  has probability exactly `1/L`.
- For `t>L`, and for `Never`, `k` exits first and the payoff is
  `r({k})_o<=s_o`.

Thus every pure planned time pays at most `s_o+Delta/L`.

The passage to an unrestricted behavioral deviation is valid, not merely a
one-shot-deviation argument.  Against the fixed opponents there is one live
public history at every date.  A behavioral strategy for `o` therefore
induces a probability law on its finite quit time together with `Never`, and
its private randomization is independent of `k`'s.  Terminal payoff is the
mixture of the displayed deterministic-time payoffs.  Public survival reveals
only that `k` has not yet Quit; that information is already encoded by the
time-dependent hazard and does not let `o` observe `k`'s private planned time.
Consequently no history-dependent behavioral deviation exceeds the same
upper bound.

This proves an upper bound, not equality: if the collision row is not
profitable, or if another pure time is strictly worse, the actual debt can be
smaller than `Delta/L`.

## Fixed target and compiler

On path the quitting coalition is literally `{o}` at date zero, independently
of `L`, so every constructed profile has terminal payoff exactly `r({o})`.
For any positive acceptance error choose `L>=1` with `Delta/L` below that
error; when `Delta=0`, any such `L` works.  The terminal target distance is
zero coordinatewise.  Therefore the exact checked consumer is

`quittingGame_isUniformEquilibriumPayoff_of_terminalTargetAcceptance`

in
`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`.
It preserves the literal target and supplies the finite-horizon uniform
quantifiers.  The target-free terminal-existence equivalence would be too weak
for the displayed named-payoff conclusion.

## Falsification and boundary tests

Each literal hypothesis is load-bearing for this clock.

1. If the outsider inequality is removed, take two players with
   `r({o})=(0,0)`, `r({k})=(0,0)`, and `r({o,k})=(0,1)`.  Player `k` gains one
   by joining at date zero although the owner-refusal inequality holds.
2. If `r({k})_o<=s_o` is removed, take
   `r({o})=(0,0)`, `r({k})=(1,0)`, and `r({o,k})=(0,0)`.  The owner gains one
   by refusing forever although every outsider collision is harmless.
3. Distinctness is an agency requirement.  If `o=k`, replacing `o`'s strategy
   also removes the purported punishment clock.
4. A deterministic punishment date does not give the claimed small bound
   when `r({o,k})_o>s_o`: the owner can choose that date and obtain the full
   collision premium.  Uniform diffusion is exactly what changes it to a
   `1/L` atom.
5. Negative `s_o`, `Delta=0`, and arbitrary signs of outsider target
   coordinates cause no problem; the proof uses only the two raw upper
   inequalities and convexity of the induced stopping-law mixture.

I found no omitted deviation or boundary counterexample.

## Novelty and source comparison

The production declarations

- `quittingInstantPunishmentWorks_iff`, and
- `isUniformEquilibriumPayoff_soloReward_of_instantPunishment`

in `UniformEquilibrium/Quitting/Punishment/InstantPunishment.lean` already give
the exact unrestricted-behavior instant-profile criterion and the same fixed
singleton target from

`quittingPunishmentValue reward o <= s_o`

plus the identical no-join inequalities.  Proposition 10's profiles have the
instant root, so their existence at every error is an explicit witness for
that already characterized branch.

At the mathematical source level, `Literature.Simon2007.lemma3`
(`Literature/Simon2007.lean`) says that if `o` is abnormal then every other
singleton row, including `{k}`, pays `o` at least its min-max value.  If `o`
is normal, its min-max is already at most `s_o`.  Thus in either case

`chi_o <= max(s_o,r({k})_o)`,

and the raw hypothesis `r({k})_o<=s_o` implies `chi_o<=s_o`.  Combined with
the raw no-join rows, this is precisely the instant-punishment existence
criterion.  So Proposition 10 does not enlarge the known solved class.

There is one formal-status distinction worth preserving.  The literature
file defines its own `MinMaxQuit` on its paper-facing quitting-game model;
the production file defines `quittingPunishmentValue`.  I found no named
checked adapter identifying these two objects for arbitrary production reward
data, and production does not import the Literature lane.  Hence the statement
that Simon supplies the raw-to-IR implication is a correct ordinary
mathematics/source comparison, not itself a checked production theorem under
the named imports.  This does not rescue novelty for an export, but it means
one should not describe the raw two-row adapter as already proved in
production Lean.

What remains genuinely useful is the explicit nonstationary punishment law
and transparent quantitative rate `debt<=Delta/L`.  Neither named production
declaration states that particular witness or rate.  That is a reusable
internal lemma, but the novelty gate for a new special-case existence export
still fails.

## Review conclusion

The unrestricted-deviation mathematics, raw inequalities, `Delta/L` upper
bound, observation/agency semantics, and literal-target consumer all check.
This file supplies the requested second independent mathematical review.  It
does not remove the independent novelty failure, and it does not certify a
Lean adapter from the raw hypotheses.
