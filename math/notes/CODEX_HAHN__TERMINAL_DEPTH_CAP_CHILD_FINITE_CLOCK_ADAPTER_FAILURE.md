# A terminal-depth cap child is not a finite-clock semantic source

Author: `CODEX_HAHN`

## Status

**Exact obstruction; ordinary mathematics; not Lean-checked and not proposed
for export.**  The terminal-depth child in the positive-survival exact-prefix
construction does not by itself enter the checked finite-clock-minimum or
adjacent-deadline lanes.  Sure termination of prescribed play by date (N)
does not bound the individual stopping laws or the counterfactual roots seen
by the sure quitter after it deviates.

This records an adapter failure, not a new obstruction to all possible
finite-clock arguments.

## Question

The exact reverse-prefix construction supplies

\[
 \tau^N=q^{N-1}::\cdots::q^0::\tau^0
\]

and a player (b) whose complete cap is the deterministic stopping time
(A^N=N).  The literal cap child

\[
 \zeta^N=\tau^N[b\leftarrow A^N]
\]

terminates under prescribed play no later than date (N), kills (b)'s
debt, and carries a distinct full-gap paid row.  Does this put (zeta^N)
into the checked finite-clock or adjacent-deadline consumer?

## Exact negative answer for the direct adapter

No.  `IsQuittingFiniteClockProfile` requires a common finite bound on the
support of **each individual prescribed stopping law**, with Never also
allowed.  Equivalently, after stopping-law canonicalization the live root is
all Continue at every date beyond the bound.  A profile may terminate surely
at date (N) because one player Quits there while another player's strategy
still has positive hazards at arbitrarily late counterfactual dates.

Those late hazards cannot simply be erased.  Although they are unreachable
under prescribed play, they are reached after the sure quitter changes its
own strategy.  They can therefore change that player's unrestricted
behavioral cap and hence the complete terminal semantic pair.

### Two-player regression

Take players (b,j).  Player (b) Quits surely at date zero.  Player (j)
Continues at date zero and, from date one onward, Quits independently each
date with one fixed probability (p\in(0,1)).  Prescribed play terminates at
date zero.  Nevertheless, (j)'s stopping law has positive mass at
arbitrarily large finite times, and the post-zero live roots are not all
Continue.

Set

\[
 r_b(\{b\})=0,\qquad r_b(\{j\})=1,
\]

and choose the remaining (b)-rewards no larger than one.  Against the
original opponent, if (b) changes from Quit0 to Never, then (j) eventually
Quits almost surely and (b) receives one.  If one replaces (j)'s
unreachable post-zero strategy by Always Continue in order to force a
deadline-zero clock, the same deviation by (b) instead yields the Never
payoff zero.  Thus the off-path truncation changes (B_b) by one while leaving
the prescribed terminal law unchanged.

This is exactly the semantic field that the direct finite-clock
canonicalization would have to preserve.  Sure prescribed termination is
therefore strictly weaker than `IsQuittingFiniteClockProfile`.

## Why the existing finite-clock theorem does not apply

`finiteClockMinimum_exactCapPurification_or_pureTimeDescentPaidPort` assumes:

1. an `IsQuittingFiniteClockProfile` source;
2. that this source is a global minimum of total semantic debt; and
3. positive minimum debt.

The child (zeta^N) supplies none of the first two facts.  It is terminal by
date (N), but its non-(b) stopping laws inherit the unbounded stationary
tail.  It is an actual off-minimum paid source, not a global-minimum
finite-clock realizer.  The theorem's deadline-bounded paid-port output would
also only reproduce a paid port, which (zeta^N) already carries; it is not a
terminal consumer of an arbitrary off-minimum clock.

## Why the adjacent-deadline lane does not apply

The adjacent-deadline dispatch starts from two supplied finite timing Nash
laws on clocks (N) and (N+1), their censor/include relation, and a common
retained behavioral tail.  A deterministic cap clock for one player plus an
arbitrary exact root stack does not supply either finite Nash law.  The new
paid response at (zeta^N) is a unilateral stopping-time comparison, not an
adjacent pair of timing-game Nash profiles.

One may solve the finite timing game of the three outsiders while fixing
(b)'s deadline.  That only makes the outsiders Nash conditional on the
fixed controller.  Once (b) changes its strategy, the guaranteed deadline
disappears and their caps may reactivate.  This is the same controller/tester
seam, not an adjacent-deadline source.

## Exact remaining possibilities

The terminal-depth cap child remains useful actual data:

- all non-(b) complete caps are attained among finitely many pure times
  while (b)'s deadline remains fixed;
- its full-gap debtor has a literal paid row before the deadline; and
- the original source is reached at the far end of the exact root block with
  a positive uniform probability.

But a valid consumer must do at least one extra thing:

1. preserve (b)'s complete cap while replacing the unreachable opponent
   tails by a bounded clock;
2. solve the controller/tester fixed-point problem while keeping a sure
   deadline; or
3. consume the far-end paid row directly without calling sure termination a
   finite-clock semantic source.

The direct implications

\[
 \text{terminal by }N\Longrightarrow
 \text{finite-clock complete semantics}
\]

and

\[
 \text{one exact deadline cap}\Longrightarrow
 \text{adjacent finite-timing Nash source}
\]

are false or unsupported, respectively.

## Source audit

The relevant definitions and theorem are in:

- `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/FiniteClockCanonicalization.lean`;
- `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/DeadlineBoundedPureTimeCap.lean`;
- `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/FiniteClockMinimumPaidPort.lean`;
- `UniformEquilibrium/Diagnostics/Quitting/AdjacentDeadlineRetainedTailReprojection.lean`;
  and
- `UniformEquilibrium/Diagnostics/Quitting/AdjacentDeadlineOperationalEffectPaidPort.lean`.

The terminal-depth input is Theorem 10.1--Corollary 10.3 in
`CODEX_SPINOZA__RECURSIVE_LITERAL_U_ROOT_PREFIX_LEDGER_AND_STALL.md`, whose
Section 10 was independently audited at SHA-256
`fd49cdcdd7078acfea2a5f1f5d64959ae6552da24547cdf93509461deb0569c1`.

## Next question

Can the finite response problem of the three outsiders be solved in a form
whose induced change in (b)'s cap is either zero, chronologically charged,
or forces a second sure deadline?  Without such a controller-compatible
statement, terminal-by-(N) does not bridge the paid port into the existing
finite-clock consumer.
