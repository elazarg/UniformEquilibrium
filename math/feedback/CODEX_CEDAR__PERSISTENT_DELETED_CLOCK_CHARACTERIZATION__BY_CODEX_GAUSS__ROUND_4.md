# Fourth review of Persistent Deleted-Clock Characterization by `CODEX_GAUSS`

Reviewed note:
[`CODEX_CEDAR__PERSISTENT_DELETED_CLOCK_CHARACTERIZATION.md`](../notes/CODEX_CEDAR__PERSISTENT_DELETED_CLOCK_CHARACTERIZATION.md),
Section 6, Proposition 6.

## Verdict

**VALID ordinary mathematics, with the stated provenance limitation.**  A
countable concatenation of the selected literal finite product-root lists is
an executable root chronology.  Two divergent labelled raw hazards give all
joint and one-player-deleted suffix survival limits, while the checked
`exactOfRoots` construction gives exact reached-tail recursion and identically
zero local prescribed/direct-debt defects.  I found no issue in either atom
application.

This does **not** transport the original atom comparison or vanishing reset
debt to those reached tails.  In particular it does not produce a
`QuittingChronologicalDebtShadowingCertificate` with small initial candidate
debt.  A useful sharpening is that no additional forcing estimate is missing
on the exact-data route: the zero prescribed/direct defects and zero generated
secant already make both forcing fields exact.  Among the full certificate
fields, only `initial_debt_le` remains after the clock conclusion.

I did not run Lean and assign no `L`, `A`, or `C` seal.

## Literal concatenation and reindexing

Each block `L_k` is a finite list of maps `I -> PMF Bool`.  Under `(6.1)` each
selected block carrying a fixed positive quota is nonempty.  Its cumulative
endpoints therefore form a strictly increasing sequence tending to infinity,
so the block lists have one unambiguous consecutive enumeration

```text
roots : Nat -> I -> PMF Bool.
```

Reindexing a nonnegative marginal series across this partition is exact:

```text
sum_t p_(t,a) = sum_k sum_(local t in L_k) p_(k,t,a),
```

and similarly for `b`.  Thus `(6.1)` makes both labels persistent.  Cedar
Proposition 1 then gives, for every starting time, vanishing joint survival
and vanishing survival after deletion of any one player.  No blockwise
simultaneous activity is required.

## Exact reached-tail data

For any literal root sequence, the checked definition
`QuittingChronologicalDebtData.exactOfRoots`
(`UniformEquilibrium/Quitting/Debt/Dynamic/ExactChronologicalData.lean`) uses
the terminal semantic pair of the actual infinite root-sequence suffix at
each time.  Therefore its `semanticPair_eq_prefix` identity is the genuine
reached-tail recursion of the concatenated sequence, not an equality with an
independently selected frozen source.

The named checked identities

```text
exactOfRoots_prescribedDefect
exactOfRoots_directDebtDefect
```

are literally zero at every global time.  They remain zero at block seams
because the candidate successor pair is defined to be the semantic pair of
the actual next suffix.  No frozen continuation is inserted there.

The same definition also sets the secant to zero and has exact generated
secant identity, nonnegative actual terminal debt, and canonical boundedness.
None of this bounds the initial debt by a requested accuracy: that debt is
the actual terminal exploitability of the newly concatenated root profile.
The cited
`PositiveSlopeCausalRegression.exact_source_has_zero_forcing_but_unit_initialDebt`
(`UniformEquilibrium/Diagnostics/Quitting/Regression/SourceMatchedExposureNoGo.lean`)
is an exact checked warning against conflating zero local defects with the
needed small-debt producer.

## Atom applications

1. With two distinct positive-debt movers, Corollary 3A gives a finite prefix
   of a literal complete source/replacement-side profile with a fixed positive
   quota for the chosen mover.  Alternating the two mover prefixes gives the
   two divergent global marginal series required by `(6.1)`.  The other
   coordinates in each literal product root may vary arbitrarily and do not
   spoil either divergence.
2. Off the mover-singleton survivor, reviewed Proposition 5 gives one literal
   half-mixed complete profile whose finite prefix contains fixed quotas for
   both the mover and one opponent label.  Concatenating those prefixes gives
   `(6.1)` directly.  In the finite-response mover-singleton rectangle branch,
   the same half-mixed profile contains the mover quota and the distinct pure-
   time observer's hazard-one quota.

Both conclusions concern the roots actually concatenated, so the survival
fields are genuine executable chronology rather than frozen-source clock
estimates.

## Exact remaining obligation

The distinction at the end of Proposition 6 is essential.  The atom/debt
claims were proved for semantic pairs of the original complete profiles.
After concatenation, `exactOfRoots` recomputes different continuation payoffs
and best-response caps.  Its zero defects are tautologically exact for those
new values/debts, but the new initial debt can be large and the original
signed terminal atom need not survive the suffix replacement.  The open
conditioned-reprojection theorem must therefore show that the actual terminal
exploitability of this already executable clock chronology is small.  It no
longer needs to manufacture its survival or forcing fields outside the
identified mover-singleton prescribed/Never branch.  The original atom and
forcing provenance may be useful evidence for the small-debt estimate, but it
is not an additional output required by the exact-data consumer.
