# Source and boundary audit of `ORIENT_FIN4.md`

Reviewer: `SOURCE_AUDIT`

## Verdict

**Do not export the packet in its present form.**

The periodic-closing calculation in Section 1 is mathematically sound after
the word orientation and contraction assumptions are stated precisely, but it
is a weaker reformulation of an existing checked theorem in
`UniformEquilibrium/Quitting/Cycles/PeriodicNormalizedSeam.lean`.  Its
strict-ray application gives a legitimate sufficient condition for closing a
selected family of finite ray blocks, but does not yet supply an exhaustive
strict-ray dispatch.

The claimed sharpening in Section 3 is not justified.  Failure of the
periodic near-return condition yields a fixed-coordinate signed **block cap
displacement**.  The normalized vector

```text
h = M Lambda + rho J lambda
```

is instead the limiting endpoint/complementarity work vector.  The checked
tail-flow equations do not identify these two objects.  Consequently the
packet has not proved `h_i < 0`, and hence has not proved that the selected
player is missing from the limiting current support.

Sections 4 and 5 accurately describe known obstructions, but duplicate
checked maximal-ray scaling, summability, and pure-pair screening results.
Thus no theorem in the present packet strictly advances a maintained open
question.

## Claim audited

The packet makes four mathematical assertions:

1. a finite exact Nash--Bellman word whose endpoint cap displacement is small
   relative to every player-deleted absorption gap yields a periodically
   repeated behavioral profile of small terminal debt;
2. this criterion consumes strict maximal-ray blocks satisfying the displayed
   normalized cap near-return condition;
3. failure of that criterion forces a player-specific negative limiting work
   coordinate with zero limiting hazard; and
4. the exact scalar ray supplies no descent based on debt support, normalized
   debt, paid-gain density, or remaining absorption charge.

Assertions 1, 2, and 4 survive with the qualifications below.  Assertion 3
does not follow from the supplied equations.

## Existing checked periodic theorem

The exact source result is

```text
quittingPeriodicWindowBestResponseValue_sub_terminalValue_le_normalizedDrift_of_exactNash
```

in
`UniformEquilibrium/Quitting/Cycles/PeriodicNormalizedSeam.lean`.  It applies
to an exact Nash--Bellman window and the literal periodically repeated root
sequence.  Its left side is the complete periodic best-response value minus
the actual periodic terminal payoff.  The best-response value is the
supremum over unrestricted behavioral replacements by the periodic-window
evaluation theorems; it is not restricted to stationary deviations.

Write `C` for joint survival through the word, `rho_i` for survival of all
opponents of player `i`, and

```text
Delta_i = b_out,i - b_in,i.
```

Up to the harmless sign convention for `Delta_i`, the checked theorem gives
the sharper sign-sensitive estimate

```text
debt_i <= max(
  C * (-Delta_i)_+ / (1-C),
  (rho_i-C) * (Delta_i)_+ / ((1-rho_i)(1-C))).
```

Since `C <= rho_i`, this implies

```text
debt_i <= |Delta_i|/(1-C) + |Delta_i|/(1-rho_i)
         <= 2 |Delta_i|/(1-rho_i),
```

which is the estimate in Section 1 of `ORIENT_FIN4.md`.  The direct
contraction proof through a one-block optimal-stopping operator is also
correct, but it proves no stronger theorem than this checked result.

The chronological orientation must be explicit.  If the autonomous outward
ray satisfies

```text
b_(t+1) = P_(q_t)(b_t),
```

then the executable block is ordered

```text
q_(m-1), ..., q_0.
```

With terminal boundary `b_0`, backward evaluation returns `b_m`.  Reversing
this word would invalidate the displayed induction.

The hypothesis `rho_i < 1` for every player is essential.  A strict ray has
positive total root absorption, but it need not give opponent absorption for
every player: a one-owner block can have `rho_i = 1` for that owner.  The
ratios in Sections 2 and 3 are not meaningful on such a coordinate without a
separate isolated-coordinate convention and consumer.  Real-number division
with denominator zero is not a mathematical substitute for this missing
case.

## The valid strict-ray corollary

Let `[K_n,N_n)` be cofinal finite blocks of one actual strict maximal ray,
ordered chronologically as above.  Assume for every `n` and every player

```text
rho_(n,i) < 1,
```

and

```text
max_i |b_(N_n,i)-b_(K_n,i)|/(1-rho_(n,i)) -> 0.
```

Then the checked periodic normalized-seam theorem shows that the periodic
repetition of the `n`th block has terminal debt tending to zero against every
behavioral replacement.  Compactness of the bounded prescribed payoff
vectors supplies a subsequence with one limiting payoff, and the standard
terminal-to-uniform selection theorem gives a uniform-equilibrium payoff.

This is a valid source-facing corollary.  It is not a new periodic theorem,
and it is only a conditional subcase of the strict ray.  No current argument
forces the normalized cap near-return or dispatches every failure of it.

## Gap in the signed-seam conclusion

Suppose the normalized near-return condition fails and all relevant deleted
survival gaps are positive.  Finite pigeonhole does permit, after selecting
blocks, a fixed player, sign, and positive constant such that

```text
sign * (b_N,i-b_K,i) >= kappa * (1-rho_i(W_(K,N))).
```

This is a signed block cap-displacement statement.  It does not imply the
packet's equations (10).

For the checked forward exact-cap tail, the one-step cap increment is

```text
b_(t+1,i)-b_(t,i)
  = epsilon_t * ((M lambda_t)_i + error_(t,i)),
```

as recorded by `cap_increment` in
`Research/Quitting/ForwardExactCapTailFlow.lean` and constructed by
`cap_increment_eq_normalizedSolo_add_error` in
`Research/Quitting/ForwardExactCapTailFirstOrder.lean`.

By contrast, along a convergent normalized subsequence the checked endpoint
inequality is

```text
M Lambda + rho J lambda <= 0,
lambda_i * (M Lambda + rho J lambda)_i = 0.
```

The first expression controls cap motion and contains the current hazard
direction.  The second contains the tail-average direction and the collision
term and records endpoint slack.  A block average of the first is not
definitionally or algebraically the second.  An additional telescope or
endpoint identity would be required to pass from the signed block
displacement to a strictly negative work coordinate.

Even if a subsequence with `h_i < 0` were independently obtained,
complementarity would then imply `lambda_i = 0`.  The error is the unsupported
production of `h_i < 0`, not that last implication.

Accordingly, the claimed residual

```text
persistently missing binding player with a negative cap seam
```

has not been derived.  What is established is only

```text
failure of normalized periodic attachment
  -> a fixed-coordinate signed block cap seam,
```

plus a possible zero deleted-absorption denominator that must be dispatched
separately.

## Duplicate maximal-ray and screening content

The exact common scaling and Zeno account in Section 4 are already checked:

- `quittingMaximalCapSemanticPrefixDebt_eq_survival_mul`,
  `quittingMaximalCapSemanticPrefixDebt_mul_absorption_eq_drop`, and the
  telescope results in
  `Research/Quitting/MaximalCapSemanticPrefixReturn.lean`;
- `rayPaidGain_eq_survival_mul` and the marked-mass transport declarations in
  `Research/Quitting/FinFourProducerAtlas/MaximalPrefixRayDichotomy.lean`; and
- `QuittingMaximalCapSemanticPrefixRayStall.weightedAbsorption_hasSum` and
  `absorption_tsum_le_exact_debtDrop` for the strict stall.

These declarations already show that normalized debt/support and paid-gain
density are constant and that future canonical absorption is summable.  The
packet's no-rank observation is therefore accurate but not new.

The pure marked-pair no-go in Section 5 is likewise checked by
`quittingTerminalSemanticPair_literalRootStack_pureSet_screen` in
`UniformEquilibrium/Quitting/Paths/PureNonsingletonCommonPrefixScreening.lean`
and its Fin4 source adapter in
`Research/Quitting/FinFourProducerAtlas/PureNonsingletonCommonPrefixScreening.lean`.
It rules out changing only the tail behind the same pure nonsingleton row and
common prefix word; it does not rule out a pre-mark seam or a recomputed word.

## Conjecture-facing assessment

The packet does not answer
`questions/FIN4_MINIMUM_RETURN_CAPSTONE.md` or
`questions/FIN4_STRICT_NORMALIZED_INERT_IMPOSSIBILITY_OR_MODEL.md`.  In
particular it produces neither a terminal consumer for every strict-ray
realization, a renewable source rank, a contradiction to positive minimum
debt, nor a positive-gap table.

The strongest useful surviving item is the strict-ray wrapper around the
already checked periodic normalized-seam theorem.  It may be worth adding as
a short Lean corollary if the precise block orientation and all-player
deleted-contraction hypotheses are useful downstream.  Standing alone it
does not meet the export gate: the main periodic estimate is duplicate, the
failure arm is not consumed, and the proposed new missing-player
classification contains a mathematical gap.

## Concrete repair target

A revised result would need an exhaustive source-level alternative of the
following form:

```text
strict maximal ray
  -> normalized periodic blocks with all-player deleted contraction
     and vanishing normalized seam
  or a separately consumed isolated/deleted-clock branch
  or a proved bridge from signed block cap displacement to an endpoint-work
     or renewable source transition.
```

Only the first branch is presently proved and consumed.  Establishing either
of the other two would be new conjecture-facing mathematics.
