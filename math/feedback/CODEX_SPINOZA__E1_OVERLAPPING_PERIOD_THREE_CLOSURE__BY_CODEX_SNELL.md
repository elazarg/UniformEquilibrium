# Second review of the E1 overlapping period-three closure

Reviewer: `CODEX_SNELL`

Reviewed note:
[`CODEX_SPINOZA__E1_OVERLAPPING_PERIOD_THREE_CLOSURE.md`](../notes/CODEX_SPINOZA__E1_OVERLAPPING_PERIOD_THREE_CLOSURE.md)

Reviewed SHA-256:
`76242f7fd1599459eb3f9ce86cc5ba1a98f8dd9718e8313dab9bf8212a0fa08e`.

Verdict: **PASS.**  I independently reconstructed the twelve cleared
Quit-minus-Continue gaps, their hazard Jacobian, the base rational interval
certificate, and the all-60-coordinate reward-neighborhood certificate.  I
found no table, orientation, interval, contraction, structural-cylinder, or
compiler discrepancy.  In particular, the E1 table has the claimed exact
absorbing period-three Nash--Bellman word, and both the stated reward
neighborhood and the larger structural class inherit an unrestricted
terminal uniform-equilibrium payoff.

## Claim and probability mode checked

The claimed word has phase supports

```text
A0={1,2}, A1={0,1,3}, A2={0,2,3}.
```

The claim is not merely stationarity against stationary deviations.  It is
an exact phasewise one-root Nash--Bellman certificate with player-deleted
cycle contraction.  The named checked compiler then compares against every
unilateral behavioral deviation and returns
`IsUniformEquilibriumPayoff none` for the phase-zero terminal value.

## Independent polynomial reconstruction

I transcribed the fifteen displayed reward rows directly in bit-mask order
and, for each phase `t`, formed from the product Bernoulli law:

```text
I_t(i) = unconditional terminal contribution in phase t,
s_t    = probability everyone Continues in phase t,
Q_ti   = pure-Quit endpoint against the other three marginals,
A_ti   = nonempty-opponent contribution to the pure-Continue endpoint,
c_ti   = probability all three opponents Continue.
```

Writing `D=1-s_0*s_1*s_2`, direct expansion of the cyclic recursion gives

```text
W_t(i)=I_t(i)+s_t I_(t+1)(i)+s_t s_(t+1) I_(t+2)(i),
V_t(i)=W_t(i)/D,
F_ti=D*(Q_ti-A_ti)-c_ti W_(t+1)(i).
```

Thus `F_ti/D` is exactly pure Quit minus pure Continue, with the successor
phase oriented as in the checked root definition.  The active list in the
note contains precisely the eight positive hazard coordinates, and its four
inactive coordinates are the complement.  No phase or player equation is
missing.

## Exact interval recomputation

I implemented rational forward interval differentiation of the evaluation
graph above, independently of the author and of the first review.  All
decimal centers were parsed as exact rationals.  I used the displayed
`rho=10^-7`, the displayed integer matrix `M`, and `C=10^-12 M`.  The base
calculation gives:

```text
det(M) mod 1000003 = 990083,
D(X) = [0.917319861335..., 0.917320043748...],
max_i sup |K(X)_i-x0_i|/rho
  = 0.000019871401791472994... < 1/40000.
```

The maximum occurs in the seventh coordinate in the packet's variable
order.  The independently obtained inactive enclosures, in packet order,
are

```text
[-.476340224136..., -.476337486188...],
[-.292681974006..., -.292679378899...],
[-.306787573251..., -.306782686875...],
[-.373816796947..., -.373812592305...].
```

Their exact rational upper endpoints are all below `-29/100`.  The whole
hazard box is strictly inside `(0,1)^8`.

For the robustness claim I replaced each of the 60 reward coordinates by a
separate interval of radius `eta=1/50000000`, both in the center residual and
in the hazard interval Jacobian.  Ordinary interval evaluation deliberately
forgets correlations between repeated occurrences.  The exact-rational
result is

```text
max_i sup |K_r(X)_i-x0_i|/rho
  = 0.8231839440269948... < 5/6.
```

The four uniform inactive enclosures are

```text
[-.476340260829..., -.476337449495...],
[-.292682010699..., -.292679342206...],
[-.306787609944..., -.306782650182...],
[-.373816833640..., -.373812555612...].
```

Again their exact upper endpoints are below `-29/100`.  These calculations
reproduce the note's locators and strict rational comparisons.

## Existence and Nash signs

The Poincare--Miranda step is valid and avoids any dependence on a uniqueness
version of the interval Krawczyk theorem.  For each fixed reward table in the
box, the interval inclusion bounds the bracket in (3.3a) by a radius strictly
smaller than `rho` in every coordinate.  Hence the corresponding coordinate
of `C F_r` is negative on the lower face and positive on the upper face.
Poincare--Miranda gives a zero of `C F_r`; the modular determinant computation
makes `C` invertible, so this is a zero of `F_r`.

Since `D>0`, active numerator equality is exact pure-action indifference.
For an inactive player the prescribed hazard is zero and `F<0` says Quit is
strictly worse than Continue.  Root payoff is affine in that player's Boolean
marginal, so the endpoint test covers every randomized one-stage deviation,
not only the two pure endpoints.

## Absorption, deleted-player contraction, and checked consumer

Every phase contains at least two active players, and the box gives each
listed active player a strictly positive hazard.  Therefore every player
faces a positive opponent hazard in every phase.  Its fixed-opponents
Continue mass is consequently strictly below one, and so is its product over
the cycle.  This is stronger than the player-deleted contraction premise of
`isUniformEquilibriumPayoff_quittingCyclicTerminalValue_of_certificate` in
`UniformEquilibrium/Quitting/Cycles/PeriodicCompiler.lean`.

I inspected that declaration and `IsεQuittingRootNash` in
`UniformEquilibrium/Quitting/Root/FirstBranch.lean`.  The compiler uses the
policy recursion, exact root Nash at every phase, and the playerwise
contraction to compare with arbitrary behavioral unilateral deviations.  It
then invokes the exact terminal-Nash-to-uniform-payoff bridge.  Thus phase
zero has exactly the unrestricted terminal uniform-equilibrium-payoff status
claimed in the note.

## Sixty-coordinate neighborhood and structural cylinder

The reward-neighborhood proof is uniform without choosing a continuous root
branch: the same Miranda face signs, inactive signs, and hazard box apply
separately to every fixed table in the closed sup-norm box.  Contraction is
reward-independent.  Hence Theorem 4.1 follows from the recomputed bounds.

I also enumerated all on-path and unilateral-endpoint coalitions for the
three supports.  The four coordinates

```text
(0,{1,2,3}), (0,{0,1,2,3}),
(3,{0,1,2}), (3,{0,1,2,3})
```

never occur in the equilibrium values or in the relevant own-payoff
endpoints.  A history-dependent behavioral deviation changes only the
deviator's action at each phase; it cannot add a missing opponent to a phase
support.  Arbitrary overwrites of those four coordinates are therefore
legitimate.

For `r'_i=alpha_i r_i+beta_i`, direct substitution gives

```text
I'_t(i)=alpha_i I_t(i)+(1-s_t)beta_i,
V'_t(i)=alpha_i V_t(i)+beta_i.
```

Both endpoints receive the same additive constant and their difference is
multiplied by the positive `alpha_i`.  Player-deleted contraction ensures
absorption almost surely even after an arbitrary unilateral behavioral
deviation, so the additive constant is also valid for terminal payoffs.  The
order used in Theorem 5.3--fill the invisible coordinates, apply the small
box theorem, apply the positive affine changes, then overwrite the invisible
coordinates--is sound.

Finally, Proposition 5.4 correctly abstracts the proof.  Its face signs and
invertible preconditioner give an active zero, its inactive signs give local
Nash, and its opponent-hazard premise gives the compiler contraction.  For a
fixed rational hazard box the tensor-Bernstein sufficient inequalities are
finite strict rational linear inequalities in the reward coordinates because
the cleared gaps are linear in the reward table.

This PASS does not Lean-formalize the interval calculation, prove an
exhaustive Fin4 periodic-certificate theorem, or infer anything from failure
of a finite support search.
