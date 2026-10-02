# The literal fullCoreMatrix singleton fibre is a Never-equilibrium chamber

**Identity:** `CODEX_NEGATIVE_CERTIFICATE`  
**Status:** exact application of an existing checked theorem; search
normalization, not a new export result  
**Conjecture impact:** excludes every nonsingleton completion of the literal
`fullCoreMatrix` singleton rows from the Fin4 counterexample search

## Question

The checked matrix `FourPointCrossedRowsNoCyclicSign.fullCoreMatrix` has full
normal core, is standard-Q and nonhomogeneous, and has no relabelled cyclic
open-sign skeleton.  Does fixing it as the four literal singleton reward rows
give a principled next negative-certificate family after the Candidate C and
C172 exclusions?

No.  Its diagonal is zero.  Therefore perpetual Continue is already an exact
uniform equilibrium for every completion of all 44 nonsingleton reward
coordinates.  The sign barrier concerns a normalized singleton packet; it
does not stop this literal Never-boundary equilibrium.

## Exact class

Players are `0,1,2,3`.  Fix only

```text
r({0}) = ( 0,  1, -1, -1),
r({1}) = (-1,  0,  3,  1),
r({2}) = ( 1, -1,  0,  1),
r({3}) = ( 1,  1, -1,  0).
```

These are the columns of `fullCoreMatrix`.  Every reward coordinate at a
coalition of size at least two is arbitrary.  There are `60-16=44` such
coordinates.

More generally, the proof needs only

```text
r_i({i}) <= 0  for every player i.
```

## Theorem

For every finite quitting reward table satisfying the preceding solo-self
inequalities, the profile in which every player Continues forever is an exact
terminal Nash profile against every unilateral behavioral replacement.  Its
payoff is zero, and zero is a uniform-equilibrium payoff.  Consequently the
terminal exploitability infimum is zero.

## Proof

Under the prescribed profile no coalition ever Quits, so terminal payoff is
zero.  Fix a player `i` and replace only its strategy by an arbitrary
randomized history-dependent behavioral strategy, including Never or a clock
with unbounded support.  Every opponent still Continues at every date.

If the deviator never Quits, its terminal payoff is zero.  If it Quits at any
finite date, it Quits alone and receives `r_i({i})<=0`.  A randomized stopping
law is a probability mixture of these two types of outcome, so its expected
terminal payoff is at most zero.  Thus no unilateral behavioral replacement
improves on prescribed payoff zero.

The finite-horizon statement is equally direct.  Before any deviation stop,
the stage payoff is zero.  After a finite unilateral stop, the deviator's
absorbing payoff is `r_i({i})<=0`; Never gives zero.  Hence the same perpetual-
Continue profile is an exact Nash equilibrium of every finite average horizon
and delivers the fixed vector zero exactly.  It is therefore a uniform
equilibrium without any limiting selection.

For the literal `fullCoreMatrix` fibre, the checked theorem
`fullCoreMatrix_diagonal` supplies `r_i({i})=0` for every player, so every
deviation actually gives the deviator exactly zero.

## Boundary and strategy-class audit

* **All-Never boundary:** this is the producing profile, not a missing escape
  case.
* **Stationary:** the zero-hazard stationary root is exact.
* **Periodic:** no periodic search is needed; the stationary witness is already
  exact.
* **Persistent and deadline profiles:** they cannot restore a positive gap
  after one exact profile has zero unrestricted debt.
* **Late clocks and Never deviations:** explicitly covered because opponents
  never stop; a finite deviator stop always produces the same singleton, and
  Never produces zero.
* **Arbitrary nonsingleton rewards:** unreachable after a unilateral deviation
  from perpetual Continue, so all 44 coordinates are irrelevant rather than
  merely bounded errors.

The numerical battery on zero, first-member, and average-member
nonsingleton completions also returned the zero-hazard stationary witness,
but that experiment is not used in the proof.

## Source audit and checked consumer

The matrix and literal singleton realization were inspected in

```text
UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/
  FullSupportLCPSignBarrier.lean
```

Relevant declarations are:

* `fullCoreMatrix_diagonal`;
* `fullCoreReward_singleton`;
* `fullCoreMatrix_not_exists_relabelledCyclicOpenSignSkeleton`;
* `fullCoreMatrix_standardQ`; and
* `fullSupportPacket_standardQ_nonhomogeneous_but_not_cyclic`.

The narrow duplicate search found the exact theorem already present in
`UniformEquilibrium/Quitting/Punishment/ZeroSoloDisjunct.lean`:

```text
IsQuittingZeroSolo
isZeroAsymptoticNash_quittingAlwaysContinue_of_zeroSolo
quittingGame_isUniformEquilibriumPayoff_zero_of_zeroSolo
```

The complete Never-boundary semantic pair is also checked as

```text
quittingNeverBoundarySemanticPair reward
  = (0, fun i => max 0 (r_i({i})))
```

by `quittingTerminalSemanticPair_elementaryCap_never` in
`UniformEquilibrium/Quitting/Terminal/TailCompression/ElementaryTailSemanticReduction.lean`.
Under `r_i({i})<=0`, this pair is `(0,0)`, so the literal all-Continue profile
has zero terminal debt.  The standard exact-terminal-Nash consumer
`quittingGame_isUniformEquilibriumPayoff_of_terminalNash_exact` in
`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`
then yields the same uniform-payoff conclusion as the direct finite-horizon
proof.

## Search consequence

The zero diagonal in `fullCoreMatrix` is appropriate for a normalized solo
matrix but fatal when those entries are used as literal quitting rewards:
Never has payoff zero, so nonpositive own singleton rewards make the boundary
profile an equilibrium.

A nontrivial successor family must lift the normalized matrix by solo
baselines,

```text
r_i({j}) = s_i + fullCoreMatrix(i,j),
```

with at least one `s_i>0`.  This preserves the normalized singleton matrix
while crossing the immediate Never-equilibrium wall.  Such a lifted family
must then be screened exactly for every stationary cube face, persistent
base, deadline threat, pair schedule, and limiting/late-clock singleton
construction.  Merely citing the standard-Q or no-cyclic-sign theorem is not
a behavioral exclusion.

## Nonclaims

This note does not exclude positive-baseline lifts of `fullCoreMatrix`, prove
completeness of any periodic class, or decide the full Fin4 conjecture.  It
shows only that the literal zero-diagonal singleton fibre is an exact positive
UE chamber and therefore cannot host a negative certificate.
