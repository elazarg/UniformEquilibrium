# Fin4 vertical-toll review notebook

Author: `CODEX_HEAVISIDE`

## Current status

Independent audit completed.  The quantitative core of
`CODEX_MAXWELL__FIN4_ACTIVE_PASSPORT_VERTICAL_RETURN_TOLL.md` is sound:
fixed unconditional mass on a nonempty reached atom gives the same conditional
root-absorption floor; the Fin4 coordinatewise-to-total conversion costs the
factor four; and the checked successor first-exit theorem gives the stated
`c*rho/(16*C)` aggregate-error toll for arbitrary finite length.

The note needs a scope repair before it can be called fully sound as written.
The analytic argument applies to all fifteen pure nonempty roots, but only the
source-selected forced pair and its actually profitable endpoint comparison
carry the fixed historical marked atom and positive actual-gain provenance.
Changing to an arbitrary other pure corner generally changes the terminal law
and may lose the positive gain.  Thus the fifteen-corner result is a local
root no-go, not fifteen source-attached active-passport no-gos.

I do not recommend export.  The main estimate and arbitrary-length first-exit
toll are already checked in Lean and archived in
`formalized/STRICT_ALLCONTINUE_BASIN_LINEAR_ABSORPTION_DEFECT.md`.  The new
composition is a useful corollary and rules out a natural successor-linked
repair family, but it is not exhaustive and leaves both non-successor seams
and the diffuse positive-aggregate-error regime.  It therefore does not make
the strict boundary change required by `exports/README.md`.

## Self-contained question checked

For a no-uniform-payoff `Fin 4` reward table, let `K,N,c,C,rho` be supplied by
`exists_finFour_minimumFiber_linearAbsorptionDefect_of_no_uniformPayoff`.
Suppose an actual marked history has a fixed nonempty coalition `A` with
unconditional stage mass at least `m0>0`.  If its conditional live root is an
`epsilon`-root Nash equilibrium against a displayed tail in `N`, must
`epsilon >= c*m0/4`?  If a finite exact-successor word starts at a tail within
`rho/2` of `K` and ends at a displayed tail where the marked root has error
less than `c*m0/4`, must its aggregate declared error be at least
`c*rho/(16*C)`?

Both answers are yes, provided the word's declared row errors are nonnegative
(or, equivalently here, each `IsεQuittingRootNash` hypothesis is used to
derive their nonnegativity).

## Calculation audit

The checked factorization gives

```text
stageMass(A) = liveMass * rootCoalitionMass(A).
```

Since `0 <= rootCoalitionMass(A)` and `liveMass <= 1`,

```text
m0 <= stageMass(A) <= rootCoalitionMass(A) <= absorption(root),
```

where the last inequality uses `A.Nonempty`.  The local basin inequality and
the checked total-defect conversion then give

```text
c*m0 <= c*absorption(root) <= totalDefect <= 4*epsilon.
```

For the path, use the checked orientation

```text
value(t+1) = Succ(value(t), root(t)),
```

so `value(0)` is the deep terminal continuation and `value(L)` is the outward
head displayed to the separate marked root.  If that marked root has error
below `c*m0/4`, its displayed tail `value(L)` is outside `N`.  The checked
first-exit theorem with the witness `time=L` yields

```text
c*rho/(4*C*card(Fin 4)) = c*rho/(16*C)
  <= sum_{t<L} error(t).
```

The proof covers `L=0` as an inconsistent boundary case and does not depend on
an a priori bound on `L`.

## Sources inspected

- `exists_finFour_minimumFiber_linearAbsorptionDefect_of_no_uniformPayoff` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinFourMinimumFiberLinearAbsorptionDefect.lean`;
- `successorPath_mem_and_absorptionSum_le_of_linearDefect` and
  `sum_error_ge_of_successorPath_exists_not_mem_linearBasin` in
  `UniformEquilibrium/Quitting/Paths/StrictAllContinueBasinSuccessorPath.lean`;
- `quittingRootTotalNashDefect_le_card_mul_of_isεQuittingRootNash` in
  `UniformEquilibrium/Quitting/Root/NashDefect.lean`;
- `quittingRootCoalitionMass_le_absorptionMass_of_nonempty` in
  `UniformEquilibrium/Quitting/Cycles/CyclicGreenDebt.lean`;
- `quittingStageCoalitionMass_eq_liveMass_mul_rootCoalitionMass` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPlateauIncidence.lean`;
- the actual Fin4 adapter `normalizedDecoratedFamily`, compact selection, and
  source correspondences in
  `Research/Quitting/FinFourProducerAtlas/NormalizedReturn.lean`;
- the exact post-date spine, fixed mass, and paid endpoint facts in
  `Research/Quitting/FinFourProducerAtlas/MinimumReturnForcedPair.lean`; and
- the already formalized underlying theorem in
  `formalized/STRICT_ALLCONTINUE_BASIN_LINEAR_ABSORPTION_DEFECT.md`.

## Remaining exact question

Can the surviving diffuse regime with rowwise errors tending to zero but
aggregate error bounded below be converted into an exact source-matched
charge or a renewable finite-rank transition?  The vertical toll itself does
not perform that conversion.
