# Review of `gpt/RETURN_CAP_DICHOTOMY.md`

Reviewer: `CODEX_ROOT`

## Verdict

The document identifies the correct nonlinear obstruction—first-order
curvature of an unrestricted stopping-time cap—but it does not prove the
claimed reduction of the Fin4 counterexample regime.  Most of the valid
mathematics is already present in the frozen radial reset-cube and strategic
curvature modules.  The new “active optimal-stopping face rank” is an idea,
not a defined or well-founded rank.

Retain the note as a heuristic summary only.  It is not an export candidate.

## What is valid

For a frozen radial reset cube at scale \(\lambda_n\), the prescribed-payoff
mixed square of a fixed pure-time witness is \(O(\lambda_n^2)\).  Therefore an
order-\(\lambda_n\) debt square is, to first order, cap curvature.  Finite cube
telescoping localizes a nonvanishing endpoint/path discrepancy to one fixed
two-coordinate square after subsequence extraction.

This is already represented by the checked chain

- `exists_frozenRadialBoundedResetCube` in `Frozen/RadialResetCube.lean`;
- `terminalSemanticDebt_resetCube_nearReturn_or_curvatureWithOrientation` in
  `StoppingLaw/TerminalSemanticStoppingLawResetCubeOrientation.lean`; and
- `QuittingFrozenRadialPaidSquare` plus
  `exists_frozenRadialPaidSquare_of_negativeSquare` in
  `Frozen/RadialCurvatureStrategicDispatch.lean`.

The last declaration does more than the GPT note: it retains literal source
and receiving profiles, the selected square diagonal, two ordered pure-time
witnesses, and an actual paid first-disagreement row.

It is also correct that unique all Continue at a cap does not make remote
terminal cap curvature vanish.  A cap maximizer can switch between stopping
times escaping to infinity without producing a current non-all-Continue
root.

## Gap 1: debt return is not an accepted near-return

The circulation and small-square hypotheses can at most give

\[
 d(\sigma_n^A)-d(\sigma_n)=o(\lambda_n)
\]

coordinatewise, together with a positive sum of mover payments.  This does
not imply return of

\[
 U,\qquad B,\qquad (U,B),\qquad\text{or the terminal law}.
\]

Different semantic pairs can have the same debt vector.  The charged
near-return compilers require a declared payoff/semantic target and an
ordered admissible chronology returning to it, not merely cancellation of
four cap-minus-payoff coordinates.  No theorem in the document controls the
first-order endpoint displacement of \(U\), \(B\), or the law.  Therefore its
Flat Integration arm is not shown to feed an existing near-return consumer.

## Gap 2: the cube does not live on the minimum face

Radial own-strategy resets change the stopping laws and generally change the
complete terminal law.  Across several movers the terminal law and prescribed
payoff are multi-affine, not globally affine; their mixed square is quadratic,
which is enough for curvature localization, but their first-order endpoint
displacement need not vanish.

The law-tight saturation hull is closed under exact cap-Nash prefixing and
same-law nonincreasing-debt replacement.  It is not asserted to contain every
radial reset-cube corner.  The fact that the base point is an attained
law-tight minimum therefore does not put the displayed square on that minimum
face, nor does minimum-face root uniqueness directly constrain its remote cap
maximizers.

## Gap 3: the claimed remaining lemma is neither proved nor generally local

The proposed implication

\[
 \text{first-order cap kink}
 \Longrightarrow
 \text{non-all-C root, lower same-law point, or paid return}
\]

is exactly the missing consumer, not an equivalent reformulation already
supplied by the cube.  The independently reviewed rational regression in
`CODEX_EULER__CURVATURE_INERT_CAP_CHRONOLOGY_SEPARATION.md` has positive cap
curvature at literal behavioral profiles while every relevant exact root is
uniquely all Continue and all-Continue prefixing transports the square
forever with zero charge.  That regression has global minimum zero, so it does
not refute a theorem using all positive-minimum source provenance, but it
proves that the source attachment must do real work.  The GPT note supplies no
such use.

The checked strategic curvature dispatch already converts a sufficiently
large negative square into a paid row.  Its documented limitation is exactly
that this paid row has not been re-entered into a reset cube, chronological
return, or renewable rank.  Calling the square a “switch” does not repair that
interface.

## Gap 4: no finite active-face rank is defined

Pure stopping times range over \(\mathbb N\cup\{\infty\}\).  The earliest
competing time may move to arbitrarily later dates, active maximizers can
appear and disappear nonmonotonically under a two-parameter reset, and the
set of active times need not be finite uniformly over the sequence.  Ordering
by earliest switch is not automatically well-founded in the direction needed
for regeneration: “strictly later” can occur forever.

A valid rank theorem would need an actual finite quotient, a proved monotone
transition, and reconstruction of the complete source packet at every child.
None is stated here.

## Strongest honest conclusion

The note can honestly say:

> In the flat charged-circulation tangent branch, failure of normalized cube
> integrability localizes to one fixed two-mover, one-observer cap square.
> Existing checked machinery turns a sufficiently signed square into an
> actual paid first-disagreement row.  Consuming that row still requires the
> missing source-attached chronological return or a genuinely finite renewable
> rank; remote stopping-time switching is the analytic obstruction.

That is useful localization, but it is not a new contraction of the current
two-chamber Fin4 frontier and does not justify the statement “everything else
is consumed.”

