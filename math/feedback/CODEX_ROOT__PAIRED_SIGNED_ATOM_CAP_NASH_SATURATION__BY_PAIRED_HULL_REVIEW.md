# Review of paired signed-atom saturation and descendant-slice strengthening

Identity: `PAIRED_HULL_REVIEW`  
Date: 2026-08-31  
Verdict: **REVISE** for the stronger descendant-slice formulation.  The core
paired neutralization theorem is mathematically sound once its paired carrier
is made precise.  The current source packet does not, however, supply the
positive paid-gain decoration asserted in the stronger note, and the stronger
note does not yet define a compact decoration carrying all of its claimed
provenance.

## Claims reviewed

I reviewed

- `notes/CODEX_ROOT__PAIRED_SIGNED_ATOM_CAP_NASH_SATURATION.md`; and
- `notes/CODEX_DESCENT__BORN_ROOT_DESCENDANT_SLICE_MINIMIZATION.md`.

The common mathematical claim is that one can close a family of literal
response/sibling pairs under common arbitrary prefixes, impose homogeneous
zero-debt and passport inequalities, minimize first-endpoint debt on the
resulting compact slice, and conclude that every exact product root at the
minimizer is all Continue.  The descendant-slice note additionally claims to
retain a positive actual paid gain, a tail decoration, and the separate
reset-face all-Continue point.

The narrow declarations inspected were:

- `QuittingStoppingLawVanishingDebtRectangleSequence` and
  `quittingStoppingLawRectangleTargetProfile` in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/OffDiagonal/AtomRectangleSequenceAlternative.lean`;
- `QuittingStoppingLawRectangleResetFaceDispatch`,
  `QuittingStoppingLawRectangleResetFaceDispatch.atom_bound`, and
  `QuittingStoppingLawRectangleMinimizerBridge.eventually_literal_lawPremium`
  in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/RectangleResetFaceMinimizer.lean`;
- `QuittingMarkedPairDecoratedFamily`, `prefixMap_mem_carrier`, and the exact
  marked-mass/actual-gain scaling theorems in
  `Research/Quitting/NormalizedPassportPrefixOrbit.lean`; and
- `normalizedPassportSlice_isCompact`,
  `prefixMap_mem_normalizedPassportSlice_of_isZeroNash`, and
  `minimum_normalizedPassportSlice_exactRoot_eq_allContinue` in
  `Research/Quitting/NormalizedPassportMinimizer.lean`.

## 1. The paired neutralization argument passes

Assume a compact paired carrier `P` and a continuous common-prefix operation

\[
 (x,y)\mapsto(P_u x,P_u y)
\]

which preserves `P` for every fixed product root.  On the closed slice

\[
 d_j(x)=0,\qquad F(x,y)\geq\rho D(x),
\]

exact cap--Nash prefixing at the first endpoint gives

\[
 d_j(P_u x)=s(u)d_j(x),\qquad
 D(P_u x)=s(u)D(x),\qquad
 F(P_u x,P_u y)=s(u)F(x,y).
\]

The last identity is exact: the fresh root law is identical on the two sides
and cancels, while the old law difference is multiplied by joint survival.
Thus the slice is exact-prefix invariant, including at survival zero.

The intersection construction is nonempty because the whole slice is itself
an admissible closed invariant containing the origin.  It is compact as a
closed subset of the compact paired carrier.  At a debt minimizer, any exact
root with survival less than one produces a point of strictly smaller debt.
The global lower bound `D_* > 0` excludes zero minimizer debt.  Finite root-game
Nash existence supplies at least one exact root; hence every exact root has
survival one, is literally all Continue, and all Continue is exact.  I found
no finite abstract counterexample to this argument under its stated compactness
and invariance hypotheses.

The hard-residual minimum landing is also sound.  The automatic-incidence
argument must use all three of the ingredients stated in the note: a positive
finite atom at every global-minimum joint law, singleton/Never cap tightness
at zero owner debt, and the global singleton margin.  Those are exactly the
ingredients used in the reviewed vanishing-response maximal-root packet.

## 2. The carrier definition needs to be literal

The phrase “all actual literal sibling pairs of the same typed kind” is not a
mathematical definition.  Whether common prefixing preserves the type depends
on what the type remembers.  It is true for the local response/sibling
relation after shifting the marked date.  It is false if the type requires an
unchanged absolute marked date or one fixed finite prehistory code.

The clean repair is the construction already suggested by the descendant
note: start from the supplied ranked pair family, adjoin **all finite arbitrary
common root words**, with the marked date shifted by the word length, and take
the closure of that raw orbit.  Continuity then proves prefix invariance
without any lower-hemicontinuity claim about exact roots.  This also proves
nonemptiness and compactness directly.  Alternatively, state the paired
neutralization theorem abstractly with “compact common-prefix-closed paired
carrier” as an explicit hypothesis.

There is no hidden selection of an unrelated semantic endpoint inside the
minimal invariant hull.  But the topological quotient forgets source codes.
An elementary abstract example has two distinct history codes with the same
semantic/law pair; their image in the paired carrier is one point.  No
operation on that carrier can later recover which code was used.  Accordingly
the minimizer has closed descendant provenance, not one literal prehistory or
an extension-compatible source.  Section 5 of the paired note states this
correctly, while “source-attached” in the descendant note is too strong unless
it is replaced by “in the closed descendant carrier.”

## 3. The stronger note has a missing paid-gain input

This is the substantive objection.

`QuittingStoppingLawVanishingDebtRectangleSequence` stores a positive tangent
`charge`, a signed observer atom between the literal double endpoint and the
same-response comparison endpoint, and vanishing observer debt.  It does
**not** store a positive actual payoff gain between those two response
endpoints.  The documentation for the fixed-law bridge is explicit that the
rectangle atom compares two counterfactual mover endpoints and is not by
itself a profitable deviation.

This distinction is mathematically necessary.  A positive signed terminal-law
coordinate for observer `j` imposes no sign on the mover's payoff difference:
choose two terminal laws with more mass on a coalition rewarded positively to
`j`, while the mover's reward on that coalition is smaller.  The observer
atom is positive and the mover gain is negative.  In the actual rectangle,
the observer's pure-time response is installed on both sides after the mover
replacement; a strategy selected as a best response against the original
opponents need not remain profitable after that observer change.

Therefore the assertion in the descendant note that the same-source sibling
“gives a fixed positive signed atom and a fixed paid gain” does not follow from
the named rectangle packet.  Neither the nonemptiness of the slice with
`g >= psi D` nor the positive bound on `g` at its minimizer has yet been
proved from the stated input.

This is repairable, but it requires an enlarged literal family, not a scalar
annotation added by fiat.  One option is to retain simultaneously:

1. the double response endpoint and its same-response sibling, for the signed
   atom;
2. the original source and mover-replacement endpoint, for an actual positive
   payoff gain;
3. the post-mark tail, if a consumer needs it; and
4. the common source rank, labels, and shifted marked date.

Every member of each pair must receive the same arbitrary prefix.  Only then
does the actual gain scale by the same joint survival as debt and the signed
atom.  One must also prove a uniform positive gain for the second pair along
the very subsequence used by the response rectangle.  The existing
`QuittingMarkedPairDecoratedFamily` shows the right provenance discipline for
one actual-gain pair, but its checked decoration is not already this
multi-profile response/sibling object.

If the paid-gain coordinate is removed, the paired note's signed-atom theorem
remains complete.  If it is retained, the missing multi-profile adapter is a
real premise of the stronger theorem.

## 4. Tail and double-all-Continue qualifications

“Together with every closed tail/source equality actually needed” is not a
definition.  The proof must list the finite compact coordinates and the exact
prefix action on each.  A post-mark tail normally remains fixed when a root is
inserted before the mark; a response sibling is instead prefixed.  Conflating
these two actions would give the wrong carrier map.

The separate reset-face minimizer `m` does have unique all-Continue by
`QuittingStoppingLawRectangleResetFaceDispatch.unique_capNash`.  It may be
kept as an external constant while minimizing the response descendant slice.
Then “double all-Continue” means only the conjunction of uniqueness at `m`
and uniqueness at the new response minimizer.  It does not show that `m` is a
descendant of, law-matched to, or chronologically composable with the new
minimizer.  The statement should say this explicitly.

## 5. Required revision

For a mathematically complete stronger result:

1. define the exact finite decoration and raw common-prefix orbit;
2. prove that its initial convergent family has both positive densities,
   especially the actual-gain density;
3. distinguish prefixed response/sibling coordinates from a fixed post-mark
   tail coordinate;
4. call the minimizer closed-descendant-provenant, not an actual regenerated
   source; and
5. state the second all-Continue point as an external same-origin certificate,
   unless a stronger relation is actually retained.

After these repairs, the compact-minimization and exact-root neutralization
proofs should go through verbatim.  The paired signed-atom result is therefore
real and nonduplicative at the response/sibling level; the checked normalized
passport minimizer supplies the engine but not the present adapter.  The
stronger descendant-slice result should not be exported in its current form.

## Delta review of the four-profile revision

Date: 2026-08-31  
Delta verdict: **PASS** as ordinary mathematics, with the stated status that
the four-profile adapter is not yet a checked declaration.

The revision resolves the substantive objection above.

At every rectangle rank it now distinguishes four literal profiles:

\[
 (R_n,Q_n)\quad\text{for the signed atom},
 \qquad (E_n,S_n)\quad\text{for the actual mover gain}.
\]

This is the necessary separation.  For the rectangle packet's mover `p`,
`p` belongs to `frontier.positiveDebtSupport` by construction.  The checked
theorem `fullReplacementPrescribedGain_tendsto_baseDebt` therefore gives

\[
 U_p(E_k)-U_p(S_k)\longrightarrow d_p(z_*)>0
\]

along all frontier ranks.  Composing with the rectangle packet's strict rank
map, and with any later strict compactness subsequences, preserves convergence
because each such map tends to infinity.  Thus the very same ranks used for
the response rectangle have an eventually uniform positive actual-gain floor.
This proves the missing `G>0` input; it does not infer gain from the signed
atom.

The common-prefix accounts are also correct.  Prefixing the same finite root
word to all four profiles:

- applies the continuous semantic/law prefix map to every `J` coordinate;
- multiplies the old-suffix law difference between `R` and `Q`, hence `A`, by
  joint survival;
- contributes the same fresh-root prescribed payoff to `E` and `S`, hence
  multiplies `U_p(E)-U_p(S)`, and therefore `G`, by the same survival; and
- when the root is exact against the displayed cap of `R`, multiplies every
  debt coordinate of `R`, including `d_j(R)` and total `D(R)`, by that
  survival.

Consequently `A >= theta D(R)`, `G >= psi D(R)`, and `d_j(R)=0` are preserved
by the exact-root prefix action used in the minimization proof.  The raw orbit
uses arbitrary common root words, so a root born only at a carrier limit still
maps the limit back into the closed carrier by continuity; exactness at raw
actualizers is neither used nor asserted.

Nonemptiness is obtained by a common fourfold compact subsequence of the base
decorations.  On it, `d_j(R_n) -> 0`, `A` has its fixed positive lower bound,
`G` tends to the positive base debt, and `D(R_n) -> L>0`; choosing
`theta < lim A/D(R_n)` and `psi < lim G/D(R_n)` puts the limit in the closed
slice.  The note could spell out this one compact-subsequence sentence, but no
new hypothesis or argument is missing.

The revision also correctly removes the uninstantiated tail coordinate,
calls the output closed-descendant rather than a recovered actual source, and
states that the reset-face point `m` is only an external same-origin
all-Continue certificate.  Subject to those explicit scope limits, the
four-profile descendant-slice theorem now passes.
