# Adversarial review of the binding-pair solo-probe repair

Target:
[`FIN4_STRICT_MAXIMAL_RAY_CARDINAL_THREE_BINDING_REDUCTION.md`](../exports/FIN4_STRICT_MAXIMAL_RAY_CARDINAL_THREE_BINDING_REDUCTION.md)

Reviewer: `CODEX_LEFSCHETZ`

## Verdict

The solo-probe repair is correct and supplies exactly the two collision-gain
signs missing from the exported both-mixed argument.  It is now stronger than
an ordinary-mathematics repair: the general sign lemma and its binding-pair
specialization are proved in Lean in
`Research/Quitting/BindingCollisionGainPositivity.lean`.

The export still needs a literal mathematical edit.  Its both-mixed proof
asserts nonnegativity of the two collision gains before handling only the zero
case, and its solo paragraph compresses two logically different uses of
maximality and sign information.  Both should instead cite the limit-cap
solo-probe argument.  This repair does not construct the finite-cap local
parity certificate or an inhabitant of the general parity specification.

I tried to falsify the repair at the limit cap, at the finite cap, in both
support patterns, and in the maximality/localization step.  I found one wrong
displayed formula in the earlier feedback but no defect in the repaired
conclusion.

## Exact solo-probe calculation

Let

\[
 d_h(b):=b_h-r_h(\{h\}),
 \qquad
 J_{hj}:=r_h(\{h,j\})-r_h(\{j\}).
\]

Fix a player `j` and let only `j` Quit with probability `t`, with
`0<t<1`.  For the probing player itself, Quit minus Continue is

\[
 g_j(t e_j;b)=-d_j(b).
\tag{1}
\]

It is independent of `t`, because a player's endpoint comparison depends
only on the opponents' root.  For every `h != j`,

\[
 g_h(t e_j;b)=tJ_{hj}-(1-t)d_h(b).
\tag{2}
\]

Thus one formula in the previous feedback is inaccurate: the probing
player's difference is not `-(1-t)d_j(b)`.  At a binding player both
expressions are zero, so the error does not affect the proposed contradiction.

Equations (1)--(2) are exactly the checked declarations

- `quittingRootEndpointDifference_soloStationaryRoot_owner_cap`; and
- `quittingRootEndpointDifference_soloStationaryRoot_other_cap`

in `Research/Quitting/BindingCollisionGainPositivity.lean`.

## Audit at the limiting cap

Let the limiting binding set be exactly `{i,j}`.  The forward-tail hypotheses
give

\[
 d_i(\bar b)=d_j(\bar b)=0,
 \qquad
 d_h(\bar b)>0\quad(h\notin\{i,j\}).
\]

For the solo probe at `j`:

- `j` is interior and exactly indifferent by (1);
- `i`, prescribed Continue, has endpoint difference `t J_ij`;
- every outsider `h` has
  `t J_hj - (1-t)d_h(bar b) < 0` for all sufficiently small positive `t`.

Consequently, if `J_ij <= 0`, a sufficiently small positive probe at `j` is
an exact non-all-Continue root against the limiting cap.  Uniqueness therefore
forces

\[
 J_{ij}>0.
\]

Interchanging `i` and `j` gives `J_ji>0`.  This checks every player class;
no sign assumption on an outsider collision entry is used.

The robust general version is already proved as
`exists_quittingSingletonCollisionGain_pos_of_unique_allContinue`.  Its
binding-pair specialization
`QuittingForwardExactCapTail.quittingSingletonCollisionGain_pos_of_bindingFinset_card_eq_two`
uses cardinality two to identify the positive binding witness with the other
member of the pair.  It therefore proves both strict signs, not just the
existence of one positive entry.

The hypotheses line up exactly:

- `singleton_le_capLimit` supplies nonnegative cap defects at the limiting
  cap;
- membership in `bindingFinset` is equivalent to zero cap defect by
  `mem_bindingFinset_iff_capDefect_eq_zero`; and
- `HasUniqueAllContinueAtCapLimit` has the exact universal implication used by
  the sign lemma.

No finite-cap inequality is inferred from `singleton_le_capLimit`.

## Transport from the limit cap to a finite cap

The two `J` entries depend only on the reward table, so their strict signs
transport unchanged from the limiting-cap probe to every finite-cap face
calculation.  This is the only limit-to-finite transfer being made.

If both selected binding hazards at a sufficiently late finite time are
positive, summable absorption makes both hazards strictly below one.  Exact
interior complementarity gives

\[
 (1-x_j)d_i(b_k)=x_jJ_{ij},
 \qquad
 (1-x_i)d_j(b_k)=x_iJ_{ji}.
\]

The strict `J` signs now imply both finite-cap defects are strictly positive.
The all-Continue root is therefore strict on the binding pair at this finite
cap.  This is the legitimate route to the finite-cap sign; the limiting
singleton bound alone would not suffice.

If exactly one binding hazard, say `x_i`, is positive, exact complementarity
gives `d_i(b_k)=0`.  The other binding player is prescribed Continue.  If its
endpoint inequality were strict, `x_i` could be increased slightly while:

- player `i` remained indifferent, since its comparison is independent of its
  own hazard and `x_j=0`;
- player `j` remained a strict continuer; and
- the outsiders remained strict continuers in the localized neighborhood.

This would contradict maximal absorption.  Hence

\[
 (1-x_i)d_j(b_k)=x_iJ_{ji}.
\]

The already established `J_ji>0` then gives `d_j(b_k)>0`.  The reverse sign
`J_ij>0` is also supplied by the same limit-cap sign lemma.  The export should
present maximality as proving the endpoint equality, not as the unexplained
source of both the equality and the collision sign.

## Support-pattern and localization audit

On a two-coordinate binding face, eventual support localization leaves only
the both-positive and solo-positive patterns, because every selected root has
positive total hazard.  Summable absorption makes all positive hazards
interior at sufficiently late times.

Maximality localizes the complete finite-cap root set correctly.  Every exact
root `x` at `b_k` has absorption no larger than the selected maximal root, and
each coordinate hazard is bounded above by total absorption.  As the selected
absorption tends to zero, every exact root lies in a fixed neighborhood of all
Continue.  Continuity and the strictly positive limiting defects of the two
outsiders make those outsiders strict Continue throughout that neighborhood
for all sufficiently late caps.

Within the resulting two-dimensional face:

- in the both-positive case the exact roots in the neighborhood are strict
  all Continue and the unique regular mixed coordination root;
- in the solo case the exact component is the segment from all Continue to
  the selected solo endpoint; after increasing the solo owner's finite cap
  defect slightly, the nearby roots are strict all Continue and one regular
  mixed coordination root.

The latter perturbation admits a common isolating neighborhood: at parameter
zero it contains the compact segment, and for sufficiently small positive
perturbation the explicit two affine comparisons put the two isolated roots
inside it and no root on its boundary.  I found no missing support pattern or
limit/finite-cap interchange in this reduction.

## What remains open

The sign repair does not prove the cardinality-two exclusion by itself.  The
ordinary export still invokes the standard finite-game component-index
theorem.  The current Lean consumer remains conditional on supplied parity and
finite-cap local-certificate data; the sign lemma supplies neither:

- an inhabitant of `ModTwoBoxComplementarityParitySpec`; nor
- `FinFourBindingPairFiniteCapParityWitness`.

Thus the honest status is:

1. the previously missing collision signs are now proved in Lean in the
   Research lane;
2. the finite/limit algebra needed by the proposed repair is sound; and
3. the explicit same-resolution local-zero computation or a general parity
   implementation remains a separate formalization obligation.

## Required export edit

1. Replace the unsupported opening of the both-mixed paragraph with the
   limiting-cap solo-probe proof, or cite the checked binding-pair sign theorem.
2. In the solo paragraph, use the same theorem for both strict `J` signs and
   use maximality only to force the finite-cap endpoint equality.
3. Do not copy the erroneous factor `(1-t)` into the probing player's own
   endpoint formula; use (1).
4. Add `Research/Quitting/BindingCollisionGainPositivity.lean` and the named
   declarations above to the source correspondence.

After these edits, the mathematical sign objection is resolved.  The export's
separate topological/Lean prerequisite must remain stated exactly as open.

## Verification performed

I ran:

```text
lake env lean Research/Quitting/BindingCollisionGainPositivity.lean
```

at the current repository head.  It completed successfully with no output.
This is a targeted Research-file compilation, not an integrated axiom audit or
a proof of the conditional parity certificate.

## Post-repair verdict

I re-read the rewritten export. **PASS on the solo-probe formulas, collision
signs, finite/limit separation, and status language.**

The probing player's comparison is now correctly stated as
`g_j = -bar_delta_j`, independent of its own rate. The other binding player
and outsider formulas have the correct signs. The proof uses uniqueness only
at the limiting cap to establish the two fixed reward-table inequalities
`J_ij > 0` and `J_ji > 0`, then uses finite-cap indifference equations only at
the selected finite root. It no longer infers a finite-cap singleton bound
from the limiting one.

The rewritten status also cleanly separates the checked generic Research
ingredients from the unproved source-specific Fin4 adapter. It no longer
claims that an abstract parity-spec inhabitant or signed component-index
formalization is required. I found no remaining objection within the scope of
this review. The whole finite-grid/cardinality-two proof is independently
covered by the separately listed whole-gate review.
