Historical design record. Frozen source/review artifact; see Research/Pending/README.md.

# Independent static review: connected convex-hull representation

Verdict: mathematical/source/API PASS; no definite Lean API error or required
repair identified. This is STATIC evidence only, not compilation, axiom,
integration, or Sorin Proposition 4 completion. All frozen patch bodies,
source/dependency record and harness were read. No shared writes, compiler,
Git, caches/worktrees, children, or math-note edits were used.

## Frozen inputs and bases

Directory: `/tmp/connected-convex-hull-representation.hYZuV5t9`.
SHA256 computed independently:

```text
2b1d72e843a889ff409fe661a324ed2ef8e872e1371ca73ac1c7ae947b91b87a  001_CONNECTED_CONVEX_HULL_REPRESENTATION.patch
b9e26c4ab53d9b27deb5e4c47eeaa6c05001da0b22b283d2fe54855c3aee961d  002_MATHUE_UMBRELLA.patch
88ddf6ceb2932393a1bba1f11dfca581ffb8428fb4727a853002cde24efcd758  AXIOMS.lean
2329010e6f38a0c2d40d4580d8af7c906d993c83d92d0f5fa72afe25443bdae0  SOURCE_AND_DEPENDENCIES.txt
c5cc87c89cb647a91cfb42d65227bf7052f6611146f756b6d6345260c5d51a94  MathUE/Topology/FarthestPointContactHull.lean
eccfb315401ec04dd3a64794e6f8ecbd2e66ce591abb00d05f79ee68381da9ce  MathUE.lean
32306dff26b27f23707f10a4f73d335ff7134386d1c3223b4b6b47703ea69ba4  Literature/Sorin1986.lean
d09a8e78f37f9863ff40e969a90f03799967d05eb70ba28a93afab84ddfce56c  literature/SORIN_1986__ON_REPEATED_GAMES_WITH_COMPLETE_INFORMATION.pdf
```

The four advertised existing-file/source hashes match. The two patches add
one generic module and its umbrella import; the current umbrella has the
exact insertion context. Root must compose any independent pending umbrella
changes and regenerate/check AxiomAudit after accepting the module.

## Source scope

Sorin printed p.151 was read directly from the supplied PDF. Proposition 4
uses connectedness of the one-stage independent-payoff image and a convex
representation with at most N terms, followed by a geometric schedule.
Only the convex-representation prerequisite is supplied here.

The publisher's [Teissier Proposition 4.2, pp.220–221](https://library.slmath.org/books/Book51/files/07teissier.pdf)
was inspected. It gives the more general at-most-d-components theorem.
The draft implements its connected case via normalized barycentric winner
regions: a boundary tie reduces the representation, while absence of ties
would give a nonconstant continuous discrete label. It does not claim the
component-count generalization or use path connectedness.

## Exact new surfaces

Both declarations are in proposed
`MathUE/Topology/ConnectedConvexHullRepresentation.lean`.

`exists_tied_max_of_isPreconnected` accepts any topological space, a finite
nontrivial label type, a preconnected source, continuous-on-source real
scores, and one strict winning source point for each label. It produces one
ACTUAL source point and two distinct labels attaining the maximum there.
The strict-winning-point premise belongs only to this generic helper; the
convex-hull theorem constructs those points internally from its selected
vertices. No favorable winner certificate is an input to the final theorem.

`exists_small_finset_of_mem_convexHull_isPreconnected` accepts a real finite-
dimensional normed vector space, any preconnected subset and actual convex-
hull membership. It produces a nonempty finite family INSIDE THAT source,
containing the SAME point in its convex hull, with cardinality at most
max(1, ambient finrank). No compactness, closedness, finite source, supplied
simplex, affine basis, coefficients, or source-nonemptiness premise appears.
Preconnected empty sources cause no problem: convex-hull membership supplies
the necessary nonempty representation.

## Minimal family, dimension, and internal choice

The proof reuses
`exists_minimal_affineIndependent_finset_of_mem_convexHull` and
`exists_pos_weights_of_minimal_convexHull_family` in
`MathUE/Topology/FarthestPointContactHull.lean`. Their exact first two bodies
and signatures were inspected. They are generic module results, stated
before that file's inner-product-space variables: importing this owner does
NOT impose a Euclidean metric or compact-contact hypothesis on the new API.

The chosen family is minimal among ALL finite source representations.
Its span-rank bound yields card≤dim+1 using `Submodule.finrank_le`. If it
already has card≤max(1,dim), the theorem immediately returns it. Otherwise
integer arithmetic gives card=dim+1 and card>1. Consequently a nontrivial
index subtype and a full affine basis are justified. In dimension zero the
first branch necessarily succeeds with one point; no impossible two-label
or zero-cardinality construction is attempted.

Strict positive weights are derived from minimality, not assumed. Their
sum is one and their weighted point sum is the original point. The local
minimality passed to the positive-weight owner correctly composes
alternative⊆family with family⊆source. All classical choices concern
internally proved nonempty finite/maximal or existential data.

## Strict-winner and replacement calculation

For basis coordinates b_k(y) and positive target weights w_k, the scores
are b_k(y)/w_k. At vertex k its score is 1/w_k>0 and all other scores are
zero. The proof supplies every winning source point from family⊆source.

Assuming no tie, finite maximization selects one label at every source point.
Each singleton fiber is exactly the finite intersection of strict comparison
regions. These are relatively open by `ContinuousOn.domRestrict` and
`isOpen_lt`. Giving the finite target its discrete topology therefore makes
the label continuous. `PreconnectedSpace.constant` contradicts the two
distinct vertex winners. This uses neither a continuous path nor compactness.

At the tied point let M be the maximal score. The proof correctly shows
M>0: if M≤0, all coordinates b_k(y)≤0 because w_k>0, contradicting their
sum one. Set a=1/M and residual weights r_k=w_k−a*b_k(y).
Maximality gives b_k(y)≤M*w_k and therefore r_k≥0. The two tied maximum
coordinates have residual zero. No sign condition on OTHER barycentric
coordinates is assumed or needed.

Coordinate summation gives sum r_k=1−a; coordinate reconstruction gives
sum r_k*v_k=point−a*y. Thus adding y with weight a yields nonnegative
weights summing to one and the SAME original point. An explicit a≤1 lemma
is unnecessary: nonnegative residuals and the exact total already imply it.

Removing both zero residuals is valid even for a two-point old family.
The new labels are Option(remaining): none carries y with coefficient a,
and some carries each retained original vertex. This permits empty remaining
families and coincident new points without an injectivity assumption.
Every new point lies in insert y (family.erase i).erase j, which lies in
source. Finite convex-sum membership then constructs the replacement hull.

Distinct subtype indices imply distinct original vertices. Both erase
membership proofs are explicit. Two applications of card_erase_add_one
and the upper bound card_insert_le give new card<old card, including when y
already belongs to the remaining family. This contradicts original global
minimality with the correct inequality orientation.

## Pinned API audit

The following actual signatures and orientations were checked:

- `Finset.exists_max_image`: supplies maximum inequalities in the direction
  used by winner_max; `lt_of_le_of_ne` takes the needed left-to-right disequality.
- `continuous_discrete_rng`, `discreteTopology_bot`,
  `isPreconnected_iff_preconnectedSpace`, and `PreconnectedSpace.constant`:
  agree with the local subtype/discrete instances and explicit x/y arguments.
- `Fintype.one_lt_card_iff_nontrivial` and
  `AffineIndependent.affineSpan_eq_top_iff_card_eq_finrank_add_one`:
  give the nontrivial label instance and basis totality actually used.
- `AffineBasis` fields toFun/ind'/tot', `coord_apply_ne`, `coord_apply_eq`,
  `sum_coord_apply_eq_one`, `linear_combination_coord_eq_self`, and
  `continuous_barycentric_coord`: all match the real normed-module setting.
- `Finset.sum_erase` is the ZERO-TERM variant generated from prod_erase;
  it accepts a zero-value equality and needs no erased-element membership.
  The draft is NOT confusing it with sum_erase_add or sum_erase_eq_sub.
- `Fintype.sum_option` puts none first, matching both `change` lines;
  `Finset.sum_coe_sort` is used in the same direction as the canonical
  positive-weight owner. `Convex.sum_mem` has the stated nonnegative,
  sum-one and point-membership premises.
- `Finset.card_erase_add_one` takes membership; `card_insert_le` needs no
  freshness premise. Both calls have the correct supplied information.

No definite wrong declaration name, reversed algebra inequality, missing
mathematical premise, or invalid cardinality argument was found. Lean still
must check dependent-subtype coercions, definitional unfolding of the local
basis/score/remaining functions, rewrite inference in the vector-sum erase
steps, generated additive declarations' import reachability, tactic behavior,
unused imports/variables and warning policy. Static inspection cannot certify
these elaboration details or transitive axioms.

## Dependencies and nonclaims

Production search found no existing connected convex-hull reduction owner
to which this new theorem should instead delegate. Existing minimal-family
and positive-weight foundations are reused rather than copied. Its owner
belongs in MathUE and imports no Literature or game-semantic module.

The source record correctly leaves literal Sorin P4 and the actual discounted
behavioral schedule for subsequent work. Current `proposition_4` remains a
Literature sorry; importing this generic theorem alone does not discharge it.
No new API here supplies an infinite schedule, actual repeated-game payoff
law, uniform equilibrium, or Nash property. The at-most-d-components theorem
is also outside this draft's promised scope.

The harness prints both new theorems. Root should check the module, harness,
umbrella integration and generated axiom audit; no such check ran here.
No proof-only overlay is proposed because no definite repair was established.
