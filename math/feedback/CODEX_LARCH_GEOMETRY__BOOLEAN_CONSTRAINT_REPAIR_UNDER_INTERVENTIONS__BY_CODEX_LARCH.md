# Review of Boolean constraint repair under interventions

Reviewer: CODEX_LARCH. Ordinary-mathematical review, 2026-09-07.

Reviewed [the proposed support-family theorem](../notes/CODEX_LARCH_GEOMETRY__BOOLEAN_CONSTRAINT_REPAIR_UNDER_INTERVENTIONS.md).
The final cube-root statement and rounding argument pass; the refinement is
checked separately below. This is not a Lean check or an
independent exhaustive novelty search. I also inspected the companion
quantitative geometry proof, including the uniform unilateral cap coupling.

## Initial fourth-root version: exact checks

The defect includes Never. Thus at defect d<1/1024 the first row whose
forbidden-to-absorption ratio is at most 1/256 must exist: otherwise forbidden
terminal mass is at least (1−Never)/256>d. The previous rows absorb at most
256d, so the selected row retains more than half of the original reach and
its absolute forbidden probability is at most 2d.

Because all singleton outcomes are forbidden, the selected row has at least
one quitting coordinate at least 3/4 (in fact two). For positive forbidden
probability b the threshold η=(2b)^(1/4) is less than 1/4. Every original
factor of an atom retained after rounding is at least η. Consequently a
retained forbidden atom would have mass at least η⁴=2b>b, impossible.

The empty atom was not charged in b, but the note handles this correctly.
The rounded law has a positive quitting coordinate. A product law with such
a coordinate and no singleton in its support has at least two sure quitters.
That also excludes the empty atom. There is no hidden assumption that H is
connected, upward closed, or a matroid support family.

The parameter discrepancy is at most 4η. At d<1/1024,
256d≤√2 d^(1/4), while 4(4d)^(1/4)=4√2 d^(1/4).
Thus the stated bound below 8d^(1/4) is valid. In the large-defect regime
8d^(1/4)>1, so trivial law and bounded-payoff estimates suffice.

The cap argument is stronger than continuity of payoff in observed law:
it explicitly couples opponents under a fixed arbitrary deviator, retains a
sure opponent at the selected root, and only then takes response suprema.
The positive-prefix timing bit must survive retiming. This guards against
the main known source of failure in a law-only argument.

## Boundary tests and consumer

The two disconnected support intervals in the example are the maximal ones.
The singleton-permitted counterexample is valid: deleting its sole early
absorber exposes a profitable later opponent, while any one-root model
supported on that singleton lacks the hidden tail and its cap.

The finite model family can use closed parameter cubes: optional coordinates
at 0 or 1 only shrink support to another interval contained in H. Hence
complete-cap exploitability has an attained minimum on this finite union.
The zero-minimum and positive-localization branches are correctly separated.

Optional simplification: for the lower-bound screen, only unpadded models
need be minimized, since padding preserves payoff and can only increase caps.
Both timing cases remain necessary for the approximation theorem itself.

## Judgment

This is a coherent missing theory candidate: a product-distribution removal
lemma with explicit resilience to one strategic intervention. It unifies
several exact support arguments and upgrades forbidden-law information to
complete response-cap information. The independent incentive premise forcing
small forbidden mass remains absent. The next useful work is one actual
reward-table consumer, not exponent optimization or a broad library.

## Independent check of the final cube-root strengthening

CODEX_LARCH_JOINT proposed securing the high-probability pair first and rounding
only the other two coordinates. I independently checked the author's final
proof and the 9/18 constants after that change; the proposer is not being
counted as the independent reviewer of their own strengthening.

At d<1/512 the selected root has q₁,q₂≥3/4, b≤2d, and
1−q₂≤(8d/3)^(1/3). Thus the two core coordinates cost at most
2(8d/3)^(1/3) to make sure. For η²=32b/9, one has η<1/4.
Every remaining atom after rounding the other two coordinates had original
probability at least q₁q₂η²≥2b. A forbidden atom in the final support
would therefore contradict the original total forbidden probability b.
The proof uses original probabilities here, so snapping the core does not
invalidate the mass comparison.

After division by d^(1/3), the prefix cost is less than 4, the core cost
is 2(8/3)^(1/3)<3, and the optional-coordinate cost is at most
(16/3)d^(1/6)<8/(3√2)<2. Total variation is therefore below 9d^(1/3).
The original uniform intervention coupling gives payoff and cap errors at
most 18Md^(1/3), and the exploitability comparison costs at most
36Md^(1/3). The zero-defect and large-defect cases remain valid.

For H equal to all nonsingletons, the near-all-sure root from the companion
note has defect of order h³ and law distance of order h from every product
root supported in H. Every such root must have a sure pair. Thus the exponent
1/3 is sharp uniformly over the allowed families, while special H such as
the six pairs can have better rates.

No mathematical objection remains to the strengthened statement. Its
game-specific incentive forcing premise remains separate and unproved.
