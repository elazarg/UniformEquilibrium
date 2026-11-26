# Independent whole-packet mathematical review

Reviewer: ACTUAL_CROSSING_SOURCE.

**Verdict: PASS. No mathematical repair requested.**

Reviewed artifact: `math/exports/PASSIVE_BOUND_TRIPLE_SELECTION_UNIFORM_EQUILIBRIUM.md`.
The reviewed complete 580-line candidate has SHA-256

`fb8d0ebe59dd05959f09c03bcd53fc6b6cf147e562305c98abda7a2811112a14`.

This review covers every section of that artifact, including its general raw
criterion, closed-domain selected-root consumer, numerical specialization,
strict sixty-coordinate example, architecture controls and source handoff.
It is an independent mathematical review of the whole text, not an approval
inherited from component reviews. The result is ordinary mathematics; no Lean
check or build is asserted. The full Fin4 conjecture remains open.

## Raw selection criterion

The proper bad-root reduction is exhaustive. Activity of player0 forces its
output to its nonpositive Quit offer. A singleton active owner has output
zero. The strict negative pair offers exclude supports13 and23. Thus only
pair12 and triple123 remain. Sure owners are already good by definition.

I checked the odds equations and all uses of the passive bound v_2<=W.
When W=0, positivity of c_21 and c_23 excludes both remaining supports.
When W>0, every positive triple has x_1<X. The positive Q_3 requirement
and G>0 produce the displayed upper bound on x_2. Substitution into phi_3
has the correct strict sign because -c_32-b_3 x_1>0. The two affine endpoint
conditions therefore force v_3>0 even at equality in an endpoint condition.
For fixed v_3>0, the same strict bounds x_1<X and x_2<Y hold at every
positive triple candidate, not merely at a bad one.

BLOCK correctly excludes pair12 and makes the Q_1 numerator nonpositive.
Under INDEX, the determinant lower bound remains valid when c_12 is
negative: replacing its two positive factors by their upper bounds lowers
the product. The other determinant product has the stated positive lower
bound. Solving phi_2 and phi_3 leaves one interval of positive candidates;
the derivative of phi_1 there is det(Dphi)/(D'F')>0. This proves uniqueness
of the entire positive triple candidate at the input needed by the proof.

I checked the ambient index convention, including the extension to the full
cube. The clipped map is continuous on ambient space, takes values in the
unit cube, and has total degree +1 on (-1,2)^4 by the displayed homotopy.
Strict inactive comparisons give identity rows; the active determinant has
sign (-1)^k det(Dphi). Thus a bad triple has index -1. A possible bad pair
has index -1 after removal of its inactive3 tie; inactive0 is already strict.
The pair implication in INDEX excludes a bad pair with c_12<0. If c_12=0,
perturbing v_1 away from zero removes its candidates.

The permitted perturbations stay in the literal closed box, keep v_0,v_2
fixed, and preserve a negative coordinate. The mixed singleton signs give
nondegenerate intervals for exactly the two coordinates being perturbed.
The unique pair's inactive3 equation has nonzero coefficient -H_3, so its
single tie is avoidable. Compactness of roots and closedness of the Nash and
good-root conditions restore all boundary inputs. The min v=0 case is
covered by AllContinue. There is no genericity assumption on the game and
no omitted boundary case at c_12=0 or at equality in (Q0).

## Closed selected-root consumer

The first-Quit-time representation covers every independent behavioral
replacement before absorption. The cap prefix formula uses its full
supremum, including literal Never. I checked the exact coherence residual
identity; every term is nonnegative. Hence positive original Never product
and zero debt imply U=B=e, including on the compact closures used later.
The passive box is used precisely at such points, not at arbitrary
prescribed continuation payoffs.

The local induction uses only the selected good-root graph. Its closedness
implies uniform smallness near an input whose only good root is AllContinue;
other bad roots need not be small. Positive outsiders then strictly prefer
Continue. In the kernel branch, the core payoff increments are quadratic
and the Quit offers linear in the small hazard, giving the stated O(epsilon)
cap and payoff errors over O(1/epsilon) steps. A small fixed total duration
preserves positive outsiders' buffers and gives a strict survival loss.

In the separating branch, the solo-owner seed stays in the exact closed
passive domain and has a nonpositive coordinate. Its virtual cap reset is
explicitly distinguished from the cap of the actual solo prefix. The signed
weighted drift is valid for every sufficiently small core-supported root.
The compact minimizing fiber is nonempty, and its positive survival makes
coherence applicable. The displacement estimate and fixed c_0 place a
hypothetical high-survival minimum inside the good-root neighborhood.
A nonzero good root preserves the original weighted constraint and the
strict survival budget while lowering survival. If only AllContinue is
good, weighted positivity forces a proper smaller zero set; the recursive
words preserve the original separator. Approximation followed by each
finite extension is legitimate because prefix maps are continuous and the
survival budget has strict slack. Length-independent cap/payoff
nonexpansiveness transfers the seed-generated words back to the original
input. No local-to-global optimization premise is smuggled into this step.

The actual minimum uses (U,B,e,N), retaining each original Never mass.
AllNever supplies a zero-debt point with nonpositive minimum. Moving the
smallest Never atom changes four prescribed values and three other caps;
the moved owner's cap is unchanged. This gives exactly the factor14 repair
bound, also on the closure. Positive debt infimum would therefore force a
positive minimum Never product. A nonzero good root contradicts that
minimum, and the local induction handles the unique-good-AllContinue case.
This proves A_Z=0. Nonnegative own shifts cannot increase regret on the
absorbing prescribed profiles. The cited terminal endpoint then fixes one
uniform-equilibrium payoff before the requested accuracy.

## Corollaries and exact controls

I independently checked the specialization's constants and quantifiers.
The whole p=0 cylinder allows every real a, including negative a, by combining
BLOCK and INDEX. For p>=0 the stated union a<=0, a>=1/2 or p=0 is correct;
the opposed-pair strip is only a boundary of this producer. No assertion
that it classifies all remaining Fin4 games is made.

For the literal sixty-entry table I recomputed the core data and determinant
bounds. W=10, c_21=19999/10000, c_12=-1/4 and J_21<0 are correct. All
nontrivial cap and sign conditions, the two affine tests and the determinant
bound have strict margins. Native singleton identities are preserved under
original-coordinate variation, while own shifts remain positive in a small
neighborhood. Continuity therefore supports the asserted open neighborhood
in all sixty original reward coordinates, without a claimed radius.

I reconstructed the coalition expectations independently with exact rational
arithmetic. The five leading coefficients in (19) are respectively
1/8, 53/20000, 10, 24803/800 and -47/200. All six safe-positive edges satisfy
their two required inequalities and form a strongly connected graph. Thus
all fourteen proper marked sets have the asserted singleton crossing; (18)
provides the full marked-set crossing. The passive intervals are exactly
[-1000,3], [-8,9], [-10,10], [-12,11], so these small witnesses lie in the
passive box. The text correctly labels them virtual, without claiming
actual independent realizability.

After changing only J_21 to1, exact recomputation gives the displayed output
(249/100,1/40,1/10,159/20), Quit offers -2099/10000 and -809/100, zero active
gaps and strict negative inactive gaps. The opposed pair has index +1.
This is an obstruction to dropping the index hypothesis, not a UE
counterexample or a claim that every root at that input is bad.

## Source and coverage scope

I inspected the cited Lean declaration signatures and relevant old raw
hypotheses. The negative-index and terminal cap/selection interfaces exist
with the stated roles. The old boxed selected consumer has a low-output
premise, so the packet correctly provides its own low-or-sure closed-domain
adapter. The strict example has premium core123 (all three have a positive
participant reward there, while player0 has none), negative reciprocal
joining products on13 and23, and a negative c_12. The named old core source
hypotheses consequently fail under every relabeling for the reasons stated.

The additional finite census of stationary, sure-first, withdrawal,
return/reset and weighted producers is explicitly a separate coverage audit.
This review does not assert that census has been rerun and does not use it
in the UE proof. The packet preserves that distinction and makes no
unrestricted exploitability-gap or arbitrary-Fin4 closure claim.
