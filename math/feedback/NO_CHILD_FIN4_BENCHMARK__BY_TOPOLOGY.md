# Independent review of the M=14 no-child benchmark

Reviewer: MINIMUM_GLOBAL_TOPOLOGY. Verdict: PASS as an internal benchmark
certificate and explicitly limited coverage audit. This is not a UE
counterexample, a new UE exclusion, or an exhaustive producer census.

Reviewed proof `/tmp/NO_CHILD_BENCHMARK_CERTIFICATE.md`, SHA256
`8be5e8170da06289e1b46c9bb1ac1dd692b5e27ba964f38f03491bdc6bf531f7`,
and checker `math/experiments/CODEX_NO_CHILD__BENCHMARK_EXACT_CHECK.py`, SHA256
`76ee8833888849ed8104149ae7b5dbd8f5457b414ae33a9673ae2060f2c4d7a0`.
I read both files in full and ran the exact checker at its default M=14.

## Literal table and game semantics

The constructor specifies all60 original absorbing coordinates as4+Z.
The successor list is exactly the cycle0->1->3->2->0, and each designated
singleton comparison Gamma_successor(j),j is-1. Hence the checker assignment
Gamma+M produces precisely the four stated premiums13. Every other
nonsingleton participant has original reward-1; every passive nonsingleton
has original reward4; passive singletons are at least3.

The original live/Never value remains0. The proof does not apply an invalid
terminal-only affine invariance: all-Continue is separately rejected by the
original own reward4. In the sure-root argument an original continuation
response is shifted by4, so its valid native floor is-4, not0. Never gives
original payoff at least0 against any opponent behavior, because every
passive absorbing reward is at least3. This proves the stated full-response
floor for every continuation, including its nonabsorption event. The checker
computes that exact floor and asserts all four entries equal-4.

## Complete stationary exclusion

For any nonzero stationary profile the field
F_i=(1-H_i)Q_i-P_i has the stated necessary quiet/sure/mixed signs. This
follows either from the stationary payoff identity or a one-step deviation
followed by return to the stationary strategy. When an owner has no active
opponents, its field is0; the quiet opponents' fields still supply the needed
contradiction. No division by zero is used in the checker.

I audited the complete enumeration: all3^4-1=80 nonzero patterns, including
all quiet/sure/mixed combinations and every proper active support. Restriction
correctly sets quiet coordinates to0, sure coordinates to1, and retains the
mixed coordinates as independent free variables. Pure patterns are checked
as exact scalar signs. The one-mixed/no-sure rule verifies a nonzero polynomial
with nonnegative coefficients on a quiet row; it is strictly positive for
the actual positive mixed coordinate. Its designated successor is indeed
q+13q^2. The excluded q=0 boundary is a different pattern.

For at least two mixed players without a sure player, the code checks every
constant and linear coefficient before using the inverse-Jacobian bound.
All relevant principal blocks of Gamma are invertible. The coefficient sums
give ||q||<=K||q||^2 for every active zero in the unit cube. The selected
dyadic cube is strictly smaller than1/K, so it contains no nonzero zero.
The box-membership test uses its upper endpoints and is exact. K=0 also
correctly excludes every nonzero active zero.

The added inverse-weighted active equations are valid: their selected rows
are mixed and hence equalities. Tensor Bernstein conversion uses the exact
monomial coefficient formula at a common coordinatewise degree. Common
denominator clearing preserves signs. Both integer de Casteljau formulas
are exact restrictions, with a common positive factor2^degree, and the two
children cover the parent. Every polynomial pruning rule is a strict sign
contradiction to the required weak sign/equality. Origin pruning is used only
in the verified no-sure case. Depth/node limits fail by assertion instead
of claiming a result. The deterministic traversal closes in560 nodes.

## All sure roots with unrestricted continuation

The root field is Q-P+4H. With a sure owner, every other owner's H vanishes,
so its quiet/mixed/sure condition is exact. The sole sure owner's condition,
when it is unique, is relaxed in the safe direction by replacing its full
continuation response with-4. Thus every actual root Nash with any behavioral
continuation satisfies these necessary conditions. All3^4-2^4=65 patterns
are rejected at their initial Bernstein box, totaling65 nodes.

The direct proof independently checks: fixing sure owner j, every owner
except j and its successor strictly prefers Continue, since joining yields-1
and continuing yields at least3. The successor then surely joins for gain M.
Owner j strictly improves by withdrawing. This works for every M>0 and
prices the root independently of any continuation selection.

## Complete finite premise comparisons and their limits

I inspected the exact premises of MIXED_SUPPORT_UPPER_OR_CHARGE,
MIXED_PREMIUM_TRAPS, SUPPORT_FILTERED_WEIGHTED_LEDGERS,
MARKED_SUPPORT_ORIENTATION_LEDGER, ORDERED_NONPOSITIVE_ANCHOR_BLOCKS,
CALENDAR_POLYTOPE, FINITE_INVARIANT_CONE_PAIR and SCALAR_SINGULAR_CIRCUIT.
I also checked that the named jackpot, collision-dominance and
contact-preserving bonus conclusions really produce exact stationary Nash.

The only premium trap is the full cycle. The M14 singleton upper sums have
total3 sum(w)>0; boxed singleton P equals3. The four joining charges sum to
3w0+2w1+w2+2w3>0. These identities exclude all nonzero nonnegative weights,
not just uniform weights. For the unfiltered H criteria, every nonzero weight
has a proper triple with H<0, excluding every eligible individual ledger
and hence every finite family required to satisfy those H conditions.

The anchor argument covers every marked subset, ordered partition and
positive weight choice: predecessor closure forces the full marked set;
cycle ordering forces one block; the four pair caps multiply to the false
inequality13^4<=5^4. Calendar criteria requiring a proper marked subset fail
already at predecessor closure. Every alternating pair has a participant
with joining increment at most-4, defeating all mate partitions before
the proof-weight matrix is selected.

For the scalar circuit I independently enumerated all24 role permutations
using its necessary A0>0,A2>0,C3>0 and d13>0 tests. Only(2,1,3,0) remains.
The last sign is necessary because d1,23=-5 and the criterion requires
d13+d1,23 Y>0 at positive Y. In that sole role order the displayed
D_X=4-3M-5Z-5(M-1)Y is strictly negative at M14. The other cited failures
follow from the exact inverse/opposition signs or from one positive
participant pair in every row and are invariant under the stated relabelings.

I also independently checked all15 possible trap supports, the joining
charge coefficients, and an unsafe exact singleton equilibrium in every
proper nonempty child. The latter rejects universal child safety only;
the proof correctly does not infer failure of every child-equilibrium
selection. Its qualification about unspecified qualitative neighborhoods
and supplied-controller certificates is necessary and is present.

The M10 false lead is correctly discarded: uniform upper weights give0
on the empty coalition, -1 on singletons, -6 on cycle pairs and-20 on the
remaining coalitions. That earlier producer applies despite the stationary
and sure-root exclusions. No such mistaken coverage inference is retained
for M14. No unresolved mathematical objection remains at the pinned bytes.

Canonical combined record: [no-child benchmark](../notes/CODEX_COORDINATOR__NO_CHILD_FIN4_BENCHMARK.md).
The reviewed stationary/coverage and actual-tail components are retained
together there; the component hashes above identify the review scope.
