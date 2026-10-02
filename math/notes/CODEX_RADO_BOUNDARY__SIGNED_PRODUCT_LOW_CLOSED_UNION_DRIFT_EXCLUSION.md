# Signed product-low premiums exclude drift by a closed-union minimum

Owner: CODEX_RADO_BOUNDARY.

Status: complete ordinary proof, not independently reviewed or Lean-checked.
No export is requested. The signed-Fin4 UE corollary is ALREADY covered by
the checked single-pivot normalization, product-low producer, and reverse
fixed-payoff lift. For polynomials, the root obstruction also follows from
TARSKI's completed stronger outside-minimum source. The proof below is an
independent, short differentiable exact-root argument, not a new negative
candidate or a newly consumed raw table class.

## 1. Bounded negative-search disposition

The current questions are
[ESCAPE_AWARE_FIN4_CERTIFICATE_SEARCH](../questions/ESCAPE_AWARE_FIN4_CERTIFICATE_SEARCH.md)
and [QUITTING_CONTROLLER_TESTER_DUALITY](../questions/QUITTING_CONTROLLER_TESTER_DUALITY.md).
The narrow concrete-candidate lookup found no surviving table suitable for
this pass. Section 8 of
[the screened-hard search](CODEX_DESCENDANT__SCREENED_HARD_RATIONAL_NEGATIVE_SEARCH.md)
exactly eliminates its sole retained diagonal-family survivor
`7dc6fad99c6ec955`; the unequal-high table now has its reviewed exact
period-three construction. Candidate C, C172, and VANISH were not reopened.
This is not a claim to have exhausted every repository table.

The selected alternative was to test a raw necessary restriction of a
putative coupled barrier: must product-low premiums fail even when original
singleton levels and participant premiums have arbitrary signs? The
direct proof succeeds, but the source audit below removes a novelty claim
for the resulting Fin4 class.

## 2. Exact raw condition and root theorem

Let I be a nonempty finite player set. Give every nonempty S⊆I a vector
r(S), with |r_i(S)|≤M and M≥0. Put s_i=r_i({i}). Fix B>M and
K=[−B,B]^I. The roots q∈[0,1]^I use independent private Quit draws.

For p_q(S)=∏_(i∈S)q_i ∏_(i∉S)(1−q_i), write

    c(q)=p_q(∅),       a(q)=1−c(q),
    R(q)=Σ_(S≠∅) p_q(S)r(S),       F(q,v)=R(q)+c(q)v.

Q_i(q) and C_i(q,v) are the literal forced-Quit and forced-Continue
endpoints, including all opponent coalitions. Thus

    F_i(q,v)=q_i Q_i(q)+(1−q_i)C_i(q,v),
    e_i(q,v)=max(Q_i(q),C_i(q,v))−F_i(q,v).

Exact root Nash means e_i(q,v)=0 for all i. The annotation v is arbitrary
in K and need not be a terminal payoff or a cap. Never has zero payoff
in the later game-semantic statement; it plays no role in this root theorem.

The RAW product-low condition is precisely

    for every q with a(q)>0, there is i with
        q_i>0 and Q_i(q)≤s_i.                         (PL)

This is `HasProductLowQuittingPremium` in the actual declaration
`UniformEquilibrium/Quitting/Classification/ProductLowQuittingPremium.lean`.
It is not the weaker test only on pure coalitions. It allows negative
premiums r_i(S)−s_i, positive premiums for other members, arbitrary
passive rewards, zero hazards, and sure hazards.

**Root theorem.** Under (PL), no H differentiable at every point of a
neighborhood of K can satisfy

    H(v)−H(F(q,v))≥a(q)                               (D)

for every v∈K and every exact root Nash q against v. Continuous
differentiability, convexity, separability, and a polynomial degree bound
are unnecessary. The same proof only needs continuity on K and
differentiability at the minimizer selected below.

Every universal robust polynomial in the current question satisfies (D):
choose w=F(q,v), giving zero Bellman residual and zero ordinary regret at
any positive tolerance. Its successor stays in K by convexity. The proof
therefore tests a literal subset of the full relation without asserting
that this subset is complete for arbitrary tables.

## 3. Every absorbing exact successor hits the closed union

Define

    D={v∈K : v_i≤s_i for at least one i}.              (1)

D is nonempty and compact, since |s_i|≤M<B. If q is exact Nash and
a(q)>0, use (PL) to choose an active i with Q_i≤s_i. Exact Nash and
q_i>0 imply F_i=Q_i. Thus

    every absorbing exact Nash successor belongs to D. (2)

No lower bound on the OTHER successor coordinates is used. In particular
(2) does not assert that the successor lies in the lower boundary of the
upper singleton orthant. Negative premiums really can violate that old
boundary assertion, as Section 6 checks.

## 4. A generic absorption bound below a singleton

For any owner i and any root q, let d_i=∏_(j≠i)(1−q_j). On the event
that no opponent quits the forced-Quit payoff is s_i. Hence

    |Q_i(q)−s_i|≤2M(1−d_i)≤2Ma(q).

Also, because v∈K,

    |F_i(q,v)−v_i|≤(M+B)a(q).

For an exact Nash root F_i≥Q_i, so

    s_i−v_i
      = (s_i−Q_i)+(Q_i−F_i)+(F_i−v_i)
      ≤ (3M+B)a(q).                                  (3)

Thus whenever v_i<s_i, EVERY exact Nash root against v has

    a(q)≥(s_i−v_i)/(3M+B)>0.                          (4)

The denominator is positive: B>M≥0 implies B>0. No division by a
hazard, opponent survival, or singleton level occurs. This covers sure
and proper supports alike. It uses only ordinary root Nash, not (PL).

## 5. Complete minimum argument

Assume H satisfies (D), and choose x minimizing H on D.

First, x cannot have x_i<s_i for any i. Finite root-game Nash existence
produces an exact q against x; (4) makes it absorbing; (2) places its
successor w in D. Then H(w)≥H(x), contradicting (D). Consequently

    x_i≥s_i for all i,       J={i:x_i=s_i} is nonempty. (5)

If J={i}, give only i hazard t>0. Its endpoints both equal s_i. For
every j≠i the Quit-minus-Continue difference is exactly

    (1−t)(s_j−x_j)+t[r_j({i,j})−r_j({i})].            (6)

It is strictly negative for sufficiently small t, because x_j>s_j.
One common positive t works for the finitely many nonowners. Hence
this is an exact root with absorption t; its successor has coordinate i
equal to s_i, so lies in D. Again (D) contradicts minimality. When I
has one player there are no nonowner tests and this case already finishes
the proof.

It remains that |J|≥2. Pick i∈J. Both positive and negative sufficiently
small changes of coordinate i keep the point in D: another binding
coordinate is unchanged. They also stay in K, since |s_i|<B. Therefore

    ∂_iH(x)=0.                                       (7)

For small h>0 put v_h=x−h e_i. Differentiability gives

    H(v_h)−H(x)=o(h).

Take ANY exact Nash root q_h against v_h. By (4),
a(q_h)≥h/(3M+B); by (2), w_h=F(q_h,v_h)∈D. Thus

    h/(3M+B) ≤ a(q_h)
      ≤ H(v_h)−H(w_h) ≤ H(v_h)−H(x)=o(h),

a contradiction after division by h and passage to zero. This proves
the theorem. It does not require q_h→0, a continuous Nash selection,
or a small-root return to the old lower boundary.

For M=0 the same proof is valid with denominator B. More directly,
every reward is zero and a sure solo root at annotation zero is an
exact positive-charge self-loop. No degenerate zero bound is hidden.

## 6. Exact signed-premium calibration

Take I=Fin4, s=(1,−1,0,0), and define all fifteen rows by

    r_i(S)=s_i−1_(|S|≥2) if i∈S, and r_i(S)=0 otherwise.

Every participant premium is nonpositive, so (PL) holds for every
product root. Both negative singleton levels and negative premiums occur.
The reward bound is M=2; use B=4. At

    v=(1,−3,0,0),       q=(1/2,1/2,0,0),

the complete forced endpoints are

    Q=(1/2,−3/2,−3/4,−3/4),
    C=(1/2,−3/2,0,0).

All four prescribed root defects are exactly zero and

    F(q,v)=(1/2,−3/2,0,0).

This successor is not above s, but it belongs to D. All eight
owner/action endpoint tests were computed through exact rational
opponent-coalition enumeration (eight outcomes per endpoint). This
calibration verifies the sign boundary of the argument; it is not a
negative candidate or a new table-specific equilibrium result.

## 7. Fin4 consequence and exact source subsumption

The root theorem would imply that every real Fin4 table satisfying (PL)
has an original fixed uniform-equilibrium payoff. Indeed, if every s_i≤0,
all-Never is exact Nash at every horizon: any deviation yields either its
nonpositive singleton or zero. Otherwise there is a positive singleton.
Assuming no original UE, the CURRENT
`finFour_punishment_le_singleton_of_no_uniformPayoff` in
`UniformEquilibrium/Diagnostics/Quitting/FinFourAuxiliaryDiscountedLocalization.lean`
produces original punishment normality. The CURRENT polynomial
characterization then produces H on a padded box, contradicted above.
This is a full-behavior, fixed-payoff statement, not stationary or periodic
completeness. The no-UE branch also excludes the separate sure-root exit;
that exit is not omitted from the characterization.

However, the ENTIRE corollary already follows from checked source
composition without this new proof:

1. Under no UE obtain original normality as above, and choose p with s_p>0.
2. `quittingSinglePivotNormalizedReward` replaces each nonpivot terminal
   coordinate by (r_i(S)−s_i)/s_p and the pivot coordinate by r_p(S)/s_p.
   `quittingSoloReward_singlePivotNormalized` makes its singleton vector
   exactly e_p. `quittingSinglePivotNormalizedReward_eq_playerwiseAffine`
   records the positive affine terminal transformation.
3. `hasProductLowQuittingPremium_playerwiseAffine` preserves (PL), because
   participant premiums are scaled by 1/s_p>0.
4. `exists_uniformEquilibriumPayoff_of_productLowPremium` in
   `UniformEquilibrium/Quitting/Classification/Existence/ProductLowPremiumUniformPayoff.lean`
   applies to the normalized table's nonnegative singleton levels. It
   produces the normalized UE; this is not a supplied strategic witness.
5. `isUniformEquilibriumPayoff_original_of_singlePivotNormalized` in
   `UniformEquilibrium/Quitting/Punishment/SinglePivotUniformPayoff.lean`
   uses only that normalized UE, s_p>0, and ORIGINAL punishment normality.
   Its proof constructs same-prefix tail lifts at each accuracy, bounds
   full original exploitability, and preserves one affine fixed target.
   Never is handled by those actual lifts, not by an assertion that every
   terminal affine change is strategically harmless.

Thus no new signed-singleton class is consumed. The nearby
`not_differentiable_absorptionDrift_of_nonnegative_productLow` genuinely
has the extra nonnegative-premium premise, but that narrower root theorem
was not the correct final stopping point for the source audit. The generic
auxiliary-germ absorbing-endpoint consumer also cannot simply be applied
to an arbitrary auxiliary periodic UE; the single-pivot reverse theorem
above is the actual available bridge.

## 8. Prior mathematical overlap and negative-certificate boundary

After the union-D proof was found, the completed
[outside-minimum note](CODEX_TARSKI_PREMIUM__GLOBAL_OUTSIDE_MINIMUM_AND_NASH_COMPONENT_RETURN_COST.md)
was inspected. It already proves, under a robust polynomial barrier, an
outside minimum where EVERY exact root has successor strictly above all
singleton levels. That immediately contradicts (PL). It is stronger
source information for polynomials than needed here. The present proof
is independent and needs only differentiability and exact-edge drift;
it does not claim discovery of the outside region or a new polynomial
counterexample restriction.

Accordingly every genuine Fin4 no-UE table must fail (PL), but this is an
already available necessary condition, not a new narrowed candidate class.
The checked
`not_hasProductLowQuittingPremium_iff_exists_inwardViolation` in
`UniformEquilibrium/Quitting/Classification/ProductLowQuittingPremiumInwardViolation.lean`
makes that failure an actual absorbing product root with no sure quitter
and strictly positive Quit premium at EVERY active player. It preserves
support and imposes no singleton-sign hypothesis. Such a root is only a
raw screen; it is neither an equilibrium nor a lower-gap certificate.

A positive negative-route result still requires one literal table and a
sound all-profile lower certificate, or a rational H and positive rational
δ verified on the ENTIRE floor-free root relation, together with actual
semantic normality and exclusion of the sure-root condition at the true
behavioral punishment vector. Every annotation, support face, near-zero
charge, and endpoint perturbation is included. The original semantic
conclusion must cover Never, arbitrarily late clocks, and all unilateral
laws. A strict premium root, finite-calendar gap, or absence of a selected
periodic profile is not that certificate.

The named source files above, the current controller question, and the
actual finite-root declaration `exists_isZeroQuittingRootNash` in
`UniformEquilibrium/Quitting/Root/NashExistence.lean` were inspected.
`SinglePivotNormalization.lean` is in
`UniformEquilibrium/Quitting/Root/`. No Lean build was run. Stop this
one source test with the complete proof and the subsumption recorded;
do not open another candidate search or export from this result.
