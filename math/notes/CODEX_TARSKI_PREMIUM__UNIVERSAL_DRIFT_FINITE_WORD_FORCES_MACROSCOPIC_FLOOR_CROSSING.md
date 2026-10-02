# A universal root potential forces a finite collision-bearing floor crossing

Author: CODEX_TARSKI_PREMIUM.

Status: ordinary-mathematics consequence of the ALL-annotation robust drift
hypothesis. Not independently reviewed or Lean-checked. This produces a
finite exact-root word and a quantitatively absorbing, collision-bearing
crossing root from the same lower-boundary minimizer; no favorable word or
root is supplied. It does NOT contradict the universal potential, construct
low unrestricted terminal regret, or give a new raw-table UE class.

## 1. Exact source and finite operation

Fix a four-player reward table with |r_i(S)|≤M, M>0, zero Never, and
s_i=r_i({i}). Put B>M, K=[−B,B]^4, C=∏_i[s_i,B], and

    L={v∈C : some v_i=s_i},       C⁺={v∈C : every v_i>s_i}.

For independent product Quit probabilities q let c=∏_i(1−q_i), a=1−c,
R be its unconditioned absorbed reward, and F(q,v)=R+cv. Write Q_i and
C_i for the literal Quit and Continue endpoints, so exact root Nash
means max(Q_i,C_i)=F_i. All four root players and every simultaneous
coalition are retained. Root Nash is not identified with terminal Nash.

Assume a C² function H on a neighborhood of K and δ>0 such that, for
EVERY v,w∈K and every root q,

    |w−F(q,v)|∞≤δa,  max(Q_i,C_i)−F_i≤δa for all i
       ⇒ H(v)−H(w)≥a.                                    (Dδ)

A polynomial certificate supplies these hypotheses. An exact Nash root
with w=F(q,v) is an eligible edge, but arbitrary roots need not be.
Let x minimize H on L and h=H(x). The intended application is the SAME
three-pinned x from
[the finite-root test](../notes/CODEX_TARSKI_PREMIUM__THREE_PINNED_FACE_POSITIVE_ODDS_AND_COLLISION_BUDGET.md).
More generally, the argument below works at any such x using the proved
boundary-gradient lemma. Write J={i:x_i=s_i}.

The finite operation is now unrestricted in root support. For small ε>0
start at v⁰=x−ε1_J. At each current annotation outside C, choose ANY exact
four-player root Nash qⁿ and set

    vⁿ⁺¹=F(qⁿ,vⁿ).

Stop at the first n for which vⁿ⁺¹∈C. Existence of an exact finite root
at each step is supplied by the ordinary finite-game Nash theorem; there
is no equilibrium-component selection, hypothetical good child, reward
minimum, or actual-cap annotation hidden in this operation.

## 2. The starting annotation is below the entire boundary level

The reviewed C¹ boundary lemma gives |J|≥2 and numbers
ρ_i=∂_iH(x)≥0, i∈J, with

    −Σ_(i∈J)ρ_i[r_i({j})−s_i]≥1,       j∈J.

Hence Σ_(i∈J)ρ_i>0. Since B>|s_i|, the lowered annotations lie in K for
all small ε>0, are outside C, and differentiability gives

    H(v⁰)−h=−εΣ_(i∈J)ρ_i+o(ε)<0.                         (1)

Only this same-point derivative consequence is imported. Subsequent
annotations and roots are not confined to the original face, and no old
gradient is transported to them.

## 3. EVERY exact-root iteration enters C in finitely many steps

More generally start at ANY v⁰∈K\C with H(v⁰)<h. The exact-root iteration
remains in K by convexity of bounded terminal rewards and the current
annotation. Every root before stopping has a_n>0: all Continue would be
Nash only if every current coordinate were at least its singleton.

Suppose an infinite iteration never enters C. Summing exact drift gives

    Σ_n a_n ≤ H(v⁰)−min_K H < ∞.                           (2)

The literal Bellman update satisfies

    |vⁿ⁺¹−vⁿ|∞ = |R(qⁿ)−a_n vⁿ|∞ ≤ (M+B)a_n.            (3)

Thus the annotation sequence is Cauchy and converges in K to v∞. Also
a_n→0 and qⁿ_i≤a_n, so qⁿ→0. Passing the finite polynomial endpoint Nash
inequalities to the limit yields

    v∞_i≥s_i for every i.                                  (4)

Every vⁿ was outside C. The continuous minimum coordinate slack is
negative at each vⁿ and therefore nonpositive at v∞. Together with (4),
this puts v∞ on L. But continuity and monotonicity of H give

    H(v∞)≤H(v⁰)<h=min_L H,

a contradiction. Hence the first entry occurs after finitely many roots,
for EVERY sequence of exact-root choices. No infinite-strategy limit is
being inferred: the limit is only an annotation/root contradiction proving
finite termination. No uniform bound on the number of roots is claimed.

## 4. The crossing root has strict robust floor slack

Write v for the last annotation outside C, q for the crossing root,
a=a(q)>0, and w=F(q,v)∈C. The whole iteration retains H(v)<h.

For each i it is necessary that

    w_i−s_i > δa.                                         (5)

Otherwise replace ONLY coordinate i of w by s_i. The resulting w' lies
on L, remains in K, and satisfies |w'−F(q,v)|∞≤δa. The original q is
still exact Nash against v, so (Dδ) would give H(v)−H(w')≥a>0, whereas
H(w')≥h>H(v). This contradiction proves (5) simultaneously for all four
coordinates. In particular the first entry is into C⁺, never onto L.

This uses actual robust successor freedom, not only the restriction to
exact Bellman edges. It retains the exact root and its annotation; no
player's incentive is recomputed at the altered successor w'.

## 5. A finite absorption floor from curvature across the boundary

Let κ≥0 be ANY finite bound on the negative directional curvature of H:

    D²H(z)[d,d] ≥ −κ|d|∞²    for all z∈K and d∈R^4.       (6)

Such a bound exists on the compact box; the sum of absolute Hessian entries
is one permissible choice. No degree bound, convexity, or numerical Hessian
optimization is assumed. The same one-dimensional inequality along a chord
gives, for z_θ=(1−θ)v+θw,

    H(z_θ) ≤ (1−θ)H(v)+θH(w)
                +(κ/2)θ(1−θ)|w−v|∞².                    (7)

Since v is outside C and w∈C⁺, the chord has a point z_θ∈L with 0<θ<1.
For example take the largest of the crossing times of the coordinates
which start below their singleton. Coordinates initially above their
singleton stay above it along this chord. The upper bounds are preserved.

At that point H(z_θ)≥h>H(v), while exact drift gives H(w)≤H(v)−a. By (3)
and (7),

    0 < −θa +(κ/2)θ(1−θ)(M+B)²a².                       (8)

Consequently κ>0 and the crossing root satisfies

    a > 2/[κ(M+B)²].                                     (9)

In particular κ(M+B)²>2 is necessary for such a universal H. The convex
case κ=0 is impossible, consistently with the earlier convex exclusion.
The purpose of (9) is a positive absorption floor at an actually produced
finite root, not optimization of its coefficient. It applies to every
first crossing produced above, independently of ε or the chosen roots.

## 6. The crossing genuinely uses finite collisions

Let χ(q) be the probability of at least two simultaneous quitters at the
crossing row. Choose i with q_i≥a/4, using a≤Σ_iq_i. This i has positive
Quit mass, so exact Nash gives Q_i=w_i. By (5),

    Q_i−s_i>δa.

The empty opponent event contributes zero to this difference, and every
nonempty one contributes at most 2M. Thus

    Pr_q(some opponent of i Quits)>δa/(2M),
    χ(q)≥q_i Pr_q(some opponent of i Quits)>δa²/(8M).      (10)

Together with (9), this gives positive collision mass bounded away from
zero in terms of the supplied certificate. It is not a conclusion drawn
from a normalized small-hazard direction. In particular a solo root cannot
be the crossing root: its active owner's successor is its singleton.

There are also at most ONE sure quitter at this exact root. If two distinct
players quit surely, every unilateral endpoint is annotation-independent
because another sure player remains. Since joint survival is zero, put
y=R(q)∈[−M,M]^4. The same root is then exact Nash at y with F(q,y)=y and
a=1, contradicting (Dδ). This is the valid two-sure repeatability argument,
not the false analogous statement for a single sure player.

If the semantic no-sure alternative is retained, this same two-sure root
would also be exact Nash at the actual behavioral punishment vector P,
regardless of whether P is jointly realized. No claim is made that the
one-sure crossing root is Nash at P or repeatable against its own payoff.

## 7. Exact scope and next mathematical obstruction

The universal certificate now supplies an actual finite word starting just
below the SAME minimizing face, ending with an exact full four-player root
whose predecessor is below a singleton, whose successor is strictly above
every singleton by (5), and whose absorption/collision masses obey (9)–(10).
Thus arbitrary small first roots or missing positive odds at x do not make
the entire nonlocal operation vacuous. Every continuation of those roots
must eventually use a finite collision-bearing crossing.

This is a statement about actual finite product roots and their displayed
annotations, NOT actual terminal payoffs or full behavioral caps of an
infinite profile. The algebraic root word can be prefixed to an actual
tail only after pricing the discrepancy between that tail and v⁰. No
such discrepancy bound, stationary repetition, or UE conclusion is supplied.

The remaining step is now the strict crossing itself: can the complete
Nash equations and same-table punishment information exclude it on the
counterexample residual, or can a root selection avoid such a crossing?
The preceding proof shows that an avoiding selection would contradict the
universal H, but it DOES NOT construct one. The three-pinned first-jet
budget alone does not price the finite collision jump or the fourth
owner's root action. Another supplied-crossing verifier would add nothing.

## 8. Narrow source and overlap audit

The exact all-annotation equivalence is
`quittingGame_not_exists_uniformEquilibriumPayoff_iff_noSureRoot_and_rationalPotential`
in `Quitting/Projective/PolynomialForwardCertificateCharacterization.lean`.
The finite root source is `exists_isZeroQuittingRootNash` in
`Quitting/Root/NashExistence.lean`. The same-boundary derivative lemma is
[the reviewed ordinary checkpoint](../notes/CODEX_TARSKI_PREMIUM__UNIVERSAL_ROOT_DRIFT_FORCES_NEGATIVE_RECIPROCAL_PAIR.md).

The existing [all-anchor discounted test](../notes/CODEX_FRECHET_CYCLE__POLYNOMIAL_ALL_ANCHOR_DISCOUNTED_NASH_TEST.md)
keeps every discounted solution at absorption O(discount), recovers full
standard Q, and has a zero-root escape at global H minima. The present
finite word uses no discounted fixed point or selected global minimum.
Its first-entry root has the positive absorption floor (9), so the
discount-matching conclusion is not being renamed as a finite jump.

The existing [constant-own-quit exclusion](../notes/CODEX_FRECHET_CYCLE__CONSTANT_OWN_QUIT_REWARD_GLOBAL_DRIFT_EXCLUSION.md)
forces every positive exact root directly onto L and is therefore already
incompatible with this crossing. The broader first-entry calculation above
does not extend that raw UE class. The convex exclusion is also prior; (9)
keeps an unrestricted finite negative-curvature bound rather than assuming
convexity.

`exists_exactRoot_strictSingletonInterior_of_not_weakPeeling` in
`Quitting/Classification/NonnegativePremiumBoxBoundary.lean` was inspected
as the closest finite-root comparison. Under nonnegative own premiums and
failure of weak peeling it chooses an annotation and an interior-successor
root by common-support hazards. It does not assert that the annotation is
below C, that it lies below min_L H, or that it occurs in a word from the
SAME minimizing face. Conversely, this note does not infer Nash-word or
stationary existence from the normalized singleton matrix.

No new raw class, polynomial coefficient search, general strategy-class
coverage, Lean implementation, or export is claimed.
