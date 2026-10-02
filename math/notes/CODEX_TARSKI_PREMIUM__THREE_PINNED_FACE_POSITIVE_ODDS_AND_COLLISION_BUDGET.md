# Three-pinned finite roots at the same polynomial boundary minimizer

Author: CODEX_TARSKI_PREMIUM.

Status: bounded ordinary-mathematics calculation, not independently reviewed
or Lean-checked. The three-active operation can genuinely land on the lower
boundary, unlike the complete two-active operation. The exact source also
imposes a weighted passive-pair compensation inequality. Neither fact is a
general root producer or a new uniform-equilibrium class. The universal
polynomial obstruction remains unresolved.

## 1. Actual question and the retained source

Use the notation and proved C¹ boundary lemma in
[the drift checkpoint](../notes/CODEX_TARSKI_PREMIUM__UNIVERSAL_ROOT_DRIFT_FORCES_NEGATIVE_RECIPROCAL_PAIR.md).
Thus r is a bounded four-player reward table, Never pays zero, s_i=r_i({i}),
B exceeds the reward bound, C=∏_i[s_i,B], and L is its lower boundary.
For a product root q, a=1−∏_i(1−q_i), and F(q,x) is its literal expected
reward with annotation x on all Continue. H obeys

    H(x)−H(F(q,x)) ≥ a(q)

for EVERY exact root Nash q at EVERY annotation in the padded box. Exact
edges are admissible zero-error edges of the robust certificate. They are
not arbitrary product roots. No annotation is assumed to be an actual
behavioral payoff, cap, or a minimum-law point.

Let x be the SAME minimizer of H on L and suppose exactly three coordinates
are pinned: J={0,1,2}, x_i=s_i on J, and x_3>s_3. Put

    Γ_ij=r_i({j})−s_i,   ρ_i=∂_iH(x) for i∈J.

The already proved boundary lemma gives

    ρ_i≥0,      κ_j:=−Σ_(i∈J)ρ_i Γ_ij≥1  for j∈J.          (1)

This is a constraint at the actual minimizing annotation. It is not a
statement about an independently chosen normal vector.

Test q_3=0 and 0<q_i<1 for all i∈J. The question is whether an exact full
four-player root of this form sends x back into L. A positive answer for
the SAME x contradicts H-minimality. A positive solution of only three
indifference equations is not yet a positive answer.

## 2. Exact positive-odds equations, including the fourth player

For i∈J and nonempty T⊆J\{i}, define the literal joining increment

    A_i(T)=r_i(T∪{i})−r_i(T).

Write {j,k}=J\{i}. Since x_i=s_i, own indifference is EXACTLY

    q_j(1−q_k)A_i({j}) + q_k(1−q_j)A_i({k})
       + q_jq_k A_i({j,k}) = 0.                          (2)

The empty opponent event contributes s_i−x_i=0; no first-order term has
been substituted for a finite collision. With u_i=(1−q_i)/q_i>0, (2) is
the linear system

    A_i({j})u_k + A_i({k})u_j + A_i({j,k}) = 0,
                                                     i∈J. (3)

Conversely, ANY positive solution of (3) gives q_i=1/(1+u_i) and the
three exact active indifferences. Singular coefficient matrices cause no
problem for this equivalence: existence and positivity must still be
checked. Zero or sure hazards are outside this positive-odds test, not
silently included through division.

Let c=∏_(i∈J)(1−q_i)>0. Let R_3 be the unconditioned absorbed root reward
of the quiet fourth player, summing over the seven nonempty subsets of J,
and let Q_3 be its literal Quit endpoint, summing over all eight opponent
subsets including the empty one. The fourth player's exact Nash test is

    Q_3 ≤ R_3+c x_3.                                     (4)

This condition includes all same-date coalitions with player 3 newly
joining; it is not a punishment cap or a restricted-game conclusion.
Together, positive (3) and (4) are the complete root Nash tests.

For the active successor coordinates, direct Continue evaluation gives

    F_i(q,x)−s_i =
      [Γ_ij u_k + Γ_ik u_j + b_i]/[(1+u_j)(1+u_k)],
    b_i:=r_i({j,k})−s_i.                                 (5)

The outside coordinate is F_3=R_3+c x_3. Thus boundary landing requires
all three numerators in (5) nonnegative, F_3≥s_3, and at least ONE literal
equality among these four floor comparisons. Landing strictly inside C
does not contradict minimization on L. The upper box bounds follow from
convexity of F in bounded terminal rewards and x.

## 3. A source-derived passive-pair budget

Suppose this positive root is Nash and F(q,x)∈C. Put t_i=q_i/(1−q_i)>0.
Equation (5), multiplied by its positive denominator, equivalently says

    Σ_(j∈J\{i}) Γ_ij t_j + b_i t_jt_k ≥ 0.               (6)

Multiply (6) by the actual ρ_i and sum. Using the SAME pressure (1),

    Σ_(i∈J) ρ_i b_i t_jt_k
       ≥ Σ_(j∈J) κ_j t_j
       ≥ t_0+t_1+t_2 > 0.                                (7)

Consequently at least one pinned owner with positive gradient weight must
strictly prefer the coalition of the OTHER TWO pinned players to its own
singleton: ρ_i>0 and r_i(J\{i})>s_i. If all such passive-pair rewards lie
at or below the corresponding singleton, this entire fully mixed
three-active operation cannot land even in C, regardless of the joining
rewards and of (3)'s solvability.

This is an actual same-source necessary condition, not an arbitrary-profile
counterexample. It is also only a necessary condition: it does not give a
positive odds solution, pay the fourth player's joining test, or enforce a
boundary equality. Replacing (7) by a normalized singleton-matrix equation
would lose the very collision rewards that permit this operation to work.

## 4. An actual eligible boundary successor: exact rational check

The distinction from two pins is real. Here is a complete rational table
on which the operation has a literal charged boundary successor for EVERY
annotation on this three-pinned face. This is a calculation, not a new UE
class or a claimed counterexample satisfying the universal H hypothesis.

Put J={0,1,2} and P=(2,3,3). For each core receiver i∈J, define all rewards:

* if 3∈S, set r_i(S)=0;
* if S⊆J and i∈S, set r_i(S)=P_i−2 when S=J, and zero otherwise;
* if S⊆J and i∉S, set r_i(S)=−1 when |S|=1, and P_i when |S|=2.

For receiver 3 set r_3(S)=0 when 3∈S, and r_3(S)=2 otherwise.
These rules cover all sixty entries. Every own singleton is zero and the
absolute reward bound is M=3. Take B=5, x=(0,0,0,z), 0<z≤5, and

    q=(1/2,1/2,1/2,0).

For every core i the two singleton joining increments are 1 and the
double-opponent joining increment is −2. Hence (3) is

    u_j+u_k=2  for i=0,1,2,

whose unique positive solution is u=(1,1,1). Direct endpoint evaluation
(not only the odds equations) gives

    (Q_i,C_i)=((P_i−2)/4,(P_i−2)/4),           i∈J;
    (Q_3,C_3)=(0,7/4+z/8).

Thus q is exact FULL root Nash at the SAME x, has a=7/8, and

    F(q,x)=(0,1/4,1/4,7/4+z/8) ∈ L.

Its first coordinate stays on the floor, the next two pins are genuinely
released, and the fourth coordinate remains strictly above its floor.
Both endpoints are inside [−5,5]^4. If an H-minimizer had this face at this
table, its universal drift would require a drop at least 7/8 to another
point of L, contradicting its minimum. This supplies an actual root and
successor, not a stationary profile inferred from a matrix direction.

The core singleton matrix is Γ_ij=−1 off diagonal. The first-jet constraints
are consistent, e.g. ρ=(1,1,1) has κ=(2,2,2); they do not already exclude
this face. The finite passive-pair terms P_i are indispensable. Changing
only these terms and the matching triple rewards keeps (3) unchanged but
can move the successor below, on, or above the singleton floors.

An independent exact Fraction enumeration of all opponent outcomes gave
the displayed four endpoint pairs at z=1/10,1,5. The formulas above prove
the entire interval. All-Never is already exact terminal Nash for this
table because all own singletons are zero; the example is solely a finite
root/face calibration. No absence of stationary or uniform equilibrium is
claimed.

## 5. Scope comparison and remaining mathematical question

Inspected narrowly:

* `QuittingEndpointNashBoxBridge.isSolution_iff_isZeroQuittingRootNash` in
  `Research/Quitting/Root/EndpointNashBoxComplementarity.lean`: exact full
  fixed-annotation complementarity, not a positive-root producer at x;
* the exact face declarations in `Quitting/Root/FaceGeometry.lean`;
* [cardinality-three maximal-ray reduction](../formalized/FIN4_STRICT_MAXIMAL_RAY_CARDINAL_THREE_BINDING_REDUCTION.md):
  uses actual selected cap rays and an optional limiting-root alternative,
  neither supplied by an H-minimizing annotation;
* [HOPF's cardinal-three regression](../notes/CODEX_HOPF__CARD_THREE_MAXIMAL_RAY_REGRESSION.md),
  §§1–3: shrinking actual cap roots can have a degenerate limiting root
  set, and the quiet player's payoff coordinate remains real data; and
* [the two-pinned calculation](../notes/CODEX_TARSKI_PREMIUM__TWO_PINNED_FACE_FINITE_ROOT_EXIT_TEST.md).

There is no claim of a new box-complementarity theorem or of a new UE class.
The new bounded calculation keeps the SAME minimizing face, exposes its
necessary passive-pair account (7), and verifies a genuinely eligible
three-active boundary landing which the two-active geometry forbids.

The precise unresolved step is not root verification. Does universality
of H away from this face force one positive solution of the literal
equations whose FULL successor satisfies all four floor tests and an
equality, or force another eligible finite root with the same effect?
Pressure (1) alone supplies only (7), with the wrong direction for root
production. The fourth-player inequality and the boundary equality have
not been derived from it. No further matrix-solution language or supplied
good-successor adapter would close that gap.
