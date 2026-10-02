# Coupled boundary minima select a bad principal, but do not produce a return

Owner: CODEX_NOETHER_SUPPORT.

Status: complete bounded ordinary-mathematical derivation and stopped operation
test; not independently reviewed or Lean-checked. The common-gradient alignment
below is already retained in TARSKI's reviewed boundary-minimum argument; the
principal conclusion is a direct corollary, not a new source alignment. Its
matrix cone exclusion is also already implied by nonprojectivity in sizes two
and three, even for the same displayed principal. The explicit original-budget
floor-loss bound in Section 5 is a follow-through calculation, not a consumer.
No raw-table UE class, absorbing selector, or return path is obtained. Keep internal.

## 1. Question, actual game, and universal annotation hypothesis

There are four players, arbitrary signed rewards r(S) at each nonempty quitting
coalition, Never payoff zero, and a bound |r_i(S)|≤M with M>0. Players' complete
stopping laws are independent; deviations in the underlying game are unrestricted
behavioral deviations. Put s_i=r_i({i}), B=M+2, and K=[−B,B]⁴.

For a one-stage product root q∈[0,1]⁴ write

    p_q(S)=∏_(i∈S)q_i ∏_(i∉S)(1−q_i),
    c(q)=∏_i(1−q_i),       a(q)=1−c(q),
    F(q,v)=Σ_(S≠∅)p_q(S)r(S)+c(q)v.

Let Q_i(q), C_i(q,v) be the literal current Quit and Continue payoffs, including
v only when everybody continues, and let

    e_i(q,v)=max(Q_i(q),C_i(q,v))−F_i(q,v).

Assume a C¹ function H on a neighborhood of K and one fixed δ∈(0,1/4] obey

    e_i(q,v)≤δa(q) and |w_i−F_i(q,v)|≤δa(q) for every i
        ⇒ H(v)−H(w)≥a(q),                            (1)

for EVERY v,w∈K and EVERY q. This is the current floor-free robust relation,
not a relation restricted to actual continuation payoffs or selected roots.
Neither normality nor existence of an actual profile realizing v is assumed
in the local analysis. In particular the permitted endpoint error is δa,
not a fixed absolute error. At a=0 both error accounts vanish.

The proposed operation was to minimize H on the lower boundary

    C=∏_i[s_i,B],       L={v∈C : v_i=s_i for some i},

identify a principal from that SAME minimum, and use its root to return to L.
Compactness makes argmin_L H nonempty; no convexity or separability of H is used.

## 2. Singleton faces, including upper-box coordinates

For every v∈C with v_i=s_i, hypothesis (1) gives

    ∇H(v)·(v−r({i})) ≥ 1+δ||∇H(v)||₁.               (2)

This is HILBERT's robust singleton-face inequality, with the padded upper-box
boundary retained explicitly. First suppose v_j>s_j for j≠i. Give only i a
small hazard t>0. Player i is indifferent and the other players' exact gaps are

    Q_j−C_j=(1−t)(s_j−v_j)
                  +t[r_j({i,j})−r_j({i})].          (3)

They are negative for sufficiently small t, so the root is exact Nash. For
every d∈[−1,1]⁴ the endpoint

    w_t=v+t(r({i})−v+δd)

has error at most δt. It belongs to K for small t, even if v_j=B: then its
coordinate direction is at most M−B+δ=−2+δ<0. There is no lower-box issue,
since v_j≥s_j≥−M>−B. Divide (1) by t and let t decrease to zero. Maximizing
∇H(v)·d gives (2).

If additional v_j=s_j, approach them from above while keeping v_i=s_i and
any upper coordinates fixed. The admissible t can depend on the approaching
point. Continuity of the gradient passes (2) to the limit; it does NOT supply
a positive Nash hazard at the limiting multi-binding point.

## 3. The previously retained gradient and its principal corollary

The minimum, binding set, gradient signs, upper-box contributions, and common
column inequality in this section are already retained in Sections 2–3 and 6
of [TARSKI's reviewed note](CODEX_TARSKI_PREMIUM__UNIVERSAL_ROOT_DRIFT_FORCES_NEGATIVE_RECIPROCAL_PAIR.md).
The argument is repeated here to keep the subsequent δ-budget calculation
self-contained. Replacing the exact-edge right side 1 by HILBERT's robust
right side 1+δ||h||₁ gives (5); the principal statements then follow directly.

Fix ANY z∈argmin_L H. Write

    J={i:z_i=s_i},     U={i:z_i=B},     h=∇H(z).

First |J|≥2. If J={i}, the exact solo root used in (3) has, for sufficiently
small t>0, successor z+t(r({i})−z) still in L. Coordinate i stays at s_i;
every other coordinate stays strictly above its singleton. This contradicts
minimality and positive drift in (1).

Since |J|≥2, every one-coordinate feasible motion in C leaves another lower
coordinate binding and hence stays in L. The one-sided derivative conditions are

    h_j≥0 (j∈J),
    h_j=0 (s_j<z_j<B),
    h_u≤0 (u∈U).                                    (4)

The upper derivatives need not vanish. Define the zero-diagonal singleton
matrix, one positive scalar, and the upper-face bill by

    Γ_ji=r_j({i})−s_j,
    c_H=1+δ||h||₁,
    β_i=Σ_(u∈U)(−h_u)(B−r_u({i}))≥0.

For i∈J, the exact identity in (2) is

    h·(z−r({i}))=−Σ_(j∈J)h_jΓ_ji−β_i.

Consequently the SAME gradient at the SAME minimum satisfies

    Σ_(j∈J)h_jΓ_ji ≤ −c_H−β_i   for EVERY i∈J.       (5)

In particular L_h=Σ_(j∈J)h_j>0. At least two of these h_j are positive:
if only h_k were positive, column k of the left side would be zero.

Equation (5) strictly separates the principal's nonnegative cone:

    there is no y≥0, y≠0, with Γ_J y≥0.              (6)

Indeed its scalar product with h_J is both nonnegative and at most
−Σ_i(c_H+β_i)y_i<0. Thus Γ_J is not projective Q: at projective right-hand
side −1, a putative normalized residual Γ_J y−z₀1≥0, with z₀≥0, y≥0 and
z₀+Σy=1, contradicts the same scalar product (including y=0).

For the same-table no-UE source, the actual repository residual supplies

    λ_i>0,     Σ_iλ_i=1,     Γλ≥0.                  (7)

Then J cannot be all four players, by multiplying (5) by λ. Thus the
H-selected principal has EXACTLY two or three players. This holds for every
minimum z and the same H, not merely for one convenient minimizer.

The outside contribution is also tied to this gradient:

    Σ_(o∉J)λ_o Σ_(j∈J)h_jΓ_jo
        ≥ c_H Σ_(i∈J)λ_i + Σ_(i∈J)λ_iβ_i >0.       (8)

For |J|=3 its single outside column therefore has strictly positive h_J-weighted
value. For |J|=2, (5) forces both h-coordinates positive and both reciprocal
off-diagonal entries strictly negative. Equation (8) is not four separate
coordinate signs. The packet λ is an algebraic proof mixture; it is not a
correlated strategy or a claimed actual independent singleton-law realization.

## 4. Novelty correction: (6) is not a new matrix-class restriction

In fact, for EVERY zero-diagonal matrix A of size two or three,

    A nonprojective Q  ⇒  no nonzero y≥0 has Ay≥0.    (9)

This needs no passage to a different subprincipal. Here is the exact elementary
reduction to the current three-player classification.

Nonprojectivity excludes the homogeneous simplex LCP branch. Thus every
column has a strictly negative entry: an entrywise nonnegative column would
give the homogeneous solution concentrated on that diagonal-zero label.
In size two this makes both off-diagonal entries negative, proving (9).

In size three, suppose first that A_12 and A_21 are negative. Column 3 has
a negative entry in row 1 or row 2. If A_13<0, row 1 of Ay≥0 forces
y_2=y_3=0, and row 2 then forces y_1=0; the other case is symmetric.

If there is no negative reciprocal pair, the negative-column condition
forces a negative directed three-cycle. After relabeling write

    A = [ 0  a −b ]
        [−c  0  d ]
        [ e −f  0 ],     b,c,f>0, a,d,e≥0.

Its determinant is ade−bcf. If it is zero, the reverse entries are all
positive and there is a positive kernel vector, giving a homogeneous solution.
If it is positive, the current strict-orientation theorem makes A standard Q.
Both alternatives contradict nonprojectivity. Hence ade<bcf.

Now Ay≥0 reads a y_2≥b y_3, d y_3≥c y_1, e y_1≥f y_2. A zero coordinate
forces all coordinates zero; otherwise multiplying contradicts ade<bcf.
This proves (9), including zero reverse entries. Conversely (6) implies
nonprojectivity by the right-hand-side argument following (6).

Therefore a stricter-looking cone inequality does not improve the static
bad-principal class. Nor is strict negative determinant of the no-pair
three-cycle new: the old nonprojective/homogeneous alternatives already
exclude equality. The dispatch's alternatives can overlap; a named cyclic
constructor does not assert absence of an outside helper.

There is a second, separate subsumption correction: the alignment itself is
not new here. TARSKI's Section 3 uses this same arbitrary lower-boundary
minimizer, actual binding set, gradient, and upper-box signs. Before discarding
the nonpositive upper terms, its displayed proof retains exactly their bill
β_i. Its Section 6 explicitly identifies the common supported gradient
inequalities, not merely the reciprocal-pair projection, as the retained object.
HILBERT's robust singleton-face inequality supplies the factor 1+δ||h||₁
without changing that minimizer. Thus (5), and its same-J principal and
same-packet consequences (6)–(8), are direct corollaries of already retained
derivations, not a newly produced alignment or a new necessary source class.

The prior strict-ray binding set in BOREL's note is still a different object;
no identification of that ray with this H-boundary minimum follows. This
distinction does not confer novelty on the H-minimum alignment. What is
recorded additionally here is the exact matrix-quantifier clarification (9)
and the explicit failed original-budget return calculation (10), with no
independent importance or export claim.

## 5. The smallest return operation fails with its original error budget

Try a small independent root supported on J and use the allowed δa endpoint
perturbation to bring its successor back into C, and hence possibly L.
The obstruction is stronger than failure of a particular Nash selection:
EVERY sufficiently small such root, Nash or not, misses C even after the
full permitted endpoint perturbation.

Let q_o=0 for o∉J and t=Σ_(j∈J)q_j. For i∈J, since z_i=s_i,

    F_i(q,z)−s_i = Σ_(j∈J)q_jΓ_ij + R_i.

Put p_j=q_j∏_(k∈J\{j})(1−q_k). Elementary independent-event bounds give

    Σ_j(q_j−p_j)≤t²,
    Pr(at least two Quit draws)≤Σ_(j<k)q_jq_k≤t²/2.

Each relevant reward-minus-singleton coordinate has magnitude at most 2M.
Thus, with the original nonnegative h_J,

    |Σ_(i∈J)h_iR_i|≤3ML_h t².

For EVERY w satisfying ||w−F(q,z)||∞≤δa(q), equation (5), a(q)≤t and
||h||₁≥L_h give

    Σ_(i∈J)h_i(w_i−s_i)
       ≤ −c_H t+3ML_h t²+δL_h a(q)
       ≤ −t+3ML_h t².

Consequently, if 0<t≤min(1,1/(6ML_h)),

    Σ_(i∈J)h_i(w_i−s_i)≤−t/2≤−a(q)/2,
    min_(i∈J)(w_i−s_i)≤−a(q)/(2L_h)<0.              (10)

This is the original δ-budget, not an assumed smaller error tolerance.
The universal relation permits below-singleton exits, so (10) does not
contradict (1). Minimality on L has no control over their H-values. It
does not exclude either the pair or the three-player binding face.

There is a second distinct issue: (5) concerns prescribed drift, NOT the
actual root indifferences. For i∈J the correct first-order endpoint gap is

    Q_i(q)−C_i(q,z)
       =Σ_(j∈J\{i})q_j[r_i({i,j})−r_i({j})]+O(t²), (11)

with collision rewards retained. It is not −Σ_jΓ_ijq_j unless extra
pair-member equalities are supplied. The singleton principal alone does
not produce an exact or δ-relative Nash root of positive charge. At q=0,
all-Continue IS exact because z≥s; finite root Nash existence already has
that zero-charge solution. Neither (10) nor (11) assumes root disappearance.

## 6. Exact sources, checks, and stopping boundary

The entry route was
[QUITTING_CONTROLLER_TESTER_DUALITY.md](../questions/QUITTING_CONTROLLER_TESTER_DUALITY.md)
and the corresponding polynomial and hard-residual sections of docs/TOOLKIT.md
and docs/FRONTIER.md. Exact definitions/declarations inspected:

- `IsQuittingFloorFreeRobustEdge`, `QuittingRobustChargedEdge`, and
  `quittingFloorFreeRobustChargedRelation` in
  `UniformEquilibrium/Quitting/Projective/RobustChargedRelation.lean`.
- `quittingGame_not_exists_uniformEquilibriumPayoff_iff_noSureRoot_and_rationalPotential`
  in `Quitting/Projective/PolynomialForwardCertificateCharacterization.lean`.
  This supplies H at the SAME table under no UE, supplied normality and a
  positive singleton. The same-table residual below supplies all normality;
  absence of a positive singleton would make all-Never exact. No reduction
  to another reward table is used here.
- `FinFourQuantitativeFullSupportHardResidual` and
  `nonempty_finFourQuantitativeFullSupportHardResidual_of_no_uniformPayoff` in
  `Diagnostics/Quitting/Collision/SingletonPacket/FullSupportProjectiveQBarResidual.lean`.
  Its full-support normalized packet gives (7), using the definitions in
  `Quitting/Classification/ThreePlayer/AnalyticPacket.lean`.
- `exists_nonprojectivePrincipal_card_two_or_three` in
  `FullSupportHardPrincipalSize.lean` and `hardPrincipalDispatch` in
  `FullSupportHardPrincipalDispatch.lean`, in that same diagnostic directory.
- `SingletonLCPFeasible` in `MathUE/LinearProgramming/SingletonLCP.lean`;
  the standard/projective/homogeneous definitions and
  `exists_negative_entry_in_column_of_noHomogeneous` in
  `Quitting/Classification/LCP/MatrixClasses.lean`;
  `standardQ_and_noHomogeneous_iff_cycleDeterminant_pos_of_reverse` in
  `Quitting/Classification/LCP/ThreeByThreeZeroDiagonalQ.lean`.
- The orientation/homogeneous/determinant proof and `threeCycleHardPrincipalIncidence`
  in `Diagnostics/Quitting/Collision/SingletonPacket/ThreeCycleLassoHardPrincipalIncidence.lean`.

All paths in the preceding list are repository-relative with the
`UniformEquilibrium/` prefix except the explicitly named `MathUE/` file.
These are source inspections under their imports, not a fresh build or a
claim that this note's gradient alignment is already formalized.

The nearby mathematical comparisons read were
[HILBERT's singleton faces](CODEX_HILBERT__POLYNOMIAL_DRIFT_SINGLETON_FACE_TEST.md),
[TARSKI's same boundary-minimizer and gradient derivation](CODEX_TARSKI_PREMIUM__UNIVERSAL_ROOT_DRIFT_FORCES_NEGATIVE_RECIPROCAL_PAIR.md),
[FRECHET's convex exclusion](CODEX_FRECHET_CYCLE__CONVEX_GLOBAL_ROOT_DRIFT_IMPOSSIBILITY.md),
[RADO's nonconvex separable exclusion](CODEX_RADO_BOUNDARY__NONCONVEX_SEPARABLE_POLYNOMIAL_DRIFT_EXCLUSION.md),
[the zero-charge anchor test](CODEX_FRECHET_CYCLE__POTENTIAL_GUIDED_ANCHOR_ZERO_CHARGE_TEST.md),
and [BOREL's distinct strict-ray binding question](CODEX_BOREL__STRICT_RAY_TAIL_NORMALIZATION.md).
The separable exclusion is not reproved or generalized to arbitrary coupled H.

TARSKI's complete current note was checked at SHA256
`950779729225c61055b8edc9d222919869fcff2968aa751204ce38f09896472b`.
Its original argument had already passed independent review, including
[my own review](../feedback/CODEX_TARSKI_PREMIUM__UNIVERSAL_ROOT_DRIFT_FORCES_NEGATIVE_RECIPROCAL_PAIR__BY_CODEX_NOETHER_SUPPORT.md),
which explicitly reconstructed these same gradient signs and common column
inequality. The initial lookup for this note missed that retained result;
the source comparison and novelty wording above correct that omission.

As an exact algebraic sanity check, all 729 zero-diagonal 3×3 matrices with
off-diagonal entries in {−1,0,1} were examined using rational simplex-vertex
feasibility. Among negative-column cases, all 109 cases with a harmful pair
and all 14 remaining negative-determinant cycles had an empty feasible cone
section. Zero-determinant no-pair cases admitted complementary simplex points.
This verifies boundary signs in (9); it is neither a substitute for its proof
nor evidence that any test table carries a universal H or is a counterexample.

The bounded operation stops at (10)–(11). There is no UE consumer or export
claim. A distinct next question, not addressed here, is whether minimizing
the SAME H on several singleton faces forces a compatible finite root/path
comparison. Finitely many binding labels do not by themselves produce a
cycle, a return edge, or a positive charge.
