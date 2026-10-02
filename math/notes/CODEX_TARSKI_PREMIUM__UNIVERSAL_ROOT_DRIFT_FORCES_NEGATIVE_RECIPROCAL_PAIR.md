# Universal root drift forces a negative reciprocal singleton pair

Author: CODEX_TARSKI_PREMIUM.

Status: the ordinary C¹ root theorem passed independent mathematical review;
it is not Lean-checked. Its entire proposed UE class and the resulting raw
counterexample restriction are ALREADY COVERED by the current unconditional
projective-Q-bar Snell consumer. No new class or export is claimed. The
retained addition is the same-boundary-minimizer/gradient-pressure calculation,
which has not yet consumed the mixed-sign case.

Independent reviews of the original frozen proof at SHA
`5266a7c40cbc5a2699db96c8523be5e6a87dc801ad113e243fece6a3c8192662`:
[FRECHET](../feedback/CODEX_TARSKI_PREMIUM__UNIVERSAL_ROOT_DRIFT_FORCES_NEGATIVE_RECIPROCAL_PAIR__BY_CODEX_FRECHET_CYCLE.md),
[NOETHER](../feedback/CODEX_TARSKI_PREMIUM__UNIVERSAL_ROOT_DRIFT_FORCES_NEGATIVE_RECIPROCAL_PAIR__BY_CODEX_NOETHER_SUPPORT.md).
Both found the same substantive source-subsumption correction, now
incorporated below. No reward minimizer, minimum behavioral law, source
chronology, or transported tester weights are used in the C¹ argument.

## 1. Exact arbitrary-table question

Let I be a finite nonempty player set. At a live date its players choose
Quit independently; the first nonempty coalition S absorbs with bounded
reward vector r(S), |r_i(S)|≤M. Let B>M≥0, let K=[−B,B]^I, and put

    s_i=r_i({i}),       Γ_ij=r_i({j})−s_i.

In particular Γ_ii=0. Never pays zero in the eventual quitting-game
application, though the root theorem uses arbitrary abstract annotations.

For a product root q∈[0,1]^I, let c(q)=∏_i(1−q_i), a(q)=1−c(q), and

    R(q)=Σ_(S≠∅) Pr_q(S) r(S),
    F(q,v)=R(q)+c(q)v.

Let Q_i(q) be i's expected root payoff if it Quits and C_i(q,v) its
expected root payoff if it Continues, using v after all Continue. Explicitly,

    Q_i(q)=Σ_(T⊆I\{i}) Pr_(q,−i)(T) r_i(T∪{i}),
    C_i(q,v)=Σ_(∅≠T⊆I\{i}) Pr_(q,−i)(T) r_i(T)
                +Pr_(q,−i)(∅)v_i.

Thus F_i=q_i Q_i+(1−q_i)C_i. Exact root Nash means

    F_i(q,v)=max(Q_i(q),C_i(q,v))        for every i.

This is the finite one-stage condition at annotation v, not a supplied
terminal Nash profile. An annotation is not assumed to be a feasible
payoff or cap vector. Suppose H is C¹ on a neighborhood of K and obeys

    H(v)−H(F(q,v))≥a(q)                              (D)

for EVERY v∈K and EVERY exact root Nash q against v. The successor lies
in K because it is a convex combination of v and bounded reward vectors.

Every robust universal polynomial in
[the controller–tester question](../questions/QUITTING_CONTROLLER_TESTER_DUALITY.md)
satisfies (D): take an exact Nash root and w=F(q,v), so both robust
errors are zero. The following theorem therefore covers every polynomial
degree and, more strongly, every C¹ exact-edge potential.

**Theorem.** Condition (D) implies that some distinct i,j satisfy

    Γ_ij+Γ_ji<0.                                      (N)

In fact it produces a nonzero vector ρ≥0 with ρᵀΓρ<0. Consequently if

    r_i({j})−r_i({i})+r_j({i})−r_j({j})≥0
                    for every distinct i,j,            (P)

then no H satisfying (D) exists. No normality, sure-root exclusion,
convexity of H, or equilibrium selection is a root-theorem hypothesis.

## 2. Eligible singleton-face roots, including upper-box faces

For every i and every x∈K satisfying x_i=s_i and x_j≥s_j for j≠i,

    ∇H(x)·(x−r({i}))≥1.                               (F)

This is the exact-edge part of the singleton-face inequality in HILBERT's
polynomial note; its complete eligibility argument is included here.

First let all nonowner inequalities be strict. Only i Quits, with
probability t>0. Its two root endpoints both equal s_i. For j≠i, the
Quit-minus-Continue difference is exactly

    (1−t)(s_j−x_j)+t[r_j({i,j})−r_j({i})].              (1)

For sufficiently small t this is strictly negative for every nonowner.
Thus the chosen root REALLY is exact Nash, a=t, and

    F(q,x)=x+t(r({i})−x).

Apply (D), divide by t, and let t decrease to zero to get (F). This is
valid if some nonowner coordinate equals B, since the full successor
segment is in K. The lower reward bound is irrelevant to this segment's
eligibility except for keeping it in the padded box.

For weak nonowner inequalities, replace each x_j by
(1−ε)x_j+εB, leaving x_i=s_i fixed. Since B>s_j, all nonowner
inequalities are now strict. Apply the preceding result and use continuity
of ∇H as ε decreases to zero. The admissible t can depend on ε; no
uniform small-root Nash assertion at intersecting faces is inferred.

All these are exact Nash–Bellman edges and hence are admissible at EVERY
positive robust tolerance. The proof does not treat an arbitrary root
as admissible merely because the certificate quantifies universally.

## 3. Minimize on the lower singleton boundary, not on the whole box

Define the compact upper singleton box and its lower boundary by

    C=∏_i[s_i,B],
    L={x∈C : x_i=s_i for at least one i}.

Choose x minimizing H on L and set J={i:x_i=s_i}. There is no assumption
that x is a global minimum on K, convexity point, actual semantic state,
or uniquely selected minimizer. We use only its elementary feasible
coordinate directions within L.

The set J cannot have one element. If J={i}, the small exact solo root
of Section2 has successor w_i=s_i, while w_j>s_j for every j≠i when
t is small enough. Thus w∈L. Minimality gives H(w)≥H(x), whereas (D)
gives H(x)−H(w)≥t>0. This is a contradiction. This step also handles
the one-player boundary: no H satisfying (D) exists then.

Hence |J|≥2. Write g=∇H(x). If j∈J, increasing only coordinate j by
a sufficiently small amount keeps another coordinate pinned at its
singleton and stays in L. Therefore

    g_j≥0                     for j∈J.                 (2)

If j∉J and s_j<x_j<B, either sign of a small coordinate change stays
in L, so g_j=0. If j∉J and x_j=B, decreasing that coordinate stays
in L, so g_j≤0. Upper-box coordinates are thus retained with their
actual one-sided derivative signs, not discarded as interior coordinates.

For each i∈J, apply (F). Every upper-box coordinate j∉J contributes

    g_j(B−r_j({i}))≤0,

because B>M≥r_j({i}). Every other nonactive coordinate contributes zero.
The remaining lower-active coordinates give

    Σ_(j∈J) g_j(s_j−r_j({i}))≥1       for every i∈J.    (3)

Let ρ_j=g_j on J and ρ_j=0 off J. Then ρ≥0 and ρ≠0, since otherwise
the left side of (3) would vanish. Multiply (3) by ρ_i and sum over i∈J:

    −ρᵀΓρ≥Σ_(i∈J)ρ_i>0.                             (4)

This proves the promised strictly negative quadratic direction on the
NONNEGATIVE cone. It is not merely a negative Hessian direction for H.
Finally, zero diagonal gives the exact finite identity

    ρᵀΓρ=Σ_(i<j)ρ_iρ_j(Γ_ij+Γ_ji).

Its negativity forces a pair with both ρ_i,ρ_j positive and (N), proving
the theorem. Equivalently, for zero-diagonal Γ, (P) is exactly copositivity
on the nonnegative cone. No full standard-Q consequence was needed.

## 4. Actual normal-Fin4 semantic consumer

Now take I=Fin4 and define the actual behavioral punishment values

    P_i=inf_(independent opponent stopping laws) B_i.

Assume normality P_i≤s_i for every i and a positive singleton for at
least one owner. No punishment infimum is assumed attained, and no single
joint profile is assumed to realize all four punishment coordinates.

The checked equivalence
`quittingGame_not_exists_uniformEquilibriumPayoff_iff_noSureRoot_and_rationalPotential`
in
`UniformEquilibrium/Quitting/Projective/PolynomialForwardCertificateCharacterization.lean`
says that failure of a uniform-equilibrium payoff supplies BOTH:

- absence of a root Nash at the literal vector P with some sure quitter;
- a rational polynomial satisfying the universal robust drift inequality
  at some positive rational tolerance on the fixed box of radius M+2.

Under (P), the second alternative contradicts Sections1–3. Therefore
the table has a fixed uniform-equilibrium payoff against all behavioral
deviations. This is the actual semantic consumer, not a root-profile
verifier. The sure-root alternative is neither thrown away nor treated
as a repeatable edge: if it occurs, it already gives the positive semantic
exit; in the no-uniform contradiction the checked equivalence excludes it.

Combining this alternative proof with the independently checked
opposite-sign class below, any normal Fin4 table without a uniform payoff
and with a positive singleton must have BOTH a strictly positive and a
strictly negative reciprocal singleton pair. This necessary raw condition
is ALSO already implied by the existing projective-Q-bar and reciprocal-
nonpositive consumers; it is not a new narrowed counterexample class.

## 5. Exact boundary checks and bounded source comparison

The existing checked reciprocal-solo class has the OPPOSITE sign:
`exists_uniformEquilibriumPayoff_of_pairwise_reciprocalSolo_nonpos`
in `UniformEquilibrium/Quitting/Classification/SingletonPacketEnergy.lean`
assumes Γ_ij+Γ_ji≤0 for all pairs. Its definition
`quittingSingletonSoloEffect` is exactly Γ, with no sign conversion.
Thus it does not subsume (P), except on the common zero-reciprocal boundary.
Its source-packet energy is nonnegative; the new potential-boundary
gradient above produces a strictly NEGATIVE energy vector.

The original lookup stopped too early at a matrix-side Q bridge. The
complete CURRENT production composition, independently checked in both
reviews and reread by the author, covers ALL of (P), for every finite
player set and with no normality or positive-singleton hypotheses:

1. Every nonempty principal of a copositive Γ is copositive: extend its
   nonnegative test vector by zero outside that principal.
2. Split each principal on its homogeneous simplex solution. If present,
   it is projective Q by `isProjectiveQMatrix_iff_standard_or_homogeneous`
   in `UniformEquilibrium/Quitting/Classification/LCP/MatrixClasses.lean`.
3. If absent, `isR0Matrix_iff_not_singletonLCPFeasible` in
   `MathUE/LinearProgramming/CopositiveQ.lean` gives R₀. Its
   `copositive_isR0Matrix_isStandardQ`, transported by
   `isStandardQMatrix_of_copositive_of_isR0Matrix` in
   `UniformEquilibrium/Quitting/Classification/LCP/CopositiveQBridge.lean`,
   gives standard Q and hence projective Q by the same split. The
   homogeneous predicate is literally the generic simplex feasibility
   predicate, with no sign change.
4. The definition `IsProjectiveQBarMatrix` in `MatrixClasses.lean` is
   projective Q on every nonempty principal, so Γ is projective Q-bar.
5. Apply the CURRENT UNCONDITIONAL declaration
   `exists_uniformEquilibriumPayoff_of_projectiveQBar_snell` in
   `UniformEquilibrium/Quitting/AbsorptionPath/PunishmentNormalPathStrategicSnell.lean`.
   Its only extra mathematical premise is the ambient projective-Q-bar
   property; no strategic path producer is assumed.

Thus the entire claimed raw class, not merely particular tournament or
cycle examples, was already solved. The absence of a six-pair wrapper
with the candidate's name was not evidence of new coverage. The stronger
same-table Fin4 normality/positive-singleton adapter is valid but redundant
here and is not being packaged as a separate result.

An exact same-table regression is the production three-owner robust cycle.
Its own-singleton vector is (1,0,0,0), and direct substitution in its reward
definition gives

    Γ=[ 0 −1  2 −1 ]
      [ 2  0 −1 −1 ]
      [−1  2  0 −1 ]
      [ 1  1  1  0 ].

Every core pair has reciprocal sum1; each pair with owner3 has sum0.
Thus (P) holds, agreeing with the already checked charged-cycle
exclusion and same-table UE. This is a regression, not claimed new
coverage of that already solved example.

Conversely the earlier signed-cycle first-jet stress matrix

    Γ*=[ 0 −1 −1  6 ]
       [ 6  0 −1 −1 ]
       [−1  6  0 −1 ]
       [−1 −1  6  0 ]

has Γ*_(0,2)+Γ*_(2,0)=−2. For ρ=(1,0,1,0), ρᵀΓ*ρ=−2.
It therefore passes this new NECESSARY matrix test. It is already solved
by an independent cycle consumer, so negative reciprocal energy is not
sufficient for a universal potential or a no-UE table.

The nearby existing extremum calculations were read: HILBERT's
`POLYNOMIAL_DRIFT_SINGLETON_FACE_TEST`, FRECHET's
`POLYNOMIAL_ALL_ANCHOR_DISCOUNTED_NASH_TEST`,
`CONVEX_GLOBAL_ROOT_DRIFT_IMPOSSIBILITY`, and
`CONSTANT_OWN_QUIT_REWARD_GLOBAL_DRIFT_EXCLUSION` notes. They respectively
retain the singleton-face inequality, the neutral global minimum and Q
consequence, convex-potential exclusion, and a special successor-invariant
face. The new step is (3)–(4) at a nonconvex lower-boundary minimum with
all one-sided upper-box derivative terms retained.

The production interfaces read also include
`ThreeOwnerRobustCycle.no_potential` and
`ThreeOwnerRobustCycle.exists_uniformEquilibriumPayoff` in
`UniformEquilibrium/Quitting/Examples/ThreeOwnerRobustCycle.lean` and
`ThreeOwnerRobustCycleUniformPayoff.lean`, and
`SureRootNonrepeatability.punishmentValue_eq_punishment`,
`exactNash_punishment`, `suppliedProfile_exactTerminalNash`, and
`owner_coordinateNashDefect_terminalValue` in
`UniformEquilibrium/Quitting/Examples/SureRootNonrepeatability.lean`.
The last example's exact sure root has gain1/8 when repeated against its
own payoff, so no such repetition is imported here.

## 6. Remaining source-independent question

The checkpoint supplies an alternative all-degree proof at an already
covered class. Its retained object is the SAME lower-boundary minimizer
of H and its supported gradient inequalities (3), not just the known
negative-pair projection. It has not narrowed an open class. The next
concrete question is
whether finite positive-absorption root inequalities at that SAME forced
lower face, retaining collision rewards, yield a charged return or an
actual sure-root exit at P. No such implication is proved here, and no
new fixed-degree search or hypothetical good-child interface is proposed.
