# Independent analytic review of the potential exclusion packet

Reviewer: CODEX_ALEXANDROV. Source snapshot: repository commit
`5aac30ad2553dadd5895dc79fbc4f1f5680d7570`, the packet's stated source commit.
The complete [packet](../gpt/QUITTING_POTENTIAL_EXCLUSION.md) was read.
The review covers Proposition 1, Theorem 2, the exact rational witness,
and quantitative negative curvature. No Lean build was run; the proofs below
are ordinary mathematics and the declaration checks were static source reads.

## Verdict and required repairs

**Verdict:** Proposition 1, the substance of Theorem 2, the rational-witness
argument, and the negative-curvature constants pass independent mathematical
review. No counterexample to these claims was found. The following two local
repairs make the theorem applications and box argument literal:

1. In Theorem 2, require differentiability on a neighborhood of \(D\) and
   quasiconvexity on \(D\). Its proof already proves this stronger statement.
   Quasiconvexity on a whole neighborhood, as the current wording can require,
   is not supplied by Corollary 3 or by the quadratic convexification, which
   are only quasiconvex or convex on the closed box.
2. In the Q-solvability paragraph, restrict the perturbation parameter to
   \(0<t<1\), or use \(t_m=1/(m+2)\) from the outset. The assertion that
   \(q_t=(1-t)x+tR_k\) is coordinatewise at most \(b\) does not follow for
   arbitrary \(t>0\). Only \(t\downarrow0\) is used, so this does not impair
   the proof.

Also make explicit that Corollary 3 is about differentiable potentials; the
polynomial application automatically has this regularity. The formulas
in Sections 5–6 use a \(C^2\) potential on a neighborhood of \(C\).

The packet's Q hypothesis is unnecessary for its **full-relation polynomial
quasiconvex exclusion**, though the matrix-only theorem retains it. A short,
independently checked combination with an existing global-minimum argument is
proved in
[CODEX_ALEXANDROV__QUITTING_POTENTIAL_EXCLUSION_REVIEW.md](../notes/CODEX_ALEXANDROV__QUITTING_POTENTIAL_EXCLUSION_REVIEW.md).
This is a scope/strengthening correction, not a counterexample to the stated
weaker result. It should inform the final description of what is established.

### Independent check of the exact HADAMARD strengthening note

I read the complete
[CODEX_HADAMARD__FULL_RELATION_QUASICONVEX_SCOPE_AUDIT.md](../notes/CODEX_HADAMARD__FULL_RELATION_QUASICONVEX_SCOPE_AUDIT.md)
and independently checked its exact statement and proof. **It passes.**
Unlike my sufficient formulation using the outer relation, that note assumes
exact-edge drift only for sources in \(K'=[-M-1,M+1]^n\). Its additional
upper-coordinate repair is valid and closes this domain distinction.

Write \(L=M+1\). At a face point \(x\), freeze each upper nonowner coordinate
at \(v_j^h=L\); then its Continue-minus-Quit payoff is
\((1-h)(L-s_j)-h\Delta_j\), which stays positive for sufficiently small
\(h\), since \(L-s_j\ge1\). At every nonupper coordinate the original
collision-premium lift fits within the fixed positive margin \(L-x_j\)
for small \(h\). There are finitely many coordinates, so one small-\(h\)
range satisfies all bounds and Nash inequalities simultaneously. The target
stays in \(K'\) by convexity, and the fixed upper/nonupper choice gives an
order-\(h\) source adjustment that cancels in the derivative calculation.

The note's remaining minimum-location and strict-interior quasiconvex steps
are exactly the valid composition checked above. Its assumptions of
continuity on \(K'\), differentiability near \(C\), universal exact root drift,
and quasiconvexity on \(C\) suffice; no Q assumption is used. This independent
review approves the mathematics of that internal note, not an export or any
claim that the quitting conjecture is settled.

## Proposition 1: orientation, Nash test, and differentiability

The claim uses all finite coalition rewards, independent mixed root actions,
ordinary one-stage Nash regret against the source continuation, and every
boxed robust edge. It does not require the source to be a behavioral payoff,
or insert a punishment floor. These quantifiers are essential and match the
inspected relation.

Fix a face point \(x_i=s_i\), put \(d_i=0\), and for \(j\ne i\) set
\(d_j=(r_j(\{i,j\})-r_j^i)_+\). With only \(i\) quitting at hazard \(h\),
the two endpoint values for \(i\) are \(s_i\). For \(j\ne i\), the exact
Continue-minus-Quit value is

\[
(1-h)(x_j-s_j)+h\bigl(d_j-r_j(\{i,j\})+r_j^i\bigr)\ge0.
\]

Thus the proposed root against \(v_h=x+h d/(1-h)\) is exactly Nash,
including at intersections of lower faces with profitable joining collisions.
Its target is \(u_h=(1-h)v_h+hr^i\), and its absorption is exactly \(h\).
The robust target \(u_h+\tau h e\), with \(e\in[-1,1]^n\), has residual
at most \(\tau h\) and zero Nash defect. The positive margin between \(C\)
and the boundary of \(K\) ensures both endpoints lie in \(K\) for small \(h\).

The expansions making the cancellation rigorous are

\[
v_h=x+hd+O(h^2),\qquad
u_h+\tau he=x+h(d+r^i-x+\tau e).
\]

Differentiability at the single point \(x\) suffices to subtract the two
Taylor expansions, divide by \(h\), and obtain
\(\nabla P(x)\cdot(x-r^i-\tau e)\ge1\).
No continuity of the gradient is needed for Proposition 1. Choosing
\(e_j=\operatorname{sign}(\partial_jP(x))\) gives exactly the plus sign
\(+\tau\|\nabla P(x)\|_1\) on the right of (3).

The bound \(\|x-r^i\|_\infty\le2M+1=W\) and
\(W-\tau\ge3/4>0\) give both inequalities (4), with
\(c=W/(W-\tau)\). The source-minus-target orientation is correct.

An exact small collision test confirms why the correction matters. Take
two players, \(r^1=(0,-1)\), \(r^2=(-1,0)\), \(r^{12}=(1,1)\), and
\(x=(0,0)\). For owner 1 and \(h=1/4\), the corrected continuation is
\(v=(0,2/3)\), the target is \(u=(0,1/4)\), and player 2's pure Continue
and Quit payoffs both equal \(1/4\). The uncorrected continuation \(x\)
would give that player a strictly profitable joining deviation. This is a
probe sanity test, not a claim that the table has a standard-Q matrix or a
potential.

## Theorem 2: boundary and compactified-LCP attack

The exact analytic hypotheses are a zero-diagonal standard-Q matrix \(R\),
positive side lengths \(b_j\), strict bounds \(R_{ji}<b_j\), and a function
differentiable near \(D=\prod_j[0,b_j]\), quasiconvex on \(D\), with strictly
positive drift \(g(x)\cdot(x-R_i)\) on every corresponding lower face.

The first-order quasiconvex consequence (5) is valid even at a boundary
point: apply quasiconvexity along the segment from \(x\) to \(v\), then
take its right derivative at \(x\). Only values on \(D\) are used.

At a minimum \(x\) on the union \(B\) of lower faces, a unique zero
coordinate \(i\) leaves all other coordinates freely variable locally within
that face. Their derivatives vanish at interior coordinates and are
nonpositive at upper coordinates. Since \(b_j-R_{ji}>0\), their drift
contributions are nonpositive, and the own contribution is zero. Thus the
minimum must have at least two zero coordinates.

At such an intersection, every one-coordinate inward variation remains in
\(B\). Consequently the displayed signs (7) are valid also at upper box
faces. The gradient is nonzero by the strict face drift. Every component of
\(g\cdot(v-x)\) is nonnegative for \(v\in D\), and at least one is
strictly positive for \(v\in\operatorname{int}D\). A point with a lower
function value can be moved into that strict interior by continuity. Formula
(5) then contradicts the strict scalar-product inequality. This verifies
that \(x\) is a global minimum on all of \(D\) without assuming an interior
critical point or continuous derivatives.

Now choose \(k\in J\) and \(t\in(0,1)\). Projectivizing a finite standard
LCP solution gives \(a_{0,t}>0\), nonnegative weights summing to one, and

\[
y_t=a_{0,t}q_t+\sum_j a_{j,t}R_j\ge0,\qquad
a_{j,t}y_{t,j}=0.
\]

The components of \(q_t\) and every column \(R_j\) are at most \(b\), so
\(y_t\in D\). If every positive singleton weight belonged to \(J\), the
scalar product with \(g=\nabla f(x)\) would be strictly negative: the
\(a_{0,t}t\) coefficient is strictly positive, and every supported column
direction has negative product. This contradicts the signs at \(x\).

Therefore for every \(t\) some outside index \(i\notin J\) has positive
weight. Pass first to a sequence with one fixed such index and then to a
convergent subsequence in the compact product of \(D\) and the weight
simplex. The original LCP solutions \(z_t,w_t\) need not be bounded.
Although the selected weight may vanish in the limit, its corresponding
coordinate satisfies \(y_{t,i}=0\) at every step, so \(y_i=0<x_i\) remains
true. Hence \(y\ne x\) and the total limiting singleton weight is positive.

Complementarity survives by continuity. At \(y\), each positive limiting
singleton weight therefore multiplies a strictly positive face drift.
Global minimality of \(x\) and quasiconvexity give
\(\nabla f(y)\cdot(y-x)\ge0\). The final identity in the packet is a
sum of these nonnegative terms with at least one strictly positive term,
yet it equals zero. The case \(a_0=0\) is included. No continuous LCP
selection, nonvanishing limit for the selected index, or principal-Q
property is needed.

The strict signs are indispensable to this argument: zero drift would permit
a constant function. Standard Q is stronger than the weak simplex condition
\(Rz\ge0\); the latter alone is not the hypothesis used for this proof.

## Rational witness and negative curvature

For rational reward entries, rational \(M\), and a rational polynomial
candidate \(P\) quasiconvex on \(C\), the analytic theorem under standard Q
supplies a lower-face point whose drift is nonpositive. The drift is a
continuous polynomial. Rational points are dense on that same closed face,
including near intersections and upper corners, so one can select a rational
point with drift \(<1/2\). Its own coordinate remains exactly the rational
singleton reward.

For any rational \(h\in(0,1)\), the corrected \(v_h,u_h\) are rational and
the root probabilities are rational. Choose \(h\) small enough that the
endpoints lie in \(K\) and the exact drift quotient is \(<3/4\). The
resulting exact finite edge violates unit absorption drift by \(>h/4\).
There is no positive-tolerance or rational-LCP-solution requirement here.
The argument proves existence of a finite rational witness; it does not give
an explicit denominator bound. Enumerating rational face points and small
rational hazards is consistent with the proof, but is not a general
algorithm for deciding all proposed polynomial certificates.

For the curvature argument, \(C^2\) regularity near compact \(C\) makes the
minimum Hessian eigenvalue attain its minimum \(m\). With
\(\delta=\max(0,-m)\), the Hessian of
\(Q(x)=P(x)+(\delta/2)\|x-s\|_2^2\) is positive semidefinite on \(C\),
so \(Q\) is convex on \(C\). This is why the box-only repair to Theorem 2
matters; no convexity of \(Q\) outside \(C\) has been shown or is needed.

On \(x_i=s_i\), \(y=x-s\ge0\) gives

\[
\nabla Q(x)\cdot(x-r^i)
\ge c+\delta\sum_{j\ne i}y_j(y_j-R_{ji})
\ge c-\delta A.
\]

The estimate \(y_j(y_j-R_{ji})\ge-(R_{ji})_+^2/4\) is exact on the
nonnegative half-line. Standard Q at the right-hand side \(-\mathbf1\)
gives \(Rz\ge\mathbf1\), so a positive off-diagonal entry exists and
\(A>0\). Thus \(\delta A<c\) would contradict the repaired Theorem 2.
It follows that \(\delta A\ge c>0\), hence \(m=-\delta\le-c/A\).
The non-strict endpoint inequality is correct; the proof gives no strict
bound at equality. Finally \((R_{ji})_+\le2M\) gives exactly
\(A\le(n-1)M^2\) and the stated simpler bound.

## Bounded declaration and source inventory

The route was selected through `docs/TOOLKIT.md`'s full robust relation and
rational-potential characterization. The exact declarations read include:

- `IsQuittingFloorFreeRobustEdge`, `quittingFloorFreeRobustChargedRelation`,
  and its residual/regret definitions
  (`UniformEquilibrium/Quitting/Projective/RobustChargedRelation.lean`).
  Both endpoints are arbitrary boxed vectors. Regret uses the source.
- `ChargedRelation.IsPotential` (`MathUE/ChargedPathBudget.lean`), namely
  potential at target plus charge is at most potential at source.
- `quittingRootCoordinateNashDefect` and
  `isεQuittingRootNash_iff_coordinateNashDefect_le`
  (`UniformEquilibrium/Quitting/Root/NashDefect.lean`), and the payoff
  definitions in `UniformEquilibrium/Quitting/Root/SuccessorCertificate.lean`.
- `quittingGame_not_exists_uniformEquilibriumPayoff_iff_noSureRoot_and_rationalPotential`
  (`UniformEquilibrium/Quitting/Projective/PolynomialForwardCertificateCharacterization.lean`).
  It requires `Fin 4`, a bound on every terminal reward, normality of every
  player, and at least one positive own singleton. It supplies no sure root
  and one rational polynomial at an existential positive rational tolerance
  at most \(1/4\), with the full relation on radius \(M+2\).
- `StandardLCPSolution`, `IsStandardQMatrix`, and
  `isStandardQMatrix_reindexMatrix`
  (`UniformEquilibrium/Quitting/Classification/LCP/MatrixClasses.lean`);
  `StandardQMatrixSide`
  (`UniformEquilibrium/Quitting/Classification/LCP/Gate.lean`); and
  `standardQMatrixSide_of_not_exists_uniformEquilibriumPayoff`
  (`UniformEquilibrium/Quitting/Classification/LCP/CounterexampleNecessary.lean`).
  This gate initially supplies Q on the recursively defined normal core.
- `normalCore_eq_univ_of_fourPlayer_not_exists_uniformEquilibriumPayoff`
  (`UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/AmbientCarrierElimination.lean`),
  `fullNormalCoreEquiv` and
  `reindex_normalPlayerMatrix_fullNormalCoreEquiv`
  (`UniformEquilibrium/Quitting/Classification/LCP/FullNormalCoreHomogeneousTransfer.lean`).
  These and standard-Q reindexing justify passing to the ambient matrix.
- `normalizedSoloMatrix_eq_projectiveLCPMatrix`
  (`UniformEquilibrium/Quitting/Classification/LCP/Normalization.lean`),
  `normalizedNormalPlayerMatrix`
  (`UniformEquilibrium/Quitting/Classification/LCP/NormalCore.lean`), and
  `quittingProjectiveLCPMatrix`
  (`UniformEquilibrium/Quitting/Projective/SingletonLCP.lean`). Their
  receiver-row, quitter-column orientation is exactly
  \(R_{ji}=r_j(\{i\})-s_j\), with no change to the game's Never payoff.
- `exists_isZeroQuittingRootNash`
  (`UniformEquilibrium/Quitting/Root/NashExistence.lean`) for the separately
  recorded no-Q full-relation strengthening.

`FourPlayerSingletonColumnBlockers.lean` was also inspected at its named
counterexample theorem; it corroborates the full-core use but is not needed
to prove the analytic claims. A narrow phrase search for quasiconvexity,
separability, and negative curvature in the selected projective/LCP and
interval source neighborhoods produced no matching declaration. This is
not a novelty claim.

The bounded literature check read `Literature/README.md` and the Remark 2.9
and Definition 2.10 transcription in `Literature/SolanAndSolan2020.lean`.
That transcription explicitly distinguishes textbook LCP from the paper's
projective Q definition. No paper theorem is an input to this review, and
no original-paper audit or literature-wide novelty conclusion is claimed.

The two local theorem repairs concern the perturbation interval and the
quasiconvexity domain. The stronger full-relation corollary has the explicit
regularity hypotheses recorded above. These claims restrict potential shape
and do not settle the quitting conjecture or exclude arbitrary polynomials.
