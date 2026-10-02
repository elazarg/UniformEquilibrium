# Potential-guided anchors still collapse to zero charge

Author: CODEX_FRECHET_CYCLE.

Status: completed bounded test of one potential-dependent construction.
Every solution of the tested feedback equations is zero-charge at small
discount, and an explicit such solution always exists. This returns to the
already recorded all-anchor minimizer obstruction; it excludes no new reward
table or polynomial class and produces no equilibrium or sure-root exit.
No export, further degree search, or constant optimization is proposed.

## 1. Literal global certificate and the proposed construction

Fix Fin4 reward data r, a coordinate reward bound M, and B=M+2. Write
K=[−B,B]^4, s_i=r_i({i}), and, for product hazards q,

    a(q)=1−∏_i(1−q_i),
    F(q,v)=Σ_{S≠∅}p_q(S)r(S)+(1−a(q))v,
    e_i(q,v)=max(Q_i(q),C_i(q,v))−F_i(q,v).

Suppose the supplied rational polynomial H satisfies the UNIVERSAL robust
inequality at some δ>0:

    v,w∈K,  ||w−F(q,v)||∞≤δa(q),  e_i(q,v)≤δa(q) ∀i
        ⇒ H(v)−H(w)≥a(q).                             (R)

The argument uses the entire robust admissibility condition as written,
not a chosen path or a presumed stationary equilibrium. It does not require
H to be convex or impose any Hessian sign. Normality and a positive singleton
are needed for the global no-UE characterization, not for the calculation
below once (R) is supplied.

The tested operation uses H itself to choose the anchor. For η>0 define

    T(v)=Proj_K(v−η∇H(v)).

This is a concrete continuous projected-gradient map, not an unspecified
favorable anchor selector. Given λ∈(0,1), seek a robust edge as in (R)
satisfying the feedback equation

    v=(1−λ)w+λT(v).                                  (A)

An absorbing solution would supply a potential-dependent charged root.
This formulation even allows both Bellman discrepancy and ordinary root
regret up to δa; it does not restrict the proposed source to exact Nash
edges. No existence theorem for this endogenous-anchor system is imported.
Its nonempty zero-charge solution set will instead be exhibited directly.

## 2. Every solution is zero-charge

Choose L≥1 bounding the Euclidean operator norm of the Hessian of H on K.
Such a finite L exists because H is a polynomial and K is compact. Assume

    κ=λ/(1−λ)≤1/(ηL).

Let (v,q,w) solve (R)'s edge conditions and (A), and put d=v−T(v).
Metric projection onto the convex box, tested against the competitor v,
gives

    ⟨v−η∇H(v)−T(v), v−T(v)⟩≤0,
    ∇H(v)·d≥||d||²/η.                                (1)

Equation (A) says w−v=κd. The whole segment from v to w lies in K.
Taylor's inequality, with no convexity assumption, therefore gives

    H(w)−H(v)
      ≥κ∇H(v)·d−(Lκ²/2)||d||²
      ≥(κ/(2η))||d||².                               (2)

But (R) gives H(w)−H(v)≤−a(q). Both a(q) and the last expression in
(2) are nonnegative. Consequently

    a(q)=0,      d=0,      w=v=T(v).                  (3)

Every hazard is zero. At q=0 the robust tolerances vanish exactly, and
the ordinary Nash-regret inequalities become

    max(s_i−v_i,0)≤0,

so v_i≥s_i for every i. Conversely, ANY projected stationary point
T(v)=v in K with v≥s supplies the coupled solution q=0,w=v. Thus, at
the stated discount, the entire solution set consists exactly of these
neutral points. This is not a failed numerical continuation or a statement
only about one chosen solution branch.

## 3. The neutral solution set is nonempty

Let z be a global minimum of H on K. The existing finite root-game Nash
theorem supplies an exact Nash root q against z. Since F(q,z)∈K,
minimality and the exact special case of (R) imply

    0≤a(q)≤H(z)−H(F(q,z))≤0.

Hence q=0 and z≥s. First-order minimum optimality on the convex box gives
∇H(z)·(u−z)≥0 for every u∈K, which is exactly the projection criterion
T(z)=z. Therefore (z,0,z) solves the coupled problem for EVERY λ∈(0,1),
not only for the small discounts used in Section 2.

No claim is made that z is a realizable terminal payoff. The root is not
a sure-quitter certificate. The robust seam cannot eliminate it: at zero
charge both allowed errors are exactly zero, and this profile satisfies
those exact conditions already.

## 4. Source correspondence and stopping point

I selected the route through `docs/TOOLKIT.md` and read the complete literal
declaration
`quittingGame_not_exists_uniformEquilibriumPayoff_iff_noSureRoot_and_rationalPotential`
in `UniformEquilibrium/Quitting/Projective/PolynomialForwardCertificateCharacterization.lean`.
For normal Fin4 data and a positive singleton, it states no uniform payoff
iff no punishment-vector sure root AND a rational potential on every robust
edge in the fixed M+2 box, at a positive rational tolerance at most 1/4.
The sure-root exclusion remains a separate conjunct.

`IsQuittingFloorFreeRobustEdge` and
`quittingFloorFreeRobustChargedRelation` in
`UniformEquilibrium/Quitting/Projective/RobustChargedRelation.lean` define
the full source/root/target relation used in (R).
`ChargedRelation.IsPotential` in `MathUE/ChargedPathBudget.lean` supplies
the orientation H(target)+charge≤H(source).
`exists_isZeroQuittingRootNash` in
`UniformEquilibrium/Quitting/Root/NashExistence.lean` is the finite-game
existence input in Section 3, not undiscounted stationary existence.
The worktree advanced externally to HEAD
`3c6d97aae7f96dcc2e019ee976ea8c6ba014ecf4` during this inspection; no
fresh Lean build or source edit was performed.

The complete earlier notebooks
`CODEX_FRECHET_CYCLE__POLYNOMIAL_ALL_ANCHOR_DISCOUNTED_NASH_TEST.md` and
`CODEX_FRECHET_CYCLE__NONPOSITIVE_DIAGONAL_QUADRATIC_ROOT_DRIFT_EXCLUSION.md`
were reread. Their all-minimizer neutral point is exactly Section 3's
existing obstruction. The present calculation merely verifies that this
specific nonlinear H-guided feedback does not escape it: indeed every
small-discount solution collapses to the same boundary. It neither extends
the quadratic exclusion nor supplies a table condition stronger than the
existing standard-Q consequence.

The method is stopped. A source that only invokes existence for (A) has
already satisfied its obligation at zero charge. Requiring an absorbing
solution as an additional field would assume the missing conclusion.
