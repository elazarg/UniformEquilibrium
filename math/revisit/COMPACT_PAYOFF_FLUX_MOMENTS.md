# A compact moment problem for four-player quitting equilibria

This is a convex dual of the project's checked rational-polynomial characterization. It removes its unknown relative tolerance and gives the exact contribution of vanishing quit rates. It applies to the following residual branch. Assume all four players are punishment-normal, at least one original own singleton reward is positive, and the game has no winning sure opening at its punishment vector. These conditions are necessary for an original counterexample and have project dispositions on their complements. For this branch the question is whether a compact family of elementary moment vectors contains zero in its convex hull at each polynomial degree.

Write r(S) for each original finite nonempty exit reward vector, s_i=r_i({i}), and choose B≥1 bounding every absolute reward. Live and Never pay zero. Set K=[−B−2,B+2]^4, the fixed box of the prior theorem. Coordinates w∈K are trial continuations. A product row q∈[0,1]^4 is independently randomized. Let c(q)=∏(1−q_i) and A(q)=1−c(q), and let F(w,q) be the sum of the original one-date exit contributions plus c(q)w. In row i write Q_i for the forced-Quit offer, P_i for the forced-Continue exit contribution with no reward on survival, and H_i=∏_(j≠i)(1−q_j). Its one-stage regret is

    d_i(w,q)=max(Q_i,P_i+H_i w_i)−F_i(w,q).

Define a compact set E of triples (w,a,z), with w∈K, 0≤a≤4, z in the four-coordinate probability simplex and az∈[0,1]^4. Impose one of the following conditions.

* If a>0, require d_i(w,az)=0 for every i.
* If a=0, require w_i≥s_i and z_i(w_i−s_i)=0 for every i.

Write L_P for the following function of these triples, for any real polynomial P on K:

    L_P(w,a,z)=[P(F(w,az))−P(w)]/a                   if a>0,
    L_P(w,0,z)=∇P(w)·Σ_j z_j(r({j})−w)                if a=0.

This is one polynomial in the coordinates after removal of the factor a. Indeed F(w,az)=w+a Σ_j z_j(r({j})−w)+O(a²) identically to first order. For D≥1, set G_D=(L_(w^α))_(1≤|α|≤D). Its dimension is m_D=binomial(D+4,4)−1.

**Criterion.** The original game has a uniform-equilibrium payoff exactly when, for every D≥1, zero belongs to the convex hull of G_D(E). Equivalently a single Borel probability ρ on E satisfies ∫L_P dρ=0 for every polynomial P. The measure has total mass exactly one, including when all its mass is on the zero-rate faces. Every degree test is finite over rational or real algebraic input: it asks for at most m_D+1 points of an explicit compact semialgebraic set and nonnegative weights with sum one. The number of unknown moments and atoms can grow with D. This argument supplies no universal degree cutoff.

## The zero-rate stratum and compactness

For a>0 the step charge satisfies a/4≤A(az)≤a by the maximum-hazard and union bounds. Suppose a sequence has a>0, converges to a point with a=0, and max_i d_i(w,az)/a→0. As q→0, Q_i→s_i and P_i+H_i w_i→w_i (using the limiting w). A strict w_i<s_i would give a positive limiting regret. If w_i>s_i, waiting is eventually strictly better, so d_i/a=z_i[(P_i+H_i w_i)−Q_i]. Thus z_i=0 in the limit on every such row. This proves that E is closed even under relative approximate Nash limits. It is bounded and semialgebraic.

Conversely every indicated zero-rate point is a limit of exact positive-rate rows in the same box. Fix z and set q=az for small a>0. Let t_i=(Q_i−P_i)/H_i, which is defined for proper q and tends to s_i. For z_i>0 set w_i(a)=t_i, making the prescribed actions indifferent. For z_i=0 set w_i(a)=max(w_i,t_i), making the prescribed Wait optimal. This converges to w. The extra room in the fixed box around every s_i keeps all coordinates in K, including if a quiet coordinate originally lay at the upper endpoint. Hence all points of E can be used in the normalized-increment inequality. The conditions at a=0 explicitly exclude the uninformative all-Continue self-loops with w_i>s_i for every i.

## Equivalence and the original endpoint

The exact earlier theorem is `quittingGame_not_exists_uniformEquilibriumPayoff_iff_noSureRoot_and_rationalPotential` in `UniformEquilibrium/Quitting/Projective/PolynomialForwardCertificateCharacterization.lean`. In the branch stipulated above it says that no UE is equivalent to some rational τ∈(0,1/4] and a rational polynomial P with P(w)−P(u)≥A(q) for all w,u∈K, all q, whenever each d_i(w,q)≤τA(q) and ||u−F(w,q)||∞≤τA(q). Its conclusion concerns the original fixed target, independent private behavioral play, literal Never, and arbitrary unilateral behavioral replacement at all sufficiently large horizons.

If such a certificate exists, take u=F(w,az) at each exact positive-rate row. Then L_P≤−A/a≤−1/4. The same bound holds on the whole zero-rate stratum by the exact approximation just proved. Integrating is impossible under a probability annihilating every L_P. Already at the degree of P the coefficient vector of P separates zero strictly from the convex hull of G_D(E).

Conversely, suppose zero lies outside this convex hull at some D. It is compact and convex, so finite-dimensional strict separation gives a real polynomial P and a constant c>0 with L_P≤−c throughout E. Rational approximation of its coefficients preserves a strict bound, since all components of G_D are bounded on E. Keep P rational, and shrink c if needed. Some positive relative tolerance τ_0 guarantees L_P≤−c/2 at all a>0 with d_i(w,az)≤τ_0 A(az). Otherwise, by choosing tolerances tending to zero and taking a compact subsequence, a positive limiting a gives an exact Nash row, and at a=0 the relative-regret argument above supplies its stated face constraints. Polynomial continuity contradicts the strict bound in either case. For any perturbed successor with ||u−F||∞≤τA, the possible loss in the drop of P is at most Lip(P)τA on K. Choose a rational positive τ≤min(τ_0,1/4) small enough that this is at most cA/4. Multiplying P by an integer at least 4/c gives the earlier robust unit-charge certificate. At a=0 we have A=0 and u=F=w, so the certificate holds there as well. The checked equivalence gives no original UE.

Finally, when all finite-degree convex hulls contain zero, Carathéodory gives a finitely supported probability on E annihilating each finite list. In the space of Borel probabilities on compact E the annihilation conditions are weakly closed, nonempty and nested as D increases. Their intersection gives the stated single probability. Conversely any such probability puts the integral of each G_D in its compact convex hull. This proves the criterion without a stationarity or period restriction on the desired equilibrium.

## Restricting the test to feasible, individually rational continuations

Let H be the convex hull of the fifteen original exit vectors r(S). Let μ_i be the original upper punishment value, the infimum over opponents' strategies of i's best unilateral payoff. Replace E in the criterion by its compact subset

    E*={ (w,a,z) in E : w belongs to H and w_i≥μ_i for every i }.

The all-degrees conclusion is unchanged. In fact every annihilating unit probability on E is supported on E*. Moreover on this restricted set there is a game-dependent η>0 such that az_i≤1−η for all i. Thus the finite-degree convex problems can be posed entirely on the original payoff polytope with proper action rows. For algebraic input the μ_i are real algebraic: the checked declaration `quittingPunishmentValue_eq_stationaryPunishmentValue` in `UniformEquilibrium/Quitting/Stationary/MinMax.lean` gives the infimum of max(Q_i,P_i/(1−H_i)) over stationary rival rows with H_i<1, also considering max(s_i,0) at the all-Continue row. The finite search concerns the precise full-deviation value.

To prove the hull assertion fix a linear functional ℓ, put h=max_S ℓ(r(S)), and choose C large enough that C+ℓ(w)>0 on K. For a>0 write F=(1−A)w+A r̄, with r̄∈H the conditional mean exit reward. By convexity the polynomial P_m(w)=(C+ℓ(w))^{2m}, m≥1, satisfies

    L_(P_m) ≤ (A/a)[(C+h)^{2m}−(C+ℓ(w))^{2m}].

At a=0 the analogous inequality holds with coefficient one by the supporting-tangent inequality for a convex function, since Σz_j r({j})∈H. Each coefficient lies between 1/4 and one. If ρ annihilates all polynomial increments, integration bounds the integral of (C+ℓ(w))^{2m} by 4(C+h)^{2m}. Taking m to infinity shows ℓ(w)≤h almost surely. A countable dense family of ℓ gives w∈H almost surely.

For each i and fixed rival row, immediate Quit and Wait with continuation μ_i have maximum at least μ_i. Indeed attach a tail with best-response cap at most μ_i+ε to that rival row on survival. The defining infimum μ_i is at most the resulting one-stage maximum; let ε decrease to zero. Consequently at a positive-rate exact row the deficit (μ_i−w_i)^+ after the step satisfies (μ_i−F_i)^+≤H_i(μ_i−w_i)^+. Whenever w_i<μ_i and some rival is active, H_i<1, so the new deficit is strictly smaller than (μ_i−w_i)^+. If all rivals are inactive, q_i>0. Since normality gives μ_i≤s_i and w_i<μ_i, optimality requires i to quit for sure, giving F_i=s_i. At zero rate the source already satisfies w_i≥s_i≥μ_i. For f(t)=((μ_i−t)^+)² the increment therefore has nonpositive sign everywhere and is strictly negative whenever w_i<μ_i. Its integral is zero: uniformly approximate its continuous derivative on the coordinate interval by polynomials and integrate those approximants. The quotients |F_i−w_i|/a are uniformly bounded, and the zero-rate derivatives are bounded by the same finite reward-and-box bound. Thus the normalized increments converge uniformly. This proves w_i≥μ_i almost surely. In particular one need never assume tangent rows can be approximated by positive rows while staying in the reduced polytope.

Finally if an exact row at w≥μ has a sure mover, it remains Nash when continuation is decreased to μ. Every player facing a sure rival has its two stage payoffs independent of the continuation. For a sole sure quitter only its Wait offer can decrease. This would be a winning sure opening, excluded by hypothesis. Compactness now gives the uniform bound away from one on E*. For each D, finite witnesses and compactness apply directly to this new set. Feasibility of every degree on E implies the existence of a single annihilating ρ and hence feasibility of every degree on E*. This does not assert equivalence of the two tests at a single degree.

## What this adds to the existing potential theorem

The polynomial certificate for nonexistence, the exclusion of quadratics and multi-affine polynomials under their own normalization, and the feasibility of finite numerical quantile tests are prior results. This argument supplies a dual feasibility problem with an attained unit probability, permits mass both on finite genuine Nash moves and on the specified zero-rate states, and gives explicit exact raw tests at each degree. No occupation measure is used as a correlation device in the game. The semantic equivalence is the existing polynomial theorem. A solution of the conjecture by this route would prove feasibility at all degrees on every residual table or exhibit one residual table and degree with infeasible moment equations. No such resolution is asserted.


Earlier single-owner face probes appear in `QUITTING_POTENTIAL_SHAPE_EXCLUSIONS.md`. The note `CODEX_EMMY_BOX__OPPONENT_COINCIDENCE_BARRIER.md` and its cubic checker balance a finite list of monomial increments on one explicit table. The general relation above includes both of these mechanisms and allows all degrees on the intrinsic payoff domain. As a check, on the older normalization |r_i(S)|≤1 and s_i≥0, with K=[−3,3]^4, the old quadratic exclusion in `REFLECTION_AND_MULTIAFFINE_POTENTIAL_EXCLUSIONS.md` implies that the enclosing-box test at degree two always passes: a strict separating polynomial could be scaled to charge all exact rows, which that result excludes. The same reasoning applies separately to the list of all square-free monomials. These conclusions about the enclosing box do not require a conjectured uniform equilibrium.
