# A cyclic three-player child with one joint phase

## Raw reward class and uniform conclusion

There are four players I={0,1,2,3}. At each live date they independently
choose Quit or Continue. The first nonempty quitting coalition S absorbs
at its finite real reward vector r(S); live reward and perpetual-continuation
reward are zero. Strategies may use private independent randomization and
the public history. A deviation replaces one player's complete behavioral
strategy. No public correlating device is added.

Let a,b,c,h_1,h_2,h_3>0, D=abc−1>0, xi,eta>0, q_2,q_3≤0, and

    v<1,                    u≤1+xi,                    R∈ℝ.

Prescribe the following five reward vectors:

    r({0})   = (1,−h_1,−h_2,−h_3),
    r({1})   = (u,0,b,−1),
    r({2})   = (v,−1,0,c),
    r({3})   = (R,a,−1,0),
    r({0,1}) = (1+xi,eta,q_2,q_3).                     (1)

The only additional restrictions are six participant-reward caps:

    r_2({0,2}), r_2({1,2}), r_2({0,1,2})≤0,
    r_3({0,3}), r_3({1,3}), r_3({0,1,3})≤0.            (2)

Every unspecified reward coordinate is arbitrary. In particular, both
players 2 and 3 may have positive participant premiums at {2,3}, and
players 0 and 1 may have arbitrary finite participant rewards at pairs
involving a solo player. No bound on eta is imposed.

**Theorem.** Every table satisfying (1)–(2) has a uniform-equilibrium
payoff. There is one vector V such that for every ε>0 some behavioral
profile and some integer N deliver V within ε at every horizon n≥N,
and every complete unilateral behavioral replacement improves that
player's expected n-date average payoff by at most ε.

The target precedes ε; the profile and threshold may depend on ε.
The proof treats every real R. In the middle region it constructs one
fixed-target joint/solo cycle and arbitrarily accurate independent
refinements. Existing original-game singleton criteria handle the two
outer regions and their equality boundaries. The conclusion does not
assert that the same controller or target is used across those regions.

## 1. Exact singleton thresholds

Write s=(1,0,0,0) for the singleton vector, and put σ₁=1−u,
σ₂=1−v>0. These two deficits are distinct from the coordinates of s. Set

    nu = (ac*h_2+c*h_1+h_3,
          ab*h_3+a*h_2+h_1,
          bc*h_1+b*h_3+h_2)/D.

All entries of nu are positive, and

    a*nu_3−nu_2=h_1,
    b*nu_1−nu_3=h_2,
    c*nu_2−nu_1=h_3.                                   (3)

Define

    L=ac+a+1,
    R_low=1+(σ₁*nu_1+σ₂*nu_2)/nu_3,
    T_1=1+(c*σ₁+σ₂)/(bc),
    T_2=1+ac*σ₁+a*σ₂,
    T_3=1+(σ₁+ab*σ₂)/b,
    T_pass=max(T_2,T_3),
    Y=D/(bL),
    R_top=T_2+xi*D/b.                                  (4)

Here 0<Y<c/(c+1)<1. The receiver-first singleton-difference matrix
of the child on {1,2,3} is

    A=[[0,−1,a],[b,0,−1],[−1,c,0]],
    A^(-1)=[[c,ac,1],[1,a,ab],[bc,1,b]]/D.              (5)

Its inverse is strictly positive. The pivot's difference row times this
inverse is exactly

    (−σ₁,−σ₂,R−1)A^(-1)
      =[bc*(R−T_1), R−T_2, b*(R−T_3)]/D.              (6)

Since

    T_3−T_1=D*σ₂/(bc)>0,
    T_2−T_3=D*σ₁/b,

all three weights in (6) are nonnegative exactly when R≥T_pass.
The lower threshold is strictly smaller than T_pass. If σ₁≥0, then

    T_2−R_low=[(c*σ₁+σ₂)h_1+σ₁*h_3]/nu_3>0.

If σ₁<0, then instead

    T_3−R_low=[σ₂*h_1−σ₁*h_2/b]/nu_3>0.               (7)

Finally, if σ₁≥0, then R_top>T_pass=T_2. If σ₁<0, then

    R_top−T_pass=D*(1+xi−u)/b≥0.

Thus the whole asserted raw class satisfies

    R_low<T_pass≤R_top.                                (8)

No positivity of σ₁ or c*σ₁+σ₂ has been assumed.

## 2. Produce the nonpivot balance by a quadratic root

For 0≤y≤Y put

    H_j(y)=h_j*(1−y)−q_j*y>0,              j=2,3.

For 0<y<Y and 0≤k≤K(y), define

    K(y)=min(by/H_2(y), [c−(c+1)y]/H_3(y)),
    z=(H_3(y)k+y)/[c(1−y)],
    d=1+by+[1−H_2(y)]k,
    w=[by−H_2(y)k]/d,
    p=1+xi*y.                                          (9)

The denominator is d=1+k+by−H_2*k≥1+k>0. Throughout this closed
interval 0≤z,w≤1; in its interior 0<z,w<1. At k=K(y), either w=0
or z=1. Set

    G(k,y)=h_1*k+z−a*w*(1−z)
            +eta*k*[1−(1−z)(1−w)/(1+k)].               (10)

The nonpivot balance will be G=0. It need not be monotone in k.
Instead put C=c(1−y), E=c−(c+1)y, d_0=1+by, d_1=1−H_2(y).
Its positive-denominator numerator is a polynomial of degree at most two:

    Q(k,y)=C*d*G(k,y)=alpha(y)k²+beta(y)k+gamma(y),

    alpha=h_1*C*d_1+H_3*d_1−a*H_2*H_3
              +eta*(C*d_1+H_3),
    beta=h_1*C*d_0+H_3*(d_0+ab*y)+y
              +H_2*(a*E−y)+eta*y*(Cb+1),
    gamma=y*(bL*y−D).                                  (11)

The coefficient alpha can be negative, positive, or zero. The coefficient
beta is strictly positive throughout 0≤y≤Y: every displayed term is
nonnegative, and

    a*E−y=ac−L*y≥ac−L*Y=1/b>0.

For 0<y<Y, Q(0,y)=gamma<0. At k=K(y), the term −a*w*(1−z)
in (10) vanishes, h_1*k+z>0, and the eta term is nonnegative. Hence
Q(K(y),y)>0.

A polynomial of degree at most two with these endpoint signs has exactly
one root in (0,K(y)). A linear polynomial has at most one; two distinct
quadratic roots in that interval would give equal signs at the endpoints;
a double root cannot change the sign. The selected root is simple.

Consequently Delta=beta²−4*alpha*gamma is positive for 0<y<Y. It is
also positive at y=0,Y, where gamma=0 and beta>0. The admissible root is

    k(y)=−2*gamma(y)/[beta(y)+sqrt(Delta(y))].            (12)

This is −gamma/beta when alpha=0. Otherwise it is the rationalized
quadratic formula, selecting the smaller positive root if there are two
positive roots; the endpoint signs put that root inside (0,K(y)).
Formula (12) is continuous on [0,Y], with k(0)=k(Y)=0 and
0<k(y)<K(y) for every interior y. No root-selection witness is supplied
as a premise.

## 3. Both endpoint limits and selection of the pivot equation

At y=0, beta(0)=c*h_1+h_3+ac*h_2=D*nu_1 and gamma(y)/y→−D.
Therefore (12) and (3) imply

    k(y)/y→1/nu_1,
    z(y)/y→nu_2/nu_1,
    w(y)/y→nu_3/nu_1>0.                                (13)

At y=Y, k=0 and both limiting z,w lie strictly between zero and one.
For 0<y≤Y define

    P(k,y)=p+
       {(p−u)y/(1−y)+(p−v)z}/[(1−z)w],
    R(y)=P(k(y),y).                                    (14)

The denominator is positive. No sign of its numerator, and no monotonicity
of P or R(y), is needed. Formula (13) cancels the common order-y factor
and continuously extends (14) with

    R(0)=1+(σ₁*nu_1+σ₂*nu_2)/nu_3=R_low.

At k=0, direct algebra gives

    P(0,y)=p+[(c+1)p−cu−v]*(1+by)/[b(c−(c+1)y)].

Substituting Y gives (1+bY)/[b(c−(c+1)Y)]=a and hence

    R(Y)=L*(1+xi*Y)−ac*u−a*v=R_top.                    (15)

The intermediate value theorem supplies an interior y for every
R_low<R<R_top. In particular it supplies every

    R_low<R<T_pass,                                    (16)

by (8). At that point set x=k/(1+k). All four hazards x,y,z,w lie
strictly between zero and one; both G=0 and P=R hold exactly.

## 4. Exact values and all action endpoints

Repeat the three aggregate rows

    (x,y,0,0),              (0,0,z,0),              (0,0,0,w).

Let t=eta*x and define the complete continuation vectors

    V_A=(p,t,w/(1−w),0),
    V_C=((1−w)p+Rw,(1−w)t+aw,0,0),
    V_B=(v*z+(1−z)(V_C)_0,
         (1−z)(V_C)_1−z,
         0,c*z).                                        (17)

The two selected equations imply

    (V_B)_0=(p−uy)/(1−y),
    (V_B)_1=k(h_1+eta).                                (18)

At A, player 0's Quit endpoint is p and its Continue endpoint is
uy+(1−y)(V_B)_0=p. Player 1's Quit endpoint is eta*x and its
Continue endpoint is −h_1*x+(1−x)(V_B)_1=eta*x. The other two
coordinates satisfy the actual policy recurrences

    [by−H_2(y)k]/(1+k)=w/(1−w),
    [−H_3(y)k−y+c*z*(1−y)]/(1+k)=0.                   (19)

These use the original collision rewards q_2,q_3, not rewards from a
linearized singleton game. The B and C recurrences in (17) are exactly
the actual singleton transitions. Every player's pure-Continue endpoint
equals its displayed value, including each supported solo owner, whose
value is zero at both ends of its solo block.

Every nonpivot displayed coordinate is nonnegative. For the pivot,

    (V_A)_0>1,
    (V_B)_0−1=(1+xi−u)y/(1−y)≥0,
    (V_C)_0=[(V_B)_0−v*z]/(1−z)>1.                     (20)

The last inequality uses v<1 and z>0. Equality in the B floor when
u=1+xi is harmless. These calculations do not require R>1 or p−u>0.

At the undiffused joint row, an outsider who Quits can form only its own
singleton or one of the three coalitions listed for it in (2). Its Quit
endpoint is therefore at most zero, bounded by its displayed value.
Both participants are exactly indifferent. These are every pure-action
comparison needed at that row.

## 5. Diffuse only the solo exits

Unspecified participant premiums at solo stages may prevent the unrefined
cycle from being exact Nash. For each integer n≥1 replace the player-2
row by n hazards

    z_n=1−(1−z)^(1/n),

and the player-3 row by n hazards w_n=1−(1−w)^(1/n). Leave the joint
row unchanged. The aggregate survival of each block is unchanged, so
the on-path distribution of the eventual coalition and its payoff V_A
are unchanged for every n.

At a player-2 microstage with remaining aggregate hazard ζ, its value
vector is ζ*r({2})+(1−ζ)V_C. As ζ runs from z to zero these vectors
lie on the segment between V_B and V_C. The analogous player-3 vectors
lie between V_C and V_A. Thus every intermediate value retains its
singleton floor. Each solo owner's coordinate is identically zero
through its own block. Every pure-Continue identity remains exact.

Put

    C_join=max(0, r_i({i,j})−s_i : j∈{2,3}, i≠j),
    e_n=C_join*max(z_n,w_n)→0.                          (21)

At a solo microstage with owner j and hazard λ, a different player's
Quit payoff is

    (1−λ)s_i+λ*r_i({i,j})≤s_i+λ*C_join≤V_i+e_n.

The owner's Quit payoff is its displayed zero. Together with (2), this
proves a uniform pure-Quit cap V_i+e_n at every live date, while every
pure-Continue transition transports V exactly.

One complete behavioral deviation costs e_n, not a sum of errors over
dates. Add e_n to every continuation coordinate. If Continue has immediate
expected absorbed reward b and opponent survival probability q≤1, then

    b+q*(V_next+e_n)=V+q*e_n≤V+e_n.

Quit is also bounded by V+e_n. Thus V+e_n is a Bellman supersolution
for every deviating action and every history. Iteration applies to any
complete behavioral replacement, including delayed and Never actions.

For each deviator i, its opponents' survival probability per full refined
period is the same fixed product

    rho_i=product_(j≠i)(1−q_j^*)<1,
    (q_0^*,q_1^*,q_2^*,q_3^*)=(x,y,z,w).              (22)

The bounded remainder in the iteration vanishes geometrically. Therefore
the deviating terminal payoff is at most (V_A)_i+e_n. Exact policy
evaluation and the same vanishing remainder identify the prescribed
payoff with V_A. This proves full terminal e_n-Nash, with one target
chosen before n and before the requested error.

If C_join=0, the unrefined cycle already gives exact terminal Nash.
This is an exact-Nash corollary for the additional relevant pair caps,
not a claim that arbitrary unspecified participant rewards are harmless
without refinement.

### Uniform horizons and finite independent stopping laws

Here is a direct uniform-horizon conclusion. Let M bound all absolute
rewards and let m=1+2n be the refined period length. From (22), both
the prescribed profile and every one-player replacement have expected
absorption time, including the absorbing date, at most

    C_time=max_i m/(1−rho_i).

The absolute difference between expected N-date average payoff and expected
terminal payoff is at most 2M*C_time/N, uniformly over all these replacements.
Indeed, before absorption and on any unused horizon tail the payoff
discrepancy is bounded by 2M times the number of pre-absorption dates,
divided by N. Consequently prescribed delivery error is at most
2M*C_time/N and full finite-horizon regret is at most

    e_n+4M*C_time/N.

Choose n so e_n is sufficiently small and then one N large enough for
these bounds. The same profile works for every larger horizon, with
the same target V_A. This proves the main theorem on (16) directly.

There is also a finite-law version. Censor each player's independent
stopping law after K refined periods by moving its remaining mass to
Never. The total moved marginal mass is at most

    tau_K=(1−x)^K+(1−y)^K+(1−z)^K+(1−w)^K.            (23)

Product coupling bounds target error by 2M*tau_K and full terminal
regret by e_n+4M*tau_K. For the latter, compare a fixed complete
deviation using only the opponents' changed marginals, then compare the
prescribed payoffs; both comparisons are uniform over the deviator.
Choosing n and then K gives actual finite independent laws on one common
finite menu, with full regret and distance from V_A tending to zero.
No new singleton-refinement or terminal-to-uniform compiler is claimed.

## 6. Exact original-game source exits outside the constructed interval

For a real matrix M, a standard LCP root at offset q is λ≥0 with
q+Mλ≥0 and λ_i(q+Mλ)_i=0 for every i. The matrix is R0 if its only
root at offset zero is zero. We use the following existing source facts:

- For an R0 matrix, a regular offset with finitely many LCP roots computes
  its integer degree as the sum of the signs of their active principal
  determinants. Regular means every inactive residual is strictly positive
  and every active principal determinant is nonzero.
- An original finite-player quitting game with an R0 singleton-difference
  matrix of degree different from one has a uniform-equilibrium payoff.
- In four players, absence of an original-game UE forces that original
  singleton matrix to be R0, in fact of degree one.
- A three-player child with nonnegative inverse and nonnegative literal
  outside singleton-row inverse weights gives a UE of the original parent
  game. No condition is imposed on its unused nonsingleton rewards.

The exact tracked declarations are identified in Section 8. The following
calculations verify their hypotheses for the same original reward table.

The full singleton matrix is

    M_full=[[0,−σ₁,−σ₂,R−1],
            [−h_1,0,−1,a],
            [−h_2,b,0,−1],
            [−h_3,−1,c,0]].                            (24)

For R≠R_low, it is R0. Indeed, if a homogeneous root (t,z) has t>0,
the three child inequalities cyclically force every coordinate of z
strictly positive. Complementarity gives z=t*nu; the pivot residual is
t*nu_3*(R−R_low), which must vanish, impossible. If t=0 but z≠0,
the cyclic negative edges force all children positive; complementarity
gives A*z=0, impossible because det A=D>0.

For R<R_low, put delta=nu_3*(R_low−R)>0 and choose q_0>delta. At
offset (q_0,−h_1,−h_2,−h_3), child feasibility forces all children
positive, hence z=(1+t)*nu. The pivot residual is

    q_0−delta*(1+t).

Exactly two roots exist: t=0, with strict inactive residual q_0−delta>0;
and t=q_0/delta−1>0, with all coordinates active. Their active determinants
are D>0 and

    det M_full=D*nu_3*(R−R_low)=−D*delta<0.

Thus the source root-sum formula gives degree zero, and the original-game
degree-not-one theorem supplies UE for R<R_low.

For R=R_low, the strictly positive vector (1,nu) satisfies
M_full*(1,nu)=0. It is a nonzero homogeneous LCP root. The original
four-player no-UE implication to R0 therefore gives UE at this equality
by contraposition. No limiting-strategy argument is used.

For R≥T_pass, formula (6) supplies the exact nonnegative passive inverse
weights, and (5) supplies a strictly positive child inverse. The existing
raw inverse theorem gives UE. Its outside-weight hypothesis is weak,
so equality R=T_pass is included literally.

Together these source cases and (16) partition every real R. Neither
the open construction interval nor u=1+xi leaves an unhandled equality
boundary. The actual-data increment is the joint/solo construction on
the residual interval, not a new proof of the existing outer exits.

## 7. Exact stress tests and a full four-player premium core

### Negative quadratic coefficient and an empty former sign interval

Take

    a=b=c=2, h_1=h_2=h_3=1,
    xi=1, eta=17/11, q_2=q_3=−1,
    u=7/4, v=0, R=685/368.

Then c*σ₁+σ₂=−1/2, and the exact thresholds are

    R_low=5/4<R<T_pass=21/8,
    T_1=7/8, T_2=0, R_top=7/2.

In particular R_low<R<T_2 would be an empty interval; positivity of
c*σ₁+σ₂ is genuinely unavailable. The selected rates and values are

    (x,y,z,w)=(1/11,1/4,7/30,4/15),
    V_A=(5/4,17/121,4/11,0),
    V_B=(13/12,14/55,0,7/15),
    V_C=(65/46,7/11,0,0).

At y=1/4 the coefficients in (11) are

    (alpha,beta,gamma)=(−5/11,387/44,−7/8),

and k=1/10 is the admissible root. These rational values satisfy all
twelve policy equations and all twelve pure-Continue identities.

The passive inverse weights (6) are

    (363/644,685/2576,−281/1288).

Thus the selected child inverse exit genuinely fails. Each other
three-player principal has a nonzero row with all entries nonpositive,
excluding a nonnegative inverse. The full matrix is R0 of degree one:
at offset (1,−1,−1,−1) child feasibility forces z=(1+t)(1,1,1), and
R>R_low leaves a strictly positive pivot residual, so t=0 is the unique
root and its active determinant is seven. The full inverse has a negative
entry: its pivot row outside the diagonal is minus (6), divided by the
positive Schur complement nu_3*(R−R_low).

Every table in the main class fails product-low at the root where only
0 and 1 have hazard 1/2: their Quit endpoints are 1+xi/2 and eta/2,
strictly above their respective singletons. This is a precise failure
of that source premise, not a class-wide claim excluding all other methods.

### A vanishing leading coefficient

Keep the same a,b,c,h,xi,u,v,q but put eta=2 and R=12509/6840.
At y=1/4, alpha=0, beta=37/4, gamma=−7/8. Formula (12) gives

    k=7/74,
    (x,y,z,w)=(7/81,1/4,17/74,10/37),
    V_A=(5/4,14/81,10/27,0),
    V_B=(13/12,21/74,0,17/37),
    V_C=(481/342,2/3,0,0).

This lies strictly inside the same residual interval and satisfies the
same exact identities. The selector never divides by alpha.

### A complete admitted table outside the premium-core-at-most-two class

For the first fixture, the following specifies every coalition:

| Coalition | Reward |
| --- | --- |
| {0} | (1,−1,−1,−1) |
| {1} | (7/4,0,2,−1) |
| {2} | (0,−1,0,2) |
| {3} | (685/368,2,−1,0) |
| {0,1} | (2,17/11,−1,−1) |
| {0,2} | (1,−1,0,−1) |
| {0,3} | (1,−1,−1,0) |
| {1,2} | (0,0,0,1) |
| {1,3} | (685/368,0,1,0) |
| {2,3} | (685/368,1,1/2,1/2) |
| {0,1,2} | (1,0,0,−1) |
| {0,1,3} | (1,0,−1,0) |
| {0,2,3} | (1,−1,0,0) |
| {1,2,3} | (685/368,0,0,0) |
| {0,1,2,3} | (1,0,0,0) |

All six caps hold. The refinement constant is C_join=1/2, so the
profile's full terminal regret is at most max(z_n,w_n)/2, and its exact
target remains the displayed V_A. The extra pair premiums are not being
ignored: they create positive unrefined joining gains but disappear in
the one-error refinement bound.

A premium trap is a nonempty player set A such that each of its members
has a positive participant premium at some coalition contained in A.
Here both {0,1} and {2,3} are traps, so their union is the full greatest
premium core. Thus the admitted class is not subsumed by a theorem requiring
at most two globally variable participant coordinates or a greatest premium
core of size at most two. The singleton computations above remain unchanged.
This is a targeted source separation, not a claim that every completion
fails every quiet-child, quotient, or other existing existence criterion.

## 8. Tracked source correspondences and scope

The exact original-table source inputs used in Section 6 are:

- `exists_finset_r0Degree_eq_sum_sign_det` in
  `MathUE/LinearProgramming/R0DegreeSum.lean`;
- `exists_uniformEquilibriumPayoff_of_r0Degree_ne_one` in
  `UniformEquilibrium/Quitting/Classification/LCP/SingletonDegreeCriterion.lean`;
- `finFour_singleton_r0Degree_eq_one_of_no_uniformPayoff` in
  `UniformEquilibrium/Diagnostics/Quitting/FinFourSingletonDegreeCriterion.lean`;
- `PassiveRowInverseCriterion.inverseWeight`, `factorization`, and
  `exists_uniformEquilibriumPayoff_of_raw_nonnegativeInverse_triple` in
  `UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/RawPassiveRowInverseCriterion.lean`.

The raw inverse theorem uses literal receiver-first singleton differences
and permits zero outside weights. The degree and R0 implications concern
the original reward table and place no additional premium or normality
hypotheses on its unspecified entries.

The constructive path and error estimate correspond to existing supplied-
path consumers, whose fields are all explicitly produced in Sections 2–5:

- `quittingRootSequenceHazardTerminalValue_le_add_of_quitError_exactContinue`,
  `QuittingInfinitePathQuitErrorCertificate.isεAsymptoticNash_and_delivers`,
  and `isUniformEquilibriumPayoff_of_arbitrarily_small_infinitePath_quitError`
  in `UniformEquilibrium/Quitting/Paths/InfinitePathSupersolution.lean`;
- `exists_uniform_quittingMeshScale` in
  `UniformEquilibrium/Quitting/Terminal/TargetTail/InfiniteSingletonMesh.lean`;
- `singletonArcCycle_isTerminalNash_and_hasValue` in
  `UniformEquilibrium/Quitting/Cycles/SingletonArcCycle.lean`;
- `quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
  in `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`.

The product-low boundary uses the literal premise of
`exists_uniformEquilibriumPayoff_of_productLowPremium` in
`UniformEquilibrium/Quitting/Classification/Existence/ProductLowPremiumUniformPayoff.lean`.
The new mathematical contribution is selection from the raw data across
the entire surviving singleton interval, including the indefinite and
linear quadratic cases, with full behavioral and uniform-horizon control.
It is ordinary mathematical evidence, not a claim of a new Lean build.

The theorem does not cover arbitrary four-player tables. The directed
cyclic child matrix, strictly negative pivot-to-child singleton entries,
v<1, u≤1+xi, two positive pair premiums, and the six caps remain genuine
raw restrictions. No unrestricted strategy-class completeness theorem or
equilibrium counterexample is asserted.
