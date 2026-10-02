# Cardinal-free stationary repair and LCP index escape

## Status and scope

This is an ordinary mathematical argument, not a Lean-checked result. It extends the attached four-player integer-LCP-degree theorem to every finite player count and strengthens the conclusion to **stationary approximate equilibria**. With nonnegative own-singleton rewards, the same matrix condition supplies an **exact stationary terminal equilibrium**.

The proof works on the original signed reward table. It does not use a punishment-normality reduction, an auxiliary terminal translation, analytic curve selection, a selected Bellman germ, or a hypothesis that all discounted equilibria have already been localized.

The new quantitative ingredient proved here is a stationary repair estimate valid for every finite quitting game. The topological ingredient is a local-index calculation at all Continue at discount zero, followed by subtraction from the global degree. The integer-degree mechanism and matrix convention are credited to the supplied `INTEGER_LCP_DEGREE_CRITERION_FOR_FOUR_PLAYER_QUITTING_GAMES(2).md`; the weak-inverse approximation is credited to `INVERSE_POSITIVE_SINGLETON_MATRIX_DISCOUNTED_INDEX_ESCAPE(2).md`.

This does **not** settle the remaining degree-one four-player case. The quantitative rate bound below is a necessary restriction on a counterexample, not its exclusion. It also applies to a positive gap over stationary profiles alone, so that bound by itself cannot exclude a game requiring nonstationary equilibria. No literature-wide priority claim is made.

## 1. Model and headline statements

Let I have n >= 2 players. Nonempty quitting coalition S pays r(S) in R^n. Live stages and Never pay zero. Fix M > 0 with |r_i(S)| <= M. Write

    s_i = r_i({i}),       Gamma_ij = r_i({j}) - s_i.

Recipients index rows; singleton quitters index columns. In particular Gamma_ii = 0.

Strategies use independent private randomization. Before absorption the only public history is all Continue, so a complete behavioral strategy is equivalent to a private law on the finite dates and Never. Every unilateral replacement law is allowed. For an actual profile p let

    U_i(p) = terminal payoff,
    B_i(p) = supremum of terminal payoff over every complete replacement,
    E(p)   = max_i (B_i(p) - U_i(p)).

A stationary profile is a constant hazard vector q in [0,1]^n, repeated indefinitely. Put

    C(q) = product_i (1-q_i),       a(q) = 1-C(q).

Discount complement lambda is in (0,1); d=1-lambda. The quitting live stage pays zero, so an immediate absorbing reward has discounted value d times that reward.

### Theorem A: universal stationary repair

Let q be any stationary lambda-discounted equilibrium of the ORIGINAL game and suppose a=a(q)>0. Put x=lambda/a. One can choose a stationary profile p from the finite list

    q, q_1 e_1, ..., q_n e_n

such that

    E(p) <= min(2M, M[x+2 sqrt(x)]) <= 3M sqrt(lambda/a).

The selection is explicit and uses only q, its original stationary terminal payoff, and lambda. Every cap in this statement is an unrestricted behavioral cap, not a stationary-deviation cap.

### Corollary A1: a quantitative all-equilibria rate restriction

If E(p) >= gamma > 0 for EVERY behavioral profile p, then every stationary discounted equilibrium q satisfies

    a(q) <= 9 M^2 lambda / gamma^2.

The sharper bound is

    a(q) <= lambda / (sqrt(1+gamma/M)-1)^2.

These hold without R0, singleton-sign, normality, or cardinal assumptions. In particular, a counterexample forces its ENTIRE stationary discounted-equilibrium set to have total absorption O(lambda). Since max_i q_i <= a and sum_i q_i <= n a, this also bounds every hazard and the total hazard.

### Theorem B: cardinal-free stationary degree criterion

Define on the whole ambient R^n

    f_Gamma(z) = min(z, Gamma z)

coordinatewise. Suppose Gamma is R0, meaning f_Gamma has only the zero root, and let kappa(Gamma) be its local integer Brouwer degree at zero.

If

    kappa(Gamma) != 1,

the original game has a fixed uniform-equilibrium payoff implemented, at every positive accuracy, by a STATIONARY profile. Independently censored finite laws can also implement the same target with vanishing full terminal regret.

All own-singleton levels and every nonsingleton reward are arbitrary signed reals.

More precisely, there exist delta>0 and lambda_0>0 such that for every 0<lambda<lambda_0 the original game has a stationary discounted equilibrium q_lambda with

    a(q_lambda) >= max_i (q_lambda)_i > delta.

Its complete outside-all-Continue equilibrium set has total displacement degree 1-kappa(Gamma). Applying Theorem A gives stationary terminal errors at most 3M sqrt(lambda/delta).

If all s_i>=0, there is instead one **exact stationary terminal Nash equilibrium with positive absorption**. That same stationary profile is a uniform epsilon-equilibrium for every sufficiently large horizon, for each epsilon>0, at its fixed terminal payoff.

The word exact here concerns terminal Nash, not equality of every finite-horizon payoff or exact Nash at every finite horizon.

## 2. Exact stationary and discounted accounting

Fix i. Let

    alpha_i = product_{j!=i}(1-q_j),       b_i=1-alpha_i.

Under the opponents' independent current actions, let Q_i be the expected reward if i Quits, and H_i the absorbing contribution if i Continues:

    Q_i = sum_{T subset I\{i}} pi_i(T) r_i(T union {i}),
    H_i = sum_{nonempty T subset I\{i}} pi_i(T) r_i(T).

Set

    R_i = q_i Q_i + (1-q_i)H_i,
    L = 1-d C = lambda+d a = a+lambda C,
    u_i = d R_i/L.

L is strictly positive, including at q=0. The actual discounted recursion is

    u_i = d [R_i+C u_i].

The two live Bellman endpoints are dQ_i and d(H_i+alpha_i u_i). Direct algebra gives

    L (Q_i-H_i-alpha_i u_i) = D_i(lambda,q),
    D_i(lambda,q) = (1-d alpha_i)Q_i-H_i.                 (2.1)

Thus stationary discounted equilibrium is exactly

    q_i=0      => D_i<=0,
    0<q_i<1    => D_i=0,
    q_i=1      => D_i>=0.                                (2.2)

These conditions bound all discounted behavioral deviations: iterate the two Bellman inequalities along an arbitrary replacement and let the bounded discounted remainder vanish. No assumption about stationary optimality of a deviator is needed.

For terminal payoffs, if b_i>0 a pure deadline t gives

    H_i (1-alpha_i^t)/b_i + alpha_i^t Q_i,

and Never gives H_i/b_i. A randomized complete clock averages these values. Consequently

    B_i(q) = max(Q_i, H_i/b_i),             b_i>0;
    B_i(q) = max(s_i,0),                    b_i=0.        (2.3)

The second case means all opponents play Never. These formulas include all arbitrarily late dates and Never.

When a>0, the prescribed terminal vector is V_i=R_i/a. Since u_i/d=aV_i/L, the discounted Nash inequalities imply

    Q_i-V_i <= M lambda/a.                              (2.4)

For b_i>0 the Continue inequality also implies

    H_i/b_i <= a(b_i+lambda alpha_i)V_i/(b_i L).

Using L>=a and |V_i|<=M gives

    B_i(q)-V_i <= M lambda(1/a+1/b_i).                   (2.5)

There is a useful sign improvement:

    V_i<=0 and b_i>0 => B_i(q)-V_i<=M lambda/a.          (2.6)

Indeed the extra term proportional to lambda alpha_i V_i/b_i is then nonpositive. This is the step that retains very slow opponent clocks without introducing a large cap error for a negative-payoff owner.

## 3. Proof of the universal repair theorem

If x=lambda/a>1, take p=q: E(q)<=2M<=3M sqrt(x), and also E(q)<=M(x+2sqrt(x)).

Suppose 0<x<=1 and put

    theta = sqrt(x)/2 <= 1/2.

### Case 1: every deleted-opponent clock has b_i>=theta a

Keep p=q. Equation (2.5) gives

    E(q) <= M x(1+1/theta) = M[x+2sqrt(x)].             (3.1)

### Case 2: some k has b_k<theta a

Since

    a=q_k+(1-q_k)b_k<=q_k+b_k,

we have q_k>(1-theta)a. In particular q_k>0, and for every j!=k,

    b_j>=q_k>(1-theta)a.                              (3.2)

If V_k<=0, keep p=q. When b_k>0, (2.6) controls k. When b_k=0, V_k=s_k; because q_k>0, the discounted equilibrium condition gives lambda s_k>=0. Hence V_k<=0 forces s_k=0 and k's full terminal debt is zero. For all other players (2.5) and (3.2) give

    E(q) <= M x[1+1/(1-theta)]
          <= M[x+2sqrt(x)],                            (3.3)

where the final inequality is equivalent to sqrt(x)<=1.

It remains to treat V_k>0. Choose

    p=q_k e_k:

retain k's same stationary hazard and set every other hazard to zero.

Under q, conditional on absorption in a row, the probability the terminal coalition is not the singleton {k} is exactly b_k/a. Thus for EVERY recipient j,

    |V_j-r_j({k})| <= 2M b_k/a.                        (3.4)

For the sole active owner, prescribed terminal payoff is s_k and complete cap is max(s_k,0). Since V_k>0,

    d_k(p)=(-s_k)_+ <= 2M b_k/a < 2M theta.             (3.5)

For j!=k, prescribed payoff is r_j({k}); its Never payoff is that same number, and its Quit endpoint is Q_j(p). Couple q and p's opponent action draws, keeping k's draw unchanged. A difference requires some player other than k,j to quit, an event of probability at most b_k. Therefore

    Q_j(p)-Q_j(q) <= 2M b_k.                           (3.6)

This is a separate counterfactual comparison, not an inference from (3.4)'s prescribed-payoff bound. Combining (2.4), (3.4), and (3.6),

    d_j(p) = [Q_j(p)-r_j({k})]_+
           <= 2M b_k + M lambda/a + 2M b_k/a
           <= M x+4M theta
            = M[x+2sqrt(x)].                           (3.7)

Equations (3.1)--(3.7) prove the sharper bound. For x<=1, x+2sqrt(x)<=3sqrt(x); for x>1 use E<=2M. This proves Theorem A.

The construction chooses either the supplied q or one explicitly specified sole-owner stationary vector. It does not mix profiles, correlate clocks, transfer a child equilibrium, or assume a continuation is strategically realizable.

Corollary A1 follows by applying the full behavioral gap to the selected p. Writing y=sqrt(lambda/a), the sharper inequality gives gamma/M<=y^2+2y, hence y>=sqrt(1+gamma/M)-1. The 9M^2/gamma^2 version follows from the simpler bound.

## 4. An original-table local-to-global degree calculation

Define for lambda in [0,1), on the WHOLE ambient R^n,

    F_lambda(q) = clip_[0,1]^n(q+D(lambda,q)),
    G_lambda(q) = q-F_lambda(q).                         (4.1)

D is the polynomial in (2.1), extended algebraically outside the strategy cube. For lambda>0 every zero of G_lambda belongs to [0,1]^n and is an actual stationary discounted equilibrium by (2.2).

Let Omega=(-1,2)^n. Every F_lambda takes values in [0,1]^n, strictly inside Omega. Homotoping it to the cube center never creates a boundary fixed point, so

    deg(G_lambda,Omega,0)=1                            (4.2)

for all lambda in [0,1). At lambda=0 the map remains a well-defined topological object; no discounted value is assigned at the singular all-Continue point.

### Local degree at all Continue

At lambda=0, singleton expansion gives

    D(0,q) = -Gamma q + O(||q||^2).                     (4.3)

For example Q_i=s_i+O(||q||), 1-alpha_i=sum_{j!=i}q_j+O(||q||^2), and H_i=sum_{j!=i}q_j r_i({j})+O(||q||^2). Their linear difference is -sum_j Gamma_ij q_j. Nonsingleton rewards cancel at this order. The expansion holds in an ambient real neighborhood, including negative q coordinates.

For q close to zero the upper clip in (4.1) is inactive. The lower clip must be retained. Exactly,

    G_0(q) = min(q,-D(0,q)).                            (4.4)

R0 and positive homogeneity imply a positive constant c with

    ||min(z,Gamma z)|| >= c||z||       for every z.       (4.5)

Indeed the continuous norm of the min-map has a positive minimum on the unit sphere. Since the componentwise minimum is 1-Lipschitz in its second argument, (4.3)--(4.4) show

    G_0(q) = f_Gamma(q)+O(||q||^2).

Choose delta>0 so small that the upper clip is inactive on the closed cube Wbar=[-delta,delta]^n and, on its boundary, the perturbation norm is less than half the margin in (4.5). A straight homotopy to f_Gamma then has no boundary zero. Consequently zero is locally isolated and

    deg(G_0,W,0)=kappa(Gamma),      W=(-delta,delta)^n.  (4.6)

Continuity in lambda, uniform on the compact boundary of W, gives lambda_0>0 such that

    deg(G_lambda,W,0)=kappa(Gamma),       0<=lambda<lambda_0,

with no boundary zeros. Additivity with (4.2) yields

    deg(G_lambda,Omega\Wbar,0)=1-kappa(Gamma).           (4.7)

If kappa!=1, this outer degree is nonzero. Thus, for EVERY sufficiently small positive lambda, an actual discounted equilibrium q_lambda lies outside Wbar. Because a fixed point lies in the nonnegative strategy cube,

    max_i (q_lambda)_i>delta,       a(q_lambda)>delta.

This proves the promised actual escaped source. It does not assert that every discounted equilibrium escapes. The local and outer solution sets may be degenerate, nonisolated, or have multiple supports; only their total degrees are used. When kappa=-1 the outer total degree is 2, not an assertion of exactly two distinct equilibria.

### Consumption

Apply Theorem A to q_lambda. The resulting original stationary p_lambda has

    E(p_lambda)<=3M sqrt(lambda/delta) -> 0.

For small lambda, the repair keeps q_lambda or retains a sole hazard greater than a(q_lambda)/2, so a(p_lambda)>=delta/2. Select a convergent subsequence of their bounded prescribed terminal vectors. Section 5 proves that its limit is one fixed uniform-equilibrium payoff, with stationary implementations. This proves Theorem B without a contrary no-UE source.

### Nonnegative singletons: exact stationary Nash

Equation (4.7) also holds at lambda=0 and supplies a nonzero root q*. Its actual undiscounted value is R(q*)/a(q*). The Bellman inequalities hold at this value.

If at least two players have positive hazards, every deleted-opponent clock contracts and (2.3) makes the profile exact terminal Nash. If exactly one player k has positive hazard, every other player's deleted clock contracts; k's only missing response is Never. Nonnegativity of s_k makes that response unprofitable. Thus all s_i>=0 guarantees an exact stationary terminal equilibrium.

A weaker raw sufficient condition for this exact conclusion is also available. For each k with s_k<0, require that the scalar inequalities

    0<h<=1,
    r_j({k}) >= (1-h)s_j+h r_j({j,k})    for every j!=k

have no common solution h. This excludes every negative-singleton sole-owner zero-discount root. The degree-produced nonzero root is then again exact stationary terminal Nash. The condition is a finite one-variable linear feasibility test, not a supplied strategic witness.

## 5. Fixed-target uniform implementation and finite laws

### Stationary implementations

For a fixed stationary profile p with a(p)>0, prescribed absorption has finite geometric mean. Its H-stage average payoff tends to its terminal vector at rate at most M/[H a(p)].

If player i's opponents have b_i(p)>0, then under EVERY replacement its absorption date is no later than the first opponent quit. Therefore the absolute terminal-to-H-stage payoff error is at most M/[H b_i(p)], uniformly over complete replacements. This gives

    H-stage gain_i <= d_i(p)+M/[H b_i(p)]+M/[H a(p)].

At most one player can have b_i(p)=0. In that case p has only that player k active. Every deviating payoff is s_k times an absorption tail weight. If s_k<0, Never has value zero and the finite-horizon gain is at most -s_k=d_k(p). If s_k>=0, the extra finite-horizon gain is at most M/[H p_k]. Thus this exceptional deleted clock also has a valid uniform bound.

Given stationary profiles p_m with E(p_m)->0, select a subsequence with U(p_m)->v. For each accuracy, choose one sufficiently late stationary profile, then a horizon threshold making all its finitely many displayed bounds small. The same profile works for EVERY larger horizon. The target v is chosen before the final accuracy.

### Finite independent censoring

For a fixed stationary p with all b_i>0, retain T rows and censor each private later clock independently to Never. Joint payoff changes by at most M C(p)^T. Under any unilateral replacement, a changed outcome requires all opponents to survive those T rows, so each cap increases by at most 2M alpha_i(p)^T. Hence

    E(p^T)<=E(p)+3M rho^T,
    ||U(p^T)-U(p)||_infty<=M C(p)^T,
    rho=max_i alpha_i(p)<1.

For a sole-owner profile, the same bound applies to all outsiders with rho=1-p_k. The owner's censored debt is at most its old debt plus M rho^T: a negative singleton's debt decreases on censoring, and a nonnegative singleton loses only its surviving prescribed mass. Thus finite laws approximate every selected stationary source with full-cap control, including the sole-owner case.

For completeness, a finite N-date profile with arbitrary signed singletons satisfies

    |U_i^H-U_i|<=M(N+1)/H,
    sup_tau U_i^H(tau,p_-i)<=B_i(p)+M(N+1)/H.

For a late deviation and s_i>=0, delay cannot improve its terminal singleton contribution. For s_i<0, compare its late contribution with Never, not with its own negative terminal payoff. Earlier opponent absorption has the stated timing bound. Mixtures of pure dates and Never give the full behavioral result.

Consequently finite-horizon regret is at most E(p)+2M(N+1)/H. This also proves fixed-target uniform delivery by the censored laws, independently of the stationary-horizon proof.

## 6. A cardinal-free nonnegative-inverse corollary

For n>=3, suppose

    det Gamma<0,       B=Gamma^{-1}>=0 entrywise.         (6.1)

Then the original game has stationary approximate uniform equilibria and a fixed uniform payoff. For the weak-inverse boundary, stationarity is preserved by the reward-perturbation argument below.

First assume B>0. If h>=0 is a nonzero homogeneous complementary solution and w=Gamma h>=0, invertibility gives w!=0. Then h=Bw>0, so complementarity forces w=0, a contradiction. Thus Gamma is R0.

At right-hand side -1, any complementary solution satisfies

    h=B(1+w)>=B1>0.

Therefore w=0 and h=B1 is the unique solution. Its local min-map degree is sign det Gamma=-1. R0 makes total LCP degree independent of the right-hand side, so kappa(Gamma)=-1, and Theorem B applies.

Here is the short justification for right-hand-side independence. The coercivity (4.5) and ||min(z,Gamma z+b)-min(z,Gamma z)||<=||b|| place every zero for bounded b in one bounded domain. Straight right-hand-side homotopies have no boundary zero there, giving degree invariance. The local full-support derivative at B1 is Gamma.

For B>=0 use K=J-I and Gamma_e=Gamma-eK. For small e>0,

    Gamma_e^{-1}=B+eBKB+e^2BKBKB+... .                   (6.2)

All coefficients are nonnegative. If B_ij and (BKB)_ij both vanish, nonempty row/column supports force row i and column j of B to have the same singleton support {k}. Invertibility and n>=3 imply there is a positive B_uv with u,v!=k. Then

    B_ik K_ku B_uv K_vk B_kj>0

is a term of (BKBKB)_ij. Thus the inverse in (6.2) is strictly positive. The diagonal stays zero and the determinant remains negative for sufficiently small e.

Change only the off-own singleton rewards by -e. The original and perturbed games have the same strategy space and first-outcome law for each prescribed or deviating profile. Uniform reward distance e gives

    |E_r(p)-E_{r_e}(p)|<=2e                            (6.3)

for EVERY profile, in particular every stationary profile. Choose stationary approximate equilibria of r_e with errors tending to zero, reuse their same constant hazards in r, and select a convergent subsequence of their original terminal payoff vectors. Section 5 yields the original fixed uniform payoff with stationary implementations. Finite censoring is also available.

No assertion that Gamma is R0 is made on the weak boundary. The cyclic permutation example below is not R0. The corollary's restriction n>=3 is genuine for the particular strict-inverse approximation; two-player existence is a separate already solved case.

## 7. Open matrix classes at every cardinal n>=4

Start with the supplied strict-inverse four-player matrix

    G4 = [ 0  2  1 -3;
          -3  0  2  3;
          -3  2  0  2;
           3 -3 -1  0 ].

It has determinant -3 and strictly positive inverse. Taking

    u=(10,1,1,1)^T,    v=(1,10,1,1)^T,
    sigma=-v^T G4 u=250

produces

    G5 = [  0  2   1  -3   0;
           -3  0   2   3  25;
           -3  2   0   2  26;
            3 -3  -1   0 -26;
           30 -1 -20 -29   0 ].

Its determinant is -750 and its inverse is strictly positive. Thus EVERY five-player reward table with

    r_i({j})=s_i+(G5)_ij

has the theorem's stationary approximate uniform equilibria, with arbitrary signed s and arbitrary nonsingleton rewards.

The construction continues indefinitely. Given zero-diagonal G with det G<0 and B=G^{-1}>0, choose positive u,v with sigma=-v^TGu>0 and set

    G_new = [ G       -Gu;
             -v^T G    0 ].

The Schur-complement formulas give

    det G_new = sigma det G <0,
    G_new^{-1} = [ B+uv^T/sigma    u/sigma;
                   v^T/sigma      1/sigma ] >0.          (7.1)

Such positive u,v always exist. G has a negative entry G_ij: an everywhere nonnegative G could not multiply a strictly positive B to the identity in dimension at least two. With u=1+t e_j and v=1+t e_i, the leading coefficient of v^TGu is t^2G_ij<0, so large positive t works. Rational G permits integer t.

Strict inverse positivity and a negative determinant persist on a neighborhood in the zero-diagonal slice. Consequently these are nonempty open singleton-matrix classes in every cardinal n>=4, with all collision rewards unrestricted.

This is not passive-player padding of one solved reward table: the new player's singleton level and every coalition completion are arbitrary. Moreover, a full strictly inverse-positive matrix cannot have an ambient balanced singleton cycle supported on a proper player subset. Such a cycle would have a singleton outcome distribution mu with some zero coordinate and Gamma mu>=0. Invertibility and B>0 would instead force mu=B(Gamma mu)>0. Thus the proper-child balanced-cycle inheritance theorem in the supplied packet cannot account for this class.

This is a comparison with that specific inheritance mechanism, not an exclusion of all other sufficient criteria.

## 8. Signed boundary test: why exact stationarity needs qualification

For two players use the zero-sum table

    r({0})=(1,-1),
    r({1})=(1/2,-1/2),
    r({0,1})=(-1,1).

For 0<p<1/5 put

    q_0=p,       q_1=1/4+3p/4,
    lambda=(p+3p^2)/(1-4p+3p^2).

Direct substitution gives D_0=D_1=0, so these are original discounted equilibria. They approach the negative-singleton sole-owner root (0,1/4). That LIMIT profile is not terminal Nash: player 1 gains 1/2 by Never.

Nevertheless the actual positive-p stationary profiles have complete caps

    B_0=1/2,       B_1=-1/2+3p/2.

Writing Z=1+6p-3p^2, their exact debts are

    d_0=6p^2/Z,
    d_1=3p(1-p)(1+3p)/(2Z),

both tending to zero. The disappearing opponent clock must not simply be dropped when the surviving owner's payoff is negative. Theorem A keeps q in precisely the nonpositive-owner branch.

For a weak-inverse matrix boundary, the four-cycle permutation matrix P has det P=-1 and P^{-1}>=0, but a singleton basis vector is a nonzero homogeneous complementary vector. Thus it is not R0. Subtracting (J-I)/20 gives a zero-diagonal matrix with negative determinant and strictly positive inverse. This tests why Section 6 uses literal reward approximation rather than claiming R0 at a weak-inverse boundary.

## 9. Evidence, source correspondence, and formalization boundary

Classical integer degree is used with the coordinatewise min-map convention of M. S. Gowda, *Applications of Degree Theory to Linear Complementarity Problems*, Mathematics of Operations Research 18(4), 1993, pp. 868--879, especially Section 2, printed pp. 869--871. The author-hosted original was inspected, including the page displaying formulas (5)--(6) and the R0 degree definition. The argument uses normalization, boundary-safe homotopy invariance, additivity/excision, and the local determinant-sign formula. It does not use a mod-2 substitute.

Relative to the supplied packets:

* The integer-degree packet supplies the existing Fin4 degree mechanism and its multibranch example. Section 4 here instead computes the local degree directly at lambda=0 and obtains an outer component of degree 1-kappa for every small discount. No no-UE localization, translated anchor, or scaled LCP at that anchor is needed.
* The inverse-positive packet supplies the weak-inverse approximation in Section 6; it is credited, not claimed anew. The new strategic conclusion preserves stationary profiles and has no four-player restriction.
* The supplied stationary endpoint formulas, full private-clock semantics, and signed finite-horizon comparisons are compatible with Sections 2 and 5; their complete arguments are reproduced here.
* The passive-row cycle packet is used only for the bounded comparison with proper-child balanced singleton inheritance, not as a hypothesis of the main theorem.

The new repair theorem and its composition were not compiled in Lean. Static repository reads were made at `5aac30ad2553dadd5895dc79fbc4f1f5680d7570`, including `AGENTS.md`, the frontier, and the generic auxiliary endpoint source; the new proof does not depend on that auxiliary source. No repository files, branches, commits, or PRs were changed. The local runtime had no available `lake` command.

`VERIFY_CARDINAL_FREE_LCP_INDEX_ESCAPE.py` uses exact Fraction and SymPy arithmetic. Its run checked:

* 800 coordinates of the discounted Bellman identity, 108 negative-Q cap implications, and 14 ambient first-order expansions;
* 200 exactly constructed discounted equilibria for 2 through 6 players, with all three repair branches exercised: 100 ordinary kept profiles, 48 nonpositive-owner kept profiles, and 52 sole-owner repairs;
* the exact signed discounted family above at four rational parameters;
* the five- and six-player bordered matrices, the supplied three-branch LCP inventory, and the weak-inverse perturbation;
* an additional finite punishment-splice regression and complete finite-horizon caps. That splice is not needed for the stationary repair proof.

All exact assertions passed. These are finite algebraic checks, not a proof of the universal theorems or a Lean validation. The accompanying JSON records the run.

A narrow formalization can separate: complete stationary cap formulas; the uniform repair theorem with its three explicit branches; the local min-map degree calculation for the original discounted polynomial; outer-degree subtraction; and the stationary fixed-target consumer. The weak-inverse boundary and cardinal-raising matrix construction are separate corollaries. No proof structure should assume the desired repair, escaped root, or uniform equilibrium as a field.

## 10. What is and is not resolved

The completed outputs are an unrestricted-cap stationary repair estimate for every finite quitting game; an explicit all-discounted-equilibria rate bound under a positive behavioral gap; a cardinal-free original-table index theorem; stationary approximate implementation under arbitrary signed rewards; and exact stationary terminal equilibrium in the nonnegative-singleton subcase. The theorem supplies open classes for every n>=4.

For the remaining R0 degree-one Fin4 matrices, the outer degree in (4.7) is zero. No escaped discounted source is forced. The paired positive-determinant matrix in the supplied packets is an example of that unresolved index regime. Neither the repair estimate nor the necessary O(lambda) rate bound turns the zero outer degree into a contradiction. The general four-player conjecture is therefore not resolved by this argument.
