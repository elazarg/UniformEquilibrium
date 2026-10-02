# A paired-cycle producer with exact finite-law cap preservation

## Status and scope

This note gives an ordinary-mathematics existence proof for an explicitly specified,
full-dimensional class of four-player quitting games, and an extension to any even
number of players at least four. Every table in the class fails the product-low
condition. The proof constructs one chronological profile satisfying all players'
incentives simultaneously; it does not take a Nash–Bellman source or a profitable
response packet as an input.

The general four-player existence conjecture is **not** proved here. No assertion
of literature-wide novelty is made. The game-specific theorem below has not been
formalized or compiled in Lean. The accompanying exact-arithmetic script checks
the finite face inequalities used in the proof; numerical tests are additional
regressions, not a proof of existence.

## 1. The four-player reward class

There are four players, paired as A = {0,2} and B = {1,3}. For player i, let j be
its partner and {k,l} the other pair. Set

- s_i = r_i({i});
- b_i = r_i({j});
- P_i = r_i({i,j});
- a_ik = r_i({k}), a_il = r_i({l});
- d_i = r_i({k,l}).

Require, independently for every i,

    9/10 <= s_i <= 11/10,
   -1/10 <= b_i,d_i <= 1/10,
   19/10 <= P_i,a_ik,a_il <= 21/10,

and, for each nonempty T contained in {k,l},

    r_i({i} union T) <= s_i + 1/50.

All other reward coordinates are unrestricted real numbers. In particular, no
symmetry between players, no equality between the two pairs, and no restriction
on all four players quitting together is assumed. Infinite all-Continue pays zero.
Using strict versions of the displayed inequalities gives a nonempty open set in
the space of all sixty reward coordinates.

### Theorem 1

Every such game has an exact terminal behavioral Nash equilibrium, at every live
suffix, of the following form. There are q_i in (1/100,1/2) such that players in A
independently quit with their respective q_i on even dates, players in B independently
quit with their respective q_i on odd dates, and inactive players Continue surely.
The same profile has a uniform-equilibrium payoff. No public randomization is used.

### 1.1 Constructing all four hazards together

For player i write h=q_j, u=q_k and v=q_l. Define

    X_i = s_i + h(P_i-s_i),
    Y_i = (X_i-h b_i)/(1-h)
        = s_i + h(P_i-b_i)/(1-h),

    R_i(u,v) = u(1-v)a_ik + (1-u)v a_il + uv d_i,
    c(u,v) = (1-u)(1-v),

    H_i(q) = Y_i - R_i(q_k,q_l) - c(q_k,q_l)X_i.

X_i is the desired payoff in i's active phase. Y_i is the desired payoff in the
other phase, as forced by active-phase indifference. The equation H_i=0 is the
remaining chronological Bellman equation. It is essential to solve all four H_i=0
at once.

Let p be the partner involution. Apply the rectangular Poincare–Miranda theorem to
F_j(q)=H_{p(j)}(q) on [1/100,1/2]^4. Thus the face coordinate q_j is the *partner's*
hazard in the corresponding equation, rather than the player's own hazard.

Here are uniform face bounds. The last two columns are respectively an upper bound
for H_i at h=1/100 and a lower bound at h=1/2:

| u | v | H_i(1/100,u,v) <= | H_i(1/2,u,v) >= |
|---|---|---:|---:|
| 1/100 | 1/100 | -29689/9000000 | 128627/100000 |
| 1/100 | 1/2 | -67811/180000 | 1913/2000 |
| 1/2 | 1/100 | -67811/180000 | 1913/2000 |
| 1/2 | 1/2 | -289/3600 | 51/40 |

To justify the bounds between corners, for fixed h the residual is affine separately
in each of the six reward inputs and bilinear in (u,v). Its extrema on their
rectangle therefore occur at vertices. More explicitly, its s and P coefficients
are positive, and its b,a_ik,a_il,d coefficients are negative. At the lower face the
worst reward vector is (11/10,-1/10,21/10,19/10,19/10,-1/10); at the upper face the
worst vector is (9/10,1/10,19/10,21/10,21/10,1/10), in the order (s,b,P,a_ik,a_il,d).
Substitution yields the table. The script independently enumerates all 512 corner
values rather than relying on the coefficient-sign simplification.

Consequently H_i<0 on q_j=1/100 and H_i>0 on q_j=1/2, uniformly in the other
coordinates. Poincare–Miranda gives an interior q with all H_i(q)=0.

### 1.2 Incentives at both phases

At i's active phase, forced Quit pays X_i. Forced Continue followed by the prescribed
continuation pays

    q_j b_i + (1-q_j)Y_i = X_i.

Thus both actions are best responses if the other-phase inequality holds.

At the other phase, Continue pays R_i+cX_i=Y_i. A forced Quit pays at most

    c s_i + (1-c)(s_i+1/50) <= s_i+3/200.

But

    Y_i-s_i >= (1/99)(19/10-1/10) = 1/55.

So Continue is strictly better by at least 1/55-3/200=7/2200. These inequalities
hold for all four players at their respective phases.

The prescribed stage evaluation therefore equals the candidate value at every
phase. Iteration, using vanishing joint survival, identifies it with the actual
terminal payoff. For any unilateral deviation by i, its three opponents have
per-period survival

    D_i = product_{j != i}(1-q_j) <= (99/100)^3 < 1.

Hence the probability of reaching K periods under the deviation is at most D_i^K,
regardless of the deviator's privately randomized, unbounded stopping rule. Iterating
the two local action inequalities and letting K tend to infinity bounds *every*
such deviation by the prescribed payoff. Never is included. This proves exact
terminal Nash at every suffix.

The initial payoff is v_i=X_i for i in A and v_i=Y_i for i in B. In particular,

    v_i >= s_i > 0,        max_i v_i <= 21/10.

The upper bound for Y_i follows from Y_i=R_i+cX_i: it is a convex combination of
X_i<=8/5 and three passive rewards bounded above by 21/10.

For completeness, let M bound the absolute values of all rewards. Against any
unilateral deviation, E[T+1] <= 2/(1-(99/100)^3), where T is the absorption date
starting at zero. The discrepancy between the expected terminal payoff and the
expected H-stage average is at most M E[T+1]/H. Thus the same profile's H-stage
deviation gains are at most

    4M / (H(1-(99/100)^3)).

Its prescribed averages converge to v. This proves the uniform-payoff assertion
directly, without assuming a downstream source producer.

### 1.3 Strict separation from product-low

Activate only one pair at a one-stage root, with both hazards positive. For either
active player i, its forced-Quit payoff is

    s_i + q_j(P_i-s_i) > s_i.

So that root has positive absorption but no active low quitter. Every table in the
class fails product-low. This establishes separation from that table condition,
not separation from every other existing equilibrium-existence theorem.

## 2. Exact finite stopping-law selectors

Let C=product_i(1-q_i). Keep K>=1 complete periods and replace every later stopping
outcome by Never, independently for each player. The finite laws are explicitly

    Pr(T_i=2m)   = q_i(1-q_i)^m     (i in A),
    Pr(T_i=2m+1) = q_i(1-q_i)^m     (i in B),
    Pr(T_i=Never) = (1-q_i)^K,

for 0<=m<K. Call this product profile sigma^K.

### Theorem 2: exact cap-preserving truncation

For every player,

    U_i(sigma^K) = (1-C^K)v_i,
    B_i(sigma^K) = v_i,
    d_i(sigma^K) = C^K v_i.

Here B_i is the cap over all complete behavioral replacements, not just the
displayed finite menu. In particular

    E(sigma^K) <= (21/10)(99/100)^(4K).

Proof of the payoff identity: the infinite periodic profile renews with its original
initial phase after K periods. Its joint survival probability is C^K; the discarded
suffix payoff is exactly C^K v_i.

Proof of the cap identity: any pure stopping date before the cutoff has precisely
the same payoff as against the infinite profile, so its payoff is at most v_i. A
late finite date has, on the deleted-survival event, payoff s_i, while Never has
zero. Both are bounded by the legal deviation in the infinite profile that waits
to the cutoff and then resumes i's prescribed strategy, whose continuation payoff
is v_i>=s_i>=0. All three classes of pure deviations are therefore bounded by v_i,
and averaging covers every privately randomized law. Conversely, quitting on i's
first active date is an exact best response against the infinite profile, by the
phase equations, and its payoff is unchanged by truncation. Thus the finite cap
is exactly v_i.

This is stronger than preserving the prescribed payoff alone: the entire four-cap
vector stays fixed for this construction. The missing continuation is paid only
through the explicit vector C^K v.

### 2.1 An actual exact best-response pivot repair

Select pivot 0. In sigma^K, move all of its original Never mass to its last active
date 2K-2. Equivalently, keep its first K-1 active hazards unchanged and set its
last active hazard to 1. Call the result tilde-sigma^K.

Every active finite date of pivot 0 is an exact best-response date against the
finite opponent laws. The modified pivot is supported on such dates; consequently

    d_0(tilde-sigma^K)=0.

This does not assume other players' caps are unchanged. We bound their changes.
For i!=0, couple the old and new pivot stopping laws by changing only the original
Never outcome. The pivot has original Never probability (1-q_0)^K. A unilateral
payoff comparison for i can be affected only if the other two opponents survive
the preceding K-1 periods as well. Thus the mismatch probability is at most

    (1-q_0)^K product_{j notin {0,i}} (1-q_j)^(K-1)
      = (1-q_0)D_i^(K-1)
      <= (99/100)^(3K-2).

This is a common bound for *every* deviation by i, so its cap changes by at most
2M times that quantity. The prescribed payoff changes by at most
2M(1-q_0)C^(K-1), which is no larger than the same bound. Therefore

    max_i d_i(tilde-sigma^K)
       <= C^K max_i v_i + 4M(99/100)^(3K-2).

The repair is late, source-preserving, and selected specifically to have this
small deleted-survival exposure. There is no claim that an arbitrary pivot best
response, or a best-response update of an arbitrary profile, has this property.

## 3. Canonical own-singleton vector (1,0,0,0)

Define transformed terminal rewards by

    rhat_0(S) = r_0(S)/s_0,
    rhat_i(S) = r_i(S)-s_i       for i != 0,

leaving the Never payoff equal to zero. The own-singleton vector is now (1,0,0,0).

It would be incorrect to treat this as an unrestricted affine payoff identity on
all finite profiles: joint Never mass matters. Instead use the already constructed
infinite profile first. Every unilateral deviation against it absorbs almost
surely, since its opponents do. For precisely these prescribed/deviating profiles,
terminal expectations transform affinely. The infinite profile is thus still exact
Nash, with initial payoff

    vhat_0=v_0/s_0,   vhat_i=v_i-s_i (i!=0).

Moreover vhat_i>=shat_i>=0. The proof of Theorem 2 now applies directly to this
transformed game and gives, without using an invalid finite-profile translation,

    Uhat_i(sigma^K)=(1-C^K)vhat_i,
    Bhat_i(sigma^K)=vhat_i,
    dhat_i(sigma^K)=C^K vhat_i.

Since the pivot belongs to the first active pair,

    vhat_0=1+q_2(P_0/s_0-1) <= 5/3,
    vhat_i<=6/5  (i!=0),

so Ehat(sigma^K)<=(5/3)(99/100)^(4K). Thus, for the three nonpivot laws displayed
in Section 2, the optimal full-regret pivot-repair LP has value no greater than
this explicit vanishing bound. The particular best-response repair of Section 2.1
also works, with M replaced by a bound on the transformed rewards.

Fixing the original s_i=1 and taking strict inequalities for the other bounded
coordinates shows that these transformed tables include an open set relative to
the canonical 56-dimensional single-pivot reward space. They still fail product-low,
because each player's forced-Quit premium over its singleton is changed only by a
positive scale or a terminal additive shift.

### A symmetric reference point (not required by the theorem)

Set s_i=1, b_i=d_i=0, P_i=a_ik=a_il=2, and all the constrained off-phase Quit rewards
at most 1. The selected equal hazard is the root in (0,1/2) of

    q^3-6q^2+8q-1=0,

approximately 0.13919414688829662. Its cycle survival is approximately
0.5490613144019711. At the canonical transformed table the initial payoff is
approximately (1.1391941469, 0.3234042761, 0.1391941469, 0.3234042761).
This example is only for orientation. No claim that it lacks a stationary
equilibrium is made.

## 4. A rational residual certificate, rather than numerical root faith

The existence proof uses an exact real zero. There is also a finite, exact-arithmetic
way to verify an approximate selector without trusting a floating-point solver.
Take any rational hazards in the displayed box and compute the four H_i exactly.
Suppose max_i |H_i|<=eta. Define candidate X_i,Y_i as in Section 1 and v_i as its
initial phase. Active-phase indifference remains exact, and the off-phase Quit
inequality remains valid independently of H_i. The only Bellman residual occurs
at the quiet phase, with magnitude at most eta.

Write C=product_i(1-q_i), D_i=product_{j!=i}(1-q_j), and V=max_i v_i. For the K-period
finite laws, backward iteration of the candidate super-solution, starting at the
actual unrestricted tail cap max(s_i,0)<=v_i, gives

    B_i(sigma^K) <= v_i + eta/(1-D_i).

The corresponding prescribed-payoff iteration gives

    U_i(sigma^K) >= (1-C^K)v_i - eta/(1-C).

Consequently a fully explicit sufficient certificate is

    E(sigma^K) <= C^K V + eta/(1-C) + eta/min_i(1-D_i)
                <= C^K V + eta/(1-(99/100)^4)
                             + eta/(1-(99/100)^3).

For rational reward tables, a rational-grid search for sufficiently small residual terminates: an
interior exact zero exists, and rational points approximate it. Residuals and the
finite-law bound can then be checked with rational arithmetic. This is a class-
specific terminating selector, not an algorithm that has been proved to terminate
on arbitrary four-player tables.

### A fully specified rational finite selector

At the symmetric reference point, use the rational hazard
q=139194147/1000000000, rather than asserting that a rounded root is an exact zero.
Take K=30 complete periods (60 finite dates, plus Never). After the canonical
normalization, the four residuals are equal to

    99320363790760452180796881 /
    860805853000000000000000000000000000.

Here C=(1-q)^4, D=(1-q)^3, and V=max(1+q, 2q/(1-q)). The exact rational bound

    C^30 V + |H|/(1-C) + |H|/(1-D)

is strictly below 1/1000000 (its decimal value is approximately 1.8163e-8).
The script checks the strict inequality using Fraction arithmetic, not floating
point. The three nonpivot laws with these hazards therefore have optimal
full-regret pivot-repair value below 1e-6: the displayed pivot law is an explicit
feasible competitor. This particular rational claim concerns the reference table,
not every table in the surrounding reward box.

## 5. Extension: any even number of players, any cyclic pair order

Let n=2m with m>=2, partition the players into m disjoint pairs, and fix any cyclic
order of the pairs. For each i use the same own-singleton, partner-singleton, and
own-pair intervals as in Section 1. For every *other* pair {k,l}, require

    r_i({k}),r_i({l}) in [19/10,21/10],
    r_i({k,l}) in [-1/10,1/10],
    r_i({i} union T) <= s_i+1/50 for nonempty T subset {k,l}.

Other entries remain arbitrary. There is an exact behavioral equilibrium cycling
through these pairs, with one hazard q_i in (1/100,1/2) per player.

Here are the details extending the simultaneous existence step. Keep X_i,Y_i as
before. Each other pair B induces the affine map

    T_i,B(z)=R_i,B+c_B z.

Compose these maps in their chronological Bellman order over the m-1 other pairs,
starting from X_i at i's next active phase; call the result Psi_i(X_i). The field
is H_i=Y_i-Psi_i(X_i), relabeled by the same partner involution.

At q_partner=1/100, the four-player lower-face estimates imply T_i,B(X_i)>Y_i>X_i
for every other pair B. Every T_i,B is increasing, so their entire composition is
also greater than Y_i. The lower sign follows.

At q_partner=1/2, X_i<=8/5. Each T_i,B is a convex combination of its input and
three rewards bounded above by 21/10, so Psi_i(X_i)<=21/10. On the other hand
Y_i>=9/10+(19/10-1/10)=27/10. The upper sign is at least 3/5. Rectangular
Poincare–Miranda again produces a simultaneous interior zero.

For the extra quiet-phase incentives, conditional on absorption by a different
pair whose hazards are at most 1/2, its simultaneous-quitting probability is at
most one third of its total absorption probability. Its conditional passive
payoff is therefore at least

    (2/3)(19/10)+(1/3)(-1/10)=37/30.

All intermediate continuation values are at least s_i: start at X_i>=s_i and
apply the positive affine maps whose conditional absorption means exceed s_i.
If alpha_B is the current pair's absorption probability, Continue consequently
pays at least s_i+(2/15)alpha_B, while Quit pays at most s_i+(1/50)alpha_B. Thus
Continue is strictly preferred by at least (17/150)alpha_B. Active-phase actions
are tied, exactly as before. Deleted survival per cycle is at most (99/100)^(n-1),
so the unrestricted-deviation argument applies.

All initial values remain in [s_i,21/10]. Truncation after K complete cycles
preserves the entire cap vector exactly and has regret C^K v_i, now with
C<= (99/100)^n. Product-low still fails on every positive two-member paired root.

## 6. Verification record and repository provenance

Read-only repository snapshot: elazarg/UniformEquilibrium at
88709a1034da3738fcb35ca10fc2cea45bad808d, 6 September 2026.

Relevant existing results read during the investigation:

- docs/FRONTIER.md: the general selection obligation and source/consumer distinction;
- UniformEquilibrium/Quitting/Terminal/PivotRepairBehavioralInfimum.lean:
  exists_objective_minimizer_eq_behavioral_infimum;
- UniformEquilibrium/Quitting/Classification/Existence/ProductLowPremiumUniformPayoff.lean:
  exists_uniformEquilibriumPayoff_of_productLowPremium;
- Research/Quitting/EscapeAwareQuantileClockHierarchy.lean: payoff-and-cap finite-clock
  approximation already exists and is not being claimed as new;
- MathUE/Topology/RectangularPoincareMiranda.lean:
  Math.Topology.exists_rectangular_zero_of_strict_face_signs;
- UniformEquilibrium/Quitting/Examples/BlockPair/FourPlayerPairedSingletonPeriodTwo.lean
  and UniformEquilibrium/Quitting/Examples/SolanVieilleBoundaryTable.lean:
  an existing exact paired period-two construction for the Solan–Vieille table.
  Alternating pairs are therefore not a new basic construction. The displayed
  reward box here is different: in particular, its own-pair Quit rewards strictly
  exceed its own singletons, unlike the capped-joint-exit boundary table.

The new mathematical content claimed in this note is the explicit paired reward
region, its simultaneous chronological producer, and the exact finite-selector
ledger for that producer. Rectangular Poincare–Miranda and the general periodic
Bellman verification principle are not new results.

Commands:

    python verify_paired_selector.py
    python verify_paired_selector.py --numerical 100 --output verification.json

The first command checks 512 rational corner values, the inactive margin, and the
explicit rational 60-date selector using Python's Fraction arithmetic and only the
standard library. The second also needs
NumPy and SciPy. In the recorded run, 100 independently perturbed asymmetric tables
passed the tests for the simultaneous root, unrestricted periodic caps, exact
finite-cap/payoff identities at four cutoffs, and the selected exact pivot repair.
The largest recorded discrepancy was below 1e-12. These numerical regressions are
not used as a substitute for the proof.

No Lean compilation, theorem-level axiom audit, repository change, branch, commit,
or pull request was performed. The arbitrary Fin4 selection problem remains open
within this work.
