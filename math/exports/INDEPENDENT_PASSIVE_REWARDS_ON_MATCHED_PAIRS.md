# Equilibria for independently varying passive rewards on matched pairs

Four independent private stopping laws choose the first nonempty quitting coalition; a player can replace its whole law, including Never. Several raw regions in the four passive payoffs lead to exact absorbing equilibria. These include the whole plane of two groupwise rewards, the half-spaces in which any one of the four rewards exceeds a common threshold, and a region with all four rewards independently unbounded below. A bounded interval for two opposite observers also suffices with the other two unrestricted. At each fixed game the constructed profile has one fixed original uniform-equilibrium payoff.

Number the players cyclically modulo four. The groups are A={0,2}, B={1,3}; m(j)=j+2. Write O(i) for the opposite group. On nonempty coalitions set Z_i(S)=(r_i(S)-s_i)/l_i, where s_i is the own singleton reward and l_i>0. Live dates and perpetual Continue pay zero in the original game, and absorbed dates pay their coalition rewards. Use real a>2b>0. The singleton entry in row i is a at m(i), −b at both players in O(i), and zero at i. Every participant in its matched pair receives M. Each member of group g receives T_g on the opposite matched coalition. The numbers T_A,T_B range independently over the entire real plane.

Set x=(a+sqrt(a²−4b²))/2. Require some d≥0 with

    Z_(j−1)({j−1,j})≤−b+d,    Z_(j+1)({j+1,j})≤−b−d          (1)
    Z_i({i} union O(i))≤T_g       (i in g).                   (2)

For M≤x require d≤b. For x<M<a set

    c=a−M,  r=c/M,  k=(b+c)/(b+M),
    d≤min{b, M(r/k)(1−sqrt(k))}.                             (3)

For M≥a, condition (1) is unnecessary. In all regimes the 24 nonsingleton entries outside these specifications are arbitrary finite real numbers. At an equality in (2) the raw reward itself is permitted. Each such original game has an exact private-periodic terminal equilibrium against all complete unilateral behavioral deviations. The same profile supplies a fixed uniform-equilibrium payoff. The proof below also gives a partial completion-free result near x.

## The middle interval

On phase j, player j quits with probability t_g and player m(j) with probability u_g, where g contains j, 0≤u_g≤t_g<1 and t_g>0. All others Continue. Put C_g=(1−t_g)(1−u_g), D_g=t_g u_g. The passive absorption head to a member of g while the opposite group h is scheduled equals

    E_g=−b(1−C_h)+(b+T_g)D_h.

In normalized units, at an active phase the owner receives M u_g upon forcing Quit and the mate receives M t_g. Waiting against the mate gives a u_g+(1−u_g)W to the owner; its indifference requires the following quiet-date value W=−c u_g/(1−u_g). Waiting against the owner gives the analogous equation for the mate. Roles swap between visits of the same group, so both indifferences hold if

    E_g+C_h M t_g=−c u_g/(1−u_g),
    E_g+C_h M u_g=−c t_g/(1−t_g).                            (4)

These equations also impose indifference on a mate of zero hazard, which is sufficient for its prescribed Continue action. They need to hold for each of the two groups.

We have 0<r<k²<1. Indeed M>x>a/2 implies sqrt(Mc)<b and

    k−sqrt(r)=(1−sqrt(r))(b−sqrt(Mc))/(b+M)>0.

First impose C_A C_B=r. Then both equations (4) in row group g become the single equation

    (b+T_g)D_h=N(C_h),     N(C)=b+c−(b+M)C.                 (5)

To check this directly, move c u_g/(1−u_g) to the left in the first equation. By C_A C_B=c/M, the sum of that term and C_h M t_g is M C_h[t_g+u_g(1−t_g)]=M C_h(1−C_g)=M C_h−c. Interchanging t_g and u_g gives the second equation. With any fixed C in (0,1), D ranges over the full interval [0,P(C)] with P(C)=(1−sqrt(C))². For example vary the two survival probabilities with product C from (C,1) to (sqrt(C),sqrt(C)); continuity and their sum at least 2sqrt(C) give the assertion.

For z in I=[r/k,k] let C_A=z, C_B=r/z. Both C's lie in I, and both N's are nonnegative. For h=A,B let L_h be the set of z for which (5), in the other group's row, is feasible with D_h in [0,P(C_h)]. Equivalently

    0≤N(C_h)≤max(0,(b+T_g)P(C_h)).

Each L_h is closed and contains the endpoint for which C_h=k, since N(k)=0. If the L's meet, choose feasible D_A,D_B and recover t_g,u_g as above. This produces (4).

If the L's are disjoint, their union misses some z by connectedness of I. Fix such a z. With q_g=1−sqrt(C_g), both N(C_h)>(b+T_g)q_h². We instead seek t_g=u_g=v_g. Equation (4) then reads

    [c/(1−v_g)+M(1−v_h)²]v_g=2b v_h(1−v_h)−T_g v_h².       (6)

For w in [0,1] define f_g(w) by solving (6) for v_g in [0,1), replacing its right hand side by its positive part at v_h=w. The left hand side increases strictly from zero to infinity. The solution is continuous, with f_g(0)=0 and right derivative 2b/a there, by (6). Evaluated at (q_g,q_h), the excess of the original right side above the left in (6) is exactly N(C_h)−(b+T_g)q_h², by the product calculation for (5). Therefore f_A(q_B)>q_A and f_B(q_A)>q_B. Choose y in (0,q_A) with f_B(y)=q_B by continuity. Then f_A(f_B(y))>q_A>y, while f_A(f_B(w))<w for sufficiently small w>0 since (2b/a)²<1. Continuity gives a positive fixed point v_A in (0,y); put v_B=f_B(v_A). Both are positive since f_A(0)=0, so clipping the right hand sides made no changes at this fixed point. This proves (6).

It remains to check each quiet player. At any phase j, h is the active group with owner hazard t_h and mate hazard u_h. Relative to the passive head E_g, the immediate Quit payoff for the successor j+1 is at most −d(t_h−u_h), since the excesses on sole owner and sole mate absorption are at most −d and +d and (2) bounds the joint term. The corresponding bound at the predecessor j−1 is +d(t_h−u_h). Quiet players' Continue payoffs include E_g plus future value C_h M u_g at j+1 and C_h M t_g at j−1, as the next owner is j+1. For equal within-group hazards the excess bounds are zero and the future values are positive. On the product branch, t_g≥1−sqrt(C_g)≥1−sqrt(k); hence C_h M t_g≥(r/k)M(1−sqrt(k))≥d. All quiet comparisons follow.

The assigned active values and the passive recursions in (4) are therefore the policy values and satisfy every one-stage endpoint comparison. Each owner has positive hazard at its own recurring dates even when mate hazards vanish. Every deleted-player survival probability decays geometrically, uniformly over the deleted player's actions. Bellman iteration against any unilateral policy and then passage to the limit give exact terminal Nash. Upon restoring each value V to s_i+l_i V, the same inequalities and convergence apply, with arbitrary signed s_i, since absorption occurs almost surely even under deviation. For N-stage averages the error between a terminal payoff and its payout over the remaining fraction of N dates is at most a reward bound times the expected truncated waiting time divided by N. Deleted geometric tails bound this uniformly in unilateral deviations. The original initial-phase payoff is the resulting fixed uniform equilibrium target.

## Outer intervals

If M≥a, have both members of one matched pair Quit surely at date one. Each receives M and receives a upon waiting. Each outsider's forced Quit is capped by (2), so no deviation gains. Another sure quitter remains after deleting any one player.

If M≤x, only j plays at phase j, with hazard q=1−v, v=b/x. The normalized phase-j values in the order (j,j+1,j+2,j−1) are (0,−bq,bq/v,0). Indeed at j+1's quiet phase the next value is zero; for j+2 the recursion is a q−v b q=bq/v using a=b(v+1/v); for j−1 it is −bq+v bq/v=0. The owner is indifferent since its next value is zero. The inactive three forced-Quit values are q times their own pair-participant entries. The successor is capped at −bq, the mate at Mq≤xq, the predecessor at q(−b+d)≤0. Deleted geometric tails apply again. The passive pair and triple data are unused in this regime.

## Local completion-free branch above x

Fix the crossed entries with strict Z_(j−1)({j−1,j})<0 and Z_(j+1)({j+1,j})<−b. In place of (2), allow all four triple entries to be arbitrary fixed finite reals. Suppose the two B recipients of the matched A pair have common T_B>−b. The two A recipients of the B pair can now take independent arbitrary values. For all M sufficiently close to x from above, take C_B=k, D_B=0, C_A=r/k, D_A=N(C_A)/(b+T_B). We have 0<D_A<P(C_A) for sufficiently small M−x because k and sqrt(r) meet at b/x in (0,1) when M=x, and N(C_A) tends to zero. The case D_B=0 eliminates dependence on both A recipients' passive rewards. These choices solve (4), and the larger roots t_g tend to q=1−b/x while u_g tend to zero. All eight quiet comparisons are strict at the limiting four-solo policy by the strict crossed entry assumptions (the mate comparison is the separate active contact already imposed). They persist by continuity for each fixed higher completion. The same result holds with group names interchanged. The radius may depend on the fixed triple data.

## Any one sufficiently positive passive reward

Return to the common singleton data a,−b and x<M<a, and now allow four separate T_i. If max_i T_i>2c, the other three entries may take any finite real values. For every such T there exists d₀(T,a,b,M)>0 such that (1) for 0≤d≤d₀ and the individual triple caps Z_i({i} union O(i))≤T_i give an exact two-date equilibrium with at least three proper mixers. The 24 unmentioned nonsingleton rewards are arbitrary and do not enter d₀.

Let q_i denote the hazard of i when its group acts, and m its mate. If the opposing group uses w,z, put C=(1−w)(1−z) and E_i=−b(w+z−2wz)+T_i wz. Define on the closed unit cube

    H_i(q)=c q_m+(1−q_m)[E_i+C M q_m].

The projection π is coordinatewise onto [0,1]. Write N(y)=H(πy)+y−πy, on all of R⁴. Its zeros satisfy H_i=0 on 0<q_i<1, H_i≥0 at q_i=0 and H_i≤0 at q_i=1. Conversely each such q gives precisely y=q−H(q). The degree of N on a sufficiently large ball equals one because N(y)−y is bounded.

At zero the homogeneous leading normal map is G y₊+y₋, where G has diagonal zero, matched entry a, and crossed entries −b. Its only homogeneous zero is zero. Indeed G times the mate permutation is a strictly diagonally dominant irreducible M-matrix; its inverse is strictly positive by the Neumann series. Thus G⁻¹≫0. Any nonzero z≥0, Gz≥0 consequently has z≫0, so z_i(Gz)_i=0 for all i would imply Gz=0, impossible. This justifies replacing N by the homogeneous map on a sufficiently small sphere. To compute its degree take a small target −τ1. The empty support gives one preimage of determinant sign +1; a singleton has no solution since G_ii=0; a matched pair has no positive solution; each of the four crossed pairs has two active coordinates τ/b, all inactive inequalities strict, and sign −1. For any triple consisting of two mates and one other player, its matched coordinates are τ/(2b), and its other active coordinate is [τ+aτ/(2b)]/b. The unused row of Gz is strictly positive, and this principal determinant is 2ab²>0. There are four such triples. Full support would give z=−τG⁻¹1<0. Thus the index at the origin is 1−4+4=1.

At any zero with q_i=1, the mate satisfies H_m=c>0, hence q_m=0. In the two opposite rows H_j=(b+c)q_k−b and H_k=(b+c)q_j−b. Either one opposite player is sure and the other zero, or both mix with equal probability Q=b/(b+c). There are four vertices of the first type. Their inequalities are all strict and their four coordinates locally stay clipped, so each has index +1. For the second type, the sure row requires E_i(Q,Q)=Q²(T_i−2c)≤0. There is precisely one such face point for i if T_i≤2c, none for i if T_i>2c. When T_i<2c the sure and zero coordinates stay clipped locally in N, leaving the two-by-two Jacobian of the opposite mixed rows with zero diagonal, off-diagonal b+c, and negative determinant. Each such zero has index −1.

Equality T_i=2c has the same index. Perturb this one coordinate downward. In a neighborhood of the indicated face root, H_m>0 still forces q_m=0 at any zero, while the opposing hazards stay proper. With p=q_i they then take a common value q(p) solving

    q(p)[c/(1−q(p))+M(1−p)]=bp.

This increases strictly with p up to Q at p=1. For p<1, the remaining contact E_i(q(p),q(p))=0 is impossible for every T_i≤2c because T_i<2b(1/q(p)−1). Thus the only nearby zero of this homotopy is the boundary point with p=1, including at equality. Its y_i coordinate moves with the perturbation, but a small enclosing ball contains this zero throughout the homotopy. The index therefore remains −1.

We have accounted for index 1+4−#{i:T_i≤2c}. If at least one T_i>2c, this sum differs from the global index 1. There must be another zero, neither the origin nor a point with a sure coordinate. It has at least three positive coordinates. Indeed with a whole group zero, the other can contain at most one proper mixer by the H equations; a nonzero singleton there makes both idle players' H strictly negative. If there is precisely one proper mixer per group, its H is −b times the opposing hazard and cannot vanish.

For the actual alternating policy, a mixing row i has value M q_m at its active phase since H_i=0 sets the active endpoints equal. A zero row has active value
    V_i=[a q_m+(1−q_m)E_i]/[1−(1−q_m)C]≥M q_m
by H_i≥0, with a positive denominator. Its quiet-phase value is E_i+C V_i; for mixing rows use V_i=M q_m. Quiet forced-Quit exceeds E_i by at most d|w−z|, by the directed crossed bounds and the triple cap. If q_m>0 then C M q_m>0 covers this loss for sufficiently small positive d. If q_m=0 then i is the sole mixer of its group, and both opposite players mix necessarily at equal hazards, because their contact equations against just that sole mixer are identical strictly increasing equations for their respective mates' rates. In that case |w−z|=0. The minimum of these finitely many admissible positive bounds gives d₀ using only T,a,b,M and the chosen proper zero; equivalently select by finite polynomial feasibility. No off-calendar reward enters. Every player faces at least one proper mixing rival, and deleted survival decays geometrically, so the computed policy values and the endpoint tests lift to unrestricted deviations, original signed levels, and the uniform target.

## Four independent passive rewards and heterogeneous singleton entries

Here and in the next section the numbers T_i=Z_i(O(i)) can be different for all four players. Write G_ij=Z_i({j}), J_ij=Z_i({i,j}), M_i=J_i,m(i), c_i=G_i,m(i)−M_i. The following tests use the original data in these row units. The singleton specializations above are unnecessary.

At alternate dates schedule the two members of A or the two members of B. A given player i uses a fixed hazard v_i on each visit of its group. For each i let j,k be the opposite players, w=v_j, z=v_k and C=(1−w)(1−z). Define the centered absorbed Wait contribution and forced-Quit offer at that opposite phase by

    E_i(w,z)=G_ij w(1−z)+G_ik z(1−w)+T_i wz,
    Q_i(w,z)=J_ij w(1−z)+J_ik z(1−w)+Z_i({i,j,k})wz.

Assume c_i>0, M_i≥0. Choose raw box coordinates 0<L_i<U_i<1. At the four vertices of [L_j,U_j] times [L_k,U_k], require the following three inequalities, where m=m(i):

    L_m[c_i/(1−L_m)+M_i C] ≤ −E_i(w,z)
                          ≤ U_m[c_i/(1−U_m)+M_i C],
    Q_i(w,z) ≤ E_i(w,z)+C M_i L_m.                           (7)

All three differences are bilinear in w,z and therefore have the asserted signs on the entire rectangle. For given w,z in the box, the first two inequalities imply that the equation

    v_m[c_i/(1−v_m)+M_i C]=−E_i(w,z)                         (8)

has a unique continuous solution v_m in [L_m,U_m], by strict increase in v_m. The four responses, assigning the i-th equation's output to its mate, form a continuous self-map of the four-dimensional box. At a Brouwer fixed point, the active values M_i v_m and next passive values E_i+C M_i v_m satisfy active indifference by (8). The last inequality in (7) checks the passive Quit endpoint. All four hazards are positive and proper, yielding exact terminal Nash and the fixed uniform payoff as before. No smallness restriction on any unsampled reward is used.

For an explicit box of unbounded independent passive rewards, restore the singleton pattern a,−b and common x<M<a, but allow four different T_i. Put L=1−r^(1/4). For ANY four T_i≤−b, choose any d≥0, use (1), and set

    Z_i({i} union O(i)) ≤ T_i−d(1/L−1).                     (9)

These requirements suffice for (7). Indeed at (w,z)=(L,L) the excess −E_i−L[c/(1−L)+M C] equals N(sqrt(r))−(b+T_i)L²>0. On [L,1]², −E_i=b(w+z)+(−2b−T_i)wz is nondecreasing coordinatewise (each partial is at least min(b,−b−T_i)); the subtracted expression decreases with w,z. Thus the lower test holds throughout. To choose U_m<1 sufficiently high, take U_m>L with c U_m/(1−U_m)≥max(b,−T_i); the right side bounds −E_i since it is a weighted sum of 0,b,b,−T_i with weights totaling one. Condition (1) bounds Q_i−E_i by d|w−z|−d(1/L−1)wz≤0, since |w−z|/(wz)=|1/z−1/w|≤1/L−1. This proves the last test. Each of these games permits all 24 unused nonsingleton entries to vary arbitrarily. Applying (7) directly often permits (2) itself: for fixed T in the orthant the positive C M L on the compact box allows some strictly positive d under (2).

## A matched pair and a single player on alternating dates

Write A={i,j}, B={k,l}. Only k is scheduled on visits to B; l always waits. For h in A require M_h≥0, c_h>0, b_h=−G_hk>0 and d_h=−G_kh>0. No sign is imposed on the singleton row of l. Require the passive reward of k on A to satisfy

    T_k>d_i c_i/b_i+d_j c_j/b_j.                            (10)

For each p in (0,1) define q_m(h)(p) uniquely by

    q_m(h)[c_h/(1−q_m(h))+M_h(1−p)]=b_h p.

It is strictly increasing in p, tends to zero at the left endpoint and to b_h/(b_h+c_h) at the right. These assertions follow by strict increase in q and the strictly increasing right side, while the coefficient M_h(1−p) is nonincreasing. Select p as the unique root

    T_k=d_i(1/q_j(p)−1)+d_j(1/q_i(p)−1).

The right side decreases continuously from infinity to the threshold in (10). At phases of A use its two hazards q_i(p),q_j(p), and let k use p on B phases. Write C_A=(1−q_i)(1−q_j), E_h,Q_h for the heads above at the A phase for h in B, and

    V_l=[p G_lk+(1−p)E_l]/[1−(1−p)C_A].

The following raw tests at the computed numbers suffice:

    p J_hk ≤ p G_hk+(1−p)M_h q_m(h)          (h in A),
    Q_k ≤ 0,        V_l ≥ p J_lk,       Q_l ≤ E_l+C_A V_l.   (11)

The value for h in A on its active date is M_h q_m(h); equality of its active endpoints is exactly its defining scalar equation. Its quiet-date Quit comparison is the first test. The value of k at its sole active date is zero and E_k=0 by the defining equation for p, hence both its active endpoints equal zero and its quiet comparison is Q_k≤0. For l the two actual values under Continue are V_l on B dates and E_l+C_A V_l on A dates, by the two-term recursion. The last two tests are exactly its forced-Quit comparisons. All three mixing players see another positive hazard every period, yielding exact terminal Nash even against Never and the finite-horizon conclusion. All rewards unmentioned in these calculations are arbitrary finite numbers, including the two passive rewards to A at the opposite matched pair (which never actually quits jointly).

In the common-M middle interval, an immediate raw family occurs whenever both T's in B exceed 2c. Choose k with lower T in B. Then

    q_i=q_j=q=2b/(T_k+2b),     p=q[c/(1−q)+M]/(b+M q).

Use (1) with d≤(1−p)Mq/p and enforce (2) only for k,l. The A quiet tests follow from the bound on d. The two equal A rates cancel their opposite directed cross increments, so Q_k≤E_k=0 and Q_l≤E_l. Here E_l=(T_l−T_k)q²≥0 and V_l≥Mp because multiplying the latter inequality by 1−(1−p)C_A leaves p(a−M)+pM(1−p)C_A+(1−p)E_l≥0. Thus (11) holds. If T_l<T_k the formulas (10)–(11) still apply as stated, and include cases with opposite signs within B.

## A bounded interval for two opposite observers

Fix a=3,b=1,M=8/3,c=1/3. Take T_1 and T_3 independently in [−1/2,1/3]; the other T_0,T_2 are arbitrary. Assume (1) with 0≤d≤1/10, and cap the triple join at the opposite matched pair only for players 1 and 3, by their own T_i. No other higher rewards enter. The following four dates give exact terminal Nash and the fixed uniform target.

On phase 0 both 0 and 2 mix at t. On phase 1 only player 1 mixes, at 1−s₁. On phase 2 both 0 and 2 mix at u, and on phase 3 only 3 mixes, at 1−s₃. For t,u in [l,h]=[21/50,17/25] put

    s₁=(1−ct/(1−t))/(1+Mu),   s₃=(1−cu/(1−u))/(1+Mt),
    E(v,T)=−2v+(2+T)v².

The mixed pair players' active values are Mt and Mu. At phase 0 their next value is −(1−s₁)+s₁Mu=−ct/(1−t) by definition, hence both are indifferent. The phase-2 check interchanges t,u and s₁,s₃. The sole players 1 and 3 have value zero at their active dates exactly when

    G(t,u;T₁)=E(u,T₁)+(1−u)²[3(1−s₃)+s₃ E(t,T₁)]=0,
    G(u,t;T₃)=0.

Indeed after player 1 continues, its phase-2 value contains the passive head E(u,T₁); on surviving it gets the mate-singleton reward 3 at phase 3 or reaches the next E(t,T₁), then its own active value zero. For u=l, G(t,l;−1/2)>0; for u=h, G(t,h;1/3)<0. The function increases with its passive parameter on the square, and the swapped equations have the corresponding signs on the t faces. Poincaré–Miranda gives a simultaneous zero in its interior.

At the sole-1 date the mate's waiting advantage over joining is c(1−s₁)+s₁ E(u,T₃)>0. For 0 and 2 the waiting advantage is at least s₁Mu−(1−s₁)/10>0; the other solo date is symmetric. At a joint visit the two crossed singletons have equal probability, so the two opposite directed increments have nonpositive combined contribution to immediate Quit. The joining triple is capped. The next value for either quiet player is zero on its own date, or at least the positive M(1−s) at its mate's. These exhaust the endpoint comparisons.

Here are exact checks of the rational signs. In the following order take

    G(t,l;−1/2), −G(t,h;1/3), c(1−s₁)+s₁ E(u,−1/2),
    s₁Mu−(1−s₁)/10, s₁, 1−s₁.

Write each as a cancellation over the rationals with relatively prime integer numerator and denominator and denominator positive at (l,l). The minimum tensor Bernstein coefficients of the numerator and denominator on the square are, respectively,

    (135261/1250,31800), (86037/625,11925), (11277/62500,7632/625),
    (2589/625,7632/125), (7/25,1272/625), (1097/625,1272/625).

For verification substitute t=l+(h−l)X,u=l+(h−l)Y. For polynomial coefficients A_jk in the monomial basis of bidegree m,n the (i,e) Bernstein coefficient is the sum of A_jk binom(i,j)binom(e,k)/(binom(m,j)binom(n,k)) over j≤i,k≤e. Their strict positivity proves the six inequalities throughout the closed square. Exchanging the variables checks the other solo date. The same strict signs persist for all common a,b,M sufficiently close to (3,1,8/3) in these formulas, using s₁=(b−ct/(1−t))/(b+Mu), the interchanged s₃, E(v,T)=−2bv+(2b+T)v², and replacing the mate-singleton value 3 in G by a.

## Coverage and formal consumers

As one separating example set a=3, b=1, M=8/3 and take, in cyclic order, the four observer payoffs (−3,1/4,−17,7/8). The single-high-coordinate test applies because 7/8>2/3. The four distinct observer payoffs remain distinct after any relabeling; retaining −1 as the crossed singleton unit fixes each row normalization. This excludes the common-passive-payoff ray. Taking any admissible 0<d<1 with equality in the crossed bounds makes h(−1+d)>−1 for every h in [0,1], so no one-owner repeated hazard meets all outsider comparisons. At either four-solo rotation with the outer-interval hazard q=1−1/x, the mate’s offer (8/3)q exceeds its prescribed xq. The game may have any values at the 24 unpriced nonsingleton coordinates, including arbitrarily large values with all four passive rewards fixed. The sufficient regions above leave other matched configurations and arbitrary four-player tables open.

The proof supplies the policy recursion, forced-Quit bound, exact Continue, and deleted period-product contraction for the proper schedules. These are the hypotheses of isεAsymptoticNash_quittingCyclicBehaviorProfile_of_quitError_exactContinue in UniformEquilibrium/Quitting/Cycles/CyclicSupersolution.lean at error zero. The sure-pair case checks both endpoints directly; the Continue bound there is weak, as permitted by isεAsymptoticNash_quittingCyclicBehaviorProfile_of_quitError_and_continueUpperBound in the same file. In UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean, quittingGame_fixedProfile_uniformPayoffWitnesses_of_terminalNash_exact and quittingGame_isUniformEquilibriumPayoff_of_terminalNash_exact give the fixed-target finite-average consequences. These declarations cover the semantic handoff. The raw production arguments in this note are ordinary mathematics.
