# Date concentration, collisions, symmetry and period length on the cyclic four-player family

Four owners draw independent private stopping times on the natural dates and Never. At the first nonempty stopping coalition T, owner i receives 1+Zᵢ(T). Perpetual continuation pays zero. All indices are modulo four and L is real with L≥10¹⁴. For owner i, write a,b,c for the hazards of i+1,i+2,i−1. Define its native rewards on coalitions containing i by the multilinear forced-Quit offer

    Qᵢ=L(a−b)+a[5(1−b)(1−c)+bc].

Evaluate this formula at the binary rival mask for each participant reward. When i is absent, its native payoff on the respective seven rival masks a,b,c,ab,ac,bc,abc is −1,6,−1,−L−1,L+2,0,13. Each native own singleton pays zero. Total welfare on singletons, pairs and the grand coalition is four; on triples it is thirteen. This specific family has a uniform-equilibrium payoff at every such L. The proof and the broader sufficient payoff test appear in [A welfare bound gives uniform equilibrium on a nonlinear cyclic family](../exports/UNIFORM_EQUILIBRIUM_FROM_A_BOUND_ON_POSITIVE_QUIT_OFFERS.md).

A player's terminal regret is its best expected payoff over all unilateral private stopping laws minus its prescribed expected payoff. Its best payoff equals the supremum over all finite deadlines and literal Never. On the native table, as a deterministic deadline tends to infinity its offer tends to the literal Never offer, since waiting forever and quitting alone both pay zero if all rivals wait forever. On the unit-raised table every finite offer gains one and the Never offer gains at most one. Its full cap therefore gains one, and the prescribed payoff gains one minus joint Never probability. Total regret on the original game equals native total regret plus four times joint Never. In this note an accurate sequence has original total terminal regret tending to zero at fixed L.

## Calendar and payoff bounds

Write s for the probability all players survive until just before a physical date and q for its conditional hazards. Put

    d_L=1026/L.

For any sequence of original independent profiles with total initial regret tending to zero, and each fixed η>0, every subsequential limit of hazard vectors at dates of reach s≥η has at least one zero coordinate and maximum coordinate ≤d_L. This allows the dates and the profiles to vary together. Consequently the largest single-date first-exit probability has limsup at most 3d_L, and the probability of a nonsingleton first-quitter coalition has limsup at most 3d_L. To capture half of the first-exit measure the number of physically distinct dates has liminf at least 1/(6d_L), irrespective of the gaps between them. At L=10^14 this requires more than sixteen billion dates. All four limiting native prescribed payoffs at any positive-reach restart lie in [−500,500], independently of L. The linked payoff theorem guarantees arbitrarily accurate profiles at each finite L.

**Two one-date comparisons.** On the diagonal the sum R of the four bounded terms in Q satisfies

    4−R(t,t,t,t)=4(1−t)(6t²−4t+1)≥4(1−t)/3.

The sum R has Lipschitz constant at most 100 in the maximum norm since each of three derivatives in each of four summands has magnitude at most six. Writing d=Σ(1−qᵢ), the sum also satisfies R(q)≤4−d+5d²/2. Indeed for the terms involving two missing-coordinate factors their four products are bounded in sum by d²/2, and the remaining factors in R contribute at most Σqᵢ.

A sure opening cannot be Nash even with arbitrary continuation values in [−L−6,L+6]. If owner 0 is sure write y=q_1,z=q_2,w=q_3. For owners 1,2,3 the respective Quit-minus-Wait differences, independent of continuation since 0 is sure, are

    Lw(z−1)−9wz−w−3z+1,
    L(2w−1−wy)−19wy+7w+6y−6,
    L(1−z)−5yz−5y−8z+6.

If w=1 the first difference is negative, so y=0; the second is then positive, giving z=1, and then the third is negative. Hence w<1, and its Wait inequality forces z≥1−12/L. Now the first difference is negative again, giving y=0. Owner 0 has Q_0=−Lz while its passive head payoff is 6z(1−w)−w(1−z) and its rival survival is (1−z)(1−w). Even the lowest proposed continuation gives Wait greater than −15, contradicting sure Quit. Rotation exhausts all sure owners. In particular this includes the refusal punishments after a sure opening on the native table and its unit row raise.

**Getting an infinite sequence of comparisons.** A positive row shift of one gives original total regret equal to native total regret plus four times joint Never. Hence both native regret and joint Never vanish. Restart at the chosen dates of reach at least η. A player who adheres to its original strategy until the live restart and then optimizes its entire continuation witnesses that its initial regret is at least the restart survival times its conditional regret. Joint Never conditional on the restart likewise tends to zero. Extract subsequences diagonally on each fixed future time, retaining native prescribed values u(t), unrestricted caps, and the four hazards q(t). At the initial restart vanishing regret gives equality of actual prescribed and cap values. The native child values are bounded by L+5 in absolute value. A sure hazard here would give a sure Nash stage row at a bounded continuation: the true regret decomposition has nonnegative assigned Quit and Wait losses at the child cap. This contradicts the established sure-opening exclusion. Therefore the limiting survival to the next date is positive. Inductively every fixed later restart still has positive limiting reach and vanishing native regret and joint Never, and every limiting hazard is strictly below one. This argument permits an entirely blank pointwise limit with stopping mass escaping through dates.

The total welfare in every native absorbing column lies between four and thirteen. Thus 4≤∑u_i(t)≤13 for all t. Every u_i(t) dominates its current Quit offer Q_i, with equality if q_i(t)>0. Since all hazards are proper, the current Wait identity is exact, u_i(t)=P_i+H_i u_i(t+1): a positive chance of the prescribed Wait forces that action optimal, and the next conditional value equals the cap. Here H_i is the product of the three opponent continue probabilities and P_i the unnormalized passive head payoff.

**A spatial and temporal maximum estimate.** For cyclic index k=i+1 let a=q_k(t), b=q_(k+1)(t), c=q_(k+2)(t), H=(1−a)(1−b)(1−c), and ℓ_(k,t)=a−b. The nonnegative term R_i in Q_i=L(a−b)+R_i is at most five. Thus u_i(t)−L(a−b)≥0. Summing in i cancels the four spatial differences and shows each of these four residuals is at most thirteen, including for an inactive owner. The coefficient of L in P_i is a(c−b), while its remainder is bounded by 13(1−H). The Wait identities yield at every k,t≥0

    |ℓ_(k,t)+a ℓ_(k+1,t)−H ℓ_(k,t+1)|≤e,       e=39/L.

Let D=sup_{k,t}|ℓ_(k,t)|. By compactness we can shift increasingly near-maximal dates to the origin, extract a full forward hazard path, and assume this supremum is attained there. The inequality and the global bound D pass to the limit. At the maximizing position,

    (1−a)(b+c−bc)D≤e,       a(D−|b−c|)≤e,

since a+H≤1. If a≤1/2, the first inequality gives b,c≤2e/D when D>0. If D²>8e these are both below D/4, so a≥3D/4 and the second inequality fails. If a>1/2, the approximate recursion gives |c−a|≤e/a: for ℓ=D it forces b−c≤−D+e/a, with the reverse estimate from |b−c|≤D; for ℓ=−D the signs reverse. Hence c≥1/3 and |b−c|≥D−2e. The first displayed inequality implies (1−a)D≤3e. Apply the original recursion at the next spatial index on this same date; its coefficient deficit is at least (1−b)c. Since |b−c|≥D−2e, this gives (1−b)cD≤3e and therefore (1−b)D≤9e. Consequently D=|a−b|≤9e/D. We obtain D≤3√e in both cases. On the four-cycle the spread between any two coordinates at any date is at most 2D≤d₀, where d₀=6√(39/L).

Were every hazard at some date positive, all u_i=Q_i there and hence R(q):=∑R_i=∑u_i≥4. For r=max q_i≤0.91, the previously computed diagonal gap 4−R(r,r,r,r)≥4(1−r)/3 and the bound |R(q)−R(r,r,r,r)|≤100d₀ contradict this for L≥10^14. If r>0.91, all four hazards exceed 0.91−d₀. Then 0<s₀:=∑(1−q_i)<2/5 and R(q)≤4−s₀+5s₀²/2<4. Thus at least one owner is quiet and the largest remaining hazard is ≤d₀<1/1000.

**An inverse linear bound on every hazard.** Set g_(k,t)=u_i(t)/L=ℓ_(k,t)+s_(k,t)/L, where the previously proved residual bounds are 0≤s_(k,t)≤13. Rewriting the exact Wait identity in g gives

    |g_(k,t)+a g_(k+1,t)−H g_(k,t+1)|≤13(1−H+a)/L.

Indeed the passive remainder is at most 13(1−H) and replacing b−c by g_(k+1,t) contributes at most 13a. Take G=sup|g_(k,t)|, attained after time shifts and compact extraction of both the values and hazards. All hazards on this limiting path remain below 1/1000 and every date has a quiet owner. The two deficits at a maximizing coordinate satisfy

    (1−a)(b+c−bc)G≤13(2a+b+c)/L,
    a(G−|g_(k+1,t)|)≤13(2a+b+c)/L.

Here 1−H≤a+b+c. Since the hazards are small, (1−a)(b+c−bc)≥(b+c)/2. Thus (b+c)(G−26/L)≤52a/L. If G≥500/L then a>0 (otherwise b=c=0 and |g|≤13/L), and b+c<a/8. Consequently the maximizing g is positive, G≥a−b≥7a/8 and |g_(k+1,t)|≤a/8+13/L<G/2. The second inequality now gives aG/2<28a/L, contrary to G≥500/L. Thus |u_i(t)|≤500 for every owner and every date on the original path. Every adjacent hazard difference is at most (500+13)/L; a path of at most two edges to a quiet owner gives max q≤1026/L.

**Concentration consequences.** By subsequences these bounds hold uniformly in the limit over all dates of reach at least η. The conditional probability of an exit is ≤3d_L on every limiting vector. Any later date of smaller reach has first-exit probability at most η. For the collision estimate use also the continuous ratio of the conditional probability of two or more quits to the probability of at least one, extended by zero at the blank vector. Continuity there follows from the quadratic union bound and the lower bound max q_i on the exit probability. With at most three active owners the union bound is at most d_L∑q_i, while the exit probability is at least (∑q_i)/3. Thus on all limiting early dates the conditional ratio is ≤3d_L. Their first-exit masses sum to at most one; the entire suffix beyond the reach threshold has total mass ≤η. Taking limsup and then η↓0 proves both concentration claims. The count of dates follows from the maximum unconditional date mass bound. In particular the comparison cannot be evaded by inserting gaps or adding tiny off-support probabilities.

**A lower bound for collision probability.** For every fixed L≥10¹⁴ the liminf collision probability on every accurate sequence is at least 1/(10⁴L). Its order on this family is exactly 1/L. The identities of the colliding players and their dates can change.

We give the discrete estimate also used below for symmetry. For one actual profile let S_t be survival before date t, U_t its conditional native payoff, z_t=S_t U_t and A_t=z_t−z_(t+1), the unconditional vector of rewards paid at date t. Terms after zero reach are set to zero. Write C for its total nonsingleton first-exit probability and m for its largest single-date first-exit mass. The matrix Γ is symmetric, with inverse K having cyclic first row (1,3,17,3)/96; in particular K is strictly positive entrywise. Suppose along a sequence (L fixed or varying with L≥10^14) that original regret, m and LC all tend to zero. This is impossible.

First every limiting initial native payoff is nonnegative. Its coordinates are bounded because the absolute value of any unconditional future column contribution in any one row is at most 6 times the respective singleton probability plus (L+5) times the collision probability. To bound one coordinate below, fix ε,η>0. If its initial value is below −ε, stop at the first date where its conditional value is ≥−ε or its reach is <η. Up to that cut the conditional native regret is less than ε/2 for sufficiently late profiles in the sequence, by the initial regret bound divided by η. Thus its current Quit offer is at most −ε/2. Since Q_i≥−L b where b is the opposite rival's hazard, b≥ε/(2L). The only negative singleton rewards in this row are −1 on the two remaining rivals, with hazards a,c. At that date a+c≤(2L/ε)(ab+bc)≤(4L/ε) Pr(at least two quits). Negative payments on collisions are also bounded by L+5 in absolute value. Summing these lower bounds with the actual reach weights loses at most (4L/ε+L+5)C. If the cut stops by reach threshold, its remaining unconditional expected payoff is bounded in magnitude by 6η+(L+5)C. If it stops by the value threshold the remaining term is ≥−ε. If there is no finite cut, its unpaid expected payoff tends to zero as the calendar runs out of finite exits. Let the sequence tend to its limit and then let ε,η tend to zero. Joint Never tends to zero and every absorbing column has welfare at least four, so the sum of each limiting initial payoff is at least four. Hence liminf z₁ᵀKz₁>0 by strict entrywise positivity.

On the other hand z_t→0 at the end of each individual calendar, because future finite reward mass vanishes. Telescoping its quadratic form gives

    z₁ᵀKz₁=∑_t [2 z_tᵀK A_t−A_tᵀK A_t].

The absolute sum of the last terms tends to zero: Σ‖A_t‖ is uniformly bounded by the singleton and collision payment estimate, and max‖A_t‖→0 by m,LC→0. Replacing A_t in the first term by S_tΓ q(t) costs o(1) in sum. Indeed singleton probabilities differ from individual hazards only on a multiple-quit draw, and the absolute error in each conditional payment is bounded by a fixed multiple of (L+5) times its conditional collision probability. Also all ‖z_t‖ are uniformly bounded. It remains to upper bound Σ_t S_t² Σ_i q_i(t)U_i(t). Let B_i(t) be the complete native response cap at t. The true regret recursion, iterated over physical dates, gives

    Σ_t S_t q_i(t)(B_i(t)−Q_i(q(t))) ≤ B_i(1)−U_i(1).

This follows by splitting prescribed action regret into the nonnegative assigned Quit and Wait losses at the following cap and the jointly survived child regret. Since U_i(t)≤B_i(t), we can upper bound by replacing U_i by the immediate Quit offer at total cost at most the initial native regret. Finally |q_i Q_i|≤(L+5)q_i(q_(i+1)+q_(i+2)), whose weighted sum is O(LC) since every such pair product contributes to a collision. The limsup of the quadratic form is therefore at most zero, the contradiction.

Here are explicit bounds from the same calculation. Fix L≥10¹⁴. Suppose on a subsequence that C has limit at most 10⁻⁴/L, and extract a limiting initial native payoff z. With ε=0.02 and η↓0, the stopped-payoff estimate gives zᵢ≥−0.02−[4L/0.02+2(L+5)]10⁻⁴/L>−0.041. Put y=z+0.041·1 and w=Σyᵢ≥4.164. Since K has minimum entry 1/96 and row sums 1/4, we obtain

    zᵀKz ≥ w²/96−(0.041/2)w+0.041² > 0.09.

The quadratic on the right is increasing for w≥4.164. In the calendar telescope, Σ_t‖A_t‖∞ and sup_t‖z_t‖∞ are each at most 6+(L+5)C, with limsup <6.001. Also max_t‖A_t‖∞≤6m+(L+5)C has limsup <0.000101 since limsup m≤3078/L. For every t the difference A_t−S_tΓq(t) arises only on multiple quits: the true collision reward is at most L+5 in magnitude, while the sum of the at most four counted singleton rewards is at most 24. Thus Σ_t‖A_t−S_tΓq(t)‖∞≤(L+29)C has limsup <0.000101. All entries of K are nonnegative and sum to one. In the remaining first term, each of the eight pair products in Σ_i q_i(q_(i+1)+q_(i+2)) is bounded by the conditional collision probability. The vanishing true regret and the preceding telescope therefore give

    zᵀKz ≤ 6.001·0.000101 + 2·6.001·0.000101 + 16(L+5)10⁻⁴/L < 0.005.

This proves the claimed lower bound at every specified L. A single physical date has limiting unconditional collision mass at most 3d_L²: at positive reach apply the pair union bound with at most three active hazards, and dates of vanishing reach have vanishing mass. This is uniform over choices of date by subsequences. It follows that the number of distinct dates needed to account for half the nonsingleton first-exit probability has liminf at least L/(6·10⁴·1026²). At L=10¹⁴ this ratio exceeds 1,583, requiring at least 1,584 dates. The half-of-all-exits count above uses the much larger singleton mass as well.

**Half-turn symmetry.** On the unit-raised cyclic game the full regret also has a positive floor over all calendars invariant under rotation by two players, the only nontrivial proper subgroup of the cyclic rotations. At every physical date such a calendar has hazards (x,y,x,y). In a limiting high-reach path as above, both cannot be positive: if both were positive, all native row values would equal Quit. With t=(x+y)/2 the sum of those offers is

    2(x+y)[5(1−x)(1−y)+xy]≤4t[5(1−t)²+t²]<4,

using xy≤t² and propriety. This contradicts the total payoff floor. If x>0 and y=0, the parity pair using x has native value −Lx and, by the Wait identity, next-date value −(L+6)x/(1−x)<0. The following date cannot be blank since its offers would all be zero. If only the other parity were active, both parities would have negative values by symmetry and the active Quit equality, violating the welfare floor. Hence the same parity must act again. Its hazard becomes at least (1+6/L)x, and iteration violates the probability bound. Rotation covers y>0. Therefore at every date of positive limiting reach the hazards converge to zero, uniformly over dates with reach at least any fixed η>0. Splitting at that reach threshold as above gives m→0 and C→0. At fixed L the discrete quadratic estimate rules out this sequence. By coupling, profiles at vanishing marginal total-variation distance from a half-turn-invariant calendar likewise cannot have vanishing regret.

## Period length grows at least linearly in the payoff parameter

There are absolute c>0 and L₀ such that for every L≥L₀, the infimum of total regret over calendars periodic from their first date with period ≤cL is positive. A period K means q(t+K)=q(t) at all dates, with arbitrary four product hazards at every phase. The calendar and its period may depend on the desired accuracy. The positive infimum may depend on L. The physical duration before absorption can comprise arbitrarily many repetitions.

We use the bounds above: any limiting positive-reach row on an accurate sequence is proper, has a quiet owner, all hazards ≤1026/L and all native continuation values bounded by 500. Its relative welfare is between 4 and 13, with singleton welfare exactly 4. For all L≥10¹⁴ the collision probability has liminf ≥10⁻⁴/L, and joint Never tends to zero.

Suppose instead L→∞ and periods K=o(L) admitted arbitrarily accurate calendars at each fixed L. Passing first to a subsequence at fixed L gives a single exact periodic sequence of limiting stage rows and continuation values, by the finite number of phases and positive survival at each date. It is nonblank: if all hazards vanished in the fixed-period limit then the conditional collision/exit ratio would vanish uniformly and so would total collision probability. Thus its joint survival over one period is below one. Its continuation values are its actual native expected payoffs by iterating the prescribed recursion. This also passes the first-exit law to the limit (the joint cycle survival stays below one at each fixed L). The conditional welfare is 4+O(1/L) at every phase: on every conditional phase the collision/exit ratio is at most 3078/L. All stage Quit inequalities and equality on positive hazards hold. Since every hazard is proper, each Wait equation holds as equality.

Write x=Lq on each date, X=Σxᵢ and let a bar denote the uniform average over the K dates. Use cyclic indices. With U the current native value and U⁺ the following one, put Rᵢ=Qᵢ−x_(i+1)+x_(i+2). The explicit rewards give 0≤Rᵢ≤5x_(i+1)/L. The coefficient of L in the passive head payoff is q_(i+1)(q_(i−1)−q_(i+2)); the bounded remaining multilinear terms have linear part Γq, where Γ has cyclic first row (0,−1,6,−1). Whenever x_(i+1)>0 the equality U_(i+1)=x_(i+2)−x_(i−1)+R_(i+1) holds. Consequently the exact Wait identities yield, uniformly in date and L,

    L(Uᵢ−Uᵢ⁺)=(Γx)ᵢ−(Σ_{j≠i}xⱼ)Uᵢ⁺−x_(i+1)U_(i+1)+O(X/L).

Indeed all xᵢ are uniformly bounded, so each omitted quadratic bounded-payoff term and the second-order remainder of the rival-survival product contributes O(X/L) on this scale. Thus each coordinate varies by at most O(K X̄/L)=o(X̄) during the period. Let u be a subsequential limit of its common values and m the limit of x̄/X̄. Then Σu=4, m≥0, Σm=1. Averaging the difference equation gives exactly

    (Γm)ᵢ=(1−mᵢ)uᵢ+m_(i+1)u_(i+1).                    (1)

Every subsequential limit of possible phase vectors x obeys

    uᵢ≥x_(i+1)−x_(i+2),     xᵢ[uᵢ−x_(i+1)+x_(i+2)]=0,     min x=0.  (2)

For any fixed u, normalized mean traffic m belongs to mixtures of normalized nonzero solutions x/Σx of (2) and of traffic on the owners with uᵢ=0. Indeed weight the phase distribution by X/X̄, include x/X as another compact coordinate, and take weak limits. If x→0 while a color has nonzero limiting share it is active along a subsequence and its limiting value is zero. If some uᵢ<0, (2) forces X uniformly bounded below. In that case ordinary unweighted limiting phase distributions suffice and m is proportional to their actual mean. If there is only a single possible nonzero limiting vector and one negative payoff, the limit is that vector on every phase.

We exclude (1)–(2), also using the exact quiet owner of the prelimit at one point. A single possible triple with support 012, up to a cyclic rotation, cannot satisfy (1). Write its x=(X,Y,Z,0) with X,Y,Z>0. Then u₁=Z, u₂=−X and (1) at row 1, multiplied by Σx, reads −X−Z=Z². A single vector on opposite owners 0,2 cannot solve the system either: u₀=−x₂<0 whereas the same row of (1) requires u₀=6.

If some u₀=−A<0, rotate this owner to zero. At every limiting phase x₂≥A+x₁>0 and u₂=x₃−x₀. First suppose u₂>0. Then x₃>0 and u₃=x₀−x₁. At least one of x₀,x₁ is zero. If u₃>0 this fixes x₀=u₃, x₁=0, x₂=A, x₃=u₃+u₂; if u₃<0 it fixes x₁=−u₃, x₀=0, x₃=u₂, x₂=u₁+u₂. Either possibility has a single triple. If u₃=0 we have x₀=x₁=0 always; row 3 of (1) reads 0=−m₂, impossible.

If u₂=−C<0 then x₀=C+x₃>0, x₂=A+x₁>0 and x₁x₃=0. Put u₁=B,u₃=D. Activity of 1 fixes x₁=B−A and activity of 3 fixes x₃=D−C. If B<A then x₃≥A−B>0, so there is just one triple; similarly for D<C. Thus take B≥A,D≥C and arrange B≥D by half-turn. Let y₁,y₃ be the unweighted means of x₁,x₃, so the means of x₀,x₂ are C+y₃,A+y₁. Row 1 of (1), multiplied by the positive mean total, gives

    (5−2B)y₃=(1+B)(A+C)−AC+(1+B−C)y₁>0.

Here B≥D≥C. Thus D≤B<5/2. Adding rows 0 and 2 now gives

    (4+2A+C−B)y₁+(4+2C+A−D)y₃+6(A+C)+A²+C²=0,

whose left side is positive.

**Negative owner opposite a zero.** Rotate to u_0=−A<0, u_2=0, with u_1=B and u_3=C. All tangent states satisfy x_2≥x_1+A, so x_2>0 and x_3=x_0. In particular their amplitudes are bounded away from zero, and ordinary time-averaging applies. If x_0>0 then x_3>0, x_1=0 (a full state is impossible), x_2=A, and x_0=C>0. If x_0 vanishes almost surely, m_0=m_3=0; row 2 gives m_2=1 and row 0 gives −A=6. If only states with x_0>0 occur then the state is the single triple just computed, already excluded by the fixed-state comparison. Hence C>0 and a state with x_0=0 occurs. Its row 1 gives B≥x_2≥A, whence C≤4 since B+C=4+A. Write m_0=m_3=z, m_1=y,m_2=x with x≥y. Mean rows 2 and 3 and normalization give

    x=1−(7−C)z,   y=(5−C)z,   z=(C+1)/(36−6C+A).

Thus A≥8−2(C−4)² from x≥y. Substituting into row 0 gives

    0=−A²−A(C²−11C+36)+C³−15C²+88C−148.

The last cubic is strictly increasing on [0,4] (its derivative has negative discriminant and positive leading coefficient), takes −49/8 at 5/2 and 28 at 4. The coefficient C²−11C+36 is at least 8 on this interval. If C≤5/2 all terms are negative. If C>5/2 then A>7/2 and −8A+28<0. This finishes the opposite-zero case.

Finally suppose u≥0. Since ∑m=1, (Γm)ᵢ=7m_(i+2)+mᵢ−1. A nonzero limiting state cannot use all owners, by summing the active equalities. At the end j of any cyclic run of positive x, the successor is absent, so u_j=−x_(j+2) and therefore both u_j and x_(j+2) are zero. Such a state uses a single owner or an adjacent pair (with at least two quiet slots after every run). A positive-payoff active owner must be the first of that pair, followed by a zero-payoff owner. If all u_i are positive, this leaves no allowable activity including at X=0. With a unique zero at 0, we have m_1=m_2=0; row 0 forces m_0=1 and row 1 forces u_1=−1. With adjacent zeros 0 and 1 and other payoffs positive, m_2=0, row 0 similarly forces m_0=1 and row 1 fails. These statements allow arbitrary added activity at zero-payoff owners. For opposite zeros 0 and 2, the positive owners 1 and 3 satisfy u_1+u_3=4. On a pair with positive owner i and its zero successor, the quiet predecessor has zero payoff and imposes x_i≤x_(i+1). Thus s=m_1+m_3≤1/2, still allowing arbitrary tiny-amplitude activity at zero owners. But adding mean rows 1,3 gives 8s=6−m_1u_1−m_3u_3; since both payoffs are strictly below 4, this implies s>1/2.

For three zeros rotate to u=(0,0,0,4). The mean equations uniquely give m=(5/33,15/22,4/33,1/22). At every prelimit date where x_3>0, active indifference and uniform convergence of phase values imply x_0≥3 eventually. Since m_3/m_0>0, there is therefore a selected date with x_3 bounded below by a positive constant, and x_0>0. (Otherwise Ex_3/Ex_0 tends to zero.) Each exact period on this family has at least one quiet owner at each date. If x_1>0 at this selected date then x_2=0 and the active 1 has U_1=−x_3, contradicting uniform convergence to u_1=0. Thus x_1=0 and U_0=−x_2≤0 at that date. The per-period variation bound is o(EX), so at all dates x_1−x_2≤Q_0≤U_0≤o(EX). Averaging contradicts m_1>m_2.

All possible signs have now been excluded, proving the period bound by contradiction. The constants are existential. An explicit minimum period at L=10¹⁴ remains undetermined.

At each fixed L≥L₀ the total regret also has a positive infimum over deterministic finite-state rules with at most cL states that advance after every unanimous Continue. Each state specifies a product hazard row and a single state to visit next after unanimous Continue. The initial state and rule may vary with accuracy. On its single live path the rule reaches a cycle within the number of states, possibly after a transient prefix. In a purported accurate sequence at fixed L, pass to a subsequence with constant prefix and cycle lengths, both at most ⌊cL⌋, and with all the finitely many hazard vectors converging. Every fixed prefix date has positive limiting reach by induction from the sure-opening exclusion. Thus the entrance to the cycle has positive limiting reach and conditional original total regret tending to zero by the restart bound. The suffix would be an accurate sequence of periods ≤cL, already excluded. This extension uses only the stated deterministic update and state-dependent product rows.
