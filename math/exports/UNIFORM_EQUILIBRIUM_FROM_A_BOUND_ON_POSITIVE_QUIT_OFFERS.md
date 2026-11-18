# A welfare bound gives uniform equilibrium on a nonlinear cyclic family

Consider four independent stopping laws on the natural dates and Never. At the first nonempty stopping coalition T, recipient i receives r_i(T); perpetual continuation pays zero. A unilateral deviation may replace its entire stopping law. Write Z_i(T)=r_i(T)−r_i({i}) for the centered rewards, Γ_ij=Z_i({j}), J_ij=Z_i({i,j}) for i≠j, with Γ_ii=J_ii=0. For a product vector q of four quit probabilities, Q_i(q) is the expected reward Z_i(R∪{i}) as the rivals' random quit set R is drawn at that date. It is independent of q_i.

## Raw criterion

Suppose some h>0 satisfies the following three finite tests.

1. Every nonempty native absorbing column satisfies ∑_i Z_i(T)≥h.
2. Whenever q≠0 and Q_i(q)>0 for every i with q_i>0, all four owners are active and ∑_i Q_i(q)≤h.
3. In each triple T there is an i∈T with J_ij−Γ_ij>0 for both j∈T other than i.

Then there is a uniform-equilibrium payoff for the original game at arbitrary signed own singleton levels. The levels of rewards paid after absorption and the payoff at perpetual continuation are distinguished throughout. The criterion uses neither a supplied strategy nor a stationary-root index.

Suppose otherwise. The checked same-table single-pivot normalization has centered rewards Z divided by a positive scalar, one positive own singleton and all others zero. Its terminal regret sum is bounded below over actual profiles. On absorbing prescribed profiles the own-singleton shifts do not change regrets, since finite deadlines already dominate literal Never at nonnegative own singletons. Thus the native infimum A of total terminal regret over absorbing profiles is positive (scale back by the positive scalar). The checked normalization applies to the literal original table and its selected positive singleton. [Single-pivot normalization, `nonempty_finFourSinglePivotNormalization_of_no_uniformPayoff`](../../UniformEquilibrium/Diagnostics/Quitting/FinFourSinglePivotNormalization.lean) · [Positive total-debt equivalence, `quittingTerminalDebtSumInf_pos_iff_not_exists_uniformEquilibriumPayoff`](../../UniformEquilibrium/Quitting/Terminal/TerminalDebtSumInf.lean)

Write C for the compact Euclidean closure of (U,B,e,N) over independent actual clocks in the native game: U is prescribed payoff, B is the cap over all finite deadlines and literal Never, e is the payoff of literal Never, and N_i is the original marginal Never mass. On C let d_i=B_i−U_i, Δ_i=B_i−e_i. At any point with ∏N_i=0, ∑d_i≥A: move the smallest Never mass of approximating profiles to any finite date, changing payoffs and rival caps by at most twice the reward bound times this mass. Fix one designated owner p. Minimize ρ≥0 over X∈C subject to

    N_p=0, d_p=0,
    N_j>0, d_j=N_jΔ_j≤ρ, (1−N_j)(ρ−d_j)=0  (j≠p).

A seed is p alone stopping surely, every rival staying at Never, and ρ twice an absolute reward bound M≥1. Feasible ρ≥A/3. Every nonsure-Never rival has N_j≥ρ/(2M) from d_j=N_jΔ_j=ρ; the others have N_j=1. Compactness gives a minimum ρ>0. At such X give the whole action Never a private bonus λ_p=0 and λ_j=ρ/N_j for j≠p, regardless of what rivals do. The bonus is only for a comparison of clocks. Its cap and prescribed payoff agree:

    b_i=max(B_i,e_i+λ_i)=U_i+N_iλ_i.

Indeed when N_j<1, λ_j=Δ_j, and for N_j=1, U_j=e_j by coupling; the other equalities follow from feasibility.

In the one-date stage game with child b every equilibrium has blank hazards. For a proposed equilibrium q write t_i=1−q_i, C₀=∏t_i, H_i=∏_{j≠i}t_j. Prefix X by this actual row and replace the Never bonuses by λ'_i=H_iλ_i. Physical finite replies inside and beyond the prefix together with the new Never offer give exactly the stage comparison of Quit to Wait with continuation b: waiting and continuing optimally yields the passive head payoff plus H_i b_i. The prescribed augmented payoff likewise equals the stage payoff, since the child prescribed bonus-adjusted value equals its cap. Therefore all prefixed augmented regrets vanish. This identity passes from approximants to the carrier; a native point with bonus λ has augmented regret equal to

    d−NΔ+(1−N)(λ−Δ)_++N(Δ−λ)_+,

a sum of nonnegative terms by averaging finite replies. If C₀=0, every newly realized bonus λ'_i N'_i is zero, so the prefixed point is absorbing with zero native regret, contradicting A>0. If 0<C₀<1, every losing marginal N'_j=t_jN_j is positive and λ'_j=C₀ρ/N'_j. Vanishing of the three terms gives feasibility at strictly smaller C₀ρ. Finite-game Nash existence now implies blank is the unique root and b≥0.

Either b=0 or b≫0. A single zero admits a small solo hazard by that owner. For two zeros i,j, a small solo hazard is feasible if either directed joining increment between them is nonpositive. Otherwise perturb both zero continuations to −ε and take equilibria. A sequence converging to blank would have all positive-continuation owners quiet, and the quit gain of i equals ε(1−q_j)+(J_ij−Γ_ij)q_j>0, contradicting convergence to blank. Any other limiting root contradicts uniqueness. For three zeros, perturb all of them in the same way. Near blank the fourth owner waits strictly. The owner i furnished by test 3 has quit gain εH_i+∑_{j∈T−i}(J_ij−Γ_ij)q_j+O((∑_{j∈T−i}q_j)^2)>0 throughout a fixed neighborhood of blank for ε>0 small. This gives the same contradiction.

Since N_p=0, product exit has probability one in the limiting original law. Thus ∑b=∑U+3ρ≥h+3ρ>h, ruling out b=0. All four cap values are strictly positive. On carrier approximants each finite assigned deadline is paid its native offer, and their total shortfall from the augmented cap tends to zero; the fourth term, literal Never, also has nonnegative shortfall. Choose a fixed η>0 so that 2Mη<min b_i. Let n be the first physical date whose cumulative total marginal finite mass reaches η. Such a date exists because p becomes surely finite. At every preceding date every finite offer has absolute value at most Mη: without some rival draw by that date quitting pays zero. Vanishing augmented regret forces the aggregate assigned mass there to tend to zero. Pass to a joint subsequence of the four atoms at date n with limit q. Their sum is at least η. Earlier rival exits have probability tending to zero, so each finite offer at n converges to Q_i(q). Any i with q_i>0 has b_i=Q_i(q). Test 2 implies full support and then ∑b≤h, the required contradiction.

More generally the same first-date argument gives a finite necessary test even without tests 1 and 2, when test 3 holds. Put c_i=1 for losers and c_p=0. With b=0, the native exit-reward hull must contain −ρc. With b≫0 there must exist a nonzero q, a single v in the convex hull of the fifteen nonempty reward columns, and ρ>0 such that, writing S=∏(1−q_i) and R(q)=∑_{T≠∅}Pr_q(T)Z(T),

    b=R(q)+S v+ρc,      b_i≥Q_i(q),      q_i(b_i−Q_i(q))=0,
    q_j<1 for every j≠p.

Indeed all deadlines are included in the augmented cap; every loser has a positive original Never marginal, hence its opening atom is below one. After the first physical row the residual exit law has total mass tending to S since a winner absorbs. For S>0 divide it by its mass and extract a common continuation payoff v; for S=0 any hull point suffices. This necessary test retains the likelihood of each head coalition and can use positive prices c_j in place of one by making the same replacement in the minimization. It supplies only a one-way exclusion on failure of both alternatives.

## A rational table and its open neighborhood

All indices are modulo four. Put L=10^14. For owner i denote the rival hazards q_(i+1), q_(i+2), q_(i−1) by a,b,c. Give its participant rewards by the multilinear polynomial

    Q_i=L(a−b)+a[5(1−b)(1−c)+bc].

That is, evaluate at the binary rival mask for every coalition containing i. Give its passive rewards for the seven masks a,b,c,ab,ac,bc,abc respectively by

    −1, 6, −1, −L−1, L+2, 0, 13.

Singletons, pairs and the grand coalition have welfare four; triples have welfare thirteen. In each triple the owner whose opposite is absent has positive joining increments L+6,1 towards the other two. At equal hazards t=1/5 all four forced-Quit offers are 81/125>0.

Here is a uniform check of the second test with h=4. A positive active owner must have its successor active. Thus the support is full and every Q_i>0. The inequalities imply q_(i+2)≤q_(i+1)+5/L all around the circle. Hence every coordinate lies within 15/L of their maximum r. The sum of the linear terms cancels; denote the sum of the four remaining terms by R(q). It is Lipschitz with constant at most 100 in max norm: each of three partial derivatives of every summand is bounded in magnitude by 6. On the diagonal

    4−R(r,r,r,r)=4(1−r)(6r²−4r+1)≥4(1−r)/3.

If r≤1−10^−4 this deficit dominates 1500/L. Otherwise all coordinates are near one. Writing d=∑(1−q_i), we have R≤∑q_i+5d²/2=4−d+5d²/2. Indeed the four distinct quadratic missing-coordinate products in the four summands are bounded in sum by d²/2. This is <4 at 0<d<2/5 and equals 4 at the grand corner.

There is an open set of independent perturbations in all 56 native rewards. For all small δ>0 first subtract δ from every participant reward with at least one rival present, preserving its own singleton zero and all passive entries. Around such a table allow independent perturbations of every native reward of size ξ<δ/20. Grand welfare h becomes 4−4δ+O(4ξ), strictly below all proper welfare, which is at least 4−2δ−4ξ. If the successor is absent, every participant payoff against at least one rival is now strictly negative (all were ≤0); singleton offers are zero. Thus positive active support is still full. An admissible full row obeys q_(i+2)≤q_(i+1)+(5+δ+ξ)/L. On compact regions away from grand the same diagonal comparison gives a fixed strict margin (take δ small). Near grand the deficit relative to the perturbed grand welfare is stable: at the center it is at least d−5d²/2, while changing the payoff entries by δ+ξ changes the difference between the grand total offer and the current total offer by at most 8(δ+ξ)d. This follows by coupling the three rival coins in each offer to sure quits. The positive triple increments stay strict, and the common positive product persists. These raw intervals allow arbitrary signed own level shifts in addition.

## Previous existence tests at this table

The singleton matrix Γ has first cyclic row (0,−1,6,−1). Every column contains a negative entry, all two- and three-owner principal determinants are nonzero and the full determinant is positive. Its complementary degree is one: at offset minus the ones vector each recipient needs its sole positive mate, forcing the unique strictly positive solution and positive local determinant. The homogeneous R₀ property follows from the same support determinants and the negative member of each column.

The raw orientation test on either the reward hull or the first-action neighborhood fails. At full equal hazard 1/5 both Quit and the passive Wait payoff P at child zero equal 81/125. The first circulant row of D_q(Q−P), omitting its zero diagonal, is

    L+4, −4L/5−26/5, −L/5−1/5.

Its row sum is −7/5; the real alternating eigenvalue 2(−4L/5−26/5)+7/5 is also negative. The conjugate pair has nonzero imaginary part, hence the determinant is positive. Passing to positive odds and dividing by H_i=∏_{j≠i}(1−q_j) preserves this sign, since Q−P=0 here. The full indifference continuation Φ therefore covers a neighborhood of zero with positive determinant and strictly positive active Quit offers. Arbitrarily small positive multiples of any singleton column lie in the reward hull and have a negative coordinate. Zero also belongs to the raw first-action set by the blank row, so all its open enlargements contain such vectors. Both versions of the weak orientation condition fail. The calculation is stable by the inverse function theorem. The four-singleton system of weighted upper joining inequalities is infeasible: sum the four inequalities for any proposed nonzero nonnegative owner weights; each row contributes (L+5−L+0)−4=1, giving a strictly positive weighted sum. This excludes every support-filtered upper ledger requiring these inequalities. The cyclic favorite-pair class has two mutually positive favorite pairs; here no pair has two strictly positive joining payoffs. A small strictly positive uniform row rules out the local product-low test. These comparisons concern the named predicates.

## Absence of stationary equilibria and sure openings

A sure opening cannot be Nash even with arbitrary continuation values in [−L−6,L+6]. If owner 0 is sure write y=q_1,z=q_2,w=q_3. For owners 1,2,3 the respective Quit-minus-Wait differences, independent of continuation since 0 is sure, are

    Lw(z−1)−9wz−w−3z+1,
    L(2w−1−wy)−19wy+7w+6y−6,
    L(1−z)−5yz−5y−8z+6.

If w=1 the first difference is negative, so y=0; the second is then positive, giving z=1, and then the third is negative. Hence w<1, and its Wait inequality forces z≥1−12/L. Now the first difference is negative again, giving y=0. Owner 0 has Q_0=−Lz while its passive head payoff is 6z(1−w)−w(1−z) and its rival survival is (1−z)(1−w). Even the lowest proposed continuation gives Wait greater than −15, contradicting sure Quit. Rotation exhausts all sure owners. In particular this includes the refusal punishments after a sure opening on the native table and its unit row raise.

A proper nonblank stationary equilibrium must give a mixer i satisfying Q_i D_i=P_i, where D_i=1−∏_{j≠i}(1−q_j), provided some rival is active. This is its indifference against literal Never and immediate Quit. A sole stationary actor with hazard s>0 gives its predecessor −1, whereas the predecessor's immediate Quit gets s(L+5)>0. An adjacent pair cannot satisfy the two mixing equations since one directional J is zero while the associated Γ is −1. On an opposite pair J=−L and Γ=6. For a triple rotate to actors 0,1,2, with hazards x,y,z and player 3 quiet. Player 2 has Q_2=−Lx and conditional passive payoff at least −1, hence x≤1/L. Player 1 has

    Q_1 D_1−P_1=L z²(1−x)+5z(1−x)(x+z−xz)+x+z−4xz>0,

contradicting its mixing.

There is no fully mixed stationary equilibrium even if its four proposed native payoffs have mixed signs. Write again a,b,c for the three rivals of i, now D=1−(1−a)(1−b)(1−c). The coefficient of L in P_i is a(c−b); its remaining part is bounded by 13D. Each mixing equation implies, with e=18/L,

    |a−[(1−a/D)b+(a/D)c]|≤e.

At a full stationary equilibrium every native payoff equals Q_i and absorption is sure, so R(q)=∑Q_i≥4. We prove the opposite. Put r=max q_i and η=10^−4. If r<1/10 then R≤20r+4r³<4. Otherwise choose a=r; its opposite c satisfies c≥r−3e because a/D≥1/3. When r≤1−η, at this row the coefficient 1−a/D is ≥(1−a)c/D≥η/6, so b≥r−6e/η. At the row with a'=c the opposite is r, and 1−a'/D'≥η/3. Its successor is the fourth coordinate and lies ≥r−12e/η, by the same equation and r−c≤3e. Thus R differs from the diagonal value by at most 1200e/η<4η/3, excluding R≥4. If r>1−η, its opposite is >1−2η. For the two remaining coordinates b,d the equations give |2b−bd−1|,|2d−bd−1|≤e+4η: their relevant D lie above 1−2η, their coefficient a/D differs from a by at most 2η, and the next high coordinate differs from one by at most 2η. Hence |b−d|≤e+4η and (1−b)²,(1−d)²≤2e+8η. The total missing mass is below 1/10 and is positive, where R≤4−d₀+5d₀²/2<4 with d₀=∑(1−q_i). This proves the stationary exclusion.

For the original unit raise r_i(T)=1+Z_i(T), no sequence of stationary profiles has vanishing complete regret. At any nonzero nonsure limiting stationary vector with a rival for each owner, absorption against all unilateral replacements by continuing is geometric; prescribed payoffs and finite deadline and Never offers pass to the limit. A nonzero limit with only one actor is ruled out by its predecessor's strict gain, as above. A sure limiting actor likewise gives the excluded one-stage best-reply inequalities at a bounded subsequential continuation (including its payoff after refusal). A sequence converging to blank must have nonzero total hazard eventually since the unit-raised blank profile has regret one per owner. Normalizing the total hazards to a simplex vector z, simultaneous exits contribute o(1) of the first-exit law. Native prescribed payoffs tend to Γz, and immediate Quit gives Γz≥0. For z_i<1 any positive z_i would give native Never value (Γz)_i/(1−z_i), so zero regret forces z_i(Γz)_i=0; at z_i=1 the zero diagonal suffices. If a rival survival is identically one along a subsequence for one owner, there is only one actor and its predecessor gains. This contradicts R₀. Compactness therefore gives a strictly positive stationary regret floor. The floor, the strict sure-opening exclusion with bounded continuations, and the regular positive orientation witness persist near the rational table, hence also in a smaller open family above.

At the cyclic center any uniform equilibrium on the original unit raise must also break symmetry of the four clocks. In fact the total regret of profiles that give every player the same law on dates and Never has positive infimum, even with unrestricted time dependence. Otherwise the joint Never probabilities tend to zero and the native debts vanish, by the positive-row shift formula. Rotation makes all four prescribed native payoffs equal, and absorption welfare makes each at least the exit probability. The first significant date argument now gives equal limiting hazards t>0, with each finite Quit offer at least one. The diagonal bound forces t=1. A deadline strictly later than the significant date then yields the passive triple reward tending to thirteen, while almost surely quitting there yields the grand reward tending to one. This contradicts vanishing debt. Since the original rewards are bounded, taking profiles within vanishing marginal total-variation distance of a common clock also cannot yield vanishing regret.
