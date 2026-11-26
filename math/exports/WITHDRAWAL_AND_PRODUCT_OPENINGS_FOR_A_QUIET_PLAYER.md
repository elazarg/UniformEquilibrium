# Withdrawal and product openings for a quiet player

Fix a four-player native quitting table Z, with each own-singleton payoff and every perpetual payoff equal to zero. At a nonempty quitter set R the game stops with payoff Z(R). A signed row translation adds the same constant to all of one player's nonempty-exit rewards, keeping the perpetual payoff zero. Write G_ij=Z_i({j}). Players use independent private stopping clocks on the positive integers and Never. A terminal regret is the supremum of the gain from replacing one's entire clock. A clock is individually finite if it stops at a finite time almost surely.

Choose a three-player child T and prescribe Never to the omitted player o. We give a sufficient product test on the raw rewards, a strict separation from the fixed withdrawal inequalities on all fourteen proper children, and the exact largest limiting outsider regret over individually finite approximate equilibria of T. The results below are ordinary mathematics.

## The continuation value after withdrawing

For each player i in T and rival hazard vector h∈[0,1]^(T−i), write H(h) for the probability that no rival quits, Q_i(h) for i's payoff from quitting against this product row, and P_i(h) for the unconditional passive contribution on nonempty rival exits. Then
```
χ_i = inf_{h : H(h)<1} max(Q_i(h), P_i(h)/(1−H(h))).
```
This is the infimum over individually finite independent rival clocks of i's full best-response payoff. In fact it suffices that joint rival survival tends to zero for the lower bound. For every date reached by all rivals, their conditional actions again have a product row. If Q_i≥χ_i, quit on the first such date. At every earlier date P_i+Hχ_i≥χ_i, also on a blank row where H=1. Iterating to the designated date gives the lower bound, including when there is no such date, since residual joint survival vanishes. Conversely approximate each h with H(h)<1 by vectors strictly between zero and one. Against the corresponding stationary independent geometric clocks the optimal cap is exactly max(Q_i,P_i/(1−H)). This follows by evaluating an arbitrary pure deadline as a convex combination of the two displayed offers and taking the supremum. Taking limits gives equality. With unrestricted rival clocks the exact value is min(0,χ_i), by the same argument and by testing all rivals at Never. In particular, assigning passive payoff one to every nonempty rival exit gives a finite-rival guarantee of at least one, even though the unrestricted guarantee is zero.

The responder knows the rival laws. Its choice after a sole withdrawal uses no realization of a rival clock. The established independent punishment theorem and the earlier precommitted security transfer concern related values. [Punishment values](../../UniformEquilibrium/Quitting/Punishment/InstantPunishment.lean) · [security transfer](../../UniformEquilibrium/Quitting/Classification/QuietExtension/DeadlineWithdrawalSecurityTerminalDebt.lean) · [earlier withdrawal tests](../formalized/WITHDRAWAL_AND_DEADLINE_QUIET_EXTENSIONS.md)

## A product test on one date

Choose any g_i≤χ_i. Take q in the child hazard cube. Let m_R be the product probability of exactly R quitting at the current date, and m0 the probability of a blank date. Independently introduce z in the simplex on the seven nonempty child coalitions. The full simplex contains every first-exit law of the child continuation after this date. For nonempty R, define J_i(R)=Z_i(R+i)-Z_i(R), and W_i(R)=0 if i is absent, Z_i(R-i)-Z_i(R) if R has at least two members including i, and g_i if R={i}. Define
```
Y = Σ m_R [Z_o(R+o)-Z_o(R)] - m0 Σ_C z_C Z_o(C)
A_i = Σ m_R J_i(R) - m0 Σ_C z_C Z_i(C)
B_i = Σ m_R W_i(R)
C_i = m0 Σ_C z_C W_i(C)
D_i = m0 [g_i - Σ_C z_C Z_i(C)]
Φ = Σ_i (max(0,B_i) + max(0,A_i,C_i,D_i)).
```
Every unqualified R sum omits the empty set. If every q,z with Φ=0 satisfies Y≤0, all signed row translations of the table have a uniform-equilibrium payoff. This is a raw finite-dimensional semialgebraic test if the floors are specified by raw inequalities. It needs neither a uniformly bounded set of weights nor linear comparison of the two excesses.

Indeed for any individually finite child profile and outsider deadline u, times before u cancel. Conditional on joint survival to u (probability S), let q be the actual hazard row and z the true conditional future first-exit law if m0>0. If m0=0 any z gives the same expressions. If S=0 the outside gain vanishes. The gain of the outside deadline over the prescribed Never is S Y. A child i can privately sample its own clock. On its atom at u, quit as prescribed or skip the atom and from u+1 choose a reply achieving at least g_i−η against the independent rival clocks conditioned beyond u. The latter gives expected gain at least S(B_i−η) because only survival of all rivals needs the conditional bound. On its clock being strictly after u, choose between (i) leaving the draw alone, (ii) advancing to u, (iii) waiting until its originally sampled finite date and withdrawing there, then taking a near-best reply against the surviving rivals, or (iv) passing through u and selecting such a reply from u+1. These operations give zero, S A_i, at least S(C_i−η), and at least S(D_i−η), respectively. In (iii) condition separately on the countably many possible old dates; withdrawal has no effect if an earlier rival quit. On its old singleton first exit, the event specifies only that rivals survived through its privately sampled date, preserving their conditional independence. In (iv), a rival exit at u gives the same passive reward as prescribed. The two choices on the atom and on later draws are disjoint conditions of one's own clock. Choose the better option on each branch (the maximizing labels use the known laws, never the rivals' realized clocks). Hence the sum of child debts bounds SΦ after η tends to zero. These replacements are independent of rivals, and amount to new stopping laws before any absorption.

Along all-individually-finite child profiles of vanishing debt the outsider gains tend to zero uniformly over deadlines. Otherwise some S Y≥δ>0; bounded Y keeps S bounded below and consequently Φ→0. Extract a convergent subsequence of q,z in a compact set; the limit contradicts the implication. Late and literal Never give a passive payoff since the rivals are finite. With all three child clocks individually finite, at least one rival forces absorption after every one-player replacement in the full game. Signed translations then preserve all debts and translate the equilibrium payoff. If G_pi≤0 for distinct child players p,i, apply cardinality-three signed existence to the child table translated by −G_{·p}. The zero-column clock-completion proof first appends the prescribed owner p's Never mass as a diffuse late block, then completes the blocker i and finally the remaining owner. The proof uses the same rival-deletion condition for three as for four clocks and yields arbitrarily accurate individually finite native child profiles. When all six are positive, a full counterexample would require the outsider's row to be negative at all three child columns and also to have a positive entry, an impossibility. Compact terminal payoff selection gives one uniform-equilibrium payoff at all accuracies. [Three-player existence](../../UniformEquilibrium/Quitting/Classification/SmallPlayerExistence.lean) · [zero-column completion](ZERO_SINGLETON_COLUMN_EQUIVALENCE.md) · [necessary singleton signs](TWENTY_ONE_SINGLETON_SIGN_CLASSES_FOR_FOUR_PLAYER_QUITTING_GAMES.md) · [terminal payoff selection](../../UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean)

Uniformly bounded weights depending on q,z directly suffice: it is enough to ensure Y≤Σ_i [a_iA_i+b_iB_i+c_iC_i+d_iD_i] with nonnegative coefficients allowed to depend on q,z. A fixed collection valid for each F and J row is the special case without dependence, and bounding the coefficients costs at most the largest max(b_i,a_i+c_i+d_i) times Φ. In particular, constant nonnegative weights suffice if for every nonempty C,R⊆T they obey
```
Z_o(C) ≥ Σ_i [(a_i+d_i)Z_i(C) − c_i W_i(C) − d_i g_i],
J_o(R) ≤ Σ_i [a_i J_i(R) + b_i W_i(R)].
```
In that case the outsider debt is at most Σ_i max(b_i,a_i+c_i+d_i) e_i, where e_i is the child regret of player i. With every d_i=0, these two rows are also necessary for universal expected comparison by these fixed aligned response gains at maximal floors g_i=χ_i. To test a nonsingleton R or C, put precisely those owners at u or u+1 respectively, with the others later. For a singleton, place its owner i at the chosen date and put all its rivals strictly later, with their independent finite post-date clocks making its complete cap at most χ_i+η. This realizes the maximal withdrawal gain to within η. Let η decrease to zero. Necessity here is for this prescribed comparison of responses. The tests with variable coefficients and the characterization below allow others.


## Exact separation

Take T=012 and o=3. The native singleton matrix in player order is
```
( 0,-1,-1, 2)
( 2, 0,-1,-1)
(-1, 1, 0, 1)
(-1, 2,-1, 0).
```
It is a relabeling of integer witness 15 in the 21-class census, with row mask (2,4,1,3) and determinant 7. At 01,02,12,012 the four respective rows are (−2,1,1/4,1/2), (3,−2,20,−19/10), (0,1,2,−1), (10,10,10,10). Rows 0,1,2 get zero on pairs with 3, two on triples with 3 and three on the grand coalition. Row 3's joining gain Z_3(R+3)-Z_3(R) is 1 at 01, −1 at 02, and −100 at every other nonempty R in T. Use g_0=−2 (Never against two finite rivals pays at least −1), a=(3/2,0,3/2), c=d=0, and select b=(0,0,0) or (3,0,0).

The future margins Z_3(C)-a·Z_T(C), in order 0,1,2,01,02,12,012, are 1/2, 2, 1/2, 13, 7, 53/8, 43/4. Subtract from the outsider's join gain the paid advances and withdrawals. In the same order the residuals for b_0=0 and 3 are respectively
```
−103, −100, −103,  5/2, −1, −803/8, −100
 −97, −100, −103, −1/2,  5, −803/8, −397/4.
```
Put X=m_{01}, Y'=m_{02}, U=m_{0}, V=m_{012}, with U denoting the singleton of player 0. Independence gives XY'=UV (including boundary hazards). Hence min(X,Y')≤(U+V)/2. The smaller of the two weighted residuals at q,z is at most 5 min(X,Y')−90(U+V)≤0. This proves the test for every higher-reward completion obeying these strict inequalities in a neighborhood of the table; for example retain upper bounds 3 and 6 for the unfavorable residuals, strict negativity for the favorable ones, and margins exceeding 80 at U,V. The two choices of weights may be selected from the actual q alone.

For fixed nonnegative weights on T, at R=01 only b_0 W_0(01)=b_0 can contribute positively: W_1(01)=−1 and the advance of 2 gives −1. This requires b_0≥1. At C=12 the future inequality gives 20a_1≤10. Indeed every child has a negative internal singleton, so χ_i≤0 by concentrating diffuse rival hazard on a negative singleton. All three payoffs at 12 are strictly positive and each member's withdrawal there is strictly unfavorable. At R=02 the two member withdrawals give −2 each, and the advance of 1 gives 1/10. Thus −1≤a_1/10−2b_0 gives b_0≤21/40, a contradiction. The two bounds on b_0 stay strictly apart in an open neighborhood in the full native reward space because the unused join coefficients and the active withdrawal coefficients in the future test have a strictly unfavorable sign.

For each of eleven other proper children there is a singleton j with negative G_hj for some outsider h, positive G_ij for every other member i, and, for any child of size greater than one, some internal G_jl<0. The witnesses (child:j,h) are (0:0,2),(1:1,0),(2:2,0),(3:3,1),(01:0,2),(03:3,1),(12:1,0),(13:1,0),(23:3,1),(023:3,1),(123:1,0). At C={j} the fixed future row fails even with the four weights a,b,c,d and the maximal finite-opponent floors, using zero for a one-player child. Indeed g_i≤G_ij for every other child i by putting an arbitrarily small stationary hazard on j and still smaller positive hazards on the other rivals, while g_j≤0 from the internal negative entry by the same diffuse test (zero for a singleton child). Thus Z_i(j)≥0, Z_i(j)−g_i≥0 for each i, and W_i(j)≤0. The right side of the fixed future requirement Z_h(C)≥Σ[(a_i+d_i)Z_i(C)−d_i g_i−c_i W_i(C)] is nonnegative. On child 02 both members quit at date two, obtaining 1 each, strictly better than either preempting for zero or withdrawing against their rival. Outsider 1 gains by preempting to zero in place of −2. On 013 everyone quits at date one, strict versus withdrawal in all three rows. Outsider 2 gains one by joining. These two individually-finite exact child equilibria also exclude any criterion that bounds every lifted outsider debt by the child debts. All comparisons separating other children are open in the raw singleton and higher entries. Every pure stationary profile with a nonempty quitter set admits a strictly profitable first-date flip. In the order 0,1,01,2,02,12,012,3,03,13,013,23,023,123,0123 one flipping player per set is respectively 1,2,0,0,1,0,2,1,0,0,2,0,1,0,3. Adding one to every nonempty reward also excludes the all-Never profile. These strict exclusions persist in the same open set. The numerical center itself has an exact mixed stationary equilibrium (1/2,1,4/5,0). Players 0 and 2 are indifferent, player 1 favors quitting, and player 3 favors waiting. For example, the four values (1−H)Q−P are respectively 0,3893/500,0,−899/10. Thus the example separates the stated quiet-lift criteria and pure stationary profiles within a game also covered by mixed stationarity.


## Conditional and precommitted withdrawal can differ

The two sources of improvement can already be distinguished with fixed weights. For T=012 the following are the native rows at columns 0,1,2,01,02,12,012.
```
 0   −2     1       1       −2       16  17
−1    0   −1/2   −99/100    1/20      1   0
−1   −2     0       0      −99/100    1   3
 2   −2   −1/2      5       −5        5  10
```
Column 3 is (−1,3,2,0). In rows 0,1,2 set pairs with 3 to zero, triples with 3 to one and the grand coalition to two. Row 3's joining gain is −3/8 at 0, one at 01, 11/4 at 02 and −50 elsewhere. The fixed rows above hold strictly with a=(0,2,2), b=(1,0,0), c=(2,0,0), d=0 and g_0=−1/4. For rival hazards u,v we have Q=u−2v+18uv and P=−2u+v+17uv. If Q<−1/4, then v>1/8 and P=v+(17v−2)u>0, which proves the floor. A replacement precommitted against every deterministic rival tuple can guarantee at most −1/2. Indeed immediate rival 1 gives the passive and quit payoffs −2,1, while immediate rival 2 gives 1,−2. Their equal mixture yields −1/2 for every own strategy.

Two concrete failures distinguish the fixed tests on this child. With c=d=0, the future test at 12 gives 16a_0+a_1+a_2≤5, whereas the right side required at 02 is at least −99/20, strictly greater than −5. This excludes removal of future withdrawals in the three-weight version even with independent floors. With d=0 and precommitted floors, the same future test at 12 gives a_1+a_2≤5 because every W_i(12)≤0. Its join test at 0 forces b_0≤17/20, whereas at 02 it requires 3b_0≥11/4. This game also has the stationary profile (30/31,3/4,1,0), so the example distinguishes two response comparisons within a game also covered by stationarity.

## Exact largest regret from a specified child

Let E_T consist of the limits of first-quitter distributions along individually finite native child profiles with maximum terminal regret tending to zero. Assume this set is nonempty, as holds on the weak-blocker branch above. It is compact by diagonal selection. Let L_T be the limit, as ε decreases to zero, of the supremum of the outsider's terminal regret over all individually finite profiles of T with maximum child regret at most ε.

Consider the following two kinds of opening.

1. A product row q with blank probability m0>0, together with z∈E_T. Require q to be a Nash equilibrium on the single date for the child, with payoff v_i=Σ_C z_C Z_i(C) after a blank. Its outside gain is Y(q,z).
2. A product row q with at least one sure player. Each child player facing a sure rival must assign mass only to actions maximizing its immediate payoff. If exactly one child player k is sure, require Q_k(q_{−k})≥P_k(q_{−k})+H(q_{−k})χ_k. The outside gain is Σ_R m_R J_o(R).

Then L_T is the supremum of zero and all these outside gains. In particular safety for *every* such approximate-equilibrium sequence holds exactly when both kinds of opening have nonpositive gain.

For the upper bound, if L_T>0, choose profiles and pure outsider deadlines whose gains tend to L_T. Their prior survival probabilities S are bounded below, since rewards are bounded. At a surviving restart child regret e_i bounds S times the restart regret, by copying play before that date and replacing the rest. Conditional child clocks are still individually finite and independent. Extract a limit of S, the opening q and the post-blank exit laws z, using any z when the blank has probability zero. If the limiting m0>0, the same pasting at the following date gives tail regret at most e_i/(S m0) with the actual, pre-limit probabilities. Hence the limiting z lies in E_T. A forced head action followed by the prescribed tail yields the usual stage Nash inequalities at the limit. If m0 tends to zero, a player facing a limiting sure rival compares its two head offers up to errors vanishing with rival survival. A unique sure player k can refuse and then secure χ_k whenever the rivals survive the root. Its honest payoff tends to Q_k, giving the inequality in case 2. In either case the observed gain tends to S times its opening gain, bounded above by the latter because the former is positive.

For the reverse bound, prepend a row of type 1 to individually finite child approximants witnessing z. Each complete child replacement on the first date either quits or continues. After a blank, even an optimal further replacement improves on the approximant's prescribed continuation by at most its vanishing regret. The two head offers satisfy the limiting Nash inequalities, so full child regret vanishes. For type 2 with a unique sure owner k, attach individually finite independent rival clocks whose complete k cap is at most χ_k+η. The other owners face a sure rival at the first date. Owner k's best refusal earns at most P_k+H(χ_k+η). Any finite tail assignment suffices with two or more sure owners. In both cases prescribing the finite root and these tails yields individually finite child approximants, with date-one outside gain tending to the stated value. This proves the equality.

One can also test a specified target z*∈E_T. Along any witnessing child sequence, a positive outsider gain would produce one of the above openings with positive survival S. Its post-cut distribution π_C=m_C+m0 z_C satisfies Sπ_C≤z*_C for each nonempty C, since the contribution from exits before the cutoff is nonnegative. Thus excluding positive openings with supp(π)⊆supp(z*) suffices for a safe lift from this target, even when another target is unsafe. Outer approximations to E_T are available from each finite interlaced-order test using the seven first-exit indicator functions as additional target coordinates, imposed conditional on every positive training observation as in that test. The intersection over all ranks yields E_T by private quantile reconstruction. The unrestricted four-player conjecture still permits equilibria with every player active. [Interlaced order tests](../notes/CODEX_ROOT__INTERLACED_ORDER_TESTS_FOR_ARBITRARY_FOUR_PLAYER_GAMES.md)

## Sharp powers for full outsider regret

The zero-set test can apply even when no bounded, profile-dependent linear comparison of debts is possible. Here are two calibrations. In each let (x,y,s) be the three child hazards and e the sum of their complete terminal regrets. Signed row translations preserve the debt comparisons on these individually finite profiles.

**A square-root loss on a surviving singleton matrix.** Use the four singleton rows
```
( 0, 1,−1, 1)
(−1, 0, 2,−1)
(−1,−1, 0, 2)
(−2, 1, 1, 0).
```
This is a relabeling of integer witness 17 of the twenty-one-class census, with canonical mask (2,4,3,5) and determinant 5. At 01,02,12,012 respectively put the four rows (0,0,0,0), (−1,0,2,0), (0,0,−2,0), (0,0,0,0). For each nonempty child set R define
```
J_3(R) = 3 J_2(R) + 1_{0∈R, 2∉R} − 1_{2∈R}.
```
Other entries are arbitrary. Use g_0=0 because an immediate quit always pays zero in child row 0. The other floors may be any valid lower bounds. We have B_0=x(y−s) and Σ_R m_R J_2(R)=(1−s)(x−y). At every child coalition C both 3Z_2(C) and 4Z_2(C) are at most Z_3(C). Consequently
```
Y ≤ 3 A_2+(1−s)x−s,       Y ≤ 4 A_2+(1−s)y−s.
```
The smaller excess above 4 max(0,A_2) is bounded by min(x,y−s), hence by √max(0,B_0). This gives Y≤4Φ+√Φ. At any outside deadline with survival S the total child regret bounds SΦ, so the full outsider regret is at most 4e+√e.

For sharpness, on date one let (x,y,s)=(t,t,0), where 0<t<1. On a blank, players 0 and 2 quit at date two and 1 at date three. Against its rivals, player 0 can receive t by waiting to date two, collecting the positive singleton of 1 if it occurs first and zero otherwise. A later choice loses one on the branch where 2 quits alone. Its prescription gets t(1−t), so its regret is t². Player 1 earns −1 if 0 quits initially, regardless of whether 1 joins it, and can earn only zero on the remaining branch. Player 2 is indifferent between its complete prescription and a first-date quit, since its joining increments on sole 0 and sole 1 are +1 and −1 at equal probabilities and the increment on 01 is zero. On a blank initial date withdrawing at the second date gives the negative singleton of 0. Thus e=t². The outsider's first-date gain is t, its gain at date two is nonpositive, and all later offers equal its prescription. The complete outside regret is exactly t. This table also has the pure equilibrium with 0 and 2 quitting together on the first date.

**A cube-root loss.** For a second native table put
```
Z_0(R)=−1_{R=012},      Z_1(R)=1_{1∈R}(1_{0∈R}−1_{2∈R}),
Z_2(R)=1_{2∈R}(1_{0∈R}−1_{1∈R}).
```
On child exits put Z_3(R)=max(0,Z_1(R),Z_2(R)) and set J_3(R)=1 if R is the singleton 0, zero otherwise. Complete the remaining entries arbitrarily. All child players obtain at least zero by Never and we take these floors. Let v_i=Σ_C z_C Z_i(C). Here B_0=xys, A_1=(1−y)(x−s)−m0 v_1, A_2=(1−s)(x−y)−m0 v_2 and Y=x(1−y)(1−s)−m0 v_3. From v_3≥0,v_1,v_2 it follows that Y≤x, Y≤A_1+s and Y≤A_2+y. Thus Y≤Φ+min(x,y,s)≤Φ+Φ^(1/3). As above the full outside debt is at most e+e^(1/3).

At date one all three independently quit with probability t. On a blank, schedule 1 at date two, 2 at date three, 0 at date four. The suffix gives all three zero. Player 1 cannot gain by withdrawing past its date because 2 precedes 0, player 2 would lose by joining 1, and player 0 cannot receive a positive payoff anywhere. Players 1 and 2 are indifferent between a date-one quit and continuing since the two opposing single-join increments cancel at equal hazards. Past a blank their suffixes are best replies. Player 0 loses precisely the probability t³ of the triple and can always obtain zero by Never. The outsider's first-date gain is t(1−t)², with zero gain at every later date since the blank suffix has only the first coalition {1}. Thus no exponent larger than 1/3 can hold across all tables passing the product test, even with a constant depending on the table.

Some positive exponent does work uniformly over these tables if constants can depend on their rewards and chosen floors. For each parameter list form the graph of ω(d)=max{max(0,Y):Φ≤d} over q,z in the compact product domain, for small positive d where the set is nonempty. If the zero set is empty, Φ already has a positive minimum. Otherwise the product test implies ω(d)→0. A single semialgebraic formula with the rewards and floors as parameters defines all these graphs. Quantifier elimination gives a finite list of bivariate polynomials in d and ω, with a common degree bound D and parameter-dependent coefficients. After specializing a table, discard identically zero polynomials. Any positive branch near zero must lie in the zero set of at least one remaining polynomial, because strict sign cells are open and a graph has empty interior. By the one-variable semialgebraic decomposition choose a single such polynomial on a sufficiently short interval. The first positive exponent of a vanishing algebraic branch is rational with reduced denominator at most D, by the Newton polygon, and hence is at least 1/D. Therefore ω(d)=O(d^(1/D)), or ω vanishes identically there. Survival scaling preserves this positive exponent. The optimal exponent over all tables remains open.
