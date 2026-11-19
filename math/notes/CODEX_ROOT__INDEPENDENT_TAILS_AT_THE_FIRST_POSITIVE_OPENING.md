# The opening and all three Never replies in a four-player quitting game

Consider the four independent private clocks on the positive dates and Never. The first nonempty quitting coalition C pays r(C); live stages and perpetual play pay zero. Write I={0,1,2,3}, Z_i(C)=r_i(C)−r_i({i}), Γ_ia=Z_i({a}). The native game pays Z on absorption, zero otherwise. Let A be the infimum, on absorbing independent profiles, of the sum of unrestricted native terminal regrets. A counterexample to existence of a uniform-equilibrium payoff, at any signed own levels, implies A>0. Indeed same-table single-pivot normalization gives a counterexample with one own level 1, three zero, and the same Z up to common positive scaling. On absorbing profiles its pivot shift adds 1 to the pivot's prescription and every finite offer; late finite offers dominate the literal Never offer at nonnegative own levels. The positive terminal-regret infimum of the normalized game implies A>0. [Single-pivot normalization](../../UniformEquilibrium/Diagnostics/Quitting/FinFourSinglePivotNormalization.lean) · [Terminal regret criterion](../../UniformEquilibrium/Quitting/Terminal/TerminalDebtSumInf.lean)

**Necessary condition.** For every pivot p and c with c_p=0, c_j>0 otherwise, A>0 supplies the minimum-price data below. Whenever their effective cap b is strictly positive in every coordinate, the following finite real-algebraic system is necessary. Write q for one nonzero opening vector, T for its positive coordinates, Q_i for the expected forced-Quit offer there, P_i for the unconditional contribution of nonempty rival exits if i waits, H_i=∏_{a≠i}(1−q_a), S=∏_a(1−q_a), and R_i=q_i Q_i+(1−q_i)P_i. There are ρ≥A/Σc_j, positive n_j for j≠p, n_p=0, and independent tail laws on a *common menu of 29 ordered finite dates and Never* such that, writing u for their four prescribed payoffs, e⁺_j for each loser's literal Never payoff and n⁺ for their Never marginals,

    n⁺_p=0,   n_j=(1−q_j)n⁺_j   (j≠p),
    b=R+Su+ρc,   b_j=P_j+H_j e⁺_j+c_jρ/n_j   (j≠p),
    b_i≥Q_i for every i, with equality on T.

At an active loser put m_j=min_{∅≠C⊆I∖{j}}Z_j(C). Then

    Q_j ≥ P_j+H_j m_j+(1−q_p)∏_{a∉{p,j}}n_a (Γ_jp−m_j)+c_jρ/(1−q_j)
        > P_j+H_j m_j.

Deleting j reveals a nonempty rival exit since p is finite. On the event that p survives the opening and the other two losers choose Never, this exit is the singleton p. Independent clocks give the displayed probability; n_j≤1−q_j. The simple strict passive-floor comparison also follows directly from the earlier conditional recursion.

**Source and proof.** Take the compact closure of the four native prescriptions U, caps B, literal Never values e and marginal Never probabilities n of actual independent clocks. Write d=B−U and Δ=B−e. Repairing vanishing Never mass of p to a finite date costs o(1) in these data, uniformly over complete replies. Thus Σd≥A if n_p=0. Minimize ρ≥0 on the conditions n_p=d_p=0 and, for j≠p,

    n_j>0,   d_j=n_jΔ_j≤c_jρ,   (1−n_j)(c_jρ−d_j)=0.

The sole finite p with others Never is feasible at high price. Every feasible ρ≥A/Σc_j; if n_j<1 then n_j≥c_jρ/(2M) for a native bound M≥1, so a minimum exists on a compact sublevel. Giving each loser the private bonus λ_j=c_jρ/n_j on the complete action Never makes its prescribed value equal its augmented cap b_j=U_j+c_jρ=e_j+λ_j. Indeed λ_j=Δ_j if n_j<1, whereas U_j=e_j and λ_j≥Δ_j if n_j=1. Put b_p=U_p=B_p. Blank is the only Nash row at continuation b. Prefixing a Nash row of joint survival C transports each bonus by its rival survival H_i, so the resulting prescribed augmented value is precisely the stage equilibrium payoff, with vanishing full augmented regret. If C=0 the absorbing native point has zero regret. If 0<C<1, the transported bonus is c_j Cρ divided by the new losing marginal. Zero augmented regret implies feasibility at Cρ because it equals the sum of the nonnegative terms d−nΔ, (1−n)(λ−Δ)_+, and n(Δ−λ)_+. Both alternatives contradict A>0 or minimality. Finite Nash existence now gives b≥0.

If b≫0, take the first date on actual approximating profiles where total cumulative finite mass reaches a fixed η>0 with Mη<min b_i/2. Its existence follows from the finite pivot after repair. Any earlier finite offer has absolute value ≤Mη, so vanishing mass-weighted augmented shortfall makes the whole skipped mass o(1). The limiting selected atoms give a nonzero q and b_i≥Q_i with equality on T. When S>0 condition each private clock on individually surviving this row. Independence and the negligible skipped mass yield the two payoff identities and the marginal identities after passing to limits. If S=0, only p can be sure at this row. All H_j=0 for losers, so any tail with these marginals and a finite pivot works.

To realize the conditional data exactly, truncate each finite-time sublaw with vanishing total-variation error and keep its Never mass fixed. With the other laws fixed the seven payoff coordinates are affine in one owner's conditional-on-finite law. Apply Carathéodory successively. The pivot needs at most eight finite atoms; each loser needs at most seven, since its own deleted payoff is constant under its own replacement. A never-only clock needs no finite atom. Compress the combined dates to ordered ranks, preserving ties, and take a subsequential limit in the product of fixed finite simplexes. This proves the claimed joint representation and exactness for these projected coordinates.

For a smaller linear test at fixed n⁺, the convex hull of the attainable seven-vectors is exactly the hull of the 75 vectors indexed by weak orders of the four players. Sample tentative finite dates independently for all players (arbitrarily for a never-only clock); erase each date independently with probability n⁺_i. Conditional on the four tentative dates all seven expectations depend only on their weak order, with each coordinate obtained by summing over the 16 erasure patterns. Conversely each order is attained by deterministic ranked dates followed by the independent erasures. Hence every linear bound at fixed marginals can be optimized over these 75 vectors. The actual common-tail representation also retains restrictions from independent tentative dates.

The statements about the finite tail concern the indicated seven payoffs and Never masses. Preservation of the full tail reply caps and the global price optimum remains an additional obligation. The opening condition applies at a strictly positive minimum; a zero cap or a minimum with mixed zero and positive coordinates needs its own exclusion before this test yields an existence result.

**Why one payoff marginal at a time loses information.** Here is a rational one-row witness even if the four prescribed tail payoffs are required to agree in all separate tests. Set p=0, c_j=1 off p, ρ=1/100, q=(0,1/2,1/2,0) and n⁺=(0,1/2,1/2,1/10). Use these native rewards:

* Row 0 pays 1 on {1,2}, zero elsewhere.
* Passive row 1 pays the indicator of 0∈C, 3∉C. Participating row 1 pays 8 if 0∈C, 83/100 if C={1,2}, zero otherwise.
* Passive row 2 pays the indicator of 3∈C, 0∉C. Participating row 2 pays 2 if 0∈C, 83/100 if C={1,2}, zero otherwise.
* Row 3 earns 1 when passive, 9 when quitting with 0, and zero at its remaining exits.

Take u=(0,79/100,79/100,34/25). The head formulas give b=(1/4,83/200,83/200,11/10); Q=b on {1,2} and Q=0 elsewhere. All losing marginals n are positive and their required conditional deletions are (3/4,3/4,1). Pointwise a successful deletion-1 score requires the pivot strictly before 3; a successful deletion-2 score requires 3 strictly before the pivot. Their sum is at most one. This rules out any common tail.

Nevertheless each deletion value can occur with exactly these u and n⁺. Let the pivot surely stop on date 2. Let 3 stop on date 1 with probability t, date 2 with probability k, Never with probability 1/10, and otherwise date 3. Players i=1,2 independently stop on date 2 with probabilities a_i, choose Never with probability 1/2, and otherwise stop on date 3. Write d=1−t−k. The deleted values are (d,t,1). Row 0 always earns 0; the other prescribed values are

    u₁=d+[8(1−t)−d]a₁,     u₂=t+2(1−t)a₂,     u₃=1−t+8k.

Choose t=41/225, k=61/900 for the first test, or t=3/4, k=111/800 for the second. In both cases k=(9/25+t)/8, t+k≤9/10. They give respectively d=3/4 and t=3/4. In each take a₁=(79/100−d)/[8(1−t)−d] and a₂=(79/100−t)/[2(1−t)], both strictly between zero and 1/2. Either tail also realizes the third deleted value. Thus even the exact separate independent-clock fibers at fixed u and n⁺ intersect the target strictly more often than the joint one does. The sure pair {1,2} is a Nash row at every continuation, so this diagnostic configuration also fails the earlier optimal-survival test. It illustrates the information in the projected data; it does not by itself supply a new raw existence class.

# Independent private clocks exclude a neighborhood of a cyclic ordering

Let X,Y,Z be independent finite deadlines on an ordered set, allowing ties. Among the three strict comparison probabilities Pr(X<Y), Pr(Y<Z), Pr(Z<X), at least one is less than 2/3−1/400. This elementary bound suffices to separate the private-clock projection from its convex hull on native opening data.

Call an outcome good if exactly two cyclic comparisons hold. The three good orders are XYZ, YZX and ZXY (earliest first). Write their probabilities as p₁,p₂,p₃, and write b for the probability of all remaining orders, ties included. Three independently sampled triples give
```
6 p₁p₂p₃ ≤ 24 b.
```
Indeed on the event that the three observed orders are distinct and good, some one of the 24 off-diagonal triples obtained by picking X,Y,Z from arbitrary samples must be bad. To see this, suppose the whole three-by-three-by-three Cartesian product were good. Connect the cell of one observed order to a different observed order by changing one coordinate at a time. Across a single change which alters the order, the moving coordinate must cross both others, since the parity of the permutation is the same at both ends. For those two values of the moving coordinate, every choice of the other two has either both between the endpoints or neither between them. There are no ties on the assumed product. Since one crossing occurred, independently varying the other two shows that *all* their values lie strictly between those endpoints. Fix the moving coordinate at the lower endpoint. Goodness then forces the other two coordinates into one fixed relative order for every choice, contradicting occurrence of all three cyclic orders. Each off-diagonal triple has the original marginal triple law by independence across coordinates, even when two selections come from the same sample. The union bound proves the inequality.

If all three comparisons have probability at least 2/3−ε, the expected number of successes is at least 2−3ε and at most 2−b, so b≤3ε. Each success probability is at most 2/3+2ε by the same sum bound and the two other lower bounds. The failure of each comparison on a good outcome identifies exactly one of the three orders. Hence pᵢ≥1/3−2ε−b≥1/3−5ε. For ε=1/400 the inequality above would give (1/3−5/400)³≤12/400, false by cubing rational numbers. This proof uses no assumption on the number or spacing of dates.

## A strictly positive opening that distinguishes private tails from their convexification

Use native centered units and label the pivot 0. Among the three losers cyclically permute 1,2,3. For each loser j let y be its cyclic successor and z its cyclic predecessor. Its payoff on every nonempty coalition D omitting j equals one if y belongs to D and z does not, and zero otherwise. Its participant reward is seven on {0,j}, −17/4 at the grand coalition, and zero elsewhere. Pivot 0 receives one whenever absent, one on every pair {0,j}, 39/8 at the grand coalition, and zero at its remaining participant positions. All four own singleton rewards in native units are zero.

Take q=(1/2,1/2,1/2,1/2), prices c₀=0 and cⱼ=1, full price ρ=1/96, and conditional Never probabilities n₀⁺=0 and nⱼ⁺=1/2. Thus nⱼ=1/4, Hᵢ=1/8, S=1/16. Denote the unconditional passive head by Pᵢ and the immediate Quit offer by Qᵢ. The pivot has P₀=7/8, Q₀=(3+39/8)/8=63/64. Each loser has Pⱼ=1/4 and Qⱼ=(7−17/4)/8=11/32. Set bᵢ=Qᵢ. All four offers are strictly positive and all four contacts hold.

Take the equal convex combination of the three cyclic strict orders of tentative finite loser dates, and make the pivot tie the last of them. In each order erase each loser independently to Never with probability 1/2. This is a mixture of three actual independent calendars, each with the stated marginal Never probabilities. In every losing row the passive payoff after its own deletion has expectation eⱼ⁺=1/4+(1/4)(2/3)=5/12. If at least one loser is retained, the earliest retained losing label is uniformly distributed by cyclic symmetry, possibly tied with the pivot. The passive indicator therefore contributes (1−1/8)/3=7/24 to the prescribed payoff. The event that j is last, retained, and both earlier losers are erased contributes another 7/24 through the participant pair with the pivot. Thus uⱼ=7/12 and u₀=7/8. In every row these values obey
```
bᵢ = qᵢQᵢ+(1−qᵢ)Pᵢ+S uᵢ+ρ cᵢ,
bⱼ = Pⱼ+Hⱼ eⱼ⁺+ρ/nⱼ  (j=1,2,3).
```
In particular all linear tests on the joint fixed-marginal tail vector accept these data.

For any actual independent tail with these marginals, draw each loser's tentative finite date from its conditional finite law, independently of the other laws and of the three independent Never erasures. In j's deletion experiment its indicator can pay only when y is retained and either z is erased or y's tentative date strictly precedes z's. A premature pivot can only reduce the payoff. Consequently
```
eⱼ⁺ ≤ 1/4 + (1/4) Pr(finite date of y < finite date of z).
```
The three comparisons are precisely a directed cycle (up to reversal). The preceding theorem forces at least one eⱼ⁺ < 5/12−1/1600. This remains a strict obstruction to the target vector in the closure. It is an independence constraint on the actual joint tail at a specified opening, price and marginals. Other openings and the separate minimum-survival and best-response requirements are untested. The example supplies no nonexistence conclusion for the original game.
