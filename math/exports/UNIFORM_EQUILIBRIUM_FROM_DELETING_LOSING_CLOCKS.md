# Deleting losing clocks gives welfare bounds for each possible opening support

## Exact statement

Four players use independent private stopping laws on the natural dates and Never. The first nonempty stopping coalition S absorbs and pays r(S). The live and perpetual rewards are zero. A player may replace its entire law. Write I={0,1,2,3}, s_i=r_i({i}), Z_i(S)=r_i(S)−s_i, Γ_ij=Z_i({j}) and J_ij=Z_i({i,j}) for i≠j. The native game pays Z at absorption and zero otherwise. Write Q_i(q) for its expected reward if i quits while its opponents quit independently with probabilities q_j. The support of q consists of its strictly positive coordinates.

Fix one player p and three numbers c_j>0 for j≠p. A functional consists of w∈ℝ⁴ and a_j≥0 for j≠p with Σ_{j≠p}c_j w_j>0. Define its fifteen corrected values by
```
L(S) = w·Z(S) + Σ_{j∈S, j≠p} a_j[Z_j(S∖{j})−Z_j(S)]    (|S|≥2),
L({p}) = w·Z({p}),
L({j}) = w·Z({j}) + a_j min_{∅≠R⊆I∖{j}} Z_j(R)        (j≠p).
```
Assume some functional has min L≥0. For each support T of a nonzero q with Q_i(q)>0 for all i∈T, assume there is a functional and a real h (both may depend on T) such that min L≥h, w_i≤0 outside T, and for every such q on T,
```
Σ_{i∈T}w_i Q_i(q) + Σ_{i∉T} w_i max(0,Q_i(q)) ≤ h.
```
Finally, in every triple V require either a j∈V with J_ij−Γ_ij≤0 for both i∈V∖{j}, or an i∈V with J_ij−Γ_ij>0 for both j∈V∖{i}.

Then the infimum A of total unrestricted native terminal regret over absorbing profiles is zero. Every original table with these centered entries and arbitrary signed own levels has a uniform-equilibrium payoff. The conditions use only the rewards and quantification over finitely many real variables.

## From a counterexample to a signed-price minimum

For a native profile let U_i be its prescribed payoff, B_i its full unilateral cap, e_i its literal Never payoff and n_i its marginal Never mass. Regret is d_i=B_i−U_i. Write Δ_i=B_i−e_i. Every finite query is a pure deadline. Late finite deadlines tend to the native Never payoff because quitting alone pays zero. An arbitrary replacement averages these pure offers. Use the compact Euclidean closure of the tuples (U,B,e,n) of actual private profiles. For a common bound M≥1 on the absolute native rewards, 0≤d_i,Δ_i≤2M there. If n_p=0, then Σd_i≥A, since one may move the vanishing Never mass of p in any approximating sequence to a finite date. Coupling bounds the resulting changes in each prescribed payoff and every rival query by twice M times the moved mass.

Suppose A>0 and minimize ρ≥0 over this compact carrier subject to
```
n_p=0, d_p=0,    n_j>0, d_j=n_jΔ_j≤c_jρ, (1−n_j)(c_jρ−d_j)=0   (j≠p).
```
Making p surely stop alone and having everyone else play Never is feasible for sufficiently large ρ. Every feasible price is at least A/Σc_j. If n_j<1, then 2Mn_j≥c_jρ; otherwise n_j=1. These positive lower bounds on the n_j give closedness on any bounded price sublevel, hence a positive minimum. At a minimizer credit the whole Never action of each loser j with λ_j=c_jρ/n_j regardless of rival behavior, and put λ_p=0. Then the prescribed augmented payoffs equal their complete augmented caps:
```
b_p=U_p=B_p,     b_j=U_j+c_jρ=e_j+c_jρ/n_j=max(B_j,e_j+λ_j).
```
For n_j<1 this follows from λ_j=Δ_j. For n_j=1 we have U_j=e_j by coupling and d_j≤c_jρ. The private credits are used only in the proof.

Blank is the unique Nash row of the one-date native prefix with child b. To prove this take any Nash row q, put t_i=1−q_i, H_i=∏_{k≠i}t_k, C=∏t_i, and prefix the carrier point by this row by prefixing actual approximants. The new marginal is n'_i=t_i n_i. Use credits λ'_i=H_i λ_i. A finite query from after the row now gives a passive head contribution plus H_i times its old native offer; the best such query and the new Never offer together give exactly the same passive contribution plus H_i b_i. Quitting at the head gives Q_i(q). The prescribed augmented payoff also equals the stage payoff, since its tail prescribed credit is Cn_iλ_i. Thus augmented regret vanishes at the prefixed point. When C=0, all realized credits vanish, so native regret vanishes at an absorbing carrier point, impossible. When 0<C<1, each losing n'_j>0 and λ'_j=c_j Cρ/n'_j. For any point and nonnegative credit λ the augmented regret equals
```
d−nΔ+(1−n)(λ−Δ)_+ + n(Δ−λ)_+.
```
All terms are nonnegative because prescribed finite deadlines earn at most the native cap. Their vanishing at the prefixed point gives precisely the feasibility conditions at Cρ. This contradicts minimality. Existence of a finite-game Nash row gives the claimed uniqueness and b≥0.

Only b=0 or b≫0 is possible. With one zero a small solo hazard of that player is Nash. With two zeros a nonpositive joining increment permits a small solo hazard of the other player. If both increments are positive, lower both zero continuations to −ε. Equilibrium rows could converge only to blank as ε decreases to zero. Near blank the two positive-continuation owners wait, and either zero-continuation player i then strictly prefers Quit by ε(1−q_j)+(J_ij−Γ_ij)q_j>0, a contradiction. With three zeros the first triple alternative gives a small solo hazard. For the second alternative lower all three zeros to −ε. Near blank the fourth player waits, and the specified zero-continuation player i has a quit gain equal to εH_i plus positive linear terms in the two other zero players' hazards and an error quadratic in their sum. It is strictly positive throughout a fixed neighborhood of blank. The same compactness argument rules this out.

## The deletion inequality and the first physical date

On actual approximants give p a surely finite law by the negligible change above. Compare all losing players' individual deletions on the *same* four drawn clocks by sending each tested player's own clock to Never. If the first coalition is S, deleting an absent player changes nothing. Deleting j∈S with |S|≥2 changes the first coalition to S∖{j}. When S={j} with j≠p, deleting j exposes a nonempty rival coalition because p surely stops. Average these pointwise comparisons and pass to the carrier limit. For every functional,
```
w·U + Σ_{j≠p} a_j(e_j−U_j) ≥ min L,
w·b ≥ min L + ρ Σ_{j≠p} c_j[w_j + a_j(1/n_j−1)] > min L.
```
The functional with min L≥0 excludes b=0, so all b_i are strictly positive.

On the approximants the prescribed-mass weighted sum of finite-deadline and literal Never shortfalls from the actual augmented caps tends to zero. Every shortfall is nonnegative. Choose a fixed η>0 small enough that Mη is below half the smallest limiting cap. Consider the first date at which the sum of cumulative finite marginal masses reaches η; it exists because p is surely finite. At all preceding dates every finite offer has absolute value at most Mη, since without a rival quitting by that date it pays zero. Total prescribed mass on all preceding dates must therefore tend to zero. Along a subsequence the four atom sizes at the selected date tend to a nonzero q. Earlier rival mass tends to zero, so each native finite offer on this date tends to Q_i(q). Thus b_i≥Q_i(q) for every i, with equality for each i in T=supp(q) by its positive assigned mass. All active Q_i(q)>0. The chosen functional for T satisfies w·b≤Σ_{i∈T}w_iQ_i(q)+Σ_{i∉T}w_i max(0,Q_i(q))≤h, contradicting w·b>min L≥h. A single p suffices because the minimum was proved for every p on the same native table.

To connect to the original target, a counterexample at any signed own levels admits the checked same-table single-pivot normalization, whose centered rewards differ only by a common positive scale. Its own singleton is one at the pivot and zero elsewhere. On every absorbing profile this pivot shift preserves regret: its prescribed payoff and every finite deadline shift equally, and the finite-query supremum dominates literal Never at nonnegative own levels. The normalized counterexample has positive infimum of the total full terminal regret, giving A>0 after undoing the scale. The contradiction yields one original payoff target for all accuracies over sufficiently long horizons against complete behavioral deviations. [Single-pivot normalization, `nonempty_finFourSinglePivotNormalization_of_no_uniformPayoff`](../../UniformEquilibrium/Diagnostics/Quitting/FinFourSinglePivotNormalization.lean) · [Terminal regret criterion, `quittingTerminalDebtSumInf_pos_iff_not_exists_uniformEquilibriumPayoff`](../../UniformEquilibrium/Quitting/Terminal/TerminalDebtSumInf.lean)

## A proper positive opening and a different full positive opening

Use cyclic indices modulo four. Each crossed singleton entry (from a neighbor) is −1. The opposite mate entries in rows 0,1,2,3 are respectively 5/2,100,20,100. Put K>100 and P>100K. Every passive coordinate in a pair or triple is P except in row 0 where it is −10. In a proper nonsingleton S containing i the default payoff is 3 if i+1∈S, −2 if the successor is absent but i−1∈S, and −1/1000 otherwise. Replace Z_2({0,1,2}) by 1/10⁶, and replace every proper participant payoff in row 3 with 1∈S by −100. All four grand rewards equal −K. The positive joining increments occur exactly at j=i+1. Every triple has a column with neither incoming increment positive.

Take p=0 and all three prices c_j=1. In both functionals use a_1=1 and all other a_j=0. The functional for the full support is w=(10,1,1,1), h=15. The singleton corrected minima exceed 15: the four uncorrected weighted singleton sums are respectively 18,89,23,89 and the correction at {1} is at least −1. In every proper pair or triple there is a passive cell outside row 0 paying P unless S={1,2,3}; in that case deletion of row 1 replaces its payoff by P. A passive recipient outside S keeps its payoff under the correction. The remaining corrected entries in each proper column are at least −100 and the sum of the four positive weights is 13, so P>100K suffices. Grand corrected welfare is P−12K. This functional also excludes b=0.

Positive support propagates to clockwise successors except when row 2 gets its exceptional reward with both 0 and 1 active. Hence the only possible proper positive support is T={0,1,2}. On full support the positivity of Q_3 implies q_1<3/100 because Q_3≤3q_0(1−q_1)−100q_1. The upper bound Q_0≤3q_1 gives w·Q<10 there. Full positive support occurs for sufficiently small positive multiples of (1,1/100,7/10,1/100): the derivatives of the four forced-Quit offers in this direction are respectively 0.0093, 0.09999, 0.009 and 0.6.

For T take w=(−1,1/20,0,0), h=−13/5. At singletons the corrected minimum is −51/20 at {2}. In a pair or triple not containing 0 the contribution from row 0 is +10. The contribution from row 1 is at least −1−(19/20)3 if deleted, and nonnegative if passive. In a proper nonsingleton containing 0 but not 1, row 0's own payoff is nonpositive and row 1 is passive. At {0,1} the corrected sum is −3−2/20+1=−2.1; at either triple containing this pair deletion replaces row 1's own payoff by P, with its remaining coefficient −19/20. The grand corrected sum is K+P+19K/20. Thus min L≥−51/20>h.

At T, Q_2>0 implies q_1>1000/1001: its positive term 10⁻⁶q_0q_1 must exceed 10⁻³q_0(1−q_1). Then Q_0≥3q_1−(1−q_1)/1000 and Q_1≤3, giving −Q_0+Q_1/20<−2.8<h. At q=(1,1,1,0) the three active offers are 3,3,10⁻⁶. Consequently a test requiring every positive-active row to have full support fails outright. Pure column welfare at the grand coalition is strictly negative for every nonzero nonnegative weighting. No pair has two positive participant joining rewards. The hard singleton matrix has a strictly positive off-diagonal mate in each row, two negative crossed entries, and every row sum is positive. All of these comparisons are exact raw constraints.

The family contains open sets in the whole centered reward space, for arbitrarily large K. Every disallowed positive opening requires a successor-absent participant state whose rewards are strictly negative apart from the specified exceptional triple. On T, the strict coefficient bounds forcing q_1 close to one persist under small perturbations; on full support the strict high penalty when 1 participates in row 3 still forces q_1 small. The lower bounds, both price sums, the two exhibited positive openings and the triple signs all have slack. Arbitrary signed own levels vary independently as well.

The new mathematical producer is the weighted lower bound on b from the simultaneous comparison of individual Never replies, followed by a different reward certificate for each feasible opening support. It uses neither a prescribed equilibrium nor a public random signal. For formalization the finite-data input consists of the corrected columns and support tests above; the native absorbing-regret criterion is the intermediate conclusion, and the linked same-table normalization and terminal criterion are the semantic consumer. Tables failing these sufficient inequalities remain open to other methods.
