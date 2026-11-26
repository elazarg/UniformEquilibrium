# Two possible first quitters force a stationary equilibrium

In a four-player quitting game write r(T) for the reward vector when the nonempty coalition T quits first, r^k=r({k}), s_k=r^k_k, Γ_kl=r^l_k−s_k and J_kl=r_k({k,l})−s_k for k≠l. Live play and perpetual Continue pay zero. Hazards at each live date are independently randomized, and a deviation can replace a player's entire stopping law. Let μ_k be the infimum over opponent calendars of k's best-response terminal payoff. Assume some s_k>0, no one-stage Nash row with a sure quitter exists at continuation μ, and

    Δ = min_{l,0≤h≤1} max_{k≠l} (h J_kl−Γ_kl) > 0.

Fix distinct players i,j with Γ_ij Γ_ji≠0. There exist calendars with terminal exploitability tending to zero and probability of an outsider among the first quitters tending to zero **if and only if** the following stationary test succeeds. Require both ratios

    q_j = Γ_ij/J_ij,       q_i = Γ_ji/J_ji

to exist and lie strictly between zero and one. Put every other hazard equal to zero, and let w* be the conditional mean exit reward at this row. Require that at continuation w* both outsiders prefer Wait weakly. The two participating players are then indifferent. This stationary calendar is an exact terminal equilibrium against all players' unrestricted deviations. Every approximating sequence as above has the same limiting payoff w* and the same first-exit law: the one-date product probabilities on {i}, {j}, {i,j} divided by their sum. The stationary calendar delivers this fixed payoff as an original uniform equilibrium since every player faces geometric rival absorption even after any unilateral replacement. Conversely any original uniform approximate-equilibrium sequence with vanishing errors and vanishing outsider exit probability obeys the same restriction: for each fixed profile and replacement the bounded finite-average returns converge to their terminal expectations.

The intrinsic degree-two moment test allowing every subset of {i,j} is already equivalent to this stationary test. In particular, on a residual table with all reciprocal singleton comparisons nonzero and no stationary terminal equilibrium, every limiting law of approximate equilibria uses at least three different player identities. This counts all possible first quitters over the calendar. More quantitatively, there is a game-dependent η>0 such that exploitability plus the third-largest of the four singleton first-exit probabilities is at least η for every original calendar. This bound also applies to calendars permitting only two positive hazards per date.

## The two-moment test

For hazards q let p_T be the product probability of exit T, c=p_∅, a=Σq_k and F(w,q)=c w+Σ_{T≠∅}p_T r(T). The intrinsic states lie in H=conv{r^i,r^j,r({i,j})} above μ. At a positive-rate row the independent profile q on i,j is one-stage Nash at w. At zero rate use a proportion vector z on i,j with w≥s and z_k(w_k−s_k)=0. At positive rate put z=q/a. Define L_P=(P(F)−P(w))/a there and L_P=∇P(w)·(Σz_k r^k−w) at zero rate. The quadratic test asks for a probability balancing L_P for every polynomial of total degree at most two. The normalized functions are continuous, by the expansion F=w+a(Σz_k r^k−w)+O(a²).

All positive rows are proper, uniformly away from sure. Indeed a limit containing a sure player is Nash at some w≥μ. If just one player quits surely, lowering the continuation to μ only lowers that player's alternative Wait; with several sure quitters no unilateral comparison uses the continuation. Either case gives a forbidden sure row at μ. Consequently Continue is optimal for every player. For i, whose only possible rival is j, this gives

    F_i−r_i^j = (1−q_j)(w_i−r_i^j).

The normalized increment of (w_i−r_i^j)² is −z_j(2−q_j)(w_i−r_i^j)². This also holds on a tangent because z_i(w_i−s_i)=0. Quadratic balance forces w_i=r_i^j whenever z_j>0; interchange i,j for the other constraint. Both coordinates have zero drift on this almost-sure support. On a solo-i row they equal (s_i,r_j^i), on a solo-j row (r_i^j,s_j), and on a positive joint row (r_i^j,r_j^i). A tangent with both owners is impossible since Γ_ij≠0.

The affine function L(w)=1−(w_i−s_i)/Γ_ij equals one on the solo-i stratum and zero on both others. For every k the normalized increment of L(w)w_k is L(w)L_{w_k}, including on tangents, by zero drift of the domestic coordinates. If solo i had positive mass, the resulting conditional mean of w would equal r^i since L_{w_k}=r^i_k−w_k there. At solo hazard h each rival's optimal Wait requires w_k−s_k≥[h/(1−h)](J_ki−Γ_ki); at a solo tangent use h=0. Taking the conditional mean gives Γ_ki≥b(J_ki−Γ_ki) simultaneously for all k≠i, with b=E[h/(1−h)] finite. This contradicts Δ at b/(1+b). Interchanging i,j excludes solo j.

Thus both owners mix almost surely, and s_i+J_ij q_j=r_i^j and s_j+J_ji q_i=r_j^i determine the common hazards above. Then F(w,q)−w*=c(w−w*), so the squared distance to w* has strictly negative increment away from w*. Every degree-two witness is the point mass at this stationary row. Conversely that row balances every degree. If exactly one Γ is zero, its corresponding J is nonzero and the other Γ is nonzero, the same square-drift conditions exclude joint rows, while the other domestic coordinate distinguishes the two solos. In this case degree two is infeasible. With a flat direction Γ=J=0 the argument dividing these numbers does not apply.

## From actual calendars to quadratic balance and the limiting law

Let e be terminal exploitability, C the probability that an outsider is among the first quitters, S_t the probability of reaching date t, W(t) the prescribed terminal payoff from that date and b_k(t) the supremum available to k by replacing its strategy from there. Write M≥1 for a uniform bound on the absolute rewards. Following the profile to t and then optimizing gives 0≤b_k(t)−W_k(t)≤e/S_t. If perpetual continuation has positive probability S_∞, the conditional probability of any future exit tends to zero along the tail. Its prescribed payoff tends to zero and an immediate quit offer tends to s_k. Hence S_∞ max_k s_k≤e.

By the first-action Bellman recursion, l_k(t)=b_k(t)−F_k(b(t+1),q(t))≥0. Subtraction of the prescribed recursion and telescoping give Σ_t S_t l_k(t)≤e. For a sequence e+C→0 take η≥e+C tending to zero and δ=√η. End the prefix just after survival first falls below δ. Throughout this prefix all q_k≤1−γ for some fixed γ>0 and all sufficiently late sequence members: otherwise extract bounded b(t+1)≥μ and rows converging to a sure row; S_t≥δ and l_k(t)≤e/δ force that row to be Nash, contradicting the sure hypothesis as above. Thus survival just after the prefix is at least γ⁴δ. The prefix charge H_n=Σ a_t diverges, since −log c_t≤a_t/γ and final survival is less than δ.

Give date t mass a_t/H_n, omitting zero-charge dates, and use source b(t+1). The sum of all l_k over the prefix is at most 4e/δ. Endpoints F(b(t+1),q(t)) differ from b(t) by these errors, so normalized polynomial increments average to zero in the limit by telescoping. At zero-charge dates the prescribed step is the identity and any omitted endpoint difference has the same summable error bound. The concentration of relative regrets follows from their average bound 4e/(δ H_n). At a positive-rate limit the row is exact. At a zero-rate limit with vanishing relative regret one has w≥s, since otherwise immediate Quit is strictly better. If w_k>s_k then Wait is eventually strictly better and the relative regret is z_k times its strictly positive advantage; thus z_k=0. On the prefix Σ_t q_k(t)≤C/δ for each outsider, since S_t q_k(t) is the probability of that player quitting at that date. Hence all limiting proportions are on i,j. The sources approach H uniformly since conditional outsider or Never probability is at most (C+e/max s)/(γ⁴δ) and b−W is bounded by e/(γ⁴δ). They are already above μ. Compactness therefore gives an intrinsic degree-two witness. Its just-proved uniqueness implies Σ q_i/H_n→q_i*/Σq* and likewise for j; both total hazards on the prefix diverge.

To identify the initial payoff, prescribe that i always waits up to the end of the prefix and then optimizes. At a prefix date the loss of this first action from the optimal cap is at most l_i(t)/(1−q_i(t)), because the prescribed mixture assigns this positive probability to Wait and the other action has nonnegative loss. Iteration shows the initial cap differs from this strategy's payoff by at most e/(γδ). Under this replacement the chance of any outsider quit on the prefix is at most Σ_t Σ_{k outside}q_k(t)≤2C/δ. Rival j's survival through the prefix tends to zero since its total hazard diverges. Thus b_i(1), and also W_i(1), tend to r_i^j. Similarly W_j(1) tends to r_j^i.

Any subsequential limiting terminal law has masses u,v,d on {i},{j},{i,j}. There is no Never mass by the bound above. The two domestic payoff identities give Γ_ij u=(J_ij−Γ_ij)d and Γ_ji v=(J_ji−Γ_ji)d. These identities and u+v+d=1 uniquely determine the normalized product law of q*. Every other player's target is then its mean exit reward under that same law. Conversely repetition of q* gives exactly this law and has zero terminal regret. This proves the assertions for arbitrary initial calendars, including those occasionally using outsiders.

For the stated probability bound, on the same prefix each probability of singleton k at date t is at least γ³ S_t q_k(t). Beyond that prefix the entire exit mass is less than δ. Thus vanishing singleton probabilities for two named outsiders imply vanishing probability that either participates in any first exit. For this argument alone take δ=√η_n with η_n a positive upper bound tending to zero on the exploitability and both outsiders' singleton probabilities. If the asserted lower bound failed, pass to a subsequence with the two largest singleton probabilities at fixed labels i,j and apply the theorem.

## One flat domestic comparison can require a nonstationary fixed pair

Give all players original own level one. The following are native rewards after subtracting one at every nonempty exit. For any player $k$ and nonempty rival set $T$, let $P_k(T)$ be its reward when $T$ quits, and let $Q_k(T)$ be its reward when $T$ and $k$ quit. At empty $T$ set both functions to zero. This specifies all sixty original entries.

* $P_0(T)=1$ if $T$ contains 2 or 3, and zero otherwise. Put $Q_0(T)=0$ always.
* $P_1(\{0\})=1$, $P_1(\{2\})=-1/2$, and all other passive values are zero. Set $Q_1(T)-P_1(T)=1$ if 3 is absent and $-1$ otherwise.
* $P_2(\{0\})=P_2(\{3\})=-1/2$, $P_2(\{1\})=P_2(\{0,1\})=1$, and all its other passive values are zero. Set $Q_2(T)-P_2(T)=33/26$ if 1 is absent and $-7/13$ otherwise.
* $P_3(\{0\})=1$, $P_3(\{1\})=P_3(\{0,1\})=-1$, and all its other passive values are zero. If 2 is absent, set $Q_3(T)-P_3(T)=5/13$ when 1 is present and $-9/13$ otherwise. If 2 is present these differences are respectively $1$ and $-100$.

Thus $\Gamma_{01}=J_{01}=0$, $\Gamma_{10}=1$, $J_{10}=2$. Player 0's allowed native payoff is always zero. In the order of sole movers $0,1,2,3$ the blockers $2,3,1,2$ give $hJ_{kl}-\Gamma_{kl}\ge5/13$ for every $0\le h\le1$.

**No sure Nash opening at punishment.** If 1 is sure, 3 strictly wants to join whatever other rivals do. Then 1 strictly wants to wait against sure 3. If 3 is sure, 1 strictly waits and 2 strictly quits. Against sure 2 with 1 silent, 3 strictly prefers waiting. Both cases are impossible.

If 2 is sure, both 1 and 3 mix: either being pure entails one of the already excluded sure cases, since 1 wants to quit when 3 is absent and 3 wants to wait when 1 is absent. Their indifference forces $q_3=1/2$ and $q_1=100/101$. Player 2's own native withdrawal continuation $\mu_2-1$ is at least $-7/13$, the minimum of its immediate Quit payoffs over all rival coalitions. Let $H$ be the probability of no rivals quitting in this row. Its gain from Quit at that continuation is at most
\[
 -(7/13)(100/101)+(33/26)(1/101-H)+(7/13)H<0.
\]
This excludes a sure 2 even when another player is sure. Finally suppose 0 is the only sure player. Again 1 and 3 both mix, because if 3 is silent then 1 wants Quit, and if 1 is silent then 3 wants Wait. Indifference of 1 forces $q_3=1/2$. Player 0 can always secure original one immediately, so $\mu_0-1\ge0$. Its forced-Continue offer is strictly positive in native units since 3 moves with positive probability, whereas forced Quit pays zero. Thus 0 cannot be sure either.

**An exact calendar on the fixed pair.** Alternately play $A=(1/4,0,0,0)$ and $B=(1/2,1/2,0,0)$. Players 0 and 1 have native Wait values zero and one respectively at both dates. Forced Quit returns zero to 0, and $2q_0$ to 1, giving exactly their prescribed support inequalities.

For outsider $k$ write $a=P_k(\{0\})$, $b=P_k(\{1\})=P_k(\{0,1\})$, with $(a,b)=(-1/2,1)$ for 2 and $(1,-1)$ for 3. Its native waiting values solve $W_A=a/4+3W_B/4$, $W_B=a/4+b/2+W_A/4$, namely
\[
 W_A=(7a+6b)/13,\qquad W_B=(5a+8b)/13.
\]
Its single-rival joining values satisfy $g=Q_k(\{0\})=(28a+24b)/13$ and $d=Q_k(\{1\})=Q_k(\{0,1\})=4(b-a)/13$. Thus its forced Quit pays $g/4=W_A$ at $A$ and $g/4+d/2=W_B$ at $B$. All four players' full replacement values follow by Bellman iteration because every player faces recurrent rival absorption. The calendar is original exact terminal Nash, gives a fixed uniform payoff, and only 0 and 1 ever have a positive prescribed hazard.

**No stationary calendar on that pair is Nash.** AllContinue loses to an immediate positive own Quit. A sole stationary mover violates the stated uniform blocker condition (and the native and original comparisons agree for the blocker). Any stationary sure quitter would yield a sure root at punishment. With two proper movers, 1 obtains one in native units from perpetual waiting. Its indifference requires $2q_0=1$. Write $v=q_1$. The outsider Wait minus Quit, multiplied by $13(1+v)>0$, equals $a A(v)+b B(v)$, where
\[
 A(v)=18v^2-9v-1,\qquad B(v)=8v^2+22v-12.
\]
Indeed the conditional mean Wait payoff is $[(1-v)a+2vb]/(1+v)$ and Quit pays $(1-v)g/2+vd$. The two quiet inequalities would require $A(v)/2\le B(v)\le A(v)$, hence $A(v)\ge0$. Convexity gives $A(v)\le-1$ on $[0,1/2]$. On $[1/2,1]$, $B-A=-10v^2+31v-11$ is increasing and at least two. This excludes every $v$.

The original positive own levels, no sure opening and strictly positive sole-owner margin hold on this same game. The example concerns schedules on this particular fixed pair; it asserts no exclusion of stationary equilibria with other prescribed participants.


## Project scope and formalization

The checked terminal-to-uniform endpoints are `quittingGame_isUniformEquilibriumPayoff_of_terminalNash_tendsto` and `exists_terminalNash_terminalPayoff_close_of_isUniformEquilibriumPayoff` in `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`. The project already has the two-player stationary support equations, the common-word realization for prescribed two-owner heads in `UniformEquilibrium/Quitting/Boundary/Holonomy/TwoOwnerCommonWordRealization.lean`, and a persistent-clock characterization of survival after deleting one player. Those ingredients do not classify every calendar whose limiting exit law uses two fixed identities. This classification uses only a second-degree necessary test for actual calendar limits, proves its sufficiency for the reciprocal-nonzero pair mask, and identifies the entire physical first-exit law. The direct support restriction does not require the general moment hierarchy as an input.

A formalization can first prove the two coordinate-square identities for exact and tangent rows, then the affine selector identities, the blocker contradiction, and the collapse of the joint sector. The passage from arbitrary calendars uses only bounded Bellman caps, high-survival prefixes and concentration of the hazard-weighted rows. The explicit flat table verifies the failure of unrestricted stationary classification when a reciprocal comparison and its corresponding joining reward both vanish. The general four-player existence conjecture remains open.
