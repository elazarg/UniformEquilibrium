# How early can the intrinsic moment test detect simultaneous quitting?

For a hypothetical four-player counterexample, the unrestricted first-degree test already passes on the simplex of singleton exit payoffs. Here is a short finite proof of the cancellation. Let $s$ be the own singleton levels and $G_{ij}=r_i(\{j\})-s_i$. The checked necessary condition `finFour_singleton_r0Degree_eq_one_of_no_uniformPayoff` implies that $G$ is $R_0$ with nonzero degree. For every coordinate target $e_k$ choose $m\ge0$ with $Gm\ge e_k$ and $m_i((Gm)_i-(e_k)_i)=0$ for all $i$. This follows by the bounded-target degree homotopy: unbounded solutions would normalize to a nonzero homogeneous complementary vector. Punishment normality on the counterexample branch gives $s\ge\mu$.

On a set $J$ of remaining labels, let $Y(J)$ consist of probability vectors supported on $J$ with $Gx\ge0$. Starting with all labels, remove $i$ if $(Gx)_i>0$ throughout $Y(J)$. For each remaining $k$, its coordinate-target solution normalized to sum one lies in $Y(J)$: in removal order, every removed label had a strictly positive value and hence zero mass by complementarity at target $e_k$. In particular these sets are nonempty. The last label cannot be removed since the diagonal is zero. At termination choose for each remaining $i$ a row $x^i\in Y(J)$ with $(Gx^i)_i=0$. The resulting stochastic matrix admits a stationary distribution $p$. At weights $p_i$ the eligible tangent moves from $s+Gx^i$ toward $r(\{i\})$ have zero mean change because $\sum p_i x^i=\sum p_i e_i$. This first-moment cancellation is also present in the earlier Solan–Solan sunspot building blocks. It is not an independent equilibrium producer. [Checked singleton degree condition](../../UniformEquilibrium/Diagnostics/Quitting/FinFourSingletonDegreeCriterion.lean)

## Degree two detects simultaneous quitting on a nonstationary table

On this table the intrinsic degree-one moment equations admit tangent rows alone. At degree two every balanced probability must charge a row with at least two positive quit hazards. Two movers per date suffice at every degree. The original game admits an exact period-two terminal equilibrium and no stationary terminal equilibrium.

Number players from 0 to 3. Set r_i(S)=1+Z_i(S) on every nonempty exit. Let m(i)=i+2 modulo four and O_i be the two players other than i and m(i). Set

    G = [0,−1,−1,5; −5,0,2,−1; −2,4,0,−5; 3,−4,2,0],
    Z_i(S) = (1−2·1[i∈S]) Σ_{j∈S}G_ij
             +100·1[i∈{0,2}, m(i)∈S, O_i∩S≠∅].

Against hazards q the forced-Quit and passive exit contributions in native coordinates are −g_i+T_i and g_i+T_i, with g=Gq and T_i the expected bonus. Constant hazard 1/2 guarantees original payoff at least 1 against any opponents, and all-Never opponents bound punishment above by 1. The sure-opening test at punishment reduces to the box signs for G. The existing support census excludes every sure opening, and G is R₀ of degree +1. On the matching 02|13 the mate premium is −2G_im>0 and Z_i(T∪{i})=−Z_i(T) for every nonempty T⊆O_i. The existing matching construction applies with λ_i=1 and yields an exact period-two terminal equilibrium with at most two movers per date, giving an original uniform-equilibrium payoff. Its two phase increments cancel under weights proportional to the phase hazards. [Matching construction and census](../revisit/ALL_PROPORTIONAL_ADDITIVE_FOUR_PLAYER_UNIFORM_EQUILIBRIUM.md)

For degree one take tangent sources w=1+Gx with x=(0,5,15,4)/24 and (8,19,26,12)/65. Use probabilities 8/73 and 65/73, and respective owner laws e₀ and (0,62,93,40)/195. The two vectors Gx are (0,13/12,0,5/12) and (3/13,0,0,0), so all active owners are indifferent. The mean x and mean owner law both equal (24,62,93,40)/219.

Suppose a degree-two balance uses only tangents and positive single-owner rows. The linear form ℓ=(26,−1,25,17)/6 gives ℓZ=1 on singletons and has minimum 73/3 over larger coalitions by substitution. Its normalized increment on every such row is 1−ℓ(w−1), nonpositive throughout the exit hull. Consequently w=1+Gx almost surely for x∈Y={x≥0 : Σx=1, Gx≥0}, using punishment for the final inequality. A positive solo hazard h at i is proper since a sure row at w≥1 would also be sure at punishment. Its source and successor x'=x+h(e_i−x) both lie on Y_i={x∈Y : (Gx)_i=0}. Proper mixing fixes the own payoff at 1. For any k with G_ki<0 the optimal Wait earns at least the forced-Quit offer 1−hG_ki. For G_ki≥0 the successor is a convex combination of two payoffs at least 1 in coordinate k.

Consider

    U(x)=−68x₀+29x₁+45x₂+62x₀²+113x₀x₁+47x₀x₂−20x₁²−78x₁x₂−35x₂².

Write B_i(x)=∇U(x)·(e_i−x). For vertices b,c of Y_i the minimum of 2B_i((b+c)/2)−(B_i(b)+B_i(c))/2 is respectively 41/288, 544/4225, 1053/14450 and 479/4225. To reproduce this, solve Σx=1, (Gx)_i=0 and each choice of two further tight inequalities from x≥0, Gx≥0. Keep feasible solutions of nonsingular systems. The four faces have 4,3,4,4 vertices. For x=Σp_b b the polarized coefficients average to B_i(x) with weights p_b p_c, so B_i>1/16 on Y_i. Every permitted tangent increment is an owner-weighted mean of these derivatives. On a solo row the exact quadratic increment [U(x')−U(x)]/h equals B_i((x+x')/2)/(1−h/2), also above 1/16. Since G is invertible this contradicts balance of U(G⁻¹(w−1)).

To verify nonstationarity, all-Continue loses to Quit, every singleton column has a negative outsider with a profitable Quit, and a stationary sure quitter would give a sure opening at punishment. For any remaining stationary row write H_i=∏_{j≠i}(1−q_j). Comparing native Quit with Never requires R_i=(2−H_i)g_i+H_iT_i to vanish on active players. If either 0 or 2 is absent, or if they alone are active, all active bonuses vanish. Every principal block of G of order at least two is nonsingular. Support 023 fails since g₃=3q₀+2q₂>0. At full support g₁=g₃=0 imply g₀=(34q₂−103q₀)/4 and g₂=26q₀−8q₂, which cannot both be nonpositive. On support 012 put p=q₀, u=q₁, q₂=5p/2 from g₁=0. The resultant in u of R₀,R₂ is p²W(p), with

    W(p)=1259375p⁵−1280175p⁴−5608600p³+3656568p²−511216p+26256.

The minimum degree-five Bernstein coefficients of W on the three equal intervals partitioning [0,2/5] are 11917024/3375, 57430208/6075 and 139968/5. Hence W>0 throughout the required interval. This rules out the last support.


For this same table every singleton column has a negative outside entry $G_{ji}$ and the participant premium against that singleton is $-G_{ji}$. The sole-owner margin is therefore strictly positive. Together with the no-sure and positive-own conditions above, the forbidden-coalition theorem converts the intrinsic degree-two obstruction into a strictly positive lower bound on terminal exploitability plus the probability of a simultaneous first exit for arbitrary original profiles. The minimum number of simultaneous movers needed in an approximate calendar is exactly two. The prior matching construction accounts for existence; the calibration identifies exactly when the degree hierarchy first detects the necessary collision. [Fixed-target and forbidden-coalition tests](../exports/FORBIDDEN_COALITIONS_AND_FIXED_TARGET_MOMENTS.md)
