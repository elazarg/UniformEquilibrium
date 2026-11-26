# Independent joining factors on the diamond

Four players X,Y,U,V independently choose Continue or Quit on each live date. A first nonempty coalition S absorbs with rewards r_i(S). The live stage, the selecting stage, and perpetual Continue pay zero. Let s_i=r_i({i}) be arbitrary signed numbers and Z_i(S)=r_i(S)−s_i on nonempty coalitions. Suppose the native singleton matrix in that order is

    Γ = [ 0  −1   2   2 ]
        [ 2   0  −1  −1 ]
        [−1   f   0  −g ]
        [−1   f  −g   0 ].

Assume g>0 and 4f>1+g. Take any independent k_X,k_U,k_V in [0,1] and k_Y in [0,1/2]. For i outside S let Z_i(S)=∑_{a∈S}Γ_ia, and for i in S let Z_i(S)=k_i ∑_{a∈S}Γ_ia. Then there is a three-date periodic strategy profile that is exact terminal Nash against all unilateral behavioral replacements. It gives one fixed original uniform-equilibrium payoff, using the same profile for all accuracies. Consequently every game in this family with any f,g>0 has a uniform-equilibrium payoff. Indeed det Γ=2g(4f−g−1), and the existing nonpositive-determinant UE theorem in `FIN4_STRICT_INVERSE_COLUMN_AND_ALL_END_MINIMUM_REDUCTION.md`, Part I equation (4), covers 4f≤1+g even for arbitrary higher coalition data. Only the positive-determinant case asserts the three-date construction here. Both twin factors range over the whole square. The previous symmetric-diamond joint theorem proves the diagonal and the square k_U,k_V≤2f/(2f+g).

## Three dates and the two core rows

On dates A,B,C, repeated in that order, use independent hazards

    A   (x,0,0,0)       B   (0,y,p,q)       C   (0,0,r,s).

Write z=(p,q,r,s), P=p+q, R=r+s, L=(1-p)(1-q), H=(1-r)(1-s). At a date t and receiver i, let b_it denote the expected native exit reward at that date if i waits, counting survival as zero, h_it opponents' survival and Q_it the native reward from quitting immediately. Additivity gives b_it=∑_{j≠i}Γ_ij q_jt and Q_it=k_i b_it. The native value N_it of always waiting, when opponents absorb almost surely, obeys N_it=b_it+h_it N_i,t+1 with cyclic indices. Set

    y=(2P+2RL)/(1+2RL),
    x=[R+(1−k_Y)P/L+k_Y P H]/[(2+k_Y P)H].                    (1)

Provided x,y are in [0,1] and z≠0, both are strictly positive. The X row has N_A=N_B=0 and N_C=2R. The Y row has N_B=−k_Y P, N_C=(1−k_Y)P/L, N_A=2x−(1−x)k_Y P. Indeed the B and C recursions in these two rows give (1), and substitution checks all six identities. In particular the scheduled players X and Y are indifferent at their respective active dates.

## Complementarity in the four twin hazards

For each twin i and t=B,C, take the continuous residual

    F_it=b_it+h_it b_i,t+1+h_it h_i,t+1 b_i,t+2 − D_i Q_it,
    D_i=1−h_iA h_iB h_iC.

Order the residuals as (U at B,V at B,U at C,V at C). If D_i>0 then F_it=D_i(N_it−Q_it). We first take k_U,k_V<1. In R^4 write z⁺ componentwise for max(z,0), evaluate all P,R,L,H,x,y,F at z⁺, and set

    Ω={z∈(−1,3/4)^4 | P<1/2, R+(1−k_Y)P/L<2H}.

The closure has L,H>0 and 0≤x,y≤1. A nonnegative point in the closure has p,q≤1/2 and r,s≤2/3, the latter because r≤R≤2H≤2(1−r), and likewise for s. Thus its boundary requires either x=1 or y=1. At the origin F vanishes. For nonnegative z near zero, let M=P+R. Uniformly for all allowable twin factors, (1) gives x=M/2+O(M²), y=2M+O(M²). For every twin i and either slot t, with p_j,r_j the other twin's two hazards, the residual expansion is

    F_it=(2f−1/2)M−g(p_j+r_j)+O(M²).

Indeed b_iA=−x, b_iB=fy−g p_j, b_iC=−g r_j, each h=1+O(M), and D_i Q_it=O(M²). Choose a twin i whose total hazard across both slots is at least M/2. Then p_j+r_j≤M/2, so each of its two residuals is at least (4f−1−g)M/2+O(M²). In particular, at every sufficiently small nonzero nonnegative z, some strictly positive hazard component has strictly positive corresponding residual, uniformly over the allowable factors.

For T≥0 consider G_T(z)=min(z,F(z⁺)−T(0,0,1,1)), componentwise. A root has z≥0 and F−T(0,0,1,1)≥0 and each positive z component has corresponding residual zero after the shift. There are no boundary roots at any T. At x=1 a twin's opponents absorb for sure on A, so D_i=1 and at C the residual is

    F_iC=−(1−k_i)g r_j−(1−r_j)<0.

At y=1 likewise D_i=1 and P=1/2. Choose i with the larger B hazard, at least 1/4. Its opposite p_j≤1/4, hence F_iB=(1−k_i)(f−g p_j)>0 since 4f>1+g. The positive B hazard would require F_iB=0.

The isolated origin has local Brouwer degree +1 for G_0. On a sufficiently small sphere the straight homotopy from G_0 to the identity cannot vanish. If a component of z is negative, that component of the homotopy is negative; if z≥0 is nonzero, the positive component chosen by the preceding expansion stays positive. If G_0 had no other root, excision would give degree +1 on Ω. But for T larger than the maximum of both C residuals on the closure, there is no root, and the degree on Ω is constant along this boundary-free homotopy. This proves existence of a nonzero complementary root, with x,y<1.

For endpoint twin factors equal to 1, approximate them from below. The uniform expansion and strict linear margin keep every nonzero complementary root uniformly away from zero. Compactness of the closure and continuity of (1) and F give a nonzero complementary root in the closure for the limiting factors. The x=1 exclusion holds even at these endpoints. The value y=1 is admissible. In all cases x,y>0, so each player faces a positive-hazard rival each cycle and D_i>0 for every player.

## Quiet comparisons and unrestricted deviations

For either twin, N_iC≥Q_iC=−k_i g r_j yields (1−r_j)N_iA≥(1−k_i)g r_j, hence N_iA≥0≥Q_iA=−k_i x. The complementarity equalities already cover each positive twin hazard. X's quiet B offer k_X(−y+2P)≤0 since y−2P=2RL(1−2P)/(1+2RL)≥0. Its C offer 2k_X R≤2R. Y's quiet C offer −k_Y R≤0≤N_YC. The A offer is 2k_Y x. The C recursion gives N_YA=[R+(1−k_Y)P/L]/H≥(1−k_Y)P, so (2+k_Y P)x≥P. This implies 2(1−k_Y)x≥k_Y P(1−x) because 2(1−2k_Y)+k_Y(1−k_Y)P≥0. Hence N_YA≥2k_Y x as required.

For each player, on every live history always waiting realizes N, immediate quitting earns at most N, and every positive prescribed quit hazard ties N. Unroll the Bellman inequalities through n cycles against arbitrary behavioral replacements, and the equalities for the incumbent. A rival is active with positive probability every cycle, making the residual survival term uniformly geometrically small. Absorption therefore restores each signed s_i exactly in the terminal payoff of every replacement. The same uniform tail bound gives convergence of finite-average to terminal payoffs uniformly over the replacements. For example the discrepancy is at most a common bound on terminal rewards times E[min(τ,n)]/n for absorption date τ; geometric opponent survival bounds this expectation uniformly. This proves the original uniform conclusion for the one incumbent target.

## Comparison with the earlier chart

At f=17/8 and g=9/32 the previous independent-factor square ends at 136/145. Fix k_X=1/10, k_Y=1/2, k_U=99/100 and take any 136/145<k_V<99/100. These points miss both earlier three-date charts. The six-phase solo classification in `DIAMOND_SOLO_AND_JOINT_UNIFORM_EQUILIBRIUM.md` also excludes exact solo equilibrium at positive own levels because k_U>16/17. Its stronger result forces a strictly positive probability of simultaneous first quitting at all sufficiently small terminal regrets. Earlier strict hull-orientation and two-unrestricted-recipient failures at this equal-factor calibration persist for sufficiently close unequal k_V by openness of their strict witnesses. The scope comparison concerns these named prior tests. The earlier `ALL_PROPORTIONAL_ADDITIVE_FOUR_PLAYER_UNIFORM_EQUILIBRIUM.md` takes a negative joining multiplier, whereas the present factors are positive at these data.
