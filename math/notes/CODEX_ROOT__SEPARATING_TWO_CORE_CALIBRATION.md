# A joint calendar outside the earlier singleton, two-recipient and orientation tests

Use row order X,Y,U,V and own singleton levels 1. Fix

    Γ = [ 0  −1   1     1   ]
        [ 1   0  −1    −1   ]
        [−1   2   0    −3/4 ]
        [ 2  −1  −2     0   ].

At the baseline, passive native rewards are additive except that Z_X({Y,V})=−1; every participant's native reward is zero. For t>0 change X's seven nonsingleton joining entries to Q_X(T)=t P_X(T), and set J_YX=J_VY=t. No other entry changes. For all sufficiently small t>0 these games and a full-dimensional open set of nearby games have a three-date exact original terminal equilibrium, no stationary terminal equilibrium and no sure head. Every sufficiently accurate terminal equilibrium requires a simultaneous first exit with probability bounded below. The conclusions refer to all unilateral behavioral replacements. They also fail all the particular former tests verified below.

In the two-core theorem take σ=−1, b=d=(1,1), e=(−1,2), f=(2,−1), and h=(−3/4,−2). Use k_X=t and k=1/2. The X passive UV entry is 2, and Y's three passive entries on U,V,UV are −1,−1,−2. The corresponding Y joining entries are zero and J_YX=t<1/2. In each twin row J_iX=J_ij=0, with Γ_ij<0. The determinant of Γ is 5/4. Its reduced matrix L=[[1,1/4],[−1,1]] is R0 by its nonzero principal determinants, and at target (1,1) it has only the regular full-support root (3/5,8/5) of positive index. A nonzero homogeneous Γ solution would require X>0 by the Y and X rows, and m≠0 by the U row, so Y=b·m>0, leaving a nonzero homogeneous L solution, impossible. The core degree computation therefore gives Γ degree one. The three-date assertion of the new theorem applies. The two mutually negative pairs YV,UV and the mutually positive pair XV distinguish this singleton graph from the strict diamond under every permutation.

**Singleton paths and actual collisions.** The four triple principal determinants are 1, 1, 1/2, 13/4 in lexicographic order. Each column has a negative entry. A continuous singleton path would have to use a constant complementary direction or a directed triangle or quadrilateral, by ALL_FOUR_PLAYER_SINGLETON_PATHS_HAVE_A_FINITE_TEST.md. R0 excludes the constant direction. The only allowed arcs are X→Y, Y→U and U→X, so the only candidate is XYU. Its owner equations force masses (2,1,1) and period survival 1/2, up to common scaling. V's unnormalized opening tail is 2 at X and −2 at Y. The negative tail excludes the path. At t=0 all pair joining entries are zero, supplying the raw row protection in GENERIC_FOUR_PLAYER_SINGLETON_PATH_CLASSIFICATION.md. Consequently the infimum of full terminal regret plus probability of a simultaneous first exit is strictly positive. Each fixed profile's regret changes by at most twice the maximum reward perturbation, and its collision probability is unchanged. This proves the same strict floor throughout a neighborhood.

**Stationary and sure alternatives.** For baseline hazards q=(x,y,u,v), the passive contributions are

    P=(−y+u+v−yv(1−u), x−u−v, −x+2y−3v/4, 2x−y−2u),   Q=0.

There is no nonzero closed-box point where q_i>0 implies P_i≤0 and q_i<1 implies P_i≥0. The following exact rational quantifier-free real algebra check exhausts all 80 supports and boundary types. It requires Python and z3-solver.

    import itertools
    import z3
    x,y,u,v = q = z3.Reals("x y u v")
    P = (-y+u+v-y*v*(1-u), x-u-v, -x+2*y-3*v/4, 2*x-y-2*u)
    for status in itertools.product((0,1,2), repeat=4):
        if not any(status):
            continue
        solver = z3.SolverFor("QF_NRA")
        for z, b, k in zip(q, P, status):
            if k == 0:
                solver.add(z == 0, b >= 0)
            elif k == 1:
                solver.add(0 < z, z < 1, b == 0)
            else:
                solver.add(z == 1, b <= 0)
        assert solver.check() == z3.unsat, status

With two or more positive stationary hazards the necessary box comparisons use P−(1−H)Q, H denoting each row's rival survival. The same comparisons are necessary with one positive hazard: the sole owner's P and Q both vanish and every other player faces eventual rival absorption. The all-Never profile fails at a positive own level. For any sure head the outsiders' forced actions use P−Q; should a sole sure owner withdraw, it can guarantee its own level in the baseline by immediately quitting next period. Thus all the baseline sure-head comparisons also imply the excluded box conditions. Both exclusions persist under small raw perturbations. For the stationary comparisons compactness suffices away from q=0, while near zero R0 gives a homogeneous positive unit-sphere lower bound for the minimum map and the stationary residual has uniform quadratic remainder after its singleton linear part. At a limiting sure head some component is one; if it is unique, its original upper punishment value differs from the baseline value by at most the supremum reward perturbation because the full terminal payoff of every fixed strategy pair has this bound. If multiple components tend to one, the withdrawal survival in each sure row tends to zero. One therefore obtains the excluded baseline box conditions on taking the limit.

**Two recipient rows.** In TWO_UNRESTRICTED_RECIPIENTS_UNIFORM_EQUILIBRIUM.md the designated row a must have J_aj≥Γ_aj on both free singleton opponents. At the baseline the only assignments (a,b;h,k) up to swapping the free owners are (Y,X;U,V), (U,Y;X,V), (V,X;Y,U). For e=b the following list gives the two free hazards on its scheduled date, then the two free hazards and the other scheduled hazard on its passive date:

    (0,1/4 ; 0,0,1/4),   (1/4,0 ; 0,0,1/4),   (0,1/4 ; 1/4,0,0).

Each gives A_e=H_o(P_p+H_p Q_o)−Q_o+P_o=1/16 and B_e=P_p+H_p P_o−(1−H_oH_p)Q_p=−1/16. Thus every assignment fails, and all three failures and the exclusions of other assignments are strict. The separate one-recipient criterion fails in each row on a positive-supplier singleton axis with J below Γ, taking suppliers U,X,Y,X for X,Y,U,V respectively. These strict comparisons persist for small perturbations.

**Orientation tests.** On the support (X,Y,V) take odds (s,s,2s) with s>0 approaching zero. For fixed small t>0 each active forced-Quit numerator equals ts+O(s²); hence Low fails. The singleton Charge coefficient at T=X is J_YX+J_VX=t>0. At zero the joining-gain Jacobian on this support has rows (0,1−t,t−1), (t−1,0,1), (−2,1+t,0), with determinant (t−1)(1+t²)<0. The signed determinant is strictly positive, which violates the support orientation even for small strictly positive odds. These three witnesses exclude the complete supportwise Low/Charge/Orientation test.

The X joining-gain coordinate Φ_X has linear term (t−1)s<0. The four singleton columns projected onto (X,Y,V) have rank three and have zero as a strictly positive combination after normalization, since Γ^(-1)e_U=(8/5,8/5,4/5,4/5)>0. Their convex hull therefore contains an open neighborhood of zero in this projection. For arbitrarily small positive s the wrong-sign Φ lies in the projected closed game-payoff hull, with a negative X coordinate in any lift. Every first-action tube also contains a full neighborhood of zero, since the zero-hazard profile certifies zero in N1. This violates both domains' weak orientation tests in PAYOFF_DOMAIN_ORIENTATION_UNIFORM_EQUILIBRIUM.md. The positive joining entry J_YX also violates the classical capped-joint hypothesis. These comparisons address the named criteria, without asserting a census of all possible proofs of existence.

Finally, for small fixed t>0 lower all seven X joining entries slightly below tP_X(T), lower the three Y joining entries on nonempty T⊆UV slightly below zero, and lower both J_iX in the twins slightly below zero. All the new raw inequalities now hold strictly with the same k_X,k. The signs, collision floor, extremum exclusions and strict witnesses above persist; for the orientation tests the three linear coefficients of the forced offers on the chosen odds ray stay positive, the X coefficient of Φ stays negative and the zero-odds determinant stays negative. The projected singleton hull retains the interior property under perturbations. Hence an open set of all sixty reward coordinates has all these properties simultaneously.
