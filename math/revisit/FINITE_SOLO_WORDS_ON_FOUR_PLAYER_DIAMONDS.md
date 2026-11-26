# A finite decision for solo play on signed four-player diamonds

Let the native singleton matrix Γ and the joining matrix J be as in the asymmetric diamond of `DIAMOND_SOLO_AND_JOINT_UNIFORM_EQUILIBRIUM.md`. In particular X→Y→{U,V}→X is its graph of possible changes of solo owner. Both cross-twin singleton entries are strictly negative, all off-diagonal ratios J_ij/Γ_ij lie strictly between zero and one, and all four own singleton rewards are positive. The 32 remaining coalition entries are arbitrary. Define α_m=Γ_Xm/(−Γ_XY), β_m=(−Γ_Ym)/Γ_YX, γ_m=−Γ_mX and δ_m=Γ_mY for each twin m. For twins m,l put

    L_ml=δ_m α_l−γ_m β_l+Γ_ml,      a_ml=L_ml/(γ_m β_m).

Assume only d=min a_ml>0 in addition to these sign conditions. There is a finite test on the two raw matrices for whether the infimum of e+C over all behavioral profiles vanishes, where e is the maximum full unilateral terminal regret and C is the probability of a simultaneous first quit. Success produces an exact periodic solo equilibrium and a fixed original uniform payoff. Failure gives a positive lower bound on e+C. The earlier decision proved this on the subset with d>1 and additional inequalities forcing alternation of the two twins.

## Reduction to the future twin masses

Here are the ingredients inherited from the diamond compactness proof. For any sequence with e+C tending to zero, the four singleton measures in exit-probability time have a subsequential limit adding to Lebesgue measure on [0,1]. The native tail W_i equals the integrated remaining singleton columns in row i and vanishes on the support of i's measure. These statements through the compactness section of the earlier paper hold before imposing its dominance assumption. When W_X=W_Y=0 with positive time remaining, the tail masses of Y and X equal respectively Σα_l T_l and Σβ_l T_l, where T_l denotes the remaining mass of twin l. The remaining masses in the twin rows are Σ L_ml T_l>0. This is the only bound needed in its local structure argument. On neighborhoods with movers in {X,U,V} or {Y,U,V} the core row is monotone and has one interval of zeros, on whose interior only the core owner can move. Away from it there are at most two colors, where a monotone row again separates the runs. The same two-color argument covers {X,Y}. Hence every compact interval before time 1 has finitely many runs. Native quiet comparisons at first physical substeps for Γ_ij<0 and last substeps for Γ_ij>0 imply W_i(start)≥J_ij times the entire run mass, exactly as in the physical-date limit argument of the earlier paper. These inequalities prohibit a final run because its column has a negative entry strictly below the corresponding J. They allow only the graph above at adjacent distinct runs: at a change p→j, W_p vanishes at the switch forcing J_pj≤0, while W_j vanishes there so Γ_jp≥J_jp on the preceding run. Thus there is an infinite tail of triples X_i,Y_i,B_i with B_i∈{U,V}.

Let b_i>0 be the mass of B_i with label m_i, and T_i=(Σ_{j>i:m_j=U}b_j,Σ_{j>i:m_j=V}b_j) its strictly future twin masses. The X and Y owner equations give masses α_(m_i)b_i at Y_i and β_(m_i)b_i at X_(i+1). The zero twin row after B_i now gives b_i=Σ_l a_(m_i,l) T_il. Hence T_(i−1)=M_(m_i) T_i, with

    M_U=[[1+a_UU,a_UV],[0,1]],    M_V=[[1,0],[a_VU,1+a_VV]].

To see the quiet constraint, subtract γ_n/γ_m times the zero row of m at the start of B_i from the quiet row n, where n is the other twin. It gives

    Σ_l C_ml T_il ≥ (J_nm−Γ_nm)b_i,
    C_ml=(δ_n−γ_n δ_m/γ_m)α_l+Γ_nl−(γ_n/γ_m)Γ_ml.

The crucial identity is C_Vl=−(γ_U/γ_V) C_Ul. Put h=T_iU/(T_iU+T_iV), c(h)=C_UU h+C_UV(1−h), and η=d min(J_VU−Γ_VU,(γ_V/γ_U)(J_UV−Γ_UV))>0. A U label requires c(h)≥η and a V label requires c(h)≤−η.

## A finite bound on the word

If c has a constant weak sign on [0,1], at most one twin can occur. If c(0)<0<c(1), the U region lies to the right of the V region. Adding U strictly increases a finite positive ratio T_U/T_V, and adding V strictly decreases it. These weak monotonicities also hold at the axes. Therefore a U cannot immediately precede or follow a V: if the later label is U then its input was in the right region and its output stays there, whereas the earlier V requires the left region, and conversely. Only constant words need be tested in these cases.

It remains to consider c(0)>0>c(1). Neither label can be eventually absent: if all future masses belong to U then c(1)<0 rules out a U, and likewise for V. All tail ratios are finite and positive. Set θ=−C_UV/C_UU. For input R=T_U/T_V, U requires R<θ and V requires R>θ. The output ratio after including the present label is

    U(R)=(1+a_UU)R+a_UV,      V(R)=R/(1+a_VV+a_VU R).

Every output and hence every sufficiently indexed tail ratio lies in [l,u], where

    l=min(a_UV,V(θ))>0,       u=max(U(θ),1/a_VU)<∞.

If l=u one need only test constants. Otherwise in log coordinates the two maps have derivatives bounded on this interval by

    q=max((1+a_UU)u/U(u), (1+a_VV)/(1+a_VV+a_VU l))<1.

In the second term V_log(r)=r−log(1+a_VV+a_VU exp(r)); in the first use U_log(r)=log U(exp(r)). The derivative of c(exp(r)/(1+exp(r))) has absolute value at most H=|C_UU−C_UV|/4. Choose any integer K≥1 with H q^K log(u/l)<2η. If two occurrences have the same next K labels, then the two strictly future ratios at their present dates differ in logarithm by at most q^K log(u/l). Indeed compare the actual tail ratios of the two occurrences after each common letter. These endpoints and the intervals between them lie in the derivative domain. The two scores therefore differ by less than 2η and both occurrences have the same present label.

The chronological sequence of its K-letter windows consequently has at most one predecessor at each visited vertex, ignoring the initial incomplete window. Every recurrent window lies on a directed cycle: take two visits sufficiently far out, and follow the unique predecessors back around the intervening closed walk. All its predecessors on the observed word must lie on the same cycle. Some recurrent window occurs arbitrarily late, so the complete tail is periodic with twin period at most 2^K. This argument concerns the calendar obtained from any low-collision limit; it requires no prior periodicity assumption.

## Executing the test

Enumerate constant words and, in the last case, all binary words of length at most 2^K. For a mixed word m_0,...,m_(p−1), form the product M_(m_0)...M_(m_(p−1)). Both off-diagonal coefficients a_UV,a_VU are positive, so this product has all entries positive and positive determinant. There is a unique positive Perron ray, with eigenvalue λ>1: each step multiplies the total mass of a nonnegative input by at least 1+d. Tested at a periodic label sequence, even a nonperiodic choice of masses has this ray at each period boundary. Indeed the boundary vectors are positive backwards iterates of the product, and a nonzero component in its second eigenspace would eventually dominate under its inverse and force a negative coordinate. For a constant label m the other future mass is zero and λ=1+a_mm, giving the unique positive scalar sequence. In either case set ρ=1/λ and use the ray as the end-of-period vector of future masses. Apply the matrices in reverse chronological order, take each increment in total mass as b_i, and multiply subsequent copies by ρ. Recover the core masses using the α,β equations, including the previous period for the first X mass.

For each phase of this resulting 3p-phase list, compute W as its sum of remaining native singleton columns weighted by the periodic geometric masses. Require W_owner=0 and W_i≥J_(i,owner) times the current phase's mass for each quiet i. There are only four finite geometric sums per phase. Necessity follows from the preceding argument, after discarding any incomplete leading triple. For sufficiency, take hazards equal to each phase's mass divided by all its remaining mass. Every player faces some positive rival hazard per period. At a scheduled date waiting gives its prescribed value, quitting ties it for the owner and gives at most this value for each quiet player. Iteration against an arbitrary unilateral replacement and geometric rival absorption give exact terminal Nash and uniform convergence of finite-average payoffs against all such replacements. This yields a single fixed original uniform payoff. For rational inputs a search for K uses rational upper bounds, e.g. log(u/l)≤u/l; the remaining comparisons use real algebraic numbers of degree at most two.

## A rational nonalternating calibration

Take Γ with rows (0,−1,2,2), (2,0,−1,−1), (−1,3/8,0,−7/48), (−1,1/2,−2/5,0). Set J_ij=9Γ_ij/10 for negative entries and Γ_ij/2 for positive entries. For the nine phases X,Y,U,X,Y,U,X,Y,V take masses (2/3,2,1,1/2,4/3,2/3,1/3,1,1/2) repeated with multiplier 3/8. In chronological order the native vectors W divided by current mass are

    (0,2,1/8,0),    (0,0,3/8,1/3),    (2,0,0,−1/3),
    (0,2,0,2/15),   (0,0,3/8,17/40),  (2,0,0,−3/20),
    (0,2,0,1/2),    (0,0,1/3,1/2),    (2,0,−1/12,0).

All quiet bounds are strict. The leaf matrices have upper row (3/2,5/24) at U and lower row (1/5,2) at V. The U score before normalization is −3T_U/20+19T_V/48; V requires T_U/T_V>95/36. In any alternating word the ratio of future masses at V would be the positive eigenray of M_U M_V, solving 24R²+55R−50=0, which has R<1. Constant words are excluded by the signs of c(0),c(1). Thus the previous six-phase producer fails and nine dates are necessary among exact periodic solo calendars. This is a lower bound on solo timing, with all simultaneous-move strategies included when defining the unrestricted quantity e+C.
