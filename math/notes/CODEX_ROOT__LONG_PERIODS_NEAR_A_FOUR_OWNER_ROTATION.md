# Repeated four-owner rotations at the boundary for simultaneous quitting

Label four private stopping laws modulo four. Perpetual play pays zero. On a nonempty first coalition S subtract the recipient's own singleton reward s_i to obtain centered rewards Z_i(S). Let G_{ij}=Z_i({j}) and J_{ij}=Z_i({i,j}). Put G_{j+2,j}=3 and G_{j±1,j}=−1. Take J_{j−1,j}=−0.9 and J_{j+1,j}=−1.1 throughout. Write T_i for i's passive reward on the matched pair not containing i. Take all four J_{j+2,j}=x_*=(3+√5)/2 initially; the other 28 independent centered reward entries at size at least two are arbitrary and finite. For strict incidence conclusions assume at least one s_i>0, and otherwise allow every signed level for existence. Write ρ=(3−√5)/2, h=1−ρ and a=ρ². At this critical table, in the repeated orientation 0,1,2,3, only the named incumbent acts in each phase, with hazard h. Its centered continuation V^k before phase k has coordinates (0,−h,(1+√5)/2,0) in cyclic order starting at k. Indeed V^k=hG_{·k}+ρV^{k+1}. The mate's offer equals its value and both crossed owners strictly prefer to wait.

**Period separation.** For each integer K≥2 there is a passive choice T=(1,0,1,t) with t>0 for which every sufficiently small perturbation of all the original reward entries admits an exact absorbing equilibrium with a calendar of period P=4K, at arbitrary signed row levels. For a direction perturbing the four matched entries by εℓ, ℓ=(−1,−1,+1,−1), ε>0 small, these equilibria have probability O(ε) of a simultaneous first exit. There exist c,δ>0 such that on this direction for 0<ε<δ each calendar with period strictly below P has either simultaneous first-exit probability ≥c or maximum original terminal regret ≥cε². The separation assumes some s_i>0. Its constants may depend on K, all fixed data and the signed levels. One can prescribe which of the K visits by owner 0 is the unique joint date in each successive block of P dates, independently in every block. Every resulting word is realized on the same game for all sufficiently small ε, including aperiodic words. The separation concerns calendars with small total collision probability. A different shorter exact calendar could have macroscopic simultaneous quitting.

## Linear response on a repeated rotation

Reduce the 4K phases modulo P, allowing an incumbent hazard t_j near h and a mate entrant hazard u_j near 0 at each visit j. Write v^j for its analytically continued exact periodic prescribed values from date j; bounded nonunit full period survival solves the affine recursion. The incumbent's Wait-Quit advantage is (1−u_j)v^{j+1}_j+u_j(3−J_{j,j+2}) in centered units at the specified singleton matrix; indices of reward recipients are read modulo four. Its mate's Wait-Quit advantage is (1−t_j)v^{j+1}_{j+2}+t_j(3−J_{j+2,j}). Use the corresponding actual expressions at nearby tables. At an incumbent indifference v_j^j is its Quit payoff. Differentiate at the critical table in the entrant hazards. Write p_j=dt_j, n_j=du_j and let g_i^j=dv_i^j. With S the shift (Sf)_j=f_{j+1}, the single-stage linearized recursion is

    g_i^j=ρg_i^{j+1}+(G_ij−V_i^{j+1})p_j+R_i^j n_j,
    R_i^j=ρG_i,j+2+hZ_i({j,j+2})−V_i^j.

In recipients j,j+1,j+2,j+3 the four R entries are r0=3ρ+(1+√5)/2, r1_j=h−ρ+hT_{j+1}, 0, r3_j=−ρ+hT_{j−1}. Expanding from date j through its next same-incumbent date j+4, the incumbent indifferences g_j^j=x_* n_j give

    [S(1−ρS)(1−aS)p]_j
       = a n_j + ρ r3_{j+1}n_{j+1} + ρ³ r1_{j+3}n_{j+3} + ρ⁴ x_* n_{j+4}.

For n=0 these implications show that the linearized incumbent contacts have trivial kernel on p, since S,1−ρS,1−aS are invertible on P-periodic vectors. Their square Jacobian is therefore invertible. Near each fixed critical table the implicit function theorem eliminates all P incumbents for every small signed vector of entrants and small reward perturbation. For the remaining mate advantages the differential at the critical center is F_j=ρg_{j+2}^{j+1}+p_j. Substitute the one-step update and the incumbent contact g_{j+2}^{j+2}=x_* n_{j+2} to get F_j=[(1−ρ S)p]_j+ρ r1_{j+1}n_{j+1}+a x_* n_{j+2}. The preceding recurrence then cancels the two further shifts and gives the tridiagonal-with-one-extra-shift formula

    F_j−aF_{j+1}=a n_{j−1}+b_j n_j+c_{j+1} n_{j+1}+ρ n_{j+2},
    b_j=−a+ρhT_{j−1},  c_j=ρ(h−ρ)+ρhT_{j+1}.

Denote this periodic linear map by H_P. For one impulse in phase j set d_j=b_j+a² and C_j=ρ+a c_j+a²d_j. On the integer line its bounded response, obtained by summing the future right sides with successive powers of a, has entries a at j+1, d_j at j, c_j+a d_j at j−1, and a^v C_j at j−2−v, v≥0. It vanishes after j+1. The P-periodic response sums all period translates. For nonnegative T, c_j+a d_j is strictly positive even at zero T (it equals ρ(h−ρ)+a(−a+a²)>0 there), hence all off-diagonal entries of H_P are positive. In particular

    (H_P)_{jj}=d_j+a^{P−2}C_j/(1−a^P).

For each j this diagonal decreases strictly with P on multiples of four. Summing columns over every periodic copy of one phase in any fixed row gives the corresponding entry of H_4 by periodicity and uniqueness of the shift solution. Changing the matched joining reward on each phase by εℓ_j changes the mate advantage at u=0 by precisely −hεℓ_j, because the old incumbent-only row contains no joint exits and its incumbent contacts remain unchanged.

## A computable passive family at each period

Fix T_0=T_2=1, T_1=0, T_3=t. At 0≤t≤1 the diagonals for phases 1 and 3 are positive at every period since their infinite-line d is −a+a²+ρh>0. For phase 2, d_2=−a+a² and all the corresponding finite-period diagonals are negative, since at P=4 already d_2+a²C_2/(1−a⁴)<0 for t≤1. For phase 0, at t=0 its diagonal is likewise negative and at t=1 its infinite-line d is positive. Its P-diagonal is strictly increasing affine in t. Thus there is a unique t_P∈(0,1) where (H_P)_{00}=0. The t_P increase strictly with P. Choose t just below t_{4K} and above t_{4K−4}. At period 4K all K copies of phase 0 have tiny negative diagonal. The four-period diagonal for phase 2 is uniformly negative, and every off-diagonal at the limiting t_{4K} is strictly positive. Choose t sufficiently close to t_{4K} that for each pair of negative-diagonal indices i≠j containing a phase-0 copy, (H_P)_{ij}(H_P)_{ji}>(H_P)_{ii}(H_P)_{jj}. This gives a nonempty open interval in t by finitely many strict tests. All resulting strict conditions also hold under small independent changes of the four T entries.

Let A be the K copies of phase 2 and B the K copies of phase 0. The principal matrix H_{AA} has constant negative row sum (H_4)_{22}. It is strictly diagonally dominant with negative diagonal and positive off-diagonals. Every nonempty principal submatrix H_D for D⊂A has det sign (−1)^|D| (scale the off-diagonals to zero) and −H_D has a nonnegative inverse with positive diagonal by a convergent geometric series. For the normal map N(y)=H_P y_++y_- on ℝ^P, a nonzero root would give a nonempty positive support D of z=y_+ on which (H_Pz)_D=0. No positive-diagonal index can occur, since all off-diagonals are positive. If D contains a B index and a second index, multiplying the two active row inequalities contradicts their strict pair inequality. A B singleton has nonzero diagonal. Supports in A are nonsingular. Thus N has no nonzero root and min_{|y|=1}|N(y)|>0.

For target −τ1 with τ>0 the exact same two-row observation excludes any nonsingleton support meeting B, as well as positive diagonals. Each D⊂A gives exactly one interior preimage by solving H_D z_D=−τ1; all remaining y coordinates equal −τ−(H_P z)_i<0. Each B singleton likewise gives one preimage of sign −1. All are regular and each lies close to zero for small τ. The local Brouwer degree is

    Σ_{D⊂A}(−1)^|D| − |B| = −K.

Let F_R(u) denote the genuine mate advantages after eliminating incumbents at the original reward table R. On a small sphere the continued map F_R(y_+)+y_- remains free of zeros and homotopic to N at the critical center and all sufficiently small perturbations. Its nonzero degree gives a zero, u=y_+≥0 and F_R(u)≥0 complementary. Every named incumbent remains strictly mixed; all quiet crossed inequalities stay strict. Every player faces a rival who almost surely quits geometrically, also after any unilateral change of stopping law. Iterating the physical comparisons bounds all deadlines and Never, and finite-average payoffs converge uniformly over unilateral deviations. Thus the resulting independent P-periodic profile is an exact terminal equilibrium and gives the fixed-target uniform equilibrium under all signed row levels. By coercivity of N and the O(|u|²+ε) Taylor error for a table at distance ε, each local solution satisfies |u|=O(ε), hence has total first-exit collision probability O(ε).

## Exclusion of shorter periods in the stated direction

Here are direct details of the rigidity needed for bounded periods. On every approximating law with original regret e, a positive s_i bounds the prescribed joint Never mass by e/s_i: moving a player's individual Never mass to an increasingly late finite deadline wins s_i precisely on joint Never in the limit. Each centered regret is at most its original regret plus |s_i| times joint Never, by centering finite deadlines (literal native Never is their late limit). In particular centered regrets tend to zero. Conditional centered regret at a reached cut is at most the initial centered regret divided by its joint reach, by changing play only after the cut.

Fix a period P′ and take subsequential limits of its arrays along vanishing regret, collision probability and perturbation. If every phase hazard tends to zero, pass to a subsequence of nonblank periods and normalize all hazards in one period by their total to obtain limiting owner masses y∈Δ. The prescribed centered payoff tends to Gy: in one period the multiple-exit and earlier-exit overlap errors are O(total²), and the period then repeats geometrically. Immediate Quit gives Gy≥0. At any i with 0<y_i<1, literal Never has limiting native payoff (Gy)_i/(1−y_i), by applying the same calculation to its rival period; hence (Gy)_i=0. At y_i=1 this equality holds by the zero diagonal. But G⁻¹ has diagonal 2/15, crossed entries 1/5 and matched entries 7/15, so Gy≥0 with y nonzero gives y strictly positive. It would then give Gy=0, impossible. Blank periods with certainty of Never already fail the original regret bound. Thus at least one limiting hazard is positive.

At each date with positive limiting reach at most one owner can have positive hazard, by the vanishing collision bound. No date can have a first limiting sure owner j: its quiet predecessor receives G_{j−1,j}=−1 when following the prescription but J_{j−1,j}=−0.9 by immediate Quit. Thus the full fixed period has positive limiting reach throughout, proper hazards, and product survival strictly below one. Consequently the prescribed payoffs converge at each cut to the literal limiting centered periodic payoffs w, which have coordinate sum one by singleton absorption. One-action deviations followed by the prescription give the actual stage comparisons at each cut. If a sole owner j acts with hazard q>0, its value and its child value are zero by indifference, and quiet i has w_i≥qJ_ij. Put E(w)=wᵀG⁻¹w. The recursion w=qG_{·j}+(1−q)v gives E(w)=(1−q)²E(v) since G_jj=v_j=0; this also holds at blanks. Iterating through a whole period gives E(w)=0 at every date. A nonnegative w of sum one would give wᵀG⁻¹w>0, so at least one coordinate is strictly negative everywhere. A blank date would allow immediate Quit at zero to this owner and is impossible.

The periodic calendar cannot use just one owner j: following quietly against that owner gives its predecessor −1 and joining gives −0.9q>−1. At a switch p→j both coordinates vanish. They cannot be mates by the positive matched joining payoff. The mate of j has positive value by its immediate offer; the remaining owner k has negative value. Writing these last two coordinates U,V gives U+V=1 and U²+3UV+V²=0 by the displayed inverse, so U=(1+√5)/2 and V=−h. No switch can next return to p, since the p coordinate would be zero at both ends of a positive j run with G_pj=−1. Hence one of the two crossed cyclic orders occurs. The aggregate hazard of a full j run is H=h since its beginning and ending p values are 0 and (1+√5)/2. The next owner k's beginning value −H and first hazard at most H force J_kj≤−1. This excludes the reverse orientation. At the last date of the run with hazard q, the mate is offered q x_* and its prescribed value is 3q−(1−q)h. Thus x_*≤3+h−h/q; since x_*=2+h and q≤h, equality forces q=h=H. The entire run consists of that one date. Any physical period P′ of this limiting calendar is a multiple of four, and its positive hazards are exactly the repeated golden rotation, up to initial phase.

Suppose by contradiction that ε→0 along the asserted adverse direction has some fixed P′<P with simultaneous exits tending to zero and regret e=o(ε²). After extraction and rotation the limiting calendar must be the just-described golden orbit and P′=4m, m<K. At every phase in that bounded period survival up to the phase is bounded below. The two crossed waiters have strict baseline waiting margins in the actual continued table, so their hazards are O(e) by testing the better action once at that phase and then following the prescribed strategy. Similarly the incumbent hazards stay in a compact subinterval of (0,1); the same two-action comparisons bound their signed indifference residuals by O(e). Removing the crossed hazards changes all payoffs and incentives by O(e) uniformly because the periodic laws have bounded period and uniformly geometrically absorbing rivals. Thus their incumbent coordinates equal the IFT solution plus O(e). For entrants u≥0 tending to zero, F_R(u)≥−O(e) and u_jF_R(u)_j≤O(e) for each phase, by the same stagewise comparisons. Write

    F_R(u)=H_{P′}u−hεℓ+O(|u|²+ε|u|).

Divide by max(ε,|u|), take a convergent subsequence, and divide each contact product by max(ε,|u|)². On P′ all phases apart from A′={phase 2 copies} have strictly positive diagonal. H_{A′A′} has strictly negative row sums and strictly dominates its positive off-diagonals as above. Its normal map has no nonzero root: only an A′ support could be orthogonal to its own H image, and every such principal submatrix is nonsingular. Therefore the case ε/|u|→0 is impossible. Passing to a further subsequence yields z=lim u/ε≥0 with H_{P′}z−hℓ≥0 complementary. Every non-A′ owner has ℓ_i=−1, strictly positive diagonal and all off-diagonals positive, hence cannot enter. The A′ block now requires H_{A′A′} z_{A′}≥h1, impossible since multiplication by the nonnegative inverse of −H_{A′A′} gives z_{A′}<0. This rules out every such sequence and gives the constants c,δ in the statement by the finite number of shorter periods. This is an obstruction to uniformly accurate collision-sparse shorter calendars at a boundary family; it is not a lower bound on regret over all profiles.

## Prescribing the unique joint date in each block

It suffices to use finite periodic placement words with uniform estimates and then take limits. Define d=d₀<0, D=−d, C=C₀>0, β=a²C and r=a⁴ (the stage index hereafter is the phase-0 visit number k). Only phase-0 visits may have entrants. In the first-order normalized equations let z_k be that entrant hazard divided by ε and W_k=Σ_{j≥0}r^j z_{k+j}, extending a finite word periodically. The impulse filter gives, at a phase-0 visit k, the linear response dz_k+βW_{k+1}, and at its following phase 2 the response CW_{k+1}. At phases 1 and 3 the response is nonnegative whenever z≥0. The matched perturbation contributes +h at all phases except 2, where it contributes −h. On a marked visit the phase-0 contact requires

    z_k=(h+βW_{k+1})/D,     W_k=h/D+(r+β/D)W_{k+1}.

At an unmarked visit z_k=0 and W_k=rW_{k+1}. Its own phase-0 guard is at least h. Within each block exactly one update contains a constant term; for a marked position b=0,…,K−1 the composed affine update on W has constant r^b h/D and the same slope

    Λ=r^{K−1}(r+β/D).

The identity d+a^{4K−2}C/(1−a^{4K})=0 is precisely Λ=1. For t<t_{4K} sufficiently close, d<0, Λ<1 and Λ→1 as t increases to t_{4K}, with finite positive limiting D. Hence the block-end equations have unique bounded nonnegative solutions, uniformly between r^{K−1}h/[D(1−Λ)] and h/[D(1−Λ)]. At any visit W_k is bounded below by r^K times the lower bound since every multiplier is ≥r. Thus the open choice of t in the degree argument can be narrowed so that CW_k>2h at every visit, uniformly in all placements. The strict limits in the period-separation construction can be imposed simultaneously. All phase-2 quiet guards then have slack at least h, the phases 1 and 3 have slack at least h, and z_k≥h/D on marked visits. The W and z have uniform finite upper bounds at this fixed t.

For completeness the two implicit-function steps and their uniformity across periods are as follows. All norms are sup norms. Near the base hazards the prescribed-payoff recursion has a unique bounded periodic solution, with its first two derivatives bounded independently of the period. Indeed each row update is a polynomial in its own hazards and raw rewards with uniformly bounded derivatives, and the shift times the continuation multiplier has norm <c<1 uniformly on a fixed real neighborhood of the base. Its inverse is a Neumann series. Let I_j be the derivative of the incumbent Wait-minus-Quit residual under a perturbation p of the incumbent hazards only. At n=0 the payoff derivative satisfies g_j^j=ρ I_j. Expanding the four-date recursion above at consecutive visits to the same owner, now retaining the arbitrary residual, gives

    S(1−ρS)(1−aS)p=−ρ(1−ρ⁴S⁴)I.

The shift S and all the displayed resolvents have uniformly bounded inverses on every periodic space. The full incumbent Jacobian and its inverse are uniformly bounded. The quantitative IFT eliminates the incumbents on one common neighborhood of u=0 and the base table for all lengths. The reduced true mate map F thus has uniformly bounded first two derivatives there.

For the marked contact submatrix, an arbitrary forcing f imposes dz_k+βW_{k+1}=f_k on the marked visits. Off them z_k=0. This gives W_k=−f_k/D+(r+β/D)W_{k+1} on marked visits, and the old homogeneous updates elsewhere. Taking a whole block gives the same slope Λ and a constant of modulus at most ||f||∞/D. Therefore the inverse on the retained contacts has sup norm bounded independently of period: the W at block endpoints have norm ≤||f||∞/[D(1−Λ)], the K inner steps uniformly bound the W there, and z_k=W_k−rW_{k+1}. Uniqueness follows from Λ<1. Set u=0 on inactive phases and solve F=0 on the marked ones. The same quantitative IFT gives, uniformly across periods, u_k=ε z_k+O(ε²) on the ray. For instance apply the contraction x↦x−L⁻¹F(x) at the origin with the common bounds on the inverse of L and the Lipschitz constant of the derivative. The reduced derivative and the first-order forcing are exactly the filter and −hℓ above. The strict first-order signs persist for a common interval 0<ε<ε₀. Payoffs, contact solutions and inequalities are uniformly Lipschitz in the original reward inputs, so at each such ray table the signs persist under all raw perturbations of norm less than a sufficiently small multiple of ε. The crossed guards have strict zeroth-order slack.

For any infinite word, repeat its first m blocks, choose the corresponding finite-period solutions and extract a coordinatewise subsequence on natural dates. Every forced date retains its prescribed active set, by the just-established common strict bounds, including the positive lower bound on marked entrant hazards. Each four incumbent visits contain a different proper mixer with hazard uniformly bounded away from zero, under every unilateral replacement. Thus continuation payoffs converge by uniform tail truncation, and one-stage Nash inequalities pass to the limit. Iteration with the same tail bound proves genuine full-law terminal and uniform incentives. All compilers use independent stopping laws. For finite periodic words use the solution on that period rather than a diagonal limit.

In particular choose a word of m blocks with offset zero in every block except one, where the offset is one, and repeat. For m≥2 there is a unique gap of K+1 rotations among the marked gaps in each m blocks. Thus the least joint-incidence period is 4Km dates. The constructed periodic profile has this same least period. A constant offset gives exactly one joint date per 4K and an entrant of order ε; the uniform positive reach to that date and geometrical absorption give total simultaneous first-exit probability of order ε.


## Exact calibration and formalization boundary

For K=2 take t=52784790177/10¹¹. The following exact SymPy calculation verifies the signs at P=4 and 8 and the uniform phase-2 waiting bound in the placement construction. The final inequality is C₀r³>2D(1−Λ).

```python
from sympy import QQ, sqrt

K = QQ.algebraic_field(sqrt(5))
def pos(x):
    q = x.to_list()
    if len(q) < 2:
        return bool(q and q[0] > 0)
    b, a = q                 # x = a + b sqrt(5)
    return (a > 0 and (b >= 0 or a*a > 5*b*b)) or (b > 0 and (a >= 0 or 5*b*b > a*a))

rho = (3-K.from_sympy(sqrt(5)))/2
h, a = 1-rho, rho**2
T = [1, 0, 1, QQ(52784790177,10**11)]
d = [-a+a*a+rho*h*T[(j-1)%4] for j in range(4)]
c = [rho*(h-rho)+rho*h*T[(j+1)%4] for j in range(4)]
C = [rho+a*c[j]+a*a*d[j] for j in range(4)]
def H(p,i,j):
    k = j % 4
    m = (j-i-2) % p
    return (a**m*C[k]/(1-a**p) + a*(i==(j+1)%p)
            + d[k]*(i==j) + (c[k]+a*d[k])*(i==(j-1)%p))

for p, negative in [(4,{2}),(8,{0,2,4,6})]:
    assert all(pos((-1 if i in negative else 1)*H(p,i,i)) for i in range(p))
    assert all(pos(H(p,i,j)) for i in range(p) for j in range(p) if i!=j)
    for i in negative:
        for j in negative:
            if i!=j and (i%4==0 or j%4==0):
                assert pos(H(p,i,j)*H(p,j,i)-H(p,i,i)*H(p,j,j))
r, D = a**4, -d[0]
slope = r*(r+a*a*C[0]/D)
assert pos(1-slope) and pos(C[0]*r**3-2*D*(1-slope))
```

The four-period entrant degree at the center with all passive matched rewards zero was previously calculated as −3. Here the four-period degree is zero, the 4K-period degree is −K, and one perturbation forces a quantitative choice between short-calendar regret and collision probability. The arbitrary 28 unused centered entries may in particular include large positive payoffs for the four crossed players who join a matched coalition. No upper bound on these four values is uniform in the neighborhood size. The other 24 entries at size at least two never occur under these profiles or any one-date deviation. The construction leaves general singleton matrices and games away from these neighborhoods open.

For a formalization, use the actual terminal value and rival survival bounds to build a period-4K certificate for `isUniformEquilibriumPayoff_quittingCyclicTerminalValue_of_certificate` in `UniformEquilibrium/Quitting/Cycles/PeriodicCompiler.lean`. The missing analytic production steps are the finite cyclic derivative formula, the orthant-degree argument with the stated strict minors, and the reconstruction of nonnegative private hazards. The shorter-calendar rigidity uses the centered quadratic identity and original regret-to-reach estimates separately. For the aperiodic realization one can instead take limits along the common four-date rival-survival bound and iterate the Bellman inequalities. These analytic results have not been checked in Lean.
