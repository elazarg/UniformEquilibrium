# A three-date equilibrium retaining both core best-response equations

Use independent private behavioral strategies, arbitrary signed rewards on the fifteen nonempty absorbing coalitions, and zero live and Never payoffs. Choose players X,Y,U,V, the last two called twins. After subtracting each original own singleton payoff on all nonempty exits and positively scaling Y, write P_i(T) and Q_i(T) for its native payoffs when a nonempty rival subset T quits without or with i. Both are zero at empty T; use the same symbols for their independent product averages. Γ_ij=P_i({j}), Γ_ii=0, J_ij=Q_i({j}). Require:

* Γ_YX=1 and Γ_Yj=−d_j<0 for each twin j. The X singleton row is unrestricted.
* For every nonempty twin subset T require P_Y(T)<0, kP_Y(T)≤Q_Y(T) for a common 0≤k<1, and J_YX≤1−k. Write E(z)=−P_Y(z), K(z)=−Q_Y(z), H(z)=(1−z_U)(1−z_V) for twin hazards only. Define the compact regions B={z∈[0,1]²:E(z)−K(z)≤H(z)} and C={z∈[0,1]²:E(z)≤H(z)}.
* For each twin i with opposite twin j put h_i=Γ_ij and c_i=max(0,h_i−J_ij)/d_j. Require J_iX≤−c_i. Its remaining entries are unrestricted.
* On C require Q_Y(r)≤0 and Q_X(r)≤P_X(r). Put m=min_(r∈C)P_X(r). For nonnegative odds on Y,U,V let L_S=Σ_(∅≠T⊆{Y,U,V}) S_X(T) ∏_(j∈T)z_j for S=P,Q. Require L_Q>0 ⇒ L_P>−m at all such odds whose two twin hazard probabilities belong to B.

**Theorem.** These raw tests imply the existence of a fixed original uniform-equilibrium payoff. If the singleton matrix is R₀ with nonzero minimum-map degree, the proof gives one exact terminal Nash calendar repeating three dates. No requirements on the twin values of Γ_iX or the sign of h_i enter. The previous four-variable weight condition, including its condition on the relative magnitudes of the singleton rewards, is removed. The two curved regions price simultaneous payoffs only where the corresponding dates can occur.

The two tests on C each admit an elementary explicit form. For the first put b_i=−Q_Y({i}), s=Q_Y({U,V}); for the second put b_i=P_X({i})−Q_X({i}), s=Q_X({U,V})−P_X({U,V}). Set D=−P_Y({U,V})>0. In each case the condition is b_i≥0 and
```
s ≤ b_U d_V+b_V d_U+2√(b_U b_V(d_Ud_V+D)).
```
Indeed C has odds (u,v) satisfying d_Uu+d_Vv+Duv≤1, and the required inequality is s uv≤b_Uu+b_Vv. The axes force b_i≥0. Minimize b_U/v+b_V/u over positive feasible odds. On the upper hyperbola use t=1/v−d_V>0 to obtain b_Ud_V+b_Vd_U+b_Ut+b_V(d_Ud_V+D)/t. Taking its infimum gives the stated formula, also for zero b_i. The test for B is a polynomial implication in three nonnegative variables with a bounded twin range whenever needed.

## All six scheduled comparisons

Use hazards A=(x,0,0,0), B=(0,y,p_U,p_V), C=(0,0,r_U,r_V), cyclically. All six entries range over [0,1]. For a player let b_t,h_t,Q_t be the native Wait exit contribution, rival survival and forced-Quit offer on date t. At a scheduled slot its scaled Never-minus-Quit comparison is
```
F_t=b_t+h_t b_next+h_t h_next b_last−(1−h_Ah_Bh_C)Q_t .
```
With positive opponent absorption per period this is (1−h_Ah_Bh_C)(N_t−Q_t) for the native always-wait value N_t. The displayed polynomial is defined regardless. Put H_p=∏(1−p_i), H_r=∏(1−r_i), E(z)=−P_Y(z), K(z)=−Q_Y(z) against twin hazards z. E(z)>0 for z≠0 and K≤kE. In the core slots the same formula reads
```
G=F_XA=P_X(y,p)+(1−y)H_p P_X(r),
F_YB=−[E(p)−K(p)]−H_p E(r)+H_pH_r[x−(1−x)K(p)].
```
Use min(x,G), min(y,F_YB), and min(p_i,F_iB),min(r_i,F_iC) for both twins. On the closed padded cube [−1,1]⁶ keep each first argument unaltered and evaluate all payoffs at positive parts. Near zero the six residuals equal the duplicated singleton matrix applied to the nonnegative input plus O(norm²): the linear rows are ay+g·(p+r), x−d·(p+r), and two copies per twin of e_i x+f_i y+h_i(p_j+r_j), where a=Γ_XY, g_j=Γ_Xj, e_i=Γ_iX, f_i=Γ_iY, h_i=Γ_ij. The duplicated homogeneous minimum map is R₀ by adding each twin's slots. Its degree equals that of Γ by assigning each twin a generic target in one slot and a target one unit lower in the other: only its higher-target slot can be active, the lower slot is strictly slack, and all regular principal determinants agree. Homotoping the linear input to its positive parts preserves the isolated zero, since a negative coordinate cannot solve the minimum equation. On a small sphere the quadratic remainder preserves this nonzero local degree.

Throughout subtract t≥0 from both C-slot twin residuals. Every root has F_YB≥0. If H_p=0 then E(p)−K(p)>0 and F_YB<0. If H_r=0 and H_p>0, then H_p E(r)>0 gives the same contradiction. Thus all twin hazards are proper. For p+r≠0, F_YB at x=0 is strictly negative, since it equals −E(p)+(1−H_pH_r)K(p)−H_p E(r). Being affine in x, a feasible F_YB therefore has F_YB(1)≥0, which yields E(p)−K(p)≤H_p and E(r)≤H_r. Consequently p∈B,r∈C. In addition F_YB≥0 implies
```
H_pH_r[x−(1−x)K(p)] ≥ E(p)−K(p)+H_p E(r).
```
By the strict sign at x=0, x>0 whenever p+r≠0. A further rearrangement gives
```
x−E(r)/H_r ≥ [E(p)−K(p)(1−(1−x)H_pH_r)]/(H_pH_r) ≥ 0.
```
Since E(r)/H_r is d_U u+d_V v+Duv in r-odds, every mate satisfies r_j/(1−r_j)≤x/d_j. If p=r=0 then min(y,x)=0. With y=0 and x>0, some e_i<0 since otherwise Γ's X column would be nonnegative and violate R₀; its shifted C residual is e_i x−t<0. With x=0 and y>0 we have G=ay and the shifted C residuals f_i y−t. The Y column has a negative entry by R₀, so one is negative. Consequently every nonzero root has p+r≠0, hence x>0 and G=0, even when y=0.

If a homotopy root reaches x=1, the scheduled A phase absorbs for sure and can itself be used as the original opening, as proved below. Thus assume no such root is encountered; y=1 is the remaining positive boundary. Assume first a≠0. The necessary G=0 there is P_X(Y sure,p)=0. If p=0 this is impossible since a≠0. If p_i>0 its B equality requires (1−p_j)u_i+p_j v_i=0 where u_i=f_i−J_iY and v_i=P_i({Y,j})−Q_i({Y,j}). Generically u_i and v_i−u_i are nonzero, excluding the case of a single active twin. With both active the two affine equations fix p uniquely, and the polynomial obtained by substitution in P_X(Y sure,p) and clearing denominators is not identically zero: setting u_i=0,v_i=1 gives p=0 and a≠0. These four coefficients are independently adjustable through unregulated twin joining entries. Hence generic inputs either admit a boundary root with x=1 or admit no boundary root throughout the homotopy. In the second case large t gives no root anywhere by boundedness of the C residuals. Homotopy and excision at t=0 supply a nonzero unshifted root. Nongeneric original twin entries can be reached by limits: a common R₀ sphere bound for the linear part and uniform quadratic remainders exclude collapse to zero. When a=0 first increase only P_X({Y}) by ε>0, preserving the X raw implication by increasing L_P. For small ε the full Γ retains R₀ and degree by the same sphere bound. In taking limits pass to one of the two alternatives along a subsequence: unshifted roots stay away from zero by the uniform duplicated full-matrix linearization, and tilted boundary roots have x=1 and bounded tilt t≤max_i ‖F_iC‖∞. The comparisons pass continuously to their respective limits. A limiting root may have y=1. No growth or hazard control at infinite odds is assumed.

## Actual unilateral payoffs

Consider first the generic solutions with y<1. Each player has opponent absorption in a cycle since x>0 and p+r≠0. Since G=0, X's always-wait values at A,B,C are respectively 0,0,P_X(r); A ties. On B the rival survival h=(1−y)H_p is positive and L_P=P_X(y,p)/h=−P_X(r)≤−m, using r∈C,p∈B. The X implication gives L_Q≤0, so its quiet B is optimal, and Q_X(r)≤P_X(r) prices C.

For Y, F_YB≥0 gives N_B≥−K(p), with equality when y>0. Thus N_C=(E(p)+N_B)/H_p≥(E(p)−K(p))/H_p≥0≥−K(r) since r∈C. Also N_A=x+(1−x)N_B≥x−(1−x)K(p). If K(p)<0 this already implies N_A≥x≥J_YX x. For K(p)≥0, F_YB≥0 gives x−(1−x)K(p)≥[E(r)+(E(p)−K(p))/H_p]/H_r≥E(p)−K(p), so x(1+K(p))≥E(p). Since 1−J_YX+K(p)≥k(1+K(p)) and kE(p)≥K(p), we get x−(1−x)K(p)≥J_YX x. These are all Y's caps, including a strictly quiet B.

For an unshifted root each twin has its two scheduled comparisons, binding on positive hazards. Its C comparison gives N_A≥(J_ij−h_i)r_j/(1−r_j)≥−c_i x≥J_iX x, pricing A. At a tilted root with x=1, the same inequality holds, since the shifted C comparison implies the unshifted weak inequality. Every rival of X faces the certain X quit at A, so its full unilateral replacement pays at most its prescribed payoff whenever its A cap holds, regardless of unreached B or C. Player X could instead refuse at A; against these fixed opponents its three caps just proved remain valid and its A slot binds because G=0. Thus starting with A gives an actual equilibrium also in the tilted-boundary alternative. All applicable comparisons pass to the nongeneric limiting roots, including y=1, by continuity since every player faces positive rival absorption per cycle at the limit (x>0,p+r≠0). Bellman iteration bounds every stopping deadline and literal Never by the always-wait value. At unshifted roots each prescribed slot attains this value; at tilted boundary roots the A opening does so. Every unilateral replacement faces uniformly geometric opponent-survival tails, so all original signed levels can be restored, and the exact terminal profile gives the fixed original uniform target. If the singleton-source hypothesis fails, the checked ordinary four-player no-UE implication gives UE already.

## A strict separating table

Take all own levels one and use X,Y,U,V in bit order 1,2,4,8. The entries are the seven P and Q rewards in increasing order of nonempty rival-subset bitmask.
```
       P                             Q
X   8,−10,−3,10,13,24,13         −24,−10,−1,−1,12,−3000,−13
Y   1,−5/8,3,−1,24,−3,7          0,0,0,0,24,0,7
U   5,−4,−3,9,24,7,7             0,1,0,12,3,1,1
V   −3,2,−3,8,24,7,24            0,−1,3,9,1,3,24
```
Here k=0, c_U=c_V=0, all Y offers against twin subsets vanish, and Q_X≤P_X on those subsets. On B the V odds v satisfy v≤1. The sole positive coefficient of L_Q is 12yv, bounded by 12y against the term −24y, so the X implication holds. Every nonsingleton principal block is invertible and each column has a negative entry, proving R₀. At t=(1012,1017,1025,1047), enumeration of the eleven blocks of sizes 2,3,4 gives a unique complementary solution, supported on XYU with entries (6605/3,14975/6,28432/15); its outside slack is 62517/5 and its active determinant is 15, giving degree +1. The theorem supplies an actual three-date equilibrium.

The singleton signs fix Y as the sole row with exactly one positive supplier, namely X. Its normalized d=(5/8,1), e=(5,−3), h=(9,8). The former weights would have to satisfy 5w_U−3w_V=−1, forcing w_V≥1/3, and 8w_V<5/8. This excludes the previous weight producer under every relabeling and independently of its higher-payoff inequalities. The two-orientation predecessor also requires the two X-to-twin entries to have the same sign. Neither matched-pair date can serve X: choosing Y or V as mate violates X's mate-premium sign, and choosing U violates U's. The older two-free-row guard on scheduled recipient a requires Q_a(T)≥P_a(T) for all three nonempty subsets of the two owners outside a,b. Checking these cells on all twelve ordered choices leaves only (a,b)=(Y,X). With o its scheduled phase and p the opposite phase, this test requires A=H_o(P_p+H_p Q_o)−(Q_o−P_o)≥0 to imply B=P_p+H_p P_o−(1−H_o H_p)Q_p≥0. At scheduled twin hazards (0,0) and opposite hazards (U,V,X)=(2/3,2/3,1/4) its A=149/144 and B=−389/432 violate the required implication. The componentwise one-recipient test requires Q_i≥P_i on the component of {P_i>0,P_i−(1−H_i)Q_i>0} approaching zero. Every row violates it near zero on rays Y,X,X,Y for rows X,Y,U,V respectively.

The supportwise Low, Charge and negative-orientation tests all fail on support S=XYV. At odds (2/5,1,3) its three active Quit-premium numerators are (9,144/5,1/5). The odds indifference map Φ_i=Σ_T(Q_i(T)−P_i(T)) z_T has values (−68,13/5,3/5) and off-diagonal derivatives (−35,−12),(−1,1),(9,−3/5), with determinant −1611/5. Charge fails already at the singleton X, whose two other participant entries in S are zero; no pair within S has two strictly positive participant premiums. This derivative occurs even in the earlier first-action payoff domain. In full original order take w=(−68,13/5,2563/375,3/5), the mixture of native exit vectors with masks (1,11,12,13) and weights (1893,314,718,75)/3000. At q=(0,0,1/15,2563/4500) the four forced Quit offers are (−1936063/16875,0,2563/375,3/5). Passive exit contribution plus rival survival times each row's minimum over its native cells and zero is (−4497391/3750,−201817/108000,15319/4500,−34/15), coordinatewise at most w. This verifies first-action membership with equality of the forced offer on both active coordinates.

The game has no sure opening followed by any continuation or punishment, and no exact stationary terminal equilibrium. Here is reproducible rational pseudocode for these finite exclusions. Native P,Q,H are the independent rival averages and survival at a row q. With a sure owner its necessary residual is P_i−Q_i+H_i min_T Q_i(T)≤0 (include empty T), since an owner declining to quit can secure at least that minimum in its child simply by immediate Quit. Nonsure owners face a sure rival and their ordinary one-date comparisons apply. With no sure player and at least two stationary movers all players face recurrent rival absorption; the Never-minus-Quit residual is B_i=P_i−(1−H_i)Q_i. All-Continue gives zero against a profitable immediate own exit. Each singleton has a negative outsider with J_ij>Γ_ij, excluding its stationary play.
```
for each quiet/mixed/sure status with a sure player:
    C_i=P_i−Q_i + 1[sure i] H_i min_T Q_i(T)
    require C_i>=0 for quiet or mixed, C_i<=0 for mixed or sure
    Bernstein controls = C evaluated at all vertices of the mixed cube
    run subdivision, discarding boxes contradicting a required sign

for each proper stationary support S of size >=2 (outside hazards zero):
    C=(B_X,B_Y,B_U,B_V, [1ᵀΓ_SS⁻¹] B_S)
    require every output >=0 and active outputs and last output <=0
    sample at {0,1/2,1}^S, then replace each one-axis triple (a,b,c)
    by the degree-2 Bernstein controls (a,2b−(a+c)/2,c)
    run subdivision with additional origin discard

subdivision:
    discard if all controls of a required nonnegative output are <0,
       or all controls of a required nonpositive output are >0
    in a stationary box containing the origin also discard if the last
       output has zero origin control and every other control is positive
    else split the next variable cyclically at its midpoint
    use the midpoint de Casteljau coefficients, preserving exact rationals
```
The 65 sure statuses use 155 boxes, maximum depth 8. In lexicographic support order the stationary counts are (1,11,1,1,1,5), (187,5,39,1) and 33, with maximum depths 5,16,9. The extra origin rule follows since a nonzero point gives positive weight to at least one non-origin control. The origin is excluded separately.

## Lean handoff

The checked declaration `finFour_singleton_r0Degree_eq_one_of_no_uniformPayoff` in `UniformEquilibrium/Diagnostics/Quitting/FinFourSingletonDegreeCriterion.lean` uses the matrix `quittingSingletonMatrix` of `UniformEquilibrium/Quitting/Classification/LCP/QuittingRewardAdapter.lean`. Positive scaling of a payoff row leaves its homogeneous complementarity zeros fixed and hence preserves its R₀ degree by homotopy. The three-date argument here constructs an exact original behavioral terminal Nash profile on the R₀ nonzero-degree branch. The checked consumer `quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors` in `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean` therefore supplies a fixed uniform payoff, also directly witnessed by geometric tails. The six-variable construction and rational raw comparisons are ordinary mathematics. General Fin4 remains open.
