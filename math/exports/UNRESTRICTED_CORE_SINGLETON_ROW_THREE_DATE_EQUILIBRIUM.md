# A three-date equilibrium with one unrestricted core singleton row

In a four-player quitting game let s_i be i's own singleton reward, and subtract it on every nonempty absorbing coalition to obtain native payoffs. For a nonempty rival subset T write P_i(T) for i's payoff on T and Q_i(T) for its payoff on T+i; define both to be zero at the empty subset. Write Γ_ij=P_i({j}), J_ij=Q_i({j}) and Γ_ii=0. For a vector of independent rival hazards, P_i or Q_i denotes the corresponding multilinear average. A player's own singleton level can have either sign. The game has zero live and Never payoffs.

Name two players X,Y and call the others U,V. Normalize the native Y row by a positive constant. The raw conditions are as follows.

1. Require Γ_YX=1 and Γ_Yj=−d_j<0 for j=U,V. Write a=Γ_XY. None of the three X singleton comparisons has a prescribed sign. For each twin i with opposite twin j, write e_i=Γ_iX, f_i=Γ_iY and h_i=Γ_ij.
2. For each nonempty T⊆{U,V}, P_Y(T)<0 and k P_Y(T)≤Q_Y(T)≤0 for one k∈[0,1). Also J_YX≤1−k.
3. There exist weights w_U,w_V≥0 and ℓ_U,ℓ_V≥0 satisfying
   ```
   w_U e_U+w_V e_V=−1,     ℓ_U+ℓ_V≤−P_Y({U,V}),
   w_i h_i≤ℓ_j<d_j         for each twin i and its opposite j.
   ```
   These are linear feasibility tests in four unknowns. In particular the weights can be concentrated on a twin with e_i<0 and h_i≤0, taking ℓ=0. They can also accommodate two positive h_i: for e_U=e_V=−1, h_U=h_V=3/2, d_U=d_V=1, P_Y({U,V})=−2, take w_U=w_V=1/2 and ℓ_U=ℓ_V=3/4.
4. Each twin i with opposite twin j satisfies J_iX≤0 and J_ij≥h_i. All remaining entries in both twin rows are free.
5. For T⊆{U,V}, Q_X(T)≤P_X(T). Define m=min_{T⊆{U,V}}P_X(T), including the empty subset. For nonnegative odds z on Y,U,V let L_C=Σ_{∅≠T⊆{Y,U,V}} C_X(T)∏_{j∈T}z_j, for C=P,Q. Require the raw polynomial implication L_Q>0 ⇒ L_P>−m throughout these odds.

Then the original signed game has a fixed uniform-equilibrium payoff against complete unilateral behavioral replacements. On the R0 degree-one singleton branch it has an exact terminal Nash calendar with three repeated dates. The example below satisfies the raw conditions but has neither an exact stationary terminal equilibrium nor an equilibrium opening with a sure quitter.

## Index after removing the Y indifference equation

The checked Fin4 implication applies to every real reward table on the fifteen nonempty coalitions: absence of a uniform-equilibrium payoff implies that the hollow singleton matrix is R0 (the only zero of min(z,Γz) is zero) with local Brouwer degree one. This is `finFour_singleton_r0Degree_eq_one_of_no_uniformPayoff` in `UniformEquilibrium/Diagnostics/Quitting/FinFourSingletonDegreeCriterion.lean`; the matrix convention is `quittingSingletonMatrix` in `UniformEquilibrium/Quitting/Classification/LCP/QuittingRewardAdapter.lean`. A homotopy through positive diagonal row scalings preserves R0 and its degree, since the homogeneous complementary zero set stays fixed. It therefore suffices to produce the asserted calendar on this branch. Set d=(d_U,d_V), g'=(Γ_XU,Γ_XV), and H the hollow twin principal matrix. First assume a≠0. On the remaining variables (y,m_U,m_V) take the three homogeneous comparison rows
```
D_0= a y + g'·m,
D_i= f_i y + e_i d·m + (Hm)_i.
```
A homogeneous solution of min((y,m),D(y,m))=0 with m≠0 must have y>0 since at y=0 the weighted twin residual is −d·m+Σ_i w_i h_i m_j≤(ℓ−d)·m<0, where j denotes i's opposite. With x=d·m>0 it lifts to Γ: Y's residual is zero and X's residual D_0 is zero since y>0. When m=0, y>0 is impossible by a≠0. Thus D is R0.

For the degree take a generic strictly positive target (u,t_U,t_V) for D, and v>0 small enough that all t_i+e_i v>0. Use the target (u,v,t_U+e_U v,t_V+e_V v) for Γ. Its Y inequality gives x≥v+d·m>0. At y=0 its weighted twin left side would be −x+Σ_i w_i h_i m_j≤−v+(ℓ−d)·m<0, contradicting the strictly positive weighted target. Therefore x=v+d·m by Y's equality, and X's equality is the first D equation. Conversely a D-solution has y>0 by the same weighted inequality, and this x lifts it. Outside slacks and support regularity coincide. On active principals, exchanging X and Y's rows and pivoting on Γ_YX=1 gives the determinant of the corresponding D principal; thus the index signs are opposite. For generic targets, singular active principals, vanishing active variables and outside ties are excluded by finitely many proper linear subspaces. R0 bounds solutions along bounded target homotopies by normalization. The regular index formula gives deg D=−deg Γ=−1.

Duplicate each twin's row and column to give it a B-slot and a C-slot. The resulting five-variable matrix acts on (y,p,r) by D(y,p+r), copying each twin's residual twice. R0 follows by adding the nonnegative copies. At the same generic target lower each extra copy's target by one; only the higher copy can be active. The local indices agree, so the duplicated matrix still has degree −1.

## A nonzero root of the five comparisons

Use dates A=(x,0,0,0), B=(0,y,p_U,p_V), C=(0,0,r_U,r_V), repeating. Write H_p=∏(1−p_j), H_r=∏(1−r_j), E(p)=−P_Y(p) and K(p)=−Q_Y(p) against twins alone. Thus 0≤K≤k E, and E>0 unless its argument is zero. On positive parts of the padded cube (−1,1)^5 use the open domain
```
E(r)+(E(p)−K(p))/H_p < H_r,
x = [E(r)+(E(p)−K(p))/H_p+K(p)H_r]/[(1+K(p))H_r].
```
On its closure H_p,H_r stay bounded away from zero: H_r≥E(r) and H_p≥E(p)−K(p)≥(1−k)E(p), while E is strictly positive whenever a twin hazard is one. Consequently 0≤x≤1, with x>0 if p+r≠0. At any nonnegative boundary point x=1 or y=1.

For X set G=P_X(y,p)+(1−y)H_p P_X(r). For each twin i at t=B,C write b_t,h_t,Q_t for its passive exit contribution, rival survival and forced quit offer at date t. Set
```
F_it=b_t+h_t b_next+h_t h_next b_last−(1−h_A h_B h_C)Q_t .
```
The cyclic words next and last are read from t. Evaluate all hazards on positive parts. The five comparisons are min(y,G) and min(p_i,F_iB), min(r_i,F_iC), coordinatewise. At zero the field is the duplicate-D minimum map plus a uniform quadratic error on nonnegative inputs: x=d·(p+r)+O(||(y,p,r)||²), G=ay+g'·(p+r)+O(||(y,p,r)||²). To first order the twins' three passive contributions are e_i x, f_i y+h_i p_j, h_i r_j; forced offers appear only in products of second order. The positive-part input extension has the same local degree: on a homogeneous interpolation from the identity to the positive part any root is already nonnegative. R0 gives a positive minimum on the unit sphere for this compact interpolation, and then absorbs the quadratic error. Thus zero is isolated with index −1.

Subtract t≥0 from both C residuals. The weight normalization gives some twin g with e_g<0. At x=1 its C residual is (h_g−J_gj)r_j+(1−r_j)e_g<0. At y=1 the first comparison requires P_X(Y sure,p)=0. At that boundary F_iB=(1−p_j)u_i+p_j v_i with u_i=f_i−J_iY, v_i=P_i({Y,j})−Q_i({Y,j}). If neither B twin acts, P_X(Y sure,0)=a≠0. A single acting twin requires u_i=0. With both acting, the two displayed affine equations must vanish where P_X(Y sure,p)=0. Generically all three alternatives fail: the two intercepts and endpoints are independently free by changing the four B joining entries Q_i({Y}) and Q_i({Y,j}). Exclude zero slopes and intercepts. Substituting the unique two affine roots in P_X(Y sure,p) and clearing denominators gives a nonzero polynomial, since u_i=0,v_i=1 for both gives a≠0. These generic perturbations leave every raw hypothesis unchanged. Negative boundary coordinates cannot be zeros of a minimum map. For large t the shifted field has no roots, by boundedness of the C residuals. Degree homotopy and excision therefore give a nonzero root at t=0. In the nongeneric case take limits of such roots: the same R0 linear part and uniform quadratic bound separate them from zero. The limit may have y=1, and x=1 is still excluded.

If a nonzero root had p=r=0, its first comparison would force ay=0 for y>0. Therefore x>0. If y=0, the C comparison for each twin i gives (1−r_j)N_iA≥(J_ij−h_i)r_j≥0 for its always-wait cyclic value N_iA, well defined since x>0. Its A value has strictly positive denominator and numerator e_i x+(1−x)h_i[p_j+(1−p_j)r_j]. The weighted sum of these numerators would therefore be nonnegative. Put T=E(r)+(E(p)−K(p))/H_p. Since x<1 and p+r≠0, we have 0<T<H_r and
```
x/(1−x)=(T+K(p)H_r)/(H_r−T)>T/H_r+K(p)≥E(r)+E(p).
```
On the twin cube E(z)≥ℓ·z by the inequalities at its four vertices and multilinearity. For each opposite pair, w_i h_i[p_j+(1−p_j)r_j]≤ℓ_j(p_j+r_j), using ℓ_j≥0 even if h_i<0. Thus the weighted numerator sum is at most −x+(1−x)ℓ·(p+r)<0. Thus y>0 and G=0.

## The actual unilateral caps

For X the always-wait cyclic values at A,B,C are 0,0,P_X(r), directly from G=0. Its A offer ties. If y<1 write the X B rival survival h=(1−y)H_p>0. Then G=0 gives L_P=P_X(y,p)/h=−P_X(r)≤−m; the raw implication gives L_Q≤0, pricing its quiet B slot. On C the twin-subset bounds give Q_X(r)≤P_X(r). For nongeneric limiting roots with y=1 take the continuous limits of these B-offer comparisons from the generic roots (which all have y<1).

For Y the always-wait values are N_A=x−(1−x)K(p), N_B=−K(p), N_C=(E(p)−K(p))/H_p. Substituting x in the recursions gives all three identities, with its B offer tied. On C its offer −K(r)≤0≤N_C. The C recursion implies N_A=[E(r)+(E(p)−K(p))/H_p]/H_r≥E(p)−K(p); hence (1+K(p))x≥E(p). Since 1−J_YX+K(p)≥k(1+K(p)) and kE(p)≥K(p), we obtain (1−J_YX+K(p))x≥K(p), equivalently N_A≥J_YX x.

For each twin the definition of F is exactly (1−h_Ah_Bh_C)(N_t−Q_t); both scheduled comparisons hold, with equality on its occupied slots. Its C inequality implies (1−r_j)N_A≥(J_ij−h_i)r_j≥0. Hence J_iX x≤N_A at A. Every player's rivals have positive cycle absorption because x,y>0. Iteration bounds every stopping deadline and Never by the always-wait value and gives equality under the prescribed calendar. Geometric tails hold uniformly over unilateral replacements; adding back each signed singleton level and undoing the Y scaling therefore yields an exact terminal Nash calendar and the fixed original uniform-equilibrium payoff.

If a=0, R0 forces some f_i<0, since otherwise the Y basis vector is a nonzero homogeneous complementary solution. The matrix D at a=0 is still R0: the argument for m≠0 is unchanged, and m=0,y>0 would have twin residual f_i y<0. Raise only P_X({Y}) by ε>0. This adds ε z_Y to L_P, preserving the raw implication. R0 and its degree persist under small perturbations by the positive sphere bound, giving exact calendars for the perturbed games. Their five coordinates stay uniformly away from zero by the duplicate-D sphere bound at a=0 and the uniform quadratic expansion. Their compact limit satisfies the five original comparisons. If p=r=0 and y>0, then x=0, and the same twin has F_iC=y f_i<0. Thus p+r≠0, x>0, and the weighted numerator argument again gives y>0. All cyclic values and offer comparisons pass continuously since every rival survival over a cycle is now strictly below one. This proves the exact conclusion also at a=0.

## A table requiring a nonstationary opening without a sure quitter

Take s_i=1. The following rows list P and Q in increasing bitmask order of the seven nonempty subsets of the other three players; X,Y,U,V correspond to bits 1,2,4,8.

| | P | Q |
|---|---|---|
| X | 1,3,5,−3,−2,0,−80 | −1,−1,1,−61/20,−1,−3000,−90 |
| Y | 1,−2,2,−2,20,−4,−60 | 0,0,1,0,0,0,2 |
| U | −1,2,2,−2,50,25,60 | 0,9/5,1,−2,0,−19/5,−6 |
| V | 1,−1,9,1,2,30,2 | 0,1,3,1,0,1,0 |

Use k=0, w_U=1, w_V=0 and ℓ_U=ℓ_V=0. Here m=−3, and L_Q>0 implies yu>y+u+3v+yv+3000uv+90yuv. Therefore y,u>1 and L_P=y+3u−3v+5yu−2yv−80yuv>3y+5u+3v+3yu>3. All raw tests hold. The matrix Γ has det 4, all pair and triple principals nonsingular, and a negative outsider at each singleton, hence is R0. At target (1012,1017,1025,1047) the only complementary solution uses the full support and equals (6290,11537/2,1051/2,2111). Thus its degree is +1.

There is no sure first-date equilibrium followed by any continuation or punishment. A necessary condition at such a head is P_i−Q_i≥0 for quiet players, equality for interior players, and P_i−Q_i+H_i min_T Q_i(T)≤0 for sure players, since immediate Quit in the child guarantees s_i+min_T Q_i(T). Others face a sure opponent. The rational subdivision below rejects all 65 statuses containing a sure owner in 123 boxes. Every stationary profile with at least two positive hazards faces geometric rival absorption. At an exact stationary terminal equilibrium each interior-hazard owner needs B_i=P_i−(1−H_i)Q_i=0, with B_i≥0 at quiet players. Sure hazards are already excluded. Singletons each have Γ_ij<min(0,J_ij) for an outsider. All-Continue fails since s_i=1. In the remaining cases the same rational subdivision rejects all six pairs, four triples and the full support in respectively 24,222,145 exact Bernstein boxes. To check termination at the trivial origin use the extra scalar linear combination of active B with row 1ᵀ Γ_SS⁻¹. On the pointed box it suffices that every Bernstein coefficient of this combination except the origin is strictly positive. Dividing cyclically by midpoints certifies the finite counts; maximum depths are 7,18,31. Thus the table has neither an exact stationary terminal equilibrium nor a winning sure first move.

No relabeling meets the two-core sign test: that test requires a player with one positive singleton and two negative ones, and the reciprocal row must give opposite signs to its core partner and each of the other two players. Checking the candidate second row with a unique positive singleton leaves Y or U; when it is Y the first row is X with mixed twin signs, and when it is U the first row Y has Γ_YU<0 but the other entries of Y have opposite signs.
The raw implication on X is genuinely conditional: on the triple XYU, odds y=u=3 with v=0 give L_Q=3>0. The payoff-domain orientation test can also fail. At XYU odds (3/2,2,3), all active joining offers are positive and the odds indifference map Φ_i=Σ_{T≠∅}(Q_i(T)−P_i(T))z_T has derivative with off-diagonal rows (−14,−12), (−4,1/2), (−1,−17/10), determinant −373/5. The active Φ values are the XYU projection of w=(−40,0,−19/10,1/2). This vector is half the native coalition reward at YUV and satisfies Q_i≤w_i, q_i(w_i−Q_i)=0, P_i+H_i min(0,min_C Z_i(C))≤w_i at q=(0,0,1/2,19/20). Thus the negative sign occurs even on the first-action payoff domain used by earlier orientation tests.

For a second example change only P_U({V}) and Q_U({V}) to 1. Both cross-twin singleton payoffs are now positive. Y is the only row with exactly one positive singleton, fixing the core roles; neither remaining twin has h_i≤0. The linear test succeeds with w=(1,0), ℓ=(0,1). The singleton determinant is 22, and at the same target the only solution is (24859,15956,2614,4222)/11 with full support. The subdivision again excludes all sure heads in 123 boxes and all pairs, triples and full-support stationary profiles in 24, 188 and 59 boxes, respectively.

## Exact rational verification of the finite exclusions

Enumerate masks with bits X=1,Y=2,U=4,V=8. For each i and rival subset T let
`w(T)=∏_{j∈T}q_j ∏_{j∉T,j≠i}(1−q_j)`. Set `P_i=Σ w(T)P_i(T)`, `Q_i=Σ w(T)Q_i(T)`, `H_i=w(∅)`. All arithmetic in the following pseudocode is rational. Each status restricts its inactive and sure coordinates before sampling. At a positive regular LCP target t, test each nonsingular active support S by computing Γ_SS⁻¹ t_S, checking strictly positive coordinates and nonnegative outside slacks. Singular singleton or empty supports cannot solve this target. This gives the degree census above.

For a sure head, statuses range over quiet, mixed, sure. Regard the mixed coordinates as the variables of a unit cube. The no-sure statuses are skipped. The sign lists POS and NEG enumerate outputs required nonnegative and nonpositive respectively; an equality occurs on both lists.
```
sure head:
    c_i=P_i−Q_i + [i is sure] H_i min_T Q_i(T)
    POS=quiet∪mixed; NEG=mixed∪sure
    Bernstein coefficients = vector c at all cube vertices  (degree 1)
    prune(C, POS, NEG, false, 0)

stationary support S of size at least 2:
    q_outside=0; enumerate variables in ascending owner order
    c_i=B_i; append c_4=(1ᵀ Γ_SS⁻¹) B_S
    POS={0,1,2,3,4}; NEG=S∪{4}
    sample c on {0,1/2,1}^S
    along each axis replace every triple (a,b,c) by (a,2b−(a+c)/2,c)
    prune(the resulting Bernstein coefficients, POS, NEG, true, 0)

prune(C, POS, NEG, contains_origin, depth):
    discard if some output in POS has maximum coefficient <0
    discard if some output in NEG has minimum coefficient >0
    if contains_origin and output 4 is zero at the origin and all
       its other coefficients are positive, discard except the origin
    otherwise split on axis (depth mod number of varying coordinates)
    for linear pairs (a,b), put e=(a+b)/2 and use (a,e),(e,b)
    for quadratic triples (a,b,c), put e=(a+b)/2, f=(b+c)/2, g=(e+f)/2
       and use (a,e,g),(g,f,c)
    recurse on both halves; only the lower half can retain contains_origin
```
A zero-dimensional cube is tested by the same sign checks with its single value. The coefficient convex-hull property validates each discard, and a point other than the origin gives positive weight to at least one non-origin coefficient. The counts in ascending lexicographic support order are 1,1,15,1,1,5 boxes on pairs, 1,133,71,17 on triples, and 145 on full support; the 65 sure statuses have maximum depth 14. Hence all recursions terminate with the stated exclusions. The theorem gives a fixed uniform-equilibrium payoff on this class; general Fin4 remains open.
