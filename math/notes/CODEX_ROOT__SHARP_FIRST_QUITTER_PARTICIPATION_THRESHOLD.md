# A sharp transition in the first-exit participation of player U

Consider the four-player quitting table below. Players are X,Y,U,V with bits 1,2,4,8. All four own singleton levels are one. For each player i and nonempty set D of its rivals, P_i(D) is its native reward if exactly D quits first, and Q_i(D) its native reward if exactly D together with i quits first. Native exit rewards are original rewards minus one. Both entries at empty D are zero for evaluating one-stage offers. Perpetual continuation and live play pay zero in original units. The entries within each list are in increasing nonempty rival bitmask order.

| Recipient | Passive P | Joining Q |
|---|---|---|
| X | 1,3,5,−3,−2,0,−80 | −1,−1,1,−61/20,−1,−3000,−90 |
| Y | 1,−2,2,−2,20,−4,−60 | 0,t,1,0,0,0,2 |
| U | −1,2,2,−2,50,25,60 | 0,9/5,1,−2,0,−19/5,−6 |
| V | 1,−1,9,1,2,30,2 | 0,1,3,1,0,1,0 |

This is the q=0 axis of [Two arbitrary joining rewards on a four-player quitting table](../exports/TWO_ARBITRARY_JOINING_REWARDS_ON_SEPARATE_DATES.md). That theorem already gives a uniform-equilibrium payoff over the whole plane. The present question concerns the support of all approximate equilibria. At each live date players randomize privately and independently. A unilateral replacement may change a player's entire stopping law, including choosing Never. Let e be the maximum gain in expected original terminal payoff, and D_i the probability i is among the first quitters.

**Theorem.** Put
```
τ = (−353281−12√378267726)/22801 ≈ −25.7300237953.
```
For t≤τ a fixed exact uniform-equilibrium profile has D_U=0. For every fixed t>τ one has inf(e+D_U)>0 over all behavioral profiles. Thus U occurs in every limiting first-exit law of vanishing-regret profiles precisely above this threshold. When the other 59 independent reward coordinates vary near the displayed values, a real-analytic threshold still gives the same dichotomy for every real t. Its formula is given below. At t=100 all four identities occur with positive singleton mass in every limiting first-exit law, even though the known exact period-two equilibrium never uses all four identities on one date.

## The anchor t=100

The published rational census in the two-reward theorem excludes every sure opening at punishment and every exact stationary terminal equilibrium at this anchor. Its lower bound on every sure player's child cap is min_D Q_i(D), which includes zero and is guaranteed by immediate Quit. All off-diagonal singleton comparisons Γ_ij=P_i({j}) are nonzero. For columns X,Y,U,V one can take blockers U,V,Y,Y respectively: each has Γ_ij<min(0,Q_i({j})). The fixed-pair classification therefore excludes any limiting law of vanishing-regret profiles with only two participating identities. [Two possible first quitters force a stationary equilibrium](../exports/TWO_POSSIBLE_FIRST_QUITTERS_FORCE_STATIONARITY.md)

Suppose e+D_U→0. Let K be the set of all possible limits of initial pairs (prescribed native payoff vector, first-exit law including Never) along such sequences at this fixed table. This set is compact by diagonal selection in a bounded finite-dimensional space, and is nonempty under the supposition. Native payoffs equal original payoffs minus one, with native Never therefore −1. Write S,E,W for the components of X,Y,V at the current date, a=x+y+u+v for the sum of the four hazards, c for their product of Continue probabilities, and s for incoming joint survival from the initial root. A prime labels the next date. On K one has E,W≥0 because their original forced-quit native offers are nonnegative at every hazard. The fixed-pair exclusion implies no law in K is supported on a pair of participants. In particular, for every player i there is a uniform d_i>0 such that each law in K has probability at least d_i of a rival of i participating in the first exit. The probability of Never tends to zero, since on positive marginal joint Never tails the actual conditional payoff tends to zero, while immediate Quit tends to the positive own level and restart regret is at most e/s.

We record the compactness estimates used below. For fixed σ∈(0,1) take the prefix ending when survival first falls below σ. Its incoming values satisfy s≥σ. All its hazards are bounded above by 1−γ for some γ>0 once the sequence index is large. Otherwise a subsequence of rows tends to a sure row at a bounded continuation cap above punishment: first-action regret tends to zero because the initial regret of each restart is ≤e/σ. Lowering the sole sure player's continuation to punishment can only favor Quit, and multiple sure players have no effective continuation. This contradicts the first input. The prefix therefore ends at survival at least σγ⁴. Its total Σa is bounded by −log(σγ⁴), and Σu≤D_U/σ. Each before- or after-row prescribed state and law approaches K uniformly on this prefix, because restarting at such a live history gives both regret and conditional U first-exit probability bounded by (e+D_U)/(σγ⁴). Each subsequential limiting row is proper, has u=0, and is exactly Nash at its limiting next prescribed continuation. Indeed the cap and prescribed value differ by at most restart regret, before and after the row. A limiting row can be entirely empty.

For a fixed player let b be its conditional best-response cap and F its prescribed one-step reward with b′ used on joint survival. The stage loss l=b−F≥0 satisfies Σ s l≤e by telescoping against the prescribed recursion. In particular the sum of s q_i (b_i−Q_i) is at most e, since the prescribed mixture assigns probability q_i to that action and both action losses are nonnegative. Native Q_i includes the usual zero empty-rival offer. We use these estimates at the fixed-survival prefixes only.

**A strictly negative linear combination.** On K we first have W≤6/5. At any limiting row with y>0 player Y has E=Q_Y=0. Its Wait equality gives x−2v+21xv≤0, hence x≤2v/(1+21v)≤1/11. On a prescribed date with x≤1/10, conditional on Y quitting and U absent the expected reward of V is ≤6/5: it is a mixture of 10x−1 upon waiting and 1+2x upon joining. With neither Y nor U quitting the possible finite rewards of V are ≤1. Rows with x>1/10 are bounded in count on each fixed-survival prefix. Their y tend uniformly to zero there, by the limiting-row implication just proved. The total probability of U participating is negligible. Summing expected rewards weighted by their event probabilities, passing to the limit and then taking σ↓0 proves the upper bound. All payoffs here are native.

Put L=S+W−E. At a limiting row with x,y>0, the preceding bound forces v>0. The full row has E=0, S=−y−(61/20)(1−y)v and W=y(1+2x). Its V wait comparison is
```
2y(1−4x)=(1−y)[x+(1−x)W′].
```
Hence y/(1−y)≤(3/5)/(1−4x)<1 and 2xy/(1−y)≤(6/5)x/(1−4x)≤(12/5)v/(1+13v). Thus L≤−(3/10)v at every such row.

Let g be the unconditional one-date contribution of finite original exits in native units to L, so L=g+cL′. At u=0 the raw coalition values for L on X,Y,V,YV,XV,XY,XYV are 0,0,−1,−1,−461/20,8,2. Consequently g≤−v+8xy+C u throughout the physical cube, for a fixed finite C. For any sequence and fixed σ as above there are errors ε_n↓0 and a fixed C' such that on its entire prefix
```
L⁺ ≤ c(L′)⁺+ ε_n a+C' u,
g  ≤ −v+C' a(−L)⁺+ε_n a+C' u.                     (1)
```
For the first inequality, at a positive limiting a a row with xy>0 has strictly negative L; any other has g≤0. For the second, at a positive limiting a a row with xy>0 has xy≤2vy≤(20/3)a(−L)⁺; when xy=0 the bound is immediate. Compactness after division by a supplies the uniform vanishing error when a is bounded from below. Along any subsequence with a→0 the displayed estimate for g gives both assertions directly from xy≤a²; the explicit Cu term removes any dependence on u/a. Empty rows satisfy the statements identically.

Iterating the first inequality gives L≤0 throughout K by letting n→∞ then σ↓0, since terminal payoffs are bounded. If some limiting root has L=0, the second inequality implies
```
(−L′)⁺ ≤ c⁻¹[(1+C'a)(−L)⁺+ε_n a+C'u].
```
The product of c⁻¹ on the prefix is bounded by 1/(σγ⁴), and Σa is bounded there. Iteration shows (−L)⁺→0 uniformly on the prefix and its endpoint. The positive part also tends uniformly to zero there because all these states approach K. Now telescope the second inequality in (1) with weights s, using the initial and endpoint L→0. It gives Σ s v→0 on the prefix. The remaining probability of V first quitting is at most σ. Taking σ↓0 leaves only X,Y as possible first quitters in this K law, contradicting the fixed-pair result. Thus L≤−δ for some δ>0 on K.

**Positive V values and separated Y dates.** For sufficiently small fixed η>0 every prefix row with a≤η has E≥δ/2 eventually. Indeed S≥Q_X−o(1)≥−C a−o(1) and W≥−o(1) by the restart regret, while L≤−δ+o(1). As Q_Y=O(u), one has b_Y−Q_Y≥δ/3 on these rows. The weighted action loss estimate proves the unweighted sum of their y is o(1) on each fixed-survival prefix.

If W=0 at some K root, choose a realizing sequence. With Y and U absent from the finite exit the raw native reward of V is nonnegative, so its prescribed recursion gives c W′≤W+C(y+u). On the prefix rows with a>η, of uniformly bounded count, the immediate Quit offer gives y≤W+o(1), using Q_V=y(1+2x)+O(u). On other rows Σy=o(1) as just proved. Starting from W→0, iterate these inequalities on the prefix: ∏c⁻¹ and Σu are bounded and vanishing respectively, and there are only boundedly many factors 1+C from large rows. Thus W⁺ tends uniformly to zero there, and so does the total Σy. This would leave Y out of the limiting law, contrary to the fixed-pair result for X,V. Compactness therefore gives W≥d>0 throughout K.

Choose κ>0 with κ<min(δ/2,d/6). The total u+y+v on rows with y<κ tends to zero on each fixed-survival prefix. For v this follows directly from b_V−Q_V≥d/3 there and the weighted action loss. For y use the small-a conclusion above. For rows with a>η, whose count is bounded, every limit with y≤κ must have y=0: if y>0 and v>0, V's tie gives W=y(1+2x)≤3κ<d; if y>0 and v=0, the Y equation gives x=0 and E=0, so −δ≥L=S+W≥−y by X's immediate offer. Both are impossible. The u assertion is already known.

**Compress the remaining calendar.** Keep every row with y≥κ. Between two kept rows, including before the first, replace the X hazards on the omitted rows by their aggregate h=1−∏(1−x). For clarity we justify this operation only in the limit. From any sequence of restarts approaching K, a kept date must occur before survival falls below a uniform σ_*∈(0,d_X/2). Otherwise the omitted rows up to that prefix have negligible total non-X hazards and the probability of a non-X first quitter is at most σ_*+o(1), although it is at least d_X−o(1). The same argument applies after the kept row because its reach has a fixed positive lower bound, also after that row by properness. Inductively, each fixed numbered gap and kept date has positive limiting reach and the aggregate h is bounded away from one there. Passing diagonally gives a limiting calendar of proper kept rows and proper solo-X rows (delete h=0), together with limiting before/after states and laws in K. On each fixed gap the sum of omitted non-X hazards tends to zero by the preceding paragraph. This estimate is on the independent rival clocks, so it also controls unilateral replacements of X by waiting.

The kept rows are Nash at their next original continuation. Across a gap, the native X values satisfy S_before=(1−h)S_after. Other player i's actual values satisfy w_before=hΓ_iX+(1−h)w_after. These follow by coupling the omitted rows to the same X clock with all other actions quiet, changing total probability by o(1). If h>0, X can quit at the gap entrance for 0+o(1), or wait throughout it and obtain S_after+o(1). Approximate optimality gives S_before≥max(0,S_after), hence both X values are zero. Each of the other players has the native forced offer zero at a solo-X row because J_YX=J_UX=J_VX=0. If h>0 there were eventually omitted rows, so an immediate Quit at the gap entrance had this same limiting offer even in the uncompressed game. Its limiting prescribed value is at least zero. Hence each compressed row satisfies all four exact Bellman comparisons.

Each kept row has y≥κ, so geometric absorption in the number of kept rows makes the propagated bounded states the actual values of this calendar. The same propagation holds for the sixteen first-exit law coordinates, since the same gap coupling also identifies their recursions. Each resulting tail law at a kept date is consequently its earlier K limit, with the uniform d_Y lower bound on some non-Y first participant. If Y's rival survival through the calendar were positive, their remaining probability of any future attempt would tend to zero and violate this d_Y bound. All other deleted-player survivals vanish by the recurring Y hazard. Bellman iteration thus gives an exact terminal Nash calendar against all unrestricted unilateral replacements, with U always quiet. It remains to exclude this exact calendar. Every restart of it has a payoff and law in K, by using the constant sequence of that same restart. Hence W≥d and L≤−δ at every retained date. If h>0 on an intervening compressed solo-X row, its successor has S=0. The successor is a retained positive-y row, where E=0 by Y's indifference and W>0. This contradicts L<0, also for a possible initial positive solo-X prefix. Only the kept positive-y dates remain. The Y equality gives x−2v+21xv=0 at each, so x=2v/(1+21v). These rows are solo Y or full XYV. Every tail has positive probability of some non-Y first exit, uniformly, so there are infinitely many full dates.

Write S,E,W for the X,Y,V native continuation values as above. At a full date put w=W′ and η=y/(1−y). Then
```
η=[x+(1−x)w]/[2(1−4x)],   W=F_v(w)=(1+2x)η/(1+η).
```
Its derivative in w is nonnegative and at most (1+2x)(1−x)/[2(1−4x)]≤13/14. At a solo-Y date W=−y+(1−y)W′≤W′. The verified inequality F_v(11/50)≤11/50 on 0≤v≤1 therefore gives W≤11/50 throughout the tail: propagate the positive part above 11/50 backwards, contracting at every one of infinitely many full dates.

Define R=(1−S)/(1+W)−1. On solo-Y dates R=R′ exactly. At full dates use X indifference and the Wait recursion S=y−3v+(1−y)(1−v)S′. They give
```
R  = [(61/20)v−2xη]/[1+2(1+x)η],
R′ = [x(1+3w)/(1−4x) + v(1/20−η)/(1−v)]/(1+w).
```
For 0<v<1 and 0≤w≤11/50 rational polynomial inequalities give R≥2v and R′≤1/8. Thus all full dates after the first have v≤1/16. The same derivative estimate and F_v(1/10)≤1/10 for v≤1/16 now give W≤1/10 after the first full date. For 0<v≤1/16 and 0≤w≤1/10 rational arithmetic gives R′≤15R/16. Between full dates R remains constant. Consequently the sum of R over all subsequent full dates is bounded by a geometric series. The same holds for v≤R/2 and x≤2v. Neither X nor V has infinite cumulative hazard. Then the probability of any non-Y first participant tends to zero at late restarts, contrary to the uniform d_Y bound on K. This proves the asserted strict floor at t=100.

## The threshold on the whole axis

First classify the sure rows with u=0 at a continuation consisting of best-response caps. If X or V is sure, the sure tests already ruled out by the t=100 census are still necessary. All on-path stage offers are independent of t, the lower bound min Q of a sole sure X or V is independent of t, and with multiple sure agents no continuation matters. If Y alone is sure, X and V have wait-minus-quit values 2−3v and −2+8x respectively. Their only stage equilibrium has x=1/4,v=2/3: neither can be on its boundary, as the other then strictly chooses the opposite required corner. U strictly prefers to wait since every passive cell it faces has value at least 2 and every joining alternative at most 9/5. Y's on-path native payoff is zero; its native Wait contribution is 29/12 and its rival survival is 1/4. Thus its refusal value must be at most w₀=−29/3 in the child.

There is a punishment capping Y at w₀ exactly when some row with U sure and X,V hazards x,v∈[0,1] satisfies
```
P₁=−2+4x−2v−60xv ≤ w₀,    Q₁=t(1−x)(1−v)+x(1+v) ≤ w₀.
```
Such a row absorbs at once, so is sufficient. For necessity, if no such pair exists, consider the two offers against an arbitrary one-date opponent row evaluated at child w₀. At u=0 the Quit offer is zero and the Wait offer is at least w₀: all nonempty passive cells without U are ≥−2 and Never is valued at the trial continuation on this one date. At u=1 the offers are exactly Q₁,P₁. If both offers at any u were ≤w₀, then u>0, and the affine dependence on u would give both offers ≤w₀ at u=1, a contradiction. Hence the maximum strictly exceeds w₀ throughout the compact cube, uniformly. Choose w₁>w₀ sufficiently close that the same one-stage maximum at child w₁ is at least w₁ throughout, and w₁<−1. Against any fixed opponent calendar Y can choose a maximizing pure action at each date and guarantee w₁ by iteration: on eternal survival the actual native Never payoff −1 exceeds this lower bound. Thus every child best-response cap strictly exceeds w₀. This argument uses only the opponents' independent hazards, as in the punishment definition.

The passive test requires v≥(23+12x)/(6+180x). Feasibility with Q₁≤w₀ requires t<0 and x,v<1. For these t, Q₁ increases in v, so use the smallest permitted v. The joint test reduces to t≤T(x) for some 17/168<x<1, where
```
T(x)=(192x²+1769x+58)/[(x−1)(168x−17)].
```
This function tends to minus infinity at both ends. Its derivative has the sign of −(110904x²+4320x−13601). The unique maximizer in the interval is x*=−90/4621+√378267726/55452, and substitution gives T(x*)=τ. For t≤τ prescribe the sure Y opening above, with U quiet. After refusal use the indicated absorbing punishment (U sure, x=x*, v=(23+12x*)/(6+180x*)). This gives exact terminal equilibrium. Every unilateral replacement absorbs by date two, giving the same original uniform payoff. The equilibrium's first-exit law has D_U=0, even though the off-path punishment uses U.

For t>τ there is no sure limiting row with U quiet at any feasible child cap, as proved above. Suppose nevertheless that e+D_U→0. A restart while survival is bounded below still satisfies this same smallness condition. Thus at all such roots the hazards are uniformly bounded by 1−γ: otherwise the limiting row would be Nash at a bounded limiting child cap and would be a sure row with u=0. For Y the uniform w₁ bound just proved applies to the limiting cap, and for X,V the guaranteed min Q bounds apply. This gives one fixed γ for all sufficiently small restart errors and U incidences. The late-tail Never bound from the anchor requires only a positive own level.

We show that changing t to 100 has a negligible effect on any Y replacement. Choose θ>0 with θ≤1/4 so small that 6Mθ<1/2 for an original reward bound M at the fixed t. On a low-regret calendar with small U incidence, cut a block just after full survival first falls below θ, restarting the normalizations at the block start. All its rows are proper as above and its remaining survival is ≥b₀=θγ⁴. On this block Y's rivals must have survival ≤1−θ. Otherwise the total probability of a first exit by Y alone is at least 1−2θ by coupling the event no rival ever attempts to quit on the block with the event of any exit. V then receives prescribed payoff within 4Mθ of its singleton-Y payoff. Immediately quitting against the first Y hazard h and no other rivals improves on that singleton-Y payoff by 1+h; coupling away the other rivals at the first date costs at most 2Mθ. This contradicts vanishing regret. For every fixed k iterate k such blocks by restarting, retaining full survival ≥b₀^k and Y-deleted survival ≤(1−θ)^k. Total U hazards on this prefix are ≤D_U/b₀^k. Thus, even after deleting Y, the chance U is among the first rival quitters tends to zero: take the sequence limit on the prefix and then k→∞. This also bounds that probability under every Y replacement coupled to the same opponent clocks. The sole changed reward at YU affects only Y. Its expected change under prescribed play is at most |t−100|D_U and under all Y replacements is uniformly negligible by the deletion bound. The same profiles would therefore violate the proved t=100 floor. This proves the theorem on the full axis.

At the anchor the three other identity exclusions can be read directly from the signed deletion test in [All four first quitters, interior payoffs and the minimum period for a uniform target](../exports/ALL_FOUR_FIRST_QUITTERS_AND_UNBOUNDED_JOINT_DATES.md). With exactly Y,U,V participating, Y's passive payoffs on U,V,UV are −2,−2,−4, all negative and no larger than the corresponding joining payoffs. With exactly X,U,V participating, V's passive payoffs on X,U,XU are 1,1,2, all positive and no smaller than the corresponding joining payoffs. With exactly X,Y,U participating, X's passive payoffs on Y,U,YU are 1,3,5 and satisfy the same positive tests. The fixed-pair theorem already excludes any smaller set. The no-sure high-survival argument in the signed deletion result converts each positive incidence into positive singleton mass on a limiting law. Compactness gives a positive minimum for all four at sufficiently small regret. Only the U threshold is asserted along the full axis.

## The phase boundary when the other 59 rewards vary

Use t and the other 55 native P,Q entries together with the four own singleton levels as independent affine coordinates for the 60 original rewards. On a neighborhood of the displayed point in these other 59 coordinates there is a real-analytic function τ of those coordinates. With the other coordinates fixed anywhere in that neighborhood and t ranging over **all** of ℝ, an exact equilibrium with D_U=0 exists at and below this threshold, and inf(e+D_U)>0 above it.

Here is its raw formula. With Y sure, U quiet and V's hazard fixed at k=0 or 1, let A_k be X's native wait-minus-quit offer. Similarly let B_k be V's wait-minus-quit offer when X has hazard k. Their signs remain A₀>0>A₁ and B₀<0<B₁. Their unique stage equilibrium on the X,V pair has v*=A₀/(A₀−A₁), x*=B₀/(B₀−B₁). U's strict quiet comparison persists. Define w₀ as Y's forced-Quit offer minus its passive absorbing contribution at (x*,v*) with U quiet, divided by (1−x*)(1−v*). With U sure and X,V hazards x,v, write P₁(x,v) for Y's passive offer and t(1−x)(1−v)+B(x,v) for its forced offer. Then
```
τ = max {(w₀−B(x,v))/[(1−x)(1−v)] : 0≤x,v<1, P₁(x,v)≤w₀}.
```
There are feasible points strictly inside the square with P₁<w₀, as at the displayed table (raise v slightly at the maximizer). The three coefficients of B on outcomes containing X or V stay strictly above w₀. Hence its value at x=1 or v=1 is uniformly above w₀, and the quotient tends uniformly to minus infinity near those boundaries. Its maximum is finite and attained. At u=0 the forced offer, all nonempty passive entries, and the native Never reward −s_Y remain strictly above w₀. The previous Bellman barrier proves that precisely t≤τ permits a refusal punishment at w₀. The sure X/V statuses with U quiet continue to fail: the closed necessary signs with the sole sure player's min Q bound depend continuously on these 59 entries and are independent of t, because Y is never the only sure player in these statuses. Compactness and the anchor census preserve the exclusions. The anchor U floor at fixed t=100 is open in the raw rewards. The positive solo-Y blocker margin used for the deletion argument also persists, so the same transfer to 100 proves the upper-side floor throughout this tube. On the lower side the same two-date punishment gives an exact equilibrium whose first exit excludes U.

For analyticity, let (x₀,v₀) be the unique optimizer at the displayed table. Both coordinates lie in (0,1). At this point ∂P₁/∂v=−2−60x₀<0. The derivative in v of t(1−x)(1−v)+B at t=τ is strictly positive, so the derivative of the quotient in the maximum formula is strictly negative. These signs persist locally. Every maximizing pair for nearby parameters tends to (x₀,v₀): boundaries with denominator tending to zero have already been uniformly excluded, and feasible points arbitrarily close to (x₀,v₀) with strict passive inequality remain feasible under perturbation. Compactness and continuity would otherwise give a different maximizing pair at the center. Thus every nearby maximum has active constraint P₁=w₀, which determines v analytically in x and the parameters. After substitution, the derivative in x has a simple zero at x₀, as the displayed quadratic numerator of T′ shows. The implicit function theorem gives the unique nearby critical point and the real-analytic threshold.

## Verification of the five rational inequalities

The following standalone Python/SymPy checker uses tensor Bernstein coefficients. Dividing by v in the two strict-domain tests removes the trivial zero at v=0. Denominators are strictly positive on the open physical domain: nonnegative controls plus the positive origin control give strict positivity in the interior, and the explicit factors also apply on w=0. The only vanishing denominator boundary is the excluded v=1 when evaluating R′.

```python
from math import comb
import sympy as s
from itertools import product
F=s.Rational
v,w,u,z=s.symbols('v w u z')
x=2*v/(1+21*v)
eta=s.factor((x+(1-x)*w)/(2*(1-4*x)))
V=s.factor((1+2*x)*eta/(1+eta))
r=s.factor((F(61,20)*v-2*x*eta)/(1+2*(1+x)*eta))
rp=s.factor((x*(1+3*w)/(1-4*x)+v/(1-v)*(F(1,20)-eta))/(1+w))
def check(f,vmax,wmax,vmin=0):
 p,q=s.factor(f).as_numer_denom()
 # rational domain is the open v<1: allow zero endpoint in denominators.
 def coeff(p):
  a=s.Poly(p.subs({v:vmin+u*(vmax-vmin),w:z*wmax}),u,z,domain='QQ')
  m=max(0,a.degree(u));n=max(0,a.degree(z));A=a.as_dict()
  return [sum(c*F(comb(i,k),comb(m,k))*F(comb(j,l),comb(n,l)) for (k,l),c in A.items() if k<=i and l<=j)
          for i,j in product(range(m+1),range(n+1))]
 cp,cq=coeff(p),coeff(q)
 if max(cq)<=0: cp=[-b for b in cp];cq=[-b for b in cq]
 print('degrees',s.degree(p,v),s.degree(p,w),'bound',min(cp),min(cq),flush=True)
 assert min(cp)>=0 and min(cq)>=0 and cq[0]>0
def upper(t,b):
 print('upper',t,b);check(b-V.subs(w,b),t,F(1))
if __name__=='__main__':
 upper(1,F(11,50))
 check(s.cancel(r/v)-2,1,F(11,50))
 for k in range(16): check(F(1,8)-rp,F(k+1,16),F(11,50),F(k,16))
 upper(F(1,16),F(1,10))
 check(s.cancel((F(15,16)*r-rp)/v),F(1,16),F(1,10))

```
