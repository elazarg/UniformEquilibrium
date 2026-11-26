# Global one-date minimizers can lie on an isolated observer-response oval

Ordinary mathematics; not checked in Lean. The complete proof has an
[independent review](../feedback/FINITE_PROPER_ROOT_OBSTRUCTION__BY_REVIEW.md).
This refutes a finite-clock selection lemma, including its small-error version. It is NOT
a positive-gap quitting game or an exclusion of actual Fin4 case F. The
explicit calibration at the end has an absorbing infinite-clock Nash law.

## Exact construction and conclusion

Fix any invertible zero-diagonal four-by-four singleton matrix Gamma with
v=Gamma^-1 e_0>0. Put alpha=v_0, S=sum_i v_i and k=S-alpha. Choose

    0<delta<=min(1,17 alpha/(9 S^2)),
    r=9 delta/68, M=max_(i,j)|Gamma_ij|,
    K>36(M+4 delta+r).

Let p,q1,q2,q3 be the four probabilities of quitting at date0; otherwise
players choose literal Never. Write x=q1,y=q2,z=q3. Prescribe the following
joining-advantage polynomials, each independent of its owner's probability:

    G0=delta[-y-(27/44)xz+(10/11)z],
    G1=2p-y-z,
    G2=x-z,
    G3=-[(p-1)xy+(2/9)p+(1/8-p/4)(x-y)].             (1)

These specify an actual finite reward table while leaving Gamma literally
unchanged. For nonempty D excluding i, put Z_i(D)=Gamma_ij if D={j}, and
Z_i(D)=K if |D|>=2. Then put

    Z_i(D union{i})=Z_i(D)+G_i(1_D).

Own singletons, live play and Never pay zero. Because G_i is multiaffine
and G_i(0)=0, its expected joining advantage is exactly (1). All sixty
rewards are specified, with private independent randomization only.

Let N be the ENTIRE one-date three-observer Nash correspondence as the
pivot probability p varies over[0,1]. It includes all proper and sure
observer laws. Let P_i be the passive expected payoff. Every pure later
deadline and Never pays P_i, so the full behavioral quantities are exactly

    e_i=P_i, B_i=P_i+max(G_i,0), U_i=P_i+q_i G_i,
    d_i=max(G_i,0)-q_i G_i,
    nu=(1-p)(1-x)(1-y)(1-z), J=d_0+r nu.             (2)

Thus N is defined by d_1=d_2=d_3=0, using full responses, not only date0.

The following properties hold.

1. N has exactly two connected components. One component E meets both
   p=0 and p=1. The other O is a smooth compact oval wholly inside(0,1)^4.
2. The one-date absorbing observer-Nash minimum is exactly

       m1=min_{N,nu=0}d_0=9 delta/34=2r.

3. Every GLOBAL minimizer of J over ALL of N lies on O, and

       0<mu1=min_N J<delta/204,
       inf_E J>=delta/162>delta/204.

   Every minimizing profile is strictly ALL-END at the pivot, ALL-END at
   the observers, and has every full cap and Never mass positive. It has
   B_0>mu1, U_0>r nu and N_0<1/(1+rS).
4. Every direct inverse-axis replacement and every inverse-axis append
   after any minimizing profile fails to improve J.
5. The global-minimum isolation persists for sufficiently small allowed
   observer regret. Within this one-date controller class, allowing a
   vanishing positive observer error does not produce a path from the
   minimizing oval to a component meeting p=0 or p=1.

Consequently global minimization over all observer-response components
alone does NOT select a spanning component, even with the displayed
finite-source counterparts of the known source and axis restrictions.

## Complete observer correspondence

At an interior observer equilibrium, G1=G2=G3=0 gives

    x=z=p+t, y=p-t,
    g(p,t)=(1-p)t^2+(1/4-p/2)t-(1-p)p^2+2p/9=0.     (3)

The discriminant in t is

    (576p^4-1152p^3+740p^2-164p+9)/144.

Its four roots are 1/2 plus or minus each of
sqrt((31+sqrt(385))/288) and sqrt((31-sqrt(385))/288).
Put

    a=1/2-sqrt((31-sqrt(385))/288), b=1-a.

Then 1/4<a<1/2<b<3/4. The two feasible interior branches for p in[a,b]
join at their folds and form O. They are wholly inside the probability
cube. The only other feasible all-mixed branch is an arc for
0<p<1/18, joining AllNever to (p,x,y,z)=(1/18,0,1/9,0).

Here are exact boundary checks establishing these assertions without a
numerical root census:

    g(p,-p)=p(18p-1)/36,
    g(p,p)=-p(18p-17)/36,
    g(p,p-1)=(54p^2-73p+27)/36>0,
    g(p,1-p)=(90p^2-127p+45)/36>0.                  (4)

The last two quadratics have negative discriminants. Together with the
four discriminant roots, these evaluations locate every possible entry
or exit from -min(p,1-p)<t<min(p,1-p). At p=0 the feasible interior-limit
root is t=0; the other root is -1/4. The low-p feasible root leaves through
t=-p at p=1/18, before the first discriminant fold. At the two central
folds the roots are strictly inside the cube. On the high-p real-root interval beyond the fourth discriminant zero,
both roots lie outside; at p=1 the only algebraic root is t=8/9.
This accounts for all all-mixed solutions.

The oval is smooth. Away from a discriminant fold, g_t is nonzero; at a
fold, the discriminant has a simple root, so g_p is nonzero. Its two
fixed-p observer Jacobian determinants are -g_t and hence have opposite
signs. These roots can disappear in interior folds; their component has
no compulsory connection to either parameter boundary.

For completeness the entire remaining component E consists precisely of:

* p=0,x=y=0,0<=z<=1;
* the all-mixed origin arc just described, including its two endpoints;
* x=z=0, 1/18<=p<=1/2,
  2p<=y<=min(1,16p/[9(1-2p)]), with y=1 at p=1/2;
* p=1/2,y=1,z=0, 0<=x<=2/9;
* y=1, 1/2<=p<=9/11,
  z=2p-1, x=(34p-9)/(63-54p);
* p=9/11,x=y=1, 0<=z<=7/11;
* 9/11<=p<=1,x=y=1,z=0.

To check completeness, split according to y=0, 0<y<1, or y=1 using
G2=x-z. If y=0, Nash requires x<=z; the other inequalities leave only
the p=0 segment. If 0<y<1, x=z; x=z=0 gives the displayed strip,
x=z=1 is excluded by the last positive quadratic in(4), and the interior
case is (3). If y=1, Nash requires x>=z. Then x=0 gives the strip top;
0<x<1 gives z=2p-1 and the displayed rational branch or its endpoint
segment; x=1 gives the last two pieces. Their remaining inequalities
reduce to 54p^2-73p+27>0 and the displayed parameter intervals.

These pieces attach in their printed order, so E is connected and spans
p=0 to p=1. O is a closed interior component separated from E by a positive
distance; the above enumeration shows there is no third component.

## Pivot objective and the global selection

On O, z=x. The curve in x,y is

    F(x,y)=36x^2 y-9x^2+36xy^2-72xy+17x+9y^2-y=0.

Set ell(x)=10x/11-27x^2/44. Exact substitution gives

    F(x,ell(x))
      =3x(3x-2)^2(972x^2-2925x+2596)/1936.           (5)

The last quadratic has discriminant -1537623, and is strictly positive.
Thus G0 can vanish on O only at x=2/3,y=1/3, whose p=1/2. Since removing
one point from the oval leaves it connected, its sign is constant away
from this point. At the other p=1/2 root, x=1/3,y=2/3, G0/delta=-19/44.
Therefore G0<0 everywhere on O except the unique zero point. The entire
oval is ALL-END, and its witness has nu=1/27 and J=r/27=delta/204.

The witness itself is not minimizing. Locally parameterize O by x there.
Implicit differentiation gives y'=1/11, p'=6/11,
(G0/delta)'=0 and nu'=-53/198. Hence J'=-53r/198<0. Consequently
mu1<delta/204 and every global minimizer on O has G0<0 strictly.

Now bound J on every piece of E. The p=0 segment has
J=r+(10delta/11-r)z>=r. On the origin arc all q_i<=1/9 except p<=1/18,
so nu>1/2 and J>=r/2. On the strip, G0=-delta y, whence
J>=delta p y>=delta/162. Every remaining piece has y=1,p>=1/2,
x>=z and 0<=z<=7/11<2/3. Therefore

    G0/delta <= -1-(27/44)z^2+(10/11)z <= -2/3,
    d_0>=delta/3.

Since r/2=9delta/136>delta/162, this proves inf_E J>=delta/162.
Strict positivity of mu1 follows from compactness: J=0 would require
both nu=0 and d_0=0, and all absorbing points have positive debt.

The absorbing points of E are exactly its p=0 endpoint z=1, the strip's
y=1 part with p>=9/34, and the subsequent y=1 pieces. Their debts are
respectively 10delta/11, delta p>=9delta/34, and at least delta/3.
Equality is attained at p=9/34,x=z=0,y=1. O contains no absorbing point.
This proves m1=9delta/34.

## Remaining source scalar checks and inverse-axis comparisons

Every coordinate q_i on O is >1/6. For x this follows because

    g(p,1/6-p)=(60p^2-34p+5)/72>0,

and no oval point can cross x=1/6. For y use

    g(p,p-1/6)=-(12p^2-14p+1)/72>0 on[1/4,3/4].

The oval contains the displayed witness with x,y>1/6 and is connected.
Thus each passive payoff obeys P_i>=-M+K/36>4delta+r. Since
|G0|<=111delta/44, all minimizing caps are positive, B_0>mu1 and
U_0>r>=r nu. Moreover N_0=1-p<3/4, whereas
r<=alpha/(4S^2) gives rS<1/4 and 1/(1+rS)>4/5.

For inverse-axis block E_T set a=1/k,c=S/k,z=exp(-kT). Its observer
payoffs and full caps are zero, B_0(E_T)=a(1-z), U_0(E_T)=(1-z^c)/S,
and nu(E_T)=z^c. After a minimizing profile, all original observer
comparisons are retained. With s=nu and lambda=1/N_0, exact grafting gives

    Delta J/s=lambda a(1-z)-(1/S+r)(1-z^c)
      >=[lambda-1-rS](1-z)/k>0 for T>0.

Here lambda>4/3 and 1+rS<5/4. The absorbing endpoint is included.
Direct replacement by an axis block has minimum

    f(r)=alpha/(Sk)[1-(1+rS)^(-k/alpha)]
       >=r-r^2 S^2/(2alpha)>=7r/8>mu1.

The lower bound follows by integrating
f'(r)=(1+rS)^(-S/alpha)>=1-rS^2/alpha. Thus all complete axis families
are priced, not only their first variations.

## Positive error does not repair the one-date component selection

Let R=max(d_1,d_2,d_3), a continuous nonnegative function on the compact
cube. Its zero set is exactly E union O. Set rho to one third of the smaller of dist(O,E) and the distance from
O to the cube boundary; rho>0. Let U={q:dist(q,O)<=rho}. On its boundary
define

    epsilon_boundary=min_(boundary U) R>0.

Every continuous one-date profile path from O to E or to p=0 or1 crosses
this boundary and hence incurs observer regret at least epsilon_boundary.
Thus allowing observer error tending to zero cannot cross these components,
even if temporary increases of J are allowed.

There is also a global near-minimum version. Put A=delta/204,
B=delta/162 and gamma=(B-A)/4=7delta/22032. The compact set

    L={q outside interior U : J(q)<=A+gamma}

contains no zero of R, because every exact observer equilibrium there lies
in E and has J>=B. If L is nonempty set epsilon_value=min_L R>0; otherwise
choose epsilon_value=1. For epsilon<min(epsilon_boundary,epsilon_value),
every epsilon-observer-Nash profile with J<=A+gamma lies in interior U.
In particular every GLOBAL minimizer over R<=epsilon does so, since the
exact witness remains feasible. These are fixed positive separations in
one finite controller class, not estimates uniform in calendar length.

## An explicit actual absorbing escape beyond the one-date controller

Take the literal matrix

    Gamma=[0,1,4,-5; 1,0,-2,-1; -1,1,0,3; 2,-1,-4,0],
    delta=1/4, K=1000.

Its inverse column0 is (1,2/5,2/5,1/5), so alpha=1,S=2 and the displayed
bounds hold. Players1 and3 now quit at EVERY natural date independently
with hazards8/9 and1/2; pivot0 and observer2 always Continue. The active
values are u1=u3=-1 and both active actions tie exactly. The absorption
probability per date is17/18. The quiet values and immediate Quit values are

    u0=(8K+3)/17, Q0=(8K+3)/18+2delta/11,
    u2=(8K+11)/17, Q2=(8K+18)/18.

Both quiet comparisons are strict at the displayed K,delta. Every later
pure deadline equals the corresponding discounted mixture of u_i and Q_i;
Never gives u_i. Thus these inequalities cover every complete deviation.
This is an actual absorbing full native Nash profile, so the TRUE
arbitrary-calendar absorbing minimum is0. In contrast the one-date
minimum is m1=9/136>0.

The example defeats the finite global-minimum-to-spanning-component lemma,
including its vanishing-error version. It does not defeat unrestricted
whole-calendar continuation. Extra dates are essential to any application
of that approach; the required link to the true positive-gap global source
remains unproved. No row-distinct genericity claim or arbitrary-calendar
component isolation is asserted here.

Sources inspected: the [residual-source partition](CODEX_COORDINATOR__FIN4_RESIDUAL_PARTITION.md)
and [retained-axis construction](CODEX_VARIATIONAL_ESCAPE__CONSTRAINED_REPAIR_AND_CONE_GRAFT_OBSTRUCTION.md);
the [component/Bellman distinction](CODEX_TARSKI_PREMIUM__GLOBAL_OUTSIDE_MINIMUM_AND_NASH_COMPONENT_RETURN_COST.md);
quittingContinuationBestResponseValue_rootThenContinuation_eq_max
(UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean); and
not_exists_uniformEquilibriumPayoff_iff_exists_terminalExploitabilityGap
(UniformEquilibrium/Quitting/Terminal/ExploitabilityGap.lean).
The remaining task is a replacement using the true arbitrary-calendar
global source; neither finite minimization nor a small finite-controller
observer error supplies that attachment. No Lean check is claimed.
