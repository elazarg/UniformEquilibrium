# Uniform equilibrium on a central negative wedge

This packet constructs an exact finite core for an unbounded two-parameter
reward region and proves a fixed uniform-equilibrium payoff against every
unilateral behavioral replacement. It is ordinary mathematics, not checked
in Lean. Arbitrary signed four-player quitting games remain open.

## 1. Raw statement

There are four players0,1,2,3. At each live date they independently choose
Continue or Quit. The first nonempty quitting coalition D absorbs and pays
r(D); live play and literal AllNever pay zero. Write kappa_i=r_i({i}) and
Z_i(D)=r_i(D)-kappa_i for nonempty D only. Native own-singleton rewards are
zero. A string such as123 denotes the coalition{1,2,3}. Fix the native rewards

```
D       Z0     Z1     Z2     Z3
0        0      2      2     -1
1        3      0     -2     -2
2       -1      1      0      1
3        3     -3     -1      0
12     -12     -K      p     -6
13       2   -100     -1      0
23      -6      9      3   -100
123     -8     11      2      1
```

All seven row0 rewards on nonsingleton coalitions containing0 are <=0.
The other21 coordinates on those coalitions and all four original
own-singleton levels are arbitrary independently.

**Theorem.** There is a finite universal constant C>=100 such that
every game in this family with

    p<=0,       K>=C(1+|p|/6)

has a uniform-equilibrium payoff against unrestricted behavioral deviations.
The constant is independent of every unrestricted reward and singleton level.
The proof is an existence proof for C, not a numerical bound on C.

Moreover, there is an open radius epsilon0>0 such that the SAME conclusion
holds when all26 nontrivial displayed entries other than Z1(12)=-K and
Z2(12)=p are perturbed independently by less than epsilon0. Native own
singletons stay zero by definition; the seven upper bounds,21 unrestricted
entries, and four arbitrary singleton levels are unchanged. One C works
throughout this neighborhood. Sections2–7 prove the reference-coefficient
case; Section8 proves the uniform perturbation statement.

## 2. Compactification and exact equations

Let delta=3/4. For N core roots put t=delta^(N-1). Compactify the negative
companion reward by

    h=6/(6-p) in(0,1],
    alpha=t h Lambda=1/K,
    beta=-6t(1-h)Lambda=alpha p.

The endpoint h=0 is an auxiliary compactification only; every physical game
has h>0. Lambda will stay in a fixed compact positive interval. All rational
expressions below are analytic uniformly for h in[0,1] and small |t|, because
p occurs only through beta and 1/K only through alpha.

A triple123 root has physical hazards (0,alpha Y,alpha Z,w). Its active
current values are (Q1,Q2,alpha q3), and its required active successors are
(F1,F2,alpha f3), with

```
Q1=-Z-100w+(1+111alpha)Zw,
Q2=beta Y+3w-(beta+alpha)Yw,
q3=-Z(100-101alpha Y),
F1=[-(1+alpha)Z-97w+(1+100alpha)Zw]
       /[(1-alpha Z)(1-w)],
F2=[(beta+2alpha)Y+4w-(beta+3alpha)Yw]
       /[(1-alpha Y)(1-w)],
f3=[2Y-101Z+106alpha YZ]
       /[(1-alpha Y)(1-alpha Z)].
```

These formulas follow by enumerating the opponents' coalitions. Introduce

```
theta=w/(1+3w),
J=[(1-w)Z+109w]/(1+3w),
w=theta/(1-3theta),
Z=(J-109theta)/(1-4theta).
```

At t=0 the first two interface identities F1=nextQ1 and F2=nextQ2 become
exactly J_next=J and theta_next=theta/delta, regardless of Y,Y_next.

The third interface solves backwards without a small denominator. With
R=Z_next(100-101alpha Y_next), it is

    Y=[101Z-R(1-alpha Z)]
         /[2+106alpha Z-alpha R(1-alpha Z)].           (2.1)

The final successor has third coordinate0 precisely when

    Y_last=101Z_last/(2+106alpha Z_last).              (2.2)

For a supplied sequence (J_j,theta_j), equations (2.1)-(2.2) define all Y_j
backwards. On the compact neighborhoods below, their values and the first
two derivatives of this map on arrays with the sup norm are uniformly
bounded independently of N. Indeed the derivative of (2.1) with respect to
Y_next is O(alpha)=O(t), all other partial derivatives are bounded, and the
resulting geometric series is uniformly summable.

To express the remaining interfaces exactly, form the current Z,w,F1,F2
from (J,theta,Y), supply Y_next, and put

```
v=(F2-beta Y_next)/(3-(beta+alpha)Y_next),
z=(-F1-100v)/(1-v-111alpha v),
theta_bar=v/(1+3v),
J_bar=((1-v)z+109v)/(1+3v).
```

The divided differences

    f=(theta_bar-theta/delta)/t,
    g=(J_bar-J)/t                                      (2.3)

have removable analytic extensions at t=0. Their partial derivatives are
uniformly bounded on a fixed compact neighborhood. The exact interfaces are

    theta_next=theta/delta+t f,
    J_next=J+t g.                                     (2.4)

At theta=t=0 and Y=Y_next=J/2, direct differentiation gives

    f=h Lambda J/3.                                   (2.5)

## 3. Uniform construction of finite orbits

Prescribe J_0=J_* near3/4 and terminal phase theta_(N-1)=theta_*, where
theta_* belongs to a fixed small open neighborhood of

    I=[9/1744,3/436].

Take h in[0,1] and Lambda in a fixed compact positive interval containing
all theta_*/(3/4). Use reference arrays

    J_j^0=J_*,    theta_j^0=delta^(N-1-j)theta_*.

For every sufficiently large N, the exact interface system has a unique
solution near these reference arrays, uniformly in all the parameters. To
prove this, compute Y backwards by (2.1)-(2.2), then f_j,g_j by (2.3), and
iterate the following map on the J,theta arrays:

```
J_j(new)=J_*+t sum_(k<j)g_k,
theta_j(new)=delta theta_(j+1)-delta t f_j  (j<N-1),
theta_(N-1)(new)=theta_*.
```

On a box with J-radius C1 Nt and theta-radius C2 t about the reference
arrays, the f,g,Y maps and their derivatives have bounds independent of N.
Choose C1>sup|g| and C2>delta sup|f|/(1-delta). This map preserves the box.
Its sup-norm derivative has row norm bounded by

    max(C Nt,delta+C t)<1

for N large. Banach therefore supplies an actual finite orbit. The same
bound on a fixed larger convex neighborhood proves local uniqueness there.
The exact cumulative and backwards Green formulas give

```
J_j-J_*=t sum_(k<j)g_k,
theta_j-theta_j^0=-t sum_(k=j)^(N-2)delta^(k-j+1)f_k,
```

and hence

    |J_j-J_*|<=C jt,
    |theta_j-theta_j^0|<=C t.                         (3.1)

All these estimates hold in C1 with respect to (J_*,theta_*,Lambda,h).
For detail, the parameter derivatives of the contraction's solution are
uniformly bounded because its inverse derivative has a geometric bound.
Differentiating the two exact formulas just displayed then gives Cjt and
Ct for the derivatives of their differences. No differentiation with respect
to the discrete N is used.

For j<=N-3, substitution in the rational Z and backwards Y formulas gives

```
|Y_j-J_*/2|+|Y_(j+1)-J_*/2|
 <=C[t delta^(-j-1)+(j+2)t],
|f_j-h Lambda J_*/3|
 <=C[t delta^(-j-1)+(j+2)t].                         (3.2)
```

The same inequalities hold for the first parameter derivatives after
subtracting the derivatives of the displayed limiting quantities. The last
two f values and their derivatives are merely uniformly bounded. Multiplying
by delta^(j+1) and summing proves the crucial scaled-entrance estimate

    sum_(j=0)^(N-2)delta^(j+1) f_j -> h Lambda J_*      (3.3)

in C1, uniformly in all the parameters. The error is O(Nt): each first term
in (3.2) contributes O(t), the j-weighted geometric sum is O(t), and the last
two weights are O(t). Thus no uncontrolled orbit error is divided by t.

## 4. Exact entrance and outer return equations

The entrance condition Q2(first)=0 is exactly

    theta_0/t=6(1-h)Lambda Y_0
                 /[3-t Lambda(25h-24)Y_0].

Backwards summation of (2.4) gives theta_0/t=theta_*−sum delta^(j+1)f_j.
Thus the exact nonsingular entrance equation is

    L_N=theta_*-sum delta^(j+1)f_j
          -6(1-h)Lambda Y_0/[3-t Lambda(25h-24)Y_0]=0. (4.1)

Its uniform C1 limit, including h=0 and h=1, is

    L_infty=theta_*-Lambda J_*.                        (4.2)

Let the final successor be E=(E0,-x,E2,0), where x=-F1(last), E2=F2(last).
E0 is initially free. Propagate row0 backwards through the roots using

```
G(y,z,w;r)=3y-z+3w-14yz-4yw-8zw+13yzw
                     +(1-y)(1-z)(1-w)r,
y=alpha Y, z=alpha Z.
```

Let C0 be its entrance value, C1=Q1(first), C3=alpha q3(first). With C2=0,
set

```
b=C0/(1+C0), B1=(C0+C1)/(1+C0), B3=(C0+C3)/(1+C0),
a=B3/(1+B3), A1=2a+(1-a)B1, A2=2a.
```

The two outer return equations are

    H1=A1(3-E0)-3(E0-x)=0,
    H2=A2(3-E0)-3E2-E0=0.                             (4.3)

All are actual finite-core quantities. Their uniform C1 limits, writing
theta=theta_*, are obtained from

```
C0=12theta+(1-4theta)E0, C1=-J_*, C3=0,
x=(J_*-12theta)/(1-4theta), E2=4theta/(1-4theta).
```

Indeed each non-solo3 row0 term is O(alpha)<=O(t). The reference solo3
survival telescopes exactly to

    product_(j=0)^(N-1)(1-w_j^0)
      =(1-4theta_*)/(1-3t theta_*).

Equations (3.1) and their derivative versions show the perturbed aggregate
has the same C1 limit; even the coarse total bound O(N^2 t) tends to0.

For every theta in the chosen neighborhood and h in[0,1], the limiting
three-equation system L=H1=H2=0 has the solution

```
J_*=3/4,
E0=(5-48theta)/[4(1-4theta)],
Lambda=theta/(3/4),
C0=5/4, C1=-3/4, A1=6/7, A2=5/7.
```

At this solution the Jacobian of (H1,H2) with respect to (J_*,E0) is

    [ -5/(8theta-2)    -45/14 ]
    [       0         -10/7  ],

with nonzero determinant25/[7(4theta-1)]. The limiting H equations do not
depend on Lambda, while partial_Lambda L=-J_*=-3/4. Thus the full Jacobian
is uniformly invertible on the compact parameter rectangle.

Uniform C1 convergence and the finite-dimensional implicit-function theorem
therefore produce unique C1 branches J_N(theta,h), E_N(theta,h),
Lambda_N(theta,h), uniformly close in C1 to these limits, for every sufficiently
large N and the whole rectangle. A uniform local contraction on finitely many
parameter neighborhoods proves this statement; uniqueness identifies the
overlaps. Every point now supplies an exact finite core for physical h>0 at

    K_N(theta,h)=1/[t h Lambda_N(theta,h)],
    p=-6(1-h)/h.

The derivative of Lambda_N in theta is positive, uniformly for N large,
since its limit is4/3. Hence K_N is strictly decreasing in theta.

## 5. Guards and exact boundaries

The limiting final scaled second hazard and wash margin are

    Z_last=(3/4-109theta)/(1-4theta),
    E2-3x/100=(436theta-9/4)/[100(1-4theta)].           (5.1)

Their simple zeros are theta_plus=3/436 and theta_minus=9/1744, with

theta_minus=delta theta_plus. Uniform C1 convergence yields unique nearby
boundary phases theta_N^+(h) and theta_N^-(h), where respectively Z_last=0
and E2-3x/100=0. Between them both quantities are nonnegative. The two
boundaries are continuous in h, including the auxiliary endpoints.

Every remaining guard is strict uniformly in h for N large:

* For j<N-1, reference Z_j is bounded below positively even at theta_plus,
  since theta_j<=delta theta_plus. The reference sequence Z decreases, so
  Y_j=(101Z_j-100Z_(j+1))/2>=Z_j/2>0. Equations (3.1) preserve these strict
  scaled signs. Final Y has exactly final Z's sign by (2.2).
* For physical h>0, first y=alpha Y_0>0. The exact entrance equation gives
  w_0>=0, with equality exactly at h=1 (p=0). Positivity of later w can be
  proved without an asymptotically small margin. When y,w>=0 and <1, row2's
  passive numerator is P2=-2y-w+2yw<=0, strictly negative if y>0 or w>0.
  At the first root Q2=0, so its F2=(Q2-P2)/[(1-y)(1-w)]>0. The next
  w=(F2-beta Y_next)/[3-(beta+alpha)Y_next]>0 because beta<=0 and Y_next>=0.
  Inductively Q2=previousF2>0, the same argument gives F2>0, and every
  later w is positive. The upper hazard bounds follow uniformly from
  bounded Y,Z, alpha<=O(t), and the small limiting w values.
* At p=0, first w=0, so player3 is quiet there. Its exact current Quit
  value and required successor still obey the row3 interface, hence it is
  indifferent; no strict activity assumption is used.
* The outer limits give C0=5/4,C1=-3/4,C3=0, b=5/9,B1=2/9,B3=5/9,
  a=5/14. Thus both deleted-opponent clocks remain proper. On the compact
  legal phase interval, 0<x<1, E0>x, and 0<h_repair<1 hold strictly, where
  h_repair=(E0-x)/(3-x). Also E2>0. Every row0 annotation is positive:
  the limiting backwards solo3 recursion connects positive E0 to C0, and
  uniform O(Nt) perturbations preserve a positive lower bound.
* The only non-strict comparisons are the permitted wash equality at the
  lower boundary and the final y=z=0 at the upper boundary. At the latter
  the exact interfaces and (2.2) still make these quiet owners indifferent.

Consequently the core is legal throughout the exact closed phase interval

    theta_N^-(h)<=theta<=theta_N^+(h).                 (5.2)

## 6. Exact gluing and unbounded raw coverage

At theta_N^+(h), final Z=Y=0, so the final root is solo3 of hazard w.
Its current coordinates1,2 are (-100w,3w), while its successor coordinates
are (-97w/(1-w),4w/(1-w)). Delete this root and move the preceding core's
exit to its current annotation. The shortened core then has exit
x_old=100w,E2_old=3w, hence EXACT wash equality.

The deletion preserves the outer return equations. The total solo3 repair
survival is unchanged by

    (1-w)[1-(97w/(1-w))/3]=1-100w/3,

and the row0 and row2 affine transitions give the same repaired endpoint.
The entrance, a,b,A are unchanged. This is an exact N-1 solution at the
lower wash boundary, with the same raw alpha,beta (h and K unchanged).

It lies near the N-1 limiting branch: its last phase tends to
 delta theta_plus=theta_minus, and its new Lambda is delta times the old
Lambda because t_(N-1)=t_N/delta. Local uniqueness of the orbit and outer
implicit-function branch therefore gives, for all N sufficiently large and
all physical h>0,

    K_N(theta_N^+(h),h)
      =K_(N-1)(theta_(N-1)^-(h),h).                   (6.1)

For each fixed h, strict monotonicity of K_N maps (5.2) onto a complete
closed K interval. Equation (6.1) joins successive intervals exactly, with
no uncovered gaps. Their endpoints tend uniformly after multiplication by
h to infinity, since

    h K_N=1/[t_N Lambda_N]

and Lambda_N stays in a compact positive interval.

Choose one sufficiently large starting N0. The continuous lower endpoint
h K_N0(theta_N0^+(h),h)=1/[t_N0 Lambda_N0(theta_N0^+(h),h)]
extends to h=0 and has a finite maximum on [0,1]. Increase this bound to
at least100 and call it C. For every physical h>0,
the glued intervals cover all K>=C/h. Since 1/h=1+|p|/6, this is precisely
the raw region in Section1.

## 7. Common finite calendar and complete response control

At a product root q let Q_i be the payoff from Quit now, P_i the passive
payoff from nonempty opponent coalitions, and H_i=product_(j!=i)(1-q_j).
For a successor value v, Continue gives P_i+H_i v_i. A reference annotation
u obeys the Continue identity when u_i=P_i+H_i v_i. If every owner who quits
with positive probability also has Q_i=u_i, the prescribed payoff identity
holds. The full behavioral cap obeys

    B_i=max(Q_i,P_i+H_i B_i(next)).                    (7.1)

Before absorption there is only one surviving public history. A private
behavioral deviation is therefore a law on finite quitting dates and Never;
its payoff cannot exceed their supremum. Equation (7.1) prices that complete
menu, including its infinite-horizon limit.

The outer calendar connects

    A=(0,A1,A2,0) --solo0--> B=(0,B1,0,B3)
      --solo2--> C=(C0,C1,0,C3) --core--> E=(E0,-x,E2,0)
      --solo3 repair--> V=(V0,0,V2,0) --solo3--> A.

Given C and E, set

    b=C0/(1+C0), B1=b+(1-b)C1, B3=b+(1-b)C3,
    a=B3/(1+B3), A1=2a+(1-a)B1, A2=2a,
    R=1-x/3, V0=(E0-x)/R, V2=(E2+x/3)/R, h_repair=V0/3.

The exact core above ensures

    C0>0, B1>0, B3>0, 0<x<3, E0>x, E2>=3x/100,
    0<h_repair<1,
    A1(1-h_repair)=3h_repair, A2(1-h_repair)=V2+h_repair.                       (7.2)

These give 0<a,b<1 and V2>0. The core has the exact active comparisons and
positive row0 annotations, exactly.
Its row0 forced-Quit offers are nonpositive by the seven raw upper bounds.

For solo0, at cumulative quitting probability u in[0,a] the annotation is

    (0,(A1-2u)/(1-u),(2a-2u)/(1-u),u/(1-u)).

All observer coordinates are nonnegative. Choose 0<mesh<1/2 and subdivide
the aggregate a into finitely many conditional hazards at most mesh. For
J_i=Z_i({0,i}), the forced-Quit surplus of observer i is at most mesh J_i^+.
Every Continue identity and every prescribed identity is exact. There is
no restriction on J_i. At the solo2 root b, its owner is indifferent; row0
has a nonpositive joining offer, while rows1 and3 have offers -Kb and -100b below
their positive annotations B1 and B3, since K>=0.

The repair is finite. At state (s,-v,z,0), a solo3 root q gives successor

    ((s-3q)/(1-q),(-v+3q)/(1-q),(z+q)/(1-q),0).

If 0<v<3, s>=v and z>=3v/100, choose q=v/100. Its quiet comparisons are
legal: row0's offer is nonpositive, row1's is -100q=-v, and row2's is3q<=z.
The successor obeys

    v'=97v/(100-v), z'=(z+v/100)/(1-v/100),
    s'-v'=(s-v)/(1-v/100).

The guards persist. With r=97/100, after n regular roots,

    S_n=1-x/3+(x/3)r^n,
    v_n=x r^n/S_n, z_n=(E2+1-S_n)/S_n.

Take 43 regular roots and then q=v_43/3. The exact inequality
`(97/100)^43<109/400<=(3E2+x)/(4x)` gives z_43>=v_43,
so the last root is legal and sets row1 to zero. Total survival is1-x/3,
and its endpoint is exactly V above. This remains valid at wash equality
E2=3x/100, which is needed at the support transitions.

The final solo3 aggregate h_repair closes the return by (7.2). Its annotations at
cumulative quitting probability u in[0,h_repair] are

    ((V0-3u)/(1-u),3u/(1-u),(V2+u)/(1-u),0).

They are nonnegative. Subdivide h_repair into conditional hazards at most
min(1/2,V2/6). Row2's joining comparison3q<=current2 holds, while all other
quiet joining offers are nonpositive. Every block is finite.

For each fixed raw game choose one finite N and one legal phase from the
constructed branches. Fix all its annotations and the target A before
accuracy. Only the solo0 mesh needs refinement. Let

    e=mesh max(0,J1,J2,J3),      rho=min(a,b)>0.

Every Continue and prescribed identity is exact, and each immediate Quit
surplus is at most e. Deleted-opponent period survival is at most1-rho: a
deviator0 faces solo2, and every other deviator faces the complete solo0
block. Prescribed survival has the same bound. Let D be the largest
reference-adjusted behavioral cap over one period. Unrolling (7.1) through
one period bounds it by max(e,(1-rho)D), so D<=e. Prescribed payoffs equal
the reference annotations because the exact affine identities iterate with
vanishing period survival. Hence every complete behavioral replacement has
terminal gain at most e. Quit surpluses enter a maximum, not a sum, so the
bound is independent of the number of small roots.

For a selected finite period of length L, absorption time under any
unilateral replacement is bounded by the opponents-only absorption time,
whose expectation is at most L/rho+1. If M bounds absolute original rewards,
terminal and horizon-T payoffs differ by at most2M(L/rho+2)/T uniformly over
all deviations. Proper opponents also ensure the native translation adds
exactly kappa_i to every terminal payoff, prescribed or deviating. Choose
the solo0 mesh first and then a horizon threshold. This proves the uniform
contract at the single target W=kappa+A for each fixed raw game. The target
need not equal the limiting vector kappa+(0,6/7,5/7,0).

## 8. Independent perturbations of the fixed coefficients

The theorem persists when all26 nontrivial reference entries other than
Z1(12)=-K and Z2(12)=p vary independently in one sufficiently small open
neighborhood. This is a uniform assertion over arbitrarily long cores;
fixed-N openness alone would not prove it. Here are the explicit changes
that supply the uniform proof.

Write xi for these26 coefficients and Gamma_ij=Z_i({j}). Near the displayed
table put

```
A=-Z1(13)>0, g=-Gamma13>0, c=Z2(23)>0, b3=Gamma23<0,
r=(c-b3)/c>1, a0=1/(r-1), delta=1/r,
B0=A-a0 Gamma13,
theta=w/(1+a0 w),
J=[(1-w)Z+B0 w]/(1+a0 w).
```

Keep h=6/(6-p), t=delta^(N-1), alpha=t h Lambda and
beta=-6t(1-h)Lambda. The exact first two current values are

```
Q1=-Z(1-w)-A w+alpha(A+Z1(123))Zw,
Q2=beta Y(1-w)+c w+alpha(Z2(123)-c)Yw.
```

Their passive numerators are

```
P1=alpha Gamma12 Z(1-w)+Gamma13 w(1-alpha Z)
       +alpha Z1(23)Zw,
P2=alpha Gamma21 Y(1-w)+Gamma23 w(1-alpha Y)
       +alpha Z2(13)Yw.
```

Set F1=(Q1-P1)/[(1-alpha Z)(1-w)] and
F2=(Q2-P2)/[(1-alpha Y)(1-w)]. Given Y_next, the exact first two interfaces
are obtained by

```
v=(F2-beta Y_next)/[c-beta Y_next+alpha(Z2(123)-c)Y_next],
z=(-F1-A v)/[1-v-alpha(A+Z1(123))v],
theta_bar=v/(1+a0 v),
J_bar=((1-v)z+B0 v)/(1+a0 v).
```

At t=0 these are exactly theta_bar=r theta and J_bar=J. Therefore
f=(theta_bar-r theta)/t and g_core=(J_bar-J)/t have analytic extensions
and uniform derivative bounds on a small compact coefficient box.

The row3 backwards elimination also stays nonsingular, although its
next-Y derivative need not vanish at t=0. Write

```
u=Z3(13), v3=Z3(23), a3=Gamma31, b3s=Gamma32,
d3=Z3(12), w3=Z3(123),
D3=(w3-u-v3)-(d3-a3-b3s),
R=uY_next+v3 Z_next+alpha(w3-u-v3)Y_next Z_next.
```

The exact backwards equation is

    Y=[R(1-alpha Z)-(v3-b3s)Z]
        /[(u-a3)+alpha D3 Z+alpha R(1-alpha Z)].       (8.1)

At the last root use R=0. At t=0 its next-Y derivative is
rho=u/(u-a3), which equals0 at the reference table. Shrink the coefficient
neighborhood so |rho|<1/2<delta uniformly. The backwards array map and its
first two derivatives are then bounded by geometric series, uniformly in N.
The steady early-orbit value at theta=0 is

    Y=mJ,          m=-Gamma32/Gamma31>0.

In addition to the former small theta and t errors, its finite-terminal
correction decays as O(rho0^(N-1-j)), for a fixed rho0<delta_min.
This bound follows by iterating the uniformly contracting backwards scalar
map (8.1); its coefficient derivatives add only a polynomial factor in the
exponent. Weighted by delta^(j+1), those corrections sum to O(t), since
rho0/delta is bounded strictly below1.

The same finite-array contraction as in Section3 consequently works with
J increments t g_core and backwards theta contraction delta. All constants
are uniform on the compact coefficient box, and N delta_max^(N-1) tends
to0. The early forcing is now

    f(theta=0,t=0,Y=Y_next=mJ)
       =-h Lambda Gamma21 mJ/c.

Its weighted sum tends to -a0 h Lambda Gamma21 mJ/c. The exact entrance
Q2(first)=0 has correction tending to 6(1-h)Lambda mJ/c. Thus the new
limiting entrance equation is

    theta-Lambda (mJ/c)[-a0 Gamma21 h+6(1-h)]=0.       (8.2)

The bracketed coefficient is strictly positive uniformly, and at the
reference table its total factor multiplying Lambda is J for every h.

For clarity, estimates with respect to coefficient derivatives may gain
powers of N: D_xi t=O(Nt), and differentiating the reference phase contributes
O((N-1-j)delta^(N-1-j)). The weighted Green error is therefore O(N^2 t)
in C1 in the coefficients, rather than the former O(Nt). Similarly a coarse
O(N^3 t) bound suffices for aggregate derivatives. All these quantities tend
to0 uniformly because delta<=delta_max<1. The geometric backwards-tail
terms obey the same conclusion. For the three variables used in the outer
implicit-function theorem, the original estimates already suffice.

The limiting core data change smoothly to

```
D=1-(a0+1)theta,
C0=Gamma03(1-D)+D E0, C1=-J, C3=0,
x=[J+(a0+1)Gamma13 theta]/D,
E2=(c-b3)theta/D,
Z_last=(J-B0 theta)/D.
```

The perturbed outer calendar is explicit:

```
b=C0/(C0-Gamma02),
B1=b Gamma12+(1-b)C1, B3=b Gamma32+(1-b)C3,
a=B3/(B3-Gamma30),
A1=a Gamma10+(1-a)B1, A2=a Gamma20,
R_repair=1-x/g,
V0=(E0-Gamma03 x/g)/R_repair,
V2=(E2-Gamma23 x/g)/R_repair.
```

Its two return equations are

```
A1(Gamma03-E0)=g E0-Gamma03 x,
A2(Gamma03-E0)=Gamma03 E2-Gamma23 E0.
```

They reduce to (4.3) at the reference table. At the singular limit,
multiplying these equations by D eliminates theta and gives

    A1(Gamma03-C0)=g C0-Gamma03 J,
    A2(Gamma03-C0)=-Gamma23 C0.

Here A1,A2 use the displayed outer formulas with C1=-J,C3=0. This system
selects smooth constants C0_*(xi),J_*(xi), independent of theta and h,
near(5/4,3/4). Its Jacobian is nonzero at the reference table by the
previous Jacobian calculation and the nonsingular change from E0 to C0.
Consequently the limiting phase and entrance data are explicit:

```
E0=[C0_*-Gamma03(a0+1)theta]/[1-(a0+1)theta],
Lambda=theta/[(m J_*/c)(-a0 Gamma21 h+6(1-h))].
```

The Lambda derivative of (8.2) and the outer Jacobian remain uniformly
invertible on a small coefficient box. The finite-dimensional selection
in Section4 therefore persists uniformly in xi and h. Its phase derivative
partial_theta Lambda stays positive. No large-K continuation profile is
supplied as a hypothesis.

All strict signs persist uniformly. In particular Gamma21,Gamma23,Z2(13)
remain negative, so row2's passive numerator is negative whenever y or w
is positive. The exact induction proving w positivity in Section5 still
applies. The final Y has the same sign as final Z by (8.1) with R=0.
Nonterminal Y,Z have uniform positive margins by continuity of the uniformly
bounded backwards map. Core row0 values remain positive; its joining offers
remain nonpositive by the unchanged seven raw upper bounds.

The perturbed wash uses q=v/A at coordinate1=-v. It preserves
z>=cv/A and s>Gamma03 v/g, because

```
v'=(v-gq)/(1-q), z'=(z-Gamma23 q)/(1-q),
s'=(s-Gamma03 q)/(1-q),
z'-cv'/A=[z-cv/A+q(-Gamma23+cg/A)]/(1-q),
s'-Gamma03 v'/g=(s-Gamma03 v/g)/(1-q).
```

After n regular roots the final q=v/g is legal whenever

    (1-g/A)^n <= [g E2-Gamma23 x]/[(c-Gamma23)x].

At the wash boundary E2=cx/A the right side is
(g c/A-Gamma23)/(c-Gamma23). The reference43-step inequality is strict,
so the same n=43 works throughout a sufficiently small coefficient box.
The final solo3 aggregate and solo0 block are split as before; their strict
signs and arbitrarily small mesh errors persist. The same full behavioral
and horizon comparison proves the consumer for the perturbed calendar.

The two terminal boundaries are final Z=0 and E2-cx/A=0. At the limit,

    E2-cx/A=(c/A)[r B0 theta-J]/D,
    Z_last=(J-B0 theta)/D.

Since J_*=J_*(xi) is independent of phase, their limiting zeros are

    theta_plus=J_*/B0,
    theta_minus=J_*/(r B0)=delta theta_plus.

They remain transverse, so the two finite-branch boundary phases exist
uniformly. The endpoint gluing also persists EXACTLY, not merely by
continuity. At
final Z=Y=0 the last root is solo3, with current pair(-A w,cw). Deleting
it makes the shortened core's exit x_old=A w,E2_old=cw, precisely the
new wash boundary. Its successors are
x=(A-g)w/(1-w), E2=(c-Gamma23)w/(1-w), and the general affine return
equations above are multiplied by1-w under deletion. The exact limiting
identity theta_minus=delta theta_plus places the shortened core near the
N-1 lower-boundary branch at the same alpha,beta. Finite-branch uniqueness
therefore identifies consecutive N and N-1 endpoints exactly, as in Section6.

Finally choose one N0 large enough uniformly on the closed coefficient box
and h in[0,1]. The lower endpoint of hK=1/(t_N0 Lambda_N0) is continuous
on this compact set and has a finite maximum. Increase it to at least100.
The glued intervals therefore give ONE constant C for the entire coefficient
box and all physical h>0. This proves the robust raw theorem, with a fixed
open radius for the26 coefficients and the same arbitrary remaining entries.

## 9. Uniform separation from the stationary and sure-root branches

The following fixed completion of the unrestricted entries, with all
kappa_i=1, separates the new region from stationary and sure-root methods:

| D | Z0 | Z1 | Z2 | Z3 |
|---|---:|---:|---:|---:|
|01|0|-1|-10|-12|
|02|0|5|-10|7|
|012|-13|6|-9|11|
|03|-3|3|-5|1|
|013|-7|8|10|-10|
|023|-7|-8|-3|15/2|
|0123|-5|-9|8|21/2|

For EVERY K>=100 at p=0 this completion has no stationary equilibrium and
no root with a sure quitter that is Nash against any actual continuation
cap. Consequently every K>=C at p=0 supplies a separating game inside the
new existence theorem, even though no numerical upper bound on C is given.
The following finite exact certificate proves the two uniform exclusions.

For product hazards q write

```
H_i=product_(j!=i)(1-q_j),
P_i=sum_(nonempty S subset opponents) weight_q(S) Z_i(S),
Q_i=sum_(S subset opponents) weight_q(S) Z_i(S union{i}),
F_i=(1-H_i)Q_i-P_i,
L_i=min({-1} union {Z_i(S): nonempty S excludes i}),
G_i=Q_i-P_i-H_i L_i.
```

Here weight_q(S)=product_(j in S)q_j product_(j outside S,i)(1-q_j).
The displayed completion has L=(-12,-8,-10,-12), independent of K.
Every nonzero stationary equilibrium satisfies F_i<=0 for q_i=0, F_i=0
for0<q_i<1, and F_i>=0 for q_i=1, by comparing Quit now with Never.
AllNever is excluded separately by each original own-singleton payoff1.
A root with a sure quitter that is Nash at an actual continuation cap must
satisfy the same signs for G: the continuation cap is at least L by Never,
and replacing it by L can only improve the sole sure owner's Quit action;
all other players have H_i=0. With multiple sure owners all H_i are zero.

Only row1 varies with K. Its exact dependence is

```
F1(K)=F1(100)-(K-100)(1-H1)(1-q0)q2(1-q3),
G1(K)=G1(100)-(K-100)(1-q0)q2(1-q3).
```

Thus all K>=100 can be excluded by one necessary-condition relaxation
using only the rational table at K=100,p=0. Enumerate support patterns in
{0,1,*}^4; for F retain the80 nonzero patterns, and for G retain the65
patterns containing a sure owner. If a pattern has q2=0, q0=1, or q3=1,
keep all original signs because the K term vanishes. In every other
pattern, keep rows0,2,3 unchanged and replace row1's condition as follows:
for mixed or sure row1 require its baseline polynomial>=0; for quiet row1
omit its condition. These are necessary for every K>=100, and do not
assume that row1's active equality persists at K=100.

One direct exclusion simplifies F: if q0=0, player2 is mixed, and q1 or q3
is positive, then at p=0

    Q2=q3(3-q1)>=0,
    P2=-2q1-q3+2q1q3<0,

so F2>0, contradicting its active equality. A pattern with one mixed
coordinate j and no sure owner is excluded by an outsider i with
Gamma_ij<0 and Z_i({i,j})>=0; such an outsider exists for every j. Choose
an outsider whose comparison was retained. For j=2 one can choose i=0.
The other single-owner cases have an identically vanishing K term.

For at least two mixed coordinates S, form A=Gamma_SS and V=A^(-1), where

    Gamma=[ 0  3 -1  3
            2  0  1 -3
            2 -2  0 -1
           -1 -2  1  0 ].

Every such principal matrix is invertible. Add the V combinations of the
mixed-row baseline polynomials. They are equalities unless mixed row1 was
relaxed. In that case each combination has the sign of its coefficient
in column1 of V: >=0 for a positive coefficient, <=0 for a negative one,
and =0 for zero. All other mixed rows remain exact equalities.

For a pattern with no sure owner, these baseline mixed polynomials have
form -Aq+R(q), with R containing only terms of degree at least2. If row1
was not relaxed they imply q=V R. If row1 was relaxed, the directly excluded
q0=0 cases have already been removed. Every remaining relevant principal
inverse has column1 entrywise nonnegative, so V F>=0 and q<=V R. In either
case put

    c_i=sum of absolute coefficients in R_i,
    D=max_i sum_j |V_ij| c_j.

Then ||q||_infinity<=D||q||_infinity^2. If D=0 the pattern is impossible;
otherwise choose the least positive integer E with2^-E<1/D and discard
all nonzero points in[0,2^-E]^S. All the constants use only the baseline
rational polynomials; the origin exclusion is uniform in K.

Here are the remaining exact finite certificate rules. Substitute the fixed
coordinates of each pattern, retain the signs just described, and append
the V combinations. Every coordinate degree is at most2. If a polynomial
is sum_m a_m x^m in d mixed variables, its tensor degree2 Bernstein
coefficient at index k in{0,1,2}^d is

    b_k=sum_(m<=k) a_m product_i [binom(k_i,m_i)/binom(2,m_i)].

Clear one common positive denominator for all coefficients in a pattern.
Reject a box if an equality has coefficients all strictly positive or all
strictly negative, or if an inequality has all coefficients of its forbidden
strict sign. Omitted conditions are ignored. Also reject a box contained
in the proved origin cube. Otherwise bisect the coordinate subdivided the
fewest times, breaking ties by increasing player index. For each degree2
coefficient triple (u,v,w) along that coordinate, integer-scaled left and
right children are

    left=(4u,2(u+v),u+2v+w),
    right=(u+2v+w,2(v+w),4w).

Scaling is positive and preserves every sign. Process left before right.
A zero-dimensional pattern is checked directly, and each direct exclusion
above counts as one node. These prescribed finite rational calculations
terminate with exactly862 nodes for the80 stationary patterns and369 nodes
for the65 sure-root patterns. No box is left unresolved. This supplies
uniform exclusions for all K>=100 at p=0; it is not a behavioral
counterexample, since Section1 supplies UE for the large-K tail.

## 10. Coverage, source scope, and formalization handoff

The new raw region is not contained in the scalar family that fixed K=100,
nor in the two cones K>=100,p>=2K and K>=0,p<=-max(200,2K): its p=0 ray
contains every sufficiently large K. The uniform separating completion in
Section9 excludes the full stationary and sure-root strategies along that
ray. Positive changes of payoff units and player relabeling do not identify
these games with K=100: the singleton matrix has a unique row with two equal
positive off-diagonal entries, fixing player0; that row's sign fixes player2,
and the remaining sign pattern fixes players1 and3. Its nonzero entries then
force every row scale to be1, leaving K unchanged.

The following finite-choice checks exclude the other named existing
selectors on the separating ray. They concern concrete sufficient mechanisms,
not an assertion that every conceivable equilibrium theorem has been surveyed.
The singleton matrix Gamma has determinant25 and inverse column0
(8,3,14,10)/25>0. Its positive graph is strongly connected, while the
participant vector on123 is(11,2,1)>0. Thus complete ordered nonpositive
anchor selection fails: an admissible marked set must be all players, and
its first block meeting123 has positive weighted participant sum. The same
positive vector defeats every upper-average weight on the core.

The upper-face joining charge at12 is Z3(123)-Z3(12)=7>0, so the required
mixed-trap sign fails. The only inverse-positive principal triple is023,
whose outside inverse row is(-3,6,2)/5; full passive-child selection fails.
The unique mutually negative singleton pair is13. Its only labeling meeting
the attached-pair sign template is(3,1,0,2), where the required nonnegative
participant premium is Z1(13)=-100. The both-premiums-arbitrary alternative
instead requires m=Gamma21=-2 to be nonnegative.

For the three invariant-cone pair partitions, the necessary positive
difference Z_i({i,mate})-Gamma_i,mate fails:01|23 gives-3 at i=0,02|13
gives-12 at i=2, and03|12 gives-6 at i=0. No proof-weight matrix repairs
those prerequisites. Inverse column2 is(9,-6,-3,5)/25, defeating the
all-signed-positive inverse-column criterion under all relabelings and
sign choices. The unique mutually positive pair01 intersects the unique
mutually negative pair13, whereas the signed four-cycle templates require
them disjoint. Every three-player subset also contains a core pair with a
negative participant reward. These raw obstructions are unchanged as K
increases along p=0.

The semantic sources inspected are
`quittingContinuationBestResponseValue_rootThenContinuation_eq_max`
(`UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean`) and
`quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
(`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`).
Section7 supplies its own full behavioral and fixed-target finite-horizon
argument; these declarations identify the intended Lean consumers, not
unproved hypotheses imported into this proof. No new Lean compilation,
integration, or formal verification is claimed.

The formalization target is the robust raw theorem in Section1. The essential new
lemmas are the finite-array contraction with uniform parameter derivatives,
the exact weighted Green sum, uniform finite-dimensional implicit selection,
and exact support-boundary deletion. Finite root identities and the common
calendar then supply the complete consumer. Only the coverage comparison
uses the finite rational Bernstein certificate; the equilibrium producer
itself is analytic and has no numerical rootfinding premise. Fin4 for
arbitrary tables remains open.
