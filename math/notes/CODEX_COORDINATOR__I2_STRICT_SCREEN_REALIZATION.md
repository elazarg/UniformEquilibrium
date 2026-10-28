# Exact common-support tails with a quiet contact at every date

Owner: CODEX_COORDINATOR. Ordinary mathematics.
This constructs actual local I2 configurations, including extremality in the
fixed-pivot replacement problem. It does NOT supply a positive absorbing gap,
an earlier head, or global minimality. Thus it is not a counterexample to UE
and not an exclusion of the I2 source. Its purpose is to identify precisely
why contact-rich replacement alone cannot close that source.

## 1. Raw open conditions and conclusion

There are four players p,i,h,k with a finite native table Z, own singleton
and Never rewards zero. All private clocks are independent; a deviation may
replace the complete clock law. Define

 G=Z_i({p}), J=Z_i({p,i}), A=Z_p({i}), C=Z_p({p,i}),
 rho=G/J, a=1-rho.

Assume J!=0, 0<rho<1 and A-rho*C>0. For each quiet player j=h,k put

 g_j=Z_j({p}), d_j=Z_j({i}), X_j=Z_j({j,p}), Y_j=Z_j({j,i}),
 D_j=Z_j({p,i}), E_j=Z_j({j,p,i})-X_j-Y_j,
 c_j=g_j-rho*X_j,
 K_j=D_j-g_j/rho+d_j*(1/rho-1).

The additional conditions are

 c_h<0, Y_h!=0, b_h=d_h-rho*Y_h>0,
 lambda=-c_h/b_h>0,
 c_k+lambda*(d_k-rho*Y_k)>0.                         (1)

These are open raw conditions. ALL remaining rewards, including
D_j and the two triple rewards entering E_j, are arbitrary finite numbers.
There is epsilon>0 determined by the raw table such that for each
u0 in(0,epsilon) an actual profile has the following properties:

- p and i have positive atoms at every date, and positive Never masses;
- h and k prescribe Never;
- every observer i,h,k has zero full behavioral debt;
- every finite response of h ties with Never, while each finite response
  of k is strictly worse than Never;
- the pivot's finite responses are strictly worse than Never, and its
  prescribed law has strictly positive debt;
- the partner law is an extreme point of the fixed-pivot feasible set
  retaining its total finite mass, tie probability, and all ALL-END
  inequalities for p,h,k.

Thus even the strengthened extremal contact conclusion of the current
I2 replacement theorem is compatible with an open set of local raw data.
The global source and its inherited objective remain indispensable. The
[contact-rich replacement](CODEX_COORDINATOR__TWO_OWNER_CONTACT_REPLACEMENT.md)
supplies those contacts at an actual minimum; this theorem deliberately
separates their local realizability from global minimality.

## 2. Exact three-state tail equations

At a fixed initial cut let Np,Ni be the two Never masses. Write P_n,I_n for
inclusive remaining finite masses and T_n=sum_(m>=n) alpha_m beta_m. Impose
alpha_n=rho*P_n. Normalize

 u=P_n/Np, v=I_n/Ni, t=T_n/(Np*Ni), b=beta_n/Ni.

The update is exactly

 u'=a*u, v'=v-b, t'=t-rho*u*b.                       (2)

Integrating partner contact gives the two-clock ordering identities
Pr(i first and both finite)=(1/rho-1)T and
Pr(p first and both finite)=PI-T/rho.
Using these identities, the numerator of j's conditional Never payoff,
after multiplication by the positive conditional-survival denominator and
division by Np*Ni, is

 g_j*u+d_j*v+g_j*u*v+K_j*t.

The corresponding immediate Quit numerator is

 rho*X_j*u+(Y_j+rho*E_j)*u*b+Y_j*b+rho*X_j*u*v.

Their difference is therefore EXACTLY

 H_j(u,v,t,b)=c_j*u+d_j*v+c_j*u*v+K_j*t
                            -[Y_j+(Y_j+rho*E_j)*u]*b. (3)

At every actual date, H_j>=0 is the full comparison to Never; equality
is a quiet contact. Formula(3) retains the passive pair and participant
triple rewards. It is not merely a first-order approximation.

## 3. An exact contact law without a resonance restriction

Fix a small positive u0 and let u_n=a^n*u0. Seek

 v_n=lambda*u_n+w_n, b_n=v_n-v_(n+1),
 t_n=rho*sum_(m>=n) u_m*b_m.

The tie expression is initially a linear functional of a candidate sequence;
positivity and its actual-law interpretation are verified below. Write

 t_n=rho*lambda*u_n^2/(2-rho)+(Tw)_n,
 (Tw)_n=rho*sum_(m>=n) u_m*(w_m-w_(m+1)).             (4)

Let Y=Y_h, d=d_h, c=c_h, K=K_h, F=Y_h+rho*E_h, and set

 r=1-d/Y,
 Q=lambda*[c-rho*F+K*rho/(2-rho)].

The equality c+lambda*(d-rho*Y)=0 cancels the linear term in u. Direct
substitution into(3) shows that all exact h contacts are equivalent to

 Y*(w_(n+1)-r*w_n)+Q*u_n^2+(Nw)_n=0,
 (Nw)_n=c*u_n*w_n+K*(Tw)_n-F*u_n*(w_n-w_(n+1)).     (5)

There is no nonlinear term in w; all remaining coefficients carry a small
factor u0. Pick q in(a^2,a) with q!=|r|. For an explicit finite choice,
use one of (2*a^2+a)/3 and (a^2+2*a)/3; they are distinct, so one works.
On real sequences use the Banach norm ||w||=sup_n |w_n|/q^n. The operator
Lw=(w_(n+1)-r*w_n) has the following bounded right inverse R:

 if |r|<q: (Rf)_0=0,
            (Rf)_n=sum_(m=0)^(n-1) r^(n-1-m)*f_m;
 if |r|>q: (Rf)_n=-sum_(m=n)^infinity r^(n-1-m)*f_m.

Both sums satisfy L Rf=f by direct subtraction, and geometric-series
estimates give

 ||Rf||<=||f||/Delta, Delta=abs(|r|-q)>0.              (6)

In particular the second sum converges absolutely. This covers negative
r and all positive resonances r=a^m; only the selected weight q must avoid
|r|. No analytic-power-series or nonresonance premise is imposed.

The other exact bounds are

 ||u^2||<=u0^2,
 ||Tw||<=rho*u0*(1+q)*||w||/(1-a*q),
 ||Nw||<=u0*D*||w||,
 D=abs(c)+abs(F)*(1+q)+abs(K)*rho*(1+q)/(1-a*q).

Here the displayed ||u^2|| is for the sequence n ->u_n^2; a^2<q is used.
Thus

 w=R[-Q*u^2/Y-Nw/Y]                                 (7)

is a contraction whenever u0*D/(abs(Y)*Delta)<=1/2. Its fixed point solves
(5) exactly and satisfies

 ||w||<=C0*u0^2, C0=2*abs(Q)/(abs(Y)*Delta).           (8)

If Q=0, the unique fixed point is zero. Since q<a, (8) gives uniform
bounds

 |w_n|<=C0*u0*u_n,
 |w_n-w_(n+1)|<=C0*(1+q)*u0*u_n.

After decreasing u0, these ensure v_n>0, b_n>0, and v_(n+1)>0.
Both v_n and t_n tend to zero. The tie expression in(4) now has positive
summands, so it is the genuine remaining tie moment.

Set

 Np=1/(1+u0), Ni=1/(1+v_0),
 alpha_n=Np*rho*u_n, beta_n=Ni*b_n.

Telescoping gives sum alpha_n=1-Np and sum beta_n=1-Ni. These are actual
independent clock laws with the claimed positive Never masses. Their
normalized finite tails and tie tails are exactly (u_n,v_n,t_n).
Their uniform smallness estimates also give

 v_n=lambda*u_n+O(u0*u_n),
 b_n=rho*lambda*u_n+O(u0*u_n),
 t_n=rho*lambda*u_n^2/(2-rho)+O(u0*u_n^2).            (9)

The constants depend only on the fixed raw table and chosen q, not n or
u0. The last bound follows from (4), (8), and q<a. For each fixed u0,
the relative errors in the first two lines actually tend to zero as
n tends to infinity, because (q/a)^n tends to zero.

## 4. All full response comparisons

For i, J alpha_n=G P_n at EVERY date, so every finite deadline and Never
give the same payoff against the fixed pivot law. Observer i is optimal.
For h, equation(3) vanishes at every date. For k, (1), (3), and (9) give

 H_k=[c_k+lambda*(d_k-rho*Y_k)]u_n+O(u0*u_n)>0

throughout a sufficiently small positive interval. The pivot's exact
Never-minus-date gap is A I_n-C beta_n. The estimate beta_n/I_n=rho+O(u0), uniformly in n, and A-rho C>0
make this gap strictly positive for all dates after shrinking u0.

Thus ALL-END holds for all four players. The three observers prescribe
mixtures of their best responses; the pivot puts positive mass on strictly
suboptimal deadlines, so its debt is positive. Every complete private
behavioral deviation induces a deadline or private mixture of deadlines
along the sole live history; the stated inequalities therefore cover all
behavioral deviations.

For clarity, its exact pivot debt is

 d_p=A PI-[C+A(1/rho-1)]T,
 d_p/(PI) -> (A-rho C)/(2-rho)>0 as u0->0.            (10)

This is consistent with quadratic tail dispersion. It is not zero debt
for the pivot and does not produce an absorbing equilibrium.

## 5. Extremality in the retained-moment feasible set

Freeze the pivot law and the partner's initial I,T. Consider all partner
laws supported on the pivot-induced contact set, retaining these moments,
and satisfying every p,h,k date-versus-Never inequality. This is exactly
the feasible set used by the contact-rich replacement argument. The
constructed law belongs to it.

Shrink u0 so Y_h+(Y_h+rho E_h)u is nonzero for 0<=u<=u0, possible since
Y_h!=0. If our law were a nontrivial midpoint of two feasible laws, its
zero h gap at every date and the nonnegative endpoint gaps would force
both endpoint laws to have H_h=0 at every date. At date0 the initial
I,T and fixed pivot law determine b uniquely by(3). The recursions(2)
then determine I_1,T_1, and the same argument determines beta_1. Induction
fixes the whole partner law. This contradicts a nontrivial decomposition.
Thus the constructed partner is extreme, without any generic-rank premise.

## 6. An exact residual-singleton control

Use the benchmark singleton matrix

 Gamma=[0,-1,-1,2; -1,0,1,1; 1,2,0,-1; 1,-1,1,0]

and labels p=2,i=3,h=0,k=1. Specify

 Z3(23)=2, Z2(23)=-3,
 Z0(02)=0, Z0(03)=-2, Z0(23)=0, Z0(023)=10/3,
 Z1(12)=-2, Z1(13)=4, Z1(23)=0, Z1(123)=0.

Set every other nonsingleton reward to zero for a complete control table.
Then rho=1/2,A=-1,C=-3, lambda=1/3. The exact functions are

 f(u)=u/3, g(u)=u^2/9, b(u)=u/6.

Direct substitution gives H_h=0 and H_k=5u/3+u^2/18>0; the pivot
Never-minus-date gap is I/2>0. Its debt is exactly PI/3.
Take 0<u0<1, so the h beta coefficient -2+2u/3 stays nonzero and the
extremality proof applies. The singleton matrix is the strict no-child,
one-pivot residual example; no assertion of global minimality is made.
The specified complete control is a solved game: players0,1 quitting surely
and2,3 continuing give an absorbing native Nash profile of payoff zero.
The two active players would receive -1 by continuing, and the quiet players
receive zero whether or not they join. Thus its tail is not a positive-gap
source or an equilibrium counterexample.

The raw conditions(1) and A-rho C>0 are strict at this example. The exact sequence-space
construction persists under all sufficiently small singleton/pair changes
preserving them, and permits arbitrary finite higher rewards. Consequently
one may also avoid row equalities and other finite genericity exclusions.
This is not an isolated nongeneric contact coincidence.

## 7. Completeness of the strict first-order contact screen

The existing common-support source screen has

 c_h<0<c_k, b_k(rho)<0<b_h(rho),
 c_k*b_h(rho)-c_h*b_k(rho)>=0,
 b_j(rho)=d_j-rho*Y_j.

If its final inequality is strict and Y_h!=0, then choosing
lambda=-c_h/b_h(rho) supplies precisely (1). Hence the construction above
realizes EVERY strict passing common-support screen with the generic
nonzero pair reward Y_h, regardless of the finite higher rewards. At first
order, z=rho and this constant ratio already give an infinite trajectory
with h tied and k strictly quiet; (5)--(9) lift it to exact actual laws.

The screen's equality boundary is not covered. Nor is the original global
source supplied: these laws need not minimize its inherited objective or
fit any prescribed earlier head. Consequently a further obstruction based
only on existence of common-support local calendars and extremal quiet
contacts cannot remove any of these open passing cells.

## Sources inspected and actual remaining issue

The exact full-cap recursion is
quittingContinuationBestResponseValue_rootThenContinuation_eq_max in
UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean. The current I2
source equations, raw interval tests, and contact-rich replacement theorem
were inspected. The older first-quiet-contact periodic-role construction
concerns a specific periodic equilibrium and does not supply this infinite
pair calendar or its extreme-law property.

A complete I2 exclusion must use global minimality or an actual compensated
activation retaining its inherited head; local contact recurrence, generic
raw rewards, and extremality alone do not contradict one another.
