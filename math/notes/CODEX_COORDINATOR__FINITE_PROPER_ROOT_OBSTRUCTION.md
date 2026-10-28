# A proper one-date trap above every strict-column singleton matrix

Ordinary mathematics; not checked in Lean. The complete proof has an
[independent review](../feedback/FINITE_PROPER_ROOT_OBSTRUCTION__BY_REVIEW.md).
This is an obstruction to particular finite-case replacements. It is not a positive-gap
example, an actual global source, or an exclusion of a Fin4 counterexample.

Let Gamma be any real invertible zero-diagonal four-by-four matrix with
v=Gamma^-1 e_0>0. Write alpha=v_0, k=v_1+v_2+v_3, and S=alpha+k. Choose

    0<r<=alpha/(2S^2), K>r+max_i |sum_(j!=i) Gamma_ij|.

The pivot is0. All own singleton, live, and Never rewards are zero. For every
nonempty coalition D excluding i, set Z_i(D)=Gamma_ij if D={j}, and Z_i(D)=K
if |D|>=2. Specify the remaining rewards by

    Z_i(D union{i})=Z_i(D)+Delta_i(D).

For i in{1,2,3}, let next and prev cycle through1,2,3. Set
Delta_i({0})=Delta_i({next(i)})=1, Delta_i({prev(i)})=-2,
and Delta_i(D)=0 for |D|>=2. Set Delta_0({j})=-r/3 for j>0,
Delta_0(D)=0 for |D|=2, and Delta_0({1,2,3})=-r.
These rules specify all sixty rewards and leave the literal Gamma unchanged.

## Complete proper one-date classification

A proper one-date profile quits independently at date0 with probabilities
q_i<1 and otherwise Never. Put x_i=q_i/(1-q_i), H_i=product_(j!=i)(1-q_j).
Let P_i be the passive payoff from the nonempty opposing quitter coalitions,
and Q_i the immediate-Quit payoff. Direct multilinear expansion gives

    (Q_i-P_i)/H_i=C_i(x)=x_0+x_next(i)-2x_prev(i),       i>0,
    (Q_0-P_0)/H_0=C_0(x)=-r[(x_1+x_2+x_3)/3+x_1 x_2 x_3].

Every later finite deadline and Never gives P_i. Thus the full cap is
B_i=max(P_i,Q_i), ALL-END means C_i<=0 for every i, and zero observer debts
add x_i C_i=0 for i>0. These conditions price every complete response law.

Their entire solution set is AllNever and

    x_0=x_1=x_2=x_3=z>0.                              (1)

Indeed, if an observer coordinate x_j vanishes, the inequality in the row
whose prev is j forces x_0 and a second observer coordinate to vanish. The
remaining inequality then forces the last coordinate to vanish. Otherwise
all observer coordinates are positive and satisfy their three equalities.
This invertible circulant system has the unique solution x_i=x_0 for i>0.
Conversely (1) satisfies all observer equalities and has C_0<0.

On (1), the pivot debt and joint Never probability give

    J_r=d_0+r nu=r(1+z^2+z^4)/(1+z)^4,
    J_r-3r/16=r(z-1)^2(13z^2+14z+13)/(16(1+z)^4).

Hence q_i=1/2 uniquely and strictly minimizes J_r over this ENTIRE proper
one-date ALL-END zero-observer-debt class. AllNever has objective r.
Writing R_i=sum_(j!=i)Gamma_ij, the minimizing tuple has

    B_i=e_i=(R_i+4K)/8>r/2, U_i=B_i for i>0,
    U_0=B_0-r/8, d_0=r/8, N_i=1/2, nu=1/16.

Thus B_0>J_r, U_0>r nu, and N_0=1/2<1/(1+rS). Every singleton condition
satisfied by the supplied Gamma remains satisfied by this completion.

## The complete inverse-axis append and replacement families fail

Use the inverse-axis zero-observer semantic block E_T, T>=0, supplied in
Section2 of the [inverse-axis construction](CODEX_VARIATIONAL_ESCAPE__CONSTRAINED_REPAIR_AND_CONE_GRAFT_OBSTRUCTION.md), with exact data

    B_0=e_0=(1-exp(-kT))/k, U_0=(1-exp(-ST))/S,
    nu=exp(-ST), B_i=e_i=U_i=0 for i>0.

The absorbing limit T=infinity is included. Grafting this block after the
minimizing one-date profile preserves all observer caps and payoffs. The
pivot cap takes the Never-through-tail branch. Put z=exp(-kT), c=S/k and
s=1/16. The full objective change is

    Delta J_r/s=(2/k)(1-z)-(1/S+r)(1-z^c)
                 >=((1-rS)/k)(1-z)>0,                T>0,

using 1-z^c<=c(1-z). Here rS<=alpha/(2S)<1, and T=0 changes nothing.
Thus no append length, including the absorbing endpoint, improves J_r.

Replacing the whole profile by E_T has objective

    J_r(E_T)=1/k-1/S-z/k+(1/S+r)z^(S/k).

Its unique minimum on0<=z<=1 occurs at z=(1+rS)^(-k/alpha) and equals

    f(r)=alpha/(Sk)[1-(1+rS)^(-k/alpha)].

Indeed its derivative in z changes from negative to positive there.
Moreover f(0)=0 and f'(r)=(1+rS)^(-S/alpha)>=1-rS^2/alpha by convexity.
Integration yields f(r)>=r-r^2 S^2/(2alpha)>=3r/4>3r/16. Thus every direct
axis replacement also fails to improve the one-date minimum.

## Explicit escape and limitation

Let observers1,2,3 quit surely at date0 and let the pivot Never. Each observer
gets K whether it Quits or Continues, and all later deadlines also get K.
The pivot gets K by waiting and K-r by joining. This is an absorbing full
Nash profile, so the actual absorbing minimum m is0.

It lies in a different support stratum, outside the closure of the proper
ALL-END partial-Nash ray (1), whose z->infinity limit has J_r->r. The full
one-date feasible set need not be disconnected: along q_1=q_2=q_3=1,
reducing q_0 from1 to0 connects that ray limit to the absorbing escape.
There is no improving replacement of the minimizing point R_* by any proper
feasible one-date profile, any E_T, or its own append R_* graft E_T. Arbitrary
compositions and excursions through higher-cost points are not analyzed.
Positive-gap global provenance or a different replacement remains essential.
No claim is made about a minimum over arbitrary calendars.
The completion has repeated higher rewards and does not satisfy the generic
row-distinctness premises of the actual F source; positive-gap ancestry also
fails. No robustness under generic higher-reward perturbations is claimed here.
