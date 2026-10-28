# Chronological exclusion of two-owner tails in four-player quitting games

This ordinary mathematical theorem excludes an open region of the actual
two-owner source case. It does not assert uniform equilibrium for every table
in that region: finite calendars, three or four infinite owners, and inherited
endpoints remain separate cases. No new Lean theorem is claimed.

Each player privately and independently chooses a complete quitting law on the
natural dates plus Never. The first nonempty quitting coalition receives its
finite native reward Z; own-singleton, live, and all-Never rewards are zero.
Write U_i for prescribed terminal payoff, B_i for the supremum over EVERY
unilateral replacement law, and d_i=B_i-U_i. This includes all finite
deadlines, Never, and arbitrary private mixtures, hence all behavioral
responses along the unique live history. ALL-END means that Never attains
B_i for every player.

The principal theorem is entirely raw: it needs no positive absorbing gap,
genericity, minimum selection, or supplied calendar. It excludes an actual
profile with the stated support and full-response properties. Any proposed actual source with these properties is therefore excluded.

## 1. Raw data and two finite polyhedra

Let p,i,h,k be four distinct players. The native table Z has own singleton
and Never rewards zero. Put

 G=Z_i(p), J=Z_i(pi), A=Z_p(i), C=Z_p(pi),
 rho=G/J, a=1-rho.

Assume J!=0 and 0<rho<1. No additional sign condition on A or C is needed.
For each j=h,k put

 g_j=Z_j(p), d_j=Z_j(i), X_j=Z_j(jp), Y_j=Z_j(ji),
 c_j=g_j-rho X_j.

The following finite raw inequalities will supply tail comparability. Put

    gh=g_h-min(X_h,0), dh=d_h-min(Y_h,0),
    gk=g_k-min(X_k,0), dk=d_k-min(Y_k,0),

and require

    gh<0<dh,     dk<0<gk.                                  (R)

The max/min expressions are just explicit arithmetic on four pair and four
singleton entries. They assume no positive lower bound on actual tail mass.

Define a COMMON-ATOM polyhedron in variables (t,z):

 K={t>=0, 0<=z<=1, C z<=A,
                 c_j t+d_j-Y_j z>=0 for j=h,k}.                 (1)

Define a PIVOT-ONLY polyhedron in variables (t,y):

 O={t>=0, g_j t-X_j y+d_j>=0 for j=h,k,
          0<=y<=rho t if J>0,
          rho t<=y<=t if J<0}.                                 (2)

Including t=0 makes these closed polyhedra; the actual source only supplies
positive t, so this can strengthen the sufficient certificate, not weaken
its conclusion. Neither polyhedron contains a root, calendar, or equilibrium
witness. They depend only on singleton and participant pair rewards.

**Chronological exclusion criterion.** Suppose there are raw constants

 tau>0, delta>0, 0<eta<1-rho

such that the following THREE affine implications hold:

 (t,z) in K  ==>  z>=rho+eta,                            (3)
 (t,z) in K  ==>  a t+tau z>=tau+delta,                  (4)
 (t,y) in O  ==>  t<=tau.                               (5)

**Theorem.** Under (R) and (3)--(5), there is NO actual ALL-END profile
with positive marginal Never masses and zero debts for all observers i,h,k
such that, after a finite date, only p and i have finite atoms and both have
infinitely many. Every other finite reward in the table is unrestricted.

More generally the same exclusion holds without (R) whenever the proposed
tail has uniformly comparable remaining finite masses. Section2 produces
this property directly from (R), so the principal raw theorem assumes no
comparability witness.

For fixed tau,eta,delta, (3)--(5) are finite linear-program checks in two
variables, or may be certified by nonnegative combinations of their affine
inequalities. Thus the hypothesis is a finite raw reward predicate. It is
independent of the unknown source's tail-comparability constants, Never
masses, earlier head, or minimizing value. Empty K or O cause no difficulty;
the proof still applies, though earlier tests often already exclude them.

Inequality (4) tests the OUTPUT ratio of a common atom, not its input ratio.
It permits common atoms whose input t is inside the pivot-only region,
provided that their output leaves it. No separation between the INPUT
projections of the two polyhedra is required.

## 2. Actual tails and the raw comparability bound

Suppose an actual profile as in the conclusion exists. Condition the two
independent laws once at a finite cut after all other owners' last atoms.
Their Never masses Np,Ni are strictly positive. Let

 alpha_n=Pr(Tp=n), beta_n=Pr(Ti=n),
 P_n=sum_(m>=n)alpha_m, I_n=sum_(m>=n)beta_m,
 u_n=P_n/Np, v_n=I_n/Ni, t_n=u_n/v_n.

Both P_n,I_n are positive and tend to zero. Every conditional tail remains
ALL-END and observer-exact. Pull back any suffix deviation through its finite
survival history to prove ALL-END; zero observer debt and positive suffix
survival then force zero suffix debt. Equivalently each observer's law is
supported on full-cap responses, and Never is one of them.

Here is a direct proof of comparability. Let f_p,f_i denote the conditional
remaining finite probabilities and q_p,q_i the current hazards. They satisfy
0<=q_j<=f_j. If M bounds all absolute rewards, a quiet observer j has

    Never-Quit = g_j f_p+d_j f_i-X_j q_p-Y_j q_i+E_j,
    |E_j|<=6M f_p f_i.                                  (E)

To see the bound, outside the event that both clocks are finite the Never
payoff has exactly its singleton contribution; its error is at most
3M f_p f_i. The corresponding immediate-Quit expansion has error at most
3M q_p q_i. Combining the two gives (E), uniformly over every date.
ALL-END and q_j<=f_j imply

    gh f_p+dh f_i >= -6M f_p f_i,
    gk f_p+dk f_i >= -6M f_p f_i.

Both finite masses tend to zero. Eventually 6M f_i<=(-gh)/2 and
6M f_p<=(-dk)/2. Absorbing these error terms proves

    (-dk)/(2gk) <= f_p/f_i <= 2dh/(-gh).                 (RB)

Since f_p/f_i=t_n(1+v_n)/(1+u_n), with u_n,v_n tending to zero, there are
fixed 0<ell<=U<infinity with ell<=t_n<=U at every sufficiently late date.
No positive gap, source minimum, or genericity was used in this argument.
In the more general comparable-tail version, start directly from this bound.

The active observer's exact comparisons give

 J alpha_n<=G P_n, with equality if beta_n>0.                    (6)

At a COMMON date beta_n>0 this forces alpha_n=rho P_n>0. Put
z_n=beta_n/I_n. The exact pivot comparison is C z_n<=A. Both infinite
supports imply z_n<1. The exact normalized ratio update is

 t_(n+1)=a t_n/(1-z_n).                                        (7)

At a PIVOT-ONLY date beta_n=0,alpha_n>0, put x_n=alpha_n/P_n.
Then 0<x_n<1 and (6) gives x_n<=rho if J>0, or x_n>=rho if J<0.
The exact update is

 t_(n+1)=(1-x_n)t_n.                                           (8)

A partner-only date is impossible by (6). An empty date changes no ratio.
These statements retain the original head: no prefix or suffix is replaced.

For completeness, (7) and comparability also give a source-dependent
uniform z collar: 1-z_n=a t_n/t_(n+1)>=a ell/U>0 at every late common date.
The proof below can avoid division limits by using (4), but this bound
confirms that all limiting actual common rates lie strictly below1.

## 3. Why the raw polyhedra govern all late dates

Write the conditional remaining finite probabilities as

 f_p=P_n/(Np+P_n), f_i=I_n/(Ni+I_n).

Their ratio is f_p/f_i=t_n(1+v_n)/(1+u_n)=t_n+o(1), uniformly down
the selected tail. Equation (E) and ALL-END give

    g_j f_p+d_j f_i-X_j q_p-Y_j q_i >=-6M f_p f_i.

At a common date q_p=rho f_p and q_i=z_n f_i. Dividing (E) by f_i
and passing to any subsequential limit of (t_n,z_n) gives
c_j t+d_j-Y_j z>=0. The pivot inequality and the obvious bounds pass
to the limit too. Thus every common-date accumulation point lies in K.

At a pivot-only date q_p=x_n f_p,q_i=0. Divide (E) by f_i and put
y_n=x_n t_n. Every subsequential limit (t,y) lies in O. The conversion
from conditional finite ratios to t_n costs o(1), since x_n<=1 and
t_n remains bounded. Compactness of t_n and x_n,z_n gives accumulation
points for every infinite subsequence of occupied dates.

Consequently, for all sufficiently late common dates, (3)--(4) imply

 z_n>=rho+eta/2,
 a t_n+tau z_n>=tau+delta/2.                              (10)

Otherwise a violating infinite subsequence would have a limit in K,
contradicting its fixed positive margin. Likewise all sufficiently late
pivot-only dates satisfy

 t_n<=tau+delta/4.                                        (11)

This is the only approximation step. It allows arbitrary finite higher
rewards: their effect in (E), after division, tends to zero with f_p.

## 4. Chronology forces an impossible one-way itinerary

At a late common date, (7) and the second inequality of (10) yield

 t_(n+1)-tau
   =[a t_n-tau(1-z_n)]/(1-z_n)
   >=delta/[2(1-z_n)]>=delta/2.                           (12)

Thus its output is strictly larger than every sufficiently late pivot-only
input allowed by (11). The first inequality of (10) gives the uniform
multiplicative increase

 t_(n+1)>=gamma t_n,
 gamma=a/(a-eta/2)>1.                                    (13)

Choose any common date after all these bounds apply; infinitely many exist
because the partner has infinitely many atoms. Following it, empty dates
leave the ratio unchanged, and another common date increases it. A next
pivot-only date cannot occur: at its input the ratio would still be at least
tau+delta/2, contradicting (11). Hence every subsequent occupied date is
common. There are infinitely many, so (13) forces t_n to infinity,
contradicting the source bound t_n<=U. This proves the criterion.

The direction of time is essential. The existing interval tests establish
that the common and pivot-only feasible sets are nonempty; they do not
ensure that the output of one can reach an admissible input of the other.
No global-minimality assertion about a conditional tail is used. The raw proof
uses no global minimality at all: condition (R) supplies comparability.

## 5. Exact residual control missed by the earlier screens

Use pivot p=0 and partner i=1, quiet observers h=2,k=3, and

 Gamma=[0,1,4,-5; 1,0,-2,-1; -1,1,0,3; 2,-1,-4,0].

Fix only these participant pair entries:

 Z1(01)=2, Z0(01)=-1,
 Z2(02)=2, Z2(12)=-11/10,
 Z3(03)=3/2, Z3(13)=1/10.                              (14)

All other nonsingleton rewards may be chosen arbitrarily finite.
Then rho=1/2, A-rho C=3/2, and (1) reduces to

 t<=1/2+(11/20)z,
 t>=4/5+(2/25)z,
 0<=z<=1, t>=0.                                         (15)

In particular z>=30/47 and t>=40/47. Condition (R) holds with
(gh,dh,gk,dk)=(-1,21/10,2,-1). The pivot constraint -z<=1 is redundant.
Polyhedron O is

 t+2y<=1, 2t-(3/2)y>=1, 0<=y<=t/2,                     (16)

so t<=1. It is nonempty: (t,y)=(3/4,0) belongs to it.
Choose tau=101/100, eta=1/10, delta=1/25. Equations (15) give

    z-(rho+eta)>=9/235,
    (1/2)t+(101/100)z-(tau+delta)>=19/940,
    tau-t>=1/100 on O.

Thus all three chronological implications have explicit strict margins.
The output test is essential here: the common point (t,z)=(19/20,9/10)
is feasible, and its input t=19/20 also belongs to the pivot-only projection,
for example with y=0. Requiring disjoint common and solo INPUT regions would
miss this control.

The prior pair screen PASSES. Its opposed coefficients are c_h=-2,c_k=5/4;
its functions are b_h(z)=1+(11/10)z>0 and b_k(z)=-1-z/10<0. The cross
inequality is

 c_k b_h(z)-c_h b_k(z)=-3/4+(47/40)z>=0,

so its interval is exactly [30/47,1). A>0 and O is nonempty, so the earlier
screen does not require rho to belong to that interval. This is a strict
comparison between necessary source screens, not a counterexample to UE.

In fact the entire I2 case is absent at pivot0 for this raw class. The other
two prospective partners already fail the first contact-ratio test:

 partner2: G=Gamma20=-1, J=Z2(02)=2, hence G/J=-1/2;
 partner3: G=Gamma30=2, J=Z3(03)=3/2, hence G/J=4/3.

The displayed inequalities already have strict slack. Both polyhedra remain
uniformly bounded near this control: the first common inequality bounds t
using z<=1, and the first solo inequality bounds t using y>=0. Compactness
therefore preserves the three strict margins under small reward perturbations.
Condition (R) and the other partners' ratio failures are also strict. Thus a
nonempty open neighborhood of these singleton/pair data has the same
exclusion of all three I2 partners at pivot0. All remaining finite source-genericity polynomials may also be avoided
within this region, although this theorem does not need genericity. The
finitely many higher rewards have no sign or size restriction; the sufficiently
late cut may depend on their size.

## 6. Full singleton residual audit

The singleton matrix is not eliminated by the existing matrix-only source
filters. Its determinant is10 and

 Gamma^-1=[1,-2,1,2;
           2/5,2/5,4/5,1/5;
           2/5,-11/10,3/10,7/10;
           1/5,-4/5,2/5,3/5].

All inverse entries are nonzero. Its strict positive inverse columns are
0,2,3, so0 is the least such pivot. Every column has a negative entry.
The pair13 is mutually negative. All principal pairs are nonsingular,
and the principal triple determinants, in order012,013,023,123, are
(6,3,4,10), all nonzero.

At the LCP offset -e0, the full support root is
(1,2/5,2/5,1/5), with index+1. The only principal triples with positive
active roots are012 and023; their omitted slacks are respectively -1/3
and -1. Triple013 has negative active coordinates; triple123 has zero
target and invertible principal block, hence no positive root. A pair
containing0 fails its nonzero observer equation, and a pair omitting0 has
zero target and nonsingular principal block. Singletons fail the target
or a negative column. Hence the full root is the unique complementary
root and the degree is+1. Negative columns and nonsingular principal blocks
also imply R0 by the same homogeneous support argument.

The only inverse-positive principal triple is023, with inverse

 [3,5,3; 3/2,5/2,5/4; 1,2,1].

Its outside row1 has inverse weights (-1,-2,-1/2), all negative, so the
passive-child existence test fails. The other three principal inverses have
mixed signs. Thus these singleton tests, including the strict positive full inverse
column and failure of the passive-child selection, all pass. This audit makes no claim that arbitrary completions
fail all collision-dependent UE criteria: the new conclusion concerns the
actual I2 source, not the entirety of the reward table's equilibrium status.

## 7. Strict improvement over pointwise multiplier tests

The control also fails every pointwise separating-multiplier attempt to
exclude its pair01 at pivot0. At leading order choose finite masses and
current atoms, in player order0123, as

 f=(19/20,1,0,0), q=(19/40,9/10,0,0).

These may be multiplied by any sufficiently small positive common scale.
They satisfy 0<=q<=f, both owners act, and direct arithmetic gives

 E=Gamma f-J q=(19/10,0,9/100,39/400).

Here J has the participant-pair entries of (14); its unspecified entries
do not enter, because f and q vanish outside01 and own diagonal entries
are zero. Thus every leading ALL-END inequality is satisfied, observer1
has exact contact, and both quiet inequalities are strict. No linear
combination of these nonnegative inequalities and that zero equality can
prove a negative value. This rules out every attempted exclusion obtained solely by choosing
separating weights for the same one-date contact inequalities.

This leading point is not an actual infinite calendar: the chronological
criterion proves precisely that feasible local data cannot be concatenated
into a bounded-ratio I2 tail. It establishes nonredundancy of the new
source exclusion without claiming failure of every known UE theorem.

## 8. Actual-source consumer and formalization

The theorem excludes an actual profile, so its use in a source classification
is direct. At a proposed source pivot p, read G,J,A,C and the two quiet rows
from the unchanged native reward table. Check (R) and (3)--(5). If the source
has positive marginal Never masses, ALL-END and zero observer debts, it
cannot have an eventual two-owner tail with this partner. No head, minimum
value, continuation, or successful calendar is an extra strategic input to
the raw predicate. The full head is retained without alteration.

For the displayed open region at pivot0, the same conclusion holds for every
partner: one is removed by the chronological theorem and the other two by
the exact contact-ratio identity. Hence the complete two-owner case at that
pivot is absent. This does not assert that every alleged counterexample
has this matrix or these pair rewards, or that every minimizing source is
actual. Finite calendars, three or four infinite owners, and inherited
endpoints remain unresolved by this theorem.

The complete-law interpretation matches quittingStoppingLawExpectedPayoff
and quittingStoppingLawReplacementPayoffCap in
UniformEquilibrium/Quitting/Paths/StoppingLawOperationalDistance.lean.
The inspected finite cap identity is
quittingContinuationBestResponseValue_rootThenContinuation_eq_max in
UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean. These are source
correspondences; the proof above uses the explicitly stated clock payoffs
and supplies its own comparison identities. No Lean command was run.

Formalization can separate the following declarations: the effective quiet-row
comparison and raw ratio bound; the two affine polyhedra and their three
implications; the exact normalized-tail updates; accumulation-point transfer
with vanishing collision error; and the scalar no-return/divergence lemma.
All probabilistic estimates are uniform over the full deadline/Never menu.
No public correlation, extra signal, or bounded-calendar restriction is used.

The result is a residual-mode exclusion, not a UE existence theorem. It
leaves the common-support cells that allow the neutral rate z=rho outside
its certificate, and supplies no arbitrary-table Fin4 closure.
