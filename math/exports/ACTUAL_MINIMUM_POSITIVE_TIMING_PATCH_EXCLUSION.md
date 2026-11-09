# A positive timing coefficient excludes guarded pair-star patches in global minima

## Exact statement

There are four players I={0,1,2,3}. A native quitting table assigns a finite
real reward Z_i(S) to each nonempty coalition S, with Z_i({i})=0 and AllNever
payoff0. Players independently choose complete laws on natural dates and
Never. Let U_i be prescribed expected payoff, B_i the supremum over every
unilateral behavioral replacement, e_i the pure Never payoff, N_i the
ORIGINAL marginal Never mass, d_i=B_i-U_i, and nu=product_i N_i. ALL-END
means B=e. Fix pivot p and call the other three players observers. Put

 Gamma_ij=Z_i({j}), J_ij=Z_i({i,j}) for i!=j,
 Gamma_ii=J_ii=0.

Assume the following explicit raw conditions:

 Gamma is invertible; G_i=Gamma_ip!=0; rho_i=J_ip/G_i>1;
 Gamma_ij/G_i<0 for distinct observers i,j;
 Gamma_pi>0>J_pi for each observer i.                         (Raw)

Define lambda_i=1-1/rho_i in(0,1), w^T=1^T Gamma^-1, and

 A_i=Gamma_pi lambda_i+J_pi(1-lambda_i),
 K_j^(i)=-Gamma_jp+lambda_i Gamma_ji+(1-lambda_i)Z_j({p,i})
             for j outside{p,i}, K_p^(i)=K_i^(i)=0,
 C_i(r)=A_i-r w^T K^(i).                                    (Coeff)

Fix ANY finite r>=0. Suppose an actual profile P has positive ORIGINAL
Never mass for every player, is ALL-END and observer-optimal, and globally
minimizes d_p+r nu among all actual observer-optimal profiles, or on a larger
feasible carrier containing those profiles.

Delete empty dates. A guarded pair-star patch is a finite consecutive
interval on which every date has positive quitting hazards exactly at p
and one observer, and every inactive observer's Quit-versus-Never comparison
is strict. A run is a maximal consecutive stretch of one observer label
within the patch. For an observer i, call such a patch i-controlling if:

* it contains three i-runs, with nonempty intervening run words containing
  no i; and
* after the third i-run it contains four consecutive runs a,b,c,a or a,b,c,b,
  where a,b,c are distinct observers.

If C_i(r)>0, no sufficiently late i-controlling patch exists.              (Patch)

All support patterns and ties OUTSIDE the selected patch are allowed,
including triple/full roots and roots without the pivot. There is no
bound on patch lengths, run lengths, bridge lengths, or gaps between patches.
The concrete nine-run word i j i k i j k i j, for distinct i,j,k, is
one i-controlling word; arbitrary no-i pair-run bridges are also covered.

Consequently, if P eventually has only pair-star dates, all three observer
labels recur, and all quiet comparisons are eventually strict, then

 C_i(r)<=0 for every observer i.                             (Conclusion)

Equivalently, ANY one positive C_i(r) excludes that entire recurrent mode.
There is no structured-matrix identity, sign assumption on Gamma^-1 e_p,
upper bound on r, pivot-contact assumption, or Never-mass equality.
If (Raw) holds and some A_i>0, the exclusion holds for all sufficiently small
nonnegative penalties. This is a whole explicit open inequality chamber,
not only a neighborhood of one structured family. For arbitrary r the
criterion also uses the six passive pair rewards in (Coeff). Every reward
not entering (Raw) or (Coeff) is unrestricted finite. Analytic neighborhoods
below may depend on the fixed table and fixed r.

## Conjecture-facing change and strategic inputs

The theorem supplies an eventual forbidden finite-patch language for actual
minima, and three explicit necessary inequalities in the recurrent guarded
pair-star mode. A single positive coefficient suffices; the other two may
have any sign. The comparison uses three occurrences of that observer and
a later four-run chart, even when their calendar distances diverge. No
successful correction strategy or uniformly invertible long bridge is assumed.

The actual observer-constrained minimum, ALL-END, positive original Never,
the selected pivot/raw chamber, and the availability of guarded controlling
patches remain inputs. This theorem does not select or realize such a source
from arbitrary games. It is a conditional actual-source restriction, not a
new UE reward-table existence class or a solution of Fin4. Quiet ties inside
the selected patch, mixed-support bridges, other raw chambers, the case
C_i(r)<=0 for every i, and nonrealized sources remain outside the exclusion.

## Complete behavioral semantics and actual tails

Before absorption there is only one public live history at each date.
Sampling one player's private randomness in advance expresses any behavioral
response as a mixture of deterministic deadlines and Never. Hence B prices
all unilateral behavioral deviations. No public lottery, correlation device,
or execution after an infinite calendar is used.

For root hazards q put H_i=product_(j!=i)(1-q_j), c=product_j(1-q_j), and

 pi_i(S;q)=product_(j in S)q_j product_(j notin S,j!=i)(1-q_j),
 Q_i=sum_(S subset I\{i}) pi_i(S;q) Z_i(S union{i}),
 P_i=sum_(nonempty S subset I\{i}) pi_i(S;q) Z_i(S).

For a literal continuation the exact recursions are

 e'_i=P_i+H_i e_i,
 U'_i=q_i Q_i+(1-q_i)P_i+c U_i,
 B'_i=max(Q_i,P_i+H_i B_i), N'_i=(1-q_i)N_i.                  (Root)

Positive original Never makes every finite head survival positive. ALL-END
and observer optimality pass to every actual conditional tail, since a better
tail response could be used after that cut. Every active observer's Quit
offer equals its END cap. Conditional remaining finite masses tend to0;
conditional payoff and Never offers tend to0; conditional joint Never tends
to1. Also sum_t q_i(t)<infinity because product_t(1-q_i(t))=N_i>0.

Deleting q=0 dates preserves U,e,N and all retained deadline values. The new
deadline set is a subset of the old one, while Never still attains the old
cap by ALL-END. Thus B and the minimizing objective are preserved. Infinitely
many nonempty dates can again be indexed by the natural numbers.

Pivot strictness on late pair dates holds even with arbitrary future
support. Write m_j for observer j's conditional remaining finite marginal
mass, M=sum_j m_j, gamma=min_j Gamma_pj>0, and
R=max_S |Z_p(S)| over nonempty observer coalitions. Independence gives
probability at least M-M^2 that exactly one observer ever quits. Every such
outcome pays the Never pivot at least gamma. A simultaneous first coalition
with two or more observers has probability at most
sum_(j<k)m_j m_k<=M^2/2. All other singleton outcomes also pay positively, so

 e_p >= gamma M-(gamma+R/2)M^2.

Since M tends to zero, e_p>0 at every sufficiently late cut with M>0.
At a pair date p,i, M>0 and the pivot Quit offer is J_pi q_i<0. Thus every
late pair-date pivot comparison is automatically strict. Earlier pivot
contacts will be preserved exactly by fixing every entrance cap.

## Exact pair-run laws

Use the ratios in (Raw). Consider a finite maximal run of L dates
whose active owners are p,i. Let E be its entrance Never vector and b its
continuation vector. The pivot's conditional absolute atoms alpha_t within
this run satisfy the active observer's tied pure-deadline equations

 G_i sum_(u<t)alpha_u+J_ip alpha_t=E_i.

Consequently

 alpha_t=(E_i/J_ip)lambda_i^t, t=0,...,L-1.                    (Atoms)

Write the observer atoms beta_t=g w_t, where g=sum beta_t and every w_t>0,
sum w_t=1. Define

 theta=lambda_i^L, m=sum_t w_t lambda_i^t,
 f=sum_t alpha_t=(1-theta)E_i/G_i.                            (Mass)

The actual profile has E_i/J_ip>0 and 0<f,g<1; E_i itself may be negative.
Fixing the weights w and varying E,g preserves the geometric pivot atoms.
The probabilities a,beta,c_pair of first head coalitions {p},{i},{p,i} are

 c_pair=(E_i/J_ip)g m,
 a=f-(E_i/G_i)g(m-theta),
 beta=g-(E_i/G_i)g(1-lambda_i m),
 a+beta+c_pair=f+g-fg.                                      (Outcomes)

The exact forward cap map is

 b_i=theta E_i/(1-f),
 b_p=(E_p-Gamma_pi g)/(1-g),
 b_j=[E_j-Gamma_jp a-Gamma_ji beta-Z_j({p,i})c_pair]
                         /[(1-f)(1-g)]  (j outside{p,i}).     (Caps)

Its active coordinate follows from E_i=G_i f+(1-f)b_i. Equations (Atoms)--(Caps)
make every active-observer deadline and its Never response equal to E_i.
The pivot payoff and joint survival propagate by

 u_before=Gamma_pi beta+J_pi c_pair+(1-f)(1-g)u_after,
 nu_before=(1-f)(1-g)nu_after.                              (Payoff)

All these maps are analytic near E=g=0, uniformly over the compact set

 theta in[0,lambda_i], m in[0,1].                           (Compact)

The endpoint theta=0 is only an analytic limit; no infinite run is performed.
In x=Gamma^-1 E coordinates, the zero-data derivative of(Caps) is

 x_next=L_i(theta)x-e_i g,
 L_i(theta)=I-[(1-theta)/G_i]e_p Gamma_i.                    (Linear)

Here e_i means a coordinate vector and Gamma_i a row. Put
z_ij=(Gamma_ij/G_i)(theta_i-1)>0 for distinct observers. Then
L_i e_p=theta_i e_p, L_i e_i=e_i, L_i e_j=e_j+z_ij e_p.
Also L_i v=v for v=Gamma^-1 e_p.

## A uniformly invertible four-run chart

Take run labels i,j,k,i or i,j,k,j, where i,j,k are distinct; call the last
label l. Starting from any nearby entrance vector E_0, the four maps(Caps)
determine E_1,...,E_4 from four observer masses g_1,...,g_4. Instead of
fixing all four final coordinates directly, impose

 (E_4)_a=(E_4^old)_a for a!=l,
 (E_3)_l=(E_3^old)_l.                                      (Reduced)

For actual theta_l>0 the last equation implies the missing final equality
exactly: the last active map theta_l E_l/[1-(1-theta_l)E_l/G_l] depends only
E_l, not g_4. This replacement avoids a derivative proportional to a tiny
theta_l when the last run is long.

The reduced Jacobian with respect to the four g's is uniformly invertible
at zero data, including all limiting parameters in(Compact). To prove it, set
x_0=0 and let u_1,...,u_4 be a kernel vector. The last reduced equation says
Gamma_l x_3=0, hence L_l x_3=x_3 and x_4=x_3-e_l u_4. Since also
Gamma_l x_4=0, the other three final equations and invertibility of Gamma
give x_4=0, or x_3=e_l u_4. Iterating the first three runs gives

 x_3=-u_1 e_i-u_2 e_j-u_3 e_k
   -[u_1(z_ki+theta_k z_ji)+u_2 z_kj]e_p.

If l=i, this forces u_2=u_3=0, u_4=-u_1 and
u_1(z_ki+theta_k z_ji)=0. Its coefficient is at least
(-Gamma_ki/G_k)(1-lambda_k)>0. If l=j, it forces u_1=u_3=0,
u_4=-u_2 and u_2 z_kj=0 with the same positive lower bound.
Every kernel vector is therefore zero. Compactness in(Compact) supplies a uniform
inverse bound and a uniform finite-dimensional implicit-function chart.

This chart permits arbitrary small entrance-cap changes, or changes in any
run moment with every entrance and final cap fixed. Each actual finite
window has some two-sided feasible neighborhood: its positive atoms and
finitely many strict quiet/pivot comparisons persist. That radius need not
be uniform. The exact contacts and the retained strict comparisons, with
the complete continuation fixed, give full caps and observer optimality by
(Root). If every entrance cap is fixed, the entire earlier head is preserved,
including tied pivot deadlines.

For the eventual recurrent pair-star corollary, controlling windows occur
arbitrarily late. Adjacent maximal run labels differ and every run is finite.
If there were only finitely many triples of
three distinct labels, the late word would alternate two labels, contrary
to recurrence of all three. Append the next run to any late distinct triple;
it repeats the first or second label and gives precisely the two words above.

## A uniform C2 estimate over arbitrarily many runs

For observer caps z_j=E_j/G_j fix one reference observer a and use

 sigma=z_a/(1-z_a), tau_j=(z_j-z_a)/(1-z_a), tau_a=0,
 bar_u=u_p/(1-z_a), bar_nu=nu/(1-z_a), together with E_p.

Center bar_nu at1. At g=0 the EXACT map of any run is linear:

 sigma^+=theta sigma-(1-theta)tau_j,
 tau^+=tau, E_p^+=E_p, bar_u^+=bar_u, bar_nu^+=bar_nu.         (Projective)

Its arbitrary subproducts have a common bound M: the coefficient of sigma
is a product of theta's, and the absolute sum of the coefficients of tau
is 1 minus that product. The other coordinates are fixed.

Uniform analyticity writes every run map as

 Phi_k(y,g_k)=A_k y+g_k R_k(y,g_k),                          (Perturbation)

where R_k and its derivatives through order3 are uniformly bounded on one
fixed neighborhood, over every run length and moment. For any finite bridge
with eta=sum g_k small, its composition differs in C2 from A_n...A_1 by at
most C eta exp(C eta), uniformly in the number of runs. Here and below the
C2 norm is taken on a sufficiently small fixed neighborhood of the origin.

For completeness, values and first derivatives follow by Duhamel expansion
and discrete Gronwall, using the bound M on EVERY subproduct, not merely on
individual A_k. A common neighborhood is valid since each prefix value is
bounded by M|y_0|+C eta exp(C eta). For second derivatives the chain rule gives

 D2 F_(k+1)=D Phi_k(F_k) D2 F_k
              +D2 Phi_k(F_k)[D F_k,D F_k].

In (Perturbation), D2_y Phi_k= g_k D2_y R_k. The previously obtained first-derivative
bound and bounded derivative subproducts therefore bound this sum by
C eta exp(C eta). The reference linear composition has zero second derivative.
This proves the claimed estimate. Smooth endpoint coordinate changes add only
uniformly bounded jets; comparing their actual arguments with zero adds an
error tending to zero with the maximum conditional tail finite mass.

Positive original Never gives summable date hazards. Each run observer mass
is at most the sum of its observer's date hazards, so the remaining sum of
g_k tends to zero. Thus every arbitrarily long finite bridge on a sufficiently
late actual tail is uniformly close in C2 to its zero-observer-mass reference.
No sum of quiet cap sizes is used; those sizes need not be summable.

## Timing lemma

If C_i(r)!=0, a sufficiently late i-run followed within a guarded pair-star
patch by a controlling four-run window must have length one. To prove this,
take such a run of length L>=2,
keep its observer mass g fixed, and transfer normalized observer weight
between its first and last dates. Both original weights are positive, so
its moment m varies in both directions. The conversion factor
1-lambda_i^(L-1) is at least1-lambda_i. Put h=(E_i/G_i)g>0. Differentiating
(Outcomes) gives the exact factorization

 (partial_m a,partial_m beta,partial_m c_pair)
                   =h(-1,lambda_i,1-lambda_i).                (Moment)

The direct head pivot-payoff derivative is h A_i, its head Never-vector
derivative is h K^(i), and its joint-survival derivative is0. Thus its
forward cap and payoff impulses are -h K^(i)/survival and -h A_i/survival.

Use the later controlling four-run window inside the patch. Keep the OBSERVER masses,
normalized weights and lengths of the intervening runs fixed; their pivot
masses are recomputed from their changing entrance caps. Use (Reduced) to
solve the four correcting masses, fixing every entrance and final cap.
The exact contacts and all finite strict inequalities give an actual
comparison curve on some two-sided moment interval.

The bridge estimate proved above preserves the exact factor h. Correcting
mass derivatives are O(h) by the uniform four-run inverse. After division
by h, all derivative errors are bounded by a constant times the maximum
conditional remaining finite mass plus the remaining sum of observer run
masses. This bound tends to zero uniformly over the intervening run counts,
lengths, and original weights. In particular h need not dominate the square
of another state coordinate.

At zero data, after dividing by h, fixed entrance and final caps force the
correcting first-order total atom vector a_total to satisfy
Gamma a_total=-K^(i). Its pivot-payoff contribution is0 since K_p^(i)=0;
its survival contribution is -1^T a_total=w^T K^(i). Consequently

 (1/h) d/dm[-u_p,entrance+r nu_entrance]
       =-A_i+r w^T K^(i)+o(1)=-C_i(r)+o(1).                  (Timing)

Equivalently, the zero-data invariants u-E_p and nu+w^T E give this balance.
Their errors across arbitrary bridges are controlled by (Perturbation).
The scalar forward payoff and survival coefficients tend to1, so solving
backwards for the entrance values introduces only another vanishing error.

Fixing the entrance cap makes the whole objective variation a positive
joint head-survival factor times the bracketed variation. At a minimum its
two-sided derivative must vanish, contradicting (Timing) for every
sufficiently late such L>=2 run when C_i(r)!=0. This proves the timing lemma.

## The three-occurrence loop

Suppose C_i(r)>0 and choose a sufficiently late i-controlling patch. By the
timing lemma its three selected i-runs all have length one. The two
intervening bridges are nonempty and contain no i-runs.
Only the observer masses at these three i-dates will have nonzero first-order
variations. Write x=Gamma^-1 E. Starting from x=0, only x_p and x_i can then
be nonzero. On a bridge run of label j!=i, (Linear) restricts to

 x_p^+=theta_j x_p+(1-theta_j)c_ji x_i,
 x_i^+=x_i,   c_ji=-Gamma_ji/G_j>0.                         (Scalar)

The bridge composition is x_p^+=a x_p+b x_i. Let
lambda_max=max_j lambda_j<1, c_min=min_(j!=i)c_ji>0 and
c_max=max_(j!=i)c_ji. Every nonempty bridge satisfies

 0<a<=lambda_max, c_min(1-lambda_max)<=b<=c_max.               (Bounds)

For actual finite runs a>0; the limiting a=0 is harmless. Indeed a is the
product of theta's and b is a positive weighted sum of the c_ji whose
weights sum to1-a. This proves the uniform bounds, including unbounded
numbers of runs and unbounded physical run lengths.

Call the two bridge coefficients (a_1,b_1),(a_2,b_2). At the first i-date
choose its observer-mass tangent u_1=1. Since its pivot tangent is zero,
the state just after it is x_p=0,x_i=-1. Just before the second i-date it
is x_p=-b_1,x_i=-1. At an i-date the pivot update is lambda_i x_p.
Choose the second and third observer tangents as

 u_2=-1-a_2 lambda_i b_1/b_2,
 u_3= a_2 lambda_i b_1/b_2.                                (Controls)

Then the state just before the third i-date is x_p=0,x_i=u_3, and just after
that date it is exactly zero. All other x coordinates have stayed zero.
Every later zero-data run therefore also has zero state and zero pivot
atom tangent. The direction and all its state values are uniformly bounded
by (Bounds), independent of the bridges.

The only nonzero simultaneous pivot/observer atom product is at the middle
i-date. Its value is

 E_pi=(1-lambda_i)b_1(1+a_2 lambda_i b_1/b_2)>0.              (Product)

The total atom tangent of each player is zero because x returns to zero.
All observer atom tangents except those of i vanish identically.

## Quadratic calculation in global absolute atoms

The following expansion uses GLOBAL ABSOLUTE planned-time atoms measured
from the entrance of the complete modified finite window, not conditional
hazards or run-local atoms. For each player the coordinate change is

 alpha_i,k=q_i,k product_(l<k)(1-q_i,l),
 q_i,k=alpha_i,k/[1-sum_(l<k)alpha_i,l].                     (Coordinates)

It is analytic near zero with identity first derivative. At the zero-tail
reference the conditional continuation Never vector is1, so joint Never
is exactly product_i(1-sum_k alpha_i,k). Since every total marginal atom
tangent in the loop is zero, its quadratic coefficient in these absolute
coordinates is zero. The same assertion alone would be false in hazard
coordinates; the augmented-objective argument below transfers the Hessian.

For a complete finite collection of atom tangents define
T_ab=sum_(k<l) a_a,k a_b,l and E_ab=sum_k a_a,k a_b,k.
Zero total masses give T_pi+T_ip+E_pi=0. The active observer's contact
identities give its quadratic debt coefficient

 0=D_i=G_i T_ip-(J_ip-G_i)E_pi,

hence T_ip=(rho_i-1)E_pi and T_pi=-rho_i E_pi. The pivot's quadratic debt is

 D_p=Gamma_pi T_pi-(J_pi-Gamma_pi)E_pi
    =-rho_i A_i E_pi.                                     (Debt)

These identities follow directly by expanding independent first-coalition
probabilities to second order; there are no other nonzero observer tangents.

In these global absolute atom coordinates, the quadratic term of joint Never
is zero because every total marginal mass tangent is zero. The Never payoff quadratic terms of p and i are zero.
For any quiet observer j, the explicit pair expansion gives

 P_j,2=-Gamma_jp T_ip-Gamma_ji T_pi
                  +(Z_j({p,i})-Gamma_jp-Gamma_ji)E_pi
       =rho_i K_j^(i) E_pi.                               (Passive)

In physical hazard coordinates the first derivative of -u_p+r nu at zero
is -(Gamma_p+r1^T)sum da. Adding the fixed-cap constraint combination
E_p+r w^T E cancels that entire first derivative. The augmented objective therefore has zero ambient differential. Its
Hessian is unchanged by (Coordinates), because the extra coordinate-change
term is multiplied by that zero differential. Likewise, second-order
corrections to the cap-solving curve do not affect its objective coefficient.
Equations (Debt)--(Passive) give the exact constrained coefficient

 Q_r=D_p+r w^T P_2
    =-rho_i C_i(r)E_pi
    =-C_i(r)b_1(1+a_2 lambda_i b_1/b_2)
    <=-C_i(r)c_min(1-lambda_max)<0.                         (Curvature)

This identity is the key gain: the SAME coefficient C_i(r) governs the
first-order timing test and the second-order three-occurrence loop.
No small-penalty limit or structured-star cancellation is used.

## Exact finite correction and uniform passage to actual tails

Use the controlling four-run window after the three selected i-runs,
inside the same patch.
Keep every intermediate observer mass, normalized weight and length fixed.
Prescribe a small parameter s multiplying the three directions(Controls), and use
the four correcting observer masses to fix all final caps by the reduced
chart. Keep all entrance caps fixed. In the zero-data reference, the loop
has already returned to zero before the correcting window, so all four
correcting mass FIRST derivatives are zero. Their second derivatives need
not vanish, and are accounted for by the zero ambient differential above.

The entire construction is finite for each chosen cut, though its length
may grow. To make the uniform passage precise, regard the composite map as
a function of the three selected masses, four correcting masses, entrance
caps, entrance pivot payoff and entrance joint Never. Bridge C2 estimates
from(Perturbation) and the finitely many controlled run maps give uniform C2 bounds
and uniform convergence of its two-jets to the zero-data reference. The
corrector's reduced cap Jacobian has a uniform inverse. The forward payoff
and survival coefficients in their respective entrance variables are
reciprocals of head survivals, which tend uniformly to one on late actual
tails. Thus the six endpoint equations (four reduced caps, payoff, Never)
solve for the four correcting masses and the two entrance values, with a
uniformly invertible block triangular derivative. Differentiating those
finite implicit equations twice proves uniform convergence of the resulting
objective second derivative to 2Q_r.

Here the zero-data reference retains every bridge/run parameter theta,m;
(Bounds) and (Curvature) hold uniformly over them. Actual cap/payoff errors tend to zero,
remaining sum g tends to zero, and fixed r is finite. Therefore a sufficiently
late construction has strictly negative second derivative, bounded away from
zero by half the uniform bound in(Curvature). The actual finite curve has a
nonempty two-sided feasible interval: every supported atom was positive,
and its finitely many quiet and pivot comparisons were strict. The exact
contacts, unchanged literal continuation, and fixed entrance caps preserve
ALL-END and observer optimality throughout the window and the earlier head.
Earlier pivot ties cause no difficulty.

Whole objective variation is a positive joint head-survival factor times
that conditional objective variation. A global minimum must have zero first
derivative and nonnegative second derivative along this curve. The obtained
negative second derivative is a contradiction. This proves (Patch).

For (Conclusion), suppose instead that the actual tail is eventually a
recurrent guarded pair-star calendar and some C_i(r)>0. Choose three late
consecutive i-runs. All three labels recur, so a controlling four-run window
exists later, as proved above. The finite interval joining them is an
arbitrarily late i-controlling patch, contradicting (Patch).

## Exact boundary calculation for the old five-date grammar

Take p=0, all unlisted rewards zero, and

 Gamma=[0,2/7,1/2,3/14;
        -1,0,1/2,1/2;
        1,-4/5,0,-1/5;
        1,-1/5,-4/5,0],
 J=[0,-10/21,-5/6,-1/2;
    -11/3,0,0,0;
     5,0,0,0;
     6,0,0,0].

Then det Gamma=17/50, Gamma^-1 e_p=(1,1,1,1), and every inequality in (Raw)
holds. Its coefficients are

 C_1(r)=3(577r+34)/1309,
 C_2(r)=(7026r+833)/3570,
 C_3(r)=-(361r-68)/714.

In particular A_i>0 for every observer, and C_1(r)>0 for every r>=0.
The cyclic word132 gives three five-date windows. With first observer-mass
tangent normalized to1, their exact zero-penalty curvatures are

 Q_0(13213)=44/819,
 Q_0(32132)=182/12225,
 Q_0(21321)=4727/71148.

All are positive: a five-word graph retaining nonnegative-curvature edges
contains this complete recurrent three-label cycle.

Instead take three occurrences of1 in 1321321 and follow them by the
controlling word2312. The two equal bridges32 have
b_1=b_2=14/75 and a_2 lambda_1=16/33. The observer-mass direction at the
three1-dates is (1,-49/33,16/33), with all other observer directions zero.
The simultaneous product is E_p1=686/9075, the endpoint atom vector is zero,
and the exact constrained objective coefficient is

 Q_r=-98(577r+34)/154275<0  for every r>=0.

The exact program below independently reconstructs these values from
first-outcome probabilities and verifies the coefficient (Curvature). No
actual minimum or positive-gap game is claimed for this boundary table.
Its role is to distinguish a five-date-only curvature argument from the
universally available three-occurrence loop.

## One actual guarded boundary construction

The support geometry is realizable: local contacts alone do not exclude it.
Use the following finite table:

 Gamma=[0,1,1,1; -2,0,1,1; 2,-1,0,-1; 2,-1,-1,0],
 J=[0,-1,-1,-1; -6,0,-3,-2; 15/2,-5,0,-3; 13/2,-3,0,0].

Initially set other rewards zero. Here
G=(-2,2,2), det Gamma=6, Gamma^-1 e_p=(1/3,1/3,1/3,1/3), and S=4/3.
The sign chamber has one negative G_i and every singleton column has a
negative entry. This is not claimed to evade every existing UE theorem.

Take rho=1/3, E=(6,-12,21/2,21/2), word01,02,03,01 and leading hazards

 a_0=(2,1,0,0), a_1=(1,0,1,0),
 a_2=(1,0,0,1), a_3=(1,1,0,0).

Direct calculation gives Gamma sum a=(1-rho)E. The8-by8 Jacobian imposing
four entrance caps and four active-observer contacts has determinant1728
(columns by date and owner, entrance rows first). The leading Quit-minus-END
vectors are

 (-7,0,-1/2,-1/2), (-6,-1,0,-1),
 (-5,-1,-1,0), (-4,0,-2,-1).

The finite inverse theorem therefore gives an exact four-date block
q(t)=t a+O(t^2) with entrance caps tE, terminal caps rho tE, active-observer
contacts, and strict quiet/pivot comparisons. Concatenate q(h rho^n) for
sufficiently small h>0. Hazards are proper and summable, so every original
Never mass is positive. Assigned caps match and tend to0; telescoping(Root)
identifies them with the actual law's Never offers. Every deadline is at
most END, every active observer deadline is tied, and Never is tied.
Thus B=e and observers have zero debt. Every pivot deadline is strict.
The negative conditional observer cap is allowed by the native payoff model.

For a finite prefix making all entrance caps positive, fix such a small h
and set these additional coordinates of the SAME game:

 Z_1(23)=Z_1(023)=2,
 Z_1(012)=Z_1(013)=Z_1(123)=Z_1(0123)=-10,
 Z_2(023)=21h/2-7/2, Z_3(023)=21h/2-11/2,
 Z_0(023)=4+2h.

These coordinates do not occur in the pair-only tail's actual outcomes.
The negative participant triples only lower its quiet forced-Quit offers,
so the tail is unchanged. Prepend q=(1/2,0,1/2,1/2). Its exact END vector is

 ((2+6h)/4, (4-12h)/8, (1+21h/2)/4, (1+21h/2)/4).

All entries are positive for small h. Observers2,3 have Q=END, observer1
has Q=-51/8<END, and pivot0 has Q=END-h. The complete prefixed profile is
therefore actual, ALL-END, observer-optimal, has positive Never and positive
initial caps, and has no finite pivot cap attainer. Its tail pivot debt is
O(h^2), by summing q_p(END-Q_p)=O(h^2 rho^(2n)). The prefix debt is
h/2+O(h^2), and joint Never is at most1/8. For r=1/4 and small h,

 d_p+r nu<r, N_p<=1/2<3/4=1/(1+rS).

Global minimality and a positive absorbing gap are NOT claimed. Here the three coefficients are
C_1(r)=(8r+3)/9, C_2(r)=(41r+21)/45, and C_3(r)=5(7r+3)/39.
They are positive for every r>=0. The present theorem proves that the
profile cannot be a global minimum at any such penalty. This one
construction has bounded runs; the proof, not the construction, handles
unbounded runs.

## Source correspondence and downstream use

The complete-law payoff and unrestricted response cap are
`quittingStoppingLawExpectedPayoff` and
`quittingStoppingLawReplacementPayoffCap` in
[StoppingLawOperationalDistance.lean](../../UniformEquilibrium/Quitting/Paths/StoppingLawOperationalDistance.lean).
The declarations
`quittingStoppingLawExpectedPayoff_behaviorStoppingLaws_eq_terminalPayoff`
and
`quittingStoppingLawCap_behaviorStoppingLaws_eq_continuationBestResponseValue`
identify them with arbitrary behavioral payoff and cap. Conversely,
`quittingTerminalPayoff_stoppingLawProfile_eq_expectedPayoff` and
`quittingStoppingLawCap_eq_continuationBestResponseValue_stoppingLawProfile`
give these identities for independent conditional-hazard implementations.

The literal prefix identity is
`quittingTerminalSemanticPair_rootThenContinuation` in
[TerminalSemanticPair.lean](../../UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean).
The full-cap recursion is
`quittingContinuationBestResponseValue_rootThenContinuation_eq_max` in
[TerminalDebtPrefix.lean](../../UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean).
Their statements give the semantic meaning of (Root), rather than a
formalization of the new run charts, timing derivative or second variation.

The declaration
`not_exists_uniformEquilibriumPayoff_iff_hasPositiveMinimumTerminalSemanticDebt`
in [PositiveMinimumSemanticDebt.lean](../../UniformEquilibrium/Quitting/Terminal/PositiveMinimumSemanticDebt.lean)
concerns a positive minimum of total debt on a compact semantic carrier.
It does not produce an actual observer-constrained minimum or this support
mode. A compact endpoint cannot replace the actual law in the summability,
conditional-tail and finite-splice arguments.

When a counterexample reduction supplies a positive absorbing threshold m,
choose an admissible 0<r<m and select the source afresh. If (Raw) holds and
some C_i(r)>0, the selected source cannot have arbitrarily late guarded
i-controlling patches. In particular the recurrent guarded pair-star tail
is impossible. Some A_i>0 permits choosing
r small enough BEFORE source selection. The present theorem produces neither
m nor actual attainment. Its new content is the complete raw/penalty
necessary condition (Conclusion) and the stronger finite-patch restriction
(Patch), with every improving comparison constructed.

An all-four-owner controlled-window argument cannot supply this conclusion:
its variations require every hazard positive and all observer contacts at
every date. Here quiet hazards stay zero and only supported observer contacts
are imposed. The rational boundary above also shows that restricting the
present method to five physical dates misses some recurrent calendars.
No claim is made that every table in (Raw) lies outside every UE existence
criterion; the conclusion concerns actual minimizing source configurations.

## Lean handoff and scope

Use the existing complete-law, payoff, full-cap and literal-prefix definitions.
Formalize the exact run outcome/cap maps and reduced four-run Jacobian first.
Prove their compact-parameter inverse bounds and the finite actual-law splice.
The projective conjugacy then gives a finite-composition C2 estimate by
Duhamel, the chain rule and summability of observer masses. This estimate
must control arbitrary subproducts; an individual matrix bound is insufficient.

Formalize the normalized timing derivative, the two-dimensional bridge
coefficients, the three explicit controls, and the absolute-atom quadratic
identities. Transfer the Hessian to hazards only after proving that the
augmented objective has zero first derivative. The final implicit system has
four cap variables and two entrance payoff/Never variables; its block
triangular inverse and finite feasibility produce the comparison strategy.
Do not package the desired improving curve or correction oracle as an
assumed structure field.

This is ordinary mathematics awaiting formalization. It proves neither an
actual-source selection theorem, an unrestricted UE reward-table class,
nor the full four-player conjecture. Quiet ties inside every candidate patch, mixed-support bridges, other
sign modes, all-nonpositive coefficients, and nonrealized sources remain open.

## Complete exact checks

Save the following Python3 program and run it with SymPy installed. It
constructs all matrices and finite-outcome expressions directly from the
included rational data. It checks the positive five-date curvatures, the
negative three-occurrence coefficient for symbolic r, and the actual guarded
construction with its positive-cap prefix. No numerical eigenvalues, stored
matrix payload, or external conference input is used.

```python
"""Exact first-outcome checks; no numeric eigensolver or generated matrix payload."""
import sympy as s
from itertools import combinations
G=s.Matrix([[0,s.Rational(2,7),s.Rational(1,2),s.Rational(3,14)],
 [-1,0,s.Rational(1,2),s.Rational(1,2)],
 [1,-s.Rational(4,5),0,-s.Rational(1,5)],
 [1,-s.Rational(1,5),-s.Rational(4,5),0]])
J=s.zeros(4);J[0,1]=-s.Rational(10,21);J[0,2]=-s.Rational(5,6);J[0,3]=-s.Rational(1,2)
J[1,0]=-s.Rational(11,3);J[2,0]=5;J[3,0]=6
lam={i:1-G[i,0]/J[i,0] for i in (1,2,3)};r=s.symbols('r')
w=G.inv().T*s.ones(4,1)
C={i:s.factor(G[0,i]*lam[i]+J[0,i]*(1-lam[i])-r*sum(w[j]*(-G[j,0]+lam[i]*G[j,i]) for j in (1,2,3) if j!=i)) for i in (1,2,3)}
assert G.inv()[:,0]==s.ones(4,1)
assert G.det()==s.Rational(17,50) and all(C[i].subs(r,0)>0 for i in (1,2,3))
expected_C={1:3*(577*r+34)/1309,2:(7026*r+833)/3570,3:-(361*r-68)/714}
assert all(s.simplify(C[i]-expected_C[i])==0 for i in (1,2,3))
def atoms(word,u):
 x=s.zeros(4,1);a=[]
 for k,i in enumerate(word):
  z=s.zeros(4,1);z[0]=(1-lam[i])*(G*x)[i]/G[i,0];z[i]=u[k]
  a.append(z);x=x-z
 return a,x

def coeff(a):
 slots=[(k,i,v) for k,ak in enumerate(a) for i,v in enumerate(ak) if v!=0]
 def second(who,never):
  out=0
  for (k,i,ai),(l,j,aj) in combinations(slots,2):
   if i==j or never and who in (i,j):continue
   if k<l:pay=G[who,i]
   elif l<k:pay=G[who,j]
   elif who==i:pay=J[i,j]
   elif who==j:pay=J[j,i]
   else:pay=0
   out+=ai*aj*(pay-G[who,i]-G[who,j])
  return s.factor(out)
 P=s.Matrix([second(i,True) for i in range(4)])
 return s.factor(P[0]-second(0,False)+r*(w.T*P)[0])
five_values={(1,3,2,1,3):s.Rational(44,819),
             (3,2,1,3,2):s.Rational(182,12225),
             (2,1,3,2,1):s.Rational(4727,71148)}
for word in five_values:
 us=s.Matrix(s.symbols('u0:5'));a,x=atoms(word,us);end=x.jacobian(us)
 z=s.Matrix([1,*(-end[:,1:].inv()*end[:,0])]);Q=coeff([v.subs(dict(zip(us,z))) for v in a])
 assert Q.subs(r,0)==five_values[word] and five_values[word]>0
 print('five-word',''.join(map(str,word)),s.factor(Q.subs(r,0)))
# Three occurrences of i=1, separated by arbitrary non-i runs (all length1 here).
i=1;bridge=(3,2);a2=s.prod(lam[j] for j in bridge)
xp=s.Integer(0)
for j in bridge:xp=lam[j]*xp-(1-lam[j])*(-G[j,i]/G[j,0])
b1=b2=-xp
ratio=s.factor(a2*lam[i]*b1/b2)
word=(1,3,2,1,3,2,1,2,3,1,2)
u=[1,0,0,-1-ratio,0,0,ratio,0,0,0,0]
aa,end=atoms(word,u)
assert end==s.zeros(4,1)
E=sum(ak[0]*ak[i] for ak in aa)
assert E==(1-lam[i])*b1*(1+ratio)
Q=coeff(aa);expected=-C[i]*b1*(1+ratio)
assert s.factor(Q-expected)==0
assert E==s.Rational(686,9075) and b1==s.Rational(14,75)
assert s.factor(Q+98*(577*r+34)/154275)==0
print('Gamma determinant',G.det(),'C',C)
print('three-occurrence loop',Q,'E=',E,'b=',b1,'u2=',-1-ratio,'u3=',ratio)
print('PASS: positive five-word cycle, negative three-occurrence coefficient, independent outcome identity.')

# One previously defined actual guarded profile, using its complete native table.
G=s.Matrix([[0,1,1,1],[-2,0,1,1],[2,-1,0,-1],[2,-1,-1,0]])
J=s.Matrix([[0,-1,-1,-1],[-6,0,-3,-2],[s.Rational(15,2),-5,0,-3],[s.Rational(13,2),-3,0,0]])
w=G.inv().T*s.ones(4,1)
assert G.det()==6 and G.inv()[:,0]==s.ones(4,1)/3
lam={i:1-G[i,0]/J[i,0] for i in (1,2,3)}
C={i:s.factor(G[0,i]*lam[i]+J[0,i]*(1-lam[i])-r*sum(w[j]*(-G[j,0]+lam[i]*G[j,i]) for j in (1,2,3) if j!=i)) for i in (1,2,3)}
expected_C={1:(8*r+3)/9,2:(41*r+21)/45,3:5*(7*r+3)/39}
assert all(s.simplify(C[i]-expected_C[i])==0 for i in (1,2,3))
# One actual construction: contact Jacobian and all leading gaps.
rho=s.Rational(1,3); E=s.Matrix([6,-12,s.Rational(21,2),s.Rational(21,2)])
word=(1,2,3,1); aa=[s.Matrix(a) for a in ((2,1,0,0),(1,0,1,0),(1,0,0,1),(1,1,0,0))]
assert G*sum(aa,s.zeros(4,1))==(1-rho)*E
v=s.Matrix(s.symbols('v0:8')); av=[]
for k,i in enumerate(word):
    a=s.zeros(4,1); a[0]=v[2*k]; a[i]=v[2*k+1]; av.append(a)
Ev=[rho*E+G*sum(av[k:],s.zeros(4,1)) for k in range(4)]
F=s.Matrix([*Ev[0],*[(J*av[k])[i]-Ev[k][i] for k,i in enumerate(word)]])
assert F.jacobian(v).det()==1728
expected=[(-7,0,-s.Rational(1,2),-s.Rational(1,2)),(-6,-1,0,-1),(-5,-1,-1,0),(-4,0,-2,-1)]
for k in range(4):
    assert J*aa[k]-(rho*E+G*sum(aa[k:],s.zeros(4,1)))==s.Matrix(expected[k])
# Prefix checks with the same game and the specified added coordinates.
h=s.symbols('h'); q=[s.Rational(1,2),0,s.Rational(1,2),s.Rational(1,2)]
extra={(1,(2,3)):2,(1,(0,2,3)):2,(2,(0,2,3)):21*h/2-s.Rational(7,2),
       (3,(0,2,3)):21*h/2-s.Rational(11,2),(0,(0,2,3)):4+2*h}
for D in ((0,1,2),(0,1,3),(1,2,3),(0,1,2,3)): extra[1,D]=-10
def reward(i,D):
    D=tuple(sorted(D))
    if (i,D) in extra: return extra[i,D]
    if len(D)==1: return G[i,D[0]]
    if len(D)==2 and i in D: return J[i,next(j for j in D if j!=i)]
    return 0
caps=[]; quits=[]
for i in range(4):
    opp=[j for j in range(4) if j!=i]; P=Q=0
    for mask in range(8):
        D=[opp[k] for k in range(3) if mask>>k&1]
        prob=s.prod(q[j] if j in D else 1-q[j] for j in opp)
        Q+=prob*reward(i,D+[i])
        if D: P+=prob*reward(i,D)
    caps.append(s.factor(P+s.prod(1-q[j] for j in opp)*h*E[i])); quits.append(s.factor(Q))
assert (s.Matrix(caps)-s.Matrix([(2+6*h)/4,(4-12*h)/8,(1+21*h/2)/4,(1+21*h/2)/4])).applyfunc(s.simplify)==s.zeros(4,1)
assert s.simplify(quits[0]-caps[0]+h)==0 and quits[1]==-s.Rational(51,8)
assert s.simplify(quits[2]-caps[2])==0 and s.simplify(quits[3]-caps[3])==0
print('PASS: actual guarded fixture, contact data, coefficient signs and positive-cap prefix.')
```
