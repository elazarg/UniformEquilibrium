# Global context rigidity excludes the generic guarded pair-star mode

## Exact raw hypotheses and conclusions

There are four native quitting players I={0,1,2,3}. Each nonempty coalition
S has finite reward Z_i(S), own singleton Z_i({i})=0, and AllNever pays0.
Players independently privately choose complete laws on natural dates and
Never. U_i is prescribed payoff; B_i is the supremum over EVERY unilateral
behavioral replacement; e_i is the pure-Never payoff; N_i is the ORIGINAL
marginal Never mass; d_i=B_i-U_i; and nu=product_i N_i. ALL-END means B=e.
Fix a pivot p; the other three players are observers. Write

 Gamma_ij=Z_i({j}), J_ij=Z_i({i,j}) for i!=j,
 Gamma_ii=J_ii=0, G_i=Gamma_ip, h_i=Gamma_pi.

Assume the explicit raw conditions

 Gamma invertible; G_i!=0; rho_i=J_ip/G_i>1;
 c_ij=-Gamma_ij/G_i>0 for distinct observers i,j, c_ii=0;
 h_i>0>J_pi for each observer i.                          (Raw)

Put lambda_i=1-1/rho_i, w^T=1^T Gamma^-1, and

 A_i=h_i lambda_i+J_pi(1-lambda_i),
 K_j^(i)=-Gamma_jp+lambda_i Gamma_ji+(1-lambda_i)Z_j({p,i})
          for j outside{p,i}, K_p^(i)=K_i^(i)=0,
 C_i(r)=A_i-r w^T K^(i), kappa(r)=1+r w_p.                 (Coeff)

All rewards not queried here remain arbitrary finite. No positive inverse
column is required for the theorem.

For each of the two cyclic orientations of the three observers define the
following explicit price matrix. Temporarily label the observers1,2,3 and
consider 1->2->3->1. With D=1-lambda1 lambda2 lambda3>0, put

 pi^1=[lambda3 lambda2(1-lambda1),
        lambda3(1-lambda2),1-lambda3]/D,
 pi^2=[1-lambda1,lambda1 lambda3(1-lambda2),
        lambda1(1-lambda3)]/D,
 pi^3=[lambda2(1-lambda1),1-lambda2,
        lambda1 lambda2(1-lambda3)]/D,
 v^i=sum_j pi_j^i c_j,
 S_ij(r)=C_i(r)(c_ij-v_j^i)+kappa(r)h_j c_ji.             (PriceMatrix)

Here c_j denotes row j of the three-by-three c matrix. Exchanging labels2,3
gives the other orientation. The same formula includes the diagonal entries.
Thus symmetry is three explicit rational equalities, directly testable from
rewards and the fixed penalty.

Fix any finite r>=0. Suppose an ACTUAL profile P has positive original
Never mass for every player, is ALL-END and observer-optimal, and globally
minimizes d_p+r nu among all actual observer-optimal profiles, or on a larger
feasible carrier containing them. Suppose that, after deleting empty dates,
its tail eventually consists of pair dates p,i; all three observer labels
recur; and every inactive observer comparison is eventually strict.

**Fixed-penalty global reduction.** If all C_i(r)!=0, the eventual observer
word is a directed three-cycle, and the matrix (PriceMatrix) for that
orientation is symmetric. Periodicity is a conclusion, not a supplied
calendar hypothesis. No bound on recurrence gaps or original run lengths
is assumed.

**Complete structured coefficient restriction.** If, more specifically,
there are c0,b_i>0 with c_ij=b_j/2 and h_i=c0 b_i, then every such minimum
satisfies C_i(r)=0 for ALL observers. This includes zero-coefficient labels
with arbitrarily long runs; the penalty is fixed before seeing the source.

**Generic Raw exclusion.** Impose the following additional explicit test:

 every A_i!=0; neither orientation's S(0) is symmetric.    (Generic)

There is r0>0, determined by the table before source selection, such that
for every 0<r<r0 the entire stated recurrent guarded Raw mode is impossible.
Condition (Generic) is an open dense condition in the24 singleton and
participant-pair coordinates on Raw. The other32 native rewards are free.
A supplied positive absorbing exploitability gap survives an arbitrarily
small perturbation into (Generic), with all source objects selected afresh.

## Importance and exact scope

The theorem replaces a finite-word search by a global restriction on the
entire recurrent calendar. Arbitrarily sparse occurrences of each label
can be used as controls. Their limiting pivot memories either produce a
negative finite closed variation, or force a unique context for each label;
that rigidity forces a directed three-cycle and explicit price equalities.
The structured result removes the entire nonzero coefficient vector, rather
than only positive timing coefficients.

Actual observer-constrained attainment, ALL-END, positive original Never,
the pivot/raw chamber, eventual pair support, recurrence and quiet guards
remain inputs. The theorem does not produce them from every game. It is a
conditional restriction on actual minimizing sources, not a new unrestricted
UE reward-table class or a solution of Fin4. Mixed-support bridges, quiet
ties, other sign chambers and nonrealized compact sources remain open.

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

Controlling windows occur
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

If C_i(r)!=0, every sufficiently late i-run has length one. To prove this,
take any sufficiently late run of length L>=2,
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

Choose a later controlling four-run window. Keep the OBSERVER masses,
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

## Full fixed-r quadratic objective

All atoms in this section are GLOBAL ABSOLUTE first-Quit atoms from the
entrance of the complete modified finite window, rather than conditional
hazards or run-local atoms. The exact coordinate change is

 alpha_i,t=q_i,t product_(s<t)(1-q_i,s),
 q_i,t=alpha_i,t/[1-sum_(s<t)alpha_i,s].

It is analytic near zero with identity first derivative. At the zero-tail
reference the continuation Never vector is1, so joint Never is exactly
product_i(1-sum_t alpha_i,t). If all total marginal atom tangents vanish,
its quadratic coefficient is zero IN THESE ABSOLUTE COORDINATES. The
augmented-objective argument below transfers the Hessian to hazards.
Let a_p(t),u_i(t) be the absolute atom tangents.
Assume every total tangent is zero, at most one observer is supported per
date, and all active observer contacts hold to first order. Define

 E_i=sum_t a_p(t)u_i(t),
 T_ab=sum_(s<t) a_a(s)a_b(t), with a_i=u_i for observers.

Then T_ij+T_ji=0 for distinct observers, while T_pi+T_ip=-E_i.
Observer quadratic debt is zero and equals

 0=D_i=G_i T_ip+sum_(j!=i) Gamma_ij T_ij-(J_ip-G_i)E_i.

Consequently the pivot quadratic debt is exactly

 D_p=-sum_i rho_i A_i E_i-sum_(i!=j)h_i c_ij T_ij.

Let P_2 be the vector of quadratic Never-payoff terms. Expanding each
independent first coalition and using w^T Gamma=1^T gives

 w^T P_2=w_p D_p+sum_i [w^T Z({p,i})-1]E_i.

Indeed an ordered pair a before b contributes
-(1-w_a Gamma_ab)T_ab to the weighted Never sum; a simultaneous pair p,i
contributes
[sum_(j outside{p,i})w_j Z_j(pi)-2+w_i G_i+w_p h_i]E_i.
Substitute T_ip=-T_pi-E_i and the three observer debt identities. Also

 w^T Z(pi)-1-w_p rho_i A_i=rho_i w^T K^(i).

Therefore the full constrained objective coefficient, at the FIXED penalty,
is

 Q_r=-sum_i rho_i C_i(r)E_i
           -kappa sum_(i!=j)h_i c_ij T_ij.                (Q)

The first derivative of -u_p+r nu at zero is
-(Gamma_p+r1^T)sum da. The fixed-cap constraint combination E_p+r w^T E
cancels it. Thus the augmented objective -u_p+r nu+E_p+r w^T E has zero
ambient differential at zero data. Hence this absolute-atom coefficient is the same Hessian
coefficient on the exact cap-solving hazard curve, including second-order
correcting controls. There is no choice of r after observing a calendar.

## Pivot memory and arbitrarily sparse controls

The preceding timing lemma makes every sufficiently late run a singleton when all
C_i(r)!=0. Write x=Gamma^-1 E and observer vector y=(x_1,x_2,x_3), with labels
understood relative to the pivot. At a label i the linearized run dynamics are

 a_p=(x_p-c_i dot y)/rho_i,
 x_p^+=lambda_i x_p+(1-lambda_i)c_i dot y,
 y^+=y-u e_i.

Fix one initial pi in the probability simplex Delta3 at the beginning of
the eventual run word, and carry its memory through that whole word by

 pi^+=lambda_i pi+(1-lambda_i)e_i,
 v=sum_j pi_j c_j,  z=x_p-v dot y.

At the beginning of any later comparison window x_p=y=0, hence z=0
regardless of that window's inherited pi. Its context sequence is therefore
the same fixed sequence for all later comparisons. Exactly,

 z^+=lambda_i z+lambda_i v_i u.                            (Memory)

Here c_i has own coordinate zero. The rows c_i are uniformly bounded, and
lambda_max<1. Thus if every |u|<=epsilon and z starts at zero,

 |z|<=K epsilon

uniformly over the entire chosen window, including arbitrarily many dates
with u=0. The observer state y follows the prescribed coordinate controls
exactly. Its total variation V=sum |u| bounds its size.

Since T_ji=-sum_t y_j(t)u_i(t), formula (Q) has per-control price

 F_(i,v)(y)=-C_i(r)(v-c_i) dot y
                  +kappa sum_(j!=i)h_j c_ji y_j.          (Price)

The difference between the actual zero-data quadratic cost and sum F u is
at most K epsilon V, by (Memory). A finite coordinate path with a bounded
number of pieces can be traversed with mesh epsilon, at arbitrary selected
occurrences of each required label. All other controls are zero.

For each label i let Omega_i be the nonempty compact set of accumulation
points of pi immediately before its occurrences. Every neighborhood of a
chosen point in Omega_i is visited infinitely often. Hence any finite ordered
list of desired label/context pairs can be realized arbitrarily late, with
arbitrarily long waits if needed. Choosing contexts within delta of their
specified limits changes the work by at most K delta V sup|y|. Neither
control order nor context selection requires consecutive occurrences.

After a closed observer path, y=0 and x_p=z=O(epsilon). Append a later
controlling four-run window, with intervening controls zero. Its uniform
linear inverse corrects the complete endpoint state using O(epsilon)
controls. Its quadratic cost is O(epsilon^2). Thus every strictly negative
limiting coordinate-path work gives an exact finite closed tangent loop of
strictly negative Q_r.

## No negative loop forces unique contexts and a symmetric price

Suppose no negative closed tangent loop can be found arbitrarily late.
For any label i with C_i(r)!=0, all elements of Omega_i must coincide.
Otherwise two contexts pi,pi' give distinct v,v': the matrix c has zero
diagonal and positive off-diagonal entries, so

 det c=c12 c23 c31+c13 c21 c32>0.

Their price-row difference is the nonzero linear form
-C_i(r)(v-v') dot y. Choose a coordinate-i interval at a suitable fixed
value of the other coordinates where the integral of this difference is
nonzero. Traverse it forward using one context and backward using the
other. Interchanging the contexts reverses the work sign, so one choice
has negative work.

Move from zero to the chosen base point along any fixed coordinate path,
perform the out-and-back excursion, and reverse the setup path using the
same context assigned to each of its reversed segments. The setup and
return line integrals cancel exactly. Either orientation of the excursion
is available arbitrarily late, so one complete assigned path has strictly
negative work. Taking epsilon and delta sufficiently small and applying
the preceding construction gives a negative exact closed tangent loop, a contradiction.
This proves uniqueness. Equivalently, reversibility of every assigned
polygon forces every closed assigned-path line integral to vanish.

Write the unique context pi^i and v^i=sum_j pi_j^i c_j. The resulting linear
price matrix has rows

 S_ij=C_i(r)(c_ij-v_j^i)+kappa h_j c_ji,  i!=j,
 S_ii=-C_i(r)v_i^i.                                      (S)

A coordinate rectangle in directions i,j has line-integral work equal,
up to orientation, to its area times S_ij-S_ji. Both orientations are
realizable by the context-selection argument. Therefore S must be symmetric.
This conclusion uses actual feasible finite directions, not an assumed
storage function or correction oracle.

## Context uniqueness forces eventual periodicity

Let G_inf be the directed graph of label transitions occurring infinitely
often. Adjacent maximal run labels differ. After a finite index every
transition belongs to G_inf. Since all three labels recur, this graph is
strongly connected.

On every edge i->j the memory recurrence and uniqueness give

 pi^j=lambda_i pi^i+(1-lambda_i)e_i.                      (Transition)

Suppose some i has two successors j,k. Then pi^j=pi^k=v and
v_i>=1-lambda_i>0. An edge j->k would imply
v=lambda_j v+(1-lambda_j)e_j, or v=e_j, impossible because v_i>0.
Likewise k->j is impossible. Strong connectivity therefore forces both
j->i and k->i. Their equations give

 lambda_j v+(1-lambda_j)e_j
       =lambda_k v+(1-lambda_k)e_k.

Coordinate i implies lambda_j=lambda_k; then the unequal point-mass
injections contradict equality. Thus every vertex has one successor.
Strong connectivity on three vertices forces one directed three-cycle.
After the last exceptional transition, the actual word is that periodic
cycle. This proves the stated general Raw reduction.

Solving (Transition) on the resulting cycle gives precisely the contexts
in (PriceMatrix). The necessary conservative conditions are its three
symmetry equalities, not an unspecified variational hypothesis.

## Transfer to an actual global minimum

The negative reference loop above can be realized arbitrarily late in the
SAME infinite actual word. Fix its finite observer-coordinate path,
control mesh, context tolerance, and strictly negative
work margin first. Only the waiting calendar distances then vary. These
choices depend on that word but not on the later cut.

The number of selected controls is finite and fixed. All intervening
uncontrolled bridges satisfy the uniform C2 estimate proved above, independent
of their lengths. The endpoint-correcting four-run inverse is uniform.
For completeness, impose six endpoint equations: the four reduced caps,
pivot payoff and joint Never. Solve for the four correcting masses and
the two entrance values u_p,nu. Their derivative is block triangular:
the reduced cap block has its proved uniform inverse, and the payoff/Never
blocks are reciprocal head survivals, tending uniformly to1. Differentiating
these finite implicit equations twice gives uniform convergence of their
solution two-jets. Consequently the exact cap-preserving comparison curves have
second derivatives converging uniformly to 2Q_r as the cut tends to infinity.
No penalty is chosen at this stage: formula (Q) already contains the fixed r.

Every selected actual window is finite. Positive supported atoms and strict
quiet/pivot comparisons provide a two-sided feasible interval, while exact
active contacts, fixed entrance caps, and unchanged literal continuation
preserve ALL-END and observer optimality. Earlier ties are preserved.
A strictly negative second derivative contradicts global minimality.
Thus an actual minimum must satisfy the periodic/conservative conclusion.

## Structured consequence, including zero coefficients

Suppose c_ij=b_j/2 and Gamma_pi=c b_i with c,b_i>0. Put y_i=b_i x_i and
U_i=b_i u_i. The observer area term in (Q) cancels because
Gamma_pi c_ij=c b_i b_j/2 is symmetric in i,j. The cost is

 Q_r=sum_i d_i sum_t a_p(t)U_i(t),
 d_i=-rho_i C_i(r)/b_i.

In these coordinates c_i has zero own coordinate and all other coordinates
1/2. Price rows are k_i(e_i-pi^i), with k_i=d_i/(2rho_i).
If all costs are nonzero, symmetry on the eventual cycle gives

 k1 lambda3(1-lambda2)=k2(1-lambda1),
 k2 lambda1(1-lambda3)=k3(1-lambda2),
 k3 lambda2(1-lambda1)=k1(1-lambda3).

Multiplying forces lambda1 lambda2 lambda3=1, impossible. Thus there is
negative curvature whenever all C_i(r) are nonzero.

If some but not all costs vanish, collapse maximal runs. Timing makes the
nonzero-cost runs singleton; a zero-cost run may have any finite length,
with theta<=lambda_max. Its exact memory update is
pi^+=theta pi+(1-theta)e_i and
z^+=theta z+[theta(1-pi_i)/2]U. Its stage cost is zero. The same tracking,
context-selection, and conservative-price proof applies. Nonzero-cost
labels have unique contexts; zero-cost price rows are zero. Symmetry forces
pi_j^i=0 whenever i has nonzero cost and j has zero cost.

The recurrent transition graph is strongly connected. It has an infinitely
recurring edge from some zero-cost label j to a nonzero-cost label i. That
edge injects at least 1-lambda_max into coordinate j of the next memory,
contradicting pi_j^i=0. Therefore a recurrent guarded structured minimum
must have C_i(r)=0 for ALL three observers, exactly at the fixed penalty.

## Generic Raw selection before the penalty and source

At r=0, every A_i and every antisymmetric entry of either orientation's
matrix S is a rational function of the24 singleton/participant-pair reward
coordinates. Its denominators are nonzero on Raw. Clear these denominators.
The product of the three A_i numerators and, for each orientation, the sum
of squares of its three antisymmetry numerators is a polynomial P.

P is not identically zero: the structured table
Gamma=[0,1,1,1;-2,0,1,1;2,-1,0,-1;2,-1,-1,0],
rho=(2,3,4), J_pi=(-2,-3,-4) has A_i=-1/rho_i, and the structured consequence rules out
symmetry for either orientation. Hence P!=0 is dense in every open Raw
region, including one with a strictly positive inverse pivot column.
If the fresh source may select the pivot, take the product of this polynomial
under the four pivot relabelings. Each factor is nonzero by relabeling the
same witness, so their product is nonzero. This is one generic perturbation
before any new pivot or source is selected.

For a fixed perturbed table with P!=0, C_i(r) and both antisymmetry vectors
are affine in r, and their values at r=0 are nonzero. Choose r0>0 so that
these finitely many strict nonvanishing conditions hold for every 0<r<r0.
This choice is made BEFORE selecting a new source. At every such r, the
entire recurrent guarded Raw mode is impossible by the preceding proof.
When the pivot will be selected afresh, take the minimum of these thresholds
for the finitely many pivots satisfying Raw at the fixed new table. The
penalty bound is then chosen uniformly before that selection as well.

For completeness, define the native absorbing gap

 g(Z)=inf_(P absorbs almost surely) max_i [B_i^Z(P)-U_i^Z(P)],

with actual prescribed profiles and full behavioral caps. The class of
absorbing prescribed profiles is reward-independent. If ||Z-Z'||<=delta,
every prescribed or deviated payoff changes by at most delta; taking
suprema changes every cap by at most delta. Taking maxima and infima gives

 |g(Z)-g(Z')|<=2delta.

Thus any supplied g(Z)>0 survives a raw24-coordinate perturbation of norm
less than g(Z)/4 into (Generic), also preserving any required open Raw or
strict inverse-column conditions. Other rewards and own singletons stay
fixed. Fix this new table first, choose 0<r<r0 and any further source-required
upper bound, and only then select all source objects afresh. No old law or
minimum is transported across the perturbation.

The checked signed Fin4 normalization supplies, from any hypothetical
original counterexample, a table R with own singleton vector e_m, zero
AllNever, and no UE payoff. The checked terminal-gap equivalence then gives
delta>0 with total debt at least delta against every actual profile. Set
Z_i(S)=R_i(S)-1_(i=m) on every nonempty coalition, retaining zero AllNever.
For R and Z the own singletons are nonnegative. A deterministic deadline
tending to infinity has payoff tending to the Never payoff plus the own
singleton times opponents' joint Never mass, by bounded convergence.
Hence the supremum over finite deadlines already dominates Never.
Every finite-deadline pivot response absorbs and loses exactly1 under this
translation, so B_m^Z=B_m^R-1. Prescribed payoff loses1-nu, yielding

 d_m^Z=d_m^R-nu, d_j^Z=d_j^R for j!=m.

All debts therefore agree on absorbing prescribed profiles, so g(Z)>=delta/4.
This native table is not asserted to lack UE: AllNever is exact Nash.
The obstruction preserved is only its positive absorbing gap. The adapter
does not force Raw, actual attainment, the guarded support, or recurrence.
Those remain separate source inputs.

## One actual guarded construction

The assumed support and strict comparisons are realizable; local contact
feasibility alone does not give the exclusion. Take p=0 and

 Gamma=[0,1,1,1; -2,0,1,1; 2,-1,0,-1; 2,-1,-1,0],
 J=[0,-3,-15/4,-13/4; -6,0,-3,-2; 15/2,-5,0,-3; 13/2,-3,0,0],

with other rewards zero. The Raw inequalities hold, det Gamma=6 and
Gamma^-1 e_p=(1/3,1/3,1/3,1/3). Take contraction eta=1/3,
E=(6,-12,21/2,21/2), observer word1,2,3,1, and leading hazards

 a_0=(2,1,0,0), a_1=(1,0,1,0),
 a_2=(1,0,0,1), a_3=(1,1,0,0).

Then Gamma sum a=(1-eta)E. The8-by8 Jacobian imposing four entrance caps
and four active-observer contacts has determinant1728, with columns ordered
by date and owner, entrance rows first. The leading Quit-minus-END vectors are

 (-9,0,-1/2,-1/2), (-35/4,-1,0,-1),
 (-29/4,-1,-1,0), (-6,0,-2,-1).

The finite inverse theorem gives an exact four-date block q(t)=t a+O(t^2)
with entrance caps tE, terminal caps eta tE, exact active-observer contacts
and strict quiet/pivot comparisons. Concatenate q(h eta^n) for sufficiently
small h>0. Hazards are proper and summable, so every original Never mass
is positive. Assigned caps match and tend to zero; telescoping (Root)
identifies them with the actual law's Never offers. Every deadline is at
most END and every supported observer response is tied, including Never.
Thus the resulting actual profile is ALL-END and observer-optimal, with all
three labels recurring and strict quiet/pivot comparisons. Its negative
conditional observer cap is allowed by the native model.

The coefficients are
C_1(r)=(8r-3)/9, C_2(r)=(41r-12)/45, C_3(r)=(35r-12)/39.
All are negative for 0<=r<12/41, and they never vanish simultaneously.
The structured consequence proves that this actual guarded profile cannot
be a global minimum at any r>=0. In particular its small-penalty region is
excluded without any positive timing coefficient.
No positive absorbing gap, global minimum or counterexample is claimed for
this construction. It is used solely to verify nonvacuity of the support
and response hypotheses.

## Source correspondence and Lean handoff

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

The counterexample normalization just used is
`nonempty_finFourSinglePivotNormalization_of_no_uniformPayoff` in
[FinFourSinglePivotNormalization.lean](../../UniformEquilibrium/Diagnostics/Quitting/FinFourSinglePivotNormalization.lean).
The terminal-gap equivalence is
`not_exists_uniformEquilibriumPayoff_iff_exists_terminalExploitabilityGap` in
[ExploitabilityGap.lean](../../UniformEquilibrium/Quitting/Terminal/ExploitabilityGap.lean).
These exact statements provide the signed-to-native source adapter; they
do not formalize the new contact, memory, or conservative-price argument.

For formalization, retain the existing complete-law and full-cap semantics.
First formalize the exact run maps, compact reduced four-run inverse, and
finite actual-law splice. Prove the projective C2 bridge estimate using
bounds on arbitrary matrix subproducts and summable observer masses.
Then formalize the fixed-r quadratic identity, memory tracking bound,
context-sampled polygon construction and exact endpoint correction. The
recurrent graph argument and rational price tests are finite after those
analytic lemmas. Do not assume an improving comparison or a correction
oracle as a strategic structure field.

This is ordinary mathematics awaiting formalization. It supplies neither
actual-source selection nor arbitrary Fin4 closure. Nonrealized sources,
quiet ties, mixed supports and tables outside Raw remain separate cases.

## Complete exact checks

Save the following Python3 program and run it with SymPy. It reconstructs
all matrices and first-outcome terms from the included rational data. It
checks the full fixed-r identity on an asymmetric Raw table with six nonzero
passive pair rewards, both orientation-genericity witnesses, and the actual
guarded construction's contact Jacobian and strict leading inequalities.
The algebraic check table is not claimed to be a minimizing source.
No numerical rank, eigenvalue, or stored matrix payload is used.

```python
"""Independent exact first-outcome check of the fixed-r Raw loop identity."""
import sympy as s
from itertools import combinations
c=s.Matrix([[0,3,s.Rational(1,5)],[5,0,s.Rational(1,2)],[2,3,0]])
h=s.Matrix([5,1,s.Rational(1,2)]); gs=[-1,1,1]
rho={1:s.Rational(3,2),2:s.Rational(4,3),3:s.Rational(2)}
G=s.zeros(4);J=s.zeros(4)
for i in (1,2,3):
 G[0,i]=h[i-1];G[i,0]=gs[i-1];J[i,0]=rho[i]*G[i,0];J[0,i]=-h[i-1]*rho[i]
 for j in (1,2,3):
  if i!=j:G[i,j]=-G[i,0]*c[i-1,j-1]
passive={(j,i):s.Integer(k) for (j,i),k in zip([(2,1),(3,1),(1,2),(3,2),(1,3),(2,3)],[1,-2,3,-4,5,-6])}
w=G.inv().T*s.ones(4,1);r=s.symbols('r');kap=1+r*w[0]
lam={i:1-1/rho[i] for i in (1,2,3)}
A={i:G[0,i]*lam[i]+J[0,i]*(1-lam[i]) for i in (1,2,3)}
K={i:s.Matrix([0 if j in (0,i) else -G[j,0]+lam[i]*G[j,i]+(1-lam[i])*passive[j,i] for j in range(4)]) for i in (1,2,3)}
C={i:A[i]-r*(w.T*K[i])[0] for i in (1,2,3)}
word=(1,2,3,1,2,3,1);u=s.Matrix(s.symbols('u0:7'));x=s.zeros(4,1);atoms=[]
for k,i in enumerate(word):
 ap=s.factor((G*x)[i]/G[i,0]/rho[i]);aa=s.zeros(4,1);aa[0]=ap;aa[i]=u[k];atoms.append(aa);x-=aa
M=x.jacobian(u);B=s.Matrix.hstack(*M.nullspace());v=B*s.Matrix([1,2,-1]);sub=dict(zip(u,v))
atoms=[aa.subs(sub) for aa in atoms]
assert M*v==s.zeros(4,1)
slots=[(k,i,aa[i]) for k,aa in enumerate(atoms) for i in range(4) if aa[i]!=0]
def reward_pair(who,i,j):
 if who==i:return J[i,j]
 if who==j:return J[j,i]
 if 0 in (i,j):return passive[who,j if i==0 else i]
 return 0

def quadratic(who,never):
 out=0
 for (k,i,ai),(l,j,aj) in combinations(slots,2):
  if i==j or (never and who in (i,j)):continue
  pay=G[who,i] if k<l else G[who,j] if l<k else reward_pair(who,i,j)
  out+=ai*aj*(pay-G[who,i]-G[who,j])
 return s.factor(out)
P=s.Matrix([quadratic(i,True) for i in range(4)])
D=s.Matrix([P[i]-quadratic(i,False) for i in range(4)])
assert D[1:4,0]==s.zeros(3,1)
E={i:sum(aa[0]*aa[i] for aa in atoms) for i in (1,2,3)}
def T(i,j):return sum(atoms[k][i]*atoms[l][j] for k in range(len(word)) for l in range(k+1,len(word)))
area=sum(G[0,i]*c[i-1,j-1]*T(i,j) for i in (1,2,3) for j in (1,2,3) if i!=j)
qdirect=s.factor(D[0]+r*(w.T*P)[0])
qformula=s.factor(-sum(rho[i]*C[i]*E[i] for i in (1,2,3))-kap*area)
assert s.factor(qdirect-qformula)==0
L={i:sum(w[j]*reward_pair(j,0,i) for j in range(4))-1 for i in (1,2,3)}
assert s.factor((w.T*P)[0]-w[0]*D[0]-sum(L[i]*E[i] for i in (1,2,3)))==0
assert all(s.factor(L[i]-w[0]*rho[i]*A[i]-rho[i]*(w.T*K[i])[0])==0 for i in (1,2,3))
assert all(z>0 for z in G.inv()[:,0])
print('PASS full fixed-r Raw identity; detGamma=',G.det(),'Q=',qdirect)
print('PASS weighted Never identity and coefficient simplification with six nonzero passive pair rewards.')

# Exact witness that both orientation-conservativity polynomials are nonzero.
c=s.Matrix([[0,s.Rational(1,2),s.Rational(1,2)],[s.Rational(1,2),0,s.Rational(1,2)],[s.Rational(1,2),s.Rational(1,2),0]])
rhos=[s.Integer(2),s.Integer(3),s.Integer(4)];lams=[1-1/z for z in rhos];As=[-1/z for z in rhos]
for order in [(0,1,2),(0,2,1)]:
 # Solve the exact three phase-memory fixed point, then construct all rows.
 p=s.Matrix(s.symbols('p0:3'));pn=p
 for i in order:pn=lams[i]*pn+(1-lams[i])*s.eye(3)[:,i]
 sol=s.solve(list(pn-p),list(p),dict=True)[0];pn=p.subs(sol);S=s.zeros(3)
 for i in order:
  vv=(pn.T*c)
  for j in range(3):S[i,j]=As[i]*(c[i,j]-vv[j])+c[j,i]
  pn=lams[i]*pn+(1-lams[i])*s.eye(3)[:,i]
 skew=S-S.T
 assert skew!=s.zeros(3)
 print('orientation',order,'skew=',skew)
print('PASS nonzero genericity witness in both orientations.')

# Actual guarded construction: coefficients, contact Jacobian, strict leading gaps.
G=s.Matrix([[0,1,1,1],[-2,0,1,1],[2,-1,0,-1],[2,-1,-1,0]])
J=s.Matrix([[0,-3,-s.Rational(15,4),-s.Rational(13,4)],[-6,0,-3,-2],[s.Rational(15,2),-5,0,-3],[s.Rational(13,2),-3,0,0]])
w=G.inv().T*s.ones(4,1)
assert G.det()==6 and G.inv()[:,0]==s.ones(4,1)/3
lam={i:1-G[i,0]/J[i,0] for i in (1,2,3)}
C={i:s.factor(G[0,i]*lam[i]+J[0,i]*(1-lam[i])-r*sum(w[j]*(-G[j,0]+lam[i]*G[j,i]) for j in (1,2,3) if j!=i)) for i in (1,2,3)}
expected_C={1:(8*r-3)/9,2:(41*r-12)/45,3:(35*r-12)/39}
assert all(s.simplify(C[i]-expected_C[i])==0 for i in (1,2,3))
roots=[s.solve(C[i],r)[0] for i in (1,2,3)]
assert all(C[i].subs(r,0)<0 for i in (1,2,3))
assert len(set(roots))==3 and min(roots)==s.Rational(12,41)
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
expected=[(-9,0,-s.Rational(1,2),-s.Rational(1,2)),(-s.Rational(35,4),-1,0,-1),(-s.Rational(29,4),-1,-1,0),(-6,0,-2,-1)]
for k in range(4):
    assert J*aa[k]-(rho*E+G*sum(aa[k:],s.zeros(4,1)))==s.Matrix(expected[k])

print('PASS actual guarded construction, all contact data, and coefficient signs.')
```
