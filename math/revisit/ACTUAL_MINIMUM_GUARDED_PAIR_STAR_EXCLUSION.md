# Actual minima exclude an eventual guarded pair-star mode in an open reward region

**Internal repair target; not an accepted conjecture-facing export.** The
singleton sign chamber in the main exclusion has R0 degree zero and is
already excluded by the implemented singleton-degree criterion. The
calculus below is retained for audit and possible generalization; its
claims of new counterexample coverage are withdrawn. See the
[source-overlap audit](../notes/CODEX_ROOT__PROOF_MECHANISM_DIVERSIFICATION.md#singleton-chamber-overlap-audit).

The separate general-ratio saturation corollary has broader singleton
scope; it is retained as useful mathematics, pending a separate handoff.

This is an ordinary mathematical proof of an actual-source case exclusion.
It does not prove the four-player quitting-game UE conjecture and is not
a Lean-checked theorem.

## Exact statement

There are four players I={0,1,2,3}. A native quitting table assigns a finite
real reward Z_i(S) to every nonempty coalition S, with Z_i({i})=0 and AllNever
payoff0. Players independently choose complete laws on the natural dates and
Never. Let U_i be prescribed expected payoff, B_i the supremum over every
unilateral behavioral replacement, e_i the pure Never payoff, N_i the ORIGINAL
marginal Never mass, d_i=B_i-U_i, and nu=product_i N_i. ALL-END means B=e.
Fix pivot p=0; the other three players are called observers. Write

 Gamma_ij=Z_i({j}), J_ij=Z_i({i,j}) for i!=j, with zero diagonals.

Choose arbitrary c>0, h_1,h_2,h_3>0, G_1,G_2,G_3!=0 and t_1,t_2,t_3>0.

The structured singleton and pivot-pair coordinates are

 Gamma_pi=c h_i, Gamma_ip=G_i,
 Gamma_ij=-G_i h_j/2 for distinct observers i,j,
 J_pi=-c h_i, J_ip=G_i(t_i+2).                                  (1)

Around EACH such structured point there is an open neighborhood U in these
18 coordinates (12 singleton rewards and6 pivot participant-pair rewards)
with the following property. For every fixed finite assignment of the other
38 coordinates (6 observer participant-pair,12 passive pair and20 higher
rewards), there is epsilon>0 such that, for every table with its specified
18 coordinates in U and 0<=r<epsilon,
no actual profile P can simultaneously satisfy:

* every N_i>0, P is ALL-END, and every observer has zero debt;
* P globally minimizes d_p+r nu among all actual observer-optimal profiles,
  or on a larger feasible carrier containing those profiles;
* after deleting all empty dates, eventually each date has exactly p and
  one observer with positive quitting hazards;
* each of the three observer labels occurs infinitely often, and every
  inactive observer has strict Quit-versus-Never inequality at every
  sufficiently late nonempty date.

There is NO hypothesis about pivot cap contacts or a Never-mass inequality.
Run lengths are unrestricted. The neighborhood and epsilon are pointwise in
the structured parameters; no uniform width over this unbounded family is
asserted. The epsilon may depend on the other38 rewards;
there is no bound on their magnitudes. The same statement holds after a
permutation of player names. No actual attainment or positive absorbing gap
is supplied by the theorem.

A general-chamber corollary is also proved below: more generally,
under the ratio conditions(4), positive Gamma^-1 e_p, and absence of ALL
finite pivot cap contacts, an actual minimum in this pair-star mode must
satisfy N_p=1/(1+r sum_i(Gamma^-1 e_p)_i). This includes arbitrarily long runs.

## Complete-law semantics, tails, and empty dates

Before absorption the only public history is the current live date. Sampling
one player's private randomness in advance expresses every behavioral response
as a mixture of deterministic deadlines and Never. Thus B is exactly the
supremum of those pure responses; the proof does not restrict deviations.

For root hazards q define H_i=product_(j!=i)(1-q_j), c=product_i(1-q_i),
and, for S subset I\{i},

 pi_i(S;q)=product_(j in S)q_j product_(j notin S,j!=i)(1-q_j),
 Q_i=sum_S pi_i(S;q) Z_i(S union{i}),
 P_i=sum_(nonempty S) pi_i(S;q) Z_i(S).

With literal continuation values, the exact identities are

 e'_i=P_i+H_i e_i,
 U'_i=q_i Q_i+(1-q_i)P_i+c U_i,
 B'_i=max(Q_i,P_i+H_i B_i), N'_i=(1-q_i)N_i.                     (2)

Positive original Never makes every finite head survival positive. ALL-END
and observer optimality therefore pass to every actual conditional tail:
a better conditional response could be used after that cut. At an active
observer date its Quit offer equals its END cap. Late conditional finite
masses tend to0, so conditional payoffs and Never offers tend to0 and
conditional joint Never tends to1. Moreover

 sum_t q_i(t)<infinity,                                      (3)

because product_t(1-q_i(t))=N_i>0.

Deleting dates with q=0 preserves U,e,N and all retained pure deadline
values. Every deadline in the compressed calendar is an old deadline, so
its cap is at most the old cap; Never still attains that old cap by ALL-END.
Thus B is preserved. The compressed law remains an actual observer-optimal
minimum with the same objective. Infinitely many nonempty dates can again
be indexed by the natural numbers. All subsequent arguments use this
compressed calendar.

## General ratio chamber and exact pair-run laws

For each observer i put G_i=Gamma_ip. The run construction requires

 Gamma invertible, G_i!=0, J_ip/G_i>1,
 Gamma_ij/G_i<0 for distinct observers i,j.                    (4)

Write lambda_i=1-G_i/J_ip in(0,1). Consider a finite maximal run of L dates
whose active owners are p,i. Let E be its entrance Never vector and b its
continuation vector. The pivot's conditional absolute atoms alpha_t within
this run satisfy the active observer's tied pure-deadline equations

 G_i sum_(u<t)alpha_u+J_ip alpha_t=E_i.

Consequently

 alpha_t=(E_i/J_ip)lambda_i^t, t=0,...,L-1.                    (5)

Write the observer atoms beta_t=g w_t, where g=sum beta_t and every w_t>0,
sum w_t=1. Define

 theta=lambda_i^L, m=sum_t w_t lambda_i^t,
 f=sum_t alpha_t=(1-theta)E_i/G_i.                            (6)

The actual profile has E_i/J_ip>0 and 0<f,g<1; E_i itself may be negative.
Fixing the weights w and varying E,g preserves the geometric pivot atoms.
The probabilities a,beta,c_pair of first head coalitions {p},{i},{p,i} are

 c_pair=(E_i/J_ip)g m,
 a=f-(E_i/G_i)g(m-theta),
 beta=g-(E_i/G_i)g(1-lambda_i m),
 a+beta+c_pair=f+g-fg.                                      (7)

The exact forward cap map is

 b_i=theta E_i/(1-f),
 b_p=(E_p-Gamma_pi g)/(1-g),
 b_j=[E_j-Gamma_jp a-Gamma_ji beta-Z_j({p,i})c_pair]
                         /[(1-f)(1-g)]  (j outside{p,i}).     (8)

Its active coordinate follows from E_i=G_i f+(1-f)b_i. Equations(5)--(8)
make every active-observer deadline and its Never response equal to E_i.
The pivot payoff and joint survival propagate by

 u_before=Gamma_pi beta+J_pi c_pair+(1-f)(1-g)u_after,
 nu_before=(1-f)(1-g)nu_after.                              (9)

All these maps are analytic near E=g=0, uniformly over the compact set

 theta in[0,lambda_i], m in[0,1].                           (10)

The endpoint theta=0 is only an analytic limit; no infinite run is performed.
In x=Gamma^-1 E coordinates, the zero-data derivative of(8) is

 x_next=L_i(theta)x-e_i g,
 L_i(theta)=I-[(1-theta)/G_i]e_p Gamma_i.                    (11)

Here e_i means a coordinate vector and Gamma_i a row. Put
z_ij=(Gamma_ij/G_i)(theta_i-1)>0 for distinct observers. Then
L_i e_p=theta_i e_p, L_i e_i=e_i, L_i e_j=e_j+z_ij e_p.
Also L_i v=v for v=Gamma^-1 e_p.

## A uniformly invertible four-run chart

Take run labels i,j,k,i or i,j,k,j, where i,j,k are distinct; call the last
label l. Starting from any nearby entrance vector E_0, the four maps(8)
determine E_1,...,E_4 from four observer masses g_1,...,g_4. Instead of
fixing all four final coordinates directly, impose

 (E_4)_a=(E_4^old)_a for a!=l,
 (E_3)_l=(E_3^old)_l.                                      (12)

For actual theta_l>0 the last equation implies the missing final equality
exactly: the last active map theta_l E_l/[1-(1-theta_l)E_l/G_l] depends only
E_l, not g_4. This replacement avoids a derivative proportional to a tiny
theta_l when the last run is long.

The reduced Jacobian with respect to the four g's is uniformly invertible
at zero data, including all limiting parameters in(10). To prove it, set
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
Every kernel vector is therefore zero. Compactness in(10) supplies a uniform
inverse bound and a uniform finite-dimensional implicit-function chart.

This chart permits arbitrary small entrance-cap changes, or changes in any
run moment with every entrance and final cap fixed. Each actual finite
window has some two-sided feasible neighborhood: its positive atoms and
finitely many strict quiet/pivot comparisons persist. That radius need not
be uniform. The exact contacts and the retained strict comparisons, with
the complete continuation fixed, give full caps and observer optimality by
(2). If every entrance cap is fixed, the entire earlier head is preserved,
including tied pivot deadlines.

Such controlling windows occur arbitrarily late. Adjacent maximal run labels
differ and every run is finite. If there were only finitely many triples of
three distinct labels, the late word would alternate two labels, contrary
to recurrence of all three. Append the next run to any late distinct triple;
it repeats the first or second label and gives precisely the two words above.

## Timing lemma: nonzero coefficients force late run length one

Let w^T=1^T Gamma^-1 and define

 A_i=Gamma_pi lambda_i+J_pi(1-lambda_i),
 K_j=-Gamma_jp+lambda_i Gamma_ji+(1-lambda_i)Z_j({p,i})
                         for j outside{p,i}, K_p=K_i=0,
 C_i(r)=A_i-r w^T K.                                       (13)

In the general chamber(4), suppose an actual minimum has the stated pair-star
tail and all sufficiently late pivot and quiet comparisons are strict. If
C_i(r)!=0, then every sufficiently late i-run has length one. This lemma
allows all earlier pivot cap contacts and arbitrary intervening run lengths.

For a run of length L>=2, move weight between w_0 and w_(L-1), keeping g
fixed. Because both weights are positive, its moment m varies in both
directions. The conversion factor 1-lambda_i^(L-1) is at least1-lambda_i.
Put h=(E_i/G_i)g, which is positive in an actual run. Differentiating(7)
with respect to m gives the EXACT factorization

 (partial_m a,partial_m beta,partial_m c_pair)
                       =h(-1,lambda_i,1-lambda_i).            (14)

The direct head payoff derivative is h A_i; the head Never derivative is
h K; joint survival has derivative0. Thus the forward cap and payoff
impulses are -h K/survival and -h A_i/survival.

Choose any later controlling four-run chart. Keep the OBSERVER masses,
moments and lengths of all intervening runs fixed; their pivot masses change
through their propagated entrance caps. Solve the four correcting masses
with(12) to hold every final cap fixed. Every entrance cap of the whole
modified window stays fixed as well. A finite two-sided feasible interval
exists by the preceding chart and strict inequalities. The remaining issue
is uniformity when the correcting window is arbitrarily far away.

Normalize observer caps z_j=E_j/G_j and choose a reference observer a. Use

 sigma=z_a/(1-z_a),
 tau_j=(z_j-z_a)/(1-z_a), tau_a=0,
 bar_u=u_p/(1-z_a), bar_nu=nu/(1-z_a),                       (15)

together with E_p. At observer mass g=0, the exact run map is

 z_j^+=(z_j-(1-theta_i)z_i)/(1-(1-theta_i)z_i),
 sigma^+=theta_i sigma-(1-theta_i)tau_i,
 tau^+=tau, E_p^+=E_p, bar_u^+=bar_u, bar_nu^+=bar_nu.         (16)

This is exact at arbitrary small cap data. Center bar_nu at1. Uniform
analyticity of(7)--(9) gives, in these coordinates,

 Phi_i(y,g)=A_i^0 y+g R_i(y,g;theta_i,m),                     (17)

with uniformly bounded derivatives near the zero-tail state. Products of
A_i^0 are uniformly bounded. More explicitly, through N zero-g runs,

 sigma_N=(product theta) sigma_0
  -sum_k[(1-theta_k) product_(l>k)theta_l]tau_(i_k).

The nonnegative weights sum to1-product theta; all other coordinates are
fixed. There is therefore no accumulation proportional to the bridge length.
By(3), sum_run g is finite and its remaining tail tends to0. For derivatives
B_k=A_k^0+O(g_k), a variation-of-constants expansion and discrete Gronwall
bound every product uniformly and give

 ||product B_k-product A_k^0||
                  <=C exp(C sum g_k) sum g_k.                (18)

All states remain in the same small neighborhood on a sufficiently late
actual tail. Endpoint coordinate changes in(15) contribute only O(maximum
remaining finite mass). This avoids the invalid alternative of summing
O(|E|) errors: quiet caps need not be summable over runs.

The exact factor h in(14) survives the transfer. The correcting four masses
have derivatives O(h) by(18) and the uniform inverse chart. After division
by h, the complete derivative differs from its zero-data calculation by
O(maximum remaining finite mass+sum_remaining_runs g), uniformly over bridge
length, run lengths, moments, and the original positive weight vectors.
In particular this estimate remains valid if h is much smaller than other
state coordinates squared.

At zero data, after division by h, the direct moment change gives head
Never vector K and pivot payoff A_i. Fixed entrance and final caps force
the correcting total first-order atom vector a_total to satisfy

 Gamma a_total=-K.

Since K_p=0, its pivot-payoff contribution Gamma_p a_total is zero, while
its survival contribution is -1^T a_total=w^T K. Hence, with the literal
continuation fixed,

 (1/h) d/dm[-u_p,entrance+r nu_entrance]
                  =-A_i+r w^T K+o(1)=-C_i(r)+o(1).           (19)

Equivalently the zero-data linear invariants u-E_p and nu+w^T E applied
along(16) give this balance; (18) bounds their accumulated errors. Forward
to backward conversion adds a factor tending to1 because the conditional
joint tail survival tends to1. Up to a positive joint head-survival factor,
the expression in brackets is the whole objective on this fixed-cap fibre.
Minimality makes its two-sided derivative zero. If C_i(r)!=0, equation(19)
contradicts this for every sufficiently late L>=2 run, proving the lemma.

## Five-date curvature after the timing reduction

First consider normalized structured members(1), with c=h_1=h_2=h_3=1. Then

 det Gamma=-3G_1G_2G_3/4, Gamma^-1 e_p=(1/3,1/3,1/3,1/3),
 w=(4/3,1/(3G_1),1/(3G_2),1/(3G_3)),
 lambda_i=(t_i+1)/(t_i+2), A_i=t_i/(t_i+2).                  (20)

In particular every A_i=C_i(0)>0. The timing lemma thus makes every late run
length one at this structured point for sufficiently small r, and persists nearby
as made precise below. Prepending the previous run to a controlling four-run
word gives, up to a permutation of the three observer labels, one of

 12131, 12312, 12132, 12313.                                (21)

There are24 words. Their first mass is a free parameter; solve the final
four masses by(12), keeping all entrance and final caps fixed. At zero data
the unique tangent, normalized by the first mass derivative u_1=1, is

 x_0=0, x_k=L_(i_k)(lambda_(i_k))x_(k-1)-e_(i_k)u_k,
 x_5=0.                                                    (22)

This is a genuine exact one-dimensional fibre at every sufficiently late
actual instance, with all five pairs active and every quiet/pivot comparison
strict. All earlier caps are preserved.

We derive its r=0 curvature without assuming full-support contact equations.
For atom tangents a_i,k, write

 E_ij=sum_k a_i,k a_j,k, T_ij=sum_(k<l) a_i,k a_j,l.

The endpoint equations give sum_k a_i,k=0 for every player. Thus
T_ij+T_ji+E_ij=0. Distinct observers never act at the same date, so E_ij=0
for observer pairs. Expanding first-outcome probabilities to second order
shows the quadratic coefficient of e_i-U_i is

 D_i=sum_(j!=i)[Gamma_ij T_ij-(J_ij-Gamma_ij)E_ij].            (23)

Passive pair rewards cancel: their contributions to Never and prescribed
payoff coincide to second order. Every observer has D_i=0 on this tangent,
since it has zero atom tangent at dates where its contact is not imposed.
For an observer i this gives

 0=G_i T_ip-(J_ip-G_i)E_pi+sum_(j observer,j!=i)Gamma_ij T_ij.

In this normalization, Gamma_pi=1, J_pi=-1 and Gamma_ij/G_i=-1/2. Dividing by G_i and
summing cancels all observer T_ij terms. Substituting into(23) for the pivot
therefore yields

 Q_0=D_p=-sum_i (J_ip/G_i-2)E_pi
   =-sum_(k=1)^5 A_(i_k)[Gamma_(i_k)x_(k-1)/G_(i_k)]u_k.     (24)

The final equality uses a_p,k=(1-lambda_(i_k))Gamma_(i_k)x_(k-1)/G_(i_k).
The run tangents and this energy are independent of G: in normalized caps
z_j=E_j/G_j, a run of label i gives z_i^+=lambda_i z_i and
z_j^+=z_j-(1-lambda_i)z_i+u/2 for quiet observer j; E_p^+=E_p-u.
Solving(22), the four values of -Q_0 for(21), respectively, are

 t1(t1*t2+t1*t3+3t1+2t2+t3+5)
                  /[2(t1+2)^2(t2+2)^2],
 (2t1-t2)(t2+t3+3)/[2(t2+2)^2(t1+t3+3)],
 [t1*t2+(2t1-t2)(t3+1)+2t1]/[2(t2+2)^2(t1+t3+3)],
 (t2+t3+3)[(2t1-t3)(t2+1)+t1*t3+2t1]
                  /[2(t2+2)^2(t3+2)^2].                    (25)

Every denominator is positive. The second expression and all relabelings
show that all24 energies are strictly negative ONLY IF 2t_i>t_j for every
distinct i,j. Under that same condition every displayed numerator is
positive, proving the converse. Thus the exact criterion for all24 signs is
max t<2min t. This is NOT a restriction in the theorem: the global calendar
argument below only needs15 selected negative words and works for every
positive parameter triple.

The program below checks all four symbolic formulas and also reconstructs
the concrete example's24 energies directly from first-outcome probabilities,
independently of(24). For that example t=(1,7/4,5/4), its least -Q_0 is16/1575.

For clarity about constrained second derivatives, use physical hazard
coordinates with the final continuation fixed. At zero data the differential
of the objective -u_p+r nu is
-(Gamma_p+r 1^T)sum_k da_k. Adding the constraint combination
E_p,entrance+r w^T E_entrance cancels this differential; observer contact
multipliers are zero. The independent constraint gradients from(22) make
these the unique multipliers. The quadratic coefficient on the fibre is
therefore the coefficient of

 E_p,entrance-u_p+r(nu+w^T E_entrance-1).                    (26)

At r=0 it is exactly(24). Since the ambient differential vanishes, quadratic
corrections to the fibre do not change it. Atom and hazard coordinates have
identity derivative at zero and give the same coefficient. Finite IFT and
continuity transfer strict negativity to sufficiently late actual windows.
A local minimum cannot have a negative second derivative along this feasible
two-sided fibre.

## A finite global argument selects negative windows for every positive triple

Order the three observer labels so t_1<=t_2<=t_3, breaking ties arbitrarily.
Each expression(25) is positive whenever its first parameter is at least
its last parameter: the first pattern always has that property, the second
and third use t_1>=t_2, and the fourth uses t_1>=t_3. Thus every qualifying
five-letter word with first label at least its last label has Q_0<0.
There are15 such words among the24 qualifying words.

Every infinite adjacent-distinct three-label word in which all labels recur
has arbitrarily late selected words. Here is a complete finite certificate.
On the24 possible four-letter states assign the following integer heights:

 8: 1321
 7: 3121,3212
 6: 1212,2121
 5: 1213
 4: 1231,2132
 3: 1232,1323,2131,2313
 2: 1313,3131,2323,3232
 1: 1312,2312,2321
 0: 2123,3123,3132,3213,3231.

A transition appends a different label and drops the first. Remove exactly
those transitions whose five-letter word has distinct middle three labels
and first label at least its last. There are48 transitions in total,15
removed and33 remaining. On every remaining transition the height decreases,
except the six transitions of the alternating two-label cycles
1212<->2121, 1313<->3131, 2323<->3232, where it is equal. The short complete
enumeration below verifies these integer statements.

If a late calendar avoided the selected negative words, its nonnegative
height would eventually be constant. Thereafter it would remain in one of
those two-label alternating cycles, contradicting recurrence of all three
labels. This proves the asserted arbitrarily late selected windows. It uses
the entire run calendar, not a bound on the gaps between three-label visits.

## Positive coordinate covariance of the structured family

The preceding finite curvature and calendar proof extends to all c,h_i>0
in(1), without transporting strategies or changing reward signs. In the
linear tangent set y_p=x_p, y_i=h_i x_i and u_i'=h_i u_i. Then(11) becomes
exactly the normalized recurrence: Gamma_i x/G_i=y_p-sum_(j!=i) y_j/2.
Dividing each observer debt equality by G_i and multiplying by c h_i cancels
the observer-observer temporal terms in pairs. It gives

 D_p=-c sum_i t_i sum_k a_p,k(h_i a_i,k).

Thus its quadratic coefficient is c times the normalized coefficient in the
transformed atoms. If the original first mass tangent is1, its transformed
value is h_first, giving the further positive factor h_first^2. Every selected
negative sign persists. Also A_i=c h_i t_i/(t_i+2)>0 and

 Gamma^-1 e_p=(1/(3c),1/(3c h_1),1/(3c h_2),1/(3c h_3))>0.

Invertibility follows by writing Gamma as diagonal row and column multiples
of the normalized matrix. These are exact equalities of finite tangent
calculations; no invariance of strategic inequalities under scaling is assumed.

## Openness, arbitrary remaining rewards, and automatic pivot strictness

Shrink a relatively compact open neighborhood U of(1) so that(4), all
four-run ranks, all A_i>0, the15 selected negative r=0 curvatures, and the signs
Gamma_pi>0>J_pi persist on its closure. These tests depend only on the specified18 coordinates. The six
observer-observer participant rewards never enter the pair-star maps or
curvature; they affect only the assumed strict quiet offers. Every other
reward may be any fixed finite number. The passive pair rewards
affect the r coefficients in(13) and(26), but not their strictly signed r=0
values. Compactness and continuity therefore give epsilon>0 retaining all
signs uniformly on U for 0<=r<epsilon. Higher rewards affect only how late
the analytic/strict-gap neighborhoods begin, not these finite tests.

No pivot-contact hypothesis is needed here. The observers have pairwise
disjoint future date supports on a pair-star tail. When the pivot plays
Never, the first quitting coalition is always a singleton observer, so its
Never payoff is a positive weighted sum of Gamma_pi>0. It is strictly
positive because observers recur. At a date of label i its forced Quit
payoff is exactly J_pi q_i<0. Thus every late pivot comparison is strict;
any earlier contacts belong to a finite head and are preserved by fixed
entrance caps. The timing lemma gives late length-one runs, and then one
of the arbitrarily late selected words contradicts the curvature test. This proves
the main theorem, including Never-mass equality and arbitrary earlier contacts.

## General-chamber Never-mass saturation corollary

Assume(4), v=Gamma^-1 e_p>0, S=sum_i v_i, and r>0. Let P be an actual
positive-Never ALL-END observer-optimal minimum in the eventual pair-star
mode, with every observer recurrent and strict quiet comparisons. Suppose
NO finite pivot deadline attains its full cap, including in the earlier head.
Then

 N_p(P)=1/(1+rS).                                          (27)

Indeed in arbitrarily late controlling four-run windows use(12) while moving
only the entrance pivot cap by t: E_0=E_0^old+t e_p. The chart supplies a
two-sided exact curve. Its active atoms and all window strict comparisons
remain valid. Observer entrance caps and payoffs are fixed. The finitely
many earlier pivot deadlines remain unchanged; since all are strictly below
the old END cap, they stay below the moved END on a sufficiently small
interval. Thus this is an actual feasible comparison for the minimum.

At zero data the total first-order window atom vector a_total satisfies
Gamma a_total=e_p, so a_total=v. By(9), the derivatives of its prescribed
pivot payoff u and joint head survival c obey, uniformly in all run lengths,

 du/dt ->Gamma_p v=1, dc/dt ->-sum_i v_i=-S.

Let s_a be joint head survival before the window, h_p,a opponent head
survival, and nu_tail the fixed continuation joint Never probability.
The exact whole-objective derivative is

 h_p,a-s_a du/dt+r s_a nu_tail dc/dt.

Minimality makes it zero. At late cuts nu_tail->1 and
h_p,a/s_a->1/N_p(P). Taking the limit gives(27). Uniformity follows from
the compact four-run chart; no bounded run-length or fixed physical word
assumption is used. This corollary leaves equality and finite pivot contacts
open in the general chamber; the main theorem excludes both in its stated
open region.

## One actual boundary construction, with all initial caps positive

The support geometry is realizable: local contacts alone do not exclude it.
Use this concrete member of(1), with t=(1,7/4,5/4):

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
Never mass is positive. Assigned caps match and tend to0; telescoping(2)
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

Global minimality and a positive absorbing gap are NOT claimed. The
saturation corollary proves this profile cannot be that minimum. This one
construction has bounded runs; the proof, not the construction, handles
unbounded runs.

## Source correspondence, scope, and downstream use

The actual-law objects are `quittingStoppingLawExpectedPayoff` and
`quittingStoppingLawReplacementPayoffCap` in
`UniformEquilibrium/Quitting/Paths/StoppingLawOperationalDistance.lean`.
The declarations
`quittingStoppingLawExpectedPayoff_behaviorStoppingLaws_eq_terminalPayoff`
and
`quittingStoppingLawCap_behaviorStoppingLaws_eq_continuationBestResponseValue`
identify them with arbitrary behavioral payoff and cap. Conversely,
`quittingTerminalPayoff_stoppingLawProfile_eq_expectedPayoff` and
`quittingStoppingLawCap_eq_continuationBestResponseValue_stoppingLawProfile`
give those identities for independent conditional-hazard implementations.

The literal prefix identity is
`quittingTerminalSemanticPair_rootThenContinuation` in
`UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`.
The full-cap recursion is
`quittingContinuationBestResponseValue_rootThenContinuation_eq_max` in
`UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean`.
Their statements were inspected; they supply the semantic meaning of(2),
not a formalization of the new run chart, timing test, or curvature proof.

The declaration
`not_exists_uniformEquilibriumPayoff_iff_hasPositiveMinimumTerminalSemanticDebt`
in `UniformEquilibrium/Quitting/Terminal/PositiveMinimumSemanticDebt.lean`
concerns positive minimum total debt on a compact semantic carrier. It does
not assert an actual observer-constrained d_p+r nu minimum or the stated
support/quiet-contact mode. A compact endpoint cannot substitute for the
actual law in the summability and conditional-tail arguments.

The downstream use is a case exclusion. If m>0 is the positive absorbing
threshold supplied by the source reduction, choose 0<r<min(m,epsilon) BEFORE
selecting the source minimum afresh. The present theorem does not supply m. If it is actual, has positive original Never, is ALL-END and
observer-optimal, and its raw coordinates lie in the specified region, it
cannot have the stated eventual pair-star mode. Quiet ties, other support
patterns, other raw regions, and a nonrealized source arm remain open.
Every finite comparison and correction chart used in the contradiction is
constructed from that actual law. No successful continuation or uniform
inverse oracle is assumed. The result proves no unrestricted UE class.

The new support coverage is separate from all-four-owner controlled-window
arguments, whose tangents require all observers' contacts at every date and
whose variations require all four hazards positive. Here quiet hazards stay
zero and their comparisons are strictly slack. No claim is made that the structured family
fails any earlier raw matrix certificate.

## Lean handoff

Use the existing complete-law payoff, unrestricted cap, and literal-prefix
definitions named above. First formalize the exact geometric run law and
its cap/payoff contact map(5)--(9). Prove the reduced four-run Jacobian and
its compact-parameter inverse bound, then apply a finite-dimensional implicit
function theorem to obtain the actual local correction chart. Formalize the
exact projective change(15)--(17) and the finite-product estimate(18) before
passing to the normalized timing derivative(19). The finite quadratic and
calendar work separates into the outcome identity(23), the four rational
formulas(25), positive coordinate covariance, and the24-state height lemma.
Finally prove the finite-law implementation, complete-cap preservation and
actual head splice, and combine them with minimality and tail summability.
The saturation corollary uses the same chart and a separate cap-moving
objective derivative. None of these adapters should be packaged as fields
assuming an improving strategy, desired continuation, or uniform correction
oracle; those objects are constructed by the finite maps in this proof.

## Exact reproducible checks

The following Python3/SymPy program checks the four symbolic family formulas,
the finite calendar certificate, the concrete member's24 curvature values
by two independent formulas, and the actual construction's finite contact data. It uses exact rational or symbolic arithmetic only.

```python
import sympy as s
from itertools import permutations, combinations
G=s.Matrix([[0,1,1,1],[-2,0,1,1],[2,-1,0,-1],[2,-1,-1,0]])
J=s.Matrix([[0,-1,-1,-1],[-6,0,-3,-2],[s.Rational(15,2),-5,0,-3],[s.Rational(13,2),-3,0,0]])
patterns=((1,2,1,3,1),(1,2,3,1,2),(1,2,1,3,2),(1,2,3,1,3))
u=s.Matrix(s.symbols('u0:5')); t1,t2,t3=s.symbols('t1 t2 t3', positive=True)
ts=(t1,t2,t3)
def tangent(word,lam):
    x=s.zeros(4,1); states=[]; atoms=[]
    for k,i in enumerate(word):
        states.append(x)
        a=s.zeros(4,1); a[0]=(1-lam[i])*(G*x)[i]/G[i,0]; a[i]=u[k]
        atoms.append(a); x=x-a
    end=x.jacobian(u)
    assert s.factor(end[:,1:].det()) != 0
    z=s.Matrix([1,*(-end[:,1:].inv()*end[:,0])]); sub=dict(zip(u,z))
    return [v.subs(sub) for v in states],[a.subs(sub) for a in atoms],z
ell=s.symbols('ell1:4'); lam={i:ell[i-1] for i in (1,2,3)}
formulas=[
 t1*(t1*t2+t1*t3+3*t1+2*t2+t3+5)/(2*(t1+2)**2*(t2+2)**2),
 (2*t1-t2)*(t2+t3+3)/(2*(t2+2)**2*(t1+t3+3)),
 (t1*t2+(2*t1-t2)*(t3+1)+2*t1)/(2*(t2+2)**2*(t1+t3+3)),
 (t2+t3+3)*((2*t1-t3)*(t2+1)+t1*t3+2*t1)/(2*(t2+2)**2*(t3+2)**2)]
for word,target in zip(patterns,formulas):
    states,atoms,z=tangent(word,lam)
    minusQ=sum((2*lam[i]-1)*(G*states[k])[i]/G[i,0]*z[k] for k,i in enumerate(word))
    minusQ=s.factor(minusQ).subs({ell[i]:(ts[i]+1)/(ts[i]+2) for i in range(3)})
    assert s.factor(minusQ-target)==0
w=G.inv().T*s.ones(4,1); r=s.symbols('r')
lam={i:1-G[i,0]/J[i,0] for i in (1,2,3)}
C={i:G[0,i]*lam[i]+J[0,i]*(1-lam[i])-r*sum(
    w[j]*(-G[j,0]+lam[i]*G[j,i]) for j in (1,2,3) if j!=i) for i in (1,2,3)}
energies=[]
for pattern in patterns:
  for perm in permutations((1,2,3)):
    word=tuple(perm[i-1] for i in pattern); states,atoms,z=tangent(word,lam)
    assert sum(atoms,s.zeros(4,1))==s.zeros(4,1)
    slots=[(k,i,atoms[k][i]) for k,label in enumerate(word) for i in (0,label)]
    def second(who,never):
      out=0
      for (k,i,a),(l,j,b) in combinations(slots,2):
        if i==j or never and who in (i,j): continue
        if k<l: pay=G[who,i]
        elif l<k: pay=G[who,j]
        elif who==i: pay=J[i,j]
        elif who==j: pay=J[j,i]
        else: pay=0
        out+=a*b*(pay-G[who,i]-G[who,j])
      return s.factor(out)
    P2=s.Matrix([second(i,True) for i in range(4)])
    # Each total mass tangent is zero, so the quadratic survival term is zero.
    Q=s.factor(P2[0]-second(0,False)+r*(w.T*P2)[0])
    claimed=-sum(C[i]*(G*states[k])[i]/G[i,0]*z[k] for k,i in enumerate(word))
    assert s.factor(Q-claimed)==0
    assert Q.subs(r,0)<0 and s.diff(Q,r)<0
    energies.append(Q)
assert min(-q.subs(r,0) for q in energies)==s.Rational(16,1575)
assert min(-s.diff(q,r) for q in energies)==s.Rational(548,4725)
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
print('PASS: four symbolic family formulas; 24 direct outcome curvatures; exact ranks; actual fixture and prefix.')
# Complete finite calendar certificate for all positive parameter triples.
from itertools import product
levels={8:['1321'],7:['3121','3212'],6:['1212','2121'],5:['1213'],
 4:['1231','2132'],3:['1232','1323','2131','2313'],
 2:['1313','3131','2323','3232'],1:['1312','2312','2321'],
 0:['2123','3123','3132','3213','3231']}
height={tuple(map(int,x)):h for h,words in levels.items() for x in words}
states={x for x in product((1,2,3),repeat=4) if all(x[k]!=x[k+1] for k in range(3))}
assert set(height)==states
allowed=forbidden=equal=0
for x in states:
 for last in (1,2,3):
  if last==x[-1]: continue
  word=x+(last,); nxt=word[1:]
  if len(set(word[1:4]))==3 and word[0]>=word[4]: forbidden+=1;continue
  allowed+=1; assert height[nxt]<=height[x]
  if height[nxt]==height[x]:
   equal+=1; assert word[0]==word[2]==word[4] and word[1]==word[3]
assert (len(states),allowed,forbidden,equal)==(24,33,15,6)
print('PASS: all48 calendar transitions; only three two-label alternating cycles remain.')
```
