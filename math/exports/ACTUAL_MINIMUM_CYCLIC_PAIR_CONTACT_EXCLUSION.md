# Cyclic pair tails: all64 periodic contact modes excluded, with a nonperiodic contact-density bound

This is an ordinary mathematical actual-source restriction with exact finite
certificates. It does not solve Fin4 and is not Lean-checked. The periodic
object in the first conclusion is the CONTACT calendar, not hazard amplitudes.

## Statement

There are four players, pivot0 and observers1,2,3. Native own-singleton and
AllNever rewards are0. Write Gamma_ij=Z_i({j}) and J_ij=Z_i({i,j}) for i!=j,
with zero diagonals. Consider the raw point

    Gamma=[0,1,1,1; -2,0,1,1; 2,-1,0,-1; 2,-1,-1,0],
    J=[0,-1,-1,-1;
       -6,0,-4/21,37/63;
       15/2,-13/7,0,-115/63;
       13/2,-13/21,50/63,0].                            (1)

There is an open neighborhood in these24 raw coordinates, independent of
the other32 native reward coordinates, with the following property. For
every table in this raw neighborhood, with any fixed finite assignment of
the other32 rewards, there is a table-dependent r0>0 such that both
conclusions below hold for0<=r<r0.

Let P be an ACTUAL independent complete stopping-law profile. Assume every
ORIGINAL marginal Never mass is positive; P is ALL-END; all three observers
are optimal; and P minimizes d_0+r*nu over the actual observer-optimal carrier,
or a larger carrier containing all such actual comparison profiles. Here
B_i is the unrestricted behavioral replacement cap, U_i the prescribed
payoff, e_i the pure-Never payoff, d_i=B_i-U_i, and nu the product of the
four original Never masses. ALL-END means B=e.

1. If there are INFINITELY MANY nonempty dates, P cannot eventually have
   cyclic pair supports {0,1},{0,2},{0,3}, together with ANY period-three
   pattern of quiet observer contacts. This covers all64 patterns.
2. Every sufficiently late NINE-date window with those cyclic pair supports,
   in any phase, contains at least THREE quiet observer contacts, counted
   as date/observer slots. Contacts, supports and amplitudes outside this
   window are unrestricted. This local statement needs no infinite-tail
   assumption. In particular an infinite cyclic pair tail has lower quiet
   contact density at least1/3 per nonempty date, even when its contact
   pattern switches arbitrarily.

A quiet contact is Quit=Never at an inactive observer; every other quiet
comparison is strict. Empty dates are deleted. No periodic, geometric,
comparable, or lower-bounded hazard amplitudes are assumed. Earlier pivot
or observer cap contacts and original Never probabilities are unrestricted.
No Never-mass inequality or saturation condition is assumed.

Generic contact-rank restrictions already rule out long stretches in which
ALL inactive observers are tied. They leave partial contacts. The present
increment permits every period-three partial-contact pattern and also
constrains arbitrary nonperiodic switching through the nine-date bound.
Neither conclusion forces every sparse date to have strictly slack quiet
comparisons. Arbitrary nonperiodic contact calendars with enough contacts,
other support words, larger supports, other raw regions and nonrealized
compact source arms remain outside the exclusions.

Encode quiet contacts by(c0,c1,c2) in{0,1,2,3}^3. At the label1 date the
inactive list is(2,3), at label2 it is(1,3), and at label3 it is(1,2); bit0
selects the first and bit1 the second. The proof gives a disjoint complete
partition:19 negative-curvature fibres,41 rational Farkas certificates,
and4 canonical-shape reductions followed by a finite feasible promotion.
The embedded checker verifies both coverage and every finite certificate.

## Actual finite comparisons and the zero-data matrices

For root hazards q and S subset I\{i}, define the finite coalition weights

    pi_i(S;q)=product_(j in S)q_j product_(j notin S,j!=i)(1-q_j),
    Q_i(q)=sum_(S subset I\{i}) pi_i(S;q) Z_i(S union{i}),
    A_i(q)=sum_(nonempty S subset I\{i}) pi_i(S;q) Z_i(S),
    H_i(q)=product_(j!=i)(1-q_j), c(q)=product_j(1-q_j).

Let e be the actual Never payoff vector, U the prescribed payoff vector,
u=U_0 the pivot prescribed payoff, and nu the joint Never mass. Superscript+
denotes the literal continuation. The exact recursions are

    e_i=A_i(q)+H_i(q)e_i^+,
    B_i=max(Q_i(q), A_i(q)+H_i(q)B_i^+),
    U_i=q_i Q_i(q)+(1-q_i)A_i(q)+c(q)U_i^+,
    nu=c(q)nu^+.

Finite native rewards give A_i=Gamma_i q+O(|q|^2) and
Q_i=J_i q+O(|q|^2). The full cap permits every behavioral response; fixing
private randomness reduces such responses to deadlines and Never.

A finite window comparison keeps the complete continuation literally fixed
and fixes all FOUR entrance Never caps. It retains all supported observer
contacts. It also either retains each original quiet contact exactly, or
moves its gap strictly negative with zero hazard, or promotes its hazard
strictly positively while retaining its contact. All initially strict quiet
comparisons persist for sufficiently small variation size. Existing positive
hazards remain positive and all hazards stay below1. Hence the exact maximum
recursion preserves ALL-END and observer optimality. The entire earlier head
is preserved, including earlier pivot contacts, because all entrance caps
and observer prescribed values are fixed. Law normalization and positive
original Never survive this finite hazard splice.

Pivot strictness at late pair windows needs no outside support assumption.
Let f be the sum of the three observer remaining finite masses, let
c=min_i Gamma_0i>0 and let R bound pivot rewards. Independence gives

    e_0>=c*f-(c+R/2)*f^2.

A supported observer has positive remaining finite mass, so e_0>0 on every
sufficiently late pair window. Immediate pivot Quit is J_0i*q_i<0.
These finitely many strict comparisons persist along small local curves.

At zero data, with tangent v_k in R4, fixed caps are equivalent to

    sum_k v_k=0,                                      (2)

because Gamma is invertible. The contact row at date k for observer i is

    (J v_k)_i-(Gamma sum_(l>=k)v_l)_i=0.               (3)

All matrices in the certificates are built directly from(2),(3).

## Nineteen two-sided fibres and their complete finite coverage

The19 contact modes and their witness lengths, starting at label1, are

    000:5, 001:7, 002:7, 003:11,
    010:7, 011:13, 012:13, 020:7, 021:13, 030:13,
    100:8, 101:14, 102:14, 120:15,
    200:8, 201:14, 202:14, 210:15, 220:15.

On an N-date witness there are2N old supported hazards. Impose four cap
constraints, N active observer contacts, and EVERY quiet contact specified
by the pattern. The embedded exact checker verifies full row rank for each
listed witness. Its nonzero kernel vector changes no zero hazard. By the
finite implicit function theorem it gives a two-sided exact constrained
curve through every sufficiently late actual instance. All omitted quiet
gaps are strictly slack, with an instance-dependent permitted radius.

Each of these19 witnesses also applies when the ACTUAL quiet-contact set
is a SUBSET of its certified set. Preserve every row in the larger set at
its actual current gap value: zero at a contact, strictly negative otherwise.
The derivative rows, full rank and negative Hessian are unchanged; all
contacts outside the certified set must be absent. Thus no periodicity of
the actual contact subset is required. In particular the15-date certificate
210 excludes arbitrary switching among000,200,010,210 on its cyclic support
window, by retaining the two designated quiet-gap slots in each period.

At r=0 the constrained quadratic is the pivot-debt quadratic

    D(q)=sum_k q_0k[-Gamma_0 sum_(t<k)q_t-J_0 q_k].     (4)

The checker verifies v^T Hess(D) v/2<0 for each witness. For example mode020
on seven dates gives-181368002/315618147. All19 signs are strict rational
inequalities, not numerical eigenvalue tests.

For the constrained Hessian transfer, at zero-tail data add the constraint
combination E_0+r*w^T E to the objective -u+r*nu, where w^T=1^T Gamma^-1.
This cancels its ambient differential; contact multipliers are zero. At
r=0 the resulting quadratic restricted to(2),(3) is exactly(4); passive
pair terms cancel. Full row rank gives a smooth IFT chart and unique
constraint multipliers. Thus its second derivative remains negative on
sufficiently late actual windows. Continuity permits a small positive r
threshold and an open raw neighborhood. The other32 fixed rewards affect
those smallness thresholds but not the strictly negative r=0 certificates.
A minimum on a two-sided feasible curve cannot have this curvature.

## Forty-one one-sided Farkas exclusions

For a five-date window, enumerate only subsets of its actual quiet contacts
that may be promoted. For a chosen subset P impose four fixed caps, five
active contacts, and the promoted contacts; keep all other quiet hazards0.
The exact matrices have a one-dimensional kernel. Retain an orientation
only when every promoted hazard derivative is strictly positive and every
unpromoted tied gap derivative is strictly negative. These are actual
one-sided feasible IFT rays, with no weak-sign feasibility assumption.

Among the three remaining modes with at most two quiet contacts per period,
022 and300 use five dates and110 uses six. Another38 denser modes use the
same certificate construction. Modes013 and211 use eight dates,320 uses
seven, and321 uses a five-date window starting at phase3. All others use
five dates starting at phase1. The complete list is the41-case BASIS record
in the embedded checker; its complement to the19 fibres is exactly
031,221,230,231, treated below. Let C_a(q) be each retained ray's
linear derivative of(4), E(q,e0) the active and quiet contact rows on the
whole block of at most eight dates, and G_b(q,e0) its remaining quiet gap rows.
The embedded checker reconstructs rational nonnegative alpha_a,beta_b
and unrestricted mu such that

    sum_a alpha_a C_a -sum_b beta_b G_b +mu^T E
             =-sum_j gamma_j q_j,   gamma_j>=1.        (5)

The coefficient of each initial observer cap is0. All coefficients and
inequalities in(5) are verified exactly by multiplication after solving an exact linear system selected by compact integer basis
records. Every reconstructed nonnegative coefficient and every residual
hazard coefficient is checked. No floating-point solver, unverified LP
return value or stored matrix payload is used.

In the zero-data leading-order problem, necessary minimum conditions are
C_a>=0 on every feasible ray, G_b<=0 on quiet slots, and E=0 at contacts.
For an actual profile the necessary inequalities concern the exact slopes
H_a>=0; the uniform passage below handles their errors. Equation(5)
is incompatible with these conditions for any nonzero nonnegative vector
of old supported hazards. Thus at least one strict feasible direction
improves the objective, uniformly over normalized baseline hazard shapes.
The two-window110 certificate is a genuine overlap argument: each isolated
window can pass its own first-order test, but compatible cap geometry across
the common dates cannot pass both.

## Uniformity of the first-order transfer

An actual observer's cap inside the block is O(|q|), since it is tied at
some supported date of each cycle and the finite Never recursion propagates
that bound. Therefore the actual linear contact equations have O(|q|^2)
errors. Hidden pivot tail cap divided by window size need not be bounded;
a separate analytic cancellation is essential.

For each selected ray let H be the exact derivative of -u+r*nu, obtained
from its invertible IFT minor. At q=0 and zero observer tail caps, allow
arbitrary small pivot tail cap T, prescribed pivot payoff U, and joint
Never V near1. The cap differential is

    [Gamma-T e_0(1-e_0)^T] sum_k v_k.

This matrix is invertible for small T, so fixed caps force sum v_k=0.
The objective derivative is then identically0 for ALL T,U,V. Each of the
three observer tail caps is an analytic function of the window hazards,
obtained from that observer's last supported contact and inversion of the
finite Never recursion to the final cut. These functions vanish at q=0.
Consequently H has a factor of window hazard size, uniformly in hidden
pivot data. Actual tails satisfy T,U->0 and V->1, so at r=0

    H=C_a(q)+o(|q|),

uniformly in normalized window shape; for small r the extra first jet is
O(r|q|). This excludes an unsupported additive O(T^2)/|q| error. Applying
the finite weights in(5), the strict negative margin dominates all contact,
raw-perturbation and tail errors. For overlapping windows each whole-profile
derivative is its local derivative times positive head joint survival, so
its sign is unchanged. One obtains an actual improving finite splice.

These60 cases involve finitely many rank and strict-sign certificates.
Intersect their raw neighborhoods and choose the minimum r threshold.
Positive original Never makes hazards and conditional finite-mass payoffs
tend to0. The infinite nonempty calendar supplies arbitrarily late witness
windows for any of these60 eventually periodic contact modes.

## Four remaining modes: actual shape production followed by a finite move

The remaining contact modes are031,230,231,221. The following arguments
allow additional quiet contacts as well. For the first three modes six
dates suffice; mode221 uses its eventual repeated contact pattern. No
periodic hazard law is assumed in any case.

### A finite promotion tolerating small quiet slack

Define five four-coordinate hazard vectors

    a0=(26/21,1,0,0), a1=(50/63,0,1,0),
    a2=(52/63,0,0,1), a3=a0/2, a4=a1/2.

There is a neighborhood of this normalized shape such that a sufficiently
late actual pair window12312 in it contradicts the stated minimum.
Only the five active observer contacts are required; the ten quiet slots
may be tied or strictly slack.

Use thirteen physical hazard variables: the ten original pair hazards and
three new hazards at slots(2,2),(3,2),(4,3), with dates numbered0 through4.
Fix all four entrance Never caps and the literal complete continuation.
Impose the five original active observer contacts and the three promoted
contacts. There are twelve equations. The new hazard at(4,3) is the free
parameter s. At zero-tail data, the cap derivative is Gamma times the total
atom tangent. The contact row for observer i at date k is

    (J v_k)_i-(Gamma sum_(l>=k)v_l)_i.

The square minor obtained by deleting the free-coordinate column is
1144740850/64827, hence nonzero. Its normalized kernel v has the following
three new-hazard coordinates:

    16090533/52033675, 8562199/5065225, 1.

All are positive. The seven other quiet-gap derivatives, in the order
(0,2),(0,3),(1,1),(1,3),(2,1),(3,3),(4,1), are

    -409825/75306, -409825/225918,
    -978476102/480791157, -807201305/480791157,
    -5682930311/1717111275, -63306659/45587025, -702/1243.

All are negative. These are strict signs, so they survive small raw and
state perturbations.

Suppose the original five controls are eta a_k+O(kappa eta), with eta>0
and small kappa. Because each observer is active somewhere in these five
dates, its exact active contact and the finite cap recursion determine
all its local caps to first order from these controls. The reference shape
satisfies every observer contact. Consequently every quiet gap is
O((kappa+delta)eta+eta^2), where delta is the raw matrix displacement.
All observer continuation caps are O(eta). This conclusion does not require
the pivot continuation cap to be comparable to eta.

The finite implicit-function chart solves the twelve equations with every
promoted contact set to zero. At s=0 its corrected point may have signed
new hazards; it differs from the original point by
O((kappa+delta)eta+eta^2). This auxiliary signed point is used only for
analytic estimates. Choose a small FIXED theta>0 and take s=theta eta.
Then choose kappa,delta sufficiently small compared with theta. The strict
kernel signs ensure that the final point has positive old and new hazards,
while all seven unpromoted quiet gaps are negative. The imposed eight
contacts hold exactly. This is a valid actual independent-law endpoint;
feasibility of the auxiliary s=0 correction is unnecessary.

For sufficiently late actual tails the pivot comparison also remains
strict. Near the reference its singleton rewards from every observer are
positive and its participant pair rewards are negative. If the opponents'
remaining finite masses have sum f, its Never payoff is at least c f-C f^2.
Its current Quit offer is at most -c sum_i q_i+C(sum_i q_i)^2. The corrected
window has positive observer hazards of order eta and still has small
remaining finite mass, so Q_0<0<e_0. Literal backward full-cap recursion
now preserves ALL-END and observer optimality exactly. Fixed entrance
caps preserve the whole earlier head, including earlier pivot ties.

It remains to compare objectives despite the off-base contact correction.
Let T be the literal pivot continuation Never cap, U its prescribed payoff,
and V the joint Never mass. At zero window hazards and zero observer
continuation caps, while allowing T,U,V independently near0,0,1, the cap
derivative on a total atom tangent w is

    A_T w,  A_T=Gamma-T e_0(1-e_0)^T.

The derivative of F=-u_0,entrance+r nu_entrance is

    [-Gamma_0+(U-rV)1^T]w.

Choose the row multiplier lambda by

    lambda A_T=Gamma_0-(U-rV)1^T.

The matrix A_T is invertible near the reference and small T. Thus the
ambient hazard gradient of F+lambda E_entrance vanishes EXACTLY at zero
window hazards and zero observer continuation caps for all T,U,V near
their limits. On the near-cyclic window its gradient is O(eta), uniformly
even if T/eta or U/eta is unbounded. Since both compared points have the
same entrance caps, the initial analytic correction changes F by at most

    O((kappa+delta)eta^2)+O(eta^3).

Along the exact corrected fibre, at the reference shape and r=0, the
leading derivative is

    dF/ds=-eta*6814784809/5151333825+o(eta).

One direct exact computation uses f0=(40/7,2,2,2), f_(k+1)=f_k-a_k, and

    C=sum_k v_(k,0)[(Gamma f_k)_0-(J a_k)_0]
       +a_(k,0)[(Gamma sum_(l>=k)v_l)_0-(J v_k)_0].

It gives the displayed negative constant. Changing the first-order pivot
continuation cap does not change C, because sum_k v_(k,0)=0; the exact
gradient cancellation above controls arbitrary larger hidden pivot state.
Passive and higher rewards cancel from this r=0 quadratic debt coefficient.

The derivative changes by O(s)+O((kappa+delta)eta)+o(eta) along the segment
0<=s<=theta eta. At r=0 and zero limiting tail state, all second derivatives
of the cap-corrected objective are the quadratic pivot-debt derivatives,
so they depend only on Gamma,J: passive rewards cancel and higher rewards
enter only higher order. Thus first choose theta small enough and then
kappa,delta small enough using only the raw reference data. For each fixed
remaining reward assignment, restrict r to a small interval by continuity
BEFORE selecting the source, then pass to a sufficiently late actual cut.
Its integrated gain is at most -c theta eta^2,
which dominates the initial correction cost. The endpoint strictly lowers
F. The entire-profile objective changes by this amount times the positive
joint head-survival factor. This contradicts minimality. The neighborhood
can be chosen using only the reference raw data; late cutoffs and the
allowable r interval may depend on the other fixed finite rewards.

### Three six-date contact cones force the near-cyclic shape

Use variables X=(E_1(0),E_2(0),E_3(0),p0,b0,...,p5,b5), where at date k
the pair label is i=k mod3+1 and q_k=p_k e_0+b_k e_i. At the reference,
propagate E_next=E-Gamma_observer q and form each gap J_i q-E_i.
Let M contain the six active contact rows and the selected quiet rows.
Let R contain all omitted quiet rows. For an actual six-window of maximum
hazard eta, the exact finite root formulas give

    M X=O(delta eta+eta^2),  R X<=O(delta eta+eta^2),
    |X|<=C eta.

The last estimate follows by propagating backwards from each observer's
active contact within the window. No future pivot-cap estimate is used.

For mode(2,3,1), M has rank14, and deleting the first observer-hazard
column gives determinant -179085920/583443. Its kernel, normalized by
b0=1, is

    (-52/7,52/7,52/7,
     26/21,1,50/63,1,52/63,1,
     13/21,1/2,25/63,1/2,26/63,1/2).

For mode(0,3,1), M has rank12. The six omitted slots are
(0,2),(0,3),(2,2),(3,2),(3,3),(5,2). Their strictly positive weights

    (7/6,21/8,1753865/646464,
     556012/564213,556012/430495,229/378)

annihilate R on ker M. For mode(2,3,0), the omitted slots are
(0,2),(2,1),(2,2),(3,2),(5,1),(5,2), and the corresponding weights are

    (1728/3887,1211431788/306407725,20412/8671,
     108/169,567/229,20979/26335).

Again they annihilate R on ker M. In each case stacking R beneath M gives
rank14 with the same positive-control kernel displayed above. The positive
dependence implies that all rows R X are also bounded BELOW by
-C(delta eta+eta^2): their weighted sum is of that order and each other row
is bounded above. Hence the stacked equalities hold up to that error.

Inverting on a complement to the one-dimensional kernel puts X within
O((delta+eta)eta) of its positive ray. Positivity of the original hazards
fixes its orientation and makes its scale comparable to eta. Thus the
first five dates have the near-cyclic shape required for the finite
promotion. This proves the three local six-date exclusions. It does not
turn a small quiet gap into an exact contact.

### The remaining mode has a positive contracting cap coordinate

For mode(2,2,1), one period has six contact equations and six controls.
The derivative with respect to those controls has determinant781625/9261.
The exact observer cap equations therefore solve analytically for the six
controls from the three entrance observer caps E:

    q=U E+O(|E|^2),  E_next=T E+O(|E|^2).

The observer equations involve no pivot cap or prescribed payoff. Here

    U=[-1/6,0,0;
       -7/4,0,-21/13;
       -17/90,2/15,-14/65;
       -119/500,-273/250,3213/3250;
       -221/1125,-1019/4875,201/1625;
       -20531/18500,21399/120250,-138663/120250],

    T=[2301/1850,9171/12025,-227/12025;
       -16241/9250,159853/120250,-310861/120250;
       -221/250,-3057/3250,1809/3250].

The characteristic polynomial is

    (2x-1)(60125x^2-158113x+39776)/120250.

Its roots are lambda_c=1/2, lambda_s in(1/4,1/2), and lambda_u>1.
The right central eigenvector is v_c=(-1,1,1). The left eigenvector

    ell=(-573509,-6114,-470398)/96997

satisfies ell v_c=1 and, critically, ell=alpha^T U with EVERY alpha_i>0:

    alpha=(4046202563/3103904000,1/100,1/100,
           32037834073/37246848000,1/100,
           183562514591/37246848000).

Since U is injective and the actual six controls are nonnegative, these
identities give, for small nonzero actual E,

    x=ell E>0,  |E|<=C x,  x_next=lambda_c x+O(x^2).

Indeed x=alpha^T q+O(|E|^2), while |q| is comparable to |E|. The quadratic
term is absorbed by the positive linear term. Positive original Never
makes actual caps tend to zero, so eventually x contracts geometrically.

Decompose E=x v_c+y v_s+z v_u into the three real eigenspaces. The ratios
b=y/x and c=z/x are bounded because |E|<=C x. Their exact recurrences are

    b_next=(lambda_s/lambda_c)b+O(x),
    c_next=(lambda_u/lambda_c)c+O(x).

Forward contraction gives b->0. For c, iterate backwards m steps:
c_n=a^(-m)c_(n+m)-sum_(j=0)^(m-1)a^(-j-1)epsilon_(n+j), with
a=lambda_u/lambda_c>1 and epsilon_n=O(x_n). Boundedness kills the first
term as m->infinity, and the geometric series tends to zero as n->infinity.
Thus c->0 as well. Consequently E_n/x_n->v_c and
x_(n+1)/x_n->1/2. Normalizing by the first observer hazard gives precisely
the five-date shape a0,a1,a2,a0/2,a1/2. The finite promotion applies.

This proof persists in a raw neighborhood. The three eigenvalues remain
simple, real, positive, and ordered lambda_s<lambda_c<1<lambda_u. The
chosen six-control Jacobian stays invertible. The3-by3 minor of U^T using
columns0,3,5 is -28224/156325, so keep alpha_1,alpha_2,alpha_4=1/100 and
solve the other three coefficients continuously for ell; all remain
positive. The contracting coordinate and the bounded relative-mode proof
therefore persist, with the final hazard ray close to the reference ray.
No statement about arbitrary switching products is used: this is one
repeated contact pattern and its exact analytic period map.

## Arbitrary switching: three quiet contacts in every nine cyclic dates

The preceding64-mode result concerns an eventually period-three contact
calendar. This additional argument imposes no periodicity on contacts and
proves the local nine-date conclusion in the statement.

At a zero-tail reference, use the18 old supported atom tangents v. The
four fixed-cap equations are sum_k v_k=0, since det Gamma=6. At date k
the active observer i(k) contributes the contact row

    L_ki(v)=(J v_k)_i-(Gamma sum_(l>=k)v_l)_i=0.

Let M be this13-by18 matrix and B its rational nullspace basis. For each
of the three phases M has rank13, so B has five columns. Put

    D(v)=sum_k v_0k[-Gamma_0 sum_(t<k)v_t-J_0 v_k],
    F=B^T Hess(D) B.

There is a three-dimensional negative-definite subspace of this base
fibre in EVERY phase. Numbering B columns from0, the following triples
have the stated leading Gram determinants:

    phase1, columns(0,2,3): -7/128, 7607/156816, -34643/20072448;
    phase2, columns(0,1,3): -276/847, 55040/617463, -7033837/232440516;
    phase3, columns(0,2,3): -64/207, 41135/156816, -123380/2028807.

Sylvester's criterion proves negative definiteness. Each of the18 quiet
rows L_ki B is nonzero. Every pair of DISTINCT quiet rows is independent
except two explicitly classified pairs: the two quiet slots at the first
date, and the two quiet slots at the last date. Each exceptional pair has
rank1. The checker below verifies all153 pairs in each phase exactly.

Suppose there are at most two quiet contacts, not an exceptional pair.
Adjoining their rows to M preserves full row rank. Their common kernel
intersects the negative three-space nontrivially, because at most two
linear constraints are added. Hence the full fixed-contact fibre has a
strictly negative tangent, produced by elementary kernel intersection.
No rank or successful-correction oracle is assumed.

In either exceptional pair case every other date is fully guarded. There
are eight consecutive guarded dates after or before that boundary date.
Choose five of them. The five-date active-contact fibre has dimension1,
full constraint rank, and quadratic value respectively

    -7/256, -138/847, -32/207

in the three cyclic phases. This is again a strict negative direction.


All rank and negative-space checks are finite. Their strict signs persist
on one raw neighborhood. For nonexceptional quiet sets, the full-rank IFT
and constrained-Hessian transfer proved above supply a two-sided improving
curve. For the two boundary exceptions use the guarded five-date subwindow;
no nonlinear redundancy is assumed. Pivot strictness with arbitrary outside
supports was proved above. This excludes every at-most-two-contact nine-date
window at a sufficiently late cut. Disjoint nine-date blocks give the lower
asymptotic density1/3 on any infinite cyclic pair tail.

## Strategic inputs, boundary checks and semantic correspondence

The strategic inputs are an ACTUAL attained observer-optimal minimum,
ALL-END, positive original Never, and raw membership in the stated region.
The periodic conclusion additionally requires an infinite nonempty calendar
and the specified support/contact pattern. These are inputs to a case
exclusion, not objects produced by this proof. In particular a compact
semantic minimum does not supply an actual law, and the argument neither
constructs a uniform equilibrium nor creates a positive absorbing gap.
Its conditional importance is complete coverage of the64 partial-contact
choices on this cyclic calendar, plus a quantitative obstruction to sparse
nonperiodic contact switching.

The reference matrices satisfy every strict finite criterion in the checker,
so the open raw region is nonempty. No actual minimizing law at that point
is asserted. The raw restriction is essential: in the allzero native table,
put q_0(t)=q_(1+(t mod3))(t)=2^(-t-3), with the other hazards0. All original
Never masses are positive; the calendar is infinite and cyclic; all three
observers are tied everywhere; and ALL-END and observer optimality hold.
At r=0 every law is a global minimum of the zero objective. Thus the stated
exclusions would fail if applied to arbitrary raw tables.

The infinite-calendar hypothesis is also essential for the periodic
corollary: at r=0 the AllNever law is a minimum at every native table, but
has no nonempty dates. Its inclusion by a vacuous eventual-periodicity
reading is explicitly ruled out. The local nine-date conclusion is simply
vacuous when no such window exists.

## Final scope and semantic correspondence

Intersecting the finitely many neighborhoods and small-r thresholds, with
the open eigenvalue and positivity conditions of mode221, proves both
conclusions. All64 period-three CONTACT patterns are excluded; this is
not an exclusion of every nonperiodic contact calendar or arbitrary Fin4.
The proof supplies no actual source minimizer or positive absorbing gap.
If a reduction supplies a positive threshold m, choose0<r<min(m,r0) before
selecting the source afresh. No old source is transported between tables.

The inspected declarations are quittingTerminalSemanticPair_rootThenContinuation
in UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean and
quittingContinuationBestResponseValue_rootThenContinuation_eq_max in
UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean. They supply literal
splice and unrestricted full-cap meanings, not a Lean proof of the new
fibres, Farkas identities, finite promotion or spectral reduction.

## Lean handoff

Formalize the finite coalition maps above and their literal full-cap splice
first. Next encode the rational contact matrices, full-row-rank minors,
negative quadratic forms and reconstructed Farkas identities; the checker
supplies exact arithmetic specifications. The analytic steps requiring new
proofs are the finite-dimensional constrained IFT, its two-sided Hessian
transfer, the one-sided finite promotion with cap-gradient cancellation,
and the positive-covector period map with bounded unstable-ratio recurrence.
Finally assemble the64-case partition and nine-date rank exceptions using
the existing complete-law semantic declarations. No new Lean theorem,
compilation, or formal verification is claimed here.

## Complete exact finite certificate

The following standalone Python3/SymPy program checks the19 negative fibres,
all41 rational Farkas certificates, disjoint complete64-mode coverage,
the four geometric components and finite promotion, and every quiet-set
rank and negative subspace needed for the nonperiodic nine-date statement.
Integer basis records only select linear systems; every reconstructed dual
sign and identity is verified independently using rational arithmetic.

```python
"""Exact Farkas producer/verifier for periodic-contact finite windows."""
from functools import lru_cache
from itertools import product
import sympy as s
R=s.Rational
G=s.Matrix([[0,1,1,1],[-2,0,1,1],[2,-1,0,-1],[2,-1,-1,0]])
J=s.Matrix([[0,-1,-1,-1],[-6,0,-R(4,21),R(37,63)],[R(15,2),-R(13,7),0,-R(115,63)],[R(13,2),-R(13,21),R(50,63),0]])
@lru_cache(None)
def rays(phase,S):
 slots=[(k,j)for k in range(5)for j in range(4)];word=[(phase+k)%3+1 for k in range(5)]
 active=[(k,j)for k,i in enumerate(word)for j in(0,i)];quiet=[(k,j)for k,i in enumerate(word)for j in(1,2,3)if j!=i];aidx=[slots.index(x)for x in active];qidx=[slots.index(x)for x in quiet]
 def gap(k,i):return s.Matrix(1,20,[(J[i,j]if t==k else 0)-(G[i,j]if t>=k else 0)for t,j in slots])
 cap=s.Matrix([[int(i==j)for k,j in slots]for i in range(4)]);act=s.Matrix.vstack(*[gap(k,i)for k,i in enumerate(word)]);Q=s.Matrix.vstack(*[gap(k,i)for k,i in quiet]);H=s.zeros(20)
 for k in range(5):
  for t,j in slots:
   val=(-G[0,j]if t<k else 0)-(J[0,j]if t==k else 0);H[4*k,4*t+j]+=val;H[4*t+j,4*k]+=val
 ans=[];P=S
 while True:
  inds=[j for j in range(10)if P>>j&1];cols=aidx+[qidx[j]for j in inds];M=s.Matrix.vstack(cap,act,*[Q[j,:]for j in inds])[:,cols];ns=M.nullspace();assert len(ns)==1
  for sign in(1,-1):
   v=s.zeros(20,1)
   for k,a in zip(cols,ns[0]):v[k]=sign*a
   if any(v[qidx[j]]<=0 for j in inds):continue
   gaps=Q*v
   if any(gaps[j]>=0 for j in range(10)if S>>j&1 and not P>>j&1):continue
   coeff=(v.T*H)[:,aidx];ans.append((P,coeff))
  if P==0:break
  P=(P-1)&S
 return ans

def certificate(cw,N,phase=0,verbose=False):
 active=[(k,j)for k in range(N)for j in(0,(phase+k)%3+1)]
 def base(k,i):return s.Matrix(1,3+2*N,[-int(i==j)for j in(1,2,3)]+[(J[i,j]if t==k else 0)+(G[i,j]if t<k else 0)for t,j in active])
 eq=[];quiet=[]
 for k in range(N):
  i=(phase+k)%3+1;eq.append(base(k,i))
  for bit,j in enumerate(j for j in(1,2,3)if j!=i):(eq if cw[(phase+k)%3]>>bit&1 else quiet).append(base(k,j))
 objectives=[];names=[]
 for start in range(N-4):
  S=sum(cw[(phase+start+k)%3]<<(2*k)for k in range(5))
  for P,coef in rays((phase+start)%3,S):
   row=s.zeros(1,3+2*N)
   for j in range(10):row[3+2*start+j]=coef[j]
   objectives.append(row);names.append((start,P))
 npositive=len(objectives)+len(quiet);M=s.Matrix.hstack(*[r.T for r in objectives],*[-r.T for r in quiet],*[r.T for r in eq]);n=M.cols
 zero,tight=BASIS[(tuple(cw),N,phase)]
 system=s.Matrix.vstack(M[:3,:],*[s.eye(n)[k,:]for k in zero],*[M[3+k,:]for k in tight]);rhs=s.Matrix([0]*(3+len(zero))+[-1]*len(tight))
 sol,params=system.gauss_jordan_solve(rhs)
 if params:sol=sol.subs({p:0 for p in params})
 sol=s.Matrix(sol);out=M*sol
 assert all(a>=0 for a in sol[:npositive]);assert list(out[:3])==[0]*3;assert all(a<=-1 for a in out[3:])
 if verbose:print('certificate',list(sol),'residual',list(out),flush=True)
 return True



# Compact integer bases reconstruct rational Farkas witnesses; every sign is verified.
BASIS={
 ((0, 1, 3),8,0):([0, 1, 2, 4, 6, 7, 8, 9, 10, 11],[0, 1, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]),
 ((0, 2, 3),5,0):([0, 2, 4, 5, 6],[1, 2, 3, 4, 5, 6, 7, 8, 9]),
 ((0, 3, 2),5,0):([0, 2, 5, 6],[0, 1, 2, 3, 4, 5, 6, 7, 8, 9]),
 ((0, 3, 3),5,0):([0, 2, 4, 5],[0, 1, 2, 3, 4, 5, 6, 7, 8, 9]),
 ((1, 0, 3),5,0):([0, 2, 4, 5],[0, 1, 2, 3, 4, 5, 6, 7, 8, 9]),
 ((1, 1, 1),5,0):([0, 2, 3, 4, 5, 7],[0, 1, 2, 3, 4, 5, 6, 7, 8, 9]),
 ((1, 1, 2),5,0):([0, 2, 3, 4, 5, 6, 7],[0, 1, 3, 4, 5, 6, 7, 8, 9]),
 ((1, 1, 3),5,0):([0, 2, 3, 4, 5, 6],[0, 1, 2, 3, 4, 5, 6, 7, 8, 9]),
 ((1, 2, 1),5,0):([1, 2, 3, 5],[0, 1, 2, 3, 4, 5, 6, 7, 8, 9]),
 ((1, 2, 2),5,0):([0, 1, 3, 4, 5, 6, 7],[0, 2, 3, 4, 5, 6, 7, 8, 9]),
 ((1, 2, 3),5,0):([0, 1, 3, 4, 5, 6],[0, 1, 2, 3, 4, 5, 6, 7, 8, 9]),
 ((1, 3, 0),5,0):([0, 1, 2, 4, 5, 6, 7],[0, 1, 2, 3, 4, 6, 7, 8, 9]),
 ((1, 3, 1),5,0):([0, 1, 2, 4, 5, 6],[0, 1, 2, 3, 4, 5, 6, 7, 8, 9]),
 ((1, 3, 2),5,0):([0, 1, 2, 4, 5, 6, 7, 8, 9, 10],[0, 1, 2, 3, 4, 5, 6, 7, 8, 9]),
 ((1, 3, 3),5,0):([0, 1, 2, 4, 5, 6, 7, 8, 9],[0, 1, 2, 3, 4, 5, 6, 7, 8, 9]),
 ((2, 0, 3),5,0):([0, 2, 3, 5],[0, 1, 2, 3, 4, 5, 6, 7, 8, 9]),
 ((2, 1, 1),8,0):([0, 1, 2, 3, 4, 5, 6, 8, 9, 10, 11, 12, 13, 14],[0, 1, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]),
 ((2, 1, 2),5,0):([0, 1, 2, 4, 5, 7],[0, 1, 2, 3, 4, 5, 6, 7, 8, 9]),
 ((2, 1, 3),5,0):([0, 1, 2, 4, 5, 6],[0, 1, 2, 3, 4, 5, 6, 7, 8, 9]),
 ((2, 2, 2),5,0):([0, 1, 2, 4, 5, 6, 7],[0, 1, 3, 4, 5, 6, 7, 8, 9]),
 ((2, 2, 3),5,0):([0, 1, 2, 4, 5, 6],[0, 1, 2, 3, 4, 5, 6, 7, 8, 9]),
 ((2, 3, 2),5,0):([0, 1, 2, 3, 5, 6, 7, 8],[0, 1, 2, 3, 4, 5, 6, 7, 8, 9]),
 ((2, 3, 3),5,0):([0, 1, 3, 4, 5],[0, 1, 2, 3, 4, 5, 6, 7, 8, 9]),
 ((3, 0, 1),5,0):([1, 3, 4, 5],[0, 1, 2, 3, 4, 5, 6, 7, 8, 9]),
 ((3, 0, 2),5,0):([0, 1, 3, 5, 6, 7],[0, 1, 2, 3, 4, 5, 6, 7, 8, 9]),
 ((3, 0, 3),5,0):([0, 1, 3, 5, 6],[0, 1, 2, 3, 4, 5, 6, 7, 8, 9]),
 ((3, 1, 0),5,0):([0, 2, 3, 4, 5, 6],[0, 1, 2, 3, 4, 5, 6, 7, 8, 9]),
 ((3, 1, 1),5,0):([0, 2, 3, 4, 5, 6],[0, 1, 2, 3, 4, 5, 6, 7, 8, 9]),
 ((3, 1, 2),5,0):([0, 1, 2, 4, 5, 6, 7, 8],[0, 1, 2, 3, 4, 5, 6, 7, 8, 9]),
 ((3, 1, 3),5,0):([0, 1, 2, 4, 5, 6, 7],[0, 1, 2, 3, 4, 5, 6, 7, 8, 9]),
 ((3, 2, 0),7,0):([0, 1, 2, 4, 5, 6, 7, 8],[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]),
 ((3, 2, 1),5,2):([0, 1, 2, 4, 5, 6],[0, 1, 2, 3, 4, 5, 6, 7, 8, 9]),
 ((3, 2, 2),5,0):([0, 1, 3, 4, 5, 6, 7, 8, 9, 10],[0, 1, 2, 3, 4, 5, 6, 7, 8, 9]),
 ((3, 2, 3),5,0):([0, 1, 3, 4, 5, 6, 7, 8, 9],[0, 1, 2, 3, 4, 5, 6, 7, 8, 9]),
 ((3, 3, 0),5,0):([0, 2, 3],[0, 1, 2, 3, 4, 5, 6, 7, 8, 9]),
 ((3, 3, 1),5,0):([0, 2],[0, 1, 2, 3, 4, 5, 6, 7, 8, 9]),
 ((3, 3, 2),5,0):([0, 1, 2, 3, 4, 6, 7, 8, 9, 10],[0, 1, 2, 3, 4, 5, 6, 7, 8, 9]),
 ((3, 3, 3),5,0):([0, 1, 2, 3, 4, 6, 7, 8, 9],[0, 1, 2, 3, 4, 5, 6, 7, 8, 9]),
 ((0, 2, 2),5,0):([0, 2, 4, 5, 6, 7, 8],[1, 2, 3, 4, 5, 8, 9]),
 ((1, 1, 0),6,0):([0, 2, 3, 4, 6, 7, 8, 9, 10, 11, 13],[0, 1, 4, 5, 6, 7, 8, 9, 10, 11]),
 ((3, 0, 0),5,0):([1, 3, 4, 6],[0, 1, 2, 3, 4, 5, 6, 7, 8, 9]),
}

# All19 negative-curvature fibres.
results=[]
for cw in product(range(4),repeat=3):
 if sum(x.bit_count()for x in cw)>2:continue
 found=False
 for N in range(5,19):
  slots=[(k,j)for k in range(N)for j in range(4)];active=[(k,j)for k in range(N)for j in(0,k%3+1)];cols=[slots.index(x)for x in active]
  quiet=[]
  for k in range(N):
   others=[j for j in(1,2,3)if j!=k%3+1]
   quiet.extend((k,j)for bit,j in enumerate(others)if cw[k%3]>>bit&1)
  if N+4+len(quiet)>=2*N:continue
  def gap(k,i):return s.Matrix(1,4*N,[(J[i,j]if t==k else 0)-(G[i,j]if t>=k else 0)for t,j in slots])
  cap=s.Matrix([[int(i==j)for k,j in slots]for i in range(4)])
  M=s.Matrix.vstack(cap,*[gap(k,k%3+1)for k in range(N)],*[gap(k,i)for k,i in quiet])[:,cols]
  if M.rank()!=M.rows:continue
  H=s.zeros(2*N)
  for a,(k,i)in enumerate(active):
   if i:continue
   for b,(t,j)in enumerate(active):
    value=(-G[0,j]if t<k else 0)-(J[0,j]if t==k else 0);H[a,b]+=value;H[b,a]+=value
  ns=M.nullspace();witness=None
  for b,v in enumerate(ns):
   Q=(v.T*H*v)[0]/2
   if Q<0:witness=(b,Q);break
  if witness:
   results.append((cw,N,witness[0],witness[1]));found=True;break
assert len(results)==19
assert {cw for cw in product(range(4),repeat=3)if sum(x.bit_count()for x in cw)<=2}-{row[0]for row in results}=={(0,2,2),(1,1,0),(3,0,0)}
print('TOTAL: all19 negative fibres verified; exactly three stated exceptions',flush=True)

# Coverage and exact dual verification of the other41 finite exclusions.
geometric={(0,3,1),(2,2,1),(2,3,0),(2,3,1)}
curved={row[0]for row in results};dual={key[0]for key in BASIS}
assert len(curved)==19 and len(dual)==41 and len(geometric)==4
assert not(curved&dual or curved&geometric or dual&geometric)
assert curved|dual|geometric==set(product(range(4),repeat=3))
for cw,N,phase in BASIS:assert certificate(cw,N,phase)

# Canonical-shape geometry and strict finite promotion for the final four modes.
def contact_matrices(mode,N):
 v=s.Matrix(s.symbols('v:'+str(3+2*N)));E=v[:3,0];eq=[];quiet=[]
 for k in range(N):
  i=k%3+1;q=s.zeros(4,1);q[0]=v[3+2*k];q[i]=v[4+2*k]
  obs=[i]+[j for n,j in enumerate([j for j in (1,2,3) if j!=i]) if mode[k%3]>>n&1]
  gap=J[1:4,:]*q-E
  eq.extend(gap[j-1] for j in obs)
  quiet.extend(gap[j-1] for j in (1,2,3) if j not in obs)
  E=E-G[1:4,:]*q
 return s.Matrix(eq).jacobian(v),s.Matrix(quiet).jacobian(v),E.jacobian(v)
weights={
 (0,3,1):[s.Rational(7,6),s.Rational(21,8),s.Rational(1753865,646464),s.Rational(556012,564213),s.Rational(556012,430495),s.Rational(229,378)],
 (2,3,0):[s.Rational(1728,3887),s.Rational(1211431788,306407725),s.Rational(20412,8671),s.Rational(108,169),s.Rational(567,229),s.Rational(20979,26335)]}
aa=s.Matrix([s.Rational(26,21),1,s.Rational(50,63),1,s.Rational(52,63),1])
expected=s.Matrix([-s.Rational(52,7),s.Rational(52,7),s.Rational(52,7),*aa,*(aa/2)])
for mode in [(0,3,1),(2,3,0),(2,3,1)]:
 M,R,_=contact_matrices(mode,6)
 if mode in weights:
  ns=s.Matrix.hstack(*M.nullspace());w=s.Matrix(weights[mode])
  assert M.rank()==12 and all(t>0 for t in w)
  assert w.T*R*ns==s.zeros(1,ns.cols)
 else:
  assert M.rank()==14
  assert M[:,[j for j in range(15) if j!=4]].det()==-s.Rational(179085920,583443)
 A=M.col_join(R);assert A.rank()==14 and A*expected==s.zeros(A.rows,1)
M,R,E=contact_matrices((2,2,1),3);B=M[:,:3];A=M[:,3:]
assert A.det()==s.Rational(781625,9261)
U=-A.inv()*B;T=E[:,:3]+E[:,3:]*U
x=s.symbols('x');assert s.factor(T.charpoly(x).as_expr())==(2*x-1)*(60125*x*x-158113*x+39776)/120250
vc=s.Matrix([-1,1,1]);ell=s.Matrix([[-573509,-6114,-470398]])/96997
alpha=s.Matrix([s.Rational(4046202563,3103904000),s.Rational(1,100),s.Rational(1,100),s.Rational(32037834073,37246848000),s.Rational(1,100),s.Rational(183562514591,37246848000)])
assert T*vc==vc/2 and ell*T==ell/2 and (ell*vc)[0]==1
assert alpha.T*U==ell and all(t>0 for t in alpha)
assert U.T[:,[0,3,5]].det()==-s.Rational(28224,156325)
poly=lambda x:60125*x*x-158113*x+39776
assert poly(s.Rational(1,4))>0 and poly(s.Rational(1,2))<0 and poly(1)<0
assert U*vc/(U*vc)[1]==aa
# Reconstruct the finite promotion with actual Gamma entrance-cap rows.
word=(1,2,3,1,2);slots=[(k,j) for k in range(5) for j in range(4)]
active=[(k,j) for k,i in enumerate(word) for j in (0,i)];promoted=[(2,2),(3,2),(4,3)]
quiet=[(k,j) for k,i in enumerate(word) for j in (1,2,3) if j!=i]
closed=[q for q in quiet if q not in promoted]
def gaprow(k,i):return s.Matrix(1,20,[(J[i,j] if t==k else 0)-(G[i,j] if t>=k else 0) for t,j in slots])
cap=s.Matrix([[G[i,j] for k,j in slots] for i in range(4)])
rows=s.Matrix.vstack(cap,*[gaprow(k,i) for k,i in enumerate(word)],*[gaprow(*q) for q in promoted])
cols=[slots.index(q) for q in active+promoted];M=rows[:,cols]
assert M[:,:12].det()==s.Rational(1144740850,64827)
vsmall=M.nullspace()[0];vsmall/=vsmall[-1];v=s.zeros(20,1)
for col,t in zip(cols,vsmall):v[col]=t
assert all(v[slots.index(q)]>0 for q in promoted)
assert all((gaprow(*q)*v)[0]<0 for q in closed)
a3=[s.Matrix([s.Rational(26,21),1,0,0]),s.Matrix([s.Rational(50,63),0,1,0]),s.Matrix([s.Rational(52,63),0,0,1])]
av=a3+[a/2 for a in a3[:2]];f=s.Matrix([s.Rational(40,7),2,2,2]);C=0
for k in range(5):
 b=v[4*k:4*k+4,0];tail=sum([v[4*t:4*t+4,0] for t in range(k,5)],s.zeros(4,1))
 C+=b[0]*(G.row(0).dot(f)-J.row(0).dot(av[k]))+av[k][0]*(G.row(0).dot(tail)-J.row(0).dot(b));f-=av[k]
assert s.factor(C)==-s.Rational(6814784809,5151333825)
print('PASS: three six-date contact cones; positive-covector221 dynamics; strict finite promotion and negative derivative.')

print('PASS: all64 contact modes partitioned; all rational rank, curvature, dual and geometric certificates verified.')

# Arbitrary, nonperiodic quiet-contact sets on nine cyclic dates.
from itertools import combinations
import sympy as s
R=s.Rational
G=s.Matrix([[0,1,1,1],[-2,0,1,1],[2,-1,0,-1],[2,-1,-1,0]])
J=s.Matrix([[0,-1,-1,-1],[-6,0,-R(4,21),R(37,63)],
            [R(15,2),-R(13,7),0,-R(115,63)],
            [R(13,2),-R(13,21),R(50,63),0]])
assert G.det()==6
def data(N,phase):
    word=[(phase+k)%3+1 for k in range(N)]
    slots=[(k,j) for k in range(N) for j in (0,word[k])]
    def gap(k,i):
        return s.Matrix(1,2*N,[(J[i,j] if t==k else 0)
                    -(G[i,j] if t>=k else 0) for t,j in slots])
    cap=s.Matrix([[int(i==j) for k,j in slots] for i in range(4)])
    M=s.Matrix.vstack(cap,*[gap(k,word[k]) for k in range(N)])
    B=s.Matrix.hstack(*M.nullspace()); H=s.zeros(2*N)
    for a,(k,i) in enumerate(slots):
        if i: continue
        for b,(t,j) in enumerate(slots):
            v=(-G[0,j] if t<k else 0)-(J[0,j] if t==k else 0)
            H[a,b]+=v; H[b,a]+=v
    return word,M,B,H,gap
selected=[(0,2,3),(0,1,3),(0,2,3)]
expected=[[-R(7,128),R(7607,156816),-R(34643,20072448)],
          [-R(276,847),R(55040,617463),-R(7033837,232440516)],
          [-R(64,207),R(41135,156816),-R(123380,2028807)]]
five=[-R(7,256),-R(138,847),-R(32,207)]
for phase in range(3):
    word,M,B,H,gap=data(9,phase)
    assert M.shape==(13,18) and M.rank()==13 and B.shape==(18,5)
    F=B.T*H*B; inds=list(selected[phase]); F3=F[inds,inds]
    minors=[s.factor(F3[:k,:k].det()) for k in (1,2,3)]
    assert minors==expected[phase]
    assert all((-1)**k*minors[k-1]>0 for k in (1,2,3))
    quiet=[(k,j) for k in range(9) for j in (1,2,3) if j!=word[k]]
    Q=s.Matrix.vstack(*[gap(k,i) for k,i in quiet])*B
    assert all(Q[a,:]!=s.zeros(1,5) for a in range(18))
    bad=[]
    for a,b in combinations(range(18),2):
        rank=Q[[a,b],:].rank()
        assert rank==(1 if (a,b) in ((0,1),(16,17)) else 2)
        if rank<2: bad.append((a,b))
    assert bad==[(0,1),(16,17)]
    _,M5,B5,H5,_=data(5,phase)
    assert M5.rank()==9 and B5.shape==(10,1)
    assert (B5.T*H5*B5)[0]/2==five[phase]<0
    print('PASS phase',phase+1,'negative3 minors',minors,
          'only rank exceptions',bad,'guarded5',five[phase])
print('PASS: every phase, every <=2-contact pattern, arbitrary amplitudes.')
```
