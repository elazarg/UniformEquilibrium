# Compact all-END minima have accumulating interior cap contacts or an isolated finite END

## Exact statement

This is ordinary mathematics, not a Lean-checked theorem.

Let I={0,1,2,3}. For every nonempty coalition T subset I, let Z_i(T) be a
finite real native reward, with Z_i({i})=0. Live and all-Never rewards are
zero. Each owner privately and independently samples one complete stopping
law on the natural dates together with a separate Never label. The first
finite tied coalition absorbs. An unrestricted unilateral deviator may
replace its entire law.

For an actual profile P let U_i be prescribed terminal payoff, B_i the
supremum over all finite pure deadlines and Never, e_i its literal Never
response, and N_i its ORIGINAL marginal Never probability. Define

    D_Z=sum_i(B_i-U_i), nu=product_i N_i,
    C=closure{(U(P),B(P),e(P),N(P)):P actual},
    A=inf{D_Z(P):P actual,nu(P)=0}.

The closure is Euclidean. Suppose A>0. Let M>=1 bound all native rewards.
Put Gamma_ii=0 and Gamma_ij=Z_i({j}) for i!=j. Assume Gamma is invertible,
every off-diagonal entry is nonzero, and v=Gamma^-1 e_h is strictly positive
for some coordinate unit vector e_h.

The native data produce fixed positive recipient weights theta and t0>0,
explicitly in Section 1. For every 0<t<t0 set rho=t sum_i theta_i and let X
be ANY global minimum on C of the SAME original full-SUM objective

    F=sum_i theta_i(B_i-U_i)+rho nu.

Assume X is all-END: B_i(X)=e_i(X) for every i. Choose any marked ordered
representation of X constructed in Section 2 from an actual realizing
sequence. It consists of a compact ordered finite-test set T subset [0,c],
c=max T, independent physical laws q_i on T together with separate Never,
and q_i({c})=0. An owner i is cofinal if

    q_i((u,c))>0 for every real u<c.

An interior cap contact is x in T minus {c} whose pure finite query attains
some owner's complete native cap. Native Never is not interior.

**Theorem.** The finite endpoint satisfies c>0, and at least one of the
following alternatives holds:

* For every a<c there is an interior cap contact x in T with a<x<c.
* No owner is cofinal. Equivalently c is isolated in T; the original finite
  mixture has a LAST positive atom, whose latent interval ends at c.

More precisely, if at least TWO owners are cofinal, interior contacts
accumulate at c by Sections 7-8. If exactly ONE is cofinal, they accumulate
by Section 9. The equivalence in the second alternative is proved from the
canonical mixture geometry, rather than assumed for an arbitrary abstract
clock. The theorem does not consume the isolated-END last-atom case.
No actual natural-date realization of X is required or inferred.

## Conjecture-facing change and strategic inputs

The named live obligation addressed here is consumption of the compact
all-END global full-SUM source while retaining its original Never masses
and every unilateral response. This theorem strictly excludes its entire
END-separated-contact mode with at least two physically cofinal owners,
including nonatomic clocks and compact minima not attained by actual laws.
It does not merely verify supplied local derivatives: the marked clock,
legal comparison profiles, complete cap envelope, timing direction, normal
multipliers and negative directions are all produced below.

The incoming strategic premise is an all-END global minimum for the fixed
objective at the produced prices. This theorem does not produce that
all-END property. The assertion is a source-mode exclusion, applicable
where an incoming source theorem supplies this minimum for these same
prices; it is not a new raw-table equilibrium-existence criterion. In
particular no compatibility with an arbitrary positive weight box is
asserted. Global minimization on C is an ordinary compact minimization,
but nonemptiness of its all-END subset is an explicit premise.

No actual calendar, public randomizer, repeated controller, minimizing
tail, prescribed cap action, endpoint rank assumption, timing witness or
PSD multiplier is an input. The finite reward data produce the fixed prices
and a uniform floor for each ORIGINAL N_i. The surviving obligations are
consumption of accumulating interior contacts and the isolated-END
last-atom case. The latter is exactly the zero-cofinal case for this
canonical representation, rather than an additional attainment branch.
The theorem does not settle Fin4 or the finite-quitting conjecture.

## 1. Fixed prices and the original-Never floor

For j!=h put w^j=Gamma^-1 e_j and define

    L_j=max_i |w_i^j|/v_i,
    lambda_j=1/[2(1+L_j)], lambda=min_(j!=h) lambda_j,
    c0=(A/(28M))^4.

Thus v plus or minus lambda_j w^j is strictly positive coordinatewise.
Since each debt is at most 2M and absorbing profiles exist, A<=8M, hence
0<c0<1.

Choose z_j in (1,2), j!=h, so that every one of the three discrepancies
z_j Gamma_jk-z_k Gamma_kj for distinct j,k!=h is nonzero. This has a finite
producer: use four distinct interior values in (1,2) for each coordinate.
Each nonzero linear form vanishes at at most 4^2 of the 4^3 grid points,
so the union of the three zero sets misses a point. Let delta>0 be the
least absolute discrepancy at the selected point. Set

    epsilon=min(c0 lambda/4, c0 lambda delta/(8M),
                min_(j!=h) c0 |Gamma_jh|/(8M)),
    theta_h=3epsilon/4, theta_j=z_j for j!=h,
    Theta=sum_i theta_i, t0=epsilon A/32.

All choices precede t and X. They give theta_min>=epsilon/2 and Theta<=8.

Moving the smallest original Never mass n of an actual profile to one
finite date forces absorption. Each of four prescribed payoffs and three
opponent caps changes by at most 2Mn; the mover's cap is unchanged because
it depends only on opponents. The estimate is uniform over whole-law
responses. Since n<=nu^(1/4),

    A<=D_Z+14M nu^(1/4).                              (1)

This extends to C by continuity. All debts remain nonnegative on C. At a
global minimum, comparison with AllNever gives F<=rho=tTheta, hence

    D_Z<=rho/theta_min<=16t/epsilon<A/2.

Consequently nu>=c0, and EACH ORIGINAL N_i>=c0. These are original Never
masses; finite probability escaping to large dates is not relabeled Never.

The objective really is the original SUM debt of one fixed raised table
R_i(S)=theta_i[Z_i(S)+t], with live/Never still zero. Native late finite
queries converge to e_i because own singleton is zero, so finite queries
already determine B_i. A finite raised query adds exactly theta_i t and
its late limit dominates raised Never. Thus, on actual profiles and C,

    B_i^R=theta_i(B_i+t),
    U_i^R=theta_i[U_i+t(1-nu)], sum_i(B_i^R-U_i^R)=F.   (2)

This continuous map takes C ONTO the raised payoff/cap carrier. Inclusion
follows by applying it to an actual realizing sequence. Conversely every
raised carrier point has an actual realizing sequence; a subsequence of
its bounded augmented native tuples converges in C, and (2) gives that
raised point. Thus a global F minimum is a global original raised SUM-debt
minimum. No maximum-debt objective or observer-only optimization is substituted.

Write mu=min_C F. It is strictly positive: if F=0, nonnegative debts and
rho>0 force D_Z=nu=0, contradicting (1). Choose M_R>0 bounding the fixed
raised rewards. The checked theorem
`positive_minimum_fourPlayer_allOwner_quadraticMargins` in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPreemptedOwnerQuadraticMargin.lean`
applies to the raised payoff/cap image: it is in that carrier, globally
minimizes its SUM debt, has four owners and positive minimum mu, and its
rewards are bounded by M_R. Its cap inequality gives

    B_i^R-R_i({i})>=mu+mu^2/(8M_R)>0.

By (2) the left side is theta_i B_i. Hence every native B_i(X)>0.
An all-Never representation has e_i=0, so cannot represent the all-END X.
Its canonical mixture therefore has positive finite mass c>0.

## 2. The marked ordered representation and all original coordinates

We prove the representation needed here, including its kernel geometry.
First, finite laws are dense for every coordinate (U,B,e,N). Censor each
law's finite mass after K to Never. The moved masses tend to zero. Coupling
bounds prescribed payoffs and every unilateral pure or mixed response
uniformly by 2M times the relevant moved masses. Supremum caps therefore
converge, as do e and original N. Thus X has a finite actual realizing
sequence P^n.

Let mu_n be the average of the four laws of P^n. Give each finite date,
followed by Never, a consecutive interval in [0,1] of length its mu_n
mass. Omit zero-length intervals. Let pi_n collapse each finite interval
to its literal natural date, and send the final interval (c_n,1) to Never.
The density r_i^n of owner i in this chart is constant on each interval,
with

    0<=r_i^n<=4, sum_i r_i^n=4 almost everywhere, int r_i^n=1.

Take a common weak-* subsequence r_i^n -> r_i in L-infinity; L1[0,1] is
separable, so the bounded ball is weak-* sequentially compact. The same
bounds and integral identities hold for r_i. Pass also to c_n->c.

Let E_n be the atom-interval endpoints, including 0,c_n,1. Each finite pure
response date a has location mu_n({b:b<a})+mu_n({a})/2. The set T_n of
these locations is finite: all dates after the last finite support have
location c_n. Native Never is a separate label, never this last tester.
Pass to common Hausdorff limits E_n->E and T_n->T. Then T is a nonempty
compact subset of [0,c], with c=max T.

Each component J=(a,b) of [0,c] outside E comes from one original atom
interval J_n=(a_n,b_n) with endpoints tending to a,b. Indeed a compact
subinterval of J eventually has no endpoint and lies in one atom; the
Hausdorff limit forces its endpoints to those of J. Its unique retained
test is the midpoint m=(a+b)/2, and T intersects J exactly at m. Weak-*
convergence shows r_i is constant almost everywhere on J: compare its
integrals on any two interior subintervals, where r_i^n has the same
constant value, then exhaust J. The same argument applies on (c,1).

The part of E outside T is null. Each component of the complement of T
contains at most one E point, apart from harmless endpoints outside [0,c]:
two such points would force an original atom midpoint between nearby
approximating endpoints, away from T. There are only countably many
complement components.

Define pi almost everywhere by collapsing each J to its midpoint, leaving
E intersect [0,c] fixed, and sending (c,1) to separate Never. Put

    q_i=pi_*(r_i dx), mu=pi_*dx.

The four latent coordinates are sampled independently. Since sum r_i=4,
mu is the physical mixture. The only positive finite mu atoms are retained
midpoints, isolated in T. Every other finite point has zero mu mass.
In particular q_i({c})=0.

For every first coalition S, including all-Never, its indicator K_S^n on
the independent latent product cube converges almost everywhere and in L1
to the pi-kernel K_S. Exclude component endpoints, c, and equality of any
two independent Lebesgue coordinates. Two remaining finite coordinates
are either in the same component J and eventually in the same old atom,
or separated by a limiting endpoint and eventually in correctly ordered
different atoms. Never membership stabilizes. These cases prove the claim.

Products of the bounded densities converge weak-* on product cubes. For
rectangle indicators the assertion is the product of marginal weak-*
identities. Finite linear combinations of rectangle indicators are dense
in L1, while the products are uniformly bounded. For any of the above
kernels, split the integral difference as

    int(K_S^n-K_S) product r_i^n
                  +int K_S(product r_i^n-product r_i).

The first term tends to zero by L1 kernel convergence and boundedness;
the second uses a FIXED kernel and product weak-* convergence. Hence every
coalition probability and prescribed payoff converges. The separate Never
query gives e. Also

    N_i(P^n)=int_(c_n,1) r_i^n dx -> int_(c,1) r_i dx=N_i(q).

The moving endpoints contribute at most 4|c_n-c|, and the remaining term
is weak-* convergence against the fixed interval (c,1). This retains each
ORIGINAL marginal N_i, not merely their product.

Here is the complete-response assertion. For any x_n in T_n with x_n->x
in T, the opponent payoff kernel of that pure response converges almost
everywhere and in L1 to the pi-query kernel at x. If x is a retained
midpoint, its isolation forces x_n eventually to be the corresponding
old atom midpoint, retaining its exact ties. Otherwise x is an atomless
cut. Adjacent retained atoms have midpoints strictly on their proper
sides, and all other comparisons stabilize off null sets. The same
argument applies at c; Never remains separate. The opponent product
argument above now gives convergence of every moving response value.

The limiting pure-response value is continuous on T: its positive atoms
are isolated and all other cuts have zero opponent mass. With Never as
an isolated extra label, every cap is attained. Choose maximizing actual
queries and pass to a convergent location subsequence to obtain the upper
cap limit; approximate any fixed limiting query by T_n to obtain the
lower cap limit. Therefore the represented full tuple is exactly X.

## 3. Fixed bounded-density comparison profiles stay in the same carrier

For ANY fixed bounded nonnegative measurable f_i on [0,1], with int f_i=1,
set

    q_i^f=pi_*(f_i dx), P_i^{n,f}=(pi_n)_*(f_i dx).

These are independent laws; P^{n,f} is an actual finite profile on the
OLD natural calendar. On an old atom interval J_n(a), its mass at a is
exactly int_(J_n(a)) f_i dx. This formula remains legal if f_i is not
constant on that interval.

All product densities are fixed and bounded, so the kernel convergence
in Section 2 gives prescribed payoffs and the separate Never response.
Furthermore

    N_i(P^{n,f})=int_(c_n,1)f_i dx -> int_(c,1)f_i dx.

For caps choose arbitrary maximizing actual queries, extract a location
limit in T or take separate Never, and apply the moving-query convergence.
This proves limsup B_i(P^{n,f})<=B_i(q^f). Approximation by T_n of every
fixed T-query gives the reverse liminf inequality. Query continuity still
holds because q_i^f has no atom at any non-atomic mu cut. Thus the ENTIRE
represented tuple for q^f belongs to the SAME C with its FULL query set.

The assertion holds for each fixed choice of f. No common actual realization
of all counterfactual variations is needed for global minimality on C.
We never recompress the new prescribed support or insert a Dirac atom at
an old atomless point. Boundedness is required separately for each fixed
variation, with no uniform bound as its chosen blocks approach c.

## 4. Legal block controls and the exact local cap envelope

Suppose, toward a contradiction, that every interior contact is at or
before a0<c. Let S be the cofinal owners. Each owner outside S has zero
physical finite mass above some cut; enlarge a0 to exceed all these cuts.

For every finite word of labels in S, cofinality supplies disjoint strictly
ordered compact clock blocks after a0, with positive physical mass for the
specified label, all ending below c. To see this, select a positive-mass
compact subinterval after the previous endpoint, with non-atomic mixture
boundaries; repeat finitely many times. Such boundaries can be chosen
because the set of mixture atoms is countable. These blocks may be chosen
arbitrarily close to c and may contain atoms, diffuse mass, or both.

For a block I of owner j let eta be its conditional probability of stopping
in I given survival to its left boundary. It satisfies 0<eta<1 because
N_j>0. Preserve the within-block conditional law and the conditional law
after the block, including original Never. Replacing eta by eta+z multiplies
mass in I by (eta+z)/eta and mass after I by (1-eta-z)/(1-eta); earlier mass
is unchanged. Both signs of sufficiently small z are legal. Compose finitely
many such conditional changes chronologically. They have bounded densities
relative to the original q_j and hence relative to mu.

For any missing owner j outside S, choose an old positive MIXTURE block
above the cut and below c. A one-sided conditional hazard y>=0 inserts
its normalized old mixture law there, removing the same conditional mass
from that owner's original Never. Its baseline hazard is zero. This is
legal because N_j>0 and the fixed block has positive mu mass; its inserted
law has bounded density 1/mu(I) relative to mu. It inserts no new mixture
atom. There is always such a late block when S is nonempty. Choose one
for each missing owner. All comparison tuples belong to C by Section 3.

The proof will also use finite transfers of mass between an owner's own
positive blocks or atoms, leaving its law outside their compact union
unchanged. These are two-sided bounded-density controls. Finitely many
hazards and transfers can be combined in a smooth finite parameter family:
first make each conditional hazard change, then the additive zero-total
transfers on its fixed positive blocks. Small two-sided transfer parameters
preserve positivity, because their densities are constant multiples of
positive source restrictions; all one-sided inserted components remain
nonnegative. Every law has a bounded density relative to mu and all native
U,e,N and their product are smooth finite polynomials in these parameters.

Let C0 be the set of owners with an interior cap contact, and put
b_i=B_i(X)=e_i(X). On an open neighborhood of the two-sided parameters x
and a relative one-sided neighborhood y>=0, the COMPLETE cap formula is

    B_i=max(b_i,e_i(x,y)) for i in C0,
    B_i=e_i(x,y) for i outside C0.                     (CAP)

For queries before the first changed block, response values are unchanged:
each opponent's earlier law and total survival past the query are fixed.
Thus all old contacts remain b_i. For owners outside C0, compactness gives
a strict uniform gap over this earlier compact set. On the compact query
window from first to last changed block there are no contacts; continuity
and compactness give a strict gap, preserved by uniform payoff coupling
for small changes. Above the last changed block, conditional suffix laws
are fixed. The END-minus-query difference equals its original conditional
suffix gap multiplied by the NEW positive opponent survival through the
changed prefix, so its sign is preserved. The finite END c itself equals
the Never response since q_i({c})=0 and own singleton is zero. This proves
(CAP) for every old query, including the infinite suffix and unused tests.

## 5. Common finite normal multipliers and their late derivative limits

For gamma_i in [0,1] on C0 and gamma_i=1 outside C0 put

    L_gamma=sum_i theta_i gamma_i e_i-sum_i theta_i U_i+rho nu.

The directional derivative of F is the support function of this compact
convex gradient box. Local minimality and finite-dimensional separation
give a common normal multiplier satisfying

    D_x L_gamma=0, D_y L_gamma>=0.                    (KKT)

Indeed if the gradient box missed {zero on x, nonnegative on y}, strict
separation from that closed cone would give a direction with nonnegative
y coordinates and strictly negative maximum derivative. It is a legal
first-order descent, contrary to global minimality on C.

Include a late two-sided block hazard for each owner in S and a late
one-sided insertion for each outside owner. As all blocks approach c,
the original physical finite mass after their first boundary tends to
zero; original N_i stays positive. A hazard's signed-law derivative is
its survival to the block times (normalized finite block law minus the
fixed law after the block). The latter law tends in total variation to
literal Never. Earlier absorption cancels. Bounded rewards give, for a
control of owner j,

    partial_j e_i -> (nu/N_i) Gamma_ij,
    partial_j U_i -> nu Gamma_ij,
    partial_j nu -> -nu.                              (3)

These formulas apply equally to a missing owner's zero hazard: its old
conditional law is exactly Never and its inserted block is finite.
The own-Never derivative is zero, agreeing with Gamma_jj=0.

For an earlier block of owner j and later block of DIFFERENT owner k,
the mixed limits are

    partial_j partial_k U_i/nu -> -Gamma_ik,
    partial_j partial_k e_i/nu -> -Gamma_ik/N_i if i outside {j,k},
    partial_j partial_k e_j=partial_j partial_k e_k=0,
    partial_j partial_k nu/nu -> 1.                    (4)

Expand the two signed laws. The earlier finite singleton cancels and its
occurrence removes the later singleton. All outcomes involving any other
late original finite activity have probability tending to zero. The
error is bounded by a fixed reward multiple of the total finite mass
after the first block, irrespective of block lengths or atomic structure.

For two blocks of the SAME owner j, the mixed signed-law derivative at
baseline is minus survival to the later block divided by (1-eta_earlier),
times (its normalized block law minus its conditional suffix). Since each
late eta tends to zero, the corresponding limits are

    partial_j1 partial_j2 U_i/nu -> -Gamma_ij,
    partial_j1 partial_j2 e_i/nu -> -Gamma_ij/N_i for i!=j,
    partial_j1 partial_j2 e_j=0,
    partial_j1 partial_j2 nu/nu ->1.                   (5)

Each individual hazard has zero pure second derivative, by separate
affinity of the law. These derivative arguments use only finitely many
controls in each family. Extra timing-transfer coordinates need not
satisfy (4)-(5); they will not be used in that calculation.

Choose multipliers for a sequence of late families and pass to a common
convergent subsequence. With ORIGINAL N_i put

    r_i=theta_i(gamma_i/N_i-1), a_i=theta_i+r_i.

The same limiting multiplier gives, from (KKT) and (3),

    r^T Gamma>=rho one^T, with equality on columns in S. (KT)

The inequality at missing owners has the one-sided sign; no stationarity
is asserted at a physical action absent from their source law.

## 6. The fixed prices forbid every effective-price reciprocity pair

Multiplying (KT) by v>0 yields r_h>=rho sum v_i>0. Since gamma_h<=1 and
N_h>=c0, both r_h<epsilon/c0 and a_h<=epsilon/c0. Multiplication by each
positive vector v plus or minus lambda_j w^j gives

    r_h plus or minus lambda_j r_j>0,
    |r_j|<epsilon/(c0 lambda_j)<=epsilon/(c0 lambda) for j!=h.

Thus a_j=z_j+r_j>3/4 for j!=h. For two nonpivot owners, the change of their
fixed price discrepancy is strictly smaller than

    (|Gamma_jk|+|Gamma_kj|)epsilon/(c0 lambda)<=delta/4.

For h,j one has |a_h Gamma_hj|<=|Gamma_jh|/8, while
|a_j Gamma_jh|>3|Gamma_jh|/4. Consequently EVERY distinct pair satisfies

    a_j Gamma_jk != a_k Gamma_kj.                     (UNBAL)

These bounds are uniform over all limiting normal multipliers satisfying
(KT). No sign is assumed for the other r coordinates, and no arbitrary
dual law is selected in advance.

## 7. Two cofinal owners: the exact compact timing direction

Let S={j,k}. Cut at an atomless boundary after every contact and after all
finite physical activity of the two outside owners. Their conditional laws
after this cut are exactly Never. In the conditional two-owner tail put

    f_j=Pr(j finite), f_k=Pr(k finite),
    A_jk=Pr(T_j<T_k), C_jk=Pr(T_j=T_k finite),
    A_kj=Pr(T_k<T_j), L=f_j+f_k-f_j f_k=A_jk+A_kj+C_jk.

Never is ordered after every finite point in these formulas. We produce
a legal compactly supported two-sided direction with

    d f_j=d f_k=d C_jk=0, d A_jk!=0.                  (DIR)

Suppose first the set of COMMON positive atoms is not cofinal. Enlarge
the cut so there is no common positive atom afterwards. Then C_jk=0
identically under all reweightings supported on each owner's OWN physical
support. Cofinality provides three strictly ordered compact positive
blocks J_left<K_mid<J_right, labeled j,k,j. Transfer one unit of signed
j mass from its normalized restriction to J_left to its normalized
restriction to J_right. For small parameters of both signs this is legal,
preserves f_j, and changes A_jk strictly negatively: for any x in J_left
and z in J_right,

    Pr(z<T_k)-Pr(x<T_k)<=-Pr(T_k in K_mid)<0.

It preserves C_jk=0 and proves (DIR), including purely nonatomic laws.

Suppose instead common positive atoms are cofinal. Choose one such atom
a after the cut. Write p_j(a),p_k(a)>0 for its conditional masses. There
are only finitely many k atoms with mass at least p_k(a)/2. Choose a
positive j block J strictly after all of them and after some positive k
block strictly above a. Such a block exists by j cofinality. Transfer j
mass from a to its normalized OWN restriction on J. Then

    d_j C_jk=int_J p_k({x}) d(q_j|J)(x)-p_k(a)<-p_k(a)/2<0,
    d_j A_jk<0.

The strict A inequality follows from the intervening positive k block.
Choose similarly a positive k block K after all j atoms of mass at least
p_j(a)/2, and transfer k mass from a to its normalized OWN restriction on K.
Then

    d_k C_jk<-p_j(a)/2<0,
    d_k A_jk=int_K Pr(T_j<x) d(q_k|K)(x)-Pr(T_j<a)>0.

The last strict inequality already follows from the positive j atom at a.
Both transfers preserve finite marginals. Their (dC,dA) vectors have
negative first coordinates and opposite nonzero second signs. Subtract
a positive multiple of one from the other to cancel dC; dA remains
nonzero. This is (DIR).

Every chosen atom or block has positive own mass, every compact transfer
ends below c, and its signed density is bounded relative to that owner's
old law. Thus the direction belongs to a genuine two-sided finite family
from Section 4, not to a formal signed-measure relaxation. No exact curve
of constant tie probability is needed; only its derivative is used.

Include these timing coordinates, dedicated late hazards for j,k, and a
one-sided old-mixture insertion for each missing owner in ONE family.
Take its common multiplier from (KKT). Let n_i be original survival through
the fixed cut and sigma=product_i n_i. For each outside owner n_i=N_i
EXACTLY, because no physical finite activity remains after the cut.
The conditional suffix values are

    e_j=Gamma_jk f_k, e_k=Gamma_kj f_j,
    U_j=Gamma_jk A_kj+Z_j({j,k})C_jk,
    U_k=Gamma_kj A_jk+Z_k({j,k})C_jk,
    U_i=e_i=Gamma_ik L+(Gamma_ij-Gamma_ik)A_jk
                       +(Z_i({j,k})-Gamma_ik)C_jk for outside i.

The fixed head contributes constants, factor sigma on U, and factor
sigma/n_i on e. Along (DIR), persistent e_j,e_k and nu have derivative
zero. Stationarity divided by sigma dA_jk therefore yields the EXACT
finite-family identity

    0=sum_out r_i(Gamma_ij-Gamma_ik)
                         +theta_j Gamma_jk-theta_k Gamma_kj,             (6)
    r_i=theta_i(gamma_i/N_i-1) for outside i.

The equality n_i=N_i makes these outside coefficients exact, before
any endpoint limit. No approximation of survival by Never was made.

Choose such families arbitrarily close to c, and take a common multiplier
subsequence. Their dedicated controls give (KT) with equality on j,k.
Subtracting those two column equalities gives

    sum_out r_i(Gamma_ij-Gamma_ik)=r_j Gamma_jk-r_k Gamma_kj.

Together with (6), this forces a_j Gamma_jk=a_k Gamma_kj, contrary to
(UNBAL). This excludes every two-cofinal END-separated source.

## 8. Three or four cofinal owners: a finite quadratic contradiction

Choose j,k in S. Cofinality supplies twenty strictly ordered positive
blocks in the word (j,k,j,k) repeated FIVE times. Add one late positive
block hazard for every remaining owner in S and a late one-sided insertion
for every missing owner. All blocks approach c along a sequence. Write x
for interior hazards, y>=0 for inserted zero hazards. For one finite family
let

    g_gamma=D L_gamma, H_gamma=D_x^2 L_gamma,
    Lambda={gamma in the cap box:g_gamma,x=0,g_gamma,y>=0}.

This is nonempty compact convex by (KKT). One positive column per cofinal
owner in D_x e_C0 tends to diag_(C0)(nu/N_i) Gamma_[C0,S]. Invertibility
of Gamma gives independent rows for Gamma_[C0,I]; deleting 4-|S| columns
lowers its rank by at most 4-|S|. Hence sufficiently late finite families
satisfy

    rank D_x e_C0>=|C0|-(4-|S|), dim Lambda<=4-|S|<=1.

The normal set is a point or a closed segment. This does not assume a
regular level manifold or full rank of all contact constraints.

Put K=ker D_x e_C0. For d in K all vertex branches of the finite cap maximum
have zero first derivative on d. Indeed their gradient differences are
weighted END derivatives vanishing on K, and one normal multiplier has
zero interior gradient. For arbitrary w_x and w_y>=0 the quadratic path

    x(tau)=tau d+(tau^2/2)w_x, y(tau)=(tau^2/2)w_y

is legal for small tau. Taylor expansion of the finite maximum and local
minimality imply

    max_(gamma vertex)[d^T H_gamma d+g_gamma dot w]>=0 for every such w.  (7)

To extract its exact content, minimize z subject to the finitely many
inequalities z>=d^T H_v d+g_v,x dot w_x+g_v,y dot w_y, with w_x free and
w_y>=0. Its dual has p_v>=0, sum p_v=1, sum p_v g_v,x=0,
sum p_v g_v,y>=0 and objective sum p_v d^T H_v d. Gradient and Hessian
are affine in gamma, so the dual is precisely
max_(gamma in Lambda) d^T H_gamma d. It is feasible by (KKT), and finite
linear-programming strong duality applies. Equation (7) gives

    max_(gamma in Lambda) d^T H_gamma d>=0 for every d in K.             (8)

For completeness, the following two-form fact turns (8) into ONE multiplier.
For two homogeneous real quadratic forms q0,q1, the joint range
Q(d)=(q0(d),q1(d)) is a convex cone. To prove additivity, for x,y set
z=x cos s+y sin s and w=-x sin s+y cos s. Then Q(z)+Q(w)=Q(x)+Q(y)=p.
If p!=0, det(Q(z),p) changes sign after s increases by pi/2, so it vanishes
somewhere. At that point Q(z)=alpha p and Q(w)=(1-alpha)p. At least one
coefficient is positive; rescaling the corresponding vector realizes p.
If p=0 use d=0. Nonnegative scaling is immediate. Thus the range is convex.
If max(q0,q1)>=0 everywhere, this cone avoids the open negative quadrant.
Separation supplies nonnegative coefficients, not both zero, whose weighted
quadratic form is nonnegative. After normalization it is a convex
combination of q0,q1.

Apply this fact to the endpoint Hessians of the segment Lambda restricted
to K; a singleton needs no argument. There exists gamma_* in Lambda with

    H_gamma_* positive semidefinite on K.                              (9)

Choose these finite multipliers and take a convergent subsequence as all
blocks approach c. Its limit satisfies (KT), so the pair j,k has
D0=a_j Gamma_jk-a_k Gamma_kj!=0 by (UNBAL). From (4)-(5), the normalized
mixed Hessian entries of L_gamma_* have limits

    same owner: -sum_i r_i Gamma_ij+rho=0,
    earlier j, later k: theta_j Gamma_jk-sum_out r_i Gamma_ik+rho
                         =a_j Gamma_jk.                              (10)

For the second equality use stationarity at cofinal column k in (KT).
Individual pure hazard second derivatives are zero exactly.

Inside each chronological chunk, swap its first and second j controls,
and swap its first and second k controls. On these TEN independent vectors,
the limiting Hessian is block diagonal with FIVE blocks

    [0 D0; D0 0].

Terms between different chunks cancel: all controls of the earlier chunk
precede all controls of the later one, and each swap has coefficient sum
zero. Each block has a negative eigenvalue. By finite-matrix continuity,
for all sufficiently late finite families the Hessian is negative definite
on a five-dimensional subspace; extra coordinates are set to zero.

But K has codimension rank D_x e_C0<=|C0|<=4. It meets this negative
five-dimensional subspace nontrivially, contrary to (9). This excludes
both three- and four-cofinal END-separated sources. No convergence of
constraint kernels or bounded inverse of a collapsing Jacobian is used.

## 9. One cofinal owner and the zero-cofinal boundary

If only owner j is cofinal, choose a cut above all physical finite activity
of its opponents. Every query x beyond that cut agrees with Never for j:
it matches every earlier opponent coalition, and on all-opponent-Never
its own singleton pays zero. Thus every such query is a cap contact.
Cofinality of j supplies physical support, hence T-points, arbitrarily
near c from below. Interior contacts therefore accumulate at c.

Suppose now no owner is cofinal. For each i choose u_i<c with
q_i((u_i,c))=0, and set u=max u_i. The physical mixture mu=pi_*dx then
satisfies mu((u,c))=0. Enlarge u to be positive if needed; c>0 was proved
in Section 1. Since mu({c})=0, almost every latent x in (u,c) has pi(x)<=u.
Such an x cannot be a fixed point of pi. It must lie in a collapsed
component J=(a,b) of [0,c] outside E with midpoint at or below u.
Any such J meeting (u,c) has a<u<b. Disjoint components permit at most
one of them. It must cover (u,c) up to a null set, so b=c.

Consequently J=(a,c) is the final retained atom interval. Its midpoint
m=(a+c)/2 has positive mixture mass c-a, and T intersects J exactly at m.
There is no T point in (m,c), so c is isolated in T; all owners' finite
physical support is at or before m. Thus m is a LAST positive mixture
atom, with its original latent interval ending at c.

Conversely, if c is isolated in T, a neighborhood (u,c) contains no finite
query and hence no physical mass for any owner, so no owner is cofinal.
This proves the equivalence. A last positive mixture atom need not belong
to every owner; no claim of simultaneous positive physical mass for all
owners is made. Native Never remains a separate label.

If the first alternative of the theorem fails, all interior contacts lie
at or below some a0<c. Sections 7-8 exclude at least two cofinal owners,
and the one-owner argument excludes exactly one. Therefore no owner is
cofinal, giving the second alternative and the asserted global dichotomy.
It is a dichotomy of canonical source modes, with no actual-attainment
alternative. The last-atom mode itself remains open.

## Boundary tests

**The matrix and price conditions are nonvacuous algebraically.** The
hollow singleton matrix

    Gamma=[0 1 1 1; 1 0 1 -2; 1 1 0 -2; 1 1 -2 0]

has determinant 6 and Gamma^-1 e_0=(1/3,1/3,1/3,1/3). All off-diagonal
entries are nonzero. With z_1=6/5,z_2=7/5,z_3=8/5, the nonpivot
reciprocity discrepancies are -1/5,-4,2/5, so delta=1/5. This tests the
finite algebraic producer, not A>0 or existence of a counterexample.

**The nonatomic timing case needs no shared atom.** Give j,k half their
mass uniformly on (0,1) and half at Never. The common finite tie probability
is zero. Transfer one unit of signed j mass from its normalized restriction
to (0,1/4) to its normalized restriction to (3/4,1). For sufficiently small
parameters both signs are legal. The change of A_jk is -3/8, because the
k survival function at finite x is 1-x/2. Finite marginals and tie mass
have derivative zero. Thus the timing producer covers diffuse overlap.

**Cofinal shared atoms give two independent timing vectors.** Put
x_n=1-2^-n and give each of j,k mass 2^(-n-1) at x_n, n>=1, with Never
mass 1/2. At n=1, transferring j mass from x_1 to x_2 has (dC,dA)=
(-1/8,-1/8); the analogous k transfer has (-1/8,1/4). Their difference
has (dC,dA)=(0,-3/8). The same calculation works arbitrarily close to END,
with the corresponding positive geometric masses.

**The old response calendar cannot be recompressed.** For two owners,
let owner 0 put half at date 0 and half at Never; let owner 1 put half
at date 1 and half at Never. Let Z_0({1})=-1,Z_0({0,1})=-2 and own
singleton be zero. Reweight owner 0 to pure Never. Its old date-0 query
still pays zero, so its full cap is zero. Deleting that now-empty date
and moving owner 1's date to new date 0 leaves a current query paying -1
and Never paying -1/2, incorrectly lowering the cap to -1/2. Section 3
keeps every old query.

**Unbounded sequence-dependent chart densities are excluded.** Give both
old laws half their mass uniformly on dates 1,...,n and half at Never.
Concentrate owner 0's finite half at date 1 and owner 1's finite half at
date 2, retaining each Never mass 1/2. The required chart densities grow
like n. Their actual first-coalition probabilities are 1/2 for {0},1/4
for {1}, zero for the tie, and 1/4 for Never. Collapsing both concentrated
finite laws to the same atomless limiting endpoint would instead create
tie mass 1/4. Fixed bounded-density transport does not make that inference.

**Finite END is an unavoidable contact and must be excluded.** At an
all-END source, its empty finite END query pays e_i for every i. Including
c among interior contacts would make the bounded-away-END premise empty.
With all rewards zero and each law half at date 0 and half at Never, the
marked test set has one retained atom and an isolated finite END; no owner
is cofinal and no interior contacts accumulate. This exact boundary test
lies outside the matrix and positive-gap assumptions, and explains why
zero cofinality cannot be discarded by terminology.

**The two-form boundary is real.** On R^2 put
q_r(x)=(u_r dot x)^2-(2/3)|x|^2 for unit lines at angles 0,pi/3,2pi/3.
Their maximum is at least |x|^2/12, because one line is within pi/6 of
any x. Every convex combination has trace -1/3, so none is PSD. Thus the
point-or-segment argument is not extended to a two-dimensional multiplier
polygon; exactly two cofinal owners are handled by their exact timing
identity instead.

## Source correspondence and implementation-overlap audit

The exact target is `quittingUniformEquilibriumPayoffConjecture` in
`UniformEquilibrium/Quitting/Conjecture/Basic.lean`. The terminal semantics
are those of
`not_exists_uniformEquilibriumPayoff_iff_exists_terminalExploitabilityGap`
in `UniformEquilibrium/Quitting/Terminal/ExploitabilityGap.lean` and
`quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
in
`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`.
They identify positive unrestricted terminal exploitability as the negative
semantic endpoint and terminal approximate existence at all errors as the
positive endpoint. The present theorem only narrows a positive-gap source;
it does not supply the all-errors hypothesis of the positive endpoint.

The stopping-law and unrestricted behavioral caps agree by
`quittingStoppingLawCap_behaviorStoppingLaws_eq_continuationBestResponseValue`
and
`quittingStoppingLawCap_eq_continuationBestResponseValue_stoppingLawProfile`
in `UniformEquilibrium/Quitting/Paths/StoppingLawOperationalDistance.lean`.
The same file's `quittingBehaviorStoppingLaws_stoppingLawProfile` returns
every supplied complete law exactly. These facts justify the model and
unilateral agency used here; they do not supply the compact controls.

`quittingTerminalSemanticPair` and `quittingTerminalSemanticCarrier` in
`UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean` retain the
payoff/cap pair and its closure. The augmented carrier C used here ALSO
retains e and every original N. Its marked representation and bounded-
density transport are new ordinary mathematics in Sections 2-3, not fields
already provided by that pair structure.

The full behavioral prefix cap is
`quittingContinuationBestResponseValue_rootThenContinuation_eq_max` in
`UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean`; its arbitrary
prescribed prefix counterpart is
`quittingTerminalPayoff_rootThenContinuation_eq` in
`UniformEquilibrium/ProofView/Concepts/Stochastic/Models/Quitting/RootContinuation.lean`.
These are the semantic prefix identities used in proving (CAP), without
assuming a Nash row. The finite-query/Never limit in (2) is
`quittingTerminalPayoff_update_finiteTime_tendsto_of_profile` in
`UniformEquilibrium/Quitting/Terminal/SingletonJointNeverDebt.lean`, with
zero own singleton removing its extra cylinder term.

The four-player quadratic margin theorem used in Section 1 was also
statically inspected under its exact carrier-membership, global-SUM,
positive-minimum, cardinality and reward-bound hypotheses. It supplies the
non-AllNever fact only; it does not supply the contact dichotomy.

Those declarations and their hypotheses were statically inspected. A
bounded search in the operational stopping-law and root source subtrees
and generic mathematical subtree found no declaration implementing this
bounded-mixture-density compact clock transport, exact two-owner compact
timing consumer, or END-separated compact-source exclusion. Existing
prefix/cap and compact semantic-pair interfaces are reused rather than
counted as new results. No literature theorem is required for the novel
source reduction; finite-dimensional separation, finite LP duality and
the two-form convexity argument are given explicitly above. No new Lean
compilation, unrestricted strategy-class completeness seal, or formalized
adapter/consumer credit is claimed.

## Adapter and consumer

The actual-data adapter takes the finite native table, reward bound M,
positive absorbing SUM infimum A, and raw singleton matrix hypotheses. It
produces the fixed theta,t0 and original-N floor c0 in Section 1. Given a
compact all-END global minimum at those fixed prices, an actual realizing
sequence produces its marked representation with all(U,B,e,N) in Section
2. Every finite comparison used later is pushed through those SAME old
actual calendars by Section 3. Thus every minimum inequality used in the
proof is an inequality at an actual-carrier point, even for a nonrealized
source. No desired timing or curvature conclusion is assumed as a field.

The downstream consumer is the explicit global source dichotomy: among
represented all-END global minima, the END-separated-contact case with
two, three or four cofinal owners is impossible; the one-cofinal case
already has contact accumulation; and zero cofinality is exactly the
isolated-END last-atom case. An incoming all-END source theorem may
therefore pass only an accumulating-interior-contact mode or an
isolated-END last-atom mode onward, with
its original table, weights, objective and Never coordinates retained.
This is a strict mode exclusion, rather than a conditional local verifier
whose test data have not been produced. It supplies no continuation law
solving either surviving mode and no uniform-equilibrium payoff by itself.

## Lean handoff

A suitable primary theorem takes native Fin4 rewards, M, the absorbing
SUM infimum A>0 and the explicit matrix hypotheses. It PRODUCES theta,t0.
For each smaller t, augmented-carrier global minimum X with B=e, and its
marked representation, it concludes the global dichotomy between interior
contact accumulation and an isolated finite END after a last positive
mixture atom. A separate central consumer proves that at least two cofinal
owners imply contact accumulation. The N floor
is derived from the repair estimate, not accepted as an additional source
field. The all-END global-minimum input is explicit and must be supplied
by the incoming source at the SAME prices.

Separate reusable declarations can prove: marked-interval product and
moving-query kernel convergence; transport of fixed bounded latent
densities retaining all e,N and old responses; full-cap stability for
finite two-sided block hazards, own-support transfers and missing-owner
one-sided insertions; cone normal multipliers; late first/mixed signed-law
derivatives; fixed-price unbalance; the exact two-owner timing direction
and coefficient identity; the rank bound and finite quadratic-path LP;
two-real-quadratic-form convexity; and five negative chronological chunks.
Do not use fields asserting legality of the timing direction, existence
of a PSD normal multiplier, a regular endpoint level set, actual calendar
attainment, or cofinality of an owner whose physical mass is absent.

Formalization should reuse the named operational cap and prefix theorems.
Start with the finite algebra and exact rational boundary calculations,
then implement the marked representation and comparison transport before
assembling either consumer. The narrowest relevant module checks should
be run under the repository's serialized Lean queue. No Lean source or
build is part of this mathematical packet.

## Scope and nonclaims

All randomness in actual and comparison profiles is independent and
private; algebraic convex combinations of multipliers are not game
randomizers. Every complete unilateral stopping-law response is retained,
including unused old dates and literal Never. The payoff mode is terminal,
not a finite-horizon or discounted assertion.

The theorem is conditional on the indicated all-END source, but its local
comparison domain and its entire excluded source mode are proved, not
assumed. It covers atomic, nonatomic and nonrealized marked sources. It
does not produce all-END activity for arbitrary prices, turn original
Never into escaped finite probability, realize an infinite natural calendar,
insert atoms at atomless cuts, consume accumulating contacts, eliminate
the isolated-END last-atom case, or establish a Fin4 equilibrium.
