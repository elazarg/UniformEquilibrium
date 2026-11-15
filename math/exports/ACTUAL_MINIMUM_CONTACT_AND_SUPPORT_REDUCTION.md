# Actual all-END minima reduce to contacts and restricted support

## Conjecture-facing change and strategic inputs

This is ordinary mathematics, not a Lean-checked result. It closes the entire
actual no-finite-cap-contact case of full-SUM all-END minimization at every
native table with no reciprocal zero pair in its singleton matrix. This
includes arbitrarily sparse and interleaved calendars. The proof supplies a
new necessary condition on local minima; no matrix inverse or joining-payoff
condition is required. A bounded-contact theorem further forces an exact singleton/price identity
at every all-four-persistent minimum. One fixed price selected in any positive
box excludes that mode for every sufficiently small raise at the SAME table.
A finite construction selects a contact global minimum
from any actual all-END global minimum below its absorbing gap, even when
the singleton matrix has reciprocal zeros.

The strategic input is explicitly an ACTUAL independent complete-law
minimum with positive original Never and all native caps END. These are
cases of the minimum problem, not a claim that its compact minimum is
always realized by one law. The local theorem needs only local optimality
under finite small hazard changes. The selector needs a true global minimum
and its stated strict absorbing-gap bound. The first joint-stage normal
form invokes the existing four-player positive-minimum cap-margin theorem
for this original full-SUM objective; its exact statement is reproduced below.
The bounded-contact obstruction additionally requires only invertibility
of the singleton matrix. Its box application chooses a finite price vector
before the raise and source; the supplied open price box is explicit. No tail optimality, supplied
controller, root selector, uniform rate, observer-debt constraint or public
randomization is assumed. All comparison laws are produced below.

After that price choice, a surviving actual minimum has a bounded finite
support for some owner or unbounded finite cap-contact dates. A contact global minimum
can also be selected with its earliest contact at its first prescribed stage,
where at least two owners have atoms. The packet neither consumes these
contacts nor proves Fin4; nonrealized compact minima remain open. It is a strict
reduction of the actual-minimum obligation, not a new raw reward-table UE
existence class or an actual-attainment theorem.

## Complete actual-source theorem

Let I={0,1,2,3}. A native quitting table Z has own-singleton, live and literal
AllNever rewards zero, with all rewards finite. Owners independently draw
complete stopping laws on natural dates plus a distinct Never point. Every
whole-law unilateral deviation is allowed. For an ACTUAL profile P retain
prescribed payoff U, full behavioral response cap B, Never offer e, and
ORIGINAL marginal Never probabilities N. Put nu=product N_i and

    Gamma_ij=Z_i({j}), Gamma_ii=0,
    F(P)=sum_i theta_i[B_i(P)-U_i(P)]+rho nu(P),
    theta_i>0, rho>0.

Assume N_i(P)>0, B_i(P)=e_i(P) for every i, and P is a local minimum of F
under finite sufficiently small changes of its conditional hazards. In
particular every actual global minimum over the full augmented carrier
satisfies this local hypothesis. An owner is PERSISTENT if its finite
stopping support is unbounded; let S be the set of persistent owners.

**Theorem.** If EVERY finite pure deadline of EVERY owner has value strictly
less than its native cap B_i(P), then

    |S|>=2 and Gamma_jk=0 for all distinct j,k in S.           (T)

Consequently, if no reciprocal pair of singleton entries is simultaneously
zero, P has a FINITE cap contact: some finite deadline of some owner attains
its full native cap. It suffices, in particular, that every off-diagonal
Gamma entry is nonzero.

No genericity, matrix inverse, alpha<1, small rho, simultaneous support date,
joining matrix, control rank, observer-optimality or tail minimum is needed
for(T). The theorem does not apply to a nonrealized closure minimum without
an actual calendar. It produces at least one finite cap contact, not a
complete consumer of that contact. Contacts may be unused prescribed actions.

## Full-cap preservation under finite variations

Before absorption there is one live public history. Write q_i(a) for P's
conditional hazard at date a. Positive original N_i implies q_i(a)<1.
For a product row q let Q_i be forced-Quit payoff, P_i its passive absorbing
contribution, H_i=product_(j!=i)(1-q_j), and h=product(1-q_j). For a fixed
suffix (u,e), the entrance maps are

    E_i(q)=P_i(q)+H_i(q)e_i,
    V_i(q)=q_iQ_i(q)+(1-q_i)P_i(q)+h(q)u_i.

These are complete prescribed/Never maps. The full cap is the maximum of
the current Quit offer and passive Continue plus H_i times the suffix cap.
Every conditional tail of an actual all-END profile is all-END: an improved
tail response, used after continuing to that cut, would improve original
Never by a positive opponent-survival factor.

Assume the strict finite-deadline hypothesis. Choose finitely many dates,
and vary finitely many of their hazards, each originally in(0,1), in a
small open rectangle. The full caps of EVERY altered profile remain END.
Indeed, through the last changed date there are only finitely many finite
deadlines, and their original strict gaps persist by continuity. After that
date the suffix is fixed. Each later END-minus-response gap is its old
conditional suffix gap multiplied by the NEW positive opponent survival
through the changed prefix. Its sign therefore cannot reverse. The new
literal Never offer is available, proving B=e exactly. No uniform margin
for the infinitely many later queries is required.

The same argument permits a one-sided increase at a zero hazard; below we
need only existing strictly positive hazards, so both signs are available.
Every such alteration remains an actual independent complete law with
positive ORIGINAL Never. No tail is executed after an infinite prefix.

## First-order identity on persistent columns

Let n_i(a)=Pr(T_i>=a), s_a=product n_i(a). Thus n_i(a)->N_i(P)>0 and
s_a->nu(P). Conditional finite masses after a tend to zero, so all late
hazards and all late prescribed/Never values tend to zero. Consequently

    D_q E(q(a))->Gamma, D_q V(q(a))->Gamma.

Fix persistent owner k and choose arbitrarily late a with q_k(a)>0. Vary
that ONE hazard both ways. Earlier absorption terms are unchanged. The
whole-source cap derivative for recipient i tends to (nu/N_i)Gamma_ik;
the whole prescribed derivative tends to nu Gamma_ik; the ORIGINAL Never
derivative tends to -nu. More explicitly, the corresponding finite-date
factors are s_a/n_i(a),s_a, and -nu/(1-q_k(a)); they have exactly these
limits. Local minimality and division by nu>0 give

    sum_i r_i Gamma_ik=rho for every k in S,
    r_i=theta_i(1/N_i(P)-1)>=0.                            (1)

This is a derivative of the ORIGINAL whole objective F, not a conditional
minimum assertion.

## Mixed variations force the persistent singleton block to vanish

Take distinct persistent owners j,k. Choose positive hazards q_j(a),q_k(b)
with a<b, both arbitrarily late. Keep all other hazards fixed and vary
these two in a small open rectangle. By the full-cap argument F equals
sum theta_i(e_i-U_i)+rho nu throughout this rectangle.

Each owner's COMPLETE law is affine in one of its conditional hazards when
its other hazards are fixed. Since j and k are distinct, U_i,e_i and nu,
and therefore F on this rectangle, are EXACTLY bilinear in the two parameters.
An interior local minimum of a bilinear polynomial has zero first derivatives
and ZERO mixed coefficient. This is exact at every selected pair(a,b).

Its late mixed limits are

    (1/nu) d_j d_k U_i -> -Gamma_ik                for every i,
    (1/nu) d_j d_k e_i -> -Gamma_ik/N_i            if i notin{j,k},
    d_j d_k e_j=d_j d_k e_k=0,
    (1/nu) d_j d_k nu ->1.                                (2)

Here d_j,d_k mean derivatives of the chosen hazards, not deviation debts.
For a direct check, changing a late hazard replaces that owner's remaining
conditional law by current Quit minus its old future law. That future law
has vanishing finite mass and tends to literal Never. In the four mixed
outcomes, the EARLIER singleton j cancels, while its occurrence removes the
later singleton k; hence the surviving payoff coefficient is -Gamma_ik.
The probability all relevant owners reach these late dates tends to nu
for prescribed payoffs and nu/N_i for recipient i's Never reply. A Never
reply excludes its own law, giving zero if i=j or k. Events involving any
additional late finite clock have vanishing probability; bounded rewards
control the error uniformly even if b-a tends to infinity. Finally the
exact Never mixed derivative is nu/[(1-q_j(a))(1-q_k(b))], giving(2).

Thus the zero mixed coefficient, divided by nu and passed to late dates,
is

    0=theta_j Gamma_jk-sum_(i notin{j,k})r_i Gamma_ik+rho.

Use(1) for column k, with Gamma_kk=0, to obtain

    0=(theta_j+r_j)Gamma_jk=(theta_j/N_j(P))Gamma_jk.

Therefore Gamma_jk=0. Since both supports are unbounded, one can also choose
k's date earlier than j's arbitrarily late, proving Gamma_kj=0. This proves
the singleton-block assertion in(T).

If S had at most one owner, choose that owner (or any owner when S is empty).
Its opponents have bounded finite stopping supports. A finite deadline after
all their possible finite dates then agrees with Never on every opponent
exit; on all-opponent-Never both pay its own singleton zero. This deadline
attains e_i=B_i, contradicting strictness. Hence |S|>=2, completing(T).

## Bounded finite contacts force an exact price identity

Assume Gamma is invertible and define s_i=sum_j(Gamma inverse)_ji.
If ALL FOUR owners are persistent and the union of finite cap-contact dates
is bounded, the SAME actual local minimum must satisfy

    (theta_i+rho s_i)Gamma_ij
                   =(theta_j+rho s_j)Gamma_ji for all i,j.  (PRICE)

Moreover theta_i+rho s_i>=0. If a fixed pair has

    delta=theta_i Gamma_ij-theta_j Gamma_ji!=0,
    D=s_i Gamma_ij-s_j Gamma_ji,

this entire mode is impossible for0<rho<|delta|/[2(1+|D|)]. No singleton
nonvanishing, sign, positive inverse column, joining condition or simultaneous
support date is required. The multipliers r in this section may be negative;
they replace the nonnegative r used in the no-contact case.

## Exact finite-window cap geometry

Let C be the owners having at least one finite cap contact; for i in C set
b_i=B_i=e_i. After A0 choose EIGHT positive hazards in chronological owner
order0,1,2,3,0,1,2,3. All owners' unbounded supports produce this word
arbitrarily late. Positive N puts these controls strictly between0 and1.
Hold every other hazard fixed and let z in R^8 denote their small changes.

In an open neighborhood of0 the COMPLETE caps are exactly

    B_i(z)=max(b_i,e_i(z)) if i in C,
    B_i(z)=e_i(z) if i notin C.                           (CAP)

The old contact offers occur before all controls, so remain fixed. All
queries between A0 and the last control are finitely many strict gaps;
continuity keeps them below b_i on C and below e_i(z) off C. After the last
control each END-minus-query gap is its unchanged suffix gap times NEW
positive opponent survival. Thus no later query can exceed e_i(z), even
when it approaches END arbitrarily closely. This proves(CAP) against the
entire infinite response menu, not a finite tester list.

Write the smooth polynomials U(z),e(z),nu(z) for the actual varied law.
Local minimality and(CAP) give multipliers gamma_i in[0,1] on C and gamma_i=1
off C such that the smooth Lagrangian

    L_gamma(z)=sum_i theta_i gamma_i e_i(z)
                          -sum_i theta_i U_i(z)+rho nu(z)

has gradient0 at0. To see this without a nonsmooth theorem, the directional
derivative is the support function of the compact convex gradient set
{D L_gamma(0):gamma_C in[0,1]^C}. If0 were outside that set, strict finite
dimensional separation would give a direction with negative derivative.

For arbitrarily late such windows, D e_C has full row rank: its first four
columns tend to diag_(i in C)(nu/N_i) Gamma_[C,I], whose rows are independent.
The exact level set e_C(z)=b_C is therefore a smooth local manifold. F on
it differs from L_gamma by a constant. Since D L_gamma=0, the Hessian of
L_gamma is positive semidefinite on ker D e_C. This is the ordinary
second-order necessary condition along the exact level manifold.

## First-order limit and the eight-control Hessian

Let the eight windows escape to infinity. The original actual laws satisfy
q(a)->0 and all conditional future finite masses tend to0. Global first
derivatives for a control of owner j tend to

    d_j e_i -> (nu/N_i)Gamma_ij,
    d_j U_i -> nu Gamma_ij, d_j nu -> -nu.

The multipliers gamma are bounded. Pass to a subsequence with gamma->g;
the first four stationary columns imply

    r^T Gamma=rho one^T,
    r_i=theta_i(g_i/N_i-1), a_i=theta_i g_i/N_i>=0,
    r_i=rho s_i and a_i=theta_i+rho s_i.                 (FO)

Invertibility actually makes this limiting g unique. Multipliers outside C
remain1. Individual second derivatives are0 exactly: a complete law is
affine in ONE of its hazards when its other hazards are held fixed.

For two different controls with earlier owner j and later owner k, the
late Hessian divided by nu has limit

    theta_j Gamma_jk-sum_(i outside{j,k})r_i Gamma_ik+rho
       =(theta_j+r_j)Gamma_jk=a_j Gamma_jk.              (MIX)

This is the ordered mixed calculation proved above, with cap
weights gamma on e. The recipient j's Never reply ignores its own control;
the prescribed earlier singleton removes the later singleton. All other
late-clock events have vanishing probability, uniformly in the date gaps.

For two controls of the SAME owner j, the corresponding limit is

    -sum_i r_i Gamma_ij+rho=0 by(FO).                    (DUP)

Indeed U_i's mixed derivative tends to -nu Gamma_ij, e_i's to
-(nu/N_i)Gamma_ij for i!=j and0 for i=j; the original Never mixed derivative
tends to nu. Diagonal Gamma_jj=0 includes the recipient-j case. These are
signed changes of one complete law, not two independent clocks for j.

Let H be the resulting symmetric8-by8 limiting Hessian divided by nu. Its
diagonal and same-owner entries are0; other entries are given by(MIX) using
the earlier owner's label. The limiting constraint matrix A has repeated
columns diag_(C)(nu/N_i)Gamma_[C,j] for the two occurrences of owner j.
The finite Hessians are PSD on their exact constraint kernels, hence H is
PSD on ker A. For example project any d in ker A to
d_n=d-A_n^T(A_n A_n^T)^-1 A_n d; full row rank gives d_n->d. The case C empty
has no constraint and needs no projection.

For each owner i set d_i=e_i-e_(i+4), swapping its two occurrences. Then
d_i is in ker A and d_i^T H d_i=0 by(DUP). Positivity of a quadratic form
on ker A implies d_i^T H d=0 for every d in that kernel. Apply this to d_j.
For i<j the order is i,j,i,j, and exact cancellation gives

    0=d_i^T H d_j=a_i Gamma_ij-a_j Gamma_ji.

Substitute a_i=theta_i+rho s_i from(FO) to obtain(PRICE). The stated strict
rho bound makes |rho D|<|delta|/2, so delta+rho D cannot vanish. This proves
both the exact theorem and its quantitative mode exclusion.

## One price choice excludes the mode at the same table

Let K be ANY compact product box of strictly positive recipient weights with
nonempty interior. Suppose a source construction is valid for EVERY theta
in K and every0<t<t0, with the objective rho=t Theta,Theta=sum theta_i.
This is the only box premise; no actual source attainment is inferred.

Since Gamma is invertible and hollow, choose i!=j with Gamma_ij!=0. Start
at the center theta0 of K. If delta(theta0)!=0 keep that center. Otherwise
increase theta0_i by one quarter of its coordinate interval width, staying
in the interior of K. The discrepancy changes by that nonzero increment
times Gamma_ij. Thus this constructs one fixed theta with delta!=0 using
only the finite native table and the box. Choose theta BEFORE t and before
any minimum. With D as above, put

    t_bar=min(t0,|delta|/[2Theta(1+|D|)])>0.

For EVERY0<t<t_bar,(PRICE) is impossible at every actual all-END minimum
with all four supports unbounded and bounded finite cap contacts. Thus every
surviving actual source has a bounded finite stopping support for some owner
OR an unbounded set of finite cap-contact dates. No perturbation of the
native table is needed for this price selection. A reciprocal zero pair
does not invalidate the identity or this construction.

## A finite-contact minimum can be selected without any Gamma genericity

For a global minimum there is also a finite comparison construction. Define

    A=inf{sum_i d_i(R):R actual,nu(R)=0}>0,
    theta_min=min_i theta_i>0.

Let an actual global minimum P of F satisfy all-END, N_i>0, and

    mu=F(P)<theta_min A.                                  (3)

**Selection theorem.** There is an ACTUAL all-END global minimum P' with
positive original Never and a finite cap contact. If P has no such contact,
P' can be obtained by increasing ONE existing hazard at ONE finite date,
has nu(P')<nu(P), and the new contact is at a different owner from the
changed hazard. No reward, weight, cap family or minimum is reselected.

Proof. If P already has a contact, take P'=P. Otherwise all its finite
queries are strict. P is not AllNever, because AllNever has finite native
queries0=e. Thus choose q_j(a)=z0 in(0,1), and vary only that hazard z
toward1. Let R_z be the resulting actual profile, with all other hazards
fixed. Up to date a there are finitely many query inequalities. Each
END-minus-query gap is affine in z, since one owner's complete law is
affine in this conditional hazard. At z0 all these finitely many gaps
are strictly positive. Later gaps have the fixed-suffix form proved above
and retain their signs for z<1; at z=1 their nonnegative limits remain.

Let z* be the first zero of one of the finitely many earlier/current gaps
on(z0,1], or1 if no such zero exists. Throughout[z0,z*], all caps remain
END. Hence F(R_z)=sum theta_i(e_i(R_z)-U_i(R_z))+rho nu(R_z) is AFFINE
in z on that interval. There is also a two-sided all-END neighborhood of
z0. Actual global minimality therefore forces its slope to be zero, so

    F(R_z)=mu throughout[z0,z*].

If z*=1, the modified owner has original Never zero: any earlier draw is
finite, and any remaining draw quits at a. Thus R_1 is absorbing and
F(R_1)>=theta_min A, contradicting(3). This argument also covers a first
contact occurring only at z=1, by continuity of the actual finite-hazard
maps and complete caps. Therefore z*<1. The actual profile P'=R_(z*) is
still proper, all-END, and has a finite contact at a date no later than a.
It remains a global minimum. Only owner j's law changed, so owner j's
response menu and cap are unchanged; the newly binding contact belongs
to a different owner. Finally

    N_j(P')=N_j(P)(1-z*)/(1-z0)<N_j(P),

with all other original N unchanged, proving the strict Never reduction.
No approximate minimum or tail minimum was substituted. This proves the
selection theorem.

## A first-stage contact and a genuine joint atom can be selected

Continue with the contact-selection theorem's SAME table, weights, rho, global value
mu and absorbing bound(3). Suppose additionally every such global minimum
has B_i^Z>0. There is an actual all-END global minimum whose EARLIEST finite
cap contact tau is exactly its FIRST prescribed stage.

Indeed choose the least possible earliest contact time tau among actual
all-END global minima; the previous selector makes this nonempty, and times
are natural numbers. If a positive hazard q_j(a) occurred at a<tau, every
finite query through a would be strictly below END. Later queries may have
contacts, but their gaps still transport by a positive factor under changing
this one hazard. Thus the SAME affine-ray argument produces, before its
absorbing endpoint, a new all-END global minimum with contact time at most
a<tau. This contradicts minimality of tau. Consequently no owner has any
finite stopping mass before tau. Some owner contacts at tau. If there were
also no prescribed mass AT tau, this finite response would quit alone at
own singleton0 and have value0, contradicting B_i^Z>0. This proves the claim. Deleting the preceding all-Continue dates then
reindexes this stage to date0 without changing U,B,e,N: all retained
responses correspond to the old responses shifted by tau, and discarded
early queries pay singleton0 strictly below the positive native cap.

For the full first-stage COLLISION conclusion take the actual source
objective to be the original unweighted SUM at

    r_i(S)=theta_i[Z_i(S)+t], rho=t Theta,
    s_i=r_i({i})=theta_i t.

Assume the explicit original cap margins

    B_i^r-s_i>mu for every owner i.                       (4)

Then at least TWO owners have positive own stopping atoms at tau. Suppose
only h has such an atom, of size a in(0,1); a<1 follows from positive N_h.
After tau condition on continuation and retain the unchanged later calendar.
This is an ACTUAL suffix profile with original payoff/cap(u,b) and full
SUM debt D_tail>=mu by global minimality. Exact first-row accounting gives

    U_h^r=a s_h+(1-a)u_h, B_h^r=max(s_h,b_h),
    U_j^r=a r_j({h})+(1-a)u_j,
    B_j^r>=a r_j({h})+(1-a)b_j for j!=h.

By(4), b_h=B_h^r. Summing the four complete debts yields

    mu>=a(B_h^r-s_h)+(1-a)D_tail
       >a mu+(1-a)mu=mu,

a contradiction. Thus the first stage has at least two positive own atoms.
Independence and proper hazards give positive probability of a literal
nonsingleton first-quitting coalition. No tail minimum or common debt vector
was assumed; the suffix floor is the original FULL SUM floor.

### The cap-margin input is already implemented for this exact source

The declaration `positive_minimum_fourPlayer_allOwner_quadraticMargins` in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPreemptedOwnerQuadraticMargin.lean`
was statically read under its imports. It assumes an ORIGINAL semantic
payoff/cap pair in the original full carrier, a global minimum of the TRUE
unweighted SUM there, exactly four players, a positive reward bound M_r,
and mu>0. It has no cube, common-debt, singleton-sign, or tail hypothesis.
It proves for every owner

    B_i^r-s_i>=mu+mu^2/(8M_r)>mu.

Our raised/weighted reward r is one ordinary ORIGINAL table. Its full SUM
is exactly F on the native augmented carrier, so its selected actual global
minimum supplies these exact inputs. Moreover B_i^r=theta_i(B_i^Z+t),
which gives theta_i B_i^Z>mu>0. Thus both native positivity and(4) hold
for EVERY minimum used in the finite contact-time selection above.
This cites an existing checked strategic input; its proof is not claimed
as new mathematics here, and no Lean build was run in this review.

### The contact is paid, and its native END kernel can genuinely differ

At all-END with positive original Never, every original debt satisfies

    d_i^r=theta_i[d_i^Z+t nu]>=theta_i t nu>0.

Thus the earliest finite contact belongs to a PAID owner. If all off-diagonal
joining increments L_ij=Z_i({i,j})-Gamma_ij are nonzero, choose any contact
owner i and an opponent j with positive atom at tau; one exists because
at least two owners have such atoms. The event that j quits at tau and all
other opponents Never has positive ORIGINAL probability. On this event
native Quit-at-tau and native Never pay J_ij and Gamma_ij, respectively,
so their payoff kernels differ. They have the same native full-cap value.
In the original raised table the corresponding late FINITE replies approach
the same full cap as the finite contact; literal Never is not that cap.
The kernel difference at j's tau event persists for every later finite reply.
This is an actual paid-contact/END witness, not yet an admissible return or
an improvement of the original minimum. Such a consumer remains open.

## Complete-law semantics and the full-SUM source objective

Along the unique live history, independent private behavioral randomization
is equivalent to independent laws of the first Quit date on natural dates
plus literal Never. A behavioral unilateral replacement is a mixture of
finite pure deadlines and Never; its cap is their supremum. Thus every cap
used in this packet covers unrestricted behavioral deviations. A finite
hazard modification is implemented by one changed conditional private coin
and the original earlier and later coins.

For a fixed native table and t>0, put r_i(C)=theta_i[Z_i(C)+t] for every
nonempty coalition, while keeping live and literal Never reward zero.
Every finite unilateral deadline guarantees absorption, so its raised
payoff is theta_i times its native payoff plus t theta_i. Late native
finite deadlines converge to e_i by bounded convergence and own-singleton
zero. Their supremum therefore equals the native full cap B_i, even if no
finite deadline attains it. The raised Never offer is

    theta_i[e_i+t(1-product_(j!=i)N_j)]<=theta_i(B_i+t).

The complete raised cap is consequently theta_i(B_i+t), and its prescribed
payoff is theta_i[U_i+t(1-nu)]. The ORIGINAL raised full-SUM debt is exactly

    sum_i theta_i(B_i-U_i)+t(sum_i theta_i)nu.

Thus rho=t sum theta_i is the actual source objective, with no relabeling
of finite mass escaping to late dates as Never. Any actual all-END minimum
of this problem supplies precisely the local hypotheses above. AllNever
comparison gives its value mu<=rho. In particular rho<theta_min A supplies
the selector's strict gap bound without an extra strategy input.

The raw singleton condition is available after perturbing a native table
with A>0 and then selecting sources afresh. Each entrywise reward change of
size delta changes every prescribed payoff and full cap by at most delta;
the absorbing SUM gap changes by at most8delta. Avoid the twelve singleton
zero hyperplanes with delta<A/8. This produces a positive-gap table with
all off-diagonal Gamma entries nonzero. No old minimum, law, cap contact,
or actual realization is transported through that perturbation.

## Exact boundary controls and falsification tests

* If at most one owner has unbounded finite support, a finite query after
  that owner's opponents' last possible finite date attains Never exactly.
  The strict no-contact hypothesis is then impossible regardless of Gamma.
* A single zero Gamma_jk is insufficient to evade the mixed argument:
  persistent j and k require BOTH Gamma_jk=0 and Gamma_kj=0. At least two
  persistent owners are necessary. This includes every sparse scheduling
  pattern and does not require simultaneous positive hazards.
* The source's original N_i>0 makes every selected positive hazard interior
  and every conditional reach factor positive. A pure sure-Quit row lies
  outside that hypothesis. No derivative through a zero reach is used.
* For an exact two-date check, let j mix Quit at an earlier date with
  probability x and k mix Quit at a later date with probability y; all
  remaining mass is literal Never. Let Gamma_jk=g>0,Gamma_kj=h>=0 and both
  joining rewards be at most their corresponding singleton offers. Both
  caps are END. The affected objective is

      theta_j*g*x*y+rho*(1-x)*(1-y).

  The y-stationarity equation gives rho=theta_j*g*x/(1-x). Its mixed
  coefficient is then theta_j*g+rho=theta_j*g/(1-x), precisely the positive
  coefficient theta_j*Gamma_jk/N_j in the proof. Hence the stationary
  candidate is a saddle, not an interior local minimum. The other owners
  may have identically zero rewards. This tests the exact cancellation;
  it is not a positive-gap game.
* In the selector the updated Never coordinate is exactly
  N_j(1-z*)/(1-z0). At z*=1 it is zero and the profile is absorbing. The
  contradiction uses the strict bound mu<theta_min A, not an unsupported
  comparison of native and weighted debt gaps. The endpoint is a genuine
  actual law, not a continuation after an infinite word.

For an exact raw matrix check in the bounded-contact theorem, take

    Gamma=[[0,-2,-5,4],[-6,0,-4,6],[1,3,0,-5],[1,-1,4,0]].

Its determinant is42, and its strictly positive inverse column at owner0 is
(26/21,38/21,1/7,4/3). For theta=(1,1,1,1), the discrepancy at pair(0,1) is4. The inverse
column sums are(95/21,46/21,127/21,170/21), so D=86/21 at that pair and
rho<42/107 suffices for the price obstruction. Consequently the
bounded-contact/full-persistent case is excluded for every completion of
these singleton rewards that supplies that price/objective and actual
minimum. This is a source-mode test, not a counterexample or a claim of UE
for all such completions. The following standalone exact check verifies
these finite data without any input file.

```python
from fractions import Fraction as F
from itertools import permutations
G=[[0,-2,-5,4],[-6,0,-4,6],[1,3,0,-5],[1,-1,4,0]]
v=[F(26,21),F(38,21),F(1,7),F(4,3)]
assert all(x>0 for x in v)
assert [sum(G[i][j]*v[j]for j in range(4))for i in range(4)]==[1,0,0,0]
det=0
for p in permutations(range(4)):
    sign=(-1)**sum(p[i]>p[j]for i in range(4)for j in range(i+1,4))
    term=sign
    for i in range(4):term*=G[i][p[i]]
    det+=term
assert det==42
S=list(map(F,[95,46,127,170]));S=[x/21 for x in S]
assert [sum(S[i]*G[i][j]for i in range(4))for j in range(4)]==[1,1,1,1]
assert G[0][1]-G[1][0]==4
D=S[0]*G[0][1]-S[1]*G[1][0]
assert D==F(86,21) and F(4)/(2*(1+abs(D)))==F(42,107)
print('PASS: inverse data and exact fixed-price obstruction.')
```

## Source correspondence, overlap and Lean handoff

The complete-law meanings are `quittingStoppingLawExpectedPayoff` and
`quittingStoppingLawReplacementPayoffCap`, and the behavioral correspondence
is `quittingStoppingLawCap_behaviorStoppingLaws_eq_continuationBestResponseValue`
in `UniformEquilibrium/Quitting/Paths/StoppingLawOperationalDistance.lean`.
The exact full prefix cap and debt identities are
`quittingContinuationBestResponseValue_rootThenContinuation_eq_max` and
`quittingTerminalDeviationDebt_rootThenContinuation_eq` in
`UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean`. They justify the
same complete response menus used in the elementary argument above. No new
Lean declaration is asserted or compiled here.

The finite multiaffine interior-minimum principle is elementary and already
used in original minimum rigidity arguments. Its reuse is explicit: a
bilinear polynomial with an interior local minimum has zero mixed term,
and an affine function with such a minimum is constant. The new content
is the ordered late mixed-law limit, its cancellation with persistent-column
stationarity to force a zero singleton block, the bounded-contact tangent
Hessian/price obstruction, and aligning the first finite cap contact with
the first prescribed joint stage at the same table and minimum value. The
solo-first collision ledger and quadratic cap margins are reused; they are
not additional new source exclusions.
An observer-constrained objective d_p+rho nu is a different problem: it
forbids the unconstrained variations used here and does not supply these
four-owner full-SUM conclusions. No specially chosen common debt vector,
marked clock compactification, or calendar-attainment theorem is used.

A Lean handoff should define an actual finite-hazard local minimum and the
persistent-owner set, prove the finite-variation all-END neighborhood using
the full prefix cap formula, and prove the signed-law first and mixed
limits for independent complete laws. The main target states that distinct
persistent owners have reciprocal singleton rewards zero under strict
finite-query slackness. The selector is a separate finite affine argument
with a true global minimum and the strict weighted absorbing-gap bound.
The bounded-contact target additionally needs the compact multiplier box,
the exact END-level manifold Hessian, and interleaved duplicate-owner
tangent swaps. No target should take its desired finite contact, zero
singleton block, the price identity, source attainment or a minimizing
tail as a structure field.

All statements concern terminal complete-law objectives. The packet gives
no new uniform-payoff target, no strategy-class completeness beyond the
actual source case, and no new Lean, adapter or consumer certification.
