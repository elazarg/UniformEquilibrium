# Two forced continuation rows exclude an open full-cap source region

## Exact statement

There are four players0,1,2,3. Native rewards Z_i(S) are finite real numbers
on nonempty quitting coalitions S, with Z_i({i})=0. Live play and Never pay
zero. Each player uses an independent complete stopping law on natural dates
plus a distinct Never point; one deviator may replace its entire law.

Fix the singleton matrix Gamma_ij=Z_i({j}) to be

    G=[0,-2,-5,4; -6,0,-4,6; 1,3,0,-5; 1,-1,4,0].

Require Z_i(S)<=0 whenever i in S and i in{1,2}. Fix thirteen nonsingleton
entries as follows; all others are arbitrary subject to that sign condition:

    Z0(01)=-1, Z0(03)=3, Z1(01)=-7, Z1(13)=-1,
    Z3(03)=2, Z3(13)=-2,
    Z0(013)=2, Z1(013)=-8, Z3(013)=0,
    Z2(01)=4, Z3(01)=0, Z1(03)=0, Z2(03)=-4.         (R)

Thus31 of the44 nonsingleton entries remain variable, eleven with the
specified nonpositive upper bound and twenty without a sign restriction.

For actual play retain prescribed terminal payoff U, full behavioral
response cap B, literal Never response e, and ORIGINAL marginal Never
probabilities N. Let C be the closure of all actual tuples(U,B,e,N), and
E={X in C:B=U}. The coordinates are bounded, so C is compact. Never masses
are not substituted for finite mass escaping every fixed date.

Define an open payoff region Omega by u=(-A,-B0,C0,D0), where

    0<A<3/4, 0<B0<7, D0>0,
    B0<7A+(7/2)D0, C0>B0/7+3A,
    h=(1-B0/7)(1-A),
    w0=A/(1-A), w1=-B0/(7-B0),
    w2=(C0-B0/7-3A)/h, w3=(D0+A-B0/7)/h,
    w3<2, w1+3w3-2w0>0, w2-w3/2+5w0/3>0.           (G)

**Theorem.** For every table satisfying(R) and the stated signs, no point
of E has payoff in Omega. Original joint Never may be zero. Every compact
K subset Omega therefore has a positive full behavioral total-regret floor
on actual profiles with U in K.

This is a source/payoff-region exclusion, not a UE existence theorem or a
positive exploitability gap over every profile of a game. The region is
nonempty: t(-1,-1,5,1/2) lies in it for every0<t<=1/100.
The exclusion also persists in a neighborhood of each such reward/source
pair, as proved below; the reward equalities do not confine its use to
isolated reward tables.

## Conjecture-facing change

The sole mutually positive participant pair is03, whose joining differences
are(-1,+1). Every support of size at least three has a nonpositive active
Quit offer, because it contains owner1 or2. The difficult pair is therefore
an opposed-joining pair. The theorem removes a complete open source region
on this reward family using actual successive continuations.

## Strategic inputs

No actual law realizing a closure point, continuation, root, minimizing
tail or return certificate is assumed. Actual approximants and their first
hazards produce both proper rows. A strict finite-depth example below passes
two compact Nash-continuation tests but fails the third, uniformly over all
free completions. This is stronger than merely writing a continuation kernel
or imposing a first-action outer bound.

Any full zero-debt source selected under a hypothetical positive absorbing
gap must avoid Omega when its table satisfies(R). Limits of approximate
sources cannot remain in a compact subset of Omega, by the regret-floor
conclusion. Arbitrary games, the rest of the opposed-pair family and other
source payoffs remain unclassified by this theorem.

## Full-cap incoming-row rule

For product first-date hazards q put hq=product_i(1-q_i),
H_i=product_(j!=i)(1-q_j). Let Q_i(q) be the immediate forced-Quit payoff
and P_i(q) the passive reward on nonempty opponent coalitions. Exact prefix
updates, with a literal continuation tuple on the right, are

    B'_i=max(Q_i,P_i+H_i B_i),
    U'_i=q_i Q_i+(1-q_i)P_i+hq U_i,
    e'_i=P_i+H_i e_i, N'_i=(1-q_i)N_i.              (1)

These compare every finite deadline and Never, hence every behavioral
replacement. With d_i=B_i-U_i>=0 their nonnegative decomposition is

    d'_i=q_i(B'_i-Q_i)+(1-q_i)(B'_i-P_i-H_i B_i)
                                      +hq d_i.    (2)

For ANY X in E, take actual approximants and a convergent subsequence of
their first hazards. Immediate Quit and conditional prescribed Continue are
legal deviations; consequently d_i>=q_i(B_i-Q_i). The limiting q satisfies

    Q_i(q)<=U_i(X), q_i(U_i(X)-Q_i(q))=0.           (3)

This requires neither positive Never nor a proper q. If further algebra
forces every q_i<1, the approximants' conditional tails have a compact limit
Y in C. Equation(2) then forces Y in E, and(1) gives

    U_i(X)=P_i(q)+H_i(q)U_i(Y) for every i.          (4)

Both actions of every proper active owner are optimal against that genuine
tail cap. Original Never is retained by N_i(Y)=N_i(X)/(1-q_i), including
zero original masses. No minimizing property is inherited by Y.

The reward assumptions give Q1,Q2<=0 everywhere, and, on q2=0, exactly

    Q0=-q1+3q3, Q1=-7q0-q3, Q3=2q0-2q1.           (5)

The quadratic terms cancel by the three specified013 participant rewards.
No free completion entry enters(5).

## The two forced rows and contradiction

Suppose a source X in E has payoff u in Omega. Since C0>0, (3) and Q2<=0
force q2=0. Q0<=-A forces q1>=A+3q3>0, so7q0+q3=B0. If q3>0, then

    D0=2q0-2q1<=2B0/7-2A-(44/7)q3<D0

by(G), a contradiction. Thus q3=0, and the unique first row is

    p=(B0/7,A,0,0).

It is proper. Only now apply(4) to obtain its genuine zero-debt tail Y.
The passive rewards on01 give exactly the vector w in(G). The inequalities
imply w0,w2,w3>0 and w1<0; in particular
D0+A-B0/7>D0/2>0.

Apply(3) to Y, with incoming hazards r. Again r2=0. Negative w1 forces
activity of0 or3; their positive payoffs and(5) force both active. If r1>0,
then7r0+r3=-w1, so w3=2r0-2r1<-2w1/7. But(G) gives
w3>-w1/3, a contradiction. Thus the unique second row is

    r=(w3/2,0,0,w0/3).

It is proper since w3<2 and A<3/4. Extract its genuine zero-debt tail T.
With k=(1-w3/2)(1-w0/3)>0, the passive03 rewards give

    U0(T)=-(w0/3)/(1-w0/3)<0,
    U3(T)=(w3/2)/(1-w3/2)>0,
    U1(T)=(w1+3w3-2w0)/k>0,
    U2(T)=(w2-w3/2+5w0/3)/k>0.

At T, positive payoffs for1,2 force its incoming hazards s1=s2=0 by(3).
But then Q0(s)=3s3>=0 cannot be at most its negative payoff. This
contradicts(3), proving the theorem for ALL zero-debt closure points.

For compact K subset Omega, the closed subset of C with U in K contains
no point with total debt D=sum_i(B_i-U_i)=0. If nonempty, its continuous
minimum debt is strictly positive; if empty the regret-floor statement is
vacuous. This floor concerns K, not the whole game.

## Stability under reward perturbation

Fix a permitted base table Z and u_* in Omega. Choose rho>0 such that
the closed SUP-NORM ball of radius2rho about u_* lies in Omega. All balls
in this paragraph use that norm. Let gamma>0 be
the minimum debt on the corresponding closed restriction of C. If that
restriction is empty, take any gamma>0.
For native Z' with entrywise distance eta from Z, the SAME actual profile
obeys

    ||U_Z'-U_Z||_infinity<=eta,
    ||B_Z'-B_Z||_infinity<=eta, |D_Z'-D_Z|<=8eta.

The cap estimate holds uniformly over all behavioral replacements before
taking their suprema. If eta<min(rho,gamma/16), every Z' profile whose
payoff lies within rho of u_* has Z-payoff in the larger ball, and hence
D_Z'>=gamma/2. In the empty-payoff case such profiles do not exist, by
the same payoff bound. The strict margin eta<rho keeps approximants of
any closed-rho-ball source in the larger ball, so closure gives the same
source exclusion for Z'.
Thus all56 native reward coordinates may be perturbed, with a radius
depending on the base table and chosen interior payoff region. No uniform
radius over unbounded free completions, or global positive game gap, is
asserted.

## Exact boundary and finite-depth tests

Put A=B0=t,C0=5t,D0=t/2,0<t<=1/100. Then

    h=(1-t/7)(1-t),
    w=(t/(1-t),-t/(7-t),13t/(7h),19t/(14h)).

The last two guard numerators are
t(27+6t)/[2(7-t)(1-t)]>0 and33t/(28h)+5t/[3(1-t)]>0.
All other guards also hold strictly throughout that interval.

For a sharper test let H=conv({0} union{Z(S):S nonempty}) and F_q(v) be
the prescribed prefix map in(1), initialized with U=B=v. Let NE(v) be its
auxiliary finite Nash roots, with offers Q_i and P_i+H_i v_i. Define

    K0=H, K_(n+1)={F_q(v):v in K_n, q in NE(v)}.

These are nested compact sets: H is invariant under every prescribed
prefix, and the Nash correspondence is closed. Positive-Never zero-debt
source payoffs lie in every K_n by proper actual-tail extraction. This is
not asserted for arbitrary sure-exit profiles with noncredible off-path
tails, nor is a terminal realization theorem for the intersection asserted.

For EVERY permitted completion and every stated t,

    u=t(-1,-1,5,1/2) belongs to K2 but not K3.        (6)

Here are exact hull witnesses. Put L=(7-t)(1-t),
F=4t^2-51t+28 and Delta=(3-4t)F. Writing z=U(T), the singleton-column
weights a(x)=G^-1 x are

    a(u)=t(47/7,167/14,10/7,15/2),
    a(w)=t/(6L)(276-5t,459-5t,60,315-4t),
    a(z)=t/(7Delta)(5(14t^2-726t+693),
         2(35t^2-3343t+3213),3(280-299t),
         7(4t^2-625t+602)).

Their entries are positive and their sums are respectively
193t/7, t(555-7t)/(3L), and
t(168t^2-15588t+14945)/(7Delta). The bounds L>6, Delta>54 give upper
bounds193/700,555/1800,14946/37800, all below1. Thus u,w,z belong to H
using just the fixed singleton rewards and0, for every free completion.

The displayed p is Nash at w: its active equalities hold, Q2<=0<C0,
and Q3<D0 by(G). The displayed r is Nash at z: its active equalities
hold, Q2<=0<w2, and
w1-Q1(r)=w1+(7/2)w3+w0/3>0. Hence w in K1 and u in K2.

Every Nash-prefix output satisfies(3). The forced-row calculation therefore
applies to an alleged u in K3, forcing the same proper p and unique
continuation w in K2, then the same proper r and continuation z in K1.
But z is not a Nash-prefix output at ANY continuation: its two positive
outsider coordinates force both hazards zero and contradict its negative0
coordinate. This proves(6). Since K1 implies the usual first-action outer
inequalities with a hull-bounded tail, u also passes that weaker test.

### A completion where every auxiliary root at u is bad

For an exact negative test, set every free nonsingleton entry to0 except
all seven participant entries of owner2, which are-10. Keep(R) unchanged.
At u=t(-1,-1,5,1/2),0<t<=1/100, the auxiliary root game has just ONE
Nash root, and every successor coordinate at it is strictly positive.

Owner2 strictly Continues: its gap at the empty opponent set is-5t,
and at nonempty opponent sets0,1,3,01,03,13,013 the gaps are respectively
(-11,-13,-5,-14,-6,-10,-10). Thus q2=0. For proper support013, using
odds x,y,z for owners0,1,3, the joining maps are

    Phi0=y-z+2yz, Phi1=-x-7z-8xz, Phi3=x-y.

The only proper pair root is03 with odds(x,z)=(t/2,t). Pair01 would
require y=-t, and pair13 would require -y=t/2. No singleton is proper
Nash because every input coordinate is nonzero. A proper013 root would
require x-y=t/2 and x+7z+8xz=t, hence z<=t/14, but then
Phi0>=-t/14>-t, a contradiction. AllContinue fails at the negative inputs.

There is no sure root either. Sure0 forces1 Continue and3 Quit, which
makes0 prefer Continue. Sure3 forces1 and then0 Continue, after which3
prefers its positive continuation. Sure1 with0 not sure forces3 Continue,
then0 Quit, reducing to the already impossible sure0 case.

At the03 root its quiet comparisons are strict. Put
h_*=1/[(1+t/2)(1+t)]. The quiet outputs are2t h_* and
(t/2-2t^2)h_*, both positive; active outputs are3t/(1+t) and
t/(1+t/2), also positive. Thus a pointwise good-root test cannot reject u
in this completion. The theorem rejects it as an ACTUAL full-cap source
through its successive genuine continuations. This root game is not an
actual equilibrium or a counterexample to UE.

## Source correspondence

Existing exact ingredients are
`quittingContinuationBestResponseValue_rootThenContinuation_eq_max` and
`quittingTerminalDeviationDebt_nonneg`
(`UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean`), and
`quittingTerminalPayoff_rootThenContinuation_eq`
(`UniformEquilibrium/ProofView/Concepts/Stochastic/Models/Quitting/RootContinuation.lean`).
They price complete behavioral replacements, not only immediate deviations.
The new ordinary mathematics is the all-source first-row extraction with
properness proved before tail inheritance, its two forced applications on
(R), and the explicit strict-depth certificate(6). No Lean build is claimed.

## Adapter and consumer

The input is a raw reward table, plus the payoff case of a full zero-debt
closure source. The theorem produces its two physical cuts and rejects the
entire case; no source realization or continuation is supplied. Compact
selection of a minimum inside E, or a limit of vanishing-debt profiles, is
sufficient to consume the exclusion whenever its payoff enters Omega.
The source restriction and compact-region regret floor are the semantic
outputs; a UE producer for the remaining payoffs is not provided.

## Lean handoff

A suitable formal theorem takes the finite reward comparisons, bounds(G)
and a putative augmented closure point with U=B and returns contradiction.
Auxiliary lemmas should expose(3), proper tail extraction, the three
polynomial identities(5), and the forced rows. Zero original Never is
allowed. A separate theorem gives the compact-region regret floor and
another gives(6); neither should assume an actual source realizer as data.

## Scope and nonclaims

The source coordinates u,w,z are different actual-tail annotations in the
contradiction, not three globally minimizing sources. The hull witnesses
in(6) by themselves realize no Nash profile. This theorem supplies no
stabilization depth for all games, no UE payoff producer outside Omega and
no counterexample to Fin4.
