# Global entry requires excursions and control of their successors

Owner: CODEX_COORDINATOR. Ordinary mathematics. The local observer attractor
does not supply a complete entry-and-return construction. This note proves
two precise limitations and a positive raw root producer: small roots can
be trapped before entry, but the same joining signs force a uniformly
absorbing Nash root on a continuation face. Its successor and recurrent use
remain uncontrolled. No new UE class or positive-gap counterexample is claimed.

All root words are constructed in backward prefix order. A diagonal proxy
annotation is a prescribed payoff and full response cap with equal coordinates;
it need not be an actual continuation. An exact root Nash condition preserves
diagonality. Limits below mean limits of finite words, never play after an
infinite number of dates.

## General weighted-payoff drift

Let a native n=4 quitting table Z have own singleton0, and let its singleton
matrix Gamma be invertible. Set

    ell = 1^T Gamma^{-1},
    K = max(0, max_{|D|>=2} -ell Z(D)),
    delta = 1/[12(K+1)].

These are finite quantities determined by the raw table. A diagonal proxy
annotation v followed backwards by a product root q has prescribed output

    v' = c v + sum_{D nonempty} P_q(D) Z(D),
    c = product_i(1-q_i).

The next assertion uses only this payoff identity; root Nash comparisons
are not needed. If max_i q_i<=delta and ell v<=1/4, then

    ell(v'-v) >= (1-c)/4.                         (1)

Proof. Write p=1-c and eta=P_q(|D|>=2). Each singleton has weighted reward
ell Gamma e_i=1 and every other coalition has weighted reward at least-K.
Therefore

    ell(v'-v) >= p(1-ell v)-(K+1)eta.

The event of at least two quitters is covered by the six pair events, so
eta<=sum_{i<j}q_i q_j <=(3delta/2)sum_i q_i. Also sum_i q_i<=4p, since the
number of quitters is at most4 times the indicator of a nonempty coalition.
Consequently eta<=6delta p, and the preceding lower bound is at least
3p/4-p/2=p/4. This proves(1).

Consequences. Suppose a backwards root sequence starts at v_0 and remains
in ell v_n<=1/4, all its roots satisfying max_i q_{n,i}<=delta. Telescoping
(1) gives

    sum_n [1-product_i(1-q_{n,i})] <= 1-4 ell v_0.

Thus absorption probabilities are summable. Since each q<=delta<=1/12,
all root joint-survival probabilities are at least(11/12)^4>0. Summability
of their deficits therefore gives strictly positive infinite joint survival.
All marginal survivals are positive too.

Hence a repeated return construction whose joint survival tends to zero
must at some point have either ell v>1/4 or max_i q_i>delta. For an explicit finite-word bound put cmin=(11/12)^4. Since log c>=-(1-c)/cmin
for c in[cmin,1],

 log nu >= -4[ell v_out-ell v_in]/cmin
        >= -[1-4 ell v_in]/cmin.

This positive survival lower bound passes to closures of finite words whose
intermediate values and roots satisfy the same bounds. Its endpoint form
also passes under composition of such phases. An endpoint in the halfspace
alone does not license this conclusion about unrestricted approximants.

If h=Gamma^{-1}e_p>0, then ell_p=sum_i h_i>0. An exact axis-to-axis word
with endpoints b e_p and b' e_p, entirely satisfying the two bounds, obeys

    ell_p(b'-b) >= (1/4) sum_roots P_root(absorption).

Thus every nontrivial such return increases the pivot seed. In particular
there is no invariant compact family of such returns with uniformly positive
absorption and b<=1/(4ell_p), if the intermediate annotations also remain
in ell v<=1/4. Allowing negative observer values does not evade this signed
weighted-payoff inequality. It is a limitation of a wholly local proof,
not a counterexample to uniform equilibrium or to a construction that makes
macroscopic excursions.

## A small-root entry obstruction

Players are 0,1,2,3, with pivot2, own-singleton and Never rewards zero.
Fix the singleton matrix

    Gamma=[0,-1,-1,2; -1,0,1,1; 1,2,0,-1; 1,-1,1,0].

For nonempty D not containing i, let
L_i(D)=Z_i(D union{i})-Z_i(D) be the joining increment. Write L_ij for
L_i({j}). Suppose the observer increments have signs

    L01<0,L03<0,L10>0,L13<0,L30<0,L31>0,

and impose the additional strict raw conditions

    L02<0, L12<0, L32>0, L23>1.                         (A)

All higher rewards are arbitrary finite numbers. These conditions are
compatible with all hypotheses of the observer orthant attractor and with
the benchmark no-child, one-pivot singleton chamber.

**Proposition.** There is delta>0, depending only on the raw table, such
that from every diagonal seed b e2, b>0, every finite word of exact proper
Nash roots whose odds are all at most delta consists of singleton3 roots
and all-Continue roots. Its diagonal annotations have the form

    v(p)=(2p,p,b-(b+1)p,0), 0<=p<b/(b+1).               (1)

Every limit has the same form with p<=b/(b+1). Starting further such words
from any of these limits does not escape this curve. At its terminal point
p=b/(b+1), the only delta-small exact root is all-Continue. In particular,
no such construction reaches an observer annotation with negative
coordinate0, despite the existence of the local observer repair theorem.

For proof, bound the absolute higher joining coefficients by K>=1. Put

    m0=min(-L01,-L02,-L03)>0,
    m1=min(-L12,-L13)>0,
    delta=min(1,m0/(4K),m1/(2K)).

For odds x_j in[0,delta], the sum of the three opponent pair monomials is
at most delta times the sum of opponent odds, and the triple monomial is
at most delta^2/3 times that sum. Therefore the full joining polynomial
for player0 satisfies

    C0(x)<=-m0 sum_(j!=0)x_j+K(delta+delta^2/3)sum_(j!=0)x_j
          <=-(2m0/3)sum_(j!=0)x_j.                     (2)

When x0=0, the joining polynomial for player1 similarly satisfies

    C1(x)<=-(m1/2)(x2+x3).                             (3)

At an exact proper root, C_i(x)<=v_i, with equality whenever x_i>0.
Suppose v=v(p) with beta=b-(b+1)p>=0. If p>0, (2) and v0>0 exclude
x0>0. At p=0, x0>0 would force all other odds zero by (2), but the quiet
player1 comparison would read L10*x0<=0, impossible. Thus x0=0 always.

If p>0, (3) and v1>0 exclude x1>0. At p=0, x1>0 would force x2=x3=0,
but the quiet player3 comparison would read L31*x1<=0. Thus x1=0.
The player3 comparison is now L32*x2<=v3=0, hence x2=0. The only remaining
odds are x3, constrained by L23*x3<=beta. Such a root updates

    beta'=(beta-x3)/(1+x3),
    p'=(p+x3)/(1+x3),

and preserves (1). If beta>0, condition L23>1 gives beta'>0. If beta=0,
then x3=0. This proves the assertion, including every closure phase by
continuity of the curve and the same exact argument at its endpoint.

This is a uniform small-odds obstruction; arbitrary finite higher rewards
cannot remove it. Any successful entry for these tables must contain at
least one root with an odds coordinate exceeding delta, or a sure quitter,
or use a different seed/architecture. It does not exclude any of those
possibilities, and it supplies no positive terminal-exploitability gap.

## The obstruction itself produces a finite-amplitude Nash root

The preceding small-root obstruction does NOT mean that the original
continuation game has only small/trivial roots. In fact it implies the
opposite uniformly over the whole curve.

**Corollary.** With the same raw assumptions, let
rho=delta/(1+delta)>0. For every b>0 and every p in[0,b/(b+1)], the
continuation game at v(p) has an exact Nash root q with

    max_i q_i>=rho, hence product_i(1-q_i)<=1-rho.       (4)

The constant depends only on the raw reward table, not on b or p. More
generally the same conclusion holds at every finite annotation with
v0>0, v1>=0, v3=0 and arbitrary v2. Roots may be proper or have sure
quitters. This corollary supplies an absorbing prefix, not an invariant
family of successor continuation values.

For each epsilon>0, change only the fourth annotation to v3=-epsilon.
The finite one-stage continuation game has an exact mixed Nash equilibrium.
Suppose all its q_i were at most rho; all odds would then be at most delta.
The proof of(2)-(3), including the p=0 cases, again forces x0=x1=0.
But the player3 root comparison would require

    C3=L32*x2<=-epsilon,

which is impossible. Therefore every such perturbed equilibrium has
max_i q_i>rho. Take epsilon to zero along a sequence. Compactness of the
four mixed-action intervals supplies a convergent subsequence. The Nash
inequalities are continuous in q and the continuation vector, so its limit
is exact Nash for v(p), and satisfies(4). For the broader face assertion, v0>0 first forces x0=0;
if x1>0, (3) forces x2=x3=0 and v1=0, and the quiet player3 comparison
would require L31*x1<=-epsilon. Thus x1=0 again and the same contradiction
applies. This argument does not restrict or assume a root support and
covers pure/sure roots directly.

If beta=b-(b+1)p<L23*delta, no singleton3 root can satisfy(4), because its
odds obey x3<=beta/L23<delta. A sure singleton3 root is impossible too:
the quiet pivot would gain L23>0 by joining it. Thus at these states the
produced root is an
actual departure from the trapped singleton construction. The remaining
strategic task is to control the resulting diagonal successor and iterate
such departures; existence of one uniformly absorbing root is not a
recurrent equilibrium construction.

## Exact full-table control

Take M=14 in the canonical premium table, but replace

    Z0(02)=-2, Z1(12)=0, Z3(23)=2.

Keep every passive nonsingleton reward zero and every participant reward
in a coalition of size at least3 equal to -5. All remaining entries are
canonical: pair rewards are13 on (recipient,other)=(0,2),(1,0),(2,3),(3,1)
except the displayed override at(0,2), and -5 on all other directed pairs
except the displayed overrides.

The observer joining parameters are A=4,B=7,C=14,D=6,E=6,F=14, so
D0=1, eta1=eta3=8>0, and all stated local-attractor hypotheses hold.
The new pivot-pair increments are L02=-1,L12=-1,L32=1,L23=14.
Moreover every higher joining coefficient for player0 is negative, and
for player1 every higher coefficient on coalitions contained in{2,3} is
negative. Hence (2)-(3) hold for ALL nonnegative finite odds, without a
smallness restriction. Every proper exact Nash word from b e2 is trapped
on(1), even allowing successive limit phases.

Nevertheless the table has an immediate absorbing Nash profile: players2
and3 quit surely; players0 and1 continue. The active comparisons are
13>=-1 and2>=1; the quiet comparisons are0>=-5. Its payoff is(0,0,13,2).
Thus the trapped proper-root construction is entirely compatible with a
simple equilibrium. A proposed universal proof must include this type of
exit rather than infer entry solely from the local attractor hypotheses.

## A raw face-root producer beyond the benchmark

The finite-amplitude argument applies to any native own-zero four-player
table satisfying only the seven joining signs

 L01,L02,L03<0, L12,L13<0, L31,L32>0.

All remaining singleton and higher rewards are arbitrary finite numbers.
Use the same m0,m1,K,delta from the proof of(2)-(3). For EVERY finite
continuation v with v0>0, v1>=0, v3=0 and arbitrary v2, there is an exact
Nash root with max q_i>=delta/(1+delta). No benchmark singleton matrix,
L10 sign, L30 sign, or L23 magnitude is needed for this face assertion.

Indeed perturb v3 to -epsilon. If all odds were at most delta, C0<=0<v0
would force x0=0. If x1>0, C1<=0 and v1>=0 force v1=0 and x2=x3=0,
whereupon the quiet player3 comparison L31*x1<=-epsilon is impossible.
Thus x1=0, and C3=L32*x2<=-epsilon is again impossible. Finite Nash
existence and a compact limit give the stated uniform root at the original
face. This is a producer from raw rewards and a specified continuation
face; producing an invariant family of its successors is still open.

For every table in this seven-sign class, apply the face producer to
v=(b,0,0,0) and let b decrease to zero. A compact root limit supplies an
actual one-date native Nash profile followed by Never, with absorption at
least delta/(1+delta). If survival is zero, the profile is already absorbing.
If it is positive, repetition is not automatically Nash because the
continuation changes. All full behavioral comparisons are priced: against
opponents who continue forever after the single root, every later deadline
and Never have the same native payoff.

## Sources and next mathematical task

The inspected finite-game theorem is exists_isZeroQuittingRootNash in
UniformEquilibrium/Quitting/Root/NashExistence.lean; its continuation input
is arbitrary signed finite data. The exact diagonal bridge is
quittingTerminalSemanticPrefix_diagonal_eq_of_isZeroNash, and continuity is
continuous_quittingTerminalSemanticPrefix, both in
UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean. The weighted
payoff identity is its prescribed-payoff component. No Lean change or build
is claimed for the new raw mathematics.

The [local observer theorem](CODEX_COORDINATOR__OBSERVER_ORTHANT_ATTRACTOR.md)
now has a sharp first-order joining region. The next global obligation is to
control the successors of the uniformly absorbing face roots, with explicit
exits and a bounded recurrent family. Staying near zero with small hazards,
or replacing that obligation by an assumption of local entry, cannot suffice.
