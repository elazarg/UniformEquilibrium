# Complete inherited inverse-axis and repetition tests

Ordinary mathematical replacement-family theorem; not checked in Lean.
This does not close the inherited endpoint pattern or a raw Fin4 reward class.
The exact scalar control below is not an actual game/source. The complete
proof has an [independent review](../feedback/INHERITED_ABSORBING_WORD_OPTIMIZATION__BY_REVIEW.md).

## Source and statement

Use the native augmented carrier and retained-query graft of Sections12–13
of the [residual partition](CODEX_COORDINATOR__FIN4_RESIDUAL_PARTITION.md). In particular,
Q has observer U=B=e=0, pivot B=e=b>0, U=u, joint Never mass v, and
opponents' Never product h, with 0<v<h<1. Set n=v/h. Inverse-axis blocks
E_T, T>=0, have observer U=B=e=0 and pivot coordinates

    B=e=a(1-exp(-kT)), U=q(1-exp(-ST)),
    h(E_T)=exp(-kT), nu(E_T)=exp(-ST),
    a=1/k, q=1/S, c=S/k>1.

A retained head P has s=nu(P)>0, lambda=1/N_p(P)>=1,
K=e_p(P)-U_p(P), and t=(B_p(P)-e_p(P))/(s lambda), 0<=t<=b.
For every absorbing tail R in this zero-observer slice its headed debt is

    d_p(Phi_P(R))=K+s V(R),
    V(R)=lambda max(t,B_p(R))-U_p(R).                 (1)

The head's three full observer caps and payoffs are retained. At a positive
absorbing-gap source all these debts are at least m. The operation uses
limits of finite grafts, not execution after an infinite calendar.

Consider every absorbing finite or countable word formed from Q and E_T,
and their carrier limits. Here absorption means joint Never mass tends to
zero along finite prefixes; an E_infinity is itself a carrier limit. Define

    Binf=b/(1-h), Uinf=u/(1-v), H=Binf-a, D=Uinf-q,
    C=lambda[b-a(1-h)], D0=u-q(1-v)=D(1-v).

**Theorem.** The infimum of V over this entire absorbing word family is
attained in the carrier and is obtained by the following finite procedure.

* If D<0 and H>=0, the minimum is V(E_infinity)=lambda max(t,a)-q.
* If D<0 and H<0, put

      z*=min(1, [lambda(-H)/(c(-D))]^(1/(c-1))).

  The minimum is V(E_T Q_infinity), where exp(-kT)=z*, and equals
  lambda(a+H z*)-q-D(z*)^c.
* If D>=0, first optimize the step words Q^j E_infinity for j>=1.
  If C<=0, use j=infinity. If C>0, use the first integer j>=1 satisfying
  C>=D0 n^j; such an integer exists. Denote its cost by Vstep.
  If t<=a, the answer is min(Vstep,lambda a-q).
  If t>a, put z0=(t-a)/[b-a(1-h)] in(0,1). The answer is

      min(Vstep,lambda t-q-D0 z0^c).                 (2)

  The extra value is attained by E_T Q E_infinity with exp(-kT)=z0.

For finite j>=1 the step cost is explicitly

    V_j=lambda Binf-Uinf-lambda H h^j+D v^j;
    V_infinity=lambda Binf-Uinf.                    (3)

Thus at most two scalar costs and one geometric integer threshold exhaust
all the headed absorbing comparisons. Every such comparison against m is
equivalent to K+s Vmin>=m, with Vmin the displayed minimum. This is a
complete optimization of this replacement family, not of arbitrary tails.

## Proof

All blocks have nonnegative pivot cap equal to their literal Never response.
The graft cap maximum therefore stays on its through-tail branch inside a
word. Let z_j=exp(-k times the total axis duration before the (j+1)-st Q).
Then 1>=z_0>=z_1>=...>=0. If the word has only finitely many Q blocks, its
remaining axis duration is infinite; set every subsequent z_j=0. Absorption
forces the deleted-player survival product to zero as well: either there
are infinitely many Q blocks, or total axis duration is infinite.
Telescoping the deleted and joint survival losses gives, respectively,

    B=a+H theta_h,  U=q+D theta_v,
    theta_h=(1-h) sum_(j>=0) h^j z_j,
    theta_v=(1-v) sum_(j>=0) v^j z_j^c.              (4)

These series converge uniformly over all admissible sequences. Conversely,
every monotone sequence is supplied by successive logarithmic axis durations;
a first zero is interpreted as an absorbing E_infinity. Finite grafts and
compactness give its carrier limit. The geometrically bounded tails of the
series justify (4) also for limits of such words. All observer coordinates
stay zero and the total Never mass is zero.

If D<0, the geometric law with ratio v is stochastically earlier than the
one with ratio h. Since z_j is nonincreasing, Jensen's inequality gives

    theta_v >= [(1-v) sum v^j z_j]^c >= theta_h^c.    (5)

Equality is attained by the constant sequence z_j=z, namely E_T Q_infinity
with z=exp(-kT), including z=0 and1 by limits. Hence the exact minimum is
that of the convex function

    lambda max(t,a+H z)-q-D z^c,  0<=z<=1.           (6)

If H>=0 both terms depending on z are nondecreasing, yielding z=0. If
H<0, then t<=b<=Binf<a, so the cap in (6) never switches. Differentiation
of this strictly convex function gives z* in the theorem.

For D>=0 we need the opposite extremum at fixed theta_h. It is supplied by
a greedy sequence with at most one fractional coordinate:

    z_i=1 (i<j), z_j=z in[0,1], z_i=0 (i>j),
    theta_h=1-h^j+(1-h)h^j z,
    theta_v=1-v^j+(1-v)v^j z^c.                    (7)

To prove maximality, first truncate to finitely many coordinates. If there
are two fractional coordinates, move a small amount of h-weighted mass
from the latest to the earliest, until the earliest becomes1 or the latest
becomes0. Monotonicity and theta_h are preserved. The derivative of theta_v
per h-weighted unit at coordinate i is

    c (1-v)/(1-h) (v/h)^i z_i^(c-1).

This is nonincreasing in i for a monotone sequence. The transfer therefore
cannot decrease theta_v. Repetition leaves at most one fractional
coordinate, proving (7). Truncation followed by a limit proves the infinite
case; the greedy value in (7) is continuous also at its adjacent interval
boundaries and tends to1 as theta_h tends to1.

On each interval (7), the cost (1) is a concave function of z on either
side of its possible head-cap switch: its only nonlinear term is
-D(1-v)v^j z^c. Thus its minimum is at an interval endpoint or a cap
switch. Endpoints are the step sequences Q^j E_infinity (including j=0
and infinity). When t<=a the cap is always active: both a and Binf are
at least t. When t>a, necessarily b>=t>a and H>0. Moreover

    B(Q E_infinity)=b+h a>b>=t.

Thus the sole cap switch occurs in the first greedy interval, j=0, at
z0=(t-a)/[b-a(1-h)] in(0,1), giving the word and value in (2). The
j=0 step E_infinity is dominated by this switch value since D0>=0.
All j>=1 step words have B>=t, so (3) applies and

    V_(j+1)-V_j=C h^j-D0 v^j.                      (8)

If C<=0 this is nonpositive, and the minimum is its limit at infinity.
If C>0, its sign is that of C-D0 n^j, which is nondecreasing in j and
eventually positive. The first j>=1 making it nonnegative is therefore a
minimizer. Equality merely gives an additional adjacent minimizer. This
proves the complete procedure, including D=0 and all equality cases.

## Finite-word corollary when t<=a

Assume the existing source bounds lambda/n>=1+rS and
lambda b/n>=A:=u+r(1-v). If t<=a, every finite-word comparison against mu
reduces exactly to the direct-axis family E_T and the insertion family E_T Q.
Together with the theorem, these exhaust all comparisons for finite/countable
words and their carrier limits, with absorbing words compared against m.

Indeed, put L_Lambda(D)=Lambda B(D)-U(D)+r(nu(D)-1). For Q this is
Lambda b-A. For an axis block, with z=exp(-kT), it is

    Lambda a(1-z)-(q+r)(1-z^c),

which is nonnegative if Lambda>=1+rS, since 1-z^c<=c(1-z). Grafting gives

    L_Lambda(A0*D)=L_Lambda(A0)
                  +nu(A0)L_{Lambda h(A0)/nu(A0)}(D).

The effective price only increases, because h(A0)/nu(A0)=1/N_p(A0)>=1.
Therefore L_Lambda(D)>=0 for every finite word whenever
Lambda>=max(1+rS,A/b). Write a word containing Q as E_T Q D. After its
first Q the pivot cap is a+(b-a)exp(-kT)>=min(a,b)>=t. Thus the full
head cap branch is active, and adding D changes the objective, divided by s,
by exactly

    exp(-ST)v L_Lambda(D), Lambda=lambda exp((S-k)T)/n,

which is nonnegative. A word without Q combines to E_T. Infinitely many
Q blocks or infinite total axis duration force absorption. Otherwise adjacent
axis blocks combine to give a finite word. The same dichotomy covers limits:
unbounded Q counts or axis durations force nu=0; with both bounded, a
subsequence has bounded word length and convergent finite axis durations.
The corresponding finite-word comparison passes to its limit. No absorbing
comparison against m is replaced by a comparison against mu.

## Complete finite-word tests at every head threshold

Keep the preceding source and notation: a=1/k, q=1/S, c=S/k>1,
0<v<h<1, n=v/h, b>0, 0<=t<=b, and lambda>=1. The headed objective is
K+s f(W), where f(W)=lambda max(t,B(W))-U(W)+r nu(W), s>0,
and K+s f(Q)=mu<m. Write w=u-rv and fQ=lambda b-w. Assume the
previously proved direct-axis, insertion, and absorbing-word tests pass, and

    lambda/n>=1+rS, lambda b/n>=u+r(1-v).             (1)

**Proposition.** Every finite/countable word in Q and inverse-axis blocks,
and every carrier limit, passes the appropriate headed comparison (against
mu if nonabsorbing, against m if absorbing) if and only if the following
additional condition holds when t=b>a:

    u-rv-q >= (q+r)n(b-a)/a.                        (2)

There is no additional condition when t<b or b<=a. Thus the complete word
family adds only this boundary test to the stated tests and bounds.

### Proof

The t<=a case is the earlier finite-word corollary. Suppose a<t<=b. Put

    G=q+r, Binf=b/(1-h), Uinf=u/(1-v),
    H=Binf-a, D=Uinf-q, E=Uinf+r,
    Bc=b-a(1-h), D0=u-q(1-v), L=t-a.

All these quantities are positive. Insertion gives w>q. If t<b, it gives
w-q>=lambda(b-t)/(1-((t-a)/(b-a))^c). Every word beginning with Q is
already dominated by Q: its head cap is active after Q since b>=t, its
suffix coefficient is lambda/n, and (1) makes each subsequent block's
increment nonnegative by the earlier graft identity. Pure axis words pass.

For a word with ell>=1 copies of Q, put z=exp(-k times total axis
duration)>0. Its cumulative axis factors before the Q blocks satisfy
1>=z_0>=...>=z_(ell-1)>=z. Telescoping gives exactly

    B=a(1-h^ell z)+Bc sum_(i<ell)h^i z_i,
    U=q(1-v^ell z^c)+D0 sum_(i<ell)v^i z_i^c,
    nu=v^ell z^c.

At fixed ell,z,B, minimizing cost maximizes the last convex sum. The
h-weighted transfer proof from the absorbing theorem gives a maximizer
consisting of a prefix of1s, one fractional x, and a suffix of z's; derivative
ratios are proportional to (v/h)^i z_i^(c-1), nonincreasing in i. A nonempty
prefix of1s begins with Q and is already dominated. Otherwise the word is
E_T Q E_A Q^(ell-1), with exp(-kT)=x and exp(-k(T+A))=z. For fixed z
its cost is concave in x on each head-cap branch. It suffices to check x=1
(a prefix Q), x=z (E_T Q^ell), or the cap switch B=t.

For E_T Q^ell set

    d_ell=Binf(1-h^ell)-a>0,
    W_ell=Uinf(1-v^ell)-q-rv^ell>0.

The positivity of W_ell follows from W_1=w-q>0. Its cost as a function
of z is lambda max(t,a+d_ell z)-q-W_ell z^c. It decreases below its cap
switch and is concave above it, so its minimum is Q^ell (already dominated)
or the cap-switch cost lambda t-q-L^c W_ell/d_ell^c.

For a general greedy cap switch the formulas are

    Bc x+C_ell z=L, C_ell=hH-Binf h^ell,
    f=lambda t-q-D0 x^c-F_ell z^c,
    F_ell=vD-E v^ell.

When ell>=2, C_ell>=h(b-a)>0 and F_ell>=v(w-q)>0. Since
L<=b-a<Bc, the feasible cap segment runs precisely from z=0 to z=x.
Its cost is concave. The endpoints are the tested absorbing word
E_T Q E_infinity and the cap-switch E_T Q^ell. The former has headed
debt at least m>mu, so supplies no additional finite test.

For ell=1, C_1=-ah and F_1=-Gv. Define

    rho=[D0 ah/(Bc Gv)]^(1/(c-1)).

Along the cap segment x=(L+ah z)/Bc, 0<=z<=L/(b-a). Its derivative
has the sign of (z/x)^(c-1)-rho^(c-1); z/x increases from0 to1. If
rho>=1 its minimum is the endpoint x=z. If rho<1 its unique minimum is

    x*=L/(Bc-rho ah), z*=rho x*,
    exp(-kT)=x*, exp(-kA)=rho.

For t<b, insertion and 1-y^c<=c(1-y) give

    W_1=w-q>=lambda(b-a)/c>=Gn(b-a)/a,               (3)

using lambda/n>=1+rS=cG/a. Hence D0=W_1+Gv>=Gn Bc/a and rho>=1.
For t=b the original Q is the endpoint x=z=1. If rho<1 the interior
minimum is strictly below Q, whereas rho>=1 permits no improvement.
Condition rho>=1 is exactly (2). This proves necessity at that boundary
and shows that every remaining case satisfies W_1>=Gn(b-a)/a.

Finally all cap-switch E_T Q^ell are dominated by the ell=1 switch.
Put d_1=b-a, W_1=w-q and A=u+r(1-v)=W_1+G. Consecutive slopes are

    (W_(ell+1)-W_ell)/(d_(ell+1)-d_ell)=A n^ell/b.

They decrease with ell, so W_ell<=W_1+(An/b)(d_ell-d_1).
From W_1>=Gn d_1/a we get An/b<=cW_1/d_1: indeed
(c b-n d_1)/a=n+(c-n)b/a>c>1. Bernoulli's inequality therefore gives

    W_ell<=W_1[1+c(d_ell/d_1-1)]
           <=W_1(d_ell/d_1)^c.

Thus W_ell/d_ell^c<=W_1/d_1^c. The ell=1 cap-switch is an insertion
competitor, already tested. This finishes all finite words. Infinite Q count
or infinite total axis duration force absorption. Positive-Never limits have
bounded Q count and bounded total axis duration; after combining adjacent
axis blocks, a subsequence has bounded word length and convergent finite
durations. Finite comparisons pass to these limits. Absorbing limits keep
their comparison to m, proving complete exhaustion of this word family.

### Canonical source: no additional finite condition

Suppose additionally r=m/2, mu<r, m<=a-q, and s JQ<=mu, where
JQ=b-u+rv=b-w. These are respectively the canonical source choice, its
subcritical bound, the axis absorbing comparison, and the inherited debt
budget. Then (2) follows already from the absorbing-word comparison, so
there is no additional finite test at any threshold t.

Only t=b>a needs proof. Set x=(b-a)/a, p=c-1 and G=q+r<=(a+q)/2.
If (2) failed, JQ>(a-q)+(a-G)x. The absorbing cap-switch word has
headed debt increase s delta over the source, where

    z0=x/(x+h), delta=W_1-D0 z0^c
         <Gn x[1-(x/(x+h))^p]<=G min(x,p).

The last step uses 1-(1+y)^(-p)<=py and n,h<=1. If x<=p, then
Gx<=(a-q)+(a-G)x because 2G-a<=q and a-q=qp. If x>=p, then
Gp<=(a-q)+(a-G)x because 2G<=a+q and a-G>0. Hence delta<JQ.
But absorption and the debt budget give m-mu<=s delta<s JQ<=mu,
contradicting mu<m/2. This proves the canonical corollary without changing
any absorbing comparison into a finite-word comparison.

## Exact strict separation from prior scalar tests

The following is arithmetic data only. It is not asserted to be realizable
by a reward table or semantic source. Choose

    alpha=k=1, S=2, m=2/5, r=1/5=m/2, mu=11/100,
    lambda=3/2, s=1/2, h=43/50, v=3/5, n=30/43,
    b=21/250, u=1/25, t=3/50, g=9/200,
    e_p(P)=1/10, U_p(P)=93/1000, B_p(P)=29/200.

Then K=7/1000, w=u-rv=-2/25, F(1)=lambda b-w=103/500,
and K+s F(1)=mu. The resulting source scalars are

    B_p(Y)=163/1000>mu, U_p(Y)=113/1000>r nu(Y)=3/50,
    nu(Y)=3/10, d_p(Y)=1/20,
    J_r(P)=19/125>mu, J_r(Q)=41/250>mu,
    mu-s J_r(Q)=7/250>0.

All survival ranges hold, including s lambda=3/4<1. With
A=u+r(1-v)=3/25, the old ratio, removal, repetition, append-axis and
insertion inequalities have the following strict margins:

    Binf-Uinf-m=1/10, b-(m-r)(1-h)=7/125,
    A-(lambda b-g/s)=21/250, lambda b/n-A=303/5000,
    lambda/n-(1+rS)=3/4,
    lambda(1-kb)-(1-Su+rSv)=107/500.

The independent axis bounds also pass: mu<1/7 and m<1/2. Every direct
replacement by E_T passes: its tail-dependent objective is

    Hdir(z)=(3/2)max(3/50,1-z)-1/2+(7/10)z^2.

It decreases to the cap switch z=47/50 and increases thereafter, so
min Hdir=5213/25000, exceeding F(1) by63/25000. The corollary therefore
checks every headed nonabsorbing word against mu.
The two headed absorbing endpoints have debts507/1000 and407/1000,
both above m. In fact every headed Q^j E_infinity passes, since its
tail cost is

    4/5+(3/5)h^j-(2/5)v^j >=4/5.

Even the entire unheaded absorbing word family passes: by the theorem its
minimum is the minimum of 1/2-(2/5)z+(2/5)z^2, exactly2/5=m at z=1/2.
Nevertheless, at exp(-T)=3/4 the headed word E_T Q_infinity has

    B=7/10, U=11/40, lambda B-U=31/40,
    d_p(Phi_P(E_T Q_infinity))=789/2000 < m=800/2000.

The margin is11/2000. Thus the complete headed absorbing-family test is
strictly stronger than all the listed scalar screens, even after all
unheaded absorbing-word comparisons and the headed step family are added.

## A scalar survivor of every word comparison

The full test is not a scalar contradiction. For arithmetic data only, take
alpha=k=1, S=2, r=3/20=m/2, m=3/10, mu=11/100, lambda=11/10,
s=1/2, t=0, K=111/2600, and Q=E_log(13/11). Then
n=h=11/13, v=121/169, b=2/13 and u=24/169. Every word collapses to a
single axis block. Its tail-dependent finite objective is

    f(z)=3/5-(11/10)z+(13/20)z^2, 0<=z<=1.

This is uniquely minimized at z=11/13, where f=7/52 and K+s f=mu.
The headed absorbing debt is891/2600>m, the unheaded absorbing debt is1/2,
and J_r(Q)=31/260>mu with mu-s J_r(Q)=131/2600>0. Also mu<3/26,
the unheaded axis optimum, and n/lambda=10/13=1/(1+rS).
Thus the listed scalar tests and all word comparisons are consistent even
at the canonical parameter choice. This is not an actual game or head.
The remaining question is which additional actual-source relation forces
these tests to fail, or which different zero-observer replacement can improve
a source that passes them.

Source declarations inspected: quittingTerminalSemanticPrefix and
quittingTerminalSemanticPair_rootThenContinuation in
UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean;
quittingContinuationBestResponseValue_rootThenContinuation_eq_max in
UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean. These establish
finite-profile prefix semantics; the retained-query carrier operation and
inverse-axis supply used here are the ordinary mathematical results cited
above. No Lean command ran. Exact control arithmetic was checked with
Python fractions.Fraction; no actual-source realization is claimed.
