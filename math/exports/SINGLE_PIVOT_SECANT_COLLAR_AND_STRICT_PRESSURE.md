# Single-pivot secant collars and a strict pivot-pressure source

## Result and scope

This is an ordinary mathematical counterexample-source reduction, using the existing
single-pivot normalization, complete finite-clock approximation, and maximum-debt
minimum moat. It is not a Lean-checked theorem and does not prove or refute
four-player uniform equilibrium.

The source keeps three own-singleton rewards exactly zero. At the selected table,
EVERY near-minimizer has a positive, quantitative mass on the PIVOT's singleton,
not just on the union of singleton outcomes. On the same actual finite profiles,
the common-calendar tester weights have strictly negative PIVOT pressure. This
produces a finite, almost-best pivot response that removes a fixed amount of pivot
singleton probability, and a legal delay-only modification with at least the same
fixed lower bound on mass loss and arbitrarily small loss to the pivot.

The universal pivot collar follows from a one-coordinate reward secant. It needs
no genericity or special root-realization theorem. The rational frozen coordinates
may also avoid any prescribed finite collection of nonzero rational polynomials.

The strict pressure conclusion concerns the pivot block only. No sign for the sum
of all four owners' pressures is asserted.

## 1. Model and notation

Players are I={0,1,2,3}. A nonempty first quitting coalition A pays r(A), and live
play and Never pay zero. Every player privately and independently selects a clock
in N union {infinity}; infinity denotes Never. This represents the unrestricted
behavioral strategies because the unique live public history is repeated
all-Continue. A unilateral deviation replaces one complete clock law.

Write s_i=r_i({i}). A uniform-equilibrium payoff is one vector v such that
for every epsilon>0 there are a behavioral profile sigma and an integer H_0
with the following properties for every H>=H_0: each prescribed expected
H-stage average payoff is within epsilon of v, and every unilateral
behavioral replacement gains at most epsilon in that average payoff.
The target v precedes epsilon; the profile and threshold may depend on it.

For an actual profile p, write U_i(p) for terminal payoff, B_i(p) for the supremum
over all complete unilateral replies, d_i=B_i-U_i, E(p)=max_i d_i, and
eta(r)=inf_p E_r(p). Suprema include every finite date and Never. No attainment
is assumed for arbitrary opponent laws.

For a fixed table, the semantic carrier is the closure of actual pairs (U,B).
The joint semantic/outcome-law carrier is the closure of actual triples
(U,B,mu), where mu records the probabilities of all fifteen nonempty first
coalitions and the Never outcome. These are finite-dimensional closures;
membership does not assert that the limiting pair or triple is itself actual.

Freeze the 56 reward coordinates other than the own singletons at b, with every
entry in (-1,1). For x in [0,1], let r^x be the table with those frozen entries and
own singleton vector

    (x,0,0,0).

All these tables are unit-bounded. Put

    e(x)=eta(r^x),
    z(p)=Pr_p(first coalition={0}),
    z_u(p)=Pr_(p[0 <- Quit_u])(first coalition={0})   for finite u,
    z_infinity(p)=0.

Outcome probabilities are independent of x. A pure-response gain at r^x is

    g_(i,u)^x(p)=U_i^x(p[i <- u])-U_i^x(p).

There is also a zero tester with gain zero. The pivot-pressure observable of a
profile and probability weights lambda on these testers is

    P_0(p,lambda)=sum_u lambda_(0,u) [z_u(p)-z(p)].

The other owners' testers and the zero tester contribute zero to this observable.

## 2. Main theorem

Suppose some real Fin4 quitting table has no uniform-equilibrium payoff. Then the
following data can be selected before any accuracy or calendar-depth request:

* b in Q^56 intersect (-1,1)^56 and t in Q intersect (0,1), with e(t)>0;
* a positive rational alpha with e(t)>2 alpha;
* a number a with t<a<1;
* one fixed parameter xi in [a,1), and m=e(xi), satisfying

      3 alpha/4 <= m <= alpha.

Write r=r^xi. Its own singleton vector is (xi,0,0,0), with xi>0. The following
conclusions hold. All the constants, source profiles, tester weights, and replies
are produced from the no-UE premise; they are not additional strategic hypotheses.
Conversely, m=e(xi)>0 implies that the selected table has no uniform-equilibrium
payoff. Thus the construction preserves the existence of a counterexample while
restricting its source data.

### 2.1 A universal full-regret / pivot-mass inequality

For EVERY actual behavioral profile p,

    E_r(p)+(xi-t) z(p) >= e(t) > 2 alpha.               (S)

In particular,

    E_r(p) <= m+alpha/4  ==>  z(p) >= 3 alpha/4.        (C)

The more precise lower bound is

    z(p) >= [e(t)-E_r(p)]/(xi-t).

The same inequality holds on the joint semantic/outcome-law carrier by continuity.
Every maximum-regret minimum there has pivot singleton mass at least
[e(t)-m]/(xi-t). Every actual profile with z(p)=0 has exploitability at least e(t),
which is strictly greater than 2m. The bound applies to every actual profile:
there is no support, date, Never-mass, or actual-attainment hypothesis on p.

### 2.2 Same-profile strict pivot pressure

There are actual finite independent profiles p_k, integers N_k tending to infinity,
and probability tester weights lambda_k such that p_k uses only
{1,...,N_k,Never}, and:

    E_r(p_k) -> m;

    sum_A lambda_(k,A) [E_r(p_k)-g_A^r(p_k)] -> 0;

    sum_A lambda_(k,A) D_p g_A^r(p_k)[nu-p_k] >= -o(1)

uniformly for every independent competitor nu on
{0,...,N_k+2,Never}. The tester pool contains every finite reply through N_k+3,
Never separately for every owner, and zero. The derivative is along the product
of the four marginal chords, not a public mixture of joint profiles.

The same weights satisfy

    limsup_k P_0(p_k,lambda_k) <= -alpha/4.             (P)

For every owner i, its total tester weight theta_(k,i) is eventually at least m/4.
After discarding finitely many terms, each selected source also has

    z(p_k) >= 3 alpha/4,
    P_0(p_k,lambda_k) <= -alpha/8.                      (P')

Thus, for every epsilon>0 and requested depth d, one such actual source can be
selected with N>=d, exploitability excess, weighted inactivity and uniform
directional error at most epsilon, and all the fixed strict bounds above.

### 2.3 Produced finite pivot response and delay-only move

The same source can be selected with a deterministic finite reply date T such that

    U_0(p[0 <- Quit_T])-U_0(p) >= m-epsilon,
    B_0(p)-U_0(p[0 <- Quit_T]) <= epsilon,
    z(p)-z_T(p) >= alpha/16.                           (R)

Let T_0 be the original private pivot clock and O=min(T_1,T_2,T_3) the first
opponent clock. Both include Never. Then

    Pr_p(T_0<O<=T) >= alpha/16.                        (W)

The deadline T is selected from the known laws; it does not depend on any realized
private clock. On the event in (W), prescribed play quits with singleton {0}, but
under the replacement an opponent quits by T, either alone with its simultaneous
opponent coalition before T or together with the pivot at T.

There is also the actual private replacement

    T_0^delay=max(T_0,T),

with the other three laws unchanged. It satisfies

    z(p)-z(p[0 <- T_0^delay]) >= alpha/16,
    U_0(p[0 <- T_0^delay])-U_0(p) >= -epsilon,
    B_0(p[0 <- T_0^delay])=B_0(p),
    d_0(p[0 <- T_0^delay]) <= d_0(p)+epsilon.           (D)

No corresponding upper bound on the other three changed debts is asserted.

By passing to a subsequence there is one fixed nonempty opponent coalition A
contained in {1,2,3} for which the event in (W) with first opponent coalition A has
mass at least alpha/112 at every selected source. A further two-way split can fix
whether O<T or O=T, retaining mass alpha/224. Neither the time nor the reward sign
on that event is asserted fixed or favorable.

## 3. The full-cap secant lemma

This argument works for any finite number of players when only one player's own
singleton reward is varied and Never remains zero.

Fix 0<=y<x<=1, put Delta=x-y, and keep one actual profile p. The prescribed pivot
payoff changes by exactly

    U_0^x(p)-U_0^y(p)=Delta z(p).

For every complete pivot replacement q_0, its payoff changes by
Delta times its singleton-0 probability, a number between zero and Delta.
Consequently

    B_0^y(p) <= B_0^x(p) <= B_0^y(p)+Delta.

All prescribed payoffs and all full response caps of the other three recipients
are unchanged: none of their reward coordinates was modified. Taking the maximum
of the four debts gives the sharper one-coordinate bounds

    E_(r^y)(p)-Delta z(p)
      <= E_(r^x)(p)
      <= E_(r^y)(p)+Delta[1-z(p)].                     (1)

These are inequalities of complete behavioral caps, not of a restricted timing
menu. In particular e is 1-Lipschitz, and

    e(y) <= E_(r^y)(p) <= E_(r^x)(p)+(x-y)z(p).        (2)

Equation (S) is (2) with y=t and x=xi. The inequality also explains why the
collar is specifically about the pivot's singleton, rather than total absorption
or total singleton mass.

## 4. The two zero endpoints and rational entrance

At x=0, all own singletons are zero. All Never has payoff and every player's full
cap zero, so e(0)=0.

At x=1, every possible payoff to player 0, including Never, is at most its own
singleton 1. Thus e(1)=0 by the existing maximum-minimum singleton moat. Here is
the short reason, including the semantic issue.

The closure of actual (U,B) pairs is compact, and the prefix map preserves it.
If its minimum maximum debt were m>0, take 0<=h<m and a finite-game exact Nash
root q against the annotation v=B-h*1. If c is joint survival, a_q=1-c, and
pi_i is the probability that only i quits, the exact full-cap prefix calculation
bounds every new debt by

    d'_i <= c d_i+pi_i h <= c m+a_q h.

Positive absorption would make every new debt less than m. Therefore the selected
root must be all Continue. Its Nash inequalities give B_i-h>=s_i, and letting
h increase to m gives B_i-s_i>=m. For player 0 at x=1 this is impossible because
B_0<=1=s_0. Hence e(1)=0. No actual minimizing strategy was required.

The tracked single-pivot normalization first turns any hypothetical Fin4
counterexample into an actual counterexample whose own singletons are (1,0,0,0)
after relabeling. Common positive scaling puts all entries strictly inside the
unit cube and makes the positive singleton lie in (0,1). Scaling by a positive
constant multiplies U, B, E, and eta by that constant, since Never remains zero. The general full-regret
reward-continuity bound preserves positivity under sufficiently small perturbations.
Perturb the 56 frozen coordinates and the positive singleton to rational values,
leaving the three zero own singletons exactly zero. This produces rational b,t with
e(t)>0. Choose a rational alpha with 0<2 alpha<e(t).

More generally, before selecting b one may prescribe any finite collection of
nonzero rational polynomials in its 56 coordinates and require that none vanish
at b. The positive-gap scaled pair has an open product neighborhood in b and t
on which the gap stays positive. The product of the prescribed polynomials is
nonzero and cannot vanish on any open box: induction on the number of variables,
using the finite-root property for a nonzero one-variable polynomial, proves
this fact. Its nonzero set is open and dense. Intersecting with the b-neighborhood
therefore leaves a nonempty open set containing a rational b; choose rational t
in the t-interval. Construct the level window and source sequence afresh at this
b. No particular polynomial, screened-root gap, countable avoidance statement,
or polynomial restriction on the final parameter xi is used or asserted.

## 5. A descending window and the explicit collar

By continuity, e(t)>2 alpha and e(1)=0 imply that the level set

    {x in [t,1]: e(x)=alpha}

is nonempty and compact. Let a be its largest element. Then

    t<a<1,       e(a)=alpha,       e(x)<alpha for a<x<=1. (3)

In particular e<=alpha throughout [a,1]. Define the positive tilt

    c=alpha/4

and the continuous outer objective

    H(x)=e(x)+cx,        a<=x<=1.

For any maximizer xi,

    H(xi)>=H(a)=alpha+ca>c=H(1),

so xi<1. Also

    e(xi)>=alpha-c(xi-a)>=3 alpha/4,
    e(xi)<=alpha.                                      (4)

The construction in Section 6 chooses one such maximizer as the limit of its
finite-calendar maximizing parameters. Thus (4) applies to that same xi.

For every x in [a,1] and every actual profile satisfying
E_(r^x)(p)<=e(x)+alpha/4, equation (2) gives

    (x-t) z(p)
      >= e(t)-E_(r^x)(p)
      > 2 alpha-alpha-alpha/4
       =3 alpha/4.

Since 0<x-t<1, the weaker bound z(p)>=3 alpha/4 follows. This proves (C),
with uniform constants on the ENTIRE descending window, even at parameters where
e(x)=0. Passing actual joint semantic/law approximants to a carrier limit proves
the stated carrier version of (S).

No compact strategy realization or cap-preserving payoff compression is involved.

## 6. Common calendars with one tilted reward coordinate

This section matches the strict pressure to actual near-minimizers and their own
tester weights. The outer optimization is one-dimensional and tilted. The scalar
direction allows one tuple of inner minimizers; no mixture of tuples or played
correlation is needed.

### 6.1 Common smooth objective and uniform approximation

For a large integer k let

    tau=k^(-1/2),        L=2k+1,
    J={zero} union (I times {0,...,L,Never}),
    F(x,p)=tau log sum_(A in J) exp(g_A^x(p)/tau),
    lambda_A(x,p)=exp(g_A^x(p)/tau)/sum_B exp(g_B^x(p)/tau).

For N let X_N be the product simplex on {0,...,N-1,Never}, and set

    f_N(x)=min_(p in X_N) F(x,p),
    eps_k=tau log |J|.

On X_L the tester pool is complete: all later finite replies have the value of L,
whereas Never remains separate. Hence E<=F<=E+eps_k. The tracked reward-uniform
complete finite-clock approximation gives rho_k->0 such that for N>=k,

    e(x)<=min_(p in X_N) E_(r^x)(p)<=e(x)+rho_k

uniformly in x in [a,1]. One available Fin4 choice is rho_k=24/j when
j=floor((k-1)/8)>=1. Indeed, the normalized finite-clock bracket has upper value
at most eta+24/j, attained by an actual profile with clock bound 8j+1<=k. It embeds
in every X_N for N>=k. The exact declarations and the literal full-cap reachable
set are identified in Section 11. Only convergence is used here.

Choose x_k maximizing

    H_k(x)=(1/(k+1)) sum_(N=k)^(2k) f_N(x)+cx

over [a,1]. Uniform convergence H_k->H and compactness give a subsequence with
x_k->xi, where xi maximizes H. In particular e(x_k)->m=e(xi)>0.
Every inner minimizer at every calendar in the window has exploitability tending
to m uniformly over that window.

For large k, x_k<1: the uniform approximation and the strict gap
H(a)-H(1)>=3 alpha/4 exclude x_k=1. Thus the right parameter direction is feasible,
even when x_k=a.

### 6.2 The strict pivot-pressure average

For each fixed N, compactness and uniform differentiability of F give the
one-sided envelope identity

    f_N'(x_k;+1)=min_(p in argmin_X_N F(x_k,p)) partial_x F(x_k,p).

For completeness, evaluating at an old minimizer gives the upper derivative bound.
For the reverse bound, choose new minimizers at x_k+h, pass to a convergent
subsequence as h decreases to zero, and use uniform differentiability and old
minimality. The limit is an old minimizer, giving the claimed minimum derivative.

Since x_k is an outer maximum and rightward motion is feasible,

    (1/(k+1)) sum_N f_N'(x_k;+1)+c<=0.

For each N choose ONE inner minimizer p_(k,N) attaining the minimum derivative.
The only reward coefficient depending on x is the pivot's own singleton, so

    partial_x F(x_k,p)
      =sum_u lambda_(0,u)(x_k,p)[z_u(p)-z(p)]
      =P_0(p,lambda(x_k,p)).

Therefore the actual tuple of selected inner minimizers satisfies

    (1/(k+1)) sum_N P_0(p_(k,N),lambda_(k,N))<=-c.       (5)

The linear tilt has changed zero pressure into a fixed negative pressure.
Neither reward-coordinate normality in the other 59 directions nor a played
mixture of profiles is used.

### 6.3 Calendar telescope and enlarged-direction bounds

Keep the SAME x_k and SAME tester pool J across the whole window. Put

    Delta_N=f_N(x_k)-f_(N+1)(x_k)>=0,
    Hcurv=96+256/tau.

Then sum_(N=k)^(2k) Delta_N<=2+eps_k. Along every independent marginal chord,
the unit reward bound gives |g_A'|<=16 and |g_A''|<=96. To see these bounds,
each varying signed marginal has l1 norm at most two. A bounded four-player
expectation has at most four first-derivative terms, each bounded by two,
and twelve ordered second-derivative terms, each bounded by four. A gain
is the difference of two such expectations; a pure-response expectation
uses no more marginal factors. The second derivative
of log-sum-exp is the weighted mean second derivative plus the variance of the
first derivative divided by tau. Thus F''<=Hcurv.

If the weighted directional derivative at p_(k,N) toward X_(N+1) were -b<0,
a chord step b/Hcurv would lower F by at least b^2/(2 Hcurv). Here b<=16 and
Hcurv>=96, so the step is legal. Comparison with f_(N+1) gives the uniform bound

    sum_A lambda_A D_p g_A[nu-p_(k,N)]
      >=-sqrt(2 Hcurv Delta_N).                         (6)

The entropy identity gives weighted inactivity at most eps_k. The averaged
right side in (6) tends to zero by the telescope and Cauchy-Schwarz.

### 6.4 Silence, transport of the same weights, and selection

Uniformly over all the inner minimizers in the window, eventually

    B_i(r^(x_k),p)-s_i(x_k)>=m/2     for every i.         (7)

Otherwise evaluate a violating sequence at r^xi. Reward continuity and compactness
of the semantic carrier produce a maximum-debt minimum at r^xi violating its
moat B_i-s_i>=m. This reasoning uses no limiting strategy realization.

Shift every finite clock of p_(k,N) up by one, leaving Never fixed. The shifted
profile p_hat is silent at zero and keeps the prescribed law. Its full cap is
max(s_i,B_i)=B_i by (7), so exploitability is unchanged. Recompute its softmax
weights using the same J. Let

    d_N=L-N+1,        a_k=4 exp(-m/(2 tau)).

The old last finite label can be removed with total normalized weight at most
1/d_N, because each owner has d_N identical old late labels. The new initial
labels have total added normalized weight at most a_k by (7). Consequently

    F(x_k,p_hat)<=f_N(x_k)+tau a_k.

For every transported tester observable bounded in absolute value by one, the
old and new averages differ by at most

    4(1/d_N+a_k),                                      (8)

when d_N>=2. This follows directly by comparing their numerators and the partition
sum ratio 1-ell_N+a_N, with ell_N<=1/d_N and a_N<=a_k. It applies in particular
to the pivot-pressure observable; all its nonpivot entries are zero.

Discard the final two calendars. For N<=2k-2, the shifted source and its new weights
have weighted inactivity at most eps_k and, uniformly toward X_(N+3), directional
error at most

    R_N=sqrt(2 Hcurv[Delta_N+Delta_(N+1)+Delta_(N+2)+tau a_k]). (9)

Indeed the source objective is at most f_N+tau a_k, while a competitor belongs to
X_(N+3). The same curvature descent calculation compares with f_(N+3).
The averaged R_N tends to zero: each Delta occurs at most three times in the sum.

The pressure average in (5) changes by o(1) under (8), since the average of
1/d_N is O(log(k)/k), and deleting two calendars costs at most 2/(k+1).
Discard also calendars whose R_N exceeds the square root of its vanishing average.
Their relative mass tends to zero. Pivot pressure lies in [-1,1], so one retained
actual profile and its own shifted tester weights satisfy simultaneously

    R_N->0,        weighted inactivity->0,
    P_0(p_hat,lambda_hat)<=-c+o(1).                     (10)

Only that one profile is played. Averaging calendars is a selection argument,
not public correlation.

The all-owner bound uses the legal competitor which changes only owner i's
marginal to Quit0 and leaves the other three marginal laws unchanged.
At a silent source, every noninitial tester of another owner has gain zero at
that competitor endpoint. Initial joining testers have total weight O(a_k) and
bounded gains. Writing W=sum lambda g and W_i=sum_u lambda_(i,u) g_(i,u), the exact
weighted derivative is

    theta_i(U_i-s_i)-W+W_i + initial-joining terms.

Use W>=E-eps_k, W_i<=theta_i(B_i-U_i), and (9) to obtain

    theta_i(B_i-s_i)>=E-eps_k-R_N-O(a_k).               (11)

Since B_i-s_i<=2 and E->m, eventually theta_i>=m/4 for every owner.

Finally evaluate the selected laws at the ONE fixed table r^xi, retaining their
selected weights. Uniform reward continuity changes exploitability, inactivity,
and the uniformly bounded directional derivatives by o(1). Pressure and prescribed
singleton probabilities are unchanged. This proves (P) and the other source
fields. The collar in Section 5 applies to those same profiles, yielding (P').

Labels later than N+3 may be aggregated at N+3 because their gain functions
coincide on the entire competitor domain X_(N+3); Never remains distinct.
Sum the weights of the aggregated labels. This preserves inactivity, all
directional inequalities, pivot pressure, and owner weights on that domain.

## 7. Extracting a finite almost-best pivot deadline

Fix a sufficiently accurate selected source p, weights lambda, and error epsilon_1>0.
Require

    P_0(p,lambda)<=-alpha/8,
    sum_A lambda_A[E(p)-g_A(p)]<=alpha epsilon_1/64.

Call a tester bad if E(p)-g_A(p)>epsilon_1. Its total weight is at most alpha/64.
Negating the pressure inequality gives a weighted pivot singleton loss at least
alpha/8. Removing all bad testers loses at most alpha/64, because every loss is
at most one. Thus the good pivot testers have weighted singleton loss at least
7 alpha/64. Since their total weight is at most one, some good pivot tester u has

    g_(0,u)(p)>=E(p)-epsilon_1,
    z(p)-z_u(p)>=alpha/16.                             (12)

Also B_0-U_0<=E, so the first inequality yields

    B_0(p)-U_0(p[0 <- u])<=epsilon_1.

If u is finite, this is the desired deadline. If u=Never, write

    W=U_0(p[0 <- Never]),
    Z=Pr(all three opponents choose Never).

All prescribed opponent finite dates are at most N. A reply at T=N+1 has exactly

    U_0(p[0 <- Quit_T])=W+xi Z,
    z_T(p)=Z.                                         (13)

Both W and W+xi Z are full response values. Since B_0-W<=epsilon_1,

    xi Z<=epsilon_1.

All Never has exploitability xi at r^xi, so xi>=m>=3 alpha/4. Therefore
Z<=4 epsilon_1/(3 alpha). Choose epsilon_1<=alpha^2/16. The universal source collar
z(p)>=3 alpha/4 and (13) then give

    z(p)-z_T(p)>=3 alpha/4-alpha/12=2 alpha/3,

which is stronger than alpha/16. The finite reply is at least as good as Never,
so it retains the gain and near-cap bounds in (12). This treats the Never label
without identifying its payoff with zero or assuming opponent absorption.

Choosing epsilon_1 no larger than the requested epsilon, and taking the original
source sufficiently accurate, proves (R) with all the same source fields. Since
E(p)>=m, its gain is at least m-epsilon.

## 8. Waiting flux and the delay-only operation

For a finite T, the singleton events give the pointwise identity

    1_{T_0<O}-1_{T<O}
      =1_{T_0<O<=T}-1_{T<O<=T_0}.                      (14)

Here infinity is ordered after all finite dates, and equal infinities do not
satisfy a strict inequality. In particular, T<O<=T_0 includes the all-Never tuple;
this is correct because a finite pivot reply converts that tuple to a pivot
singleton. Taking expectations gives

    z(p)-z_T(p)
      =Pr(T_0<O<=T)-Pr(T<O<=T_0).                     (15)

Equations (R) and (15) prove (W). The seven possible nonempty first opponent
coalitions partition the first event, giving the alpha/112 extraction. Splitting
at O<T versus O=T gives alpha/224. Finiteness permits a common coalition, and if
needed a common split, along a subsequence as errors tend to zero and calendars
increase.

Now replace the pivot clock by max(T_0,T). This map is applied to that player's
private clock alone, so the new law is independent of the unchanged opponents.
Its singleton indicator is 1_{max(T_0,T)<O}. Thus

    z(p)-z(p[0 <- max(T_0,T)])=Pr(T_0<O<=T).             (16)

Let F_0(u)=U_0(p[0 <- u]) for pure u. Since F_0(T)>=B_0-epsilon and every F_0(u)<=B_0,
affinity in the replaced marginal gives

    U_0(p[0 <- max(T_0,T)])-U_0(p)
      =sum_(u<T) p_0(u)[F_0(T)-F_0(u)]
      >=-epsilon Pr(T_0<T)>=-epsilon.                 (17)

The pivot cap depends only on its three opponents, which have not changed.
Equations (16)-(17) prove (D), including its complete-cap statement.

The favorable total gain of the pure deadline need not occur on the particular
positive-mass event in (W). Its contribution there may have either sign and may
be offset by gains on other clock configurations. No favorable raw reward toggle
is inferred solely from (15).

## 9. Compatibility, scope, and the remaining obstruction

The reduction begins with rational b, optionally avoiding finitely many prescribed
nonzero polynomials as in Section 4, keeps the other three own singletons
identically zero, and produces xi e_0 with xi>0. Common positive scaling
by 1/xi restores the numerical unit-pivot form; all clock probabilities and pressure
bounds are unchanged, while payoff gains and error scales are multiplied by 1/xi.
The resulting reward bound need not remain one.

The final xi need not be rational. Rational approximation of a chosen table does
not automatically preserve its exact outer optimality or its vanishing-error
source sequence. The theorem does not make that assertion.

Neither xi nor r^xi is claimed to maximize the full own-singleton fiber. The
positive level m is selected from a tilted, descending one-parameter window.
Accordingly (P) is a strict sign for the pivot block only. A sign for total
singleton pressure, preservation of a previously selected minimum, and any
prescribed replacement chronology are not additional fields of this source.

The remaining consumer is specific. One must handle an actual near-minimum source
with the universal secant bound (S), together with a finite nearly best pivot
response and a delay-only move that remove a fixed amount of pivot singleton mass.
The own cap stays unchanged, but the other three full caps can increase. Nothing
here shows that the modified profile stays near the minimum, returns with its
singleton-mass loss retained, or has a lower complete maximum regret. Therefore a
bounded singleton mass is not yet a renewable rank.

The result gives no counterexample table and no arbitrary-table low-regret
strategy. It does not establish a cardinal reduction for arbitrary finite player
counts or a normal form for general stochastic games.

## 10. Exact boundary calculations

### Sharpness of the one-coordinate secant

Fix r_0({1})=3/4, r_0({0})=x with 0<=x<=1/2, and set every other reward
entry to zero. All three nonpivot own singletons are zero. At the all-Never
profile, z=0 and E=x, so the upper secant inequality is equality. At the
pure clock profile (0,1,Never,Never), z=1, U_0=x, B_0=3/4, and every
nonpivot debt is zero. Thus E=3/4-x and the lower secant inequality is
equality. The complete pivot cap in this second example is attained by
Never or by a finite date after 1. Both sides of the secant can therefore
be sharp with unrestricted caps.

### Never is not the zero response payoff

Set r_0({0})=xi>0 and r_0({1})=1/2, with all other reward entries zero.
Let player 1 quit at date zero with probability 1-q and Never with probability
q; players 2 and 3 use Never. The pivot's Never response pays
W=(1-q)/2. A finite response after date zero pays W+xi*q and has singleton
probability q. Every other pivot response is no better, so the Never-to-cap
gap is exactly xi*q. This is the correction retained in (13), not an
assumption that Never is worth zero or that opponents absorb surely.

### Waiting flux includes joint Never and deadline ties

For deterministic T_0=0, O=1, T=1, the positive waiting event has mass one,
net singleton loss is one, and the delay-only move loses one singleton unit.
This is the O=T branch, not just strict preemption before the deadline.
If instead all four clocks are Never and T is finite, the original singleton
indicator is zero and the finite response's singleton indicator is one.
The negative event {T<O<=T_0} has mass one; omitting it would falsify (14).
The delay-only map leaves this all-Never tuple unchanged, as (16) requires.

### Unchanged pivot cap does not bound outsider debt

The following complete four-player table has own singletons (1/2,0,0,0):

    r_0({0})=r_0({0,2})=1/2,
    r_1({0})=r_1({0,1})=r_1({0,2})=-1/2,
    every other reward entry is zero.

At clocks (0,Never,1,Never), payoff and full cap are both
(1/2,-1/2,0,0), so E=0. The pivot's finite reply T=1 is also exactly best.
Applying T_0 -> max(T_0,1) changes the clocks to (1,Never,1,Never).
The pivot payoff and cap stay 1/2, and pivot-singleton mass falls from one
to zero. Player 1's prescribed payoff stays -1/2, but Quit0 now pays its
singleton zero, and its full cap is zero. Thus its debt becomes 1/2 and
E becomes 1/2. This is a boundary example for the local delay implication,
not an example satisfying the positive-minimum counterexample premise.
It shows why that implication alone is not a global descent argument.

## 11. Tracked dependencies and formalization interface

The proof uses the following tracked entrance and semantic results:

* `exists_finFour_no_uniformPayoff_iff_exists_singlePivot`
  (`UniformEquilibrium/Diagnostics/Quitting/FinFourSinglePivotNormalization.lean`).
  It supplies an actual no-UE table with one unit own singleton and three zero
  own singletons, without requiring retention of an earlier minimum.
* `abs_quittingTerminalExploitabilityInf_sub_le_of_reward_close`
  (`UniformEquilibrium/Quitting/Terminal/TerminalExploitabilityRewardRobustness.lean`).
  The general perturbation entrance uses this bound. Section 3 proves the sharper
  one-coordinate inequalities needed for the new collar.
* `minimumTerminalSemantic_exploitabilitySingletonMargin`
  (`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPlateauDynamicCostate.lean`).
  The moat is also derived in Section 4. Maximum-debt and total-debt minima are not
  interchanged.
* `escapeAwareQuantileClock_fin4_normalized_quantitative_bracket`,
  `exists_finiteClockSemanticPair_exploitability_eq_upper`, and
  `quantileClockSupport_fin4`
  (`Research/Quitting/EscapeAwareQuantileClockHierarchy.lean`).
  For every unit-bounded Fin4 table and integer j>0, these give a literal
  finite-clock upper value attained at clock bound 8j+1, lying between eta
  and eta+24/j. This proves the uniform approximation used in Section 6.
* `hasEscapeAwareQuantileClockCompression_of_normalized`
  (`Research/Quitting/EscapeAwareQuantileClockTransport.lean`) and
  `quittingFiniteClockSemanticReachable`
  (`Research/Quitting/FiniteClockTerminalSemantics.lean`).
  The only compression premise is the unit reward bound. The finite-clock
  reachable pair is realized by independent actual laws, retaining Never,
  and its second coordinate is the full behavioral cap, not a menu cap.
* `quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
  (`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`)
  and `not_exists_uniformEquilibriumPayoff_iff_exists_terminalExploitabilityGap`
  (`UniformEquilibrium/Quitting/Terminal/ExploitabilityGap.lean`).
  These identify the positive-gap premise with the original UE decision problem.

The remaining mathematical ingredients are finite-game Nash existence,
compactness of finite-dimensional simplices and carriers, and differentiation
of finite smooth sums. The scalar envelope and all common-calendar estimates
needed here are proved in Sections 4–6; no further strategic witness is supplied
as an assumption. The new secant, tilted selection, and response/delay results
are ordinary mathematics to be formalized, not new Lean-checked declarations.

Natural formalization units are the one-coordinate full-cap sandwich; endpoint
zero and the last-level/tilted-window selection; the scalar envelope and modified
common-calendar extraction; finite near-best response selection including the
Never conversion; and the max-clock waiting-flux identities. Their conclusions
must be proved from raw data and the stated positive-gap premise, not stored as
assumed output fields.
