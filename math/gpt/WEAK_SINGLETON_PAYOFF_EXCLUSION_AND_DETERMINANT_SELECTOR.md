# Quantitative minimum-cap margins, weak payoff exclusion, and a determinant-clock selector

## Status

This is an ordinary-mathematics proof and a finite, exact-arithmetic regression
record. It has not been formalized in Lean or independently reviewed. The
companion `VERIFY_WEAK_SINGLETON_EXCLUSION.py` uses only Python's standard
library. Its checks establish the displayed finite arithmetic, not the universal
theorems below.

The argument strengthens the universal positive-minimum singleton-cap margin by
an explicit debt-dependent amount. It also removes the strict payoff deficit
and the uniformly nonconcentrated weight hypothesis from the supplied auxiliary-cap producer, when the coordinate
that witnesses the payoff exclusion has a nonnegative own singleton. It also
gives a finite reward-table class to which the stronger producer applies. The
unrestricted four-player conjecture is not proved.

## 1. Model and statements

Let I be finite and nonempty, n=|I|. Nonempty quitting coalition S pays r(S),
Never pays zero, and |r_i(S)| <= M for some M>0. Put s_i=r_i({i}). Strategies are
independent complete stopping laws on the nonnegative integers plus Never.
For an actual profile p, write U_i(p) for its terminal payoff, B_i(p) for its
supremum over ALL unilateral replacements, d_i=B_i-U_i, and D=sum_i d_i.
All finite dates, unbounded stopping laws, private randomization and Never are
included in B_i.

Fix a nonempty subset J of players and suppose s_i>=0 for every i in J. Other
players' singleton rewards may have either sign. Assume the weak exclusion

    (WE_J)  for every actual p, some i in J satisfies U_i(p)<=s_i.

For the construction, it is enough to assume this only for finite root words
followed by all-Never. In the canonical four-player case, all own singletons
are nonnegative, so J can be the entire player set.

**Theorem 1 (weak payoff exclusion).** Under (WE_J), for every epsilon>0 there
are actual independent finite stopping laws with total unrestricted terminal
regret D<epsilon. Consequently the game has a fixed uniform-equilibrium payoff.
For rational data and rational positive epsilon, a terminating rational-grid
algorithm produces such laws.

The number of dates can be bounded, for 0<epsilon<=M, by

    O(n + (M/epsilon)^2 log(16nM/epsilon)).

The constant is absolute. This bounds the number of rows, not the cost of
solving each finite normal-form approximate Nash problem. An explicit
non-asymptotic block bound is given in Section 4.

**Theorem 2 (quantitative minimum-cap and payoff margins).** In an arbitrary
bounded signed quitting game, suppose the compact complete-semantic carrier has
positive minimum total debt D_*. Define, for x>=0,

    Phi_M(x) = (sqrt(2M+x)-sqrt(2M))^2.

At EVERY minimum point (U,B), EVERY player i with s_i>=0 satisfies

    B_i-s_i >= D_* + Phi_M(d_i),
    U_i-s_i >= D_*-d_i+Phi_M(d_i) >= Phi_M(D_*) > 0.   (1.1)

These concern global minimum points, not every positive-debt profile. The
existing inequality is B_i-s_i>=D_*. Formula (1.1) is a quantitative
strengthening and, in particular, rules out equality U_i=s_i. Its proof pays
for the entire solo-prefix block before spending auxiliary-root debt; it does
not presume that the solo rows are exact Nash for their owner.

If all singleton rewards are nonnegative, every cap has a common strictly
positive surplus over the old bound, including zero-debt coordinates. Put

    kappa=Phi_M(D_*),
    theta=kappa/[2(kappa+2M)],
    Lambda=Phi_M(theta D_*)>0.

Then every minimum point satisfies

    B_i-s_i >= D_*+Lambda    for EVERY i.             (1.2)

The estimates are explicit and uniform over the whole minimum fibre. They do
not exclude an arbitrary positive minimum in the interior above these bounds.

Theorem 2 gives a short qualitative proof of Theorem 1. Section 4 supplies an
actual finite-law producer rather than leaving existence at the compact minimum.

## 2. The complete-cap ledger used here

For a product root q, set

    c=prod_i(1-q_i), a=1-c,
    beta_i=prod_(j!=i)(1-q_j), pi_i=q_i beta_i.

Let Q_i be the payoff from Quit now. Write the Continue payoff against
continuation v as H_i+beta_i v_i, where H_i is the passive absorbing
contribution. Literal prefixing of an actual profile has exact semantics

    U'_i=q_i Q_i+(1-q_i)(H_i+beta_i U_i),
    B'_i=max(Q_i,H_i+beta_i B_i).                         (2.1)

The cap formula does not require a best response to attain its supremum.
These continuous maps also preserve the closure of the actual semantic pairs.

Given scalar h>=0, choose a root against v=B-h*1. Let g_i be its ordinary
mixed-action regret against this annotation. The actual prefixed pair satisfies

    d'_i <= c d_i+pi_i h+g_i,
    D' <= D-a(D-h)+sum_i g_i.                            (2.2)

For completeness, let w_i be the mixed root payoff against v. Then

    B'_i <= w_i+g_i+beta_i h,
    U'_i = w_i+c(h-d_i).

Subtract and use beta_i-c=pi_i. This proves (2.2), including its approximate
root version. The exact-root coordinate inequality is the existing auxiliary
Nash debt inequality in the repository; it is not a new result here.

We also use the elementary forcing estimate. If v_i<=s_i-delta, delta>0,
then, with a_i=1-beta_i,

    Q_i-(H_i+beta_i v_i)
      >= beta_i delta-2M a_i
      >= delta-(2M+delta)a.                              (2.3)

This follows by conditioning on whether an opponent quits. It does not require
v_i to lie in the reward box. Therefore an exact Nash root has

    a >= delta/(2M+delta).                               (2.4)

Indeed, otherwise Quit is strictly better for i, forcing q_i=1 and a=1.
If instead each g_i<=delta/4, the same argument gives

    a >= delta/[2(2M+delta)].                            (2.5)

Below that bound q_i<=a<1/2, the Quit advantage exceeds delta/2, and ordinary
mixed regret exceeds delta/4.

## 3. First, the qualitative singleton-boundary exclusion

Let K be the closure of the bounded semantic pairs (U,B). It is compact,
nonempty, and closed under (2.1). Suppose its minimum total debt is D_*>0.
The existing minimum-singleton-margin theorem says at every minimum point

    B_j>=s_j+D_*    for all j.                           (3.1)

One can derive (3.1) directly from (2.2): at a minimum, take an exact root
against B-(D_*-eta)*1, with 0<eta<D_*. Any positive absorption would lower
D. Thus every such root is all-Continue. Finite Nash existence then implies
B_j-(D_*-eta)>=s_j. Let eta decrease to zero.

Suppose, towards contradiction, that a minimum point has U_i<=s_i for some
player i with s_i>=0. From (3.1), nonnegative debts, and sum_j d_j=D_* we get

    U_i=s_i, d_i=D_*, B_i=s_i+D_*,
    d_j=0, U_j=B_j>=s_j+D_*    for j!=i.                  (3.2)

Choose the single fixed hazard

    theta=D_*/[2(D_*+2M)].                               (3.3)

At a root where only i quits with probability theta, player i is indifferent.
For j!=i the Continue-minus-Quit difference is

    (1-theta)(U_j-s_j)
      +theta(r_j({i})-r_j({i,j}))
      >= (1-theta)D_*-2Mtheta=D_*/2>0.                  (3.4)

Thus this is an exact root against U. Formula (2.1) shows that its literal
prefix preserves d_i=D_* and every other zero debt. It is another global
minimum, with U_i=s_i. Apply (3.1) again and repeat the SAME root.

After k prefixes, the outsider payoff is

    U_j^(k)=(1-theta)^k U_j+[1-(1-theta)^k]r_j({i}).       (3.5)

Every one of these minimum points satisfies U_j^(k)>=s_j+D_*. Taking limits
in (3.5) gives the raw-table inequalities

    r_j({i})>=s_j+D_*    for every j!=i.                  (3.6)

Now construct a NEW stationary profile: only i quits, with hazard theta.
This is not an identification of its caps with the limits of the old caps.
Those old caps can contain an escaping counterfactual tail. Instead verify
the new profile directly from (3.6).

The owner gets s_i and cannot improve: a finite own quit pays s_i, and Never
pays zero<=s_i. An outsider j sees i's geometric clock. Let v_j=r_j({i}) and

    Q_j^solo=(1-theta)s_j+theta r_j({i,j}).

By (3.4), now using v_j in place of U_j, Q_j^solo<=v_j. Pure Quit at date t
pays

    [1-(1-theta)^t]v_j+(1-theta)^t Q_j^solo<=v_j.

Never pays v_j, since i quits almost surely. Averaging bounds every randomized
or unbounded replacement. Thus the new profile is exact terminal Nash, in
contradiction to D_*>0. This proves the strict qualitative conclusion of
Theorem 2. The next two subsections give its quantitative refinements.

Under (WE_J), the closed set of possible prescribed payoffs is contained in
{u: some i in J has u_i<=s_i}. Theorem 2 therefore excludes a positive minimum.
Actual profiles with D arbitrarily close to zero follow from the definition of
K. The next section produces finite profiles explicitly.

### 3.1 Quantitative cap surplus pays for a complete solo block

Fix a minimum point and a player i with s_i>=0. Abbreviate D=D_* and set

    d=d_i, e=D-d, z=B_i-s_i-D>=0.

Thus U_i-s_i=e+z. The case d=0 of the cap inequality in (1.1) is the old
margin (3.1). Suppose d>0.

There must be an outsider j with r_j({i})<=s_j. Otherwise every outsider
strictly prefers the passive singleton payoff to its own singleton. A
sufficiently small positive stationary solo-i hazard makes Continue optimal
for every outsider. Since s_i>=0, the explicit unrestricted-deviation check
above makes this an exact terminal equilibrium, contrary to D>0. For a
one-player game that exact equilibrium already exists, so a positive minimum
with this nonnegative-singleton player is impossible.

At the original minimum, every outsider has

    U_j-s_j >= D-d_j >= d.

Fix 0<rho<d. Prefix solo-i roots of the constant hazard

    theta_rho=rho/[2(rho+2M)]

until the first time that some outsider has U_j-s_j<=rho. Before each
prefix, all outsiders strictly prefer Continue: their endpoint advantage is
at least (1-theta_rho)rho-2Mtheta_rho=rho/2. The outsider identified in the
previous paragraph eventually crosses, by geometric convergence toward its
passive singleton payoff. Hence the block is FINITE.

Let x=(1-theta_rho)^k be its joint survival factor. The owner's cap is
constant: Q_i=s_i and B_i>s_i. Every outsider's cap takes the Continue
branch. The EXACT semantics after k roots are consequently

    U_i^k=s_i+x(U_i-s_i), B_i^k=B_i,
    d_j^k=x d_j                   (j!=i),
    D_k=D+(1-x)z.                                      (3.7)

In particular the whole solo block costs at most z in total complete debt.
The owner need not play a best response on these rows. We have neither
assumed nor claimed that D_k decreases.

At the first crossing, some j!=i satisfies

    B_j^k-s_j <= rho+x d_j <= rho+e.                    (3.8)

Now fix 0<delta<d and choose rho<delta. Select an exact auxiliary Nash root
against B^k-h*1, where h=e+delta>=0. At the crossing coordinate the auxiliary
continuation lies at least delta-rho below s_j. The absorption estimate (2.4)
and exact ledger (2.2) give, using global minimality and (3.7),

    D <= D_next
      <= D_k - a(D_k-h)
      <= D+z - (d-delta)(delta-rho)/(2M+delta-rho).

Here D_k>=D, so D_k-h>=d-delta>0. The prefix stays in the SAME compact
behavioral semantic carrier. Rearranging and letting rho decrease to zero
proves, for every delta in (0,d),

    z >= delta(d-delta)/(2M+delta).                     (3.9)

The maximum is attained at

    delta_* = sqrt(2M(2M+d))-2M,

which belongs to (0,d). Substituting yields

    max_[0<=delta<=d] delta(d-delta)/(2M+delta)
      = (sqrt(2M+d)-sqrt(2M))^2 = Phi_M(d).             (3.10)

The maximization can also be verified without differentiation. Write A=2M,
t=delta_*, so d=2t+t^2/A. Then, for every delta>=0,

    t^2/A - delta(d-delta)/(A+delta)
      = (delta-t)^2/(A+delta) >= 0.

Here t^2/A=Phi_M(d), and equality holds at delta=t.

This proves B_i-s_i>=D+Phi_M(d_i). Subtracting d_i gives the first payoff
bound. Since

    D-d+Phi_M(d)=D+4M-2 sqrt(2M(2M+d))

is decreasing in d and d<=D, it is at least Phi_M(D). This completes (1.1).

This is a source-preserving finite expenditure comparison: a bounded solo
block may increase debt by z, but a subsequent literal auxiliary Nash prefix
would decrease it by more than z unless (3.9) holds. No cap replacement,
stationary identification of an escaping tail, or payoff-only reconstruction
enters that comparison.

### 3.2 A common cap surplus, even when the player's debt is zero

Assume now that EVERY s_i is nonnegative. Fix any owner i, let z=B_i-s_i-D,
and put kappa=Phi_M(D)>0. Formula (1.1) gives U_j-s_j>=kappa for every j.
As in Section 3.1, absence of an exact equilibrium forces an outsider with
r_j({i})<=s_j.

First prefix one solo-i row of hazard

    theta=kappa/[2(kappa+2M)].

Every outsider's Continue advantage is at least kappa/2. Every outsider's
new payoff surplus is also at least kappa/2, because
r_j({i})-s_j>=-2M. The owner cap stays fixed, and (3.7) applies.

For any 0<rho<kappa/2, continue with sufficiently small constant solo-i
hazards until an outsider's payoff surplus is at most rho, as before. The
block has survival x<=1-theta, total debt at most D+z, and at the crossing

    B_j^k-s_j <= rho+x d_j <= rho+(1-theta)D.

Given 0<delta<theta D, choose also rho<delta and use the auxiliary scalar
h=(1-theta)D+delta. Exactly the calculation (3.9) now gives

    z >= delta(theta D-delta)/(2M+delta).

Maximizing over delta proves z>=Phi_M(theta D)=Lambda. This proves (1.2),
including d_i=0. Combining it with (1.1) is permissible; it does NOT show
that all auxiliary roots remain all-Continue when the shift exceeds D, and
it does not dispose of the full-debt or reset-rigid interior chambers.

## 4. Finite actual-law algorithm

Start with all-Never:

    U=0, B_i=max(s_i,0), D_0=sum_i max(s_i,0).

If D_0=0, stop. At a fixed working tolerance 0<e<=M, repeat until D<e.
All steps use exact rational arithmetic when the input is rational. Set

    tau=e/8, theta=e/(16M),
    A=tau/(4M+tau),
    eta=A*tau/(8n),
    Delta=A*tau/8.                                      (4.1)

Here Delta is a lower bound on the total-debt expenditure of an accepted
auxiliary prefix.

### 4.1 Charged auxiliary step

If

    min_i(B_i-s_i)<=D-tau,                              (4.2)

take h=D-tau/2 and find a rational root q whose every ordinary regret against
v=B-h*1 is at most eta. Since D>=e, h>=0. A coordinate satisfying (4.2) obeys
v_i<=s_i-tau/2. Equation (2.5) gives a>=A/2, since eta<=tau/8. Thus (2.2) gives

    D'<=D-a*tau/2+n eta<=D-Delta.                        (4.3)

Prefix q to the actual old profile and calculate its COMPLETE new caps by
(2.1). No individual debt is assumed to decrease in this step.

Such a rational root exists effectively. Boolean-game payoffs have absolute
value at most R=M+D_0 throughout the algorithm. Ordinary root regrets are
4Rn-Lipschitz in the hazard sup norm. Approximate an existing exact Nash root
by a grid of mesh at most eta/(4Rn). Exhaustive testing of that finite rational
grid must find an accepted point. Floating-point root solving is optional,
not part of the correctness argument.

### 4.2 The concentrated-debt boundary

Otherwise every B_i-s_i>D-tau. Choose i in J with U_i<=s_i, using (WE_J).
Then

    d_i>D-tau,
    sum_(j!=i)d_j<tau,
    s_i-tau<U_i<=s_i,
    U_j>s_j+D-2tau>=s_j+3e/4    (j!=i),
    B_i>s_i.                                            (4.4)

This is exactly the case in which a scalar auxiliary shift just below D is
not enough to force absorption. It cannot simply be omitted or assigned a
weight bounded away from one.

First test the finite singleton column:

    r_j({i})>=s_j+e/4    for all j!=i.                    (4.5)

If (4.5) holds, only i quitting with hazard theta is exact terminal Nash. The
owner's singleton is nonnegative because i is in J. For the outsiders,

    (1-theta)(r_j({i})-s_j)
      +theta(r_j({i})-r_j({i,j}))
      >= (1-theta)e/4-2Mtheta>0.                         (4.6)

The complete-deviation verification is the geometric-clock argument in
Section 3. Section 4.4 turns this exact stationary profile into finite laws.

If (4.5) fails, prefix solo-i rows of hazard theta until D<e or some outsider
j has U_j<=s_j+e/2. Before each such row all outsiders have U_j>s_j+e/2, so

    Continue_j-Quit_j
      >= (1-theta)e/2-2Mtheta>0.                         (4.7)

The owner need not be root-indifferent: U_i<=s_i, so mixing in Quit raises
its prescribed payoff. Its cap stays fixed at B_i. Every outsider's cap takes
the Continue branch in (2.1). Therefore the exact full-cap ledger is

    U'_i=theta s_i+(1-theta)U_i, B'_i=B_i,
    U'_j=theta r_j({i})+(1-theta)U_j,
    d'_j=(1-theta)d_j                  (j!=i),
    D'=D-theta[(s_i-U_i)+sum_(j!=i)d_j]<=D.              (4.8)

In particular, no cross-player debt recharge is hidden in the solo block.
The outsiders' caps themselves may move; their complete debts obey (4.8).

A row count is available. Some outsider has r_j({i})<s_j+e/4 because (4.5)
failed. Formula (3.5) still gives its payoff after the solo block. Since its
initial payoff and the singleton reward lie in [-M,M], the block stops after
at most

    L(e)=ceil[(16M/e) log(8M/e)]                         (4.9)

rows. Indeed, by then (1-theta)^L*2M<=e/4, so that outsider's surplus is
strictly below e/2. It may stop earlier if D<e.

If D>=e when the outsider threshold is reached, (4.8) retains
sum_(j!=i)d_j<tau, and the selected outsider obeys

    B_j-s_j<=e/2+tau=5e/8 < D-tau.                      (4.10)

Thus the next iteration MUST be a charged auxiliary step. A solo block cannot
restart indefinitely without the actual debt expenditure (4.3).

### 4.3 Termination and the date bound

Let D_in be the debt when a fixed-tolerance stage begins. Apart from a final
stationary exit, every block has at most L(e)+1 rows and spends at least Delta.
Consequently an adequate bound for that stage is

    (L(e)+1) * (ceil(D_in/Delta)+1).                     (4.11)

This proves termination without a compactness or attainment assumption about
a behavioral best response.

For the sharper asymptotic date bound, first run a stage at e=M if D_0>M;
its cost is O(n), since D_0<=nM. Once debt is at most M, run decreasing dyadic
levels until one is at most epsilon. Each level begins with D_in<=2e. For
e<=M,

    Delta=e^2/[512(4M+e/8)] >= e^2/(2112M).

Hence (4.11) is O((M/e)^2 log(8M/e)). The dyadic sum is bounded by a constant
multiple of the last term. The last level can be chosen in (epsilon/2,epsilon],
yielding

    O(n+(M/epsilon)^2 log(16nM/epsilon)).                (4.12)

A stationary exit at an earlier level is truncated directly to the ORIGINAL
target epsilon, not merely to the current working level.

### 4.4 Finite laws after a stationary exit, including signed outsiders

Let v=r({i}) be the solo stationary payoff. Here s_i>=0 and v_j>s_j for j!=i;
outsider v_j and s_j need not be nonnegative. Truncate the solo law after K
rows and replace its remaining mass by Never. Put z=(1-theta)^K. The prescribed
payoff is (1-z)v.

An outsider's finite response before the cutoff has unchanged payoff and is
at most v_j. A late finite response pays

    (1-z)v_j+z s_j<=v_j.

Never pays (1-z)v_j. Thus its full regret is at most z max(v_j,0), even when
v_j<0. The owner has full regret z s_i. Therefore

    D<=nM(1-theta)^K.                                   (4.13)

Taking K>theta^(-1)log(nM/epsilon) gives D<epsilon. At the last or an earlier
dyadic working level, theta is bounded below by epsilon/(32M); the truncation
cost is absorbed by (4.12).

This completes the proof of Theorem 1's finite-law assertion. The construction
is literal prefixing throughout, except for the explicitly verified stationary
exit. It never invokes an arbitrary own-payoff best-response replacement as
though it preserved other players' regrets.

## 5. Uniform horizons and the canonical three-law selector

For a fixed N-date profile followed by Never, prescribed horizon-H average
payoffs differ from terminal payoffs by at most M(N+1)/H. Uniformly over every
unilateral deviation, its average payoff is at most

    B_i+M(N+1)/H.

For late own quits with s_i>=0, discounting the absorbing tail cannot improve
that positive singleton reward. For s_i<0, compare instead with the complete
response that changes the late own quit to Never; this removes a nonpositive
contribution. Earlier opponent absorptions contribute the displayed timing
error. Taking mixtures covers every randomized stopping law. Thus horizon-H
regret is at most

    D+2M(N+1)/H.

A cluster point of the constructed bounded payoff vectors supplies one fixed
uniform payoff target. The finite profile and horizon threshold may depend on
accuracy; the target does not.

For canonical Fin4, s=(1,0,0,0), retain the three nonpivot laws of the output.
The displayed pivot law already has total unrestricted debt below epsilon,
so the optimal full-regret pivot-repair LP has value below epsilon. It is an
explicit feasible competitor. There is no assertion that an arbitrary exact
best response of the pivot would preserve the other three debts.

## 6. A finite determinant-clock reward criterion

Let I={0,1,2,3}. Define

    A={0,1}, B={2,3},
    Z_+={{0},{3},{0,3}},
    Z_-={{1},{2},{1,2}}.

For an actual product of stopping laws put

    x=Pr(terminal coalition A), y=Pr(terminal coalition B),
    z_+=Pr(terminal coalition in Z_+),
    z_-=Pr(terminal coalition in Z_-).

Then

    x y <= z_+ z_-.                                    (6.1)

To prove it, set

    a_1=Pr(T_0<T_2), b_1=Pr(T_2<T_0),
    a_2=Pr(T_1<T_3), b_2=Pr(T_3<T_1).

Interpret Never as greater than every finite time. The two pairs of clocks are
independent. Terminal A implies both forward comparisons; terminal B implies
both reverse comparisons. The two crossed comparison events terminate in Z_+
and Z_-, respectively. Consequently

    x<=a_1 a_2, y<=b_1 b_2,
    z_+>=a_1 b_2, z_->=b_1 a_2,

which proves (6.1). Finite ties are allowed and simply do not satisfy the strict
comparison in question. Never is allowed without any absorption assumption.
This proof distinguishes the two crossed masses rather than replacing their
sum by a square-root bound.

**Theorem 3 (raw-table criterion).** Suppose s_0,s_1>=0; s_2,s_3 may have either
sign. Choose positive a,b,l,m with ab<=lm. Require, for each nonempty S,

    r_0(S)-s_0 <= a*1_{S=A} - l*1_{S in Z_-},
    r_1(S)-s_1 <= b*1_{S=B} - m*1_{S in Z_+}.            (6.2)

All other reward coordinates are arbitrary. These are thirty finite linear
reward inequalities for fixed constants, together with one scalar product
inequality. The game has a uniform-equilibrium payoff and the finite-law
selector of Section 4 terminates.

Indeed, Never contributes -s_0 and -s_1 to the two surplus coordinates, so

    U_0-s_0<=a x-l z_-,
    U_1-s_1<=b y-m z_+.

If both coordinates were positive, multiplication and (6.1) would give

    abxy > lm z_-z_+ >= abxy,

a contradiction. Hence (WE_J) holds for J={0,1}. Theorem 1 applies. No
stationary root, continuation annotation, punishment vector, or chronology
is an input to this raw-table criterion.

## 7. Complete rational fixture and strict separation

Take canonical singletons (1,0,0,0), a=20, b=l=1, m=20. Never pays zero.
The complete table is:

| S | r_0 | r_1 | r_2 | r_3 |
|---|---:|---:|---:|---:|
| {0} | 1 | -20 | 1 | 1 |
| {1} | 0 | 0 | 1 | 1 |
| {0,1} | 21 | 0 | 0 | 0 |
| {2} | 0 | 0 | 0 | 1001/1000 |
| {0,2} | 1 | 0 | 0 | 1 |
| {1,2} | 0 | 0 | 3 | -2 |
| {0,1,2} | 1 | -2 | 2 | 2 |
| {3} | 1 | -20 | 1 | 0 |
| {0,3} | 1 | -20 | 2 | 0 |
| {1,3} | 1 | 0 | -1 | 3 |
| {0,1,3} | 1 | 0 | -1 | 2 |
| {2,3} | 1 | 1 | 1 | 1 |
| {0,2,3} | 1 | 0 | -2 | 1 |
| {1,2,3} | 1 | 0 | 1 | 3 |
| {0,1,2,3} | 1 | 0 | 3 | -2 |

All inequalities (6.2) hold and M=21. At q=(0,0,1,1), both active Quit payoffs
are 1, exceeding their own singleton 0. Thus product-low fails; supportwise
balance and ordered premiums, which imply product-low, fail as well.

The actual pure-B profile has payoff (1,1,1,1), whose surplus over s is
(0,1,1,1). Therefore:

* No strict uniform payoff deficit can hold.
* For any probability weight with max_i w_i<=beta<1, its surplus at this same
  profile is 1-w_0>=1-beta>0. Even a profile-dependent collection of weights
  with such a common bound cannot satisfy the earlier group exclusion.

Moreover the correlated half-A/half-B lottery has payoff

    (11,1/2,1/2,1/2)>s

in every coordinate. Hence no nonzero nonnegative linear functional separates
the full convex hull of terminal rewards below s. The criterion genuinely uses
independent stopping clocks. That correlated lottery is not an implemented
strategy.

These are separations from the named criteria, not from every existing
sufficient equilibrium theorem. The fixture itself is not claimed difficult:
it has an exact one-row mixed equilibrium described next. The class theorem,
not the complexity of this particular example, is the result.

### 7.1 A checked concentrated-debt source and its literal exit

Player 0 plays Never; player 1 quits at date zero with probability 1/200 and
otherwise Never; players 2 and 3 quit surely at date one. The exact semantics
are

    U=(199/200,199/200,1,1),
    B=(11/10,1,1,200199/200000),
    D=22199/200000.

At e=1/10, tau=1/80, the charged-step test fails:

    min_i(B_i-s_i)=1/10>D-tau.

Player 0 is the low coordinate. A solo stationary exit is unavailable because
r_1({0})=-20<s_1. The algorithm therefore prefixes solo-0 rows of hazard
1/3360. The exact first crossing of U_1<=1/20 occurs after 155 rows. Every
row satisfies (4.7), the complete-cap identities (4.8), and nonincrease of
actual total debt. At the crossing,

    D = 1/10 + (3359/3360)^155 * 2199/200000,

approximately 0.11049923928549413, still above e. The auxiliary-step test now
holds. The exact rational root

    q=(1,1/3,10/11,0)

is Nash against the prescribed auxiliary annotation B-(D-1/160)*1. Prefixing
it produces

    U=B=(53/33,-20/11,2/3,14/11).

The checker verifies these COMPLETE caps a second way, by scanning every pure
response date, a date after the cutoff, and Never. This is a 158-row finite
profile, most rows being off-path after the last added root.

The same root followed directly by Never is also exact terminal Nash for this
fixture. The checker records that fact explicitly. The long genealogy is a
regression of the concentrated-debt/solo-run/charged-exit mechanism, not a
minimal profile or evidence that a long chronology is necessary here.

## 8. Verification record and source correspondence

`python VERIFY_WEAK_SINGLETON_EXCLUSION.py` passed. It checks:

* 320 exact rational instances of the scalar maximization identity (3.10);
* every raw-table inequality and the stated criterion separations;
* a profitable membership toggle for every nonempty pure coalition, and a
  profitable outsider response against every one-active-player stationary
  profile in the fixture;
* 1,296 products of half-integer laws on {0,1,Never}, checking (6.1) and the
  weak payoff exclusion exactly;
* the concentrated-debt seed, all 155 solo-prefix cap ledgers, the rational
  auxiliary root, and the final complete caps by an independent forward
  pure-response calculation.

The finite grid is a regression, not a proof of (6.1). Its proof is Section 6.
The exact final strategy is a fixture check, not a proof for every table. The
universal construction is proved in Sections 2--5.

Repository state inspected read-only through the GitHub connector:
`elazarg/UniformEquilibrium`, main at
`88709a1034da3738fcb35ca10fc2cea45bad808d`.

Named sources read directly:

* `AGENTS.md` and `docs/FRONTIER.md`;
* `UniformEquilibrium/Quitting/Terminal/AuxiliaryNashDebt.lean`, especially
  `quittingTerminalSemanticDebt_prefix_le_auxiliaryNash`;
* `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticAuxiliaryNashBudget.lean`,
  especially `minimumTerminalSemantic_singletonMargin`;
* `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticNonnegativeWeightChamber.lean`,
  whose displayed closing theorem requires two positive weight coordinates;
* `MathUE/Probability/IndependentFirstStoppingPair.lean`, for the existing
  disjoint-pair clock interface.

The supplied auxiliary-cap note already proves the exact prefix ledger,
strict-deficit forcing, a rational producer under its stronger hypotheses,
and the nonconcentrated-weight producer. The supplied two-pair note already
uses independent clock comparisons. Those ingredients are credited, not
claimed anew here. The additions are the explicit debt-dependent cap surplus and uniform strict
payoff margin at nonnegative-singleton coordinates of a global debt minimum,
the common strict cap surplus when all singleton rewards are nonnegative,
the concentrated-debt solo
block with a forced charged exit, their weak-exclusion selector, and the
separate-crossed-mass finite table attachment.

No literature-wide priority claim is made from this limited comparison. No
Lean compiler, theorem-level axiom audit, repository edit, commit, branch, or
pull request was used.

## 9. Remaining scope

(WE_J) is sufficient, not necessary. Tables with actual payoffs strictly above
the singleton vector can have equilibria; the supplied paired-cycle producer
already illustrates that. For arbitrary canonical Fin4 the construction can
encounter a profile with every U_i>s_i, and the weak-exclusion hypothesis does
not address that case.

This work does not eliminate the full-debt or reset-rigid residuals in general,
exclude every polynomial nonexistence certificate, or produce a counterexample.
It supplies a complete new boundary consumer and a raw-table producer on the
stated class. It does not claim a general four-player proof or exact terminal
Nash existence for the entire weak-exclusion class.
