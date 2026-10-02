# Bidirectional deadline deviations and a strictly stronger quiet-extension test

## Status and scope

This note proves an ordinary mathematical extension of the capped-clock child
compiler in `CAPPED_CLOCK_DEVIATION_DOMINATION_AND_QUIET_EXTENSION.md`.
It is not a Lean-checked result. No repository files were changed.

The new operation can withdraw a child's scheduled quit at the outsider's
chosen deadline, as well as advance a child's later quit to that deadline.
The two operations use disjoint events in that child's private clock, so
combining them costs the **maximum**, not the sum, of their two weights.

The result is a raw-table sufficient condition for four-player uniform
payoff existence. It strictly contains the previous capped-clock criterion.
An explicit rational table, and its entire radius-1/512 reward neighborhood,
pass the new test while every proper-child instance of the old test fails.
In that neighborhood the full singleton matrix is R0 of degree +1, no
nontrivial stationary-response-invariant partition exists, and no
pure terminal equilibrium exists.

This does not consume the arbitrary strict-pivot source, prove the Fin4
conjecture, or provide a counterexample to it. A further section strengthens
the withdrawal floor using a two-variable stationary-security linear program.

## 1. Game and evaluations

Let I be finite and let each nonempty coalition A have payoff r(A) in R^I.
The first finite minimum of independent private clocks T_i in N union {infinity}
selects the entire coalition attaining that minimum. Infinity means Never and
pays zero. This clock model includes every behavioral strategy and every
complete unilateral replacement in the quitting game.

For a nonincreasing f:N union {infinity}->[0,1], with f(infinity)=0, put

    U_i^f(p) = E[f(tau) r_i(A)],
    B_i^f(p) = sup over all private replacement laws of U_i^f(replacement,p_-i),
    d_i^f(p) = B_i^f(p)-U_i^f(p).

The payoff is defined to be zero on joint Never. Terminal evaluation takes
f(t)=1 for finite t. The H-stage average evaluation, under the repository's
zero-payoff quitting-stage convention, takes

    f_H(t)=max(H-t-1,0)/H.

Normalized discounted evaluations are included too. No supremum is assumed
attained. Write s_i=r_i({i}).

Fix a nonempty proper child S subset I. The child uses the restricted
rewards on coalitions in S. The quiet lift Lp gives every outsider Never.
A child player's payoff and full cap are unchanged by that lift, at every
one of these evaluations.

## 2. The finite raw-table test

For i in S define the computable Never floor

    ell_i = min({0} union {r_i(B): empty != B subset S\{i}}).

For nonempty A subset S and i in A define

    W_i(A) = r_i(A\{i})-r_i(A),       if |A|>=2;
    W_i({i}) = ell_i-s_i.

The empty-coalition reward is never used in the first line. The second line
explicitly includes both possible later opponent absorption and Never.

For each outsider k choose weights a_ki,b_ki >= 0, i in S, satisfying

    (N)  s_k <= sum_i a_ki s_i;

    (F_A) s_k-r_k(A) <= sum_i a_ki [s_i-r_i(A)];

    (J_A) r_k(A union {k})-r_k(A)
          <= sum_{i not in A} a_ki [r_i(A union {i})-r_i(A)]
             +sum_{i in A} b_ki W_i(A).

F and J range over every nonempty A subset S. All coordinates on their
right belong to the literal child table. For a three-player child there
are fifteen displayed inequalities and six nonnegative weights. Computing
ell needs only finite minima. Alternatively expand the three singleton J
inequalities over the possible later coalitions and Never: that gives 24
linear inequalities for a fixed three-player child.

Putting every b_ki=0 recovers the preceding capped-clock test exactly.

### Theorem 2.1: complete deviation domination

Set c_ki=max(a_ki,b_ki). For EVERY actual independent child profile p, EVERY
outsider k and EVERY evaluation f as above,

    d_k^f(Lp) <= sum_i c_ki d_i^f(p).                 (2.1)

The same statement applies simultaneously to all outsiders, with their own
rows of weights. In particular, with

    K=max(1, max_{k outside S} sum_i c_ki),

we have E_f(Lp)<=K E_f(p). The sum-debt version is

    D_f(Lp)<=sum_{i in S}[1+sum_{k outside S}c_ki]d_i^f(p).

This controls all finite deadlines, arbitrarily late deadlines, Never,
and arbitrary randomized complete replacements.

### Theorem 2.2: the original uniform target

If the child has a specified uniform-equilibrium payoff v_S, then the
parent has a uniform-equilibrium payoff v with v restricted to S equal
to v_S. Outsiders can use Never in every selected profile.

For Fin4 and |S|=3, the existing unconditional three-player theorem supplies
the child payoff and profiles. Thus the raw inequalities alone imply UE
for the original signed four-player table. No equilibrium, continuation,
root, or survival schedule is an additional input.

For rational rewards the test is a finite rational LP. A feasible test has
rational weights. Given such weights and a positive rational error, a
terminating enumeration of finite rational child laws supplies finite
parent laws with that full terminal-regret error. This is an existence and
exact-enumeration claim, not an efficiency or calendar-bound claim.

## 3. Actual private clock transformations

Fix a finite outsider deadline t. For a child clock x define

    C_t(x)=min(x,t),
    R_t(x)=infinity if x=t, and x otherwise.

At t=infinity define both maps to be the identity. C advances later clocks;
R withdraws precisely the atom at the deadline and leaves every other atom,
including Never, unchanged.

Let G_i^C(t,T) and G_i^R(t,T) be the change in i's evaluated payoff under
these separate unilateral transformations of a deterministic child tuple T.
Let G_k(t,T) be the outsider's gain from replacing Never by t.

We first prove

    G_k(t,T) <= sum_i [a_ki G_i^C(t,T)+b_ki G_i^R(t,T)]. (3.1)

If t=infinity or the child already absorbs before t, all relevant gains
vanish. If t is before a finite first child date tau with coalition A,
withdrawals do nothing and cap replacements quit alone at t. Write

    alpha=s_k-sum_i a_ki s_i,
    psi=r_k(A)-sum_i a_ki r_i(A).

The outside-minus-child residual is

    f(t)alpha-f(tau)psi
      =[f(t)-f(tau)]alpha+f(tau)[alpha-psi] <= 0

by N and F_A. This includes signed rewards. If the child never absorbs,
N gives the comparison directly.

Suppose next t=tau<infinity. A child i outside A joins A under C_t, and
R_t does nothing. A child i in A is unchanged under C_t. If |A|>=2, its
withdrawal leaves A\{i} at the SAME date and gives exactly
f(t)[r_i(A\{i})-r_i(A)]. If A={i}, withdrawing that lone quit either
reveals a later opponent coalition B or leaves Never. In the former case
its new payoff satisfies

    f(tau')r_i(B) >= f(t)ell_i,      tau'>t,

because ell_i<=0, r_i(B)>=ell_i, and 0<=f(tau')<=f(t). Never also pays
at least f(t)ell_i. Thus the withdrawal gain is at least
f(t)(ell_i-s_i). The J_A inequality proves (3.1).

These cases exhaust all deterministic clock tuples, including all ties
and all Never patterns. For fixed a,b, N,F,J are also NECESSARY for (3.1)
to hold for every deterministic tuple at terminal evaluation. Recover N
using joint Never, F_A using exactly A at date 1 and t=0, and J_A using A
at date 0. In the singleton case choose the later opponent coalition or
Never attaining ell_i. This is necessity for this particular pathwise
compiler, not for every possible equilibrium extension.

### Why the coefficient is max(a,b)

Fix i and write c=max(a_ki,b_ki). If c=0, leave i unchanged. If c>0,
construct one randomized private transformation, with independent random
choices:

* when T_i<t, keep T_i;
* when T_i>t, change T_i to t with probability a_ki/c, and otherwise keep it;
* when T_i=t, change T_i to Never with probability b_ki/c, and otherwise keep it.

At t=Never use the identity. All probabilities lie in [0,1]. Only one
of the advancing and withdrawing events can occur for a given original
clock. Conditional on the whole deterministic tuple,

    c * (expected payoff gain of this single replacement)
       = a_ki G_i^C+b_ki G_i^R.                     (3.2)

For an outsider law nu, sample a private replica Z with law nu, independent
of the child clocks, and use t=Z in this transformation. The resulting
child law depends only on its own original clock and independent private
randomness. It is independent of its opponents and is a legal complete
behavioral replacement.

A common Z can be used to prove the comparison; different child summands
are separate unilateral experiments, not a simultaneously played correlated
profile. Integrate (3.1)-(3.2). Each constructed child replacement gains at
most d_i^f(p). Hence the outsider law gains at most sum_i c_ki d_i^f(p).
Take its full response supremum to prove (2.1). There is no exchange of a
supremum and a limit or expectation.

Equivalently, the four deterministic deadline maps are identity, cap,
withdrawal, and flip (cap on T_i>t and withdrawal on T_i=t). The weighted
combination decomposes into these maps with total nonidentity weight c.
The max coefficient is the smallest normalization that implements both
transition probabilities a/c and b/c in this construction.

## 4. Never relaxation, target selection, and finite laws

If N is omitted, all terminal pathwise comparisons still hold except on
joint child Never. Let

    p_inf=Pr(all child clocks are Never),
    A_k=max(s_k-sum_i a_ki s_i,0).

Then

    d_k(Lp)<=sum_i c_ki d_i(p)+A_k p_inf.             (4.1)

For any child h, capping its clock at larger and larger deterministic
finite dates gives gains converging to s_h p_inf: finite first outcomes
are eventually unchanged and joint Never becomes singleton h. Bounded
convergence and the complete response cap give s_h p_inf<=d_h(p).
Consequently, if s_h>0,

    d_k(Lp)<=sum_i c_ki d_i(p)+(A_k/s_h)d_h(p).       (4.2)

This is a terminal relaxation. Without N, the same finite-horizon inequality
is NOT being asserted merely from a positive singleton.

To preserve a child target, choose child profiles whose uniform errors
tend to zero at that target. For each fixed profile, bounded convergence
of Cesaro payoffs gives terminal delivery at the same accuracy. For each
fixed deviation it also passes the horizon Nash inequality to the terminal
limit. This holds for every deviation, so terminal exploitability is small.
Apply (2.1) or (4.2) to the quiet lifts. Choose a subsequence on which the
bounded outside terminal coordinates converge. Their full terminal payoff
vectors tend to one target v extending v_S, and full regrets tend to zero.
The existing terminal-target uniformization theorem supplies ordinary UE
at that one fixed v.

For rational finite-law production, enumerate finite rational child product
laws, and compute all child pure response values at their displayed dates,
one finite date after the final displayed date, and Never. The maximum is
the unrestricted terminal cap. Child UE, the existing finite-law full-cap
approximation, continuity on each finite menu, and rational density ensure
that a dovetail eventually finds any strictly requested positive regret
accuracy. Lift that law quietly, dividing the requested error by K (or the
factor from (4.2)). This produces actual finite laws, not a payoff-only
realizer.

## 5. Stronger withdrawal floors from a two-variable LP

The Never floor ell_i is not the strongest raw continuation bound available.
For fixed child i, consider the finite LP in h and v:

    maximize v,
    0<=h<=1,
    v<=s_i,
    v <= (1-h)r_i(B)+h r_i(B union {i})
          for every empty != B subset S\{i}.        (5.1)

A finite reward bound permits adding -M<=v<=M without changing the optimum,
so this LP attains its value V_i. Set

    gamma_i=max(ell_i,V_i).

### Terminal strengthening

In every singleton J inequality, ell_i may be replaced by gamma_i.
The same terminal cap bound (2.1), and the same UE consequences, remain
valid. Gamma is an explicitly computed scalar, not an assumed favorable
continuation or a full-cap attainment premise.

To prove it, first take a feasible h>0 in (5.1). Repeating own hazard h
against ANY opponent plans guarantees at least v in terminal expectation.
Condition on a deterministic first opponent date L and coalition B. Before
L any own stop pays s_i>=v. Conditional on own survival to L, the mean
payoff at L is (1-h)r_i(B)+h r_i(B union {i})>=v. If the opponents never
stop, own geometric stopping pays s_i almost surely. Average over arbitrary
opponent clocks to obtain the guarantee.

At an optimal h=0, small positive h gives feasible guaranteed payoffs tending
to V_i, by continuity of the finitely many affine expressions. Thus V_i is
always arbitrarily closely guaranteed, even when the optimum's h=0 would
not itself guarantee a positive payoff on joint Never. The ell_i alternative
is guaranteed exactly by Never. No positive guarantee is assigned to Never.

Change the withdrawal transformation only on the event T_i=t: instead of
Never, use a fresh near-optimal guaranteeing plan starting at t+1. If A has
at least two members, another child still absorbs at t, so the leave value
is unchanged. If A={i}, the legal restart guarantees gamma_i-eta against
the conditional future opponent laws. Advance and withdrawal events remain
disjoint, so the coefficient is still max(a,b). The gain comparison acquires
at most eta*sum_i b_ki error. Let eta decrease to zero after bounding each
actual child gain by its full cap. This proves the exact numerical debt
inequality without a cap-attaining or security-attaining strategy assumption.

### All-evaluation strengthening

For all nonincreasing evaluations f, replace ell_i by

    gamma_i^- = min(gamma_i,0).

This nonpositive bound is attained by some stationary h or by Never. Indeed,
if a positive LP optimum is obtained only at h=0, every passive payoff is
positive and Never guarantees zero. A nonpositive optimum attained at h=0
is no better than the already available Never floor. Otherwise an optimal
positive hazard supplies the bound.

For h>0 and v<=0, every possible own-only stopping payoff is at least v,
and the conditional mean at any opponent stopping date is at least v.
Multiplying by the smaller future evaluation weight preserves the lower
bound f(t)v. Own stopping occurs almost surely on opponent Never. For a
Never plan, nonabsorption has value zero>=f(t)v. The preceding deterministic
first-opponent-date argument therefore proves the evaluated restart bound.
This establishes the all-f version with gamma_i^-.

All these enhancements remain finite raw-table tests. For rational rewards
(5.1) has rational optimal values and rational optimizers; after computing
the floors, the weights are found by an ordinary rational LP. They are
sufficient tests, not a classification of every possible continuation plan.

## 6. A rational strict-separation example

Define the integer base table R below, then define the LITERAL target table

    r_i(A)=R_i(A)-b_i for every nonempty A,
    b=(0,1/16,1/16,1/16),       r(Never)=0.

This is the definition of a new table, not an assertion of strategic
equivalence under terminal translation. All compiler inequalities are
checked directly on r.

| A | R_0 | R_1 | R_2 | R_3 |
|---|---:|---:|---:|---:|
| 0 | 1 | 3 | -1 | -1 |
| 1 | 4 | 0 | -1 | -1 |
| 01 | 0 | 0 | -1 | 0 |
| 2 | 0 | -1 | 0 | 3 |
| 02 | 1 | 0 | 0 | 1 |
| 12 | 2 | -2 | 0 | 1 |
| 012 | 0 | 1 | -1 | 0 |
| 3 | 0 | -1 | 3 | 0 |
| 03 | 0 | -1 | 0 | -1 |
| 13 | 0 | 0 | 0 | 0 |
| 013 | 1 | 0 | -1 | 0 |
| 23 | 0 | 1 | 1 | 1 |
| 023 | 0 | 0 | 0 | -1 |
| 123 | 1 | 0 | 0 | 0 |
| 0123 | 0 | 1 | 0 | 1 |

Use S={0,1,2}, outsider k=3, and

    a=(1/8,0,2),       b_withdraw=(1,0,0),
    c=max(a,b_withdraw)=(1,0,2).

Here s=(1,-1/16,-1/16,-1/16), ell_0=0, and the other withdrawal
weights vanish. In child-coalition order 0,1,01,2,02,12,012, the exact slacks are

    N: 1/16;
    F: 1, 5/8, 17/8, 25/8, 1, 7/8, 17/8;
    J: 1, 1/2, 4, 17/8, 1, 3/4, 1.

They are all strictly positive. Therefore for every child profile and every
nonincreasing evaluation,

    d_3^f(Lp)<=d_0^f(p)+2d_2^f(p),
    E_f(Lp)<=3E_f(p).                                (6.1)

The new move in coordinate 0 is explicit: at the outsider's privately
replicated finite deadline, withdraw a scheduled Quit with probability one;
if the original clock was later, advance it with probability 1/8. Child 2
uses the ordinary cap map. Child 1 needs no response term.

### Every old proper-child LP fails

This statement includes all nonempty proper child subsets, not just the
four triples.

If 0 is outside the child, the outsider-0 Never inequality asks
1<=sum_i lambda_i(-1/16), impossible for nonnegative weights. No positive
child singleton permits its omission.

It remains to consider the seven proper children containing 0.
For S={0} or {0,1}, outsider 2's future comparison at A={0} is

    1 <= 0                    or    1 <= -3 lambda_1,

respectively. Both are impossible.

For the other five children, the following outsider has positive joining
gain exactly one at A=S:

    S=02,03,012,013,023;
    k=1, 1, 3,  2,  1.

The old J right side is identically zero at A=S because every child is
already a quitter. These five LPs are therefore impossible, independent
of their weights. The new withdrawal right side need not be zero there.

### An explicit strategy regression

The date-zero root q=(1/2,1/3,1,0), followed by Never, is exact terminal
Nash at this literal table, with

    U=B=(2/3,-9/16,-11/48,23/16).

The complete immediate/Never/late response values are

| i | Quit at 0 | Never | any finite date >0 |
|---|---:|---:|---:|
| 0 | 2/3 | 2/3 | 2/3 |
| 1 | -9/16 | -9/16 | -9/16 |
| 2 | -11/48 | -17/24 | -35/48 |
| 3 | 5/48 | 23/16 | 23/16 |

Every further finite date has the displayed late value. Thus this table is
not a proposed counterexample. The existence theorem for the full raw
class does not assume or use this particular strategy.

Every nonempty pure first coalition has a strict unilateral membership
toggle of gain at least one; for singleton coalitions the witness is an
outsider join, so no hidden later clock can invalidate it. In mask order
0,1,01,2,02,12,012,3,03,13,013,23,023,123,0123, witness players are

    2,2,0,0,1,1,0,1,1,0,2,2,3,1,0.

The corresponding gains are

    1,1,4,1,1,1,2,1,1,1,1,2,2,1,1.

All Never admits a gain of one for player 0. Consequently no deterministic
profile is terminal Nash.

## 7. A full 60-coordinate open neighborhood

Let rho=1/512. Every literal reward table r' with ||r'-r||_infinity<rho,
and the same zero Never convention, still satisfies the new test with
exactly the weights in Section 6 and its freshly computed Never floors.
Moreover every old proper-child LP still fails.

The floor ell_i is 1-Lipschitz in the reward sup norm. With sum a=17/8
and sum b_withdraw=1, N slack changes by at most (25/8)rho, every F slack
by at most (25/4)rho, and every J slack by at most (33/4)rho. These are
strictly below the displayed minimum slacks 1/16,5/8,1/2. Thus (6.1),
with factor 3, holds throughout this full-dimensional neighborhood.

All nonpivot own singletons remain negative, and s_0 remains positive,
so the Never obstructions for children omitting 0 persist. The positive
blocker and join gaps for children containing 0 were at least one and
change by at most 2rho. Their algebraic obstructions therefore persist too.

### The degree-one matrix and lack of a response quotient

At the center,

    Gamma = [ 0  3 -1 -1
              3  0 -1 -1
             -1 -1  0  3
             -1 -1  3  0 ],

    det Gamma=45,
    Gamma^{-1}=(1/15)[2 7 3 3;7 2 3 3;3 3 2 7;3 3 7 2].

Its inverse is strictly positive and has maximum row-sum norm one.
For the perturbed singleton matrix, ||Delta Gamma||_infinity<=6rho.
The Neumann estimate gives

    ||(Gamma+Delta Gamma)^{-1}-Gamma^{-1}||_infinity
       <=6rho/(1-6rho)=3/253 < 2/15.

Thus its inverse remains strictly positive, and its determinant remains
positive along the segment of matrices. Such a matrix is R0: a nonzero
homogeneous complementary solution with slack w would have x=Gamma^{-1}w>0,
forcing w=0 and then x=0. At right-hand side -1 the unique LCP solution
is x=Gamma^{-1}1>0 with zero slack, and its local min-map degree is
sign det Gamma=+1. Hence the R0 degree is +1 throughout this neighborhood.
This uses the LCP degree convention already stated in the supplied notes.

For the stationary residual Delta_i(q)=(1-alpha_i(q))Q_i(q)-H_i(q), direct
exact computation at q=(1/2,1/2,1/2,1/2) gives

    Delta=(-35/64,-1/8,1/8,-3/8).

These four numbers are pairwise distinct, with minimum separation 11/64.
Every block-constant hazard subspace contains this common half-hazard point.
Any nontrivial response-invariant partition would equate two of these
residuals, which is impossible. A reward perturbation by rho changes each
residual here by at most (7/4)rho, so pairwise distinctness persists.
Thus the only response-invariant partition anywhere in the neighborhood
is the discrete partition, whose quotient has degree +1.

### Further bounded comparisons

Every reciprocal pair of off-diagonal singleton entries keeps the same
nonzero sign in both directions. Hence the escort-edge necessity in the
supplied balanced-cycle results excludes every balanced singleton cycle,
including repeated-owner cycles and cycles on proper subsets.

Each center triple has, after relabeling, matrix

    [0 3 -1;3 0 -1;-1 -1 0]

with inverse

    [-1/6 1/6 -1/2;1/6 -1/6 -1/2;-1/2 -1/2 -3/2].

Its negative diagonal persists in the radius-rho neighborhood: its inverse
norm is 5/2, the triple perturbation norm is <=4rho, and the inverse-change
bound is 25rho/(1-10rho)<1/6. Therefore the inverse-nonnegative triple
inheritance criterion fails throughout this neighborhood.

At equal stationary hazards tending to zero, the singleton-average payoff
has surplus 1/4 over every own singleton at the center. Perturbing the
centered entries changes this limit by at most 3rho/2, so all four surpluses
remain positive. Actual sufficiently small positive hazards therefore give
payoff strictly above every singleton. The strict, group, and weak payoff-
exclusion criteria in the supplied frontier all fail there.

The pure membership witnesses also persist, with gain at least 1-2rho,
and all Never still admits the positive pivot deviation. Thus the whole
neighborhood lacks deterministic terminal equilibria.

These comparisons concern the named tests. They do not assert that this
class misses every other solved class, that its members have no stationary
equilibrium, or that a bounded-period verifier could not recognize an
independently found strategy. The new contribution is a raw-table compiler
that controls every child profile, not the isolated existence of the
explicit regression strategy.

## 8. Arbitrary nonsingleton coordinates within the new cylinder

Keep the center singleton rewards fixed. The thirty-three nonsingleton
entries for recipients 0,1,2 can be chosen arbitrarily, without bounds or
sign restrictions. With the weights of Section 6, the three singleton F
slacks and the N slack are unchanged and positive.

Choose the four recipient-3 entries on nonsingleton child coalitions large
enough to satisfy their F inequalities strictly. Next choose the seven
recipient-3 entries on coalitions A union {3}, nonempty A subset {0,1,2},
small enough to satisfy their J inequalities strictly. Each is a distinct
free coordinate. Their upper bounds use the actual child leave rewards
and the computed singleton withdrawal floor. There are no conflicting
assignments. Thus every selection of the thirty-three child-recipient
collision coordinates admits a nonempty open region of the remaining
eleven coordinates passing the new raw test.

This does not say every completion of the fixed singleton matrix is solved.
It describes precisely which inequality-defined region is produced, and
why that region is nonempty without supplying any desired strategic data.

## 9. Source correspondence and implementation boundary

Existing source inputs:

* `quittingGame_exists_uniformEquilibriumPayoff_threePlayer`
  (`UniformEquilibrium/Quitting/Classification/ThreePlayer/Existence.lean`)
  supplies unconditional child UE.
* `quittingGame_isUniformEquilibriumPayoff_of_terminalNash_tendsto`
  and the all-errors equivalence in
  `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`
  supply the fixed-target terminal-to-uniform consumer.
* `exists_finiteDeadlineTimingProfile_approximation`
  (`UniformEquilibrium/Quitting/Terminal/FiniteMenuFullProfileApproximation.lean`)
  supplies finite-law full-cap approximation for the rational enumeration.
* `CAPPED_CLOCK_DEVIATION_DOMINATION_AND_QUIET_EXTENSION.md` supplies the
  previous a-only raw inequalities, their Never relaxation, and the
  balanced singleton escort comparison.
* `STATIONARY_RESPONSE_QUOTIENT_DEGREE_ESCAPE.md` supplies the precise
  response-invariant partition and LCP degree conventions used in Section 7.

The source inspected through the connector had head
`5aac30ad2553dadd5895dc79fbc4f1f5680d7570`. No Lean compiler was available
locally; no Lean build, theorem-level axiom audit, or publication occurred.
The new clock compiler, finite raw criterion, restart-floor enhancement,
and strict open-set separation are ordinary mathematics proved here.
The companion Python script checks the literal rational certificate and
regression values with exact fractions. Its finite checks do not replace
the general proof.

The unconsumed conjecture-wide task is still to cover arbitrary remaining
tables or exclude their positive-gap sources. In particular, an arbitrary
pivot delay has no new universal cap-control claim in this note.
