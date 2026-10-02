# Two-pair payoff exclusion and geometric finite-menu selection

## Status and deliverable

This note derives a sufficient reward-table criterion for uniform equilibrium,
and a quantitative finite-menu construction on a canonical four-player
subclass. The construction selects actual independent stopping laws and bounds
unrestricted behavioral regret. It does not solve arbitrary four-player UE.

The arguments below are ordinary mathematics. The rational fixture and stated
constants were checked using the accompanying standard-library Python program
with exact `Fraction` arithmetic. No new Lean theorem was compiled, no source
was committed, and no global priority claim is made.

The main quantitative result is a rational table, and a relatively open
56-dimensional neighborhood of canonical tables around it, for which literal
backward Nash-root recursion produces exact finite-menu Nash profiles with
geometrically vanishing unrestricted regret. This is a raw-table producer,
not a consumer assuming a favorable sequence of responses or continuations.

## 1. Model

There are four players, numbered 0,1,2,3. At each live date, their independent
choices are Continue and Quit. The first nonempty quitting coalition S pays
r(S) in R^4. Infinite all-Continue pays zero. Absorbing rewards are repeated
thereafter in the finite-average formulation.

A behavioral strategy is equivalently an independent stopping law on
N union {Never}. Write U_i for prescribed terminal payoff, B_i for the
supremum over all unilateral behavioral replacements, d_i=B_i-U_i, and
E=max_i d_i. All finite pure stopping times, arbitrarily late dates, privately
randomized complete laws, and Never are included in B_i.

Put s_i=r_i({i}). Define the two mean surplus functionals

    G_A(u) = ((u_0-s_0)+(u_1-s_1))/2,
    G_B(u) = ((u_2-s_2)+(u_3-s_3))/2,

and abbreviate G_A(S)=G_A(r(S)), G_B(S)=G_B(r(S)). These functionals include
passive as well as participating players; they are not the participant-only
premium sums of the supportwise-balance criterion. Let A={0,1}, B={2,3}.

## 2. A complete raw-table UE criterion

**Theorem 1.** Suppose

    s_0+s_1 >= 0,       s_2+s_3 >= 0.

Let a,b,L be nonnegative real numbers satisfying

    a <= b+2L.

Assume the following coordinatewise inequalities on the fifteen terminal rows:

    (G_A(A),G_B(A)) <= ( a,-b),
    (G_A(B),G_B(B)) <= (-b, a),
    (G_A(S),G_B(S)) <= (-L,-L)       for every other nonempty S.

Then the game has a uniform-equilibrium payoff against unrestricted unilateral
behavioral deviations.

Only the two sums of singleton levels must be nonnegative; individual singleton
levels may have mixed signs. There are thirty linear reward inequalities for
fixed a,b,L. No stationary profile, continuation, punishment vector, response
cap, or root selector is an input.

### 2.1 The clock inequality, including Never

For an actual product of stopping laws let

    x=Pr(terminal coalition A),
    y=Pr(terminal coalition B),
    n=Pr(Never),
    z=1-x-y-n.

Then

    sqrt(x)+sqrt(y)+sqrt(n) <= 1,                        (1)

and therefore

    z >= 2(sqrt(xy)+sqrt(xn)+sqrt(yn)) >= 2sqrt(xy).      (2)

Here is a proof that does not require finite support or absorption. For the
independent pair (T_0,T_2), set

    a_1=Pr(T_0<T_2), b_1=Pr(T_2<T_0),
    c_1=Pr(T_0=T_2=Never).

For (T_1,T_3) define a_2,b_2,c_2 in the same way. Each triple has sum at most
one: finite ties are the omitted event. The event A implies both first clocks
are earlier; B implies both second clocks are earlier. Independence between
the two pairs gives

    x <= a_1 a_2, y <= b_1 b_2, n=c_1 c_2.

Cauchy--Schwarz gives (1). Squaring it gives (2). All statements are continuous
in the terminal coalition probabilities and hence hold for their limits.

The bound is sharp. Let players 0,1 independently quit at date zero with
probability p and otherwise Never. Let players 2,3 independently quit at date
one with probability q and otherwise Never. Then

    x=p^2, y=(1-p)^2 q^2, n=(1-p)^2(1-q)^2,

so equality holds in (1).

The two-target square-root inequality is already present in the repository.
The point here is its attachment to a complete equilibrium criterion, retaining
the Never term rather than replacing independent laws by arbitrary coalition
lotteries.

### 2.2 The payoff exclusion

The table inequalities imply

    G_A(U) <= ax-by-Lz - n(s_0+s_1)/2,
    G_B(U) <= ay-bx-Lz - n(s_2+s_3)/2.                 (3)

If x<=y, use the first line, the singleton-sum sign, and (2):

    G_A(U) <= ax-by-2L sqrt(xy)
           <= (a-b-2L)x - b(y-x) <= 0.

If y<=x, the symmetric calculation gives G_B(U)<=0. Consequently

    min(G_A(U),G_B(U)) <= 0                            (4)

for every actual profile and every limit of actual payoff vectors.

### 2.3 Why this proves UE without preserving caps

Let K be the closure of actual semantic pairs (U,B), and D=sum_i(B_i-U_i).
If no uniform payoff exists, the terminal-equilibrium characterization gives
an attained positive minimum D_*>0 on K. At every such minimum the existing
minimum-singleton-margin theorem gives

    B_i >= s_i+D_*.

Writing d_i=B_i-U_i and using sum_i d_i=D_*, we obtain

    G_A(U) >= D_*-(d_0+d_1)/2 >= D_*/2 > 0,
    G_B(U) >= D_*-(d_2+d_3)/2 >= D_*/2 > 0.            (5)

This contradicts (4). Thus the minimum debt is zero, and actual terminal
approximate Nash profiles exist at every positive error. The terminal-to-uniform
fixed-target selection theorem supplies one uniform-equilibrium payoff.

This is the permitted use of payoff-only information: it excludes a necessary
payoff property of a positive semantic minimum. It does not realize a payoff
and infer that its response caps have been preserved.

### 2.4 A short independent derivation of the minimum margin

For completeness, the margin used above has an elementary prefix proof. For a
root q let c be its joint Continue probability, s_i(q) its opponent-Continue
probability, Q_i its Quit endpoint, and H_i its Continue absorbing contribution.
Prefixing a semantic pair (u,B) gives

    u'=F(q,u),    B_i'=max(Q_i,H_i+s_i(q)B_i).

These formulas hold on K by continuity. At a minimum choose an exact root Nash
against v=B-h with h_i>=0. Its Nash payoff w satisfies

    B_i' <= w_i+s_i(q)h_i,
    u_i' = w_i+c(h_i-d_i).

Consequently

    D' <= cD_* + sum_i p_q({i})h_i.

Minimality gives D_*<=D'. Set every h_i=D_*-epsilon for 0<epsilon<D_*.
Since sum_i p_q({i})<=1-c, every such exact root must have c=1. Finite Nash
existence supplies a root, so all-Continue is Nash against B-(D_*-epsilon)1.
Thus B_i-(D_*-epsilon)>=s_i. Let epsilon decrease to zero.

This proof uses no strategic equivalence under a terminal reward translation.

### 2.5 Extension to any finite player set

Theorem 1 also works with arbitrarily many additional players. Fix four
distinct players 0,1,2,3. Replace A and B by any two target coalitions such
that A contains 0,1 and excludes 2,3, while B contains 2,3 and excludes 0,1.
Use the same two surplus means on these four coordinates and impose the same
inequalities at every other nonempty coalition. The remaining players' reward
coordinates are unrestricted.

The cross-pair proof still bounds x and y, and the probability that everyone
Never is at most c_1c_2, so (1) persists. At a positive minimum over all players,
d_0+d_1<=D_* and d_2+d_3<=D_*, so (5) persists. This is a sufficient class for
arbitrary finite player sets, not a reduction of arbitrary games to this class.

## 3. Quantitative canonical subfamily

For the rest of the note assume s=(1,0,0,0) and strengthen the table test to

    (G_A(A),G_B(A)) <= (1,-3/4),
    (G_A(B),G_B(B)) <= (-3/4,1),
    (G_A(S),G_B(S)) <= (-1,-1)           otherwise.       (6)

**Lemma 2.** Every actual prescribed payoff satisfies

    min_i(U_i-s_i) <= -3/8.                              (7)

Proof. Write p=sqrt(x), q=sqrt(y), t=sqrt(n). From (1), p+q+t<=1. Equation
(3) and z=1-p^2-q^2-t^2 give

    G_A(U) <= 2p^2+(1/4)q^2+(1/2)t^2-1,
    G_B(U) <= (1/4)p^2+2q^2+t^2-1.

For 0<=p<=1/2,

    G_A(U) <= 2p^2+(1/2)(1-p)^2-1 <= -3/8.

The final quadratic is convex, so its maximum on that interval occurs at an
endpoint; the endpoint values are -1/2 and -3/8. For 1/2<=p<=1,

    G_B(U) <= (1/4)p^2+2(1-p)^2-1 <= -7/16.

The corresponding endpoint values are -7/16 and -3/4. At least one coordinate
in a group is at most that group's mean, proving (7).

## 4. A general actual-tail forcing lemma

This lemma is independent of the particular two-pair test. Let a canonical
single-pivot table be bounded by M>0. Suppose a number kappa>0 satisfies

    for every actual profile, min_i(U_i-s_i)<=-kappa.     (8)

Assume its three singleton joining gains obey

    g_j=r_j({0,j})-r_j({0}) >= 0           (j=1,2,3),      (9)

with g_k=g>0 for at least one fixed outsider k. Let L_0>=0 be an upper bound
on U_k for all actual profiles; max(0,max_S r_k(S)) is sufficient. Define

    alpha = kappa*g / [4M(L_0+g+kappa)] > 0.              (10)

**Lemma 3.** Every exact independent root Nash against the payoff of any
actual tail satisfies

    1-product_(j!=0)(1-q_j) >= alpha.                    (11)

Thus it forces absorption by somebody other than the exceptional pivot. It
is not enough merely to lower-bound joint absorption.

Proof. Let a be the left side of (11), and suppose a<alpha. Since alpha<1,
every outsider has positive Continue support. Put t=q_0 and compare the root
to the row (t,0,0,0), retaining the literal continuation U. Each endpoint
changes by at most 2Ma under this coupling, so each Continue-minus-Quit gap
changes by at most 4Ma. Exact root Nash therefore gives, for every outsider j,

    (1-t)U_j - t g_j >= -4Ma.                            (12)

For the fixed k, U_k<=L_0 gives

    (1-t)(L_0+g) >= g-4Ma > 0.

Hence t<1 and

    1-t >= (g-4Ma)/(L_0+g).

Using g_j>=0 in (12) yields

    U_j >= -4Ma/(1-t)
         >= -4Ma(L_0+g)/(g-4Ma) > -kappa.                (13)

The last strict inequality is precisely a<alpha. The pivot also has positive
Continue support. Comparing its endpoints with those against all-Continue
opponents gives

    U_0 >= 1-4Ma > 1-kappa.                              (14)

Together (13)--(14) contradict (8). This proves (11).

There is no cap installation in this argument. Every root is tested against
the payoff of its actual tail. The rewards of profiles with unrelated
continuation annotations are immaterial.

## 5. The literal finite-menu producer

**Theorem 4.** Under (8)--(9), with alpha as in (10), define

    sigma^0 = all-Never,
    choose ANY exact product Nash root q^n against U(sigma^n),
    sigma^(n+1) = q^n :: sigma^n.                        (15)

Every sigma^N is an actual independent profile on

    {0,1,...,N-1,Never}.

It is exact Nash for that finite stopping menu and satisfies

    d_j(sigma^N)=0                  (j!=0),
    E(sigma^N)=d_0(sigma^N) <= (1-alpha)^N.               (16)

In particular, N>=ceil(alpha^(-1) log(1/epsilon)) suffices when 0<epsilon<1.
This is a bound on the number of dates, not a claim about bit complexity or
the runtime of the finite Nash solver.

Proof. At the all-Never source, the complete debt vector is (1,0,0,0).
For any actual semantic pair and an exact root against its prescribed payoff,

    B_i'=max(Q_i,H_i+s_i(q)B_i),
    U_i'=max(Q_i,H_i+s_i(q)U_i).

The positive-part Lipschitz bound gives

    0<=d_i'<=s_i(q)d_i.                                  (17)

Thus the three zero debts stay exactly zero. Lemma 3 gives
s_0(q^n)<=1-alpha, and iteration proves (16). Supremum attainment is never
assumed; the cap formulas and (17) cover all complete behavioral deviations.

For exact finite-menu Nash, induct on N. At N=0 the only menu action is Never.
At the next date a pure menu response either Quits immediately or Continues
and uses a previous-menu response. The latter has optimal value U_i(sigma^n)
by induction. Exact root Nash makes their maximum exactly the new prescribed
payoff. Mixing complete stopping laws does not improve a maximum of these
pure-time payoffs.

Equivalently, the outsiders' late finite deviations equal Never because their
singletons are zero. The pivot's only additional payoff after the menu is its
singleton reward times the probability that all three opponents Never. That
probability is at most product_n s_0(q^n)<=(1-alpha)^N. This also explains why
(11), rather than merely joint absorption, is the decisive forcing conclusion.

### Selection of the three laws in the original question

Take sigma^N_1,sigma^N_2,sigma^N_3 from (15). The prescribed pivot law already
gives unrestricted exploitability at most (1-alpha)^N. Consequently the
finite optimal pivot-repair LP has value at most that number. The selected
opponent laws were produced from the table, not assumed to exist. No assertion
is made that an own-payoff best response by the pivot preserves the bound;
the stated LP minimizes total exploitability over pivot laws.

### Fixed uniform payoff and horizons

Compactness gives a cluster point v of U(sigma^N). Choose N along that cluster
sequence so both its payoff error and (16) are small. For fixed sigma^N and
horizon H>=N+1, prescribed average payoff differs from terminal payoff by at
most M(N+1)/H. Under any unilateral deviation, opponent absorption occurs by
N-1 or never. Deviator absorption after that date yields its nonnegative
singleton (1 for the pivot, zero for the others); delaying this cannot raise
its finite-average payoff above its terminal payoff. Early-absorption timing
changes contribute at most M(N+1)/H. Hence finite-horizon gain is at most

    (1-alpha)^N + 2M(N+1)/H.

This supplies one fixed uniform payoff target without claiming convergence of
the entire arbitrarily selected backward-root sequence. The constructed
profiles are not claimed to be full terminal epsilon-Nash at every suffix.

## 6. A rational four-player fixture

The complete table is as follows; Never pays (0,0,0,0).

| S | r_0(S) | r_1(S) | r_2(S) | r_3(S) |
|---|---:|---:|---:|---:|
| {0} | 1 | -2 | -15/4 | 0 |
| {1} | -5/2 | 0 | 1 | -3 |
| {2} | -7/4 | -5/4 | 0 | -5/2 |
| {3} | -2 | -3/4 | -4 | 0 |
| {0,1} | 2 | 1 | -3/4 | -3/4 |
| {0,2} | -3 | 1/2 | 1/2 | -13/4 |
| {0,3} | -7/4 | 1/2 | -9/4 | 1/4 |
| {1,2} | -3/2 | -3/2 | -2 | -3/2 |
| {1,3} | 1/2 | -2 | 1/2 | -15/4 |
| {2,3} | 1/4 | -3/4 | 1 | 1 |
| {0,1,2} | 0 | -3 | 7/4 | -17/4 |
| {0,1,3} | 5/4 | -9/4 | 0 | -4 |
| {0,2,3} | -1/2 | -5/2 | 3/2 | -15/4 |
| {1,2,3} | -3/4 | -1/4 | -1/2 | -9/4 |
| {0,1,2,3} | -1 | -7/4 | -7/2 | 3/2 |

The checker verifies every inequality in (6), with

    M=17/4, kappa=3/8,
    (g_1,g_2,g_3)=(3,17/4,1/4).

Select observer k=2. Then L_0=7/4 and g=17/4, so

    alpha = 1/68,
    E(sigma^N) <= (67/68)^N.                              (18)

N>=ceil(68 log(1/epsilon)) is sufficient.

### Separation from the named earlier raw-table criteria

At q=(1,1,0,0), both active Quit payoffs exceed their own singleton levels:

    Q_0=2>1,   Q_1=1>0.

Thus product-low fails, and so do supportwise weighted balance and ordered
premiums, each of which implies product-low. This is a separation of table
criteria, not a claim of exclusion from every other known equilibrium class.

Furthermore, the correlated half-half lottery over A and B gives

    [r(A)+r(B)]/2 = (9/8,1/8,1/8,1/8)
                 = s+(1/8,1/8,1/8,1/8).

Therefore no nonzero nonnegative linear functional separates the entire
convex hull of terminal rewards below the singleton vector. The payoff
exclusion genuinely uses independent-law restrictions, not a linear social
payoff inequality on the convex hull. The displayed correlated lottery is
not implemented as a strategy.

Exact finite checks also show that every nonempty pure terminal coalition
has a profitable membership toggle, and that no exact root has two sure
quitters. The latter check enumerates all six choices of two sure players,
all supports of the two remaining players, and explicitly rules out the
one-mixed-player degeneracies. It does not rule out a unique sure quitter
with a suitable punishment tail or all other existing sufficient classes.

### Realizable continuations matter

The exact root

    q=(1/100,1/10,0,0)

is Nash against the annotation

    v=(3/2,1/33,0,0).

Every active quitter is strictly above its singleton payoff. The exact
Quit/Continue endpoint pairs, checked by the script, are

    player 0: (11/10,11/10),
    player 1: (1/100,1/100),
    player 2: (-767/4000,129/2000),
    player 3: (-373/1000,-1191/4000).

This annotation has no coordinate below its singleton by 3/8, so Lemma 2
shows that it is not an actual-tail payoff. The example is not a refutation
of an existential favorable-root condition: other roots at this annotation
may exist. It shows why forcing proved for actual tails must not be silently
extended to arbitrary box annotations.

## 7. A full-dimensional robust canonical neighborhood

Fix the own singleton entries and perturb every other entry of the fixture by
at most eta=1/16 in absolute value. There are sixty terminal payoff entries
and four fixed singleton equalities, hence this is a 56-dimensional box in
the canonical affine space. Its relative interior is open.

For every actual profile, each prescribed payoff changes by at most eta;
Never remains zero. Thus (8) holds with kappa'=3/8-eta=5/16. Every joining
gain changes by at most 2eta, so all three remain positive. For observer 2,
valid common constants are

    M'=69/16, L_0'=29/16, g'=33/8.

The forcing lemma then gives

    alpha' = 11/920,
    E(sigma^N) <= (909/920)^N.                            (19)

Using a lower bound g' in place of the exact joining gain is safe: the proof
uses that lower bound directly, and g/(L_0+g+kappa) increases with g.

Throughout this neighborhood the pair-A product-low violation remains strict.
The correlated lottery remains at least 1/16 above s in every coordinate,
so the convex-hull separation also remains impossible. No claim is made that
the absence of two-sure roots has been checked throughout the neighborhood.

## 8. Source correspondence and limits

The inspected repository is elazarg/UniformEquilibrium at commit
`88709a1034da3738fcb35ca10fc2cea45bad808d`.

Existing sources used or compared:

- `MathUE/Probability/SquareRootCoalitionClock.lean`: disjoint-pair clock budgets.
- `MathUE/Probability/IndependentFirstStoppingPair.lean`:
  `twoDisjointFirstStoppingPairMasses_sqrt_sum_le_one` for arbitrary complete laws.
- `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticAuxiliaryNashBudget.lean`:
  `minimumTerminalSemantic_singletonMargin` and the positive-minimum plateau.
- `UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`: the semantic
  prefix cap/debt identities used in the attached unique-sure and cap-clock notes.
- `UniformEquilibrium/Quitting/Terminal/PivotRepairBehavioralInfimum.lean`:
  `exists_objective_minimizer_eq_behavioral_infimum` identifies optimal repair
  against fixed finite opponent laws with the finite LP value.
- `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`:
  the terminal-all-errors to fixed uniform-payoff consumer, also described in
  the supplied supportwise-weighted and ordered-premium notes.

The additional conclusions derived here are the two-pair payoff criterion,
its finite-player extension, the quantitative actual-tail opponent forcing
lemma, and their composition into the displayed geometric finite-menu selector.
The Python checker establishes the finite fixture arithmetic, not these
infinite-strategy theorems. Those proofs are given in the body of this note.

The no-general-consumer warnings in the supplied cap-clock and installation
notes are unaffected: horizontal cap installation can still replenish others'
caps. The present construction avoids that operation entirely. It uses exact
Nash prefixes from the canonical all-Never source and forces the deleted
opponent clock directly from the table.

For arbitrary canonical Fin4 rewards, the payoff-deficit property and the
joining inequalities are not established and can fail. Therefore this is a
complete sufficient-class result, including an explicit selector on a robust
region, not a solution of the unrestricted Fin4 conjecture or a counterexample.
