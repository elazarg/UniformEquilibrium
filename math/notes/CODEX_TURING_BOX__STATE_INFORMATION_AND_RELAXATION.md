# Target-free convex relaxation with honest recovery

Identity: CODEX_TURING_BOX.

Sections 13–14 contain a direct producer independently checked by
CODEX_NASH_BOX and CODEX_EMMY_BOX, with bounded source-coverage comparisons.
Its canonical self-contained mathematical export is
[`FOUR_JOINT_PHASE_UNIFORM_EQUILIBRIUM`](../exports/FOUR_JOINT_PHASE_UNIFORM_EQUILIBRIUM.md):
a four-date cycle of proper joint roots produces exact terminal equilibria
with32 locally controlled coordinates,12 upper-only coordinates and16
arbitrary finite coordinates, without public signals or supplied strategic
witnesses. This is reviewed/exported ordinary mathematics, not checked Lean
or arbitrary-Fin4 coverage. Section 12 records why universally dispersing
a canonical positive pivot cannot replace these macroscopic simultaneous
atoms.

Section 14 gives the coordinate strengthening by full-deviation payoff
monotonicity. CODEX_EMMY_BOX independently checked its exact support and
transfer. The export includes this strengthened source-to-UE conclusion.

Section 15 gives a second independently checked producer on an unbounded
reward region. Its canonical self-contained export is
[`FOUR_JOINT_PHASE_RECTANGLE_UNIFORM_EQUILIBRIUM`](../exports/FOUR_JOINT_PHASE_RECTANGLE_UNIFORM_EQUILIBRIUM.md).
It replaces local Jacobian inversion by opposite rectangle-face signs,
while retaining exact paired singleton identities and four sufficiently
negative collision barriers. Section 16 is a separate, unreviewed exact
calculation: a local exact periodic continuation can turn out of the legal
hazard region at its first inactive wall. It does not exclude distant
equilibria or unrestricted approximate strategies.

Section 17 points to the existing reviewed singleton-concentration repair
and its growing-period source composition. Our reconstruction duplicated
that result and supplies no new mathematical coverage. The remaining
all-hazards-small source-selection problem is still open.

Section 18 gives an unreviewed, exact grammar falsifier: even on the fixed
paired singleton matrix, no uniformly bounded-period producer restricted
to at most two active players per root covers every collision completion.
The exhibited family is solved by a sure triple, so this is not a new UE
exclusion or a refutation of a solved-game-or-pair-source disjunction.

Section 19 is independently reviewed ordinary mathematics for a passive-
reward ray with fixed paired singletons and no persistent-base exit. A
symmetric/asymmetric branch switch produces exact private-clock terminal
equilibria and fixed-profile uniform payoffs for every K>=0. Its bounded
source comparisons are not an exhaustive classification. The remaining
global question is how to select collision/clock compensation from arbitrary
reward data, not how to widen this particular family.

Section 20 closes a separate exact-equilibrium nonattainment test by an
explicit asymmetric equilibrium. It supplies no new reward-class claim.

Section 21 tests a genuinely different auxiliary source: small NEGATIVE
private planned-Never taxes with jointly changing finite menus. An explicit
proper-sentinel seed and a private pivot ladder produce good taxed Nash laws
on the existing rational common-menu obstruction. This is an unreviewed
source calibration on an already-solved table, not arbitrary-table coverage.
Section 22 gives an independently bounded-checked falsifier of that UNIVERSAL source:
after making the sentinel's realized rewards positive, EVERY exact taxed
finite-menu Nash law waits until the last date, for all nonpositive tax
magnitudes. Small taxes then leave a fixed ORIGINAL full-deviation gap.
CODEX_NASH_BOX checked all four nonpositive tax coordinates, all Nash
components, private-payment rescaling, backward induction and the uniform
full gap. This is ordinary mathematics, not a Lean check, UE counterexample
or counterexample-class exclusion; the same table has explicit original
exploitability1/N. The universal negative-tax exact selector is retired.

Section 23 tests the ENTIRE realized-absorption discounted Nash source,
with nonstationary clocks and selective Never allowed. The source exists
automatically; whether its best original regret tends to0 remains open.
An exact switching calibration defeats a fixed-active-face heuristic,
and Section23.4 gives a bounded independently checked producer of GOOD growing-period
components on Solan's already-solved three-player calibration. Its geometric
joiner bursts have macroscopic physical absorption and vanishing discount
loss, so original FULL regret tends to0. This refutes the proposed global
corner-confinement estimate, not the entire discounted selector. The missing
operation is now production or selection of favorable components from
arbitrary genuinely four-active tables.

Section25 supplies a four-active stress test with no exact stationary
terminal Nash profile. The exact support-by-support proof below is ordinary
unreviewed mathematics, not a whole-game obstruction. A separately recorded
rational period12 joint calendar has full regret below1/300; the live
constructive question is whether overlapping three-player seams support an
all-errors rule rather than a fixed two-actor alphabet.

Section25.3 gives a complete ordinary proof candidate excluding an entire
all-conditional-hazards-small approximate-equilibrium mode for EVERY fixed
bounded collision completion of these paired singleton columns. It uses
one legal finite suppression deviation and a finite hazard-time interval;
no compactification or assumed complementarity adapter remains in that
argument. This is not independently checked, not arbitrary-Fin4 coverage,
and not a UE counterexample: a prospective equilibrium may retain large
conditional hazards and change its whole calendar across accuracies.

Status of the earlier relaxation sections: ordinary mathematical proof draft,
not checked in Lean and not an export. Their main candidate theorem permits
one convexification of the
complete payoff/cap state followed by an arbitrary finite independent prefix.
It preserves the zero set of the target-free exploitability value, with a
modulus independent of prefix length. A fixed bound on nested public-signal
rounds is also covered, with a bound that deteriorates with the number of
rounds. No arbitrary-game equilibrium producer is supplied.

Sections 3--6 passed a bounded independent mathematical check by
CODEX_EMMY_BOX, recorded in
[`the owned review`](../feedback/CODEX_TURING_BOX__STATE_INFORMATION_AND_RELAXATION__BY_CODEX_EMMY_BOX.md).
That check is not an export gate and does not audit a public-signal producer.
In particular, the result must not be read as a uniform rounding theorem for
unbounded public-signal trees. A source audit below finds no fixed-depth
premise in the known general sunspot producer.

A separate concrete alternative below replaces iid public roots by private
marginal hazards when the conditional total hazard is uniformly small.
That result permits unboundedly many draws, but no retained public-signal
state. Section 9 also passed CODEX_EMMY_BOX's bounded independent check,
including the time-inhomogeneous extension, deleted rates and Never. A
source-matched limitation of that operation is recorded in Section 10.
That composition also passed the same bounded independent review. None
of these reviews claims a new reward-table producer or an export gate.

## 1. Question and exact semantics

Let I be a finite nonempty player set of size n, and let
r(S) in R^I be a reward vector for every nonempty S subset I. Assume
|r_i(S)| <= R, where R > 0. Every player independently samples a date in
N union {Never}; the earliest finite date produces its nonempty quitting
coalition, and joint Never pays zero. A unilateral deviation replaces the
player's entire independent date-or-Never law. Before absorption the only
public history is the date and the fact that all players have continued.

For a profile sigma write U_i(sigma) for its terminal expected payoff and
B_i(sigma) for the supremum over every complete unilateral behavioral
replacement. Thus B_i is the supremum over all pure finite dates and Never,
including dates later than every proposed prefix. Put

    D_i(u,b) = b_i-u_i,
    d(u,b) = max_i D_i(u,b).

Let K be the compact closure of the actual pairs (U(sigma),B(sigma)), and
eta = min_{z in K} d(z). Every z in K has D_i(z) >= 0 and all its coordinates
in [-R,R]. Let T_w be exact semantic prefixing by an arbitrary finite word
w of independent Boolean roots.

The question is whether allowing a convex seed destroys the target-free
existence problem:

    rho = inf { d(T_w zbar) : w finite, zbar in conv K }.

The convex seed is an analytic relaxation. It is not declared to be an
available correlated strategy, and its barycentric payoff is not declared
to be an equilibrium target. Can rho=0 be rounded to genuine approximate
equilibria without tightness or one limiting stopping law?

## 2. Bounded source lookup

Navigation used `docs/FRONTIER.md`, the controller--tester route, and
`docs/TOOLKIT.md`, its common-quantile and terminal-semantic entries. The
following exact declarations and files were inspected under their imports;
no Lean build was run in this mathematical session.

- `quittingUniformEquilibriumPayoffConjecture`,
  `UniformEquilibrium/Quitting/Conjecture/Basic.lean`.
- `quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`,
  `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`.
- `isUniformEquilibriumPayoff_iff_diagonal_mem_terminalSemanticCarrier`,
  `UniformEquilibrium/Quitting/Classification/Existence/UniformPayoffTerminalSemanticCarrier.lean`.
- `quittingTerminalSemanticPair`, `quittingTerminalSemanticPrefix`, and
  `quittingTerminalSemanticDebt`,
  `UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`.
- `quittingTerminalSemanticDebt_nonneg_of_mem_carrier`,
  `UniformEquilibrium/Quitting/Root/TerminalSemanticDebt.lean`.
- `quittingTerminalSemanticPrefix_within` and
  `quittingTerminalSemanticPrefix_within_of_opponentContinueMass_le`,
  `UniformEquilibrium/Quitting/Root/TerminalSemanticPrefixMetric.lean`.
- `quittingFinitePrefixSemanticEval`,
  `UniformEquilibrium/Quitting/Terminal/TailCompression/ElementaryTailSemanticReduction.lean`.
- `terminalSemanticCarrier_eq_closure_neverGeneratedSemanticReachable`,
  `UniformEquilibrium/Quitting/Root/NeverGeneratedSemanticCarrier.lean`.
- `quittingControllerTester_reachableClosure_eq_carrier`,
  `UniformEquilibrium/Quitting/ControllerTester/ControllerValue.lean`.
- `exists_finiteDeadlineTimingProfile_approximation`,
  `UniformEquilibrium/Quitting/Terminal/FiniteMenuFullProfileApproximation.lean`.
- `quantileClockSupport`, `quittingQuantileClockCompressedProfile`, and
  `pmfPi_pureDeviationActiveCompressedLaws_eq_map`,
  `UniformEquilibrium/Quitting/Paths/CommonQuantileClockTransport.lean`.
- `SignedTwoPlayerExactNashNonattainment.not_exact_terminal_nash`,
  `UniformEquilibrium/Quitting/Examples/SignedTwoPlayerExactNashNonattainment.lean`.
- `comparisonProfile`, `comparisonProfile_exploitability`, and
  `comparisonTarget_isUniformEquilibriumPayoff`,
  `UniformEquilibrium/Diagnostics/Quitting/FinFourHardDeadlineTimingNashBarrier.lean`.
- `sqrt_exactFiniteFirstStoppingPairMass_add_sqrt_le_one`,
  `MathUE/Probability/IndependentFirstStoppingPair.lean`, with its literal
  independent marginal-law hypotheses and proof split into overlapping
  and disjoint pairs.

The narrow nearby search checked convex-hull, mixture, Jensen, scalarized-debt,
and finite-prefix terminology in the root, controller--tester, and existence
subtrees. The candidate rounding statement was not found in that lookup.
This is not a global novelty audit.

Conference comparisons inspected: `arch/SUFFICIENT_STATE.md`,
`arch/SUFFIX_INFORMATION_OBSTRUCTION.md`,
`arch/STATE_TOPOLOGIES_AND_APPROXIMATION.md`,
`arch/EXECUTABLE_COMPACT_STATE.md`, `arch/CONTROLLER_VS_TESTER.md`,
`arch/FINITE_WINDOW_SEMANTIC_VALUE.md`, and
`arch/SEMANTIC_BARRIER_DUALITY.md`. Their compactness and reconstruction
claims are not hypotheses of the proof below.

## 3. Exact finite-prefix formulas

Fix a word of H independent roots with Quit probabilities q_i(t), t < H.
Put

    c_i = product_{t<H} (1-q_i(t)),
    S = product_i c_i,
    L_i = product_{j!=i} c_j.

Here c_i is the player's own prefix survival, S the joint prefix survival,
and L_i the opponents' prefix survival. All lie in [0,1], and c_i L_i=S.

For a pure deviation that quits at t < H, let Q_i(t) be its complete terminal
payoff against the opponents' prefix. This value includes earlier opponent
absorption, and it is independent of the continuation. Let P_i be the
expected payoff from opponent absorption before H when i always continues
through the prefix. Put M_i=max_{t<H}Q_i(t); if H=0 use M_i=-R.

There is a constant G_i, independent of the tail, such that for every
abstract pair z=(u,b) in the box,

    U_i^w(z) = G_i + S u_i,
    B_i^w(z) = max { M_i, P_i + L_i b_i }.                 (1)

The second formula is exact for actual tails: deviations quit before H, or
continue through H and then choose an arbitrary complete tail replacement.
The former give the Q_i(t); the latter have cap P_i+L_i b_i. It then agrees
with the iterated abstract prefix map by its defining root recursion. For
H=0 it gives max{-R,b_i}=b_i throughout the box.

More explicitly let

    alpha_i(t)=q_i(t) product_{s<t}(1-q_i(s)).

These are the probabilities of i's own first prefix Quit. Independence gives

    G_i = sum_{t<H} alpha_i(t) Q_i(t) + c_i P_i,
    sum_{t<H} alpha_i(t) + c_i = 1.                        (2)

Equation (2) can also be seen by conditioning on i's own prefix date. When
i survives the prefix, opponents have already absorbed with contribution
P_i, or all opponents survive and the continuation contributes L_i u_i.

Consequently, for every z with b_i>=u_i,

    D_i(T_w z) >= S D_i(z) >= 0.                         (3)

Indeed B_i^w>=Q_i(t), and B_i^w>=P_i+L_i b_i, so (2) gives

    U_i^w <= (1-c_i)B_i^w + c_i(B_i^w-L_i(b_i-u_i))
            = B_i^w-S(b_i-u_i).

Finally, for i!=j,

    L_i L_j = S product_{k notin {i,j}} c_k <= S.         (4)

No division by a survival probability occurred in (1)--(4), so these formulas
include surely absorbing prefixes and literal S=0.

## 4. One convex seed, arbitrary prefix: recovery theorem

It is useful to state the result for a more general source family F. Assume
F is a nonempty family of box pairs with nonnegative debts, closed under
every finite product-root prefix. Set eta_F=inf_{z in F}d(z).

Take a finite mixture zbar=sum_a p_a z_a of elements z_a in F, with p_a>0 and
sum_a p_a=1. Fix any word w and put epsilon=d(T_w zbar). By (3), epsilon>=0.
Then the following two estimates hold:

    eta_F <= n epsilon/S                         if S>0, (5)
    eta_F <= epsilon+2R sqrt(S)+2RS              always. (6)

Proof of (5). Equation (3) gives S D_i(zbar)<=epsilon for every i. Since
debt is affine in z,

    sum_a p_a sum_i D_i(z_a) <= n epsilon/S.

Choose an a whose total debt is at most this average. Its maximum debt is
no larger than its total debt, so it proves (5). Notice that this branch
selects the unprefixed source constituent. It need not preserve a proposed
barycentric payoff target.

Proof of (6). Choose i maximizing L_i. Equation (4) implies

    L_j <= sqrt(S)       for every j!=i,

because L_j^2<=L_iL_j<=S. Choose a constituent z_a=(u^a,b^a) with
b_i^a<=bbar_i. Such a constituent exists by the definition of the average.
Equation (1) and monotonicity of the maximum imply

    B_i^w(z_a) <= B_i^w(zbar).

For j!=i, the same formula is L_j-Lipschitz in b_j, so

    B_j^w(z_a) <= B_j^w(zbar)+2R sqrt(S).

For every j,

    |U_j^w(z_a)-U_j^w(zbar)| <= 2RS.

Thus d(T_w z_a)<=epsilon+2R sqrt(S)+2RS. Prefix closure puts T_w z_a in F
and proves (6). When n=1 the statement about j!=i is empty and the estimate
still holds. When S=0 all the displayed error terms vanish: the selected
prefixed constituent has debt at most epsilon exactly.

Since S<=1, (6) is at most epsilon+4R sqrt(S). Split at

    S0 = (n epsilon/(4R))^(2/3).

If S0<=1, use (5) for S>=S0 and (6) for S<=S0. If S0>1 the bound is trivial
from eta_F<=2R. This proves the word-length-independent estimate

    eta_F <= h(epsilon),
    h(x) = x+(4R)^(2/3)(n x)^(1/3).                    (7)

For epsilon=0 use (5) when S>0 and (6) when S=0; there is no need to divide
by S0=0.

For F=K, every chosen source constituent lies in the genuine semantic
carrier. It need not be an actual profile. A sequence of actual profiles
approximates it, and any fixed word w acts continuously; hence the selected
prefixed pair is likewise approximated by actual prefixed profiles. To get
an actual delta-approximate equilibrium, choose the relaxed epsilon small
enough that h(epsilon)<delta/2 and approximate the selected carrier pair
with additional maximum-debt error below delta/2.

There is no joint-law realization of zbar in this construction. There is no
common clock, tight stopping-law limit, ancestry between accuracies, or
public coin to execute. One constituent is selected during the mathematical
construction, and its independent behavioral approximant is used alone.

## 5. Consequences and scope

Since K subset conv K and the empty word is allowed, rho<=eta. Conversely
(7) gives eta<=h(rho), by approximating the infimum. Therefore

    rho=0 if and only if eta=0.                           (8)

For four players, (7) reads

    eta <= epsilon+4 R^(2/3) epsilon^(1/3).

There is also a quantitative positive-gap version. If eta_F>0, then every
relaxed prefixed pair has

    d(T_w zbar) >= eta_F^3/(64 n R^2).                   (9)

To verify (9), if epsilon>=eta_F/2 it follows from eta_F<=2R. Otherwise
(6) gives sqrt(S)>=eta_F/(8R), and (5) gives
epsilon>=eta_F S/n>=eta_F^3/(64nR^2). Literal S=0 cannot occur in this
second case.

In particular, the closed prefix orbit of conv K is a larger invariant
semantic set whose debt floor remains positive whenever eta>0. It contains
conv K, not merely K. This is a consequence about barriers for a supplied
game, not a newly constructed counterexample or a strict reward-table
classification.

This theorem removes a particular proof-language restriction: target-free
existence does not require every relaxed state or its barycentric payoff to
be realized by one actual stopping law. It does not prove that rho=0 from
arbitrary rewards. The source problem has been relaxed, not solved.

The uniform-payoff quantifiers are unchanged. For the fixed game, first
construct one family with actual terminal debt tending to zero. Select ONE
payoff limit v along a subsequence. Then, for every requested accuracy,
choose a sufficiently late member of that same subsequence close to v.
The target v is fixed before that accuracy quantifier; it is not selected
again separately for each accuracy.

## 6. Bounded-depth public-signal trees

Define an auxiliary class recursively. F_0 is the actual semantic family
(or its compact closure). An element of F_d is a finite independent prefix
followed, if the prefix survives, by one publicly observed fresh draw from
a finite distribution of elements of F_{d-1}. Players and a deviator see
that draw before choosing continuation actions. Prefix lengths and the
number of outcomes may be arbitrary. Leaves use actual independent
behavioral profiles. There are at most d draws on every surviving branch.

The payoff and cap of the draw are both their averages: the deviator sees
which child has been selected and may choose its complete strategy for that
child. Thus its semantic pair really is the convex average. Each F_d is
prefix-closed and has nonnegative debts. This is an auxiliary stronger
information model used only for analysis.

Let eta_d=inf_{z in F_d}d(z). Applying (7) to F_{d-1} gives

    eta_{d-1} <= h(eta_d).

For every fixed finite d,

    eta_0 <= h composed d times (eta_d),
    eta_d=0 if and only if eta_0=0.                     (10)

The constructive extraction follows the two branches of the lemma. The
large-survival branch selects one child and drops the preceding prefix.
The small-survival branch selects one child and keeps that prefix. In
either case the first public draw is removed, leaving a tree of depth at
most d-1. Applying the extraction repeatedly produces an actual profile,
with a worsened error tending to zero for fixed d.

The resulting actual target is selected afterward using compactness of its
payoff vectors. It need not equal the public model's averaged target.

The bound deteriorates roughly through exponent 1/3^d. It is not uniform in
d. No flattening of arbitrary trees to the one-draw class is asserted, and
no claim is made for an unbounded number of signals as accuracy tends to
zero. The max in the cap formula is exactly where naive flattening changes
the deviator's information.

There is now an exact limit on improving this extraction merely by a
better whole-tree account. Proposition 4 of the neighboring
[`Emmy notebook`](CODEX_EMMY_BOX__OBJECTIVES_AND_GLOBAL_SELECTION.md)
gives finite half-hazard one-owner words followed by ACTUAL Never with
private full debt at least 1/48, but H fresh public owner draws with full
debt 2^(-H). Any extraction using only child selection and keep/drop of the
existing roots stays in that restricted word family. Thus such an
unchanged-root operation has no depth-independent modulus tending to zero.
The example does not refute uniform recovery that synthesizes new product
roots; its family is not closed under all legal prefixes. The proof passed
my bounded check in the neighboring owned feedback.

There is a precise joint accuracy/depth consequence of (9). Put
A=8 sqrt(n) R. Since eta_d>=eta_{d-1}^3/A^2, induction gives

    eta_d >= A (eta_0/A)^(3^d).                         (11)

Thus a supplied depth-d tree of full error epsilon gives

    eta_0 <= A (epsilon/A)^(1/(3^d)).                  (12)

In particular a family with errors epsilon_m tending to zero and depths
d_m would suffice if

    log(A/epsilon_m)/3^(d_m) tends to infinity.         (13)

For example d_m=o(log log(1/epsilon_m)) suffices. This is a source-level
accuracy/information-complexity test, not a claim that the known general
sunspot construction satisfies it. No fixed-target claim is used in its
derivation.

## 7. Fixed-target decoding really can fail

This example is already recorded independently in
[`CODEX_BROUWER__QUITTING_TABLE_COVERAGE.md`](CODEX_BROUWER__QUITTING_TABLE_COVERAGE.md),
under "Why this is not an independent-law existence proof." It is not new
reward-table coverage. It makes the difference between the two consumers
exact.

On Fin4 let every reward be zero except

    r({0,1})=(1,1,0,0),       r({2,3})=(0,0,1,1).

The profile in which players 0,1 quit at the first date and players 2,3
choose Never is exact terminal Nash with payoff x=(1,1,0,0). The selected
pair already receives the maximal reward 1; an outsider cannot obtain a
positive reward by deviating alone because its required partner chooses
Never. Reversing the pairs gives an exact Nash payoff y=(0,0,1,1).
Thus ((x+y)/2,(x+y)/2) is a diagonal point of conv K.

Nevertheless the barycentric target v=(1/2,1/2,1/2,1/2) cannot even be
approximated by actual prescribed payoffs. Every independent profile has
payoff (a,a,b,b), where a,b are the probabilities that the exact first
quitting coalitions are {0,1} and {2,3}. The inspected theorem
`sqrt_exactFiniteFirstStoppingPairMass_add_sqrt_le_one` in
`MathUE/Probability/IndependentFirstStoppingPair.lean` gives

    sqrt(a)+sqrt(b)<=1.

This inequality passes to closure. If the maximum payoff error from v is
delta<1/4, then a,b>1/4, contradicting the inequality. The lower bound
1/4 is attained as follows: players 0,1 surely quit at date 1, while each
of players 2,3 independently quits at date 0 with probability 1/2 and
otherwise chooses Never. Then pair 23 absorbs at date 0 with probability
1/4, and pair 01 absorbs at date 1 exactly when 2,3 both chose Never,
also with probability 1/4. Consequently
v is not a uniform-equilibrium payoff, despite being a relaxed diagonal.

Target-free recovery is unaffected: this game already has the genuine
targets x,y and zero. The recovery theorem selects a target afterward;
it does not decode the particular barycenter v. Thus preservation of the
relaxed payoff is a dispensable proof-language requirement for the
terminal-all-errors existence consumer, not a game-semantic requirement.

A preliminary two-player illustration using the midpoint of targets 0,1
was false, because 1/2 is a uniform two-date exact equilibrium payoff.
That failed illustration is not used above.

## 8. Actual public-signal source audit

The bounded-depth premise was tested against Solan and Solan,
*Quitting Games and Linear Complementarity Problems*, accepted manuscript
dated May 1, 2018, Sections 2.1--2.2 and 3.3.5; see the
[primary manuscript](https://econ.biu.ac.il/sites/econ/files/seminars/sunspot11.pdf).
Theorem 2.4 provides sunspot approximate equilibria. Its model reveals a
fresh independent public signal before every live decision. Section 3.3.5
uses randomly sized kiloblocks, with new type draws after blocks. It does
not supply a fixed bound on the number of revealed draws as accuracy
improves. Finite signal alphabet and finite signal depth are different.
In that branch the block lengths make the sole active player's hazard
smaller than the accuracy parameter; the block type and kiloblock counter
are retained public state, not a current-signal-only root kernel.

The tracked `Literature/SolanAndSolan2020.lean` was inspected at `Table`,
`SoloExitNormalized`, `TablePayoffsBounded`, `SunspotProfile`,
`SunspotEpsilonEquilibrium`, `theorem2_13_sunspot`, and `theorem2_4` with
its proof. Its public-signal state returns to a new draw after survival.
Its normalization subtracts own singleton constants from all outcomes,
including Never; translating back is necessary for the present zero-Never
semantics. No production import or Lean trust claim is made here.

Finite censorship of a supplied sunspot strategy can control all terminal
deviations, as the earlier Brouwer note calculates, but its required signal
depth may depend on accuracy. Hence that censorship plus (10) is not an
arbitrary-game independent equilibrium producer. This attempted source
application presently fails on quantitative information complexity, not on
the size of the signal alphabet or source bookkeeping.

## 9. An actual alternative operation: small iid roots can be rebalanced

This theorem changes the roots rather than freezing a public seed path.
It is a separate ordinary mathematical proof draft, not a new arbitrary-game
source theorem. A narrow search for iid-signal, categorical-coupling and
marginal-hazard terminology in the stationary/root subtrees and the tracked
Solan--Solan transcription found no matching statement; that is not a
global novelty claim.

At every live date draw a fresh iid public signal omega, then independently
let player i Quit with conditional probability q_i(omega). The prescribed
q depends ONLY on the current signal, not on earlier signals or a retained
public macrostate. The public deviator is unrestricted and may remember all
signals. Suppose, almost surely,

    sum_i q_i(omega)<=delta<=1.

Let lambda_i=E[q_i(omega)]. Construct an actual private stationary profile
with independent Quit hazard lambda_i for player i at each date, with Never
included by its usual geometric stopping law. If the public profile has
maximum full terminal debt epsilon, the private profile has debt at most

    epsilon+8R delta,                                  (14)

and its prescribed payoff differs coordinatewise by at most 4R delta.
Neither bound depends on time or the number of signals.

Proof. We compare processes for any subset J of players, including J=I
and every deleted-player set I\{i}. Put L=sum_{j in J}lambda_j<=delta.
The public one-date coalition law mu is the mixture of product Bernoulli
laws q_J(omega); the private law mu' is product Bernoulli lambda_J. Compare
both to the categorical law nu on subsets of J given by

    nu(empty)=1-L,       nu({j})=lambda_j,
    nu(S)=0 when |S|>=2.

For mu, its empty mass is at least 1-L by the union bound and each singleton
mass is at most lambda_j. Therefore the total-variation distance, using
the convention TV=(1/2)sum absolute differences, is exactly

    beta=TV(mu,nu)
        =sum_j E[q_j(1-product_{k!=j}(1-q_k))]
        <=E[sum_{j!=k}q_j q_k]
        <=delta L.                                    (15)

The same argument gives

    beta'=TV(mu',nu)<=sum_{j!=k}lambda_j lambda_k
                      <=L^2<=delta L.                 (16)

Choose maximal couplings of each law with the same categorical draw.
Because all nu's empty mass can be matched to empty, a categorical
Continue forces both other coalition draws to be empty. Independent
copies of these couplings may be used at every date. If L=0 all three
processes always continue and agree. If L>0, at the first categorical
Quit, the probability that either actual coalition fails to match that
singleton is at most

    (beta+beta')/L<=2delta.                             (17)

Before that date both processes have continued. Hence their complete
first-coalition outcomes agree outside an event of probability 2delta.
The prescribed payoff comparison for J=I is at most 4R delta.

For J=I\{i}, insert the same deterministic Quit date of player i in both
opponent systems, or insert Never. Agreement survives until the prescribed
date or opponent absorption; all-Never also agrees. Thus EVERY pure-date
or Never response payoff differs by at most 4R delta, uniformly over the
date. Every complete private replacement is a mixture of these pure dates.
The public cap is at least the supremum over the same responses ignoring
the signal. Consequently

    B_i(private)<=B_i(public)+4R delta,
    U_i(private)>=U_i(public)-4R delta,

which proves (14). The relative factor L in (15)--(16) is essential:
an opponent may have arbitrarily smaller total hazard than the full profile,
and a bare delta^2 error would not justify this complete-response claim.

The argument also allows deterministic calendar variation of the signal
law and q, provided signals are independent across dates, q at date t uses
only t and that date's signal, and the same conditional total bound delta
holds at every date. At the first categorical Quit date the conditional
mismatch probability is still at most 2delta. If no categorical Quit ever
occurs, both processes choose Never. No retained signal memory is allowed.

Iid SIGNALS alone do not imply this hypothesis: a general sunspot profile
uses iid fresh noise to update a history-dependent public state. The known
general source in Section 8 does precisely that. Thus (14) does not apply
to it merely because its primitive signals are independent.

An independently checked exact persistent-state falsifier appears in
Section 6 of
[`CODEX_EMMY_BOX__OBJECTIVES_AND_GLOBAL_SELECTION.md`](CODEX_EMMY_BOX__OBJECTIVES_AND_GLOBAL_SELECTION.md).
One initial public bit selects a permanent sole owner in the two-player
table with singleton rows (1,2),(2,1) and zero collision/Never rewards.
Every branch is exact Nash with arbitrarily small conditional hazards.
Private averaging preserves the limiting prescribed payoff (3/2,3/2) but
creates a Never cap of 2 and regret tending to 1/2. The failure is retained
state, not large conditional hazards. Target-free selection of one branch
still succeeds. My bounded check is in
[`the owned feedback`](../feedback/CODEX_EMMY_BOX__OBJECTIVES_AND_GLOBAL_SELECTION__BY_CODEX_TURING_BOX.md).

### Expected small hazard is not enough

On Fin4 let r(I)=(1,1,1,1), let r({i}) be the ith unit vector, and let
every other coalition reward be zero. At each date a fresh public signal
prescribes all players Quit surely with probability theta>0 and all
Continue otherwise. This is exact public Nash with target (1,1,1,1):
on a Quit signal a unilateral Continue yields zero, and on a Continue
signal quitting alone yields 1, equal to the prescribed continuation.
No complete deviation can exceed 1.

The EXPECTED total hazard is only 4theta. Nevertheless marginal rebalancing
gives private hazards theta, whose prescribed coordinate payoff is

    [theta(1-theta)^3+theta^4]/[1-(1-theta)^4] -> 1/4.

Quitting immediately has payoff (1-theta)^3+theta^3 -> 1, so complete
private regret has liminf at least 3/4. The conditional total bound cannot
be replaced by an expected-total bound. This is a falsifier of that
weakened rebalancing theorem, not a game-level positive-gap example: pure
sure grand-coalition quitting is already an exact private equilibrium.

## 10. Source-level limits of the alternative

### Diffuseness cannot be required from every table

The participant-indicator table r_i(S)=1 if i belongs to S, zero otherwise,
has the exact pure grand-coalition equilibrium. This is the solved table
used in the root notebook's atomless-clock test. It also rules out an
unconditional SMALL-CONDITIONAL-HAZARD PUBLIC producer, even when arbitrary
public memory is allowed. Every full public cap is 1, since Quit at date 0
guarantees reward 1. At any live public history put m=sum_i q_i<=delta.
Its conditional absorption probability a satisfies the second-order union
bound

    a>=m-sum_{i<j}q_i q_j>=m(1-delta/2).

Summing over all reached dates and histories, allowing Never, gives

    sum_i U_i=E[|first quitting coalition|]
             <=1/(1-delta/2),
    maximum full debt>=1-1/[n(1-delta/2)].               (18)

For Fin4 this lower bound tends to 3/4 as delta tends to zero. Therefore
an arbitrary-table public theorem cannot be put globally into the diffuse
source form of Section 9. This does NOT refute a solved-game-or-diffuse
disjunction, or a diffuse-source theorem under an actual no-UE hypothesis.

### Even a full-normal/Q residual can require retained state or large roots

A stronger bounded source comparison uses the existing Solan--Vieille
boundary table. Its singleton rows, in owner order 0,1,2,3, are

    (1,4,0,0), (4,1,0,0), (0,0,1,4), (0,0,4,1).

Pairs 01 and 23 pay (1,1,1,1); the other pair rows are

    02:(1,1,1,0), 03:(1,0,1,1),
    12:(0,1,1,1), 13:(1,1,0,1).

Triples 012,013,023,123 pay respectively e_0,e_1,e_3,e_2; the grand
coalition pays (-1,-1,-1,-1), and Never pays zero. Thus R=4 and each own
singleton reward is 1.

The following exact declarations were inspected, with no new Lean build:

- `boundaryReward`, `boundaryReward_unitSoloExit`, in
  `UniformEquilibrium/Quitting/Examples/SolanVieilleBoundaryTable.lean`.
- `periodTwo_residualHardClass` and
  `periodTwo_residualHard_fullCore_nonstationary_but_uniform`, in
  `UniformEquilibrium/Quitting/Examples/BlockPair/FourPlayerPairedSingletonResidualHard.lean`;
  the former supplies standard-Q and no homogeneous simplex solution through
  `ResidualHardClass`, and the latter additionally states the full normal
  core and the checked uniform-equilibrium payoff.
- `quittingSerializedRoots`, in
  `UniformEquilibrium/Quitting/Root/SequentialSerialization.lean`, and
  `isAsymptoticNash_quittingSerializedRoots`, in
  `UniformEquilibrium/Quitting/Root/SequentialSerializationEquilibrium.lean`.
- `Schedule`, `Schedule.roots`, in
  `UniformEquilibrium/Quitting/Examples/SolanVieilleBoundarySoloHazardLedger.lean`,
  and `Schedule.one_over_sixtyEight_lt_literal_exploitability`, in
  `UniformEquilibrium/Quitting/Examples/SolanVieilleBoundarySoloHazardSemantic.lean`.

Suppose a no-retained-state public protocol of Section 9 has full debt
epsilon and conditional total hazard at most delta at every date. Its
private marginal replacement has full debt at most epsilon+32delta.
Every private hazard is at most delta. The checked serialization theorem
then constructs an actual one-owner-per-date private profile with full
debt at most epsilon+32delta+32*4delta=epsilon+160delta.
The serialization simply cycles the four owners within each original
date, with each owner's original marginal hazard. It is literally a
`Schedule` with owner t modulo 4 and scalar hazard
lambda_{t modulo 4}(floor(t/4)). The checked complete one-owner floor gives

    epsilon+160delta>1/68.                             (19)

In particular there is no no-retained-state diffuse public family with
both epsilon and delta tending to zero on this full-normal/Q residual
table. This is an ordinary composition of inspected theorems with the new
rounding estimate; that composition has not been checked in Lean. It is
not a new equilibrium-class exclusion: the same table already has a
checked exact period-two equilibrium. Nor does it rule out a source
restricted to actual positive-gap/no-UE tables. It does rule out treating
the entire algebraic Q residual as if its public strategy could discard
the retained macrostate while keeping uniformly small roots.

The relevant next mathematical operation is therefore not alphabet
compression or a different objective over frozen branches. It must either
recover non-small simultaneous roots from a retained-state source, or
remove retained state by an operation more substantial than averaging
current hazards. The bounded lookup does not establish whether a hybrid
collision dispatch plus a no-memory source covers the remaining tables.

## 11. Tests and outstanding work

The two extreme survival tests in the proof are exact: an empty prefix has
S=L_i=1 and gives ordinary finite-mixture selection; a prefix with S=0
admits exact selection of one low-cap constituent at the only potentially
surviving deleted coordinate. The pairwise bound L_i L_j<=S also treats
multiple sure quitters without a special assumption.

The artificial restriction removed is source-preserving decoding: an
existence proof need not realize the relaxed barycentric payoff, reuse the
public calendar/root alphabet, preserve a prefix, or maintain ancestry
between accuracies. Complete private independence and every behavioral
deviation remain compulsory.

The alternatives actually tested are offline constituent selection with
prefix deletion/retention, and genuine replacement by private marginal
hazards. The first has a word-length-independent recovery theorem and a
fixed-depth extension; the second has a depth-independent estimate for
exogenous no-retained-state small-root protocols. Their exact failure
boundaries are recorded rather than repaired by silently weakening agency.

The least practical enlargement that passes both the frozen-word and
diffuse-law fixtures is to permit genuinely new simultaneous product roots,
including non-small collision rows, and to select the final payoff only
after producing low full debt. The frozen-word fixture is repaired by small
simultaneous roots; the residual boundary fixture already uses non-small
period-two roots. This does not supply one general selection rule between
those mechanisms or a new reward-table existence class.

The bounded strictly iid source-overlap test is now completed in
Proposition 3 of the neighboring
[`Emmy notebook`](CODEX_EMMY_BOX__OBJECTIVES_AND_GLOBAL_SELECTION.md),
with my bounded check in the owned feedback. A diffuse stationary iid
current-signal-only source of vanishing full debt forces either all own
singletons nonpositive, or a homogeneous normalized-singleton simplex
witness. Immediate Quit gives its coordinate floor and complete Never
gives complementarity; no error/total-hazard assumption is needed. The
nonvertex case is already produced by
`isQuittingStationaryUniformEquilibriumPayoff_of_nonvertexHomogeneousWitness`
in `UniformEquilibrium/Quitting/Classification/LCP/HomogeneousProducer.lean`,
whose declaration was inspected. No vertex sufficiency or calendar-varying
classification is inferred from that citation.

The outstanding obstacle is mathematical: produce relaxed low-debt points
with bounded/sufficiently slow signal-depth growth, or replace the retained
public-state/collision mechanism by genuine private product roots while
controlling every deleted-player cap. Finite signal alphabets, additional
response bookkeeping and source passports do not establish this step.

One neighboring global selection alternative survives its full test:
Section 6 of
[`CODEX_NASH_BOX__DIRECT_EXISTENCE_BEYOND_TEMPORALIZATION.md`](CODEX_NASH_BOX__DIRECT_EXISTENCE_BEYOND_TEMPORALIZATION.md)
minimizes ORIGINAL full debt over the entire exact private-Never-bonus
finite-game correspondence. On its solved rational table, fixed-menu
vanishing bonuses have minimum gap tending to 18/49, yet jointly growing
menus and small bonuses have infimum gap zero. My bounded check of this
limit-order calculation is in
[`the owned feedback`](../feedback/CODEX_NASH_BOX__DIRECT_EXISTENCE_BEYOND_TEMPORALIZATION__BY_CODEX_TURING_BOX.md).
This is not a new producer or a review of that note's robust perturbation
theorem. It is evidence that a bad branch or a fixed-menu limit does not
falsify global existential selection.

Recommendation: change the consumer to target-free recovery when exploring
relaxations, but do not redirect the main existence effort to universal
seed freezing, universal diffuseness, or iid current-signal averaging.
The bounded source tests show those are insufficient. The concrete next
question is whether a direct search in the one-convex-seed/prefix class
can produce rho=0 from arbitrary rewards, without recursively importing
the same unbounded public-state construction.

## 12. A direct source attempt: dispersed pivot plus recomputed opponents

This section is ordinary mathematics and is not independently reviewed.
The concrete proposed source was to spread the canonical positive pivot's
private clock over many dates, then recompute the other three clocks as
Nash responses in their actual finite game. Unlike freezing a public word,
this permits new independent clocks and a new payoff at every accuracy.
The following test shows that unconditional atom dispersion itself is too
restrictive. It is stronger than a failure of an exact nonpivot selector.

Use I={0,1,2,3}, Never reward zero, and the complete table

    r_0(S)=1 if 0 belongs to S, and 0 otherwise;
    r_i(S)=-1 if S={0}, and 0 otherwise, for i=1,2,3.

Own-singleton rewards are (1,0,0,0), so this is a genuine canonical
single-pivot table. Let T_i be arbitrary independent private date-or-Never
clocks, and suppose only that

    sup_(finite t) Pr(T_0=t) <= delta.

There is no conditional-hazard, support-size, stationarity, or response
restriction on any clock. Write T_-=min(T_1,T_2,T_3), with minimum Never
when all three are Never, and put

    A=Pr(T_0<T_-, T_0 finite),
    J=Pr(T_0=T_-<Never).

The prescribed payoffs and COMPLETE caps are exactly

    U_0=A+J,       B_0=1,
    U_i=-A,        B_i=0  (i=1,2,3).

For the caps, player 0's pure date 0 guarantees reward 1 and no reward
exceeds 1. Any nonpivot's pure date 0 guarantees reward 0, and all that
player's rewards are nonpositive. Thus these are all-date-and-Never caps,
not displayed-menu comparisons. Independence also gives

    J=sum_t Pr(T_0=t) Pr(T_-=t) <= delta.

Consequently EVERY such actual profile satisfies

    E=max{1-A-J,A} >= (1-J)/2 >= (1-delta)/2.       (20)

In particular, fixing a uniform pivot on N dates and selecting ANY three
nonpivot laws cannot produce vanishing full regret. Exact or approximate
nonpivot Nash selection cannot repair it. If the nonpivot full regret is
at most epsilon, then A<=epsilon and the stronger pivot bound is

    D_0 >= 1-epsilon-delta.

The bound in (20) is sharp at delta=1/N: let players 0 and 1 independently
use the uniform law on the same N dates and players 2,3 use Never. Then
J=1/N and A=(1-1/N)/2, so all four debt coordinates equal (1-1/N)/2.
This exact calculation distinguishes small UNCONDITIONAL pivot atoms
from small conditional hazards; the last hazard of a uniform clock is one.

The alternative actually tested is a genuinely new joint root: players
0 and 1 Quit surely at date 0, and players 2,3 use Never. Its payoff is
(1,0,0,0), its complete caps are the same vector, and it is exact terminal
Nash. Repeating this same profile gives that fixed uniform payoff. There
is no public correlation. The collision atom is the repair, not a more
careful choice among dispersed clocks.

Source/coverage boundary: the semantic lookup for this attempt used
`PivotRepairBehavioralInfimum.lean`, `PivotRepairSourceCompression.lean`,
`PivotRepairExactObjective.lean`, and
`PivotRepairUniformPayoffCharacterization.lean` in
`UniformEquilibrium/Quitting/Terminal/`, together with the exact root
prefix definition in `Root/TerminalSemanticPair.lean`. The finite LP
already permits unrestricted pivot laws; imposing dispersion is therefore
an extra proposed source condition, not part of that consumer. The fixture
has an elementary pure-coalition equilibrium and gives NO new coverage
beyond implemented/accepted anchored-coalition producers. The bounded
pending-export comparison included `GLOBAL_TWO_JOINT_CYCLIC_CHILD_` and
`BELOW_SINGLETON_JOINT_PHASE_UNIFORM_EQUILIBRIUM`; this is not a claim to
extend either class. In particular, no positive-minimum or no-UE hypothesis
is asserted of the fixture.

Direction change: do not pursue universal pivot dispersion, even with
freely recomputed opponent laws. The next source attempt must select and
rebalance macroscopic simultaneous atoms as well as any dispersed tail.
Making every atom small is not merely an implementation convenience here.

## 13. Four joint phases: a full-dimensional direct source candidate

### Exact raw statement and status

Let I={0,1,2,3}, with the independent-clock and full unilateral-deviation
semantics in Section 1. The following complete table r* has fifteen rows;
Never remains zero.

| S | r*(S) |
|---|---|
| 0 | (1,4,0,0) |
| 1 | (4,1,0,0) |
| 2 | (0,0,1,4) |
| 3 | (0,0,4,1) |
| 01 | (5,9/2,13/2,10) |
| 02 | (−3,−3,−3,−3) |
| 03 | (2,5/4,2,2) |
| 12 | (2,2,2,5/4) |
| 13 | (−3,−3,−3,−3) |
| 23 | (13/2,10,5,9/2) |
| 012 | (−3,−3,15/2,−3) |
| 013 | (−3,2,−3,−3) |
| 023 | (15/2,−3,−3,−3) |
| 123 | (−3,−3,−3,2) |
| 0123 | (−100,−101,−102,−103) |

**Candidate theorem (ordinary proof below).** There is a constant delta>0
such that every raw reward table r with

    max_(S nonempty,i) |r_i(S)−r*_i(S)| < delta

has an exact terminal Nash equilibrium, against all complete behavioral
replacements. It is four-periodic with scheduled pairs

    A=01,    B=12,    C=23,    D=03,

and two proper independent hazards at every date; the other two players
Continue. Its actual phase-A payoff is one fixed original-game uniform
equilibrium payoff. The same profile and target work at all accuracies
once the horizon is sufficiently large. All sixty rewards may vary
independently. The raw neighborhood is not defined by admitting a strategy
or certificate; delta and its center precede the table being tested.

No unrestricted Fin4 coverage is asserted. In particular, no assertion
that these tables lack stationary equilibria is made. The present
comparison excludes the particular implemented/accepted criteria below,
not every possible proof from the reward data. Independent algebra and
coverage review are still required before an export claim.

### Actual independent clocks and the center

In the rate ordering

    q=(a0,a1,b1,b2,c2,c3,d0,d3),

set all eight rates to 1/2 at r*. For player i and date t, let q_i(t)
be its scheduled rate, or zero when unscheduled, and define its private
clock by

    Pr(T_i=t)=q_i(t) product_(s<t)(1−q_i(s)).

Each player is active twice per period, so its Never mass is zero.
Sample the four entire clocks independently. The schedule uses only the
deterministic public date; no correlated seed or communication is present.

The actual phase values at r* are

    V_A=(3,11/4,2,3),       V_B=(2,3/2,3/2,2),
    V_C=(2,3,3,11/4),      V_D=(3/2,2,2,3/2).             (21)

If phase t schedules {i,j}, the policy identity is exactly

    V_t=(r*(i)+r*(j)+r*(ij)+V_(t+1))/4.

For an active owner i, its Quit and Continue endpoints are respectively

    Q_ti=(s_i+r*_i(ij))/2,
    C_ti=(r*_i(j)+V_(t+1),i)/2.

Both equal V_ti at every one of the eight active occurrences. For an
inactive k, Continue equals V_tk; its forced Quit endpoint averages the
four literal rows k,ki,kj,kij with weight 1/4 each. The eight positive
Continue-minus-Quit margins, ordered by phase and inactive receiver, are

    (A,2):1/8,   (A,3):15/4,
    (B,0):2,     (B,3):7/8,
    (C,0):1/8,   (C,1):15/4,
    (D,1):7/8,   (D,2):2.                               (22)

Thus every actual prescribed action is optimal against the continuation
in (21). The asymmetric grand row is intentionally unused: at most two
players are scheduled, so even a unilateral Quit can create at most a
triple. Its asymmetry removes a response-quotient overlap; it is not a
new strategic resource.

### The raw eight-equation producer

For arbitrary nearby rewards r and eight arbitrary rates q, let {i,j}
be phase t's pair, and write x=q_ti, y=q_tj. Define

    S_t=(1−x)(1−y),
    G_t=x(1−y)r(i)+(1−x)y r(j)+xy r(ij),
    P=S_A S_B S_C S_D,
    U_t=[G_t+S_t G_(t+1)+S_t S_(t+1)G_(t+2)
                   +S_t S_(t+1) S_(t+2)G_(t+3)]/(1−P).   (23)

Indices are cyclic. These are the actual policy values wherever all
rates are proper. In particular U_t=G_t+S_t U_(t+1); no independently
selected continuation value is a variable or hypothesis.

For each active occurrence of i, with scheduled mate j and its rate y,
define the literal Quit-minus-Continue residual

    F_ti(r,q)=(1−y)s_i+y r_i(ij)
                          −y r_i(j)−(1−y)U_(t+1),i.      (24)

The eight rows F are ordered A0,A1,B1,B2,C2,C3,D0,D3. Equations (21)
give F(r*,q*)=0 for q*=(1/2,...,1/2). Since 1−P=255/256 at this point,
F is smooth in a full neighborhood in R^60×R^8.

The exact rate Jacobian is J=K/255, where

    K = [   0   504  −256   256   −80   −80     0     8 ]
        [ 249     0     0   128  −128  −128   −10    22 ]
        [ −24     0     0  1022  −512  −512   −40    88 ]
        [ −20   −20  1022     0     0  −384    64   −64 ]
        [ −80   −80     8     0     0   504   256  −256 ]
        [−128  −128    22   −10   249     0   128     0 ]
        [   0  −384   −64    64   −20   −20     0  1022 ]
        [−512  −512    88   −40   −24     0  1022     0 ].

This calculation is reproducible directly from (23)–(24). For example,
differentiate the policy system:

    partial U_t = partial G_t+(partial S_t)U_(t+1)
                                      +S_t partial U_(t+1).

At the center, differentiating an owner rate x at its own phase gives
forcing (r(i)−r(j)+r(ij)−U_(t+1))/2; propagation around the cycle is
division by 1−(1/4)^4. This yields the displayed K without differentiating
any source-selected or fictitious value. Exact rational elimination gives

    det K=2^10 3^7 5^5 17^4 ·29·151·6421
         =16435089066040617600000,
    det J=28792380416/31320375 >0.                         (25)

The implicit function theorem now produces a smooth local rate selector
q(r), with q(r*)=q* and F(r,q(r))=0. Shrink a raw reward ball so every
rate lies in (1/4,3/4). Because the inactive endpoint expressions and
(23) are continuous, shrink it again so all eight margins in (22)
remain strictly positive. This single positive delta proves the raw
existence statement: all strategic inputs are produced from r by (23),
(24), and the local implicit selector. No strategic witness is assumed.
The argument currently gives existence of a neighborhood radius, not
an explicit executable radius or a quantitative rate condition number.

### All complete deadlines, Never, and uniform payoffs

Fix any table in this neighborhood and its produced proper rates. At
every live date, the assigned U bounds both unilateral endpoints and
equals the prescribed policy value. Each player has three opponents,
each scheduled twice per period, so even under an arbitrary complete
replacement by that player the probability of surviving a whole period
is at most

    rho=(3/4)^6 <1.                                      (26)

This uses only independent opponent coins on the unique continuing public
history. A deviator's private history or memory cannot change those coins.
The deviation can choose different actions at every date, Quit at an
arbitrarily late deadline, or Never.

Iterate the one-step endpoint inequality through m periods. The terminal
payoff already realized is retained exactly; the unabsorbed continuation
remainder has absolute value bounded by a fixed reward/value bound times
rho^m. Let m grow. Every complete replacement has terminal payoff at
most U_Ai. The prescribed profile attains U_Ai, hence its COMPLETE cap
B_i equals U_Ai. This includes the limit of arbitrarily late deadlines
and the pure Never replacement, not merely the eight displayed actions.

Let M bound every absolute reward in the fixed neighborhood. Under any
unilateral replacement, if tau is the first quitting date starting at zero,

    E[tau+1] <= 4/(1−rho).

The N-date average reward differs in expectation from terminal reward
by at most 4M/[(1−rho)N], including the zero selecting date. It follows
that the prescribed average payoff converges to U_A, and every complete
behavioral gain in the N-date game is at most 8M/[(1−rho)N]. One common
threshold therefore works for all deviations and all larger horizons.
The selected actual target U_A is fixed before the accuracy.

### Bounded implemented and accepted coverage tests

These comparisons are part of the candidate, not a complete novelty seal.
They concern literal raw criteria and their whole listed finite selection
sets. A preliminary symmetric grand row (−100,...,−100) WAS covered by
the half-turn automorphism quotient. The asymmetric row displayed above
is the final center; none of (21)–(26) changes when it is substituted.

1. **Singleton-only sources.** The literal comparison matrix is

       Gamma=[ 0  3 −1 −1; 3  0 −1 −1;
              −1 −1  0  3; −1 −1  3  0 ].

   It is the paired matrix with full normal core, standard-Q property,
   no homogeneous simplex witness, and failure of projective Q-bar
   established in `FourPlayerPairedSingletonLCP.lean` and
   `FourPlayerPairedSingletonResidualHard.lean` under
   `UniformEquilibrium/Quitting/Examples/BlockPair/`. Their conclusions
   depend only on Gamma, not this completion. Its eigenvalues are
   1,5,−3,−3, determinant45; its inverse has diagonal2/15, favorite
   entries7/15, and cross entries1/5. Pair determinants are −9 or −1;
   every triple determinant is6, and every triple inverse has a diagonal
   entry−1/6. Thus the full nonnegative-inverse theorem, which requires
   NEGATIVE determinant, does not apply; its R0 degree is+1. No proper
   triple passes the nonnegative-inverse child test. Harmful pair matrices
   are not standard-Q, but no inference from their failure to original
   parent UE is made. Bare full ordinary-non-Q is unavailable.

2. **Every nondiscrete response quotient.** At all-sure hazards the
   actual displacements are r_i(I)−r_i(I−i), namely

       (−97,−98,−99,−100).

   They are pairwise distinct. Every nondiscrete partition identifies
   two players, so its response-invariance condition fails already at
   this point. This covers all fourteen nondiscrete partitions, including
   paired and orbit quotients. It survives positive playerwise affine
   transports: Gamma's row sums all equal1, and the necessary block-row
   identity forces equal positive row scales inside each block; the
   displayed unequal responses remain unequal after that common scale.
   The discrete quotient has Gamma's degree+1.

3. **Every proper quiet child with nonnegative weights.** In the
   accepted `NONNEGATIVE_SINGLETON_FINITE_QUIET_LIFTS` criterion, its (J)
   compares outsider join gain with a nonnegative sum of child join
   gains. Every triple child fails (J):

   | Child | coalition T | omitted outsider's join gain | sole child outside T's join gain |
   |---|---|---|---|
   | 013 | 01 | 1 | −13 |
   | 123 | 23 | 1 | −13 |
   | 012 | 12 | 3/4 | −5 |
   | 023 | 03 | 3/4 | −5 |

   Child members in T have zero join gain, so the weighted right side
   is nonpositive for EVERY nonnegative weight vector. The four pair
   children01,12,23,03 fail at their whole coalition, with the same
   positive outsider gains. Child02 fails at T={2}: outsider1's gain2
   must be at most child0's gain−3 times a nonnegative weight; child13
   fails at T={3} with outsider0's gain2 and child1's gain−3. Finally
   each singleton child has some outsider with positive join gain2.
   This excludes the entire proper-child selection set, not one chosen
   child or target.

4. **Two-pair joint and matching sources.** Checking the THREE partitions:
   01|23 has positive outsider joining cap violations, e.g.
   r_0(03)=2>s_0=1; 02|13 has participant failure−3<0; 03|12 has
   opposite-pair cap violation r_0(01)=5>s_0=1. This excludes the raw
   `TWO_PAIR_JOIN_CAP` test, its weak crossed-matching specialization,
   and sources requiring those same twelve individual caps. The signed
   inverse-column source has only positive allowable column signs here;
   partition01|23 violates K_0=11/2<=0, partition03|12 violates K_0=1<=0,
   and partition02|13 has negative participant premiums. Opposite-sign
   and below-own joint-premium sources have additional incompatible
   center equalities or those same joining caps. This last sentence is
   a bounded raw comparison, not an arbitrary-neighborhood exclusion.

5. **Guarded crossed and one-sided sources.** At any receiver i, the
   unique positive singleton neighbor is its favorite f(i), with
   Gamma_i,f(i)=3. If a selected partner is not f(i), the outsider
   favorite axis has negative displacement for all sufficiently small
   positive hazards. If the partner is f(i), a sure harmful outsider
   (2 for i0, 3 for i1, 0 for i2, 1 for i3) gives displacement−3.
   Thus EVERY ordered lower face fails, covering lower-ranking,
   weak-polynomial and one-sided lower guards, under all relabelings.

6. **Premium/core and three-child sign patterns.** Pair traps01,12,23,03
   overlap, so the mixed-premium-trap source's larger-trap inequalities
   cannot hold. The greatest premium core is all four. The protected
   set P_max is empty, since every player's grand participant reward
   is below its singleton. Product-low fails already at pair01, whose
   two participant rewards exceed their own singletons. The positive
   singleton graph is two transpositions, not a directed favorable
   four-cycle or a favorable three-cycle; every proper triple omits
   one player's favorite. Hence the literal cyclic-child and signed
   four-cycle source patterns inspected here cannot be selected.

The narrow declaration audit used:

- `exists_uniformEquilibriumPayoff_of_nonnegative_singletonInverse`,
  `UniformEquilibrium/Quitting/Classification/LCP/NonnegativeInverseCriterion.lean`;
- `exists_uniformEquilibriumPayoff_of_raw_nonnegativeInverse_triple`,
  `UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/RawPassiveRowInverseCriterion.lean`;
- `quittingSingletonBlockRowSum_eq_of_responseInvariant`,
  `UniformEquilibrium/Quitting/Stationary/ResponseInvariantQuotient.lean`;
- `exists_uniformEquilibriumPayoff_of_pairedCenteredCompletion`,
  `UniformEquilibrium/Quitting/Examples/BlockPair/PairedResponseQuotientClass.lean`;
- `exists_guardedCrossed_stationaryTerminalNash_uniformPayoff_of_strictRawUnit`,
  `UniformEquilibrium/Quitting/Stationary/GuardedCrossedResponseRawProducer.lean`;
- `QuittingHalfWeakPolynomialGuards`,
  `UniformEquilibrium/Quitting/Stationary/GuardedCrossedResponseWeakPolynomialFaces.lean`;
- `QuittingOneSidedWeakUnitGuards`,
  `UniformEquilibrium/Quitting/Stationary/OneSidedWeakUnitProducer.lean`;
- `isZeroAsymptoticNash_quittingCyclicBehaviorProfile_of_certificate` and
  `isUniformEquilibriumPayoff_quittingCyclicTerminalValue_of_certificate`,
  `UniformEquilibrium/Quitting/Cycles/PeriodicCompiler.lean`.

The new supplied-data-to-strategy step is the eight-rate local producer
(23)–(25), not the already checked periodic compiler. The concrete next
requested check is independent reconstruction of the Jacobian and a bounded
coverage challenge to the asymmetric center. Do not export before resolving
that comparison against the relevant accepted scheduling-source families.

## 14. Thirty-two local, twelve upper-only, sixteen arbitrary coordinates

Status: ordinary mathematical proof, not Lean-checked. CODEX_EMMY_BOX's
bounded independent support/transfer check passed, and the strengthening
has been incorporated into the frozen standalone packet. Its input is the
reviewed four-phase cylinder
theorem of Section13, with some existential radius delta_0 in(0,1].

### 14.1. Exact raw-coordinate partition and claim

Write a reward coordinate as(S,i), meaning recipient i's reward r_i(S).
Partition the sixty coordinates into the following three disjoint sets.

P consists of all four recipients' coordinates in the eight rows

    0,1,2,3,01,12,23,03.                              (26)

Thus |P|=32. These are exactly the coalition rows that can occur under the
prescribed pair schedule A=01,B=12,C=23,D=03 without any deviation.

C consists of the following twelve coordinates. The listed center values
are taken literally from Section13's raw table.

| Coalition S | Recipients i | Center values in that order |
|---|---|---|
| 02 | 0,2 | -3,-3 |
| 13 | 1,3 | -3,-3 |
| 012 | 0,2 | -3,15/2 |
| 013 | 1,3 | 2,-3 |
| 023 | 0,2 | 15/2,-3 |
| 123 | 1,3 | -3,2 |

F consists of the remaining sixteen coordinates:

| Coalition S | Arbitrary recipients i |
|---|---|
| 02 | 1,3 |
| 13 | 0,2 |
| 012 | 1,3 |
| 013 | 0,2 |
| 023 | 1,3 |
| 123 | 0,2 |
| 0123 | 0,1,2,3 |

**Strengthened producer.** There exists delta>0 such that EVERY finite raw
table r satisfying

    |r_i(S)-r*_i(S)|<delta  for every(S,i) in P,
     r_i(S)<=r*_i(S)+delta for every(S,i) in C               (27)

has an exact terminal Nash equilibrium and a fixed original-game uniform
equilibrium payoff, with the same deterministic four-phase schedule and
private scheduled hazards in(1/4,3/4) as Section13. There is NO lower bound
on a C-coordinate, and NO condition on an F-coordinate except finiteness.
The strategy, payoff and finite-horizon cutoff are allowed to depend on
the original table; the payoff is fixed before choosing an accuracy.
All complete unilateral behavioral replacements, late deadlines and Never
remain in scope. No public correlation, normalization or reward transport
is used. This is a producer on a32-dimensional open box times a12-dimensional
coordinatewise lower set times R^16, not an arbitrary-game producer.

### 14.2. Literal support and monotonicity for full deviations

Fix ANY scheduled hazards q, with unscheduled players pure Continue. A
unilateral replacement by player i does not make any other player change
its prescribed schedule. At a phase with scheduled edge e, its terminal
coalition belongs to

    {j}, {k}, e, {i}, {i,j}, {i,k}, {i} union e,

with unavailable or repeated elements omitted; if i is already in e,
there are at most the two scheduled players. The baseline coalitions are
the P-rows. The only non-P coalition coordinates that can affect the
REPLACING PLAYER'S OWN reward are precisely C. More explicitly:

| Replacing player | Non-P coalition rows in its own payoff |
|---|---|
| 0 | 02,012,023 |
| 1 | 13,013,123 |
| 2 | 02,012,023 |
| 3 | 13,013,123 |

For example,012 can be created by player2 at A or player0 at B, but it
cannot occur under player1's own replacement: at A only opponent0 is
scheduled, at B only opponent2 is scheduled, and the other two edges
produce013 or123. The same literal edge check gives every table entry.
No unilateral replacement can create the grand coalition. An unscheduled
pair02 or13 can be created only when its recipient is one of that pair's
two members, never when that recipient is one of the passive players.

Consequently, suppose two finite raw tables r and rhat agree on P and
satisfy r_C<=rhat_C coordinatewise. Their F-coordinates may differ freely.
Couple their prescribed players' private randomization and any one fixed
complete replacing behavioral rule nu_i. Their realized stopping date and
quitting coalition are identical, because their actions and information
before absorption are identical. On every sample path, the replacing
player's absorbed reward under r is at most its reward under rhat; the
Never reward is zero in both. The prescribed reward is identical, since
it uses only P. Therefore, for every i, every nu_i and every finite N,

    U_i^r(sigma)=U_i^rhat(sigma),
    U_i^r(nu_i,sigma_-i)<=U_i^rhat(nu_i,sigma_-i),
    gamma_N,i^r(sigma)=gamma_N,i^rhat(sigma),
    gamma_N,i^r(nu_i,sigma_-i)
                         <=gamma_N,i^rhat(nu_i,sigma_-i).    (28)

Here U is the terminal expected payoff and gamma_N is the original
finite-horizon average payoff, with zero live and selecting dates. The
latter comparison just multiplies the identical absorbed reward by the
same nonnegative realized fraction of paid dates. It includes deviations
that use an unrestricted private seed and all dates beyond the horizon.
It does not presume a finite-menu or Markov best response.

The same conclusion holds if a complete rule is expressed as an initial
private date-or-Never law. More generally any behavioral replacement has
only the date and all-Continue past on its surviving path, so the coupling
retains exactly its intended agency. In particular all pure-deadline and
Never caps, and their full behavioral supremum, weakly decrease. Hence an
exact terminal Nash profile or fixed-payoff uniform equilibrium under
rhat transfers with the SAME profile and payoff to r.

### 14.3. Producer from the reviewed local theorem

Let delta_0 be Section13's reviewed radius. Set delta=delta_0/2. Given
ANY original table r satisfying(27), define a comparison table rhat by

    rhat_P = r_P,
    rhat_(S,i) = r*_(S,i)+delta for(S,i) in C,
    rhat_(S,i) = r*_(S,i) for every proper(S,i) in F,
    rhat_(I,i) = 0 for all i.                               (29)

Every proper coordinate of rhat is STRICTLY within delta_0 of the center:
the P-error is<delta, the C-error is delta, and the remaining proper
error is zero. The arbitrary-grand version of the reviewed cylinder
theorem produces actual independent hazards q in(1/4,3/4) and the four
phase profile sigma for rhat. It has full terminal regret zero and a fixed
uniform payoff v=U_A^rhat(sigma).

The literal original table r and the comparison table rhat have the same
P-coordinates and r_C<=rhat_C. Apply(28): sigma has full terminal regret
zero in the ORIGINAL table and exactly the same phase-A payoff v. For any
accuracy, use the proxy's uniform cutoff; its prescribed finite-horizon
payoffs are identical and every actual deviation payoff is no larger.
Thus the same sigma and v give the original uniform equilibrium as well.

Alternatively the already reviewed deleted-opponent geometric contraction
proof applies directly, with a finite reward bound depending on r. No
uniform bound on the newly unrestricted negative or irrelevant rewards
is needed for this existence conclusion. The proof adds no IFT equations,
no new strategy consumer and no assumption on a chosen continuation.
It changes only the source region of the actual raw-table producer.

The entire P/C/F support partition, the pathwise monotonicity in(28) for
all complete replacements, and the proxy reduction(29) passed the bounded
independent check. The frozen standalone retains the source-to-UE proof;
the next mathematical question is a producer with genuinely global scope,
not another widening of this particular local neighborhood.

## 15. An unbounded reward-region rectangle producer with four negative collision barriers

Status: independently reviewed and exported ordinary mathematics, not checked
in Lean. The canonical self-contained statement and proof are in
[`FOUR_JOINT_PHASE_RECTANGLE_UNIFORM_EQUILIBRIUM`](../exports/FOUR_JOINT_PHASE_RECTANGLE_UNIFORM_EQUILIBRIUM.md).
This replaces local Jacobian inversion by a rectangle
argument on an unbounded structural reward family. It is not arbitrary-table
existence, an open full-dimensional classification, or a proof of stationary
nonexistence. The family retains exact paired singleton and half-turn
identities; those remain genuine restrictions on its conjecture-facing scope.

### 15.1. Raw data and actual conclusion

Use the same independent-clock quitting semantics and four-phase schedule
A=01,B=12,C=23,D=03. Fix the singleton rows literally as

    r(0)=(1,4,0,0), r(1)=(4,1,0,0),
    r(2)=(0,0,1,4), r(3)=(0,0,4,1).

Choose any finite parameters

    R>=0, S>=6, V>=10, W>=48,

and prescribe the four scheduled pair rows as

    r(01)=(5,9/2,R,S),       r(23)=(R,S,5,9/2),
    r(12)=(V,2,2,W),         r(03)=(2,W,V,2).                (30)

Put M=max(5,R,S,V,W). The eight triple coordinates in Section14's C
set are ARBITRARY finite numbers. Define

    L=max(5, r_0(012),r_2(012),r_1(013),r_3(013),
              r_0(023),r_2(023),r_1(123),r_3(123)).

The four unscheduled-pair participant coordinates satisfy the literal
upper bounds

    r_0(02),r_2(02),r_1(13),r_3(13) < -24 M L.             (31)

The remaining sixteen F coordinates are arbitrary finite rewards. No
strategic witness, continuation, root, target, or limiting law is an input.

**Claim.** EVERY table (30)–(31) has an exact terminal Nash equilibrium
against all complete behavioral deviations, and its actual phase-A payoff
is a fixed uniform-equilibrium payoff of the ORIGINAL game. The profile
is four-periodic with two private scheduled hazards at each phase, each
strictly larger than1/6 and strictly less than1. It is a nonlocal raw
producer on an unbounded structural class, not just persistence around
one numerical center.

### 15.2. Eliminate six owner equations without a continuation input

For variables a,g define

    b=g/[2(1-g)],       d=a/[2(1-a)].

The scheduled hazards are

    A:(a,b), B:(g,d), C:(a,b), D:(d,g),

with the phase's players in increasing order. Define candidate scalar
values, all explicit functions of a,g and the raw parameters,

    v0=1+4b,             v1=1+(7/2)a,
    u1=1+d,              u2=1+g,
    w0=abR+(1-a)(1-b)u2,
    z0=4g(1-d)+gdV+(1-g)(1-d)w0,
    z1=4d(1-g)+dgW+(1-d)(1-g)v1,
    w1=abS+(1-a)(1-b)z1.                                  (32)

Only two residuals remain:

    F_A(a,g)=1-(1-b)z0,
    F_B(a,g)=1+d-(1-d)w1.                                 (33)

If both vanish, the FOUR phase vectors are

    U_A=(v0,v1,w0,w1),    U_B=(z0,u1,u2,z1),
    U_C=(w0,w1,v0,v1),    U_D=(u2,z1,z0,u1).                (34)

Here is the exact verification, not an assumed evaluation. The four
passive-coordinate recursions are exactly the definitions of w0,z0,z1,w1
in(32). Active A0 has Quit=1+4b and Continue=4b+(1-b)z0, so its equality
is F_A=0. Active A1 has Quit=1+(7/2)a and Continue=4a+(1-a)(1+d);
these agree by d=a/[2(1-a)]. Active B1 has Quit=1+d and
Continue=(1-d)w1, giving F_B=0. Active B2 has Quit=1+g and
Continue=(1-g)(1+4b), identical by b=g/[2(1-g)]. The half-turn gives
the other four active equalities. Therefore every coordinate of(34)
satisfies its LITERAL policy recursion once(33) vanishes. Proper rates
make the period contracting, so uniqueness of that recursion identifies
(34) with actual terminal values, not independent continuation data.

### 15.3. Exact opposite-face signs on a data-dependent rectangle

Set

    e=1/(4M),        h=(1-e)/(3/2-e),
    Q=[1/4,h] x [1/4,h] in coordinates(a,g).               (35)

Since M>=48, h>1/4 and h<2/3. On Q,

    1/4<=a,g<=h<2/3,
    1/6<=b,d<=1-e<1.

All scalars in(32) lie in[0,M]: first v0<=5, v1<=10/3, u1<=2,
u2<=5/3; every remaining formula is a nonnegative combination of
already bounded numbers with total coefficient at most one. In
particular z0,w1<=M. All formulas are continuous on the closed rectangle.

On the lower g face, g=1/4 and b=1/6. Since d>=1/6 and V>=10,

    z0 >= g[(1-d)4+dV]
        =1+d(V-4)/4 >=5/4,
    F_A <=1-(5/6)(5/4)=-1/24.                             (36)

On the lower a face, a=1/4 and d=1/6. Since S>=6,W>=48,g>=1/4,

    w1 >= bS/4+(1-b)gW/8
        >=(3/2)b+(3/2)(1-b)=3/2,
    F_B <=7/6-(5/6)(3/2)=-1/12.                           (37)

On the upper g face b=1-e, so

    F_A=1-e z0 >=1-e M=3/4.

On the upper a face d=1-e, so

    F_B=1+d-e w1 >=1-e M=3/4.                             (38)

Apply Poincare–Miranda to the field(F_B,F_A), with its coordinate order
(a,g). Equations(36)–(38) give a zero STRICTLY inside Q. Consequently all
eight scheduled hazards are proper and exceed1/6. This is a root produced
from the raw four parameters, without a nonsingular-Jacobian hypothesis.

### 15.4. Inactive endpoints and all complete clocks

At every inactive slot, the Quit endpoint contains exactly ONE of the
four negative unscheduled-pair participant rewards in(31). Its product
weight is x(1-y) or(1-x)y for the two scheduled rates. On Q every rate
is at least1/6 and every Continue probability is at least e, so this
weight is at least e/6=1/(24M). All other constituent rewards of that
inactive Quit endpoint are at most L: they are its own singleton1,
a scheduled-pair participant reward at most5, or one of the eight triple
coordinates defining L. Thus(31) makes the complete inactive Quit endpoint
STRICTLY negative, uniformly on Q. Its Continue value is nonnegative,
since every prescribed reward in(30) and each singleton is nonnegative.
This proves all eight inactive root inequalities at the produced zero.

No arbitrary triple reward was deleted or approximated: its possible
positive contribution is exactly paid by(31). Simultaneous quitting remains
a product-root event with its literal triple reward.

All active endpoints are equal by Section15.2. Every player's three
opponents have six prescribed coins per period, each with Quit probability
>1/6. Deleted-opponent survival is at most(5/6)^6<1, uniformly over the
replacing player's entire behavior, memory and Never choice. The same
endpoint telescoping as in Section13 therefore proves exact TERMINAL Nash
against every complete replacement, not just the symmetric or periodic
strategy class. A finite reward bound depending on the given table and
the geometric stopping bound prove that the ACTUAL payoff U_A is one fixed
uniform target, with the same profile for all sufficiently large horizons.
This completes the claimed producer proof.

### 15.5. Whole-selection coverage witness, not merely one failed root

For any parameters in(30), take a finite K satisfying

    K>max(4,24M max(5,R+1,W+1)).

Set both unscheduled pair rows equal to(-K,-K,-K,-K), and choose

    r(012)=(-K,-K,R+1,-K),
    r(013)=(-K,W+1,-K,-K),
    r(023)=(R+1,-K,-K,-K),
    r(123)=(-K,-K,-K,W+1),
    r(I)=(-2K,-2K-1,-2K-2,-2K-3).                          (39)

This is an explicit member of the new source for EVERY unbounded parameter
choice, not a new isolated small neighborhood. A numerical finite instance
is R=0,S=6,V=10,W=48,K=56449. Floating root searches give one interior
root approximately(a,g)=(.56005,.61309), but neither that experiment nor
uniqueness is used in the exact proof.

Its singleton matrix is exactly Section13's paired Gamma: ordinary standard
Q, full normal core, degree+1, no homogeneous simplex solution, and no
projective Q-bar. The same full/triple inverse screens fail. All-sure
responses are(-K,-K-1,-K-2,-K-3), excluding every nondiscrete literal
response quotient and its positive row-rescaling repair as before.

Every proper nonnegative quiet child fails over ALL weights. For children
013,123,012,023 use respectively T=01,23,12,03. The omitted outsider's
join gain is1 in all four cases, whereas the sole possible donor's gain
is respectively -K-S,-K-S,-K-V,-K-V. All are negative. The four scheduled
pair children fail at their whole coalition, with outsider gain1 and no
child donor. Child02 at T={2} has outsider1 gain2 against donor0 gain-K;
child13 at T={3} has outsider0 gain2 against donor1 gain-K. Every singleton
child has an outsider join gain2. Thus no child-selection or weight-selection
loophole is left in this named quiet-lift criterion.

The ALL-sure-owner Nash sets can also be computed exactly. For owner0,
write(x,y,z)=(q1,q2,q3). The other players' Quit-minus-Continue differences
are

    d1=(1-y)(1/2+z/2)-(K+1)yz,
    d2=(1-z)[-K+(K+1)x]+z[-K-V+(V-2)x],
    d3=2-(K+S+2)x-2y+(S-1)xy.                             (40)

If z>0, d3>=0 gives x<=2/(K+3). Then d2<0 forces y=0, and d1>0
forces x=1, a contradiction. Thus z=0. If y<1, d1>0 forces x=1,
then d2>0 forces y=1. The complete induced Nash set is precisely

    z=0, y=1, x in[K/(K+1),1].

The owner's reward is-K and its Continue payoff is Vx; opponent Continue
mass is zero, so every punishment-floor excess K+Vx is strictly positive.

For owner1 put(x,y,z)=(q0,q2,q3). The differences are

    d0=(1-z)[1-(K+V+1)y]-Kyz,
    d2=(1-z)(2-x)-(K+2)xz,
    d3=-K-Sx+(K+1)y+(S-K-4)xy.                            (41)

If z=0, d2>0 gives y=1, d0<0 gives x=0, then d3=1 contradicts z=0.
If z>0, d3>=0 gives y>=K/(K+1), since its x coefficient is strictly
negative. Thus d0<0 gives x=0. If z<1 then d2>0 gives y=1 and d3=1
gives z=1. The complete Nash set is precisely

    x=0, z=1, y in[K/(K+1),1].

The owner reward is-K and its Continue payoff is Sy; again all floors
are strictly violated, independently of the punishment value.

Owners2/3 use the half-turn coordinates but NOT an assumed grand-row
symmetry. For owner2,(x,y,z)=(q3,q0,q1), replace (K+1) in d1 by(K+3),
(V-2) in d2 by V, and(S-1) in d3 by(S+1). Then d3>=0 bounds
x<=2/(K+1), still making d2<0 because K>4. The same Nash set and owner
floor K+Vx follow. For owner3,(x,y,z)=(q2,q0,q1), replace Kyz in d0
by(K+2)yz, (K+2)xz in d2 by Kxz, and(S-K-4)xy in d3 by(S-K-2)xy.
Every sign implication in(41) still holds, giving owner floor K+Sy.

Consequently EVERY singleton-owner/free-set punishment compiler fails:
smaller free sets accepted with outsider no-join signs extend to these
full induced Nash sets. Every persistent-base/free-set compiler with base
size>=2 also fails, because its signs would yield a full zero-tail one-shot
Nash root with a sure quitter, whereas every such owner strictly prefers
Continue here. This is the whole selection screen, not just pure bases.

All three pair partitions fail the joining-cap sources:01|23 has
r_0(03)=2>1;02|13 has participant reward-K;03|12 has r_0(01)=5>1.
For the positive signed-inverse-column test, the first partition has
K_1=S-1>0, the third K_0=V-1>0, and the second negative participant
premiums. Every guarded lower face still fails: a nonfavorite partner
exposes the negative favorite axis, while a favorite partner exposes the
sure harmful outsider with pair reward-K. Four premium pairs overlap,
the grand protected set is empty, and the positive singleton graph is two
transpositions, not a favorable three- or four-cycle. These are the same
named finite source screens inspected in Section13, checked anew on(39).
They do not exclude every stationary certificate or establish disjointness
from earlier qualitative IFT neighborhoods with unspecified radii.

### 15.6. Source correspondence and the remaining global obstacle

I read `exists_rectangular_zero_of_strict_face_signs` in
`MathUE/Topology/RectangularPoincareMiranda.lean` and the actual consumer
`exists_uniformEquilibriumPayoff_of_periodic_rectangular_face_signs` in
`UniformEquilibrium/Quitting/Cycles/PeriodicRectangularFaceSign.lean`.
The latter enumerates one active slot per field coordinate; it is NOT
directly a two-coordinate-to-eight-slot adapter. Here the mathematical
rectangle theorem first produces the two-variable zero; identities(32)–(34)
then give all eight owner equalities; the already inspected declarations
in `UniformEquilibrium/Quitting/Cycles/PeriodicCompiler.lean` consume the
actual policy/root/deleted-contraction data. A clamped extension of the
rectangle field makes its continuity global if the topology declaration
requires it. I also read `PairedCollisionReward.exists_uniformEquilibriumPayoff`
in `UniformEquilibrium/Quitting/Examples/BlockPair/PairedCollisionRewardExistence.lean`:
its one-parameter literal reward family is not the class(30)–(31).

The unbounded region removes TWO local proof restrictions: owner production
does not need a nonzero eight-rate Jacobian, and passive joint rewards may
be arbitrarily large rather than near a center. All triple own-recipient
rewards are allowed; four sufficiently negative collision barriers pay
their entire inactive deviation effect. No public signal is introduced.

What remains is genuinely mathematical. An arbitrary table has neither
the exact half-turn elimination nor four selectable very negative barrier
coordinates; those rewards cannot be manufactured by a change of proof
language. The next global question is whether owner/continuation selection
can replace the negative barriers, possibly handing off to a different
macroscopic joint root when the rectangle's inactive wall is first crossed.
The present proof supplies NO such handoff and NO solved-game-or-barrier
disjunction. A concrete next test is to relax one barrier in(31) through
its first inactive wall and determine whether the enlarged active root
system has an actual continuation branch or instead loses every legal
periodic producer. Section 16 tests that particular local handoff mechanism;
its negative conclusion is not part of either exported producer.

## 16. Exact periodic continuation turns the wrong way at its first wall

Status: ordinary mathematical proof draft with exact rational calculations,
not independently checked or exported. This is a scoped falsifier of a
particular global-construction mechanism, NOT a uniform-equilibrium
counterexample, fixed-period completeness claim, stationary exclusion or
claim that all distant branches fail. The raw table below is only a
one-parameter change of Section13's explicit table.

### 16.1. A precise local continuation question

Take all Section13 proper rows literally, put

    r(I)=(-100,-101,-102,-103),

and vary ONLY c=r_0(02). Keep the calendar A=01,B=12,C=23,D=03.
The eight old scheduled hazards q*=(1/2,...,1/2), with every unscheduled
hazard zero, remain owner-indifferent for EVERY c: that reward is neither
on path nor in any old active owner's endpoint. Their actual four phase
values therefore remain Section13's displayed values.

At c_0=-5/2, the inactive slot C0 has exactly zero gap. Its Quit endpoint
is (1+c+2+15/2)/4, and its Continue value is2; hence its Quit-minus-Continue
gap is(c+5/2)/4. All other inactive Continue-minus-Quit margins are strict:

    A2:1/8, A3:15/4, B0:15/8, B3:7/8,
    C1:15/4, D1:7/8, D2:2.                               (42)

Thus this is the FIRST wall reached by increasing c from its original
value-3, not a simultaneous unresolved boundary. The natural proposed
handoff activates player0 at C while keeping the old eight owners proper.
Does that produce a nearby legal exact equilibrium for c>c_0?

**Local falsifier.** There are a parameter radius eta>0 and a neighborhood
V of this sixteen-hazard four-periodic profile such that, for every
c in(c_0,c_0+eta), NO legal four-periodic profile in V is an exact terminal
Nash equilibrium against all complete behavioral replacements. The
unique enlarged owner-indifference branch has NEGATIVE new C0 hazard.

### 16.2. The actual nine-rate Jacobian and orientation

Introduce the ninth rate z=q_C0 and keep the order

    (a0,a1,b1,b2,c2,c3,d0,d3,z).

At C the independent root has active support{0,2,3}; elsewhere it is the
original pair root. For real rates near(q*,z=0), evaluate the ACTUAL
periodic policy by its geometric formula. Its denominator is nonzero.
Let F consist of the eight original owners' Quit-minus-Continue residuals,
followed by the new C0 residual, always using those actual policy values.
At(c_0,q*,0), F=0.

Write K for Section13's displayed8x8 integer matrix, whose old owner
Jacobian is K/255. The full new rate Jacobian is the exact block matrix

    J9=(1/510) [ 2K   v ]
                 [ w^T  0 ],

    v=(0,204,816,1024,-2024,525,0,60)^T,
    w=(0,-96,-16,16,-770,1525,0,128)^T.                    (43)

The reward-parameter derivative F_c is zero in its first eight coordinates
and equals1/4 in its last coordinate. The top-left block really is the
unchanged old Jacobian: c affects none of its eight residuals when z=0.

For a reproducible derivation, differentiate actual policy recursion,

    partial U_t=partial G_t+(partial S_t)U_(t+1)
                                      +S_t partial U_(t+1).

At the base all S_t=1/4. The policy forcing from the newly added C0 rate
is concentrated at phase C and equals

    (0,-51/16,-4,-15/4).

This is the full vector of expected rewards when player0 Quits at C minus
U_C, not a proposed replacement continuation. Propagate it with the factor
1/4 around the four-phase cycle and divide by1-1/256. Differentiate each
old owner's endpoint to obtain v/510. For the last row, direct derivatives
of the new Quit endpoint with respect to c2,c3 are1 and11/2; subtract
the corresponding derivative of U_C0 to obtain w/510. The new diagonal
entry is zero because that forcing has recipient0 component zero.

Exact elimination, equivalently the Schur complement of K/255, gives

    det J9=365313976064/52200625 !=0,
    Schur= - (w^T/510)(K/255)^(-1)(v/510)
          =4281023157/562351180 >0.                       (44)

Thus the implicit function theorem supplies a UNIQUE nearby real
owner-indifference branch(q(c),z(c)), with

    z'(c_0)=-(1/4)/Schur
           =-140587795/4281023157 <0.                    (45)

For a further integer check, the determinant of the9x9 integer matrix
inside(43) is16335113998573531131494400000; dividing by510^9 gives(44).
All these are exact rational calculations, not a floating sign inference.

### 16.3. Why this excludes every nearby legal four-periodic exact NE

In a sufficiently small full sixteen-hazard neighborhood, all old scheduled
hazards stay proper and all seven margins(42) stay strictly positive.
Any exact terminal Nash profile there MUST set those seven inactive
hazards to zero. Indeed every phase is reached with positive probability,
so a strict endpoint violation at a date produces a profitable complete
one-date replacement; a positive hazard on a strictly inferior Quit
endpoint is impossible. The other eight proper hazards must therefore
satisfy their owner equalities.

If the remaining new hazard z=0, local invertibility of the old8x8
Jacobian forces q=q*: its eight equations are independent of c at z=0.
But for c>c_0 the new C0 Quit endpoint is strictly profitable, contradicting
terminal Nash. If z>0, it is proper in this neighborhood and must also
satisfy its endpoint equality. The unique nine-equation solution is then
the branch(45), whose z is strictly NEGATIVE for c>c_0 sufficiently close.
This contradicts legality. These two cases prove the local falsifier.

No agency restriction was used in the necessary conditions: the profitable
one-date endpoint replacement is one allowed complete private law, and
its realized gains are multiplied by the strictly positive probability of
reaching that date. Nearby opponent clocks remain geometrically proper,
so actual phase values and all endpoint comparisons have their intended
terminal meaning, including late deadlines and Never.

### 16.4. Consequence for a genuinely global producer

This test rejects continuing one chosen exact four-phase equilibrium
through successive inactive walls merely by activating the violating
player. Here even the whole nearby exact four-periodic equilibrium set
disappears on the forward side of the wall. The original game could still
have a distant four-periodic equilibrium, another period, a different
support or profiles with arbitrarily small terminal regret; none is
excluded. In particular preserving the old payoff, ancestry or branch
would impose an artificial restriction on target-free existence.

Any global homotopy/selection argument must explicitly permit a distant
source/payoff/support jump or a truly approximate mechanism. This scoped
falsifier belongs in the notebook, not in a new export or a positive-gap
claim against unrestricted actual profiles. No full bifurcation
classification is needed for the direction-changing conclusion.

## 17. Singleton concentration is already consumed

A supplied independent-clock family concentrating terminal absorption on
one singleton, with every outsider's full deviation debt tending to zero,
does not require preservation of its calendar or payoff approximants.
Under the owner's punishment normality, the fixed singleton reward is a
uniform-equilibrium payoff. This is an existing composition, not new
counterexample-class elimination here.

The canonical proof and exact source correspondence are in
[`CODEX_MORSE__GLOBAL_QUITTING_OBSTRUCTION`](CODEX_MORSE__GLOBAL_QUITTING_OBSTRUCTION.md),
under `QCUT-O1` and `QCUT1`–`QCUT7`, with independent checks in
[`CODEX_NOETHER's quantile review`](../feedback/CODEX_MORSE__QUANTILE_PUNISHMENT_REPAIR__BY_CODEX_NOETHER.md)
and
[`CODEX_BROUWER's quantile review`](../feedback/CODEX_MORSE__QUANTILE_PUNISHMENT_REPAIR__BY_CODEX_BROUWER.md).
Its direct first-positive-owner-atom adapter supplies approximate solo
roots to `isUniformEquilibriumPayoff_soloReward_of_approximate_caps`
in `UniformEquilibrium/Quitting/Punishment/ApproximateCompletedCycle.lean`.
The alternative quantile proof keeps a finite independent prefix and
replaces only its tail; its owner bound includes all deadlines and Never,
also for negative singleton rewards.

In particular, the growing-period interior-cyclic concentration arm is
already covered, as recorded in [the current frontier, Section 6](../FRONTIER.md).
Our independent reconstruction supplies confirmation, not a new producer,
consumer, or source extension. The genuinely open next question is how
to produce and consume the remaining all-hazards-small family without
public correlation or restricting complete private-clock deviations.

## 18. A fixed-period pair-root grammar cannot cover all completions

Status: ordinary proof draft, not independently reviewed or Lean-checked.
This is a direction-changing restriction test, not an export candidate,
new solved-table class, or positive-gap example against every private law.

### 18.1. Exact raw family and claimed grammar failure

For each real K>=4, define a four-player quitting table G_K as follows.
The singleton rows are

    r(0)=(1,4,0,0), r(1)=(4,1,0,0),
    r(2)=(0,0,1,4), r(3)=(0,0,4,1).

For every pair S, each participant receives4 and every nonparticipant0.
For every triple S, each participant receives K and its nonparticipant0.
The grand row is(-1,-1,-1,-1). Live and Never rewards are zero. Coins
are independent across players and dates; a deviation replaces the entire
private date-or-Never law. Let E_K(sigma) be maximum full terminal regret,
over all players and all such replacements.

Fix any positive integer L. The tested grammar P_L consists of ALL
L-periodic independent root arrays q_(t,i) in[0,1], subject only to at
most two positive coordinates at every phase. Support labels may change
arbitrarily between phases and between reward tables or accuracies.
Sure roots, empty roots, unused players and every initial phase are allowed.
Only the prescribed profile is restricted; deviations are unrestricted.

Claim: there exist K_L>=4 and gamma_L>0 such that

    K>=K_L and sigma in P_L  ==>  E_K(sigma)>=gamma_L.     (52)

The thresholds are existential, not numerically produced. Taking the
maximum threshold and minimum gap over L=1,...,H gives the same conclusion
for every grammar with period at most a fixed H. This is an exact family
of restricted-strategy falsifiers, not an explicit numerical K threshold.

Every G_K is nevertheless solved. At date zero let players0,1,2 Quit
surely and player3 Never. Participants receive K; a withdrawal receives
the pair's nonparticipant reward0. Player3 receives0 and a join receives
grand reward-1. This is exact terminal Nash against all replacements,
and its fixed target(K,K,K,0) is a uniform-equilibrium payoff. The first
root has three active players, outside P_L.

### 18.2. The vanishing-total-hazard boundary is impossible

Suppose(52) fails. Choose K_n>=n and L-periodic pair-root profiles with
full regret epsilon_n->0. Since the root array is a fixed finite cube,
pass to a convergent subsequence q_n->q*. On prescribed play only
singleton and pair coalitions can occur. All its recipient rewards are
in[0,4], independent of K_n. In contrast, immediate Quit by any replacing
player yields at least1: its resulting coalition has size at most three,
and its own rewards there are respectively1,4,K_n. Consequently

    U_n,i>=1-epsilon_n.                               (53)

First exclude q*=0. Let a_n,i=sum_t q_n,t,i and A_n=sum_i a_n,i.
All-zero profiles already have regret1, so A_n>0 eventually. Extract
w_i=lim a_n,i/A_n with w>=0 and sum_i w_i=1. Since L is fixed and all
hazards tend to zero, one period has singleton-i first-stop mass
a_n,i+O(A_n^2), pair mass O(A_n^2), and total absorption probability
A_n+O(A_n^2). Geometric repetition therefore gives

    U_n,i -> v_i=w_i+4*w_m(i),                        (54)

where m exchanges0 with1 and2 with3. This expansion uses only bounded
prescribed singleton/pair rewards; the diverging triple rewards never
appear. It also proves the analogous deleted-player expansion whenever
w_i<1:

    payoff_i(Never,sigma_n,-i) -> (v_i-w_i)/(1-w_i).    (55)

Indeed deleting i replaces A_n by A_n-a_n,i, keeps the opponents'
first-order singleton masses, and still permits only bounded singleton
and pair rewards on the deviating path. Equation(53) gives v_i>=1,
equivalently Gamma*w>=0 for the hard paired singleton matrix.

This already forces every w_i strictly positive. Put A=w0+w1 and
B=w2+w3. Neither can be zero, since the other group's rows would be
negative. The four inequalities are

    3*w1>=B, 3*w0>=B, 3*w3>=A, 3*w2>=A.

Thus all w_i>0 and all w_i<1. Never's full-regret bound and(55) now give

    w_i*(v_i-1)/(1-w_i)<=0.

Together with v_i>=1 this forces every v_i=1. But(54) has
sum_i v_i=5, a contradiction. Thus the limiting root array has positive
total hazard. This is the complete-deviation check at the null boundary;
one-row local Nash errors alone would not suffice.

### 18.3. Sure roots are impossible, and triple deviations remove pairs

There is no sure coordinate in q*. Otherwise choose the first phase t
in the initial period containing one. Every earlier limiting root has
all coordinates strictly below one, so its joint probability of reaching
t is bounded below by a positive constant. Choose a sure player a there.
The limiting root has at most one further potentially active player b.
There is an inactive player i whose favorite mate is not a. If b is its
mate, b cannot stop alone while a quits surely; if b is not its mate,
no possible singleton at that root pays i positively. Pair absorption
pays i zero in either case. Therefore i's conditional prescribed payoff
at phase t tends to zero: the chance of surviving a's coin tends to zero,
and all later prescribed payoffs are bounded by4. Immediate Quit still
pays at least1. Following prescribed behavior before t and deviating
there gives a positive initial gain, contradicting epsilon_n->0.

It follows that the joint reach of EACH of the L phases is bounded
below. Let s_n,t be that joint reach. Copying the prescribed behavior
before t and then using any complete replacement implies that every
conditional suffix debt is at most epsilon_n/s_n,t. In particular each
immediate Quit endpoint is at most4+epsilon_n/s_n,t.

At a phase with active pair a,b, choose any inactive player i. Its pure
Quit receives K_n on the simultaneous a,b-quit event, while all its other
possible rewards are nonnegative. Hence

    K_n*q_n,t,a*q_n,t,b <= 4+epsilon_n/s_n,t.

Thus every limiting root has at most ONE positive coordinate. The limit
is an actual singleton calendar with positive total hazard, proper roots,
and every phase payoff at least1. Its actual values converge from those
of q_n, since the joint geometric denominator stays strictly positive and
all prescribed rewards are the same bounded singleton/pair rows.

### 18.4. The limit would be a forbidden balanced singleton calendar

At a positive limiting root with owner j and hazard p in(0,1), j's
immediate Quit endpoint tends to1. Indeed the only possible additional
active coordinate tends to zero, and j's endpoint only uses its singleton
one and pair-participant four, never K_n. The conditional Nash bounds
on both Quit and Continue, together with the policy mixture and p>0,
force the limiting actual value u_t,j=1. More explicitly, if delta is
the conditional debt bound, the policy identity bounds
`|u_t,j-Quit_t,j|` by delta times a constant depending only on p.

The limit therefore has the exact singleton arc, all-player floor1 and
active owner value1. At any empty phase, assign the next positive phase's
owner; the values remain unchanged until that phase, so its active-value
condition also holds. At least two distinct owners occur: otherwise a
nonmate of the sole owner would have payoff zero, contradicting the
floor. Thus every deleted player has a positive opponent clock.

For completeness, such a balanced calendar is impossible for these
singleton rows at ANY finite period. Start at a positive owner-j phase.
The next j value remains1. Each nonmate i has singleton reward zero at
j's stop, so its next value is u_t,i/(1-p)>1. Follow to the first
different positive owner. All intervening positive j phases keep j's
value1 and increase the nonmates' values, so that first different owner
must be m(j). Its reward four to j forces j's following value
`(1-4*a)/(1-a)<1`, violating the floor. Opponent divergence ensures that
different owner exists. This is exactly the previously known balanced
singleton obstruction, not a newly claimed lemma here.

All compactness alternatives have contradicted epsilon_n->0. Therefore
there cannot be K_n->infinity with inf_(sigma in P_L)E_Kn(sigma)->0,
which is equivalent to the uniform-tail positive gap(52).

### 18.5. Source boundary and next mechanism

The initial bounded overlap route was the interior-cyclic/vanishing-hazard
heading in [the current frontier](../FRONTIER.md), followed by
`PeriodOneNormalizedSourceLimit.selectedNeverPayoff_tendsto` and the
same-source endpoint calculations in
`UniformEquilibrium/Quitting/Cycles/PeriodOneVanishingHazardEndpointLimits.lean`.
The null-boundary calculation above is an elementary fixed-period version,
proved explicitly rather than transferred without matching hypotheses.
The generic balanced obstruction is
`BalancedSingletonCycleCertificate.exists_escortCycle` in
`UniformEquilibrium/Quitting/Cycles/CyclicSingletonEscort.lean`;
`not_nonempty_balancedSingletonCycleCertificate` in
`UniformEquilibrium/Quitting/Classification/QuietExtension/CappedClockPairedCycleExclusion.lean`
records it for the paired capped-clock family. Its separate family
hypotheses are not assumed for G_K; the common-singleton proof is given
above. Narrow checks in the maintained frontier/toolkit and the bounded
periodic-format note found no identical arity test. This is not an
exhaustive novelty assertion.

The falsified implication is UNIVERSAL completion coverage by a fixed
period bound and pair-only roots, even permitting arbitrary distant
support selection and approximate rather than exact Nash. It says
nothing against unbounded periods, three-/four-active roots, or a
disjunction that first consumes already-solved persistent-base cases.
The fixtures are precisely solved by the latter source. No remaining
counterexample class has shrunk.

The next global construction must admit genuinely larger simultaneous
roots or explicitly discharge those solved-base alternatives before
restricting its grammar. Another pair-calendar neighborhood would not
resolve the obstacle tested here.

## 19. A complete passive-reward ray by symmetric/asymmetric joint clocks

An explicit symmetric/asymmetric branch switch produces exact private-
clock terminal equilibria throughout the raw reward family below. The
same profiles produce fixed uniform-equilibrium payoffs. All persistent-
base selections fail on this family; no arbitrary-completion or arbitrary-
Fin4 coverage is asserted.

### 19.1. Self-contained theorem and exact raw data

There are four players 0,1,2,3. Their original singleton rewards are

    r(0)=(1,4,0,0),    r(1)=(4,1,0,0),
    r(2)=(0,0,1,4),    r(3)=(0,0,4,1).

Define the mate permutation m=(0 1)(2 3). The allowed parameters are

    T=(5+sqrt(5))/2,
    T<A<4,
    D=sqrt((4-A)/(A-1)),  J=(A-1)*D,
    0<B<=J,
    C=(1-D)*(1-J),
    Kcrit=C/(1-sqrt(D))^2,
    0<=K<infinity.

In this range 0<D<(3-sqrt(5))/2<1 and 0<J<1, so C>0 and
0<Kcrit<infinity. Define the complete nonsingleton table by

| S | r(S) |
| --- | --- |
| 01 | (A,A,K,K) |
| 02 | (B,K,-B,K) |
| 03 | (-B,K,K,B) |
| 12 | (K,-B,B,K) |
| 13 | (K,B,K,-B) |
| 23 | (K,K,A,A) |
| 012 | (K-1,K-1,K-1,K) |
| 013 | (K-1,K-1,K,K-1) |
| 023 | (K-1,K,K-1,K-1) |
| 123 | (K,K-1,K-1,K-1) |
| 0123 | (-1,-1,-1,-1) |

There is no normalization or modification of these original rewards.
Live and Never pay zero, randomization is private and independent, and
every deviation replaces a complete behavioral law, including Never.

Theorem: for EVERY allowed A,B,K, the ORIGINAL game has an exact terminal
Nash profile against every complete unilateral replacement. Its actual
value at each initial phase is a uniform-equilibrium payoff, with the
same profile supplying all positive accuracies over sufficiently long
finite horizons. No payoff translation, public correlation, supplied
root or limiting behavioral law is an input. The profile is constructed
below solely from the raw parameters, before choosing an accuracy.

For proper hazards a,b in(0,1), use the four-date owner word0,2,1,3,
giving the owner's mate hazard b:

    phase0: q0=a, q1=b;
    phase1: q2=a, q3=b;
    phase2: q1=a, q0=b;
    phase3: q3=a, q2=b.

All omitted players Continue. Every listed coin is independently drawn,
across players and dates. These roots equivalently specify four independent
complete date-or-Never laws. The private randomization has no common seed.
The selection of a,b uses two branches, with a common exact boundary.

### 19.2. The symmetric branch and the exact switch boundary

Write qstar=1-sqrt(D). For 0<=K<=Kcrit define, for 0<q<1,

    f_K(q)=1+(A-4)*q/(1-q)
           -K*q^2-(1-q)^2*(1+(A-1)*q).             (56)

This function is continuous, extends to f_K(0)=0, and has derivative
f'_K(0)=-1. Therefore f_K(q)<0 for all sufficiently small positive q.
At the other endpoint its value is exactly

    f_K(qstar)=C-K*qstar^2
             =qstar^2*(Kcrit-K)>=0.               (57)

For completeness, put z=sqrt(D), so qstar=1-z and
4-A=(A-1)*z^4. The part of f_K(qstar) not containing K is

    1-z^2-(A-1)*(1-z)*(z^2+z^3)
      =(1-D)*(1-(A-1)*D)=C.

The intermediate value theorem supplies a q in(0,qstar] with f_K(q)=0.
Select any such q and put a=b=q. When K=Kcrit take q=qstar exactly.
This includes K=0; no division by K or positive K hypothesis is used in
this branch. No uniqueness or continuity of the root selection is claimed.

### 19.3. The asymmetric branch above the switch

For K>Kcrit set

    x=C/K,  s=1-D+x,
    a=(s+sqrt(s^2-4*x))/2,
    b=(s-sqrt(s^2-4*x))/2.                          (58)

Here 0<x<(1-sqrt(D))^2. Hence the discriminant is
positive, 0<b<a<1, and

    ab=x,       (1-a)*(1-b)=D.                      (59)

Indeed the discriminant factors as
`[x-(1-sqrt(D))^2]*[x-(1+sqrt(D))^2]`; positive roots sum to s, and
their Continue probabilities have positive sum 2-s and product D.
Here s<2 because x<(1-sqrt(D))^2<1. In particular neither root
reaches or exceeds one.

At K downarrow Kcrit, both roots tend to qstar: the discriminant
vanishes and a=b=1-sqrt(D). Thus the symmetric boundary and the limiting
asymmetric policy agree exactly. The theorem uses the IVT branch below
and the explicit radical branch above this boundary, not an asserted
globally unique continuation through every possible equilibrium branch.

### 19.4. Actual values and both owner equations

Let tau=(0 2 1 3), and let tau act on payoff coordinates in the usual
way. Both the raw table and the root calendar are equivariant under
this permutation/phase shift. Define

    d=(1-a)*(1-b),    x=a*b,
    L=1+(A-1)*b,      H=1+(A-1)*a,
    W=K*x+d*L,        Z=K*x+d*H,
    U0=(L,H,W,Z),     Ut=tau^t(U0).                (60)

Here tau acts by (tau u)_i=u_(tau^(-1)i). In the symmetric branch
d=(1-q)^2; only in the asymmetric branch and at the switch is d=D.

These will be shown to be ACTUAL policy values, not supplied arbitrary
continuations. At phase0 the two active players' pure Quit endpoints
are L and H. Their Continue endpoints are respectively

    4*b+(1-b)*Z,       4*a+(1-a)*W.

Thus both active players are indifferent exactly when

    Z=1+(A-4)*b/(1-b),
    W=1+(A-4)*a/(1-a).                            (61)

In the symmetric branch both equations are precisely f_K(q)=0, so the
IVT has supplied BOTH owner equalities, including at the boundary.

In the asymmetric branch d=D and D^2=(4-A)/(A-1). Subtracting the
right side of the W equation from W and using a+b-ab=1-D gives

    W-[1+(A-4)*a/(1-a)]
      =K*x+D-1+(A-1)*D*[b+a*(1-b)]
      =K*x-(1-D)*(1-(A-1)*D)=0.

Interchanging a,b gives the Z identity. Thus neither owner equation
was discarded by solving only their difference or sum.

For passive player2 at phase0, the only nonzero absorbed reward is
the pair01 reward K, of probability x. Joint Continue has probability
D, and the next phase's player2 value is L. Therefore its policy
recursion is W=K*x+d*L. The same argument gives player3's recursion
Z=K*x+d*H. The active policy recursions follow from(61) and their
indifference. Thus ALL sixteen coordinate policy recursions hold,
by equivariance. Joint survival per period is d^4<1, so these bounded
recursions uniquely identify the actual geometric policy values.

### 19.5. Every inactive endpoint, on both branches

At phase0, player2's pure Quit endpoint is

    Q2=d+B*(b-a)+(K-1)*x,

and player3's is

    Q3=d+B*(a-b)+(K-1)*x.

These account respectively for no opponent Quit, either sole opponent,
and both opponents. In particular the triple term is the ORIGINAL
K-1, not a clipped or discarded reward. Continue equals W or Z by
actual policy evaluation. The endpoint margins are exactly

    W-Q2=(A-1)*d*b+B*(a-b)+x,
    Z-Q3=(A-1)*d*a-B*(a-b)+x.                     (62)

For a=b=q these are BOTH

    (A-1)*(1-q)^2*q+q^2>0.

For the asymmetric branch they are respectively

    J*b+B*(a-b)+x>0,
    a*(J-B)+B*b+x>0,

because d=D, 0<B<=J and a>b>0. Equivariance checks all
eight inactive endpoints at the other three phases. Along with both
active equalities per phase, this verifies all sixteen local endpoint
pairs. Simultaneous pair quits and the triples caused by a unilateral
Quit are explicitly included.

### 19.6. Complete caps and fixed-profile uniform payoffs

Each player has one a coin and one b coin per period. Deleting that
player leaves three of each, with opponent survival d^3<1 per period.
The exact policy equations and endpoint inequalities therefore iterate
to a bound on EVERY complete replacement, with vanishing remainder
controlled by the deleted geometric clock. Pure Never and arbitrarily
late deadlines satisfy the same comparison. The profile is exact
terminal Nash at every initial phase.

For any finite bound M on the original table's absolute rewards, the
same profile has delivery error at most M*C_hor/N and full horizon
regret at most2*M*C_hor/N, where

    C_hor=1+4/(1-d^3).

Thus every fixed actual value Ut in(60) is one uniform-equilibrium payoff,
chosen before accuracy. More explicitly, if
M=max_(i,S)|r_i(S)|, then for every epsilon>0 the SAME selected profile
is epsilon-horizon Nash and delivers Ut within epsilon whenever
N>=2*M*C_hor/epsilon. The table-specific
M may grow with K; no bound uniform over changing reward tables is
needed. The calendar and targets need not be inherited from any old
certificate or approximate family.

The clock estimate is independent of the deviator's rule: absorption
occurs no later than the first opponent Quit. At each complete block of
four dates its surviving probability is multiplied by d^3, so the sum
of opponent live probabilities is at most4/(1-d^3). Iterating the
coordinate Bellman inequalities against an arbitrary replacement gives
the actual terminal cap Ut_i; the tail vanishes even for Never. Comparing
the terminal reward with its finite-horizon delivery loses at most M
times this live-time budget divided by N for either the prescribed
profile or ANY replacement. This proves the displayed delivery and
regret bounds, with no restriction to cyclic, stationary or finite-menu
deviations.

### 19.7. What the high-K branch actually synthesizes

At fixed A,B and K->infinity,

    a -> 1-D,    b ~ (1-J)/K,
    K*ab=C.

Thus a macroscopic independent owner clock coexists with a genuinely
rare joint collision. Its passive reward K compensates the vanishing
probability and retains a finite continuation contribution. The actual
policy remains geometrically proper uniformly in this limit, because
the deleted survival remains D^3. Dropping the rare collision BEFORE
evaluating its payoff would destroy the construction.

At the boundary A downarrow T with FIXED K>0 and a fixed admissible B,
J approaches1, C approaches0, Kcrit approaches0, and the eventual
asymmetric profile approaches the golden singleton calendar
`a=(sqrt(5)-1)/2, b=0`. For A>T the positive rare mate hazard and
passive pair transfer repair that calendar's violated favorite-join
cap. This gives a concrete continuation mechanism through a reward
threshold, not an arbitrary local IFT neighborhood or ancestry claim.
The qualification K>0 is essential: at K=0 the symmetric root instead
approaches a=b=(3-sqrt(5))/2. If K varies with C, other branch limits
may occur; the theorem asserts no universal golden limit along such paths.
To verify the K=0 assertion, put p=(sqrt(5)-1)/2 and c=1-p. At A=T,

    (1-q)*f_0(q)=(T-1)*q*(q-c)*(q-p)*(q-(1+p)).

The only nonzero root at or below the limiting endpoint qstar=c is c.
The derivative f'_0(0)=-1 uniformly for A near T excludes a limiting
zero root. Compactness of the selected q in[0,qstar] then forces q->c.

An exact small parameter instance is A=19/5, B=1/2, K=10. Here
D=1/sqrt(14), J=sqrt(14)/5, and(58) is an exact radical policy.
Numerically a is about0.725771 and b about0.0254085, only as a check;
the source and proof above are exact.

### 19.8. Whole persistent-base exclusion for every K>=0

For EVERY sure owner j, its mate has joining-minus-passive
gain A-4<0 when the other nonowners Continue. Its other noncollider
has gain -B<0. If one further nonowner quits, either player's gain is
`(K-1)-K=-1`; if both do it is `-1-K<0`. Both are strictly dominated
Quitters in the ENTIRE induced mixed game. The remaining nonowner
kappa(j), with kappa=(0 3 1 2), then has gain B>0 and Quits surely.
The full induced Nash set is this unique point. There owner j gets
-B by Quit and0 by Continue, while all-opponents-Continue mass is
zero. No punishment value can repair its leave gain B.

This also excludes every larger persistent base and free set, not just
singleton bases. Fix j in the base. Were the required leave, free-Nash
and outsider-no-join signs all true, the remaining base players' sure
Quits, the free players' mixed actions and the outsiders' Continues
would together constitute a Nash point in the FULL j-induced game.
Its uniqueness would force the point above and its strictly profitable
owner leave, a contradiction. There is no missing tail coefficient:
the sure kappa(j) Quit makes every all-opponents-Continue probability
zero. This is a whole-correspondence calculation for all K>=0.

The exact source objects inspected are `quittingPersistentBaseUtility`,
`quittingPersistentBaseNashSet`, `quittingPersistentBaseRoot` and
`quittingPersistentBaseRoot_free_purePayoff_le`
(`UniformEquilibrium/Quitting/Root/PersistentBaseInducedGame.lean`), and
`nonempty_quittingPersistentBaseCertificate_of_inducedNash` and
`exists_uniformPayoff_of_persistentBase_inducedNash_signs`
(`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseNashSemanticAdapter.lean`).

### 19.9. Every proper-child raw F/J withdrawal test fails

For EVERY nonempty proper child E choose j in E with kappa(j) outside.
Such a j exists because kappa is a four-cycle. Use the singleton
coalition{j} and outsider kappa(j). Its joining gain is B>0. For ANY
permitted child donor the advancement gain is respectively

    donor j:                 0,
    donor m(j):              A-4<0,
    other noncollider donor: -B<0.

The unique positive-gain donor kappa(j) is not in E. Withdrawal by a
nonmember has gain zero. Withdrawal by the member j has gain equal to
its selected restart floor minus its own singleton1. Each of the five
raw withdrawal kinds has floor at most1 on this literal singleton:
the patient floor is at most max(1,0)=1; the deadline/cancel floors
are at most0; the evaluated security minimum is at most0; and the LP
security maximum is at most1, since its feasible floor has the literal
singleton constraint. Hence every withdrawal gain is nonpositive.

For any nonnegative donor weights, every F/J weighted left side is
therefore nonpositive and cannot dominate the strictly positive outsider
gain. Requiring the additional Never row cannot repair this failed
joining row. Thus all the named F/J-only and N/F/J raw child certificates fail
over ALL children, weights and withdrawal kinds, including the smaller
advancing-only capped-clock cone. This is a raw coefficient witness, not
a claim that every arbitrary child strategy fails.

The inspected definitions are `WithdrawalFutureJoinKind.gain` and
`WithdrawalFutureJoinRewardCertificate.join_row`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/WithdrawalFutureJoinRaw.lean`)
and their floor definitions in the same subtree's
`PatientWithdrawalRaw.lean`, `DeadlineWithdrawalRaw.lean`,
`DeadlineWithdrawalRestartPointwiseCore.lean`,
`DeadlineWithdrawalSecurityMixedPointwise.lean`,
`DeadlineWithdrawalSecurityLP.lean` and
`CappedClockPointwiseDomination.lean`.

### 19.10. Singleton and ALL response-quotient comparisons

The original singleton matrix, with recipient rows and quitter columns,
is

    Gamma=[[0,3,-1,-1], [3,0,-1,-1],
           [-1,-1,0,3], [-1,-1,3,0]].

Its determinant is45. Its inverse has diagonal2/15, mate entries7/15
and cross-pair entries1/5, all strictly positive. If w>=0 is nonzero
and Gamma*w>=0, then w is strictly positive: if one coordinate were
zero, its mate's row would force the other pair's two coordinates zero,
and a cross row would force the remaining coordinate zero. Hence the
homogeneous complementarity system Gamma*w>=0, w_i*(Gamma*w)_i=0
has no nonzero solution; Gamma is R0, and its nonnegative-inverse degree
is +1. In particular the existing ordinary/projective non-Q and
degree-not-one exits do not apply. Each singleton column also has two
outsider rewards0 below their own singleton1, excluding the strict
positive-column source.

There is no proper balanced singleton word of ANY finite period. Its
active owner value must be1 and every player's phase value at least1.
At a transition from a nonempty run of owner i to a different owner j,
if j is not m(i), j's rewards during the run are zero and its value at
the next j root is1. Positive run absorption then makes its value at
the run's start strictly below1. Thus every distinct-owner transition
must stay within one mate pair. Such a cyclic word uses at most that
pair and gives the other pair payoff zero, another contradiction.
Zero-hazard dates may be deleted. The positive directed graph of Gamma
also consists only of the two mate transpositions, so no relabeling gives
the positive three-cycle or four-cycle required by the named cyclic-child
singleton and signed-four-cycle raw sources. These facts do not exclude
general singleton strategies with arbitrary periods and approximate caps.

For response-invariant quotients one must test the actual raw stationary
displacement, not just Gamma. The necessary within-block singleton-row-
sum identities leave exactly the following seven set partitions:

    0|1|2|3;  01|2|3;  0|1|23;  02|13;
    03|12;    01|23;   0123.

The other eight partitions fail a singleton row-sum identity. Of the
seven displayed, four fail actual response invariance on the closed
block-constant cube. Let H(q) be the zero-discount displacement from
`quittingDiscountedDisplacement`. Exact row witnesses are

| partition | block-constant q | unequal rows of H(q) |
| --- | --- | --- |
| 01\|2\|3 | (0,0,1,0) | H0=B, H1=-B |
| 0\|1\|23 | (1,0,0,0) | H2=-B, H3=B |
| 02\|13 | (1,0,1,0) | H0=B, H2=-B |
| 03\|12 | (1,0,0,1) | H0=-B, H3=B |

They fail because B>0, independently of K. The mate-pair partition
01|23 IS response-invariant by the tau^2 automorphism, and the all-player
partition IS invariant by tau. Their quotient matrices are respectively
[[3,-2],[-2,3]] and [1], with positive determinants5 and1, positive
inverses and degree+1. The discrete quotient is Gamma itself. Therefore
EVERY actual quotient fails the currently favorable negative-determinant/
nonnegative-inverse or degree-not-one exits; no claim that all quotients
are absent is made.

The exact inspected quotient objects are
`QuittingResponseInvariantOnUnitCube` and
`quittingSingletonBlockRowSum_eq_of_responseInvariant`
(`UniformEquilibrium/Quitting/Stationary/ResponseInvariantQuotient.lean`),
`quittingDiscountedDisplacement`
(`UniformEquilibrium/Quitting/Stationary/DiscountedDisplacement.lean`),
and `finFour_exists_uniformEquilibriumPayoff_of_responseQuotient_nonnegative_inverse`
(`UniformEquilibrium/Diagnostics/Quitting/FinFourResponseQuotientCriterion.lean`).
The last criterion explicitly requires determinant<0, not merely a
nonnegative inverse. The literal cyclic-child source inspected is
`GameTheory.CyclicChildJointPhase.RawTable`
(`UniformEquilibrium/Quitting/Cycles/CyclicChildJointPhaseSource.lean`),
whose three-child singleton pattern has a positive directed three-cycle.

### 19.11. Other named raw-data coverage boundaries

These are bounded comparisons with literal criteria, not a claim of
exhaustive novelty or disjointness from unspecified qualitative IFT
neighborhoods. All label choices in each listed finite matching/base
criterion are included.

For the paired affine raw-region producer, each recipient here has TWO
singleton quitters below its own singleton. But
`RawRegion.eq_partner_of_singleton_lt`
(`UniformEquilibrium/Quitting/Cycles/PairedCycleSchedule.lean`) permits
only the unique scheduled partner. Thus no schedule meets that raw region.
For the strict/weak crossed-matching sources, the favorite is forced by
the unique positive singleton difference, and its required participant
cap A<=1 fails. The positive-inverse crossed source also fails every
scheduled matching: its scheduled singleton must be below own, so the
mate pair is unscheduled and its A>1 violates one of the two unscheduled
participant caps. These are the actual `RawSource`, `WeakRawSource` and
`InverseRawSource` in
`UniformEquilibrium/Quitting/Cycles/CrossedMatchingPhaseSource.lean`.

The below-singleton raw family forces the favorite mate and row scale1
from the singleton rows. Its common scheduled premium<-1 would require
both participants of each cross scheduled pair to receive a negative
reward. But every cross pair here has one participant B>0. Hence
`GameTheory.PairedCycle.BelowSingleton.RawFamily`
(`UniformEquilibrium/Quitting/Cycles/BelowSingletonJointPhaseSource.lean`)
fails every labeling. The two-pair join-cap criterion requires
r_i({i,mate(i)})>=r_i({mate(i)}) for every scheduled mate, plus outsider
insertion caps at the own singleton. Its joining-versus-partner condition
fails each matching:
favorite pairs have A<4, whereas every cross matching contains a
participant -B below its passive singleton0.

For the pair-mass raw bounds,
`hasQuittingActualNonconcentratedGroupExclusion_half_of_twoPairRewardBounds`
(`UniformEquilibrium/Quitting/Paths/TwoPairGroupExclusion.lean`) requires
every singleton's surplus average on either recipient pair to be
nonpositive. The singleton of a mate of a recipient yields an average
at least1, for EVERY recipient partition, violating that requirement.
`hasQuittingActualWeakSubsetExclusion_zero_one_of_crossMassBounds`
(`UniformEquilibrium/Quitting/Paths/TwoPairCrossMassRewardExclusion.lean`)
requires the designated recipient's positive mate singleton surplus3
to be nonpositive; its sole favorable indicator is a PAIR coalition,
so no relabeling avoids this contradiction.

For premium criteria, both01 and23 are positive-premium traps since
A>1. Their union is the full core. Every player has the negative grand
premium -2, so there is no protected player, and all criteria requiring
nonnegative participant premiums fail. Empty/pair/triple greatest-core
criteria fail the core's size4. The weighted-floor criterion fails on
the grand coalition: every nonzero nonnegative weight vector gives a
strictly negative forced-Quit floor, since every participant grand
premium is -2. The boxed Nash-charge criterion requires every trap to
have size at least3, contradicted by01 and23. The mixed support-local
low/charge criterion also fails at either pair trap: the product root
giving both members hazard1/2 has each active Quit endpoint (1+A)/2>1,
and a pair trap cannot use the boxed-charge alternative. The same root
refutes `HasProductLowQuittingPremium`
(`UniformEquilibrium/Quitting/Classification/ProductLowQuittingPremium.lean`).
Finally every triple contains a cross pair with one negative join gap
-B, excluding raw triple sources requiring six positive pair joins.

For the four-joint local raw class centered at favorite participant5,
the declared radius is at most1/2, incompatible with A<4. The unbounded
four-joint rectangle class fixes favorite participant coordinates5 and
9/2, likewise incompatible with A<4. The common-large-pair-participant
source requires positive common participant rewards on all pairs,
contradicted by the cross entries-B. These comparisons concern these
declared raw classes, not every strategy architecture or every unquantified
neighborhood.

### 19.12. Whole positive singleton-word exclusion at the exact singleton rows

Consider the named chronological singleton word0,2,1,3 with ANY four
proper positive hazards p_i, indexed in chronological word order, and
its corresponding relabelings preserving the paired singleton pattern.
Each owner's mate occurs two phases later. Write u_i=1-p_i in(0,1).
An active owner's value must be its singleton1. Its Continue endpoint
collects zero at the next nonmate, reward4 if its mate quits at the next
phase, zero at the remaining nonmate, and value1 upon return. Therefore
the four owner-indifference equations, cyclically indexed, are exactly

    E_i=u_i*(4-4*u_(i+1)+u_(i+1)*u_(i+2))-1=0.      (63)

Put alpha=u0-u2 and beta=u1-u3. Subtract opposite equations:

    E0-E2=4*(1-u1)*alpha-u2*(4-u0)*beta,
    E1-E3=u3*(4-u1)*alpha+4*(1-u2)*beta.             (64)

All four coefficients displayed in these two rows are strictly positive.
The determinant of this two-by-two system is

    16*(1-u1)*(1-u2)+u2*u3*(4-u0)*(4-u1)>0.

Hence alpha=beta=0. Put u0=u2=x and u1=u3=y. The remaining equation
difference is (4+x*y)*(x-y)=0, so x=y=u. The common equation factors as

    u^3-4*u^2+4*u-1=(u-1)*(u^2-3*u+1)=0.

Its unique root in(0,1) is u=(3-sqrt(5))/2. Thus EVERY all-positive
proper owner solution for this named singleton word has the golden
hazards p=(sqrt(5)-1)/2, not only one locally continued branch.

At a root of owner j, its inactive mate has policy value H=2+p and
forced-Quit value 1+p*(A-1). Since T=3+p and p^2=1-p, the required
inactive inequality is exactly A<=T. Our strict A>T violates it.
Consequently this entire named positive proper singleton-calendar
architecture fails on the raw family, including any locally selected
positive branch at these exact singleton rows. No unspecified IFT
radius needs to be chosen. This does NOT exclude arbitrary owner words,
longer calendars, zero/sure hazards or general singleton strategies.

### 19.13. Source/consumer scope and the remaining global problem

The source is entirely raw: for the exact allowed A,B,K, equations
(56)--(59) PRODUCE the legal hazards. Equations(60)--(62) then identify
actual policy values and all endpoint signs. Deleted-player contraction
proves unrestricted terminal Nash and the finite-horizon bounds. This
is the same mathematical consumer chain represented by
`quittingSubBellmanValue_le_superSolution_of_survival_zero` and
`isεAsymptoticNash_quittingCyclicBehaviorProfile_of_quitError_exactContinue`
(`UniformEquilibrium/Quitting/Cycles/CyclicSupersolution.lean`), followed
by `quittingGame_fixedProfile_uniformPayoffWitnesses_of_terminalNash_exact`
(`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`).
These declarations are semantic consumer anchors; the raw source here
is the explicit mathematical hazard construction(56)--(59), with its
own full endpoint and clock proof. The comparison does not assert a
strategy-class completeness theorem.

What is removed is the need to stay on one locally continued equilibrium
branch, in one small reward neighborhood, or at uniformly tiny hazards.
The branch switch covers this ENTIRE nonnegative passive-reward ray while
every persistent-base selection fails. Its high-K branch couples a large
owner clock to a small collision whose reward contribution remains order1.

What remains is genuinely global: select a compensation architecture from
arbitrary collision data after the existing matrix, child and base exits
have failed. Nothing here shows that an arbitrary table admits the exact
symmetries, passive transfers or owner equations used above. The concrete
next question is whether a global construction can choose WHERE to retain
macroscopic joint roots and WHERE to disperse clocks, rather than enlarging
this family in further parameter directions.

## 20. An asymmetric exact calibration defeats a nonattainment guess

This is ordinary exact arithmetic, not independently reviewed or Lean-checked.
The three-player table has singleton rows

    r({0})=(1,0,2), r({1})=(2,1,0), r({2})=(0,2,1).

Every pair pays1/4 to each member and0 to its outsider; the grand coalition
pays−1 to each player; Never pays0. Symmetric stationary small hazards
approach terminal Nash, but no positive symmetric stationary hazard is exact.
The stronger guess that NO exact independent-clock equilibrium exists is
FALSE: use the three periodic independent hazard vectors

    q0=(1/15,0,1/6), q1=(0,1/6,1/15), q2=(1/6,1/15,0).

Each date has joint survival7/9. Direct Bellman recursion gives the ACTUAL
phase payoffs

    U0=(7/8,21/20,19/20),
    U1=(21/20,19/20,7/8),
    U2=(19/20,7/8,21/20).

At phase0 the Quit/Continue endpoint pairs for players0,1,2 are respectively

    (7/8,7/8), (59/72,21/20), (19/20,19/20).

Thus both active owners are indifferent and the inactive player has margin
83/360. The other phases are coordinate rotations. Every deleted player
leaves two opponents, each with per-period survival7/9; their joint survival
49/81 contracts. Telescoping the endpoint inequalities therefore caps ALL
finite deadlines and Never, hence every complete unilateral law. This is an
exact terminal Nash profile, not merely a root equilibrium with an unchecked
continuation value.

The failed step was to extend a symmetric recurrence to all support changes.
For comparison, writing h for a common hazard and α=3/4, the common Quit
endpoint is Q(h)=1−2αh−h²/2. All-active symmetric exact continuation requires

    Q(h_next)=[Q(h)−2h(1−h)]/(1−h)²<Q(h),

which forces increasing hazards while that symmetric regime persists. The
asymmetric pair itinerary above evades precisely that restriction. No claim
about all asymmetric profiles follows from the symmetric calculation.

There is also no conjecture-facing reason to seek another universal exact-NE
nonattainment theorem. Solan, *The Dynamics of the Nash Correspondence and
n-Player Stochastic Games* (2001), Theorem2.1, already obstructs exact sources
using a different three-player table. The original
[paper](https://www.math.tau.ac.il/~eilons/value4.pdf) was inspected at its
definition of admissible inverse iterates and Theorem2.1. Its printed claim
allows unbounded formal continuation vectors; actual terminal equilibria have
bounded continuation vectors, so the bounded semantic consequence is the
relevant one, not unrestricted formal inverse-iterate exclusion. The local
`SOLAN_2001__CLEANED_TEXT.md` records this distinction. Our displayed fixture
does not improve that boundary and is parked.

## 21. Negative private Never taxes admit a proper-sentinel cap pump

Ordinary exact mathematics, not independently reviewed or Lean-checked.
The GLOBAL question being tested is this: for every Fin4 table with own
singletons(1,0,0,0) and every η>0, are there a common finite menu
F_N={0,...,N−1,Never}, taxes b0=0 and −η≤b_i≤0, and an EXACT mixed Nash
law of the auxiliary payoffs

    U_i(p)+b_i P_p(T_i=Never)

whose ORIGINAL unrestricted exploitability tends0 as η tends0? Selection
ranges over ALL auxiliary equilibria and all N, changing with η. A tax is
paid according to the player's PRIVATE planned clock, even if someone else
quits first. It is neither a terminal-table perturbation nor a live-stage
reward. No public seed or chronology across accuracies is imposed.

The following construction answers the test positively on the rational
exact-common-menu obstruction, not on arbitrary tables. Core rewards for
T=S∩{0,1,2} are0 if T is empty, and otherwise

| T | (r0,r1,r2) |
| --- | --- |
| 0 | (1,7,7) |
| 1 | (7,0,7) |
| 2 | (7,7,0) |
| 01 | (6,8,7) |
| 02 | (9,7,5) |
| 12 | (7,5,8) |
| 012 | (7,6,6) |

Player3 receives−1 if it quits with a core player,1 if it is absent and
player1 or2 quits, and0 otherwise. Never pays0. This is the complete table.

### 21.1. Exact private-tax prefix transport

Suppose a finite common-menu tail is auxiliary Nash with taxes b, original
payoff u, marginal Never masses z, and AUGMENTED payoff v_i=u_i+b_i z_i.
Prepend an independent ordinary one-shot Nash root q against continuation v.
The resulting full law is exact auxiliary Nash with taxes

    b'_i=b_i ∏_{j≠i}(1−q_j).                       (T1)

Its augmented payoff is the ordinary root payoff against v. Indeed, if the
player Continues, both its conditional terminal payoff and its new tax
contribution have the common factor∏_{j≠i}(1−q_j); after this division the
tail objective is u_i+b_i z_i. If it Quits, no planned-Never tax is paid.
Every complete menu replacement decomposes into these current choices and
a conditional tail replacement. This proves the full finite-game claim.
Crucially(T1) uses OPPONENT survival separately for each player, not one
joint-survival multiplier for every tax.

### 21.2. A literal finite seed and the change of support

On the one-date menu choose independent Quit probabilities

    q=(3/5,13/20,3/10,1),
    b=(0,0,−11/20,−1657/1000).

The core Quit-minus-Never augmented gaps are

    1+q2−2q1=0,
    q0−2q2−b1=0,
    q1−2q0−b2=0.

The probability of some core Quit is451/500, while player3's ORIGINAL
Never value is151/200. Its tax makes Never equal to its prescribed Quit
payoff−451/500. The seed is therefore exact auxiliary Nash, with

    v=(1057/200,126/25,547/100,−451/500).

Player3 is PROPER: its seed clock is surely finite. This is the strategic
property to retain, not just a numerical continuation coordinate.

Put w0=451/500 and prepend the two-active root

    q0=h=w0/(1+w0)=451/951,
    q3=k=1−1/v0=857/1057, q1=q2=0.

Pivot Quit pays1 and Continue pays(1−k)v0=1. Player3 Quit pays−h and
Continue pays−(1−h)w0=−h. Player1's Continue-minus-Quit gap is

    −h+(1−h)(1−k)v1 ≥0

because v1−w0 v0=27293/100000>0. Player2's gap is
2h+(1−h)(1−k)v2>0. Thus this is an ordinary Nash root, and(T1) produces
another exact auxiliary law. Write its augmented payoff as

    V=(1,V1,V2,−w),  w=h,
    Vj=[7w0+v_j/v0]/(1+w0), j=1,2.

Then V1≥8w>w and V2>0. Its only nonzero taxes are

    B2=−55000/1005207, B3=−1657/1902.                (T2)

Player3 remains proper under this prefix.

### 21.3. A private pivot ladder actually makes all taxes vanish

Starting from this law, recursively prepend ONLY pivot0 with hazard

    h_n=w/[1+(n+1)w], n=0,1,... .                  (T3)

After n such prefixes the augmented values are

    V0(n)=1,
    Vj(n)=7+[Vj(0)−7]/(1+nw), j=1,2,
    V3(n)=−w/(1+nw).

Pivot Quit and Continue equal1. Player3's Quit value−h_n equals its
Continue value(1−h_n)V3(n), so prescribing Continue is optimal. Player1
Continues optimally exactly when V1(n)≥w/(1+nw), which follows from
V1(0)≥w; player2's gap is2h_n+(1−h_n)V2(n)>0. Therefore every root is
ordinary Nash against the actual AUGMENTED tail value, and(T1) applies at
every step. For each nonpivot,

    B_i(n)=B_i(0)/(1+nw).                          (T4)

All laws are finite private clocks on one common menu (n+2 finite dates),
not an execution of infinitely many predecessor roots. Player3 remains
proper on every one of these finite laws.

### 21.4. Original full caps, including after the entire menu

An auxiliary Nash inequality and |b_i|≤η imply that every original menu
deviation gains at mostη. For a finite common-menu profile, the full cap
is exactly the maximum of its menu cap and

    NeverReply_i+s_i ∏_{j≠i} z_j.                 (T5)

Indeed any pure date after ALL finite menu dates yields exactly this value;
arbitrary replacement laws average pure replies. The nonpivots have s_i=0.
The pivot has s0=1, but z3=0 by the retained proper sentinel, so its omitted
late value is already its menu Never reply. Since B0(n)=0, its ORIGINAL
full debt is exactly0. Thus the constructed original exploitability obeys

    E(n)≤(1657/1902)/(1+nw)→0.                    (T6)

This is a full original-game bound, not only a finite-menu or current-root
calculation. The actual original payoff converges to the SAME fixed target
(1,7,7,0): the pivot coordinate is exactly1, coordinates1/2 approach7
under the solo-pivot recursion, and player3 approaches0. One can instead
use terminal-all-errors payoff selection, which needs no target fixed by
the auxiliary source.

For every η>0, sufficiently large n gives BOTH |B_i(n)|≤η and E(n)≤η.
Hence infimum over the WHOLE negative-tax correspondence, with N free,
is0 on this fixture. This does not follow by taking taxes to0 on a FIXED
menu, whose exact Nash limit is the original last-date obstruction.

### 21.5. Source boundary and next mathematical question

The finite-law full-cap identity(T5) is the same semantic distinction
recorded by `singlePivot_pivot_fullCap_eq_max_menu_never_add_deletedNever`
and `singlePivot_nonpivot_fullCap_eq_menuCap`
(`UniformEquilibrium/Quitting/Terminal/SinglePivotFiniteMenuSource.lean`).
The finite Nash existence source is `exists_exactFiniteDeadlineTimingNash`
(`UniformEquilibrium/Quitting/Terminal/FiniteDeadlineNashExistence.lean`).
Neither theorem selects the proper-sentinel seed or the pump. The raw
seed, signs, and recursions above supply that step on this particular table.

The whole negative-tax selector is NOT thereby produced on an arbitrary
table. What this test removes is the proposed obstruction that negative
taxes could only return the robust bad common-menu branch: a distant
two-active support switch plus a retained proper sentinel bypasses it.
The open next question is whether an arbitrary table or its WHOLE taxed
Nash correspondence supplies an analogous proper-source/pump alternative,
with payoff and source allowed to change, or whether some entire
correspondence really fails. Merely postulating a seed satisfying a new
interface would not answer that source question.

## 22. Positive sentinel rewards defeat the ENTIRE negative-tax selector

This is a self-contained ordinary proof draft, not independently reviewed or
Lean-checked. It is a no-go for a specific auxiliary exact-source mechanism,
NOT a negative answer to uniform-equilibrium existence.

### 22.1. Exact table, agency, and quantifiers

There are four players0,1,2,3. The core rewards are determined only by the
core part T=S∩{0,1,2}: they are0 when T is empty and otherwise

| T | (r0,r1,r2) |
| --- | --- |
| 0 | (1,7,7) |
| 1 | (7,0,7) |
| 2 | (7,7,0) |
| 01 | (6,8,7) |
| 02 | (9,7,5) |
| 12 | (7,5,8) |
| 012 | (7,6,6) |

Player3 receives5 when3 is absent and T is nonempty,4 when3 is present
and T is nonempty, and0 when T is empty. This specifies all nonempty
coalitions. Every reward is nonnegative and at most9. Own singletons are
(1,0,0,0); live and Never pay0.

For every integer N≥1, all players independently choose a PRIVATE planned
clock in F_N={0,...,N−1,Never}. A unilateral deviation changes its entire
law. In the auxiliary finite normal-form game player i's objective is

    original terminal payoff + b_i P(own planned clock=Never),
    b0,b1,b2,b3≤0.                                 (A1)

The tax is paid whenever that PRIVATE plan is Never, including when another
player quits earlier. All exact mixed Nash components are in scope.
The original terminal reward is r(S), where S is the set of players at the
earliest finite planned date, and is0 if all plans are Never. Write U_i(p)
for its expectation. ORIGINAL full exploitability means

    E(p)=max_i [sup_{t∈{0,1,...,Never}} U_i(t;p_{−i})−U_i(p)].

The supremum also equals the supremum over arbitrary complete replacement
laws: a player's payoff is affine in its own private clock law. No public
signal, conditional correlation, or bounded-controller deviation restriction
is imposed.

**Claim A (all nonpositive magnitudes).** For EVERY b as in(A1), EVERY exact
auxiliary Nash law Continues surely at dates0,...,N−2. Its final-date law is
an exact one-date auxiliary Nash law with the SAME b.

**Claim B (small-tax full gap).** If −η≤b_i≤0 with0≤η≤1/100, every such
law has ORIGINAL full exploitability at least

    18/49−2η > 1/3.                               (A2)

This is uniform in N, b, and the entire auxiliary Nash correspondence.
Nevertheless the original table has profiles with full exploitability1/N.
Thus jointly increasing the menu and removing negative taxes does NOT give
a universal producer, although it does on Section21's different sentinel
completion.

### 22.2. Every pre-final tail is reached

Consider an auxiliary Nash law on a common menu with at least two finite
dates. Write q_i for its first-date Quit probability. A finite next-date
deviation pays NO Never tax. Nonnegativity of every realized reward ensures
that its future conditional contribution is nonnegative.

No core player can Quit surely at the current date:

- If q0=1, player2's current Quit payoff minus finite-next-date payoff is
  q1−2≤−1, forcing q2=0. Player1 then prefers Quit8 to Continue7 (Never
  adds a nonpositive tax), forcing q1=1. Player0 now earns6 by Quit but7
  by finite Continue, a contradiction.
- If q1=1 and q2<1, player0's analogous difference is q2−1<0, forcing
  q0=0. Player2 then prefers Quit8 to Continue7, forcing q2=1, a
  contradiction. If q2=1 instead, player1's Quit value5+q0≤6 is below its
  finite Continue value7.
- If q2=1, player1's difference q0−2<0 forces q1=0. Player0 then prefers
  Quit9 to Continue7, forcing q0=1; player2 now prefers finite Continue7
  to Quit5.

The core rewards are independent of player3's choice, so these comparisons
also apply if player3 mixes or quits surely.

Nor can player3 Quit surely. If it did, every core player's finite next-date
choice is effectively Continue now: absorption at the current date gives
it7 if an opponent core player Quits and0 otherwise. Never adds a
nonpositive tax and cannot improve this alternative. Thus the core
first-date probabilities form an ordinary zero-continuation one-shot Nash
root with gaps

    Δ0=1+q2−2q1, Δ1=q0−2q2, Δ2=q1−2q0.

The previous no-sure argument excludes core sure choices. All three core
probabilities must then be positive: q0=0 would force q1≥1/2 and then q2>0
and q0>0; q1=0 contradicts Δ0≤0; q2=0 contradicts Δ1≤0 with q0>0.
The three zero gaps give

    q*=(2/7,4/7,1/7), H*=P(some core Quit)=253/343.

Player3's prescribed Quit payoff is4H*. A finite-next-date deviation earns
5H* from current core absorption and a nonnegative contribution otherwise,
with no planned-Never tax. This is a strict improvement.

Consequently every player's first-date Continue probability is positive.
Conditional tails retain independence and remain exact auxiliary Nash,
with taxes rescaled as

    b_i^(t)=b_i/∏_{j≠i} S_j(t),                   (A3)

where S_j(t) is marginal survival to date t. A terminal tail-deviation gain
is weighted by JOINT prefix reach, but its tax change is weighted only by
the deviator's OWN prefix survival; division gives(A3). All denominators
are positive, and all rescaled taxes remain nonpositive, however large.
Applying the argument successively shows that every pre-final tail is
reached. No off-path subgame perfection has been assumed.

### 22.3. Every one-date taxed Nash payoff lies in a high box

Take arbitrary b0,b1,b2,b3≤0, with no size restriction. At the final date the
core Quit-minus-Never augmented gaps, independent of q3, are

    Δ0=1+q2−2q1−b0,
    Δ1=q0−2q2−b1,
    Δ2=q1−2q0−b2.                                 (A4)

Let v be the AUGMENTED Nash payoff. Every player can choose finite Quit,
so v_i is at least its current Quit value Q_i.

If no core player Quits surely, all three probabilities are positive.
Indeed q0=0 would force q1≥1/2 from Δ0≤0, contradicting Δ2≤0 with
q2<1. If q1=0 then Δ0>0 forces q0=1. If q2=0 then Δ1≤0 forces
q0=0. They therefore mix and(A4) vanishes. Writing e_i=−b_i≥0 gives

    q0=2/7+(2e0+e1+4e2)/7,
    q1=4/7+(4e0+2e1+e2)/7,
    q2=1/7+(e0+4e1+2e2)/7.                       (A5)

In particular q≥q* coordinatewise. The finite Quit values are

    Q0=1+5q1+8q2−7q1q2,
    Q1=8q0+5q2−7q0q2,
    Q2=5q0+8q1−7q0q1.

Each is multi-affine in the two displayed variables. Checking the four
corners of [q*_j,1]×[q*_k,1] gives respective minima31/7,19/7,34/7.
Hence every core coordinate v_i>2, and H≥H*.

If some core player Quits surely, either at least two do, only player0
does and q2≥1/2, or only player1 does and q0≥1/2. For only player0,
q1<1 and Δ1≤0 imply q2≥(1−b1)/2≥1/2. For only player1, q2<1
and Δ2≤0 imply q0≥(1−b2)/2≥1/2. Only player2 is impossible:
q0,q1<1 would give Δ0=2−2q1−b0>0.

With at least two sure core players every Q_i≥5, since each finite Quit
coalition contains another sure core player. In the case q0=1,q2≥1/2,
Q1=8−2q2≥6, Q2=5+q1≥5, and

    Q0=1+8q2+(5−7q2)q1≥5.

In the case q1=1,q0≥1/2, Q0=6+q2≥6 and Q2=8−2q0≥6; the
multi-affine Q1 has minimum4 on [1/2,1]×[0,1]. Thus the core
coordinates again exceed2 and H=1. Finally

    v3≥Q3=4H≥4H*=1012/343>2.                     (A6)

This lower bound uses the available finite Quit action, so it holds even
when player3 chooses Never with a large negative tax. We have proved the
uniform high-box conclusion v_i>2 for EVERY one-date auxiliary Nash law
and EVERY nonpositive tax magnitude.

### 22.4. The WHOLE earlier root correspondence is all-Continue

For an ordinary one-shot root against ANY continuation vector v_i≥2,
player3's gap is

    −H−(1−H)v3<0.

Hence q3=0 in every root Nash law. For the core the ordinary gaps are

    Δ_i=g_i+q_(i−1)−2q_(i+1)
        −v_i(1−q_(i−1))(1−q_(i+1)), g=(1,0,0),

with core indices cyclic. All-Continue is Nash. Every other support fails:
one active player's gap is g_i−v_i<0; support01 has
Δ0=(1−q1)(1−v0)−q1≤−1; support02 has
Δ2=−2q0−v2(1−q0)≤−2; support12 has the analogous Δ1≤−2.
If all three are active, summing their gaps gives

    ΣΔ_i≤1−Σq_i−2Σ(1−q_j)(1−q_k)≤−1.

For the last inequality the multi-affine expression Σq_i+2Σ(1−q_j)(1−q_k)
has vertex values6,3,2,3 according as0,1,2,3 coordinates are1, and hence
is at least2 throughout the cube. Every positive Quit probability requires
a nonnegative gap, contradicting these inequalities. Thus all-Continue is
the UNIQUE ordinary root Nash law throughout the high box.

By Section22.2 all conditional tails of an actual finite-menu auxiliary
Nash law exist and are Nash with the taxes(A3). At any such tail let b
denote its current rescaled tax vector. Write a_i=1−q_i, and let u_i and
z_i be the next conditional tail's ORIGINAL payoff and own Never mass.
Let A_i be player i's current-date expected reward on the event that at
least one opponent Quits, when i Continues. A deviation which Continues
now and uses that fixed conditional tail law has augmented payoff

    A_i+(∏_{j≠i}a_j)u_i+b_i z_i
      =A_i+(∏_{j≠i}a_j)[u_i+(b_i/∏_{j≠i}a_j)z_i].

The private tax term b_i z_i is NOT weighted by opponent survival. The
displayed rescaling is precisely what permits an ordinary root with the
next tail's AUGMENTED value; it includes taxes paid when another player
quits currently. Deviations between current Quit and this fixed conditional
Continue law show that the actual current root is Nash for that ordinary
root game. Starting with the final tail's high-box value from Section22.3,
uniqueness forces the previous root to be
all-Continue. That preserves the value and taxes. Backward induction forces
every pre-final root to be all-Continue. This proves Claim A without
selecting a preferred equilibrium branch.

### 22.5. Uniform small-tax gap and the original approximate bypass

Now0≤η≤1/100. No core sure choice occurs at the final date. If q0=1,
then Δ2≤−1+η<0 forces q2=0; Δ1>0 forces q1=1, contradicting
Δ0=−1−b0<0. If q2=1, Δ1≤−1+η<0 forces q1=0, and Δ0>0
forces q0=1, already excluded. Finally suppose q1=1. The case q2=0
forces q0=0 by Δ0<0 and then contradicts Δ2>0. Thus q2>0 and
Δ2≥0 gives q0≤(1+η)/2. If q0=0, Δ2>0 forces q2=1 and
contradicts Δ1<0. Thus q0>0 and Δ0≥0 gives q2≥1−η. But then
Δ1≤−3/2+7η/2<0, again contradicting q1=1.

Hence(A5) holds. Every nonnegative increment in(A5) is at mostη.
Since H≥H*, player3's final gap−H−b3<0 gives q3=0.

Let W0 be the pivot's ORIGINAL menu Never reply. Mixing equates its
finite Quit value to W0+b0, while its original prescribed payoff is
U0=W0+b0 q0. At any pure deadline AFTER the final menu date, its payoff is

    W0+(1−q1)(1−q2)(1−q3),

because precisely the event of all opponents choosing Never adds the own
singleton1. Thus this actual complete unilateral deviation gains at least

    (1−q1)(1−q2)−b0 q0
      ≥(1−q1)(1−q2)
      ≥18/49−|q1−4/7|−|q2−1/7|
      ≥18/49−2η>1/3.

This proves Claim B for all auxiliary components and all N. The large-tax
statement is ONLY concentration at the last date; the fixed ORIGINAL gap
statement uses the explicit small-tax bound.

For contrast, let the pivot be uniform on0,...,N−1 and all other players
choose Never. The original payoff is(1,7,7,5). At a finite date t<N,
players1,2,3 receive respectively

    (7t+8)/N, (7t+5)/N, (5t+4)/N.

Later replies equal their Never values7,7,5. Every pivot finite reply pays1
and Never pays0. Hence the ORIGINAL full exploitability is EXACTLY1/N,
solely at player1. This legal independent-clock sequence proves that the
table has zero infimum original exploitability, so(A2) excludes the entire
negative-tax exact-source class, NOT the UE conclusion.

### 22.6. Source correspondence and the restriction actually falsified

The semantic missing reply is the exact late value from
`singlePivot_pivot_fullCap_eq_max_menu_never_add_deletedNever`
(`UniformEquilibrium/Quitting/Terminal/SinglePivotFiniteMenuSource.lean`).
Ordinary finite Nash gives a nonempty auxiliary equilibrium correspondence
at every N,b; the source statement used is finite mixed Nash existence,
as instantiated by `exists_exactFiniteDeadlineTimingNash`
(`UniformEquilibrium/Quitting/Terminal/FiniteDeadlineNashExistence.lean`).
The original all-errors terminal endpoint is
`quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
(`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`).
No declaration is claimed to check the private-tax no-go proved here.

The restriction falsified is EXACT Nash of finite common menus modified
ONLY by nonpositive private planned-Never transfers, including at the pivot.
Allowing every tax magnitude, every Nash component, changing menus, and then taking
taxes to0 does not repair it. Positive planned-Never subsidies or genuinely
approximate menu Nash laws are not covered. Section21's negative-payoff
sentinel pump remains valid on its different table, but is not universally
produced. The next mechanism must allow something beyond this entire
negative-tax source class, not merely select another branch of it.

## 23. Entire realized-discount correspondence: the global test remains open

This is a different source attempt, not a further private-transfer variant.
The source exists unconditionally. No conclusion about its best ORIGINAL
terminal regret is proved here. The switching calibration below is ordinary
unreviewed mathematics, not a new equilibrium class or an export candidate.

### 23.1. Exact global question and actual source

For an arbitrary finite four-player quitting table, let X=ℕ∪{Never} with
the one-point compactification topology. Each player chooses an independent
countably additive law on X. For 0<α<1 define

    U_i^α(p)=E_p[α^τ r_i(S) 1{τ<Never}],

where τ is the first finite planned clock and S its quitting coalition.
Never pays0. Let D_α be the ENTIRE exact Nash correspondence for these
discounted objectives, with all complete unilateral replacement laws
allowed. Neither stationarity nor properness of any specified player is
required. The proposed global source statement is

    liminf_(α↑1) inf_(p∈D_α) E_original(p)=0.       (D1)

Both the laws and their payoff targets may change with α. The terminal
all-errors endpoint would select a fixed uniform payoff afterward. A bad
stationary branch, or even a bad nonstationary branch, does not falsify(D1).

This source is genuinely automatic. The discounted terminal kernel on X⁴
is continuous: near AllNever its magnitude is bounded by Mα^min(T_i),
which tends to0; near any finite first date, the relevant finite atoms and
ties stabilize. Thus the product mixed game is compact and continuous.
Alternatively the tracked Fink theorem already supplies a stationary
discounted Nash member at every α. No original reward translation or
private planned-action payment is used.

The exact tracked source anchors inspected are
`StochasticGame.exists_isDiscountedStationaryBellmanEq_bounded` and
`IsDiscountedStationaryBellmanEq.isDiscountedεNash`
(`UniformEquilibrium/ProofView/Concepts/Stochastic/Equilibrium/Discounted/Fink.lean`),
and `discountedAuxEU_quittingGame_none`
(`UniformEquilibrium/Quitting/Bellman/Discounted/PayoffBridge.lean`). The
repository normalized stage payoff is α times the displayed U^α, because
the live stage itself pays0; that common positive factor does not change
Nash. `quittingDiscountedLiveValue_eq_rootPayoff` and
`quittingDiscountedDenominator_mul_endpointDifference`
(`UniformEquilibrium/Quitting/Stationary/DiscountedDisplacement.lean`)
retain actual discounted values and endpoint inequalities. They do not
select a favorable original terminal law.

The bounded overlap check found only narrower stopped operations:
`CODEX_FRECHET_CYCLE__DEGREE_ONE_GERM_SCHEDULING_AND_MACROSCOPIC_EXIT_BOUNDARY.md`
concatenates small points of a supplied stationary germ; its own scope
explicitly leaves the global discounted-component question open.
`CODEX_RADO_BOUNDARY__DISCOUNTED_LOCALIZATION_SOURCE_CONNECTION_STOP.md`
tests stationary auxiliary roots and self-return. Neither is an all-
nonstationary, entire-correspondence obstruction to(D1).

### 23.2. Solan's hard calibration, including exact support switches

Use the three-player table G_ε of Solan, *The Dynamics of the Nash
Correspondence and n-Player Stochastic Games* (2001), Figure1:

| S | reward |
| --- | --- |
| 0 | (1,3,0) |
| 1 | (0,1,3) |
| 2 | (3,0,1) |
| 01 | (1+ε,0,1) |
| 02 | (0,1,1+ε) |
| 12 | (1,1+ε,0) |
| 012 | (0,0,0) |

Here 0<ε<1/3 is fixed, not the desired equilibrium accuracy. The primary
source is https://www.math.tau.ac.il/~eilons/value4.pdf, Sections2–3.
The paper's bounded-terminal consequence and the already-known UE/no-
exact-terminal-Nash distinction motivate this test. The printed definition
of its abstract admissible set permits unbounded annotations; that larger
formal statement is NOT needed or asserted here. A fourth player can be
padded with reward−1 whenever it joins and0 otherwise, core rewards
depending only on the core coalition and being0 when it is empty. The
displayed calibrated profiles keep that player literally Never.

Put λ=1−α. There is an exact three-date ROTATING-PAIR discounted Nash
branch for all sufficiently small λ>0:

    qA=(a,b,0), qB=(0,a,b), qC=(b,0,a),
    uA=(1+εb,1−a,w), with the values rotated likewise.

The full owner equations and the passive Bellman equation are precisely

    1+εb = α(1−b)w,
    1−a = 3a+α(1−a)(1+εb),
    w = 3b−2ab+α(1−a)²(1−b).                     (D2)

At λ=0 they have a=b=0,w=1. Their Jacobian in(a,b,w) has determinant
ε−3. The ordinary implicit-function theorem gives

    a = [(1−3ε)/(3−ε)]λ+O(λ²),
    b = [8/(3−ε)]λ+O(λ²),
    w = 1+[(11+7ε)/(3−ε)]λ+O(λ²).

Both active probabilities are strictly between0 and1. At phaseA the
inactive player's Quit value is(1−b)(1+εa), and its Continue value is w.
Their difference has positive leading coefficient

    [19+6ε+3ε²]/(3−ε).

The rotated inequalities are identical. These root inequalities plus the
bounded discounted telescope verify Nash against ALL complete deadlines,
Never and their mixtures. All three clocks and all deleted-opponent clocks
are proper. Thus support can switch at every date in an exact source;
a fixed-active-face argument is not WLOG.

This is nevertheless another BAD component, not a falsifier of(D1).
As λ↓0, the original first-quitter singleton masses tend to1/3 each,
collision mass tends to0, and the two opponents' first-singleton masses
after deleting any owner tend to1/2 each. This follows by the exact
three-date geometric survival account: each player's total first-order
rate per period is a+b. Consequently original payoffs tend to4/3,
Never replies tend to3/2, and the full cap tends to3/2. For the last
assertion every pure deadline is, up to O(λ), an interpolation between
the own singleton1 and the eventual Never value3/2; the period-prefix
formula includes the complete Never limit. Hence ORIGINAL full regret
tends to1/6. The symmetric stationary branch has the same limiting loss.
None of this bounds the infimum over the other components.

### 23.3. The genuinely missing global operation

For the displayed core table, no core player can be a sure quitter at a
reached date of a discounted Nash profile. For example q0=1 forces q1=0
(joining earns0, whereas finite Continue earns at least1), then q2=1
(joining earns1+ε rather than0), then owner0 strictly prefers Continue3
to Quit0. The other cases rotate. The comparisons apply to any
nonnegative continuation values. Thus every finite surviving tail is
reached and is exact discounted Nash with the SAME discount and table.

Let C be the convex hull of0 and the seven displayed reward vectors.
Define T_α(K) as the set of root Nash payoff vectors against continuation
αv with v∈K. The sets T_α^m(C) are nested, nonempty and compact. Their
intersection K_α is EXACTLY the payoff set of all discounted Nash clocks
for this calibration: actual tails give one inclusion; compact nested
selection gives a bounded infinite root spine for the other, and α^t
makes its terminal remainder vanish against arbitrary full deviations.
This equality uses the no-sure argument above; it is not asserted for
arbitrary tables with off-path punishment tails.

The attempted global estimate is

    sup_(v∈K_α) ||v−(1,1,1)|| = O(1−α).           (D3, FALSE by23.4)

Unlike the fixed-face heuristic, this quantifies over macroscopic roots,
all support switches, all infinite calendars and the entire viability
kernel. A proof would require a true global invariant or contraction;
the local Jacobian and the rotating-pair calculation do not supply it.
Even qualitative convergence to the corner, without its rate or a
separate full-response account, would not settle(D1).

The concrete obstruction in this attempt is a possible long excursion
through two-owner faces and macroscopic roots before returning to a
small-hazard region. The one-shot map can amplify a passive coordinate,
so a coordinatewise maximum argument fails. No exclusion of those
excursions, no good exact discounted component, and no full-source
falsifier follows from that argument. The construction below supplies a
good component and disproves(D3); another isolated bad branch would not
advance the question.

### 23.4. A good growing-period discounted component on G_ε

The following is a complete ordinary proof, bounded independently checked
by CODEX_NASH_BOX in the corresponding feedback file (D4–D12 only), not
checked in Lean or exported. It supplies an actual favorable component
of the ENTIRE source(D1) on the displayed, already-solved three-player
calibration. It is not an arbitrary-table or genuinely four-active source.
Fix 0<ε<1/3. There are α_k↑1 along a subsequence and exact discounted
Nash profiles p^k with periods3k such that

    E_original(p^k)→0,  U_original(p^k)→(1,1,2).       (D4)

All three clocks and every opponent-deleted clock are proper. Within
each phase there is a macroscopic quitting burst, despite α_k→1.
Consequently(D3) is false: a continuation coordinate tends to2, not1.
This does not contradict Solan's bounded no-exact-terminal-Nash result,
because the periods grow and the limiting private laws need not realize
the limiting payoff. It also does not contradict the fixed-period source
obstruction in Noether's RM33: its constants fix the period before the
discount limit, whereas here k grows and (1−α_k)k→0.

Here is the finite producer, including its parameter order. Put
r=(1+ε)/ε>1 and B*=1/(2+ε), and fix the compact interval
I=[B*/2,3B*/2]⊂(0,1). For each integer k≥2 and B∈I there is a UNIQUE
λ=λ_k(B)>0 such that α=1−λ∈(0,1) and the recursion

    b_0=0,
    b_(t+1)=[λ+(ε+α)b_t]/[αε(1−b_t)],
    b_(k−1)=B                                             (D5)

has all b_t∈[0,B]. The finite iterates are continuous and strictly
increasing in λ while below1. Starting at λ=0 gives0, and increasing
λ until the preceding iterate first reaches B makes its next iterate
strictly exceed B. Induction gives the asserted unique crossing; its
inverse B↦λ_k(B) is continuous. In particular no unproved asymptotic
root is being used as a finite solution. Since the recursion gives
b_(t+1)≥r b_t+λ/ε, it also gives the uniform estimate

    0<λ_k(B)≤B/[r^(k−1)−1],  kλ_k(B)→0.                (D6)

For this λ define the other active probabilities BACKWARD by

    a_(k−1)=λ/(4−α),
    a_t=[λ+αa_(t+1)]/[4−α+αa_(t+1)].                   (D7)

They satisfy0<a_t≤λ/2. Indeed the last entry is at most λ/3, and the
displayed map sends[0,λ/2] into[0,λ/2], since4−α≥3. The phase roots
are q_t=(a_t,b_t,0),0≤t<k. Repeat this phase with labels rotated once,
then twice, and replay the resulting3k-date word forever. No public
randomization or correlation between private clocks is added.

The proposed discounted phase values are

    u_t=(1+εb_t,1−a_t,w_t).

Define w BACKWARD from w_k=1−a_0 by

    w_t=3b_t−2a_tb_t+α(1−a_t)(1−b_t)w_(t+1).           (D8)

This is precisely the passive player's Bellman equation, including the
rotated child at the phase boundary. The first owner's interior
indifference is exactly(D5); the second owner's interior indifference
is exactly(D7). At the phase boundary the second owner's equation is
1−a_(k−1)=3a_(k−1)+α(1−a_(k−1)), also exactly(D7).
The remaining first-owner boundary equation is the scalar equation

    G_k(B):=w_0−[1+εB]/[α(1−B)]=0.                   (D9)

At b_0=0 the second player continues and is indifferent; no strictly
positive hazard is required there. Thus(D9), together with the inactive
inequality checked below, is the entire finite existence problem.

We now prove a uniform scalar limit on I. Let c_0(B)=B and
c_(j+1)=c_j/(r+c_j). Reading(D5) backward gives

    b_t=[αεb_(t+1)−λ]/[ε+α+αεb_(t+1)].

On[0,max I] this map differs from x↦x/(r+x) by O_ε(λ), uniformly,
and the latter is1/r-Lipschitz. Therefore

    max_(0≤j<k)|b_(k−1−j)−c_j(B)|=O_ε(λ),
    Σ_(j<k)|b_(k−1−j)−c_j(B)|=O_ε(kλ).

The explicit solution and its product are

    c_j=B/[r^j+εB(r^j−1)],
    ∏_(j<k)(1−c_j)
      =(1−B)/[1+εB−εB r^(−(k−1))].

The difference between products of numbers in[0,1] is at most the sum
of the coordinate differences. Hence, uniformly for B∈I,

    P_k(B):=∏_(t<k)(1−b_t)→(1−B)/(1+εB).             (D10)

If a=0 and α=1 in(D8), retaining the SAME b_t and terminal value1,
the passive values are exactly

    w̄_t=1+2[1−∏_(s=t)^(k−1)(1−b_s)].

The actual a_t≤λ/2, discount lossλ, and terminal error a_0 change each
one-step affine recurrence by O_ε(λ); all its transmission coefficients
are in[0,1]. Thus max_t|w_t−w̄_t|=O_ε(kλ), uniformly on I.
Equations(D6) and(D10) now give

    G_k(B)→G∞(B)
      =3−2(1−B)/(1+εB)−(1+εB)/(1−B)
      =(1+ε)B[1−(2+ε)B]/[(1+εB)(1−B)]               (D11)

uniformly on I. Its sign is positive at B*/2 and negative at3B*/2.
For EVERY sufficiently large k, the ordinary intermediate-value theorem
therefore gives B_k∈int I with G_k(B_k)=0. Every such selection satisfies
B_k→B*, since G∞ has exactly one zero on I. Choose this B_k first,
then λ_k=λ_k(B_k), α_k=1−λ_k, and the actual finite roots(D5)–(D8).
A monotone subsequence of α_k may be taken if desired; only α_k→1 is
needed for(D1).

All inactive inequalities hold for these actual finite roots, not only
at the limit. At any phase date the inactive third player's immediate
Quit value is Q_2=(1−b_t)(1+εa_t), whereas its prescribed Continue
value is w_t. Since the remaining b-product includes the last factor
1−B_k, the exact comparison above gives

    w_t≥1+2B_k−O_ε(kλ_k),
    Q_2≤1+ελ_k/2.

Because B_k≥B*/2>0 and kλ_k→0, w_t>Q_2 at EVERY phase date once
k is large. The other two players are indifferent by the exact equations.
After rotating, these are all nine player/phase families. Thus every root
is exact Nash at its actual next discounted value. The displayed ports
are uniformly bounded, and the remainder after n dates has factor α_k^n.
The Bellman inequality therefore telescopes against ALL pure deadlines,
Never, and their arbitrary mixed complete replacements. This proves
p^k∈D_(α_k), not merely a finite-root certificate.

It remains to compare ORIGINAL full responses, including Never. Put
A_k=∏_(t<k)(1−a_t). Equations(D6),(D7),(D10) give

    A_k→1,  P_k→1/2,  J_k:=A_k P_k→1/2.

Each individual clock survives a full3k-date period with probability J_k;
every opponent-deleted clock survives that period with probability J_k².
Thus all those clocks are proper, and their physical absorption bounds
are uniform. For any player i and ANY complete replacement of its law,
the first absorbing time is at most the unchanged opponents' first quit
time. With reward bound M=3,

    |U_i(original replacement)−U_i^α(replacement)|
       ≤Mλ E[T_−i+1]≤Mλ(3k)/(1−J_k²).

This also holds for the prescribed law. Exact discounted Nash consequently
implies the original FULL cap bound

    E_original(p^k)≤18λ_k k/(1−J_k²)→0.                (D12)

No finite-deadline or omitted late-response qualification is present.
At the first date the discounted value is(1,1−a_0,w_0)→(1,1,2).
The same comparison transfers that limit to original terminal payoffs.
The tracked terminal-all-errors endpoint can then select the uniform
payoff; alternatively the fixed target follows from this convergence.
The harmless fourth-player padding described above keeps player3 Never,
an exact discounted and original best response with value0, and gives
the corresponding padded target(1,1,2,0). This is still three-active,
already-known UE coverage rather than a new Fin4 class.

The mathematical lesson is source-level, not a new conditional consumer:
the all-component discounted selector survives this hard calibration.
Its favorable component uses long pair phases and macroscopic bursts;
the fixed-period small-hazard germ is not the whole correspondence.
The role of the sparse actual phase is crucial: a geometric b-growth
builds a fixed physical absorption while the λ-dependent companion a
and discount loss total only O(kλ). What remains genuinely open is a
global selector that produces comparable bursts or another favorable
component from arbitrary four-player reward data. The scalar sign change
here uses the special cyclic singleton and collision rows and is not
claimed for an unresolved four-active table.

## 24. The discounted burst source and the constrained-owner quantifier

This exact connection is supporting ordinary mathematics, not additional
game-class coverage or a full audit of the constrained-owner source.
Use the core G_ε and the actual components from Section23.4. Add a fourth
player d whose reward is−1 whenever d joins and0 otherwise. Core rewards
depend only on the core quitting coalition and are0 if it is empty.
This LITERAL padding has own reward s_d=−1, so it does NOT meet an
all-own-nonnegative source hypothesis.

Let δ=1−α and let d use the independent geometric clock
Pr(T_d=t)=δ(1−δ)^t,t≥0. If the first core quitting date is τ, its
core reward is retained precisely when T_d≥τ, INCLUDING ties. Thus,
for every core player and every complete replacement of its own law,
the ORIGINAL padded payoff equals its realized-discount payoff
E[α^τ r_i(S_core)1{τ finite}]. Exact discounted core Nash therefore
means all three core players have original FULL debt exactly0.

Restrict the dummy's law to

    K_δ={p:Pr(T_d≥t, including Never)≤(1−δ)^t for every t≥0}.

These prefix bounds, not a pointwise conditional hazard requirement, are
the actual constrained-owner domain in
`CODEX_EMMY_BOX__SINGLE_OWNER_COMPACTIFICATION`, Section1. Every law in
K_δ is proper and stochastically no later than Geom(δ). The dummy's
pure-deadline payoff f(t)=−Pr(τ≥t) is nondecreasing, with f(Never)=0.
Common-quantile coupling therefore shows that Geom(δ) is K_δ-optimal
against ANY core profile. Hence the padded profiles just constructed
are exact Nash in the dummy-owner constrained game.

The unrestricted dummy cap is0, attained by Never. Its debt is exactly

    Pr(T_d≤τ)=E[1−α^(τ+1)]
      ≤δ E[τ+1]≤3δk/(1−J_k³)→0,

where δ=λ_k, the core joint-period survival is J_k³, J_k→1/2, and
δk→0. Thus a negative-own dummy owner has GOOD constrained components;
an obstruction for all three CORE owners does not imply one for this
fourth owner.

There is an explicit nonnegative-own repair, with a complete source
comparison rather than presumed affine invariance of Never. Change ONLY
the dummy column to the following exact values:

    r_d(S)=1 if d∉S and S is nonempty,
    r_d(S)=0 if d∈S,
    r_d(Never)=0.

This adds1 to every FINITE-terminal dummy reward, including dummy-alone,
and does not change core rewards. On the constrained domain K_δ the
dummy is proper, so every product profile, every constrained dummy
competitor and every nonowner competitor absorbs surely. Consequently
the dummy's constrained objective increases by the SAME constant1 for
all such comparisons. The ENTIRE dummy-owner constrained Nash
correspondence is unchanged. This is an exact restriction-specific
transport, not arbitrary payoff-shift invariance for the original game.

At the constructed profiles the CORE is also proper. Its literal Never
dummy response then earns1; no response earns more than1. Thus the
full dummy cap is1, its prescribed payoff is1−Pr(T_d≤τ), and its
debt remains Pr(T_d≤τ)→0. The repaired table has core own rewards1
and dummy own reward0. It meets the nonnegative-own source assumption.
This column is NOT the different padding with absent1, joined-core−1
and dummy-alone0. It also does not silently identify the literal core
table with a separately canonicalized one: source correspondence under
any further core-column change requires its own proof.

## 25. Four-active burst test: an inactive wall, not a whole-source no-go

Current question: does the ENTIRE realized-discounted Nash correspondence
contain original-terminal approximate Nash components on arbitrary
completions of the hard paired singleton matrix? This permits distant
support changes and approximate, rather than exact, original equilibria.
The following one-table test is ordinary unreviewed calculation. It does
not exclude the whole discounted source, a strategy class with three/four
simultaneous actors, or UE.

Use cyclic labels I=Z/4Z; the mate of i is i+2. Fix singleton rewards1
to the quitter,4 to its mate and0 to the other two. Complete the table by:

| coalition | participant rewards | nonparticipant rewards |
| --- | --- | --- |
| adjacent pair{i,i+1} | r_i=−1, r_(i+1)=2 | both1 |
| opposite pair{i,i+2} | both0 | both1 |
| any triple | all−1 |1 |
| grand | r_i=−10−i | none |

The original paired labels are obtained by the cyclic order0,2,1,3.
Thus the singleton comparison matrix is exactly the paired hard matrix
up to relabeling, not a singleton class with an available homogeneous or
negative-determinant nonnegative-inverse exit.

Bounded initial coverage test. The four frozen phase sources do not
supply their named profiles here. The first joint source's favorite-pair
rates lie in(1/4,3/4); at such a root Quit earns1−b<3/4, while Continue
earns at least4b>1 whenever the actual next Nash value is nonnegative.
Every full best-reply value is indeed nonnegative, since Never against
this table earns only nonparticipant rewards0,1,4. The rectangle source
requires favorite-pair participant rewards5,9/2; the passive-ray source
requires them A>T; here both are0. The named proper singleton-calendar
source has cross-pair participant caps at most1 under either orientation,
whereas the directed successor receives2. Its global owner-equation
uniqueness at these singleton rows rules out silently choosing other
positive rates for that same named calendar. The common-large-pair source
also has incompatible positive participant premises. The literal ordered
lower-face stationary guards fail for EVERY partner choice: selecting a
nonmate leaves a harmful favorite-axis displacement near zero; selecting
the mate leaves the sure-successor displacement−1. These are bounded
named-source comparisons, not an exhaustive novelty or stationary-Nash
nonexistence claim.

The table also has NO root Nash with a sure quitter. If i is sure, its
mate must Continue: joining gives at most0, whereas Continue gives at
least1 (or4 at the singleton). Its predecessor i−1 must Continue:
joining gives a negative reward and Continue is nonnegative. With those
two absent, successor i+1 must surely join, earning2 rather than0.
Then i earns−1 from joining and0 from withdrawing, a contradiction.
This covers all sure-owner induced Nash rows and hence the actual
persistent-base exits, not merely a chosen pure root.

A two-active extension of Section23.4 is insufficient. Try roots
q_t=(a_t,b_t,0,0) during one phase, with the next phase shifted one label
BACKWARD, so the previous owner becomes the next joiner. The exact active
current values would be u_0=1−2b_t,u_1=1+a_t. Their interior equations are

    a_(t+1)=[λ+(1+α)a_t]/[α(1−a_t)],
    b_t=[λ+2αb_(t+1)]/[2−α+2αb_(t+1)].

Choose a_0=0, a_(k−1)=B and the boundary value
b_(k−1)=λ/(2−α). The pair recursions have a geometric-burst regime
λk→0. Their limiting survival factors, writing the last a-burst as B,
are

    P_a=(1−B)/(1+B),
    b_0=2B/(1+5B),
    X:=1−2b_0=P_b=(1+B)/(1+5B),
    J=P_aP_b=(1−B)/(1+5B).

The two passive phase recursions force the remaining active seam to
4J(1−J)+J³=1. Its nontrivial admissible root is
J=c=(3−sqrt(5))/2, hence B=(1−c)/(1+5c). At the last date the inactive
predecessor's Continue value tends to(1−B)X, but its forced Quit value
tends to1−2B. Their difference is EXACTLY

    (1−B)X−(1−2B)=3B(3B−1)/(1+5B)<0,

because the displayed B lies in(0,1/3). Thus this burst word reaches a
strict inactive wall. The limit calculation, not a fully audited finite-k
existence theorem for these incomplete root equations, is what is retained.
Numeric diagnostics at k=15 give B≈0.212395, λ≈1.07e−5 and the offending
margin≈−0.11215, consistent with the exact limiting margin≈−0.11212.
No numeric experiment is being used to exclude other components.

The concrete next operation is to admit a third simultaneous actor at
this wall, or select a distant discounted component. A local repair is
not assumed to exist: a diagnostic three-active, four-phase Newton search
found no interior zero, which is incomplete evidence only. Freezing the
two-player root alphabet would discard a real best response and cannot
be the proposed global producer. No further reward-parameter expansion
or UE counterexample conclusion is inferred from this test.

### 25.1 Every exact stationary component is excluded

This is an ordinary exact calculation, not independently reviewed or Lean
checked. A stationary profile means independent constant conditional Quit
hazards q_i in[0,1], equivalently geometric clocks when q_i>0 and Never
when q_i=0. Deviations still include ALL independent complete replacement
clocks, all pure dates and Never. The table in Section25 has no exact
terminal Nash profile of this stationary form.

The sure-quitter case was excluded above. Thus assume all q_i<1. If at
least two players are active, every active player has a proper opponent.
Write Q_i for its immediate Quit payoff and N_i for the one-date expected
reward received when it Continues and an opponent quits, and let A_i be
the opponent absorption probability. A stationary interior best response
requires

    Q_i=N_i/A_i.                                           (S1)

Indeed the same stationary tail is reached with positive probability, so
root Quit and Continue must be indifferent. Its value then equals Q_i;
the Continue recursion gives A_i Q_i=N_i. This value is also the full
Never payoff. The argument uses no restriction on allowed deviations.

Zero active players leave immediate Quit gain1. With one active player i,
the successor i+1 receives0 by Never and1+q_i by Quit0. With exactly two
active opposite players, either player's Never payoff is4 and its Quit
endpoint is at most1, contradicting(S1). With exactly two active adjacent
players i,i+1, the latter's Never payoff is0 and its Quit endpoint is
1+q_i>0, again contradicting(S1).

For three active players, rotate the cyclic labels so q=(a,b,c,0), with
a,b,c in(0,1). The relevant endpoints, directly summing the four possible
opponent outcomes, are

    Q_0=1−2b−c+bc,        N_0=(4−3b)c, A_0=b+c−bc,
    Q_1=1+a−2c−ac,       N_1=ac,       A_1=a+c−ac.

Equation(S1) for player0 gives Q_0>0, hence b<1/2. Also Q_0≤1, so

    (5/2)c < N_0=Q_0 A_0 ≤ A_0 < (1+c)/2,

which forces c<1/4. But Q_1>1−2c>1/2, while N_1/A_1≤c<1/4 because
A_1≥a. This is impossible. The grand-coalition rewards do not enter this
case, so cyclic relabeling is legitimate despite their asymmetric values.

It remains to exclude all four positive hazards. Put z_i=q_i/(1−q_i)>0.
For each i set x_i=z_(i−1), y_i=z_(i+2), w_i=z_(i+1), and

    L_i=x_i+y_i+w_i,
    T_i=x_i y_i+x_i w_i+y_i w_i,
    V_i=x_i y_i w_i,
    A_i'=L_i+T_i+V_i,
    N_i'=4y_i+T_i+V_i,
    P_i'=1+2x_i−w_i−T_i−(10+i)V_i.

Here the common denominator for the actual one-date endpoints is
1+A_i'. Therefore Never=N_i'/A_i' and Quit=P_i'/(1+A_i'). Condition(S1)
would force all four residuals

    F_i=N_i'(1+A_i')−P_i'A_i'

to vanish. However the following exact polynomial identity holds:

    Σ_i F_i = Σ_i z_i + Q(z)
      + Σ_i [3T_i(2y_i+w_i)+2T_i²
        +V_i((9+i)x_i+(15+i)y_i+(12+i)w_i)
        +(13+i)T_iV_i+(11+i)V_i²],

where

    Q(z)=2Σ_i z_i²+(z_0−z_2)²+(z_1−z_3)²
         +7Σ_i z_i z_(i+1).

All summands are nonnegative and Σ_i z_i>0, so Σ_i F_i>0, a contradiction.
For a direct expansion check, the only potentially negative monomials in
the sum are the quadratic terms−2z_0z_2−2z_1z_3; the displayed Q absorbs
them into squares. The higher-degree terms follow by expanding
N_i'+A_i'(N_i'−P_i'). This completes every stationary support case.

This exact exclusion says nothing about the infimum regret over stationary
profiles or about nonstationary clocks. In particular it is compatible
with the rational period12 approximate profile in
`CODEX_EMMY_BOX__SINGLE_OWNER_COMPACTIFICATION.md`, Section15. The relevant
consumer for an eventual all-errors construction remains
`quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
(`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`).
The inspected periodic cap is
`quittingTerminalDeviationDebt_cyclicBehaviorProfile_le_card_mul_error_div_opponentAbsorption`
(`UniformEquilibrium/Quitting/Cycles/PeriodicApproximateNashDeviationCap.lean`);
it is a consumer for supplied roots, not a producer of overlap seams.

### 25.2 A quadratic obstruction to a continuous diffuse equilibrium flow

The following standalone flow lemma is exact ordinary mathematics. Its
adapter from discrete approximate equilibria is a PROOF DRAFT, not yet a
claimed whole-mode exclusion.

Let P exchange the opposite mates in Z/4Z and let R=I+4P be the singleton
reward matrix, with rows indexed by recipients. There is no locally
absolutely continuous v:[0,infinity)→R^4 and measurable a:[0,infinity)→R^4
satisfying almost everywhere

    v_i≥1,  Σ_i v_i=5,
    a_i≥0,  Σ_i a_i=1,  (v_i−1)a_i=0,
    v'=v−Ra.                                             (S2)

Indeed put g=v−1 and W=gᵀ(I−4P)g. Since g≥0 and Σg=1, W is bounded
and W≤Σg_i²≤1. Using P²=I gives (I−4P)R=−15I, while
(I−4P)1=−3*1. Consequently

    W'=2W−6+30g·a=2W−6.

Thus W(s)=3+(W(0)−3)exp(2s), which is unbounded below since W(0)≤1.
This contradicts compactness of the simplex containing g. No assumption
of a fixed active support, periodicity or constant rates enters this lemma.

Intended discrete test. Suppose for this fixed singleton matrix, with ANY
one fixed finite collision completion, a sequence of private product
profiles had both original complete regret→0 and maximum conditional
hazard→0. Reparametrize date by total cumulative log-survival hazard
s(t)=Σ_(u<t)Σ_i −log(1−q_i(u)). On bounded s intervals the cumulative
individual hazards are uniformly Lipschitz. Collision mass should vanish
relative to total hazard; reached tails should have value at least1, and
policy improvement by suppressing own quitting at positive slack should
force the complementarity integral ∫(v_i−1) da_i to vanish. Any all-Never
mass must also vanish: replacing only one's Never branch by an increasingly
late deadline gains the JOINT all-Never probability, so that probability
is bounded by full regret. These facts would give a global flow(S2).

The outstanding proof obligation is the full compactification, particularly
the complementarity integral with all original deviations and possible
finite individual hazard totals. It must not assume that small root errors
are small FULL terminal debts. If this adapter survives, it excludes a
genuine all-hazards-small approximate-equilibrium mode for arbitrary fixed
collision completions of these singletons; it does not itself produce UE.

The compactification route above remains an unproved route as stated.
Section25.3 instead proves the intended exclusion directly on one finite
hazard-time interval, without taking any limit of profiles or controls.

### 25.3 Full-profile diffuse-mode exclusion by a finite hazard window

Status: complete ordinary proof candidate, not independently checked or
Lean-checked. This is a whole-mode exclusion for actual private profiles,
not a producer or a fixed-target decoding statement.

#### Exact finite data and quantifiers

Let I=Z/4Z, let P exchange opposite mates, and let the singleton reward
matrix be R=I+4P: a singleton quitter earns1, its mate earns4, and its
other two opponents earn0. Fix ANY original collision completion with

    |r_i(S)|≤M for every i and every nonempty S, where M≥4.

Never and live rewards are0. Every player chooses a private complete
quitting law on dates0,1,... and Never; the four laws are independent.
Equivalently, its live-date conditional Quit hazards are q_i(t). Full
regret D_i is the supremum gain over ALL complete unilateral replacement
laws, including all finite deadlines and Never. Set η=max_i D_i.

Claim. Every such profile with

    sup_(i,t) q_i(t)≤δ:=1/(10000M)

has η>1/10000. The assertion is uniform over all bounded collision
completions, all calendars, finite or infinite individual cumulative
hazards, and positive private Never masses. It does not bound the largest
UNCONDITIONAL date atom. In particular a proper uniform finite clock has
last conditional hazard1 and does not satisfy the premise.

Proof. Suppose instead that η≤1/10000. The proof below also applies when
the maximum conditional hazard is smaller than δ. Throughout use this
fixed upper bound δ, so Mδ≤1/10000 and δ≤1/16.

#### Three consequences of actual complete unilateral agency

Put

    J_t=product_(u<t) product_i(1−q_i(u)),

and let v_t be the actual prescribed payoff vector conditional on all
four clocks surviving to date t. Each finite J_t is positive. Let Q_it
be player i's immediate-Quit payoff against the three opponent hazards,
and let C_it be its immediate-Continue payoff with the ACTUAL prescribed
tail v_(t+1). Thus

    v_ti=q_i(t)Q_it+(1−q_i(t))C_it,       |v_ti|≤M.       (S3)

First, the joint all-Never probability J_infinity is at most η. Replace
only player i's private Never branch by a deterministic date n, keeping
all its finite-date probabilities unchanged. On the event that all
opponents are Never this eventually gains its own singleton reward1.
The probability that a finite opponent clock survives to n tends to0,
so boundedness of rewards gives limiting gain equal to the product of
all four private Never probabilities, namely J_infinity. Each replacing
law is legal, hence J_infinity≤D_i≤η. This argument does not condition a
private Never payment on game reach or normalize the original Never value.

Second, match one's prescribed hazards before t and then Quit surely at
t. Its root gain is exactly J_t(Q_it−v_ti). Consequently

    v_ti≥Q_it−η/J_t,        |Q_it−1|≤4Mδ.              (S4)

For the latter estimate, an opponent quits with probability at most3δ;
the endpoint differs from the own singleton1 by at most M+1 on that
event, and3(M+1)≤4M for M≥4.

Third, on ANY finite date window suppress one's quitting precisely at
dates for which C_it>Q_it; retain its original hazard at the other dates
and revert to the original tail after the window. This is ONE legal
complete replacement law. Write J'_t for its joint reach. Reducing one's
hazards gives J'_t≥J_t. Finite Bellman telescoping, with the same actual
tail v after the window, gives its exact gain

    sum_window J'_t q_i(t)(C_it−Q_it)_+.

The sum is nonnegative and at most D_i. Equation(S3) therefore implies

    sum_window J_t q_i(t)(v_ti−Q_it)_+≤η.               (S5)

In fact telescoping gives the stronger coefficient q_i/(1−q_i), but
the displayed weaker bound is sufficient. This step uses a full legal
deviation; it does NOT infer full regret from a sum of unweighted root
errors.

#### Hazard time and a controlled exact interpolation

Define h_it=−log(1−q_i(t)), h_t=sum_i h_it and s_t=sum_(u<t)h_u. Thus
J_t=exp(−s_t). Because J_infinity≤η<exp(−1), there is a finite first
index T with s_T≥1. Ignore zero-hazard cells, on which v_t=v_(t+1).
For a positive cell put a_it=h_it/h_t and linearly interpolate v_t,
v_(t+1) on [s_t,s_(t+1)]. Let a(s)=a_t there. Then a≥0 and sum a=1.

The elementary logarithm inequalities give

    q_i≤h_i≤q_i/(1−δ),  h_i−q_i≤δh_i,  h_t≤5δ.

In particular s_T≤1+5δ<log4 and J_t≥1/4 on every used cell and endpoint.
All constructions below use only the FINITE original dates before T.

Let A_t be the unconditional one-date expected stopping reward vector,
including every simultaneous coalition. Its singleton coefficient for
player i differs from h_it by at most4δh_it. Its total collision
probability is at most sum_(i<j)q_iq_j≤(3/2)δh_t. Therefore

    ||A_t−R h_vector_t||_infinity≤6Mδh_t.

The exact prescribed recursion is v_t=A_t+exp(−h_t)v_(t+1). Rewriting it
and using exp(h)≤2, exp(h)−1≤2h and exp(h)−1−h≤h² for h≤5/16 gives

    v_(t+1)−v_t=h_t(v_t−Ra_t)+E_t,
    ||E_t||_infinity≤27Mδh_t,
    ||v_(t+1)−v_t||_infinity≤4Mh_t.                    (S6)

For completeness, the three error terms are
(exp(h)−1−h)v_t, −(exp(h)−1)R h_vector_t and
−exp(h)(A_t−R h_vector_t). Their norms sum to at most
3Mh_t²+12Mδh_t≤27Mδh_t. The final bound follows from
||v_t−Ra_t||≤2M and27δ≤2.

It follows that the finite linear interpolation, restricted to[0,1],
satisfies almost everywhere

    v'=v−Ra+e,       ||e||_infinity≤50Mδ.              (S7)

Indeed replacing v_t by the interpolated v costs at most4Mh_t≤20Mδ.
No convergence, compactness or relaxed control theorem is being assumed.

#### The reached value box and integrated complementarity error

At any date, collision probability is at most(3/2)δ sum_i q_i, whereas
absorption probability is at least(1−(3/2)δ)sum_i q_i. Thus collision
probability is at most2δ times absorption probability. Summing against
tail reach shows that the probability of first absorption by a collision
is at most2δ, for EVERY tail, including tails with positive Never mass.
On the used endpoints, conditional Never probability is
J_infinity/J_t≤4η. Singleton reward sums are exactly5. Hence(S4) and
bounded collision rewards give

    v_i(s)≥1−τ,             τ=4Mδ+4η,
    |sum_i v_i(s)−5|≤σ,     σ=12Mδ+20η.               (S8)

The second bound follows from5 times conditional Never plus
(4M+5) times conditional collision probability;8M+10≤12M.
Linear interpolation preserves both bounds.

Put g=v−1. For any s in cell t, equations(S4),(S6) imply

    g_i(s)≤(v_ti−Q_it)_++24Mδ.

Using(S5), J_t≥1/4 and h_it≤q_i/(1−δ), the sum of h_it times the first
term over all cells before T is at most5η, for each i. Over a partial
last cell the nonnegative upper bounds may simply be extended over the
whole cell. Since s_T<2, summing over all four players gives

    integral_0^1 g(s)·a(s) ds≤20η+48Mδ.               (S9)

This is the required complementarity estimate with the correct reached
weights. It allows changes of active support and arbitrary nonstationary
hazards; no player is singled out globally.

#### Quadratic contradiction on this finite window

Let A=I−4P and W=gᵀAg. Put x=g+τ*1≥0 and κ=σ+4τ. Equation(S8) gives
sum x≤1+κ. For any nonnegative x of mass L,

    −(3/2)L²≤xᵀAx≤L².

To see the lower bound, write each mate pair's sum and difference as
b,d. Its quadratic contribution is−(3/2)b²+(5/2)d², and the sum of the
two pair-sum squares is at most L². Moreover

    W=xᵀAx+6τ sum x−12τ².

Here τ≤0.0008, σ≤0.0032 and κ≤0.0064. In particular, the deliberately
looser estimates τ,κ≤0.01 imply everywhere on[0,1]

    −1.6≤W≤1.1,          ||g||_1≤1.05.                (S10)

Using AR=−15I, A1=−3*1 and(S7), exact differentiation gives

    W'=2W−6 sum g+30g·a+2gᵀAe.

The absolute error term is at most
2*(1.05)*5*(50Mδ)≤600Mδ. Integrate over[0,1], apply(S8)–(S10), and obtain

    W(1)−W(0)
      ≤−3.8+6σ+30(20η+48Mδ)+600Mδ
      =−3.8+6σ+600η+2040Mδ
      ≤−3.5168.

But(S10) requires W(1)−W(0)≥−2.7. This contradiction proves the claim.
All probability comparisons retained simultaneous quits and Never; all
profile modifications used in the proof are complete PRIVATE laws.

#### Meaning and bounded prior-source check

For this singleton matrix, any fixed-completion terminal approximate-Nash
sequence with full regret tending to0 must retain a conditional hazard
larger than1/(10000M) once its regret is below1/10000. The table may still
have UE via macroscopic singleton/joint bursts, a boundary support change,
or an entirely different calendar. No fixed public target or chronology
across accuracies is imposed. This is a permanent exclusion of one actual
profile mode, not an unrestricted positive-gap game or an equilibrium
producer. It explains why universally diluting a good joint calendar is
not a sound arbitrary-completion operation.

The paired face obstruction itself is NOT a new ingredient. The inspected
declarations `Math.PairedFacePotential.translated_face_drift_ge_one`
(`MathUE/Analysis/Examples/PairedFacePotential.lean`) and
`pairedFacePotential_boundedCompletion_face_drift`,
`pairedFacePotential_boundedCompletion_not_fullRoot`
(`UniformEquilibrium/Quitting/Examples/PairedFacePotentialBoundedCompletion.lean`)
already give a coupled singleton-face potential and explicitly separate
it from full-root inequalities. Their translated singleton rewards are
our R/4. The associated geometry was inspected in
`MathUE/Analysis/Examples/PairedFacePotentialGeometry.lean`. The bounded
lookup in these files and the selected singleton-face circulation sources
did not find the actual all-behavior small-hazard exclusion above; no
exhaustive novelty claim is inferred. The distinct candidate contribution
is(S3)–(S10), especially legal finite suppression and the finite-window
transfer from FULL regret, not another face polynomial.

Concrete requested check: adversarially test the full private-law
suppression identity(S5), the Never-branch replacement, and the collision
and interpolation error bounds before using this as a proved source-mode
reduction. The remaining global mathematical question is how to produce
or select the necessary macroscopic hazard structure from arbitrary
collision data; this result supplies no such selection.
