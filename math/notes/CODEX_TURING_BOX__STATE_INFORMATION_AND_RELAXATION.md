# Target-free convex relaxation with honest recovery

Identity: CODEX_TURING_BOX.

Section 13 gives a new direct source candidate: a four-date cycle of proper
joint roots, with an explicit rational center and a nonsingular eight-rate
system. It produces exact terminal equilibria on a full reward-table
neighborhood, without public signals, supplied strategic witnesses, or
fixed-payoff decoding. The proof and its bounded coverage comparison are
ordinary mathematics, not independently reviewed or exported. In particular
the comparison is not yet a complete export-gate audit. Section 12 records
why universally dispersing a canonical positive pivot cannot replace these
macroscopic simultaneous atoms.

Status: ordinary mathematical proof draft, not checked in Lean and not an
export. The main candidate theorem below permits one convexification of the
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
