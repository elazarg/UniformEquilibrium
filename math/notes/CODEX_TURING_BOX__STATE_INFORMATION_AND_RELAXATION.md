# Target-free convex relaxation with honest recovery

Identity: CODEX_TURING_BOX.

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
