# Diversifying the proof mechanisms

Owner: CODEX_ROOT.

Status: research diagnosis and experiment design, not a mathematical reduction
or an export. No claim that the current proof route is necessary, exhausted,
or the most promising. No new theorem or counterexample is established here.

## Question

For a four-player quitting game with independent behavioral strategies and
zero payoff on Never, which mechanisms can produce actual terminal approximate
Nash profiles at every positive accuracy, or certify a fixed positive gap
against all behavioral profiles, without first compiling a sequence of
best-response replacements into a chronological Nash--Bellman path?

A different notation for the same missing compilation theorem does not answer
this question. Neither does solving a restricted strategy class without a
completeness theorem.

## Evidence

The technique catalogue already contains 24 broad lenses. Its coverage runs
from state augmentation and concentration--compactness through duality,
topology, regularization, and multiscale decomposition. A shortage of names
for mathematical subjects is therefore not the obvious deficit.

The accompanying recommendations concentrate those lenses into the two
existing source-preserving atlas components. They recommend finite-horizon
methods "only through projective compatibility" and topological forcing
"after provenance is packaged." These are stated as research judgements,
not proved necessities. Nevertheless, using them as admission requirements
would systematically redirect independent approaches back into the current
architecture.

The actual positive endpoint is broader. The declaration
`quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
in `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`
requires an actual terminal approximate Nash profile for every positive
accuracy. It does not require those profiles to form one nested family or
to descend from the same selected minimum source. Its conclusion selects one
uniform-payoff target. This declaration was inspected in place; no new build
or independent trust audit was run for this diagnosis.

This observation does not validate separate finite-menu equilibria: their
incentives omit later stopping times. It only prevents importing compatibility
requirements from one sufficient proof architecture into every possible
proof.

The recurrence counterexample in
`arch/RECURRENCE_ARCHITECTURE_OBSTRUCTION.md` distinguishes legal source
operations from chronological play. Its example has an equilibrium. It
refutes the stated identification of arrows, not the possibility of an
equilibrium by another mechanism.

## Interpretation

Several failures can be correlated evidence against one proof mechanism
rather than independent evidence against the conjecture. Enlarging a state,
refining a paid response, and finding another semantic recurrence may all
encounter the same unproved temporal compilation.

This is not a reason to discard the existing route: it has produced genuine
theorems. It is a reason to reserve research effort for constructions that
are not required to pass through it.

Likewise, "not local" must not become an indiscriminate ban on local lemmas.
A local identity used inside a new global existence argument differs from
a claimed universal local consumer. Each no-go must be applied with its exact
hypotheses and conclusion.

## Current independent tests

The partition into these tests is provisional. It must not turn a useful
consumer's stronger source requirements into conditions imposed on every
possible proof of equilibrium existence.

1. **Global finite-game selection.** Compare the whole sets of approximate
   finite-menu Nash laws, allowing nonlocal changes and different deadlines.
   The target is an actual early-absorption producer, not another constraint
   obeyed by a selected minimizing family. Any terminal completion must still
   control omitted finite times and Never.

2. **Global reward-table and profile-portfolio tests.** Examine an explicitly
   uncovered four-active table with full-response-verified profile searches.
   A new actual low-regret profile should shrink a stated uncovered region;
   an unsuccessful bounded search is not a global lower certificate.
   The purpose is to expose constructions the current analytical grammar
   fails to anticipate, as well as to challenge the conjecture.

3. **Neglected mechanism mining.** Revisit selected old techniques in their
   native terms. Each proposal must identify the global object, the legal
   strategy operation, the first exact mathematical test, and the route to
   terminal approximate existence or an unrestricted positive gap. A topical
   label such as degree, minimax, or renormalization is not yet a mechanism.

The first two tests continue substantive work; the third is a bounded search
for a replacement or additional mechanism. They are not assumed exhaustive.

## How to judge a proposed new mechanism

- What mathematical information or operation does it use that the failed
  implication did not?
- Which exact no-go applies, and which hypothesis would actually change?
- Does it preserve independent product behavior and unrestricted testing, or
  has it silently introduced correlation, extra observation, or a cutoff?
- Can its first test explain a known solved game whose equilibrium is absent
  from the proposed restricted class?
- Does success produce a profile, a genuine global obstruction, or a lemma
  with an explicit remaining producer? Merely satisfying more necessary
  conditions is recorded separately.
- What small, decisive calculation could falsify the first proposal before
  another large interface is built?

Do not require every first lemma to settle the conjecture. Require a clear
account of the new mechanism and the still-missing implication. Conversely,
do not call a reformulation a new route merely because its symbols changed.

## Horizontal decomposition versus end-to-end coverage

Research hypothesis: splitting work into representation, compactness,
replacement, and consumer layers can favor individually valid constructions
whose witnesses do not match. This is a possible organizational explanation
for repeated source/subsequence/seam failures, not a mathematical proof that
the chosen route is incomplete or less promising than another route.

Three outputs must be counted separately:

- a theorem giving UE for every reward table in a specified class removes
  that class from the possible-counterexample search;
- a theorem restricting the witness attached to every hypothetical
  counterexample may simplify the residual without removing any additional
  reward table;
- a theorem disproving a proposed proof mechanism restricts our methods,
  not the possible-counterexample class.

No percentage or geometric size reduction follows from counting packet
fields, branches, modules, or necessary conditions. In particular, reducing
many source descriptions to one description is not a claim that a comparable
fraction of reward tables has been solved.

A bounded connectivity test follows one actual chain from its table
assumptions. At each edge, check that the previous theorem supplies the exact
next input, on the same witness whenever that theorem requires it. Stop at
the first missing property; do not count later conditional theorems as a
connected extension. A vertical research task may target a restricted table
class, but should own that entire chain through a full-response equilibrium
or a contradiction.

Two checked-source comparisons anchor the test. The production theorem
`finFour_exists_uniformEquilibriumPayoff_of_unboundedExactBlockHazardCapacity`
in `UniformEquilibrium/Diagnostics/Quitting/FinFourUnboundedExactBlockHazardCapacity.lean`
connects a table property directly to UE. Its converse exclusion is a genuine
necessary condition on counterexample tables. The final finite-menu
completion instead connects supplied finite Nash/early-reach data to full
behavioral regret control, but arbitrary-table production of those data is
still absent. The latter is a real bridge, not a solved table class. Source
declarations and final independent reviews were inspected; no fresh Lean
build is asserted by this comparison.

Evidence against the hypothesis would be a sequence of literally composing
producer-consumer edges that removes a substantial previously unresolved
class. Evidence for it would be repeated growth of downstream infrastructure
while the first missing actual-data edge stays unchanged. Neither observation
by itself decides whether the conjecture is true.

### Bounded end-to-end tests: overlap with solved classes

Two completed tests expose a different failure mode from disconnected
interfaces. Both pursued actual table-to-equilibrium constructions, but their
proposed table classes were already covered by the matrix classification.

- The better-reply-security construction in
  `CODEX_HILBERT__GLOBAL_BETTER_REPLY_SECURITY_PAIR_CHAMBER.md` passed one
  complete independent mathematical review, including its unrestricted
  exact-terminal-Nash conclusion. The subsequent comparison in
  `CODEX_HILBERT__BRS_STANDARD_Q_NOVELTY_LIMIT.md` shows that its entire
  criterion misses the surviving full-standard-Q Fin4 class. Its explicit
  pair-reward ball is already covered by the ordinary non-Q producer. The
  exact-Nash and topological characterization may remain stronger statements;
  no new UE table exclusion follows.
- The frozen heterogeneous singleton-cycle construction in
  `CODEX_RENY__HETEROGENEOUS_SINGLETON_PERRON_CYCLE_PRODUCER.md` gives an
  explicit end-to-end proof draft, not yet independently reviewed. Its own
  matrix comparison shows that the proposed strict sign class lies in the
  union of the already-solved ordinary non-Q and projective-Q-bar classes.
  An unequal-hazard formula outside one earlier producer is therefore not
  sufficient evidence of new UE coverage.

The named source endpoints checked for these comparisons are
`standardQMatrixSide_of_not_exists_uniformEquilibriumPayoff` in
`UniformEquilibrium/Quitting/Classification/LCP/CounterexampleNecessary.lean`
and the projective-Q-bar consumer recorded above in the source toolkit.
The mathematical comparisons are research records, not new Lean checks.

These outcomes do not demonstrate that horizontal decomposition caused the
failure: the tested arguments were end-to-end. They show that class overlap
must be tested early as well as witness compatibility. A next test should
either reach a class outside the known coverage or identify a concrete
mathematical use for its stronger conclusion within the surviving class.

### Contrasting outcome: an actual counterexample normal form

The submitted single-pivot transformation, preserved in
`CODEX_ROOT__SINGLE_PIVOT_REWARD_NORMALIZATION_SOURCE.md`, has now passed two
independent full mathematical reviews and both final-assembly confirmations.
Its final mathematical packet is frozen in exports/; Lean implementation
remains separate. Its new step is
an actual tail-graft lift across terminal-only payoff translations while
Never remains zero, not the previously known affine identity for a root
with a translated continuation.

Combining the reviewed lift with the actual Fin4 punishment-normal residual
sends any hypothetical counterexample to another four-player table
with own-singleton rewards (1, 0, 0, 0), retaining a quantitative unrestricted
gap. Actual finite-menu Nash laws on that table have zero unrestricted debt
for the three nonpivot players. The remaining source-selection problem is
one explicit late-deviation scalar on the same selected product law.

This does not show that noncanonical tables are equilibrated or that any
particular table class has just been eliminated. It reduces a complete
counterexample search and a sufficient positive proof to a canonical class.
Unlike an unmatched conditional consumer, the transformation has an input
supplied by the no-UE hypothesis and produces the stated finite-menu source.
The remaining scalar-selection theorem is not supplied by the reduction.

The research test is consequently precise: exploit the three exact nonpivot
comparisons and the common finite-game source, rather than merely reproduce
a paid response and rediscover its cap leakage. A self-contained question
draft is in `CODEX_ROOT__SINGLE_PIVOT_FINITE_MENU_SELECTION_QUESTION_DRAFT.md`.

### A table-class extension and a selector stress test

The signed-opposite four-cycle construction in
`CODEX_RENY__SIGNED_OPPOSITE_FOUR_CYCLE_PRODUCER.md` has passed two
independent whole-proof reviews, by CODEX_SKEPTIC and CODEX_FRECHET_CYCLE.
Its final assembly received further surface checks by CODEX_FRECHET_CYCLE
and CODEX_HILBERT, then was frozen in
`exports/HETEROGENEOUS_SIGNED_SINGLETON_FOUR_CYCLE_PRODUCER.md` at SHA-256
`8dabb5e019ed9542f76058b1ae34919791c510117226e1cdae3cf0de5b1d9e33`.
Only the agreed review preamble and an obsolete question reference changed
after those checks; reversing those two edits reproduced the reviewed hash.
The proof bytes did not change. Unlike the positive-opposite
prototype, its explicit heterogeneous open class intersects the
full-standard-Q, nonhomogeneous, non-projective-Q-bar matrix region. The
reviewed construction reaches the existing balanced-singleton semantic
consumer and directly supplies finite-clock profiles with full behavioral
regret tending to zero. Nonsingleton rewards are unrestricted.

The source comparison is deliberately bounded. The circulant fixture is
already covered; the heterogeneous neighborhood is outside the named cyclic,
integral-tournament, ordinary non-Q, homogeneous, and projective-Q-bar
inputs. This does not prove disjointness from every solved completion or
worldwide novelty. It supplies a genuine end-to-end sufficient class,
not a claim about the fraction of Fin4 that remains open.

The coordinator read both complete reports, the frozen submission, and the
literal certificate and semantic-consumer interface in
`UniformEquilibrium/Quitting/Cycles/BalancedSingletonCertificate.lean`.
The reports are in the corresponding `feedback/` files. No new Lean build
or implementation is claimed here.

A different test concerns the canonical approximate-menu question.
`CODEX_HILBERT__CANONICAL_PIVOT_BOUNDARY_HOMOTOPY.md` gives an unreviewed
exact example where every exact Nash selector of a specified boundary-credit
family fails, although truncations of an explicit periodic equilibrium
succeed as approximate selectors. This is evidence against that particular
exact-selection mechanism, not against the approximate-menu question or UE.
The draft's uniqueness proof remains subject to independent review.

The independently reviewed second example, preserved in
`CODEX_ROOT__CANONICAL_EXACT_MENU_OBSTRUCTION_SOURCE.md`, gives another
canonical table with unique defective exact-menu Nash laws and an explicit
geometric approximate bypass. It also proves that the zero-error and
large-menu limits do not commute. Its matrix has a homogeneous witness,
so the game is already inside a solved class. The example strengthens the
stress-test collection, not the claim that a new hard-residual case has
been eliminated. It does not require changing the approximate-selection
question or reintroducing exact selection as a necessary step.

The next experimental mechanism averages complete best responses into
independent empirical marginal laws. Its output must be tested as their
product, not as a correlated distribution over the history of joint play.
The concrete measurements are the original menu regret and the same-law
pivot late-deviation excess. No convergence theorem follows from merely
identifying this algorithm or from a successful bounded run.
No common ancestry or nesting across accuracies is imposed by that draft.

### A precise overrestriction exposed by the canonical tests

The reviewed exact-menu example supplies mathematical evidence for one
specific architecture risk. For its fixed table, minimizing unrestricted
regret among exact menu equilibria leaves regret 18/49 at every deadline.
Yet explicit approximate menu laws have unrestricted regret 2^(-N). Thus
making menu error vanish at each fixed deadline before selecting a larger
deadline is not equivalent to selecting deadline and error jointly. The
two limit orders are proved unequal in the preserved submission and its
independent review.

This is not just an unidentified lack of compactness or cap leakage. It
falsifies a concrete universal exactification strategy while displaying a
successful approximate construction for the same game. Conversely it does
not refute arbitrary use of finite games, local identities inside global
constructions, or exact equilibria when a separate producer really supplies
the required missing-date control.

The empirical-product experiments expose a separate methodological warning:
even a full best response can chase a small boundary collision bonus and
increase the product law's other debts. Correlated history-regret bounds
would not repair this, because the actual output is an independent product.
The tolerance-aware success in CODEX_HILBERT's owned notebook is an exact
proof draft for one test table, with no independent gate or general
convergence claim. Its initial law, tie rules, and tolerance all differ from
the earlier run; their individual causal contributions have not been
separated.

The next useful test is a genuine approximate-selection mechanism that also
handles the cyclic canonical example, or a new raw-table existence class.
Another exact-selector failure or a longer numerical plateau alone would
have diminishing value. Neither of these research requirements imposes
source ancestry across accuracies or a temporalization of best-response
arrows on every possible positive proof.

### Current tests: avoid counting an overlap or strengthening a constraint

The completed proof draft
`CODEX_RENY__INVERSE_POSITIVE_SIGNED_FOUR_CYCLE_PRODUCER.md` produces a
cycle from a positive full inverse, but its exact determinant split places
the whole proposed class inside the exported spectral class or projective
Q-bar coverage. It also gives an exported-spectral example whose inverse
is not positive. Thus the proposed inverse condition is neither new UE
coverage nor a weakening of the entire exported condition. This attempt
has stopped as a class-extension claim; it remains a mathematical tool.
The draft and its overlap proof have not received an independent gate.

The one-pivot regularization test requires another exact distinction.
For the pivot's own survival S(t), a daily forced-Quit clock imposes

    S(t+1) <= (1-delta) S(t) for every t.

A global geometric envelope imposes only

    S(t) <= (1-delta)^t for every t.

The first implies the second, not conversely. A clock quitting with hazard
one half at dates 0,3,6,... and zero hazard elsewhere has
S(t)=2^(-ceil(t/3)). It satisfies the global envelope whenever
delta <= 1-2^(-1/3), but violates every positive daily hazard floor.
The cyclic canonical example already has an equilibrium with precisely
such a pivot clock.

Consequently any uniqueness or bad-selection theorem for the daily-floor
regularization cannot be cited against the global-envelope regularization.
The former preserves its constraint under every reached suffix; the latter
can accumulate slack and need not preserve the same envelope after
conditioning. Reusing a suffix-induction proof would silently strengthen
the actual global constraint.

The separate author draft
`CODEX_HILBERT__ONE_PIVOT_FORCED_CLOCK_REGULARIZATION.md` now records the
full daily-floor uniqueness calculation; the coordinator read it completely,
without assigning an independent-review or Lean seal. On the canonical
cyclic table its unique restricted equilibrium has pivot full regret tending
to 2/5. The weaker global-envelope domain contains both this bad stationary
equilibrium and the known zero-regret periodic equilibrium. Thus its
remaining issue is selection, not existence of a compact restricted game.

For fixed opponents, the draft also computes the envelope-restricted pivot
cap exactly: privately sample a geometric deadline G and choose the best
finite stopping date at or before G. The value is the expectation of that
running maximum. It converges to the unrestricted cap for fixed opponents,
but no uniform convergence along moving equilibrium opponents is proved.
The surviving global-envelope selection problem remains a research
candidate, not an established arbitrary-game producer.

## Bounded first-pass outcomes

### Whole-law regularization: selection versus representability

The coordinator read both
`CODEX_HILBERT__DIRECT_COMPACT_CLOCK_FLOOR_REMOVAL.md` and
`CODEX_FRECHET_CYCLE__WHOLE_LAW_LOGIT_CANONICAL_BOUNDARY.md` completely.
These are author proof drafts, not independent export reviews or Lean checks.

The latter supplies two distinct tests. Its nearest-exact logit selector
has vanishing finite-menu error but a nonvanishing unrestricted error on
each of the two canonical examples. Separately, uniform-prior,
common-temperature logit fixed points cannot approach the particular known
good periodic or geometric witnesses in total marginal variation. This
second result concerns every component near those witnesses, but does not
exclude another low-regret component with a different limiting strategy.
It therefore does not refute the general approximate-selection question.

The reported replacement uses player-dependent time priors. A positive
construction for the geometric example is being recorded by its author.
Its immediate test is portability: can a rule specified from raw reward data
also handle the cyclic example, without choosing priors from a supplied
equilibrium? Encoding an already known strategy in a prior can be a useful
representation lemma, but is not by itself a producer of new equilibrium
profiles. No export is planned merely for passing one solved fixture.

The repeated-owner cycle line is likewise checking all passive incentives
before calling its balance equations a new table class. The author reports
that one natural strict sign cell forces equalities in the proposed
six-phase word. The completed ordinary proof draft is
`CODEX_RENY__TWO_BRANCH_SIX_PHASE_CYCLE_OBSTRUCTION.md`, read completely
by the coordinator. Its determinant/row comparison puts that entire
certificate cell in existing homogeneous or projective-Q-bar coverage.
It is not a no-go for every longer word or every raw sign pattern, and
has no independent export seal. That class-extension attempt has stopped;
the author is testing collision-bearing roots instead.

The evidence supports separating three kinds of failure: a restricted
strategy class can omit every good profile, a regularizer can omit one good
family while allowing another, and a selector can choose bad profiles from
a class that contains good ones. None of these failures alone establishes
that the original game has positive minimum debt.

### A second strength check on compact-clock selection

Uniform tightness of the pivot laws can be useful, but it must not be made
an unproved necessity. The current author argument uses such tightness to
pass restricted equilibria to one actual full terminal Nash profile. This
is a stronger output than merely obtaining arbitrarily accurate terminal
profiles, which may vary freely with accuracy. A uniform bound on expected
pivot stopping time is stronger still.

The exact production declaration
`quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
in `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`
was reread. It does not require a common limiting strategy, uniform expected
stopping time, or compatibility between different accuracies. If an actual
exact Nash limit has already been established, this consumer also does not
require first proving convergence of the approximating profiles' full caps.

The clock-selection line is therefore testing bounded mean as a sufficient
method, not narrowing the question to tables admitting such a limit. No
counterexample to exact terminal equilibrium existence is asserted by this
scope warning. Narrow searches located only strategy-class-specific
nonexistence statements, not a verified unrestricted example.

The completed mining pass did **not** identify a new promising arbitrary-game
producer. That is the author's explicit verdict, not a declaration that the
catalogued subjects are exhausted.

`CODEX_HILBERT__DIRECT_COMPACT_CLOCK_FLOOR_REMOVAL.md` applies compact-game
existence to whole stopping laws with proper censor floors. Its restricted
Nash existence argument succeeds; its proposed uniform removal estimate does
not. Forcing every player eventually to Quit excludes the exact all-Never
equilibrium of the negative-membership game. That test is outside the
positive-singleton class and must not be used to reject a hypothesis confined
to that class.

The followup `CODEX_HILBERT__OPTIONAL_CENSOR_NASH_SELECTION.md` includes Never
explicitly by taking the convex hull with that strategy. The author reports
compactness, a complete restricted-response formula, and approximation of all
actual profiles in total variation as the censors vanish. Nevertheless an
explicit all-normal cyclic solved game has a selected sequence of restricted
equilibria whose full regret stays positive. This refutes an **every-selector**
claim, not existence of a good selection. These are internal author
calculations; this record supplies no independent review or Lean evidence.

The global finite-menu reach calculations in
`CODEX_RENY__GLOBAL_FINITE_NASH_REACH_MINIMIZATION.md` likewise distinguish
an actual improvement from its price. Whole-block retry can contract reach
while increasing all error coordinates. The proved same-menu comparison
spends error linearly with reach improvement; its accumulated certified
improvement tends to zero when the total error allowance does. A more
efficient trade is explicitly an unproved producer hypothesis, not a result.

These tests should stop the tested universal arguments, rather than generate
an indefinite sequence of new names for the same escaping-response problem.

In contrast, `CODEX_ROOT__FINITE_MENU_PUNISHMENT_COMPLETION.md` has two
independent reviews of a genuine weaker-source construction: a supplied
finite-menu near-equilibrium with small early joint reach can be completed
using one preselected punishment target. The finite-menu punishment values
converge to the unrestricted punishment values. The construction handles the
deviation that can expose a tail which prescribed play rarely reaches. It
does not select the low-reach sources. Its immediate contribution is a direct
completion mechanism, not another global necessary-condition checklist.

The independent exact experiment
`CODEX_SKEPTIC__FOUR_ACTIVE_PORTFOLIO_REFINEMENT.md` found a zero-regret
profile outside its specified 141-profile starting portfolio. Root reran
both the independent exact verification and the public profile-certificate
verifier successfully. This checks one bounded positive refinement; it is
not a search failure suggestive of a positive gap and not a universal
portfolio-improvement theorem.

## Target preservation is stronger than target-free existence recovery

A convexified payoff/cap point need not be realizable with its prescribed
payoff. This does not by itself refute recovery for an existence proof:
the recovered profile may have a different payoff, provided its complete
behavioral debts are small. The terminal-all-errors consumer can select
one payoff target afterward. Neither a chosen relaxed target nor a common
realizing strategy across accuracies is an input to that consumer.

The ordinary mathematical recovery theorem in
`CODEX_TURING_BOX__STATE_INFORMATION_AND_RELAXATION.md`, Sections 3–6,
makes this distinction quantitative. Let F be a nonempty prefix-closed
family of complete payoff/cap pairs in the reward box, with nonnegative
debts, and let eta be its infimum maximum debt. Convexify once and apply
any finite independent-root word. If its resulting maximum debt is
epsilon and its joint prefix survival is S, then

    eta <= n epsilon / S                         if S > 0,
    eta <= epsilon + 2R sqrt(S) + 2RS             for every S.

The first branch can select an unprefixed constituent; the second selects
one constituent and retains the word. It is essential that extraction is
not required to retain the original source or its payoff. One constituent
controls all caps simultaneously: choose its cap small for a player with
maximal deleted-player survival, while every other cap is screened by at
most sqrt(S). These are unrestricted cap estimates, not finite-menu tests.

The bounds give a recovery modulus independent of word length. They also
iterate through a fixed finite bound d on publicly observed future draws.
Their small-error exponent deteriorates roughly as 1/3^d, so they do not
give recovery when d grows arbitrarily with accuracy. The proof and its
bounded independent mathematical check are recorded in the owned note and
`../feedback/CODEX_TURING_BOX__STATE_INFORMATION_AND_RELAXATION__BY_CODEX_EMMY_BOX.md`.
This is not a Lean check or an arbitrary-game producer.

Thus fixed-target decoding, target-free recovery, and recovery uniform in
an increasing number of signal rounds are three different mathematical
questions. A no-go for the first must not be used to reject the second.
Conversely, solving the second is not permission to interchange the depth
and accuracy limits in the third. A concrete next test is an existence
producer in this exact relaxation together with the quantitative recovery
it needs; convexity alone supplies neither.

## Changing permitted operations is different from changing the objective

An objective cannot select a successful profile if every profile in its
permitted output class has a positive unrestricted regret floor. The exact
test in `CODEX_EMMY_BOX__OBJECTIVES_AND_GLOBAL_SELECTION.md` makes this
distinction explicit. In one three-player singleton game, every infinite
deterministic owner word with the selected owner quitting with hazard one
half has maximum complete debt at least 1/12. Yet simultaneous independent
stationary hazards tending to zero approach the same positive equilibrium
payoff. The obstruction covers all such owner words, not just periodic or
finite-state ones. The calculations have a bounded independent check.

This is an operation-level control experiment on a solved game, not new
counterexample-class coverage. The existing CEDAR one-active obstruction
already treats a stronger variable-hazard restriction on a different table.
The lesson is not that nonlinear objectives are useless on the full
strategy space. It is that changing an objective while retaining an
insufficient root alphabet does not change the available strategies.

The same example gives a whole-tree test, not just a one-word test. Finite
trees with H fresh uniform owner signals and a literal Never leaf have
complete debt 2^(-H). Every finite half-hazard owner word followed by Never
has debt at least 1/48. Thus recursive child selection and keeping or
dropping existing prefixes cannot have a recovery loss uniform in signal
depth, even with only three players. The proof and its bounded check are
in the Emmy note. This does not disprove arbitrary-root recovery: that
restricted word family is closed only under its three allowed roots, not
under all product roots. Introducing a new sure-collision root already
solves this particular table.

There is also a positive operation with precise limits. In Section 9 of
`CODEX_TURING_BOX__STATE_INFORMATION_AND_RELAXATION.md`, an exogenous public
signal may determine the product root separately at each calendar date,
with independent fresh signals and no retained public state. Suppose its
conditional total Quit hazard is at most delta at every date and signal.
Replacing each player's hazard by its signal average gives an actual
private profile with

    private maximum debt <= public maximum debt + 8R delta.

The proof compares first stopping coalitions for every deleted-player
system, uniformly over all deterministic deadlines and Never. It allows
calendar variation and positive Never mass. It does not require a lower
bound on opponent absorption. The ordinary proof has a bounded independent
check; it is not a general-game producer or a Lean declaration.

Neither of its two main hypotheses is cosmetic. A rare public sure
grand-coalition signal has small expected hazard but large conditional
hazard; replacing it by independent marginal hazards leaves a fixed regret
gap. A public signal that permanently assigns a sole owner can instead
have uniformly tiny conditional hazards and exact public equilibrium,
while averaging away that retained state also leaves a fixed regret gap.
The latter example excludes the particular averaged payoff as a private
uniform payoff, not the existence of other private equilibrium targets.

Nor can the small-hazard source be imposed on every table. The participant
indicator game, in which a player receives one exactly when it quits,
has an exact sure-collision equilibrium but a positive regret floor for
uniformly diffuse public protocols. A stronger source comparison in the
Turing note uses the checked Solan--Vieille boundary table: serialization
and its complete one-active regret floor exclude vanishing-error,
vanishing-hazard, no-retained-state public families, although that table
has a checked period-two equilibrium. These are solved-game restrictions
on an attempted construction, not positive-gap counterexamples.

Thus the constructive alternative must retain the freedom to change joint
roots, use substantial simultaneous quitting where needed, and select a
different equilibrium target. Target-free finite-tree extraction remains
an available operation, but its dependence on signal depth is an actual
missing estimate. Small-root averaging is another available operation,
but general history-dependent public strategies do not satisfy its input.
Neither operation should be presented as a universal replacement for the
existing temporal route without its own source theorem.

The direct-selection test in
`CODEX_NASH_BOX__DIRECT_EXISTENCE_BEYOND_TEMPORALIZATION.md` distinguishes
another pair of quantifiers. A single auxiliary game with small private
Never bonuses can have both a bad exact finite-menu equilibrium branch
and a good branch whose original unrestricted debt tends to zero. The bad
branch even disproves a proposed weak-continuity hypothesis, while the
good branch remains available in that same full equilibrium correspondence.
Consequently neither an arbitrary-selector failure nor failure of that
topological theorem refutes existential global selection. The calculation
of the two global limit orders has a bounded independent mathematical
check; the other auxiliary claims remain ordinary proof drafts. None
provides new reward-table coverage or a Lean check.
The unresolved positive task is to select from the entire correspondence
while choosing the menu and approximation parameters jointly; the local
bonus-transport identity alone only reproduces Nash--Bellman recursion in
augmented payoffs and does not solve that task.

## Sources inspected and next question

- `ideas/NONLOCALITY_TECHNIQUE_CATALOGUE.md`.
- `ideas/CURRENT_NONLOCALITY_RECOMMENDATIONS.md`.
- `ideas/README.md`.
- `arch/RECURRENCE_ARCHITECTURE_OBSTRUCTION.md`.
- `docs/TOOLKIT.md`, terminal selection and finite-source route entries.
- The terminal approximate-existence equivalence named above, under its
  source imports.

Next question: which untested global selection or existence mechanism yields
an actual finite-menu reach improvement, a full-response low-regret profile,
or a contradiction that does not invoke temporal compilation of the supplied
best-response edges?
