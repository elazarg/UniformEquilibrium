# Blindspot audit: global dynamics, independent clocks, and correlation

Author: `CODEX_GROTHENDIECK`
Status: `IDEA`

Current status: this was one bounded strategic audit, not a proof attempt and
not checked in Lean.  Its main finding is that the conference portfolio is
mathematically serious but too concentrated on local Bellman/certificate
production and low-player examples.  The sharpest underused route is Simon's
finite-dimensional correspondence: subject to a paper-level theorem whose
critical necessity direction still needs an audit, a global bounded-variation
certificate for one `F_epsilon` graph would rule out **all** quitting profiles,
not merely a controller class.  This suggests a six-to-eight-player,
computer-assisted counterexample search using multivalued dynamics and strict
Lyapunov functions.  The positive mirror is Simon's still-open topological
Question 1.

The one proved item in this notebook is the elementary Lyapunov variation
bound in Candidate 1.  Everything else is labelled `CONJECTURE`, `ANALOGY`, or
`EXPERIMENT` as appropriate.

Next concrete question: for a sparse six-player reward family with no
stationarily generated or instant approximate equilibria, can one find one
rational `epsilon > 0`, a compact rational/near-feasible carrier `K`, a
piecewise-affine `V`, and `c > 0` such that

`V(y) <= V(x) - c * ||y-x||_1`

for every nontrivial `F_epsilon` edge `(x,y)` in `K`?  Before trusting the
consequence, independently repair or refute the necessity direction of Simon
2007/2012 Theorem 3.

## Exact audit question

Fix a nonempty finite player set `I` and rewards

`r : {S subset I | S nonempty} -> R^I`.

The base game has one live state.  At date `t`, each player independently
chooses Continue or Quit as a behavioral function of the public history.  A
nonempty quitter set absorbs at `r(S)`; eternal continuation pays zero.  The
target is one fixed vector `v`, chosen before the accuracy.  For every
`eta > 0`, one behavioral profile may depend on `eta`, but it must deliver `v`
and cap replacement of any one player's complete behavioral strategy for all
sufficiently long finite horizons.

The audit asks:

> Is there a mathematically serious route to either terminal approximate Nash
> profiles at every accuracy or a fixed terminal exploitability gap against
> every behavioral profile which the current conference has ignored or
> reduced prematurely to local certificate engineering?

I treated the following as disqualifying shortcuts:

- a target varying with accuracy;
- a stationary, periodic, solo-hazard, or bounded-controller no-go without a
  completeness theorem;
- public correlation not present in the base game;
- a supplied-object verifier without an arbitrary-game producer; and
- an asymptotic, discounted, or terminal claim without the relevant bridge.

## Board refresh and scope of inspection

The board was refreshed immediately before this file was written.  It then
contained the Banach/Hilbert singleton and solo-hazard notes, Cedar's paid-row,
radial-packet, and atom-chronology notes, Gauss's stationary toggle/face work,
and Noether's quit-time compactification note.  No existing conference note
attacked Simon 2012 Question 1, Simon's full `F_epsilon` orbit equivalence, or
a cross-time independent-clock coalition inequality.  The current export
queue contained only special-class or named-table results.

I did not survey the Lean tree.  The bounded symbol searches used the terms
`SimonViability`, `QuestionOne`, `HasQuitApproximateEquilibria`,
`InfiniteOrbitCondition`, `sunspot`, `conditionedProductPurification`,
`pureTime`, `Puiseux`, and `vanishing discount`, and stopped after the sources
below made the candidate obligations precise.

## Sources checked

### Exact project declarations

- `quittingUniformEquilibriumPayoffConjecture`
  (`UniformEquilibrium/Quitting/Conjecture/Basic.lean`) is an open proposition,
  not a theorem.  Its source commentary records Simon's expectation that a
  counterexample, if one exists, is unlikely below six players and is more
  promising around eight, probably with computer assistance.  I did not
  inspect the original Simon 2016 article in this session, so I use this only
  as the repository's recorded search heuristic.
- `quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
  (`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`)
  is the checked positive endpoint.
- `not_exists_uniformEquilibriumPayoff_iff_exists_terminalExploitabilityGap`
  (`UniformEquilibrium/Quitting/Terminal/ExploitabilityGap.lean`) is the checked
  negative endpoint.
- `sSup_range_quittingTerminalPayoff_update_eq_pureTime`
  (`UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean`) proves
  that, against fixed opponents in the terminal problem, unrestricted
  behavioral best response reduces to deterministic quit times.
- `Math.Topology.SimonViability.QuestionOneHypotheses`,
  `QuestionOneConclusion`, and `QuestionOneAffirmative`
  (`MathUE/Topology/SimonViabilityQuestion.lean`) state Simon's topological
  question independently of quitting games.  `QuestionOneAffirmative` is an
  open proposition.
- `QuestionOneHypotheses.exists_oneEdgeBudgetedPrefix` and
  `QuestionOneHypotheses.conclusion_of_edgeBudgetedFinitePrefixes`
  (`MathUE/Topology/SimonViabilityBudgetCompiler.lean`) show, respectively,
  that the seven hypotheses give one charged edge and that compatible finite
  prefixes meeting one diverging variation budget give the requested
  unbounded extended orbit.  They do not iterate the one-edge output.
- `scale_eq_one_of_conditionedProductPurification_two_active` and
  `no_conditionedProductPurification_of_two_active_phantom`
  (`UniformEquilibrium/Quitting/Cycles/ConditionedProductPurification.lean`)
  prove exact rowwise rigidity of a conditioned product law with two active
  quitters.  They do not give a cross-time law inequality.
- `collisionMass_logarithmicBlock_le_sq`
  (`UniformEquilibrium/Quitting/AbsorptionPath/LogarithmicBlockDiscretization.lean`)
  confirms that diffuse independent hazards suppress simultaneous quitting to
  second order.  Its continuous derivative/Bellman producer is not supplied.
- `no_vanishing_twoSided_entryTarget_realization`
  (`UniformEquilibrium/VanishingDiscount/Analytic/Endpoint/PrescribedEndpointTargetTransportNoGo.lean`)
  is a checked warning against automatically transporting a prescribed
  endpoint along a universal vanishing-discount calendar.  It is not a
  quitting-game counterexample.

### Literature statements and semantic mismatches

- Simon, *The structure of non-zero-sum stochastic games* (2007), Theorem 3,
  is transcribed as `Literature.Simon2007.theorem3_corrected_2012`
  (`Literature/Simon2007.lean`).  Under failure of stationarily generated and
  instant approximate equilibria, it claims equivalence of approximate
  equilibrium existence with cyclic, arbitrarily long finite,
  unbounded-variation infinite, and unbounded-variation extended
  `F_epsilon` orbit conditions.  The transcription is in the non-built
  Literature lane and the corrected theorem ends in `sorry`.  The local
  reading note `literature/Simon2007/defects.md` identifies an unexpanded step
  in the necessity direction: the proof selects a date whose survival lies in
  a prescribed interval without visibly ruling out a one-stage jump across
  that interval.  Therefore this is a serious paper-level bridge to audit,
  not a checked project theorem.
- Simon, *A Topological Approach to Quitting Games* (2012), Question 1 and the
  conditional all-game conclusion are transcribed as
  `Literature.Simon2012.Question1Affirmative` and
  `question1_affirmative_implies_all_quitting_games`
  (`Literature/Simon2012.lean`).  The latter also ends in `sorry`; several
  analytic adapters in the paper application remain open.  Question 2 is
  reported false via a Gobbino--Simon construction, so convex fibers and a
  boundary-fixed homotopy alone are not enough.
- Solan--Solan, *Quitting Games and Linear Complementarity Problems* (2020),
  Theorems 2.4 and 2.13 are represented as
  `Literature.SolanAndSolan2020.theorem2_4` and `theorem2_13_sunspot`
  (`Literature/SolanAndSolan2020.lean`).  They use an actual public-signal
  stochastic game; the Q branch has at most one quitter on path.  This is not
  an ordinary quitting profile, and the Literature lane is not a production
  theorem surface.

The `docs/FRONTIER.md` and `docs/TOOLKIT.md` entries were used only as maps.
In particular, the toolkit already records the Simon Question 1 boundary.
Thus Candidate 2 is not a discovery unknown to the repository; it is a route
sidelined by the current conference.

## Ranked candidate 1: Simon orbit obstruction plus a Conley/Lyapunov search

Classification: `PROOF` for the elementary lemma below; `CONJECTURE` for the
existence of a useful game certificate; `ANALOGY` for the Conley-theory
framing.

### Why this could change the universal obligation

The conference's negative work repeatedly runs into the same scope fence: a
positive gap on stationary, solo, periodic, or bounded controllers is not a
gap against all behavior.  Simon's Theorem 3 is designed to supply exactly
that missing bridge.  In its hard branch, one does not classify strategies.
One proves or refutes unbounded total variation of a finite-dimensional,
set-valued one-stage equilibrium correspondence.

The contrapositive search target is especially concrete.  For one fixed
`epsilon_0 > 0`, let `K` be the compact set of `epsilon_0`-rational,
near-feasible payoff vectors used in the finite-orbit clause, and let

`G = {(x,y) in K x K | y in F_epsilon_0(x)}`.

If every finite `G`-orbit has uniformly bounded variation, the finite-orbit
condition fails.  Subject to the corrected Simon equivalence and the two easy
branch exclusions, approximate equilibria fail at one fixed accuracy.  That
is an all-quit-profile statement, not a bounded-architecture screen.  After
the paper-to-production semantic adapter, it would feed the checked terminal
gap endpoint.

The natural field is multivalued dynamical systems.  A nontrivial recurrent
class or cycle creates arbitrarily large variation; a gradient-like graph
admits a complete Lyapunov function.  This is the same positive/negative
dichotomy the project has been trying to express with many local accounts,
but at the level where the paper's all-behavior theorem operates.

### A first exact lemma

**Lemma 1 (ordinary mathematics; proved here).**  Let `(K,d)` be any set with
a nonnegative distance, `G subset K x K`, and suppose there are a bounded
function `V : K -> R` and `c > 0` such that

`V(y) <= V(x) - c d(x,y)`

for every `(x,y) in G`.  Then every finite `G`-orbit
`x_0,...,x_m` satisfies

`sum_{t<m} d(x_t,x_{t+1}) <= (sup_K V - inf_K V)/c`.

**Proof.**  Sum the edge inequalities:

`c sum d(x_t,x_{t+1}) <= sum (V(x_t)-V(x_{t+1}))`

`= V(x_0)-V(x_m) <= sup_K V-inf_K V`.  This also permits self-loops, since
their distance is zero.  QED.

For computation, use `d(x,y)=||x-y||_1` and a piecewise-affine `V`.  The graph
of `F_epsilon` is defined by finitely many polynomial product-law equations
and inequalities after retaining the row variables.  A proposed certificate
is therefore a finite semialgebraic implication, amenable to exact rational
polyhedral subdivision, quantifier elimination, or a rigorous SOS-to-rational
certificate pipeline.  No floating-point certificate would suffice.

### First concrete test

1. Start at six players, not four.  Use a sparse directed "inspires-to-quit"
   graph with at least two overlapping proper cycles; the conjecture module's
   source commentary records this as the first plausible counterexample scale.
2. Prove exact positive gaps excluding the stationarily generated and instant
   branches.
3. Fix a small rational `epsilon_0` and retain the row variable in the exact
   semialgebraic graph of rational/near-feasible `F_epsilon_0` edges.
4. Search for a piecewise-affine `V` and rational `c > 0` satisfying Lemma 1.
5. In parallel, re-prove the suspect survival-interval step in the necessity
   direction of Simon's theorem.  Without that, the computation has no
   all-behavior consumer.

### Quick falsifiers and known failure mode

- Every known equilibrium table must defeat the Lyapunov search by a
  nonconstant cyclic or unbounded-variation orbit.  The Solan--Vieille
  boundary table, which has a checked period-two equilibrium, is a mandatory
  negative regression.
- A scalar decreasing only on a selected edge or one SCC is useless.  The
  inequality must hold on the entire set-valued graph in the carrier.
- A bound on one orbit is useless; Lemma 1 is valuable precisely because it
  covers every orbit.
- The decisive logical risk is the paper bridge.  The corrected equivalence is
  not checked in production and contains a known compressed step.  If its
  necessity direction is false, this route loses its all-behavior force.

## Ranked candidate 2: attack Simon 2012 Question 1 as native topology

Classification: `CONJECTURE`; the one-edge and finite-prefix compiler facts
cited here are proved in Lean, but the iteration theorem is open.

### Why this could change the universal obligation

Question 1 deliberately strips away quitting-game grammar.  Its seven
hypotheses concern a compact contractible union of full-dimensional convex
polytopes, a boundary-fixed straight homotopy, a compact correspondence with
contractible local fibers, and a uniform local escape segment near every
relevant boundary piece.  The requested output is an extended orbit of
unbounded variation.  Simon's paper claims that an affirmative answer,
together with game-facing analytic work, produces approximate equilibria for
all quitting games.

The project has already isolated the exact missing step:

`one charged local edge  !=  compatible prefixes with diverging budgets`.

This is a cleaner universal question than paid-row re-entry or atom
chronology, and a counterexample would decisively retire a published proof
program rather than one repository certificate.

### First concrete lemma/test

Prove or refute the following **restartable escape lemma** first in dimension
one and then for one polytope:

> Under the Question 1 hypotheses, there is `a > 0` and a compact restart set
> `R` such that every finite full-graph orbit ending in `R` extends to another
> point of `R` while adding variation at least `a`.

If true, iteration gives prefixes with budget `a n`, and
`QuestionOneHypotheses.conclusion_of_edgeBudgetedFinitePrefixes` supplies the
extended orbit.  If false, retain the smallest exact counterexample and test
whether it can be thickened to satisfy all seven hypotheses.

The adversarial companion test is to adapt the reported two-dimensional
Gobbino--Simon counterexample to false Question 2 and ask exactly which
Question 1 hypothesis prevents it.  This should happen before attempting a
general homology proof.

### Quick falsifiers and known failure mode

- Question 2 is already reported false.  "Compact convex fibers plus
  homotopy" is therefore not a valid proof sketch.
- The checked one-edge theorem may send the endpoint away from the part of the
  frontier where the escape premise can be reused.  Monotone distance to one
  polytope is not a return mechanism.
- Even a proof of abstract Question 1 does not by itself check Simon's full
  game application: `lemma4_5` and the abnormal-player construction in
  `Literature/Simon2012.lean` retain open analytic obligations.

## Ranked candidate 3: independent quit times as a common-randomness no-go

Classification: `CONJECTURE` for the inequality; `EXPERIMENT` for a reward
gadget search; the two-stage equality calculation is exact.

### Why this could change the universal obligation

Conditional on survival, the public history of an ordinary quitting game is
just another all-Continue date.  Thus an on-path behavioral profile is a
deterministic sequence of product Bernoulli rows, equivalently a tuple of
independent player quit times `T_i` in `N union {infinity}`.  Moreover the
checked pure-time extremality theorem says that a unilateral terminal best
response is already a deterministic quit time.

This suggests using noninteractive-correlation inequalities, not another
controller enumeration.  Public-signal equilibria can correlate which
coalition quits.  Ordinary profiles can only create ties among independent
clocks.  A reward table that makes two incompatible coalition ties necessary
could yield an all-profile gap once the clock inequality and incentive gadget
are both proved.

### First concrete lemma/test

Take four clock players and disjoint pairs `A={1,2}`, `B={3,4}`.  Define

`a = P(T_1=T_2 < min(T_3,T_4))`,

`b = P(T_3=T_4 < min(T_1,T_2))`,

and let `ell=1-a-b`, including every other first-quitter coalition and the
Never event.

**Clock-tie conjecture.**  For independent `T_1,...,T_4`,

`ell^2 >= 4 a b`.

The simplest two-date construction attains equality.  At date zero let
players 1 and 2 quit independently with probability `1-delta`, while 3 and 4
continue.  Conditional on survival, let 3 and 4 quit surely at date one.  Then

`a=(1-delta)^2`, `b=delta^2`, `ell=2 delta(1-delta)`,

so `ell^2=4ab` exactly.  At the balanced point `delta=1/2`, at least half the
law leaks to the two unwanted singleton coalitions.  Diffuse hazards do not
evade this: simultaneous pair mass is second order, consistently with
`collisionMass_logarithmicBlock_le_sq`.

The first task is to prove or refute the inequality for arbitrary countable
independent clock laws.  A proof should use stopping-time atoms and survival
tails, not finite truncation.  The second task is a six-player rational reward
gadget: four clock players plus two calibrators whose Nash inequalities force
`a,b >= alpha` and `ell <= beta` with `beta^2 < 4 alpha^2`.  Then some player
must have a fixed gain.  Exact search may suggest the table, but the final
argument must quantify over all independent clock laws and all pure-time
deviations.

### Quick falsifiers and known failure mode

- The exact rowwise rigidity theorem for conditioned product purification
  supports the mechanism but does not imply the cross-time conjecture.
- A law separation is not a game counterexample.  Because the equilibrium
  target is free, the game may choose only `A`, only `B`, Never, or some other
  pure sure-exit outcome unless incentives force both desired atoms.
- Extra calibrator players can themselves quit and change the terminal
  coalition.  Their entire deviation menu must be included, not treated as an
  external auditor.
- A single exact independent-clock law with `a,b` both large and leakage small
  refutes the proposed inequality; a reward table with a stationary or
  sure-exit equilibrium refutes only the gadget, not the clock lemma.

## Ranked candidate 4: derandomize the universal sunspot construction

Classification: `ANALOGY` to chattering/relaxed-control purification;
`CONJECTURE` as an ordinary-equilibrium transfer.

### Why this could change the universal obligation

Normalized quitting games have paper-level sunspot approximate equilibria at
every accuracy.  In the hard Q-matrix branch, the Solan--Solan construction
has at most one quitter at a time.  That matters: exact multi-owner product
purification rigidity does not immediately obstruct a calendar that selects
one active owner.  A successful causal derandomization would import an
arbitrary-game producer rather than synthesize a new certificate from scratch.

The relevant external mathematics is purification of relaxed controls by
low-discrepancy chattering or rotor-router schedules.  A deterministic public
calendar can match signal frequencies on every interval, not only globally.
If the sunspot proof uses signals only through such interval occupations and
continuation values, a balanced rotor could replace them.

### First concrete lemma/test

Extract one finite-state `AtMostOneQuitter` sunspot controller from
`theorem2_13_sunspot`.  Replace each iid public label by a periodic balanced
word whose discrepancy on every interval is at most two.  Prove, or refute by
a pure quit-time deviation, a bound of the form

`ordinary terminal exploitability <= sunspot error + C * mesh`.

The first regression should be the Solan--Vieille boundary table: it has no
sufficiently accurate stationary equilibrium but does have a checked
ordinary period-two equilibrium.  Passing this test would show that calendar
predictability is not automatically fatal; it would not prove the universal
transfer.

### Quick falsifiers and known failure mode

- The public signal is observed before the live action.  A deterministic
  rotor reveals all future labels, so a player can time a deviation using
  information unavailable against iid signals.
- General autonomous/correlated constructions use private current
  recommendations and delayed public disclosure, not merely empirical signal
  frequencies.  A public lottery alone may be too weak.
- The repository's exact product-purification no-go kills any attempted
  one-row rescaling with two active quitters.  Chattering must stay genuinely
  single-owner or pay a quantified collision error.
- If one explicit Q-branch table has a fixed predictable-calendar deviation
  gain for every balanced word, the deterministic purification thesis should
  be abandoned rather than repaired with a larger block grammar.

## Recommended bet and kill criterion

### Recommendation

Bet first on **Candidate 1**, with Candidate 2 as its topological mirror.
This is not because a counterexample is more likely than a proof.  It is
because Simon's correspondence offers the rare thing missing from the current
conference work: a claimed theorem-level bridge from a finite-dimensional
global obstruction to all behavioral profiles.  It also aligns with the
repository's recorded expert heuristic that a counterexample, if real, likely
starts around six players and needs computation.

The research packet should have two independent workstreams:

1. repair/falsify the corrected Simon Theorem 3 necessity argument and write a
   clean adapter from its open-loop quit profiles to the project's terminal
   semantic endpoint; and
2. search sparse six-to-eight-player families for an exact strict Lyapunov
   certificate on one rational `F_epsilon` carrier, using the checked
   Solan--Vieille period-two table as a mandatory negative control.

This would be materially different from enumerating stationary faces, finite
blocks, singleton cycles, paid rows, atoms, or deadlines.  A success would
either produce an all-behavior counterexample route or force a recurrent
orbit whose structure can feed the positive side.

### Kill criterion

Kill the recommended route if either of the following occurs:

- the necessity implication
  `approximate equilibria -> arbitrarily large rational near-feasible
  F_epsilon orbits` is refuted, or cannot be repaired without an assumption
  absent from ordinary finite quitting games; or
- after a mathematically defined search class covering all sparse
  six-to-eight-player inspiration digraphs of the chosen type, every candidate
  is proved to have a nonconstant recurrent `F_epsilon` orbit or falls into a
  known positive stationary/instant class, so no strict Lyapunov certificate
  can exist in that class.

Do not kill it merely because one polynomial degree, one SOS relaxation, one
player count, or one parametrization fails.  Conversely, do not keep it alive
on numerical bounded variation alone: the deliverable is an exact global
inequality on the full correspondence plus the audited all-behavior bridge.

## Overall audit judgment

The user's concern is partly right.  The existing agents are not doing empty
mathematical tricks: Noether and Cedar state genuine conjecture-closing theses
and explicit kill criteria, and several local no-go results correctly prevent
false completeness claims.  But the realized portfolio is over-invested in
local interfaces and four-player architecture separations.  Those are
unlikely by themselves to decide the conjecture.

The missing strategic layer is a global normal form with an all-behavior
consumer.  Simon's orbit equivalence, if repaired, is the best such layer
visible in the inspected sources.  Independent-clock correlation inequalities
are the most concrete new counterexample mechanism if the Simon bridge fails.
The sunspot theorem is the most concrete positive source if predictable
calendar purification can survive adversarial timing.

## Feedback wanted

1. Can a reader independently repair or refute the survival-interval step in
   Simon 2007 Theorem 3's necessity direction?
2. Is the clock-tie inequality `ell^2 >= 4ab` true for arbitrary independent
   countable quit times?  If false, what is the sharp surviving inequality?
3. Which sparse six-to-eight-player reward family is the smallest honest test
   for a strict `F_epsilon` Lyapunov certificate after stationary and instant
   branches are excluded?
