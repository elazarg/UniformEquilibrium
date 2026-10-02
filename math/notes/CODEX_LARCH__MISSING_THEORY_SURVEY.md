# Missing-theory survey: finite observations, stability, and strategic repair

Author: CODEX_LARCH.

## Current best attempt

This is a bounded research audit and a proposed investigation order, dated
2026-09-07. It contains static inspection of Lean declarations, ordinary
mathematical deductions, and explicitly open research questions. No Lean
compilation, independent mathematical review, or export was performed here.

The strongest candidate is a theory of **finite observations of independent
stopping laws, with quantitative stability of their realizability
constraints**. Its immediate test is a power-law strengthening of pair-only
terminal-law rigidity. Sections 3–4 give a proof of existence of such a bound
using finite-observation compression and a classical semialgebraic inequality.
The exponent and constant are not computed. The prospective UE consumer
still needs an incentive argument.

Two harder extensions deserve bounded investigation: correcting prescribed
payoffs while retaining response caps (Section 5), and optimizing several
independent laws together after eliminating one law by the existing repair LP
(Section 6). Neither extension is proved here.

The user identifies `../multitubes/` as the large theory obtained by the
previous pass and considers its UE usefulness exhausted. This audit does not
investigate that project or recommend rebuilding its transport theory.

## 1. What was searched, and what was not

The question is whether accumulated local mathematics conceals a general
theory that simplifies several developments, supplies a genuinely missing
hypothesis, or changes a conjecture-facing obstruction. A theorem-shaped
restatement of UE existence does not qualify as progress.

At the inspected committed snapshot `11809f7`, `MathUE/`,
`UniformEquilibrium/`, and `Research/` contain 3,077 Lean files, occupying
48,645,904 source bytes. The older August mining checkpoint `5fa99bf` has
1,635 files and 26,682,983 bytes in these lanes. That checkpoint is a size
and consolidation comparison, **not an identification of the multitubes
pass**. There are 1,981 changed or added paths between those snapshots.
The working tree is being edited concurrently; these are committed-snapshot
measurements, not a frozen description of every current local file.

The compressed conference layer is itself substantial: at the initial
inventory, `math/formalized/` had 204 Markdown files and 87,032 lines;
`math/exports/` had five packets plus its README. The 799 top-level notebooks
had 363,945 lines. These counts are scoped audit evidence, not maintained
project status.

I used semantics and current questions to select routes, read the relevant
parts of the frontier/toolkit, inspected the export packets and selected
formalization records, and followed exact source declarations. Searches in
older notebooks were targeted falsification/overlap checks, not a full read
of the conference. `MERIDIAN_BLINDSPOTS.md` was particularly useful for
excluding already explored broad techniques.

The detailed sample is concentrated on recent stopping-law, payoff-calendar,
repair, premium/exclusion, and overlap results. Older probability and
occupation modules provide a control sample. General stochastic-game
semantics, the literature lane, and most Research families were not audited
exhaustively. An absence claim below means “not found in these targeted
searches,” not “absent everywhere.”

## 2. A cost-effective continuation protocol

Use **new mathematical interfaces**, not recent file timestamps, as the main
unit of search. Renames, generated files, and promotions can make an old
theory look new. Conversely, a new generic lemma can unlock an old consumer.

1. Make a local, disposable inventory of imports, public declaration
   statements, module abstracts, and file hashes. Do not feed proof bodies
   into the first pass. Use the umbrellas to identify production reachability.
2. Read the current-best-attempt blocks and formalizer coverage boundaries.
   For each candidate record the object, quantifiers, actual source,
   preserved observables, output, converse, and missing hypothesis.
3. Form clusters by those mathematical fields. Examples are “preserves a
   finite list of expectations,” “bounds all response suprema,” and “turns a
   vanishing residual into distance to an exact feasible set.” File-name
   similarity and import degree are navigation aids only.
4. Match outputs to hypotheses across clusters. Inspect the exact Lean
   statements at each proposed match, including the difference between one
   profile, a sequence, a closure point, and a selected suffix.
5. Before developing a candidate, search both negative notebooks and existing
   generic modules for the proposed implication. Several leads below were
   rejected at this stage.
6. Give a surviving candidate one bounded mathematical test: a proof,
   minimal exact counterexample, or a precise obstruction. Expand its source
   neighborhood only when that test requires it.

A sensible allocation is roughly half the reading effort on recent
interfaces, one quarter on their older dependencies/consumers, and one
quarter on excluded or unformalized attempts. This corrects the positive
selection bias of `formalized/` without reading all notebooks.

The next iteration should take one candidate at a time through proof and
falsification. Do not build a new large library on the strength of a
suggestive analogy. Stop when the putative theory merely reproduces an
existing interface, requires UE existence as its producer, or loses the
independent-strategy semantics needed by its consumer.

## 3. First candidate: independent-observation geometry

### Existing pieces that should be viewed together

- `exists_sparseFiniteStoppingLawMixture_wholePayoff_eq`
  (`UniformEquilibrium/Quitting/Paths/SparseWholePayoffFiniteMixture.lean`)
  reduces one mixture to at most the number of players plus one support
  actions, preserving the whole prescribed payoff vector.
- `quittingActualTerminalPayoffSet_eq_finiteCalendarPayoff` and
  `isCompact_quittingActualTerminalPayoffSet`
  (`UniformEquilibrium/Quitting/Paths/FiniteCalendarPayoffClosure.lean`)
  identify all actual prescribed payoffs with one fixed finite-calendar
  image. Response caps are not preserved.
- `canonicalOverlap_threshold_feasible_iff_twoSupported`
  (`MathUE/Probability/FiniteOverlapSparseCompression.lean`) preserves one
  overlap expectation and improves another on the supplied finite menu.
- `uniformSixPairTerminalLaw_noncharacterization`
  (`UniformEquilibrium/Quitting/Paths/PairOnlyTerminalLawRigidity.lean`)
  excludes a law that passes every two-pair square-root constraint.
- The unreviewed ordinary-math note
  [finite-calendar prescribed-outcome realization](CODEX_TARSKI_PREMIUM__FINITE_CALENDAR_PRESCRIBED_OUTCOME_REALIZATION.md)
  already states the finite-observable generalization and a full-law version.
  The reviewed export
  [finite-calendar reward-table tests](../exports/FINITE_CALENDAR_PAYOFF_EXCLUSION_RAW_TABLE_TESTS.md)
  contains the prescribed-payoff compression proof and its selector consumers.

The common object is a product of independent measures evaluated on a finite
vector of functions of the first quitting coalition. The output dimension
need not equal the number of players. Equality constraints and one optimized
linear observable lead to related sparse-support arguments.

This is established cubature mathematics, not a proposed new version of
Carathéodory. Bayer–Teichmann give finite positive representations of vector
expectations in [their proof of Tchakaloff's theorem](https://people.math.ethz.ch/~jteichma/tchakaloff120405.pdf).
The application here must compress coordinates successively against the
**current** other marginals; a convex mixture of entire profiles would
introduce unavailable correlation.

### Useful general statement

Let there be n independent clocks on the natural numbers plus Never. Let
g(S) be a vector of terminal-coalition observables whose range has affine
dimension d, counting the Never outcome. Every attainable expectation of g,
and every limit of such expectations, has an independent realization using
at most d+1 actions per player and at most n(d+1) finite dates.

Proof: truncate finite tails with arbitrarily small product-coupling error;
apply affine support reduction separately to each marginal, preserving the
entire vector each time; rank the union of occupied dates using one common
increasing map; take a limit in the resulting fixed finite product simplex.
The rank map preserves every tie and comparison among realized clocks.
This also proves compactness of the observable image. Its finite-calendar
parametrization is polynomial, so its image is semialgebraic by real
projection closure. These are ordinary-math arguments, not Lean checks here.

For four players and the six exact-pair probabilities, d is at most six.
Thus **28 finite dates plus Never suffice for the entire six-coordinate
image**, even when the original strategies have unbounded support. This
does not preserve every terminal outcome or any response cap.

The useful extraction is an observer-indexed product-expectation theory,
followed by a stopping-order adapter. The recently implemented payoff
theorem is one instance; the six-pair image and full-law image are others.
The generic dimension is the affine rank of the observations, not the player
count and not the number of dates in the original strategy.

### Why a larger theory is warranted

The six-pair feasible set is already known not to be characterized by its
two-coordinate inequalities. This is a higher-order constraint imposed by
independence. A useful theory should explain feasible support families,
boundary strata, and quantitative distance from impossible combinations.
It should produce inequalities consumed by game-specific incentive bounds.

The full six-coordinate problem was already proposed in
[MERIDIAN's audit](MERIDIAN_BLINDSPOTS.md). What has changed is the available
combination of exact rigidity, finite-observation realization, and polynomial
interfaces. The recommendation is to exploit that combination, not to
reannounce the original overlap conjecture, which has since been resolved.

## 4. First mathematical test: robust pair concentration

For an actual four-player profile let q_e be the probability of each of the
six pair coalitions. Define

    leakage(q) = 1 - sum_e q_e,
    spread(q)  = 1 - max_e q_e.

Leakage includes singleton, triple, full-coalition, and Never outcomes.
Both quantities are nonnegative. The exact source declaration
`exists_pair_terminalOutcomeMass_eq_one_of_terminalPairMass_eq_one`
(`UniformEquilibrium/Quitting/Paths/PairOnlyTerminalLawRigidity.lean`)
states that leakage zero forces spread zero.

**Ordinary-math deduction.** There are an integer N ≥ 1 and C > 0,
depending only on four-player clock geometry, such that every actual profile
satisfies

    spread(q)^N ≤ C * leakage(q).

Proof: use the 28-date realization from Section 3. On its compact product
simplex, each q_e is a polynomial. Leakage and spread are continuous
semialgebraic functions. Their zero sets satisfy the inclusion above.
The compact semialgebraic Łojasiewicz inequality therefore gives N and C;
the exact observable realization transports the same inequality to all
independent behavioral profiles. The needed form is stated explicitly in
[Basu–Mohammad-Nezhad](https://arxiv.org/abs/2211.10034).

This deduction has not been independently reviewed or formalized here.
It computes neither N nor C and makes no claim that its constants are sharp.
The bound is independent of rewards, calendar length, and Never mass.

Even without the semialgebraic theorem, compactness gives: for each ρ > 0,
there is δ > 0 such that leakage < δ implies spread < ρ. Otherwise a
convergent sequence of six-pair vectors contradicts exact rigidity.
This qualitative observation is **not credited as a new frontier result**:
the older zero-singleton closure theorem in
[its formalization packet](../formalized/ZERO_SINGLETON_BEHAVIORAL_LAW_PRODUCT_BASE_AND_SURE_CORE_DESCENT.md)
already provides a route to such compact-limit consequences.

The sharper research task is to find an explicit small exponent and useful
constant, preferably from a direct probabilistic proof. Failing that, choose
a fixed spread threshold, such as ρ = 1/4, and certify a positive minimum
leakage on the 28-date image. This is a finite polynomial problem, not a
bounded-calendar approximation to the strategy class.

### Exact UE interface

Suppose a reward-table argument supplies constants ρ,A > 0 such that every
profile with exploitability E below a fixed threshold has

    spread ≥ ρ,       leakage ≤ A * E.

The power bound then implies E ≥ ρ^N/(C*A) within that threshold; profiles
outside it already have its positive lower bound. This would produce a
full-behavior exploitability gap. **The reward-table argument is missing.**
The geometric theorem does not assert that any table forces these two
inequalities on the same profile.

For positive work, concentration can identify a near-pair outcome source,
but does not control its counterfactual caps. Outcome proximity alone must
not be used to infer that the profile is approximately Nash.

The existing `FinFourAllPairCrossingConsumer.lean` and
`PairMassForcingConsumer.lean` in `UniformEquilibrium/Quitting/Terminal/`
are relevant consumer neighborhoods; their supplied forcing premises must
be inspected before integrating a new inequality.

## 5. Second candidate: payoff-fiber recovery with response control

Exact finite payoff realization and approximate full-semantic realization
solve different problems. A third theorem would say when an approximate
realization of (u,b) can be corrected to have **exactly u**, with arbitrarily
little increase in any complete response cap.

Write K for the closure of actual semantic pairs. The open target is a
meaningful sufficient condition on (u,b) in K ensuring that, for every ε > 0,
some actual p satisfies

    U(p) = u,       B_i(p) ≤ b_i + ε for every i.

Do not presume this for every point of K. The first useful subproblem is a
correction on a fixed block of positive masses whose payoff directions have
a uniformly bounded right inverse. This supplies actual feasible changes,
not an arbitrary signed solution to a linearized moment equation.

A basic conditional estimate explains the desired bridge. Suppose q is an
approximate source with ||U(q)-u||∞ ≤ δ, and one can correct it to p with
U(p)=u and sum_i TV(p_i,q_i) ≤ Lδ. For rewards bounded by M, product coupling
gives

    |U_i(p)-U_i(q)| ≤ 2MLδ,
    |B_i(p)-B_i(q)| ≤ 2MLδ.

The second estimate holds uniformly for each fixed deviating law, since only
opponents matter, and hence survives taking the supremum. Thus payoff
correction retains an explicit cap budget. This conditional estimate is
elementary; **producing the correction and its uniform constant is the
mathematical issue**.

The prospective theory is constrained inverse-function/error-bound
mathematics for independent product expectations, with singular supports
classified separately. A compactness statement on each fixed calendar does
not provide a bound uniform as calendars grow. Likewise, generic
regularity of reward tables does not justify assuming a hypothetical
minimum source lies on a regular stratum.

First tests: a nonsingular finite support face; degeneration of one support
mass; and the geometric repair example with a nonattained law-space
infimum. Any useful sufficient condition must be shown present in an actual
unresolved source family. Otherwise it is another conditional adapter.

This revisits the older relaxation/recovery question with the newer exact
finite-observation machinery. It is the more direct UE-facing extension of
the first candidate, but currently has lower confidence than the law-only
stability result.

## 6. Third candidate: multilateral repair and its dual obstruction

`exists_objective_minimizer_eq_behavioral_infimum`
(`UniformEquilibrium/Quitting/Terminal/PivotRepairBehavioralInfimum.lean`)
identifies the compact finite repair LP value with the infimum over one
player's entire behavioral law against supplied finite opponent laws.
Its objective is the maximum of the affine constraints defined by
`QuittingPivotRepairLPInput.constraintGain`
(`UniformEquilibrium/Quitting/Terminal/PivotRepairFiniteLP.lean`).

This is stronger than computing that player's best response: it optimizes
the full game's exploitability while changing that one law. However,
`smallPivotRepairValue_iff_exists_uniformEquilibriumPayoff`
(`UniformEquilibrium/Quitting/Terminal/PivotRepairUniformPayoffCharacterization.lean`)
shows that asking for arbitrarily good outer sources is still a
conjecture-level characterization.

The obvious coordinate-descent producer has already been attacked. The
unreviewed ordinary-math notebook
[complete one-law repair trap](CODEX_HILBERT__FULL_EXPLOITABILITY_COORDINATE_REPAIR_TRAP.md)
gives an explicit positive-value family closed under every nonincreasing
one-law replacement, including neutral retiming, while a joint move improves
the value. Its status is not a Lean theorem, but it is a mandatory falsifier
before recommending alternating repair.

The serious next theory would retain the LP's dual response-test weights
and study their change when **two or more independent marginals** move.
One-law affine structure becomes multilinear interaction; replacing the
joint law by an arbitrary coupled law would solve a different problem.

First bounded test: on that trap, eliminate the pivot by its existing LP and
find the smallest simultaneous opponent variation that decreases the actual
full objective. Derive its mixed term and compare it with existing signed
response-square/curvature identities. Then test whether any proposed
two-law descent assertion fails on another exact finite table.

Only continue toward a general theory if this yields a reusable sufficient
condition, an interaction-rank obstruction, or a dual certificate retaining
the literal source. A new potential that merely assumes cross-player
recharge is bounded has not supplied the missing mathematics. No universal
pair-repair descent theorem is proposed as true here.

## 7. Smaller completion opportunities and rejected rediscoveries

### A real small completion: existence of phase occupations

`SwitchedPotentialCalculus.lean` in `MathUE/Probability/` says occupation
duality is missing, but `exists_optimal_phaseOccupation_and_phaseBias_of_feasible`
(`MathUE/Probability/PhaseOccupationDuality.lean`) already provides it.
The latter still takes nonemptiness of its phase occupation set as a premise.

For nonempty finite state and action sets, the premise has a short ordinary
proof. Choose one action at every phase and state. On the finite augmented
state space (phase,state), advance phase cyclically and apply that action's
kernel. Cesàro averages of iterated laws have a convergent subsequence in the
finite simplex; the invariance defect is the difference of the final and
initial laws divided by the averaging length, so tends to zero. The limit
is invariant. Put its mass on the chosen actions to obtain a phase occupation.
This removes the supplied-feasibility premise at this nonempty scope.

It does not establish attainability of that optimal recurrent class from
every prescribed initial state. State/action nonemptiness and a positive
period must be explicit. This is a small classical completion, not a new
large UE theory. No Lean implementation was attempted.

### Other leads excluded or demoted

| Proposed direction | Audit disposition |
| --- | --- |
| Another general directed-transport/cocycle library | Excluded by the user's multitubes guidance; extensive local transport theory also exists. |
| Generic phase-occupation strong duality | Already present; the old comment is not the current boundary. |
| General finite-observable cubature | Already stated in a notebook and classical; useful as a shared core, not a novelty claim. |
| Exact bounded-calendar preservation of full caps | Too strong: the STALL example cited in the realization notebook separates exact geometric equilibrium from every finite-calendar exact equilibrium. |
| Repeated optimal one-law repair | Explicit ordinary-math trap; investigate joint interaction instead. |
| Finite semialgebraic model of every response graph | The ordinary-math infinity-fiber universality example allows arbitrary compact fibers; retaining whole response graphs is a much stronger demand than retaining cap values. |
| Exact pairwise law inequalities as complete joint characterization | Refuted by `uniformSixPairTerminalLaw_noncharacterization`. |
| Zero-singleton laws collapse to a product base | Already covered by the zero-singleton formalization packet; do not repackage as new. |
| Quantifier elimination decides whether UE exists | Finite-scale formulas and certified approximation do not decide whether an infimum is exactly zero. QE is also active work in this workspace. |

The full-response-graph obstruction is documented in
[infinity-fiber universality](../ideas/CONTINUATION_GAME_STATE/INFINITY_FIBER_UNIVERSALITY.md).
It does not prove that the much smaller full-semantic carrier is
nonsemialgebraic. That distinction must survive any future survey.

## 8. Recommended next pass

1. **First:** develop the finite-observation core only far enough to expose
   the six-pair image, then seek a concrete quantitative leakage bound.
   Require a new inequality beyond pairwise projections and identify its
   exact incentive premise. This has the clearest new mathematical test.
2. **Second:** test payoff-fiber recovery on one actual family with a fixed
   correction block. Seek a uniform estimate or an exact failure at a
   singular support, before proposing a global recovery theorem.
3. **Third:** independently audit the one-law trap and use it to define the
   minimum useful multilateral repair problem. Do not launch generic
   coordinate descent as a conjecture attack.
4. **Small separate task:** close phase-occupation nonemptiness and correct
   the stale local duality boundary when implementing that completion.

The result of this pass is a ranked, falsifiable research program and one
ordinary-math power-bound deduction. It is not a claim to have found a
multitubes-sized completed theory, an all-codebase audit, or progress on the
sign of the unrestricted controller value.

## Verification of this record

`python scripts/check_docs.py` passed. A separate local check resolved this
note's Markdown links and explicit Lean file paths and checked the names of
seven central theorem declarations in their source files. `git diff --check`
passed for the tracked working-tree diff. These are documentation/static
checks, not compilation or independent validation of the mathematical
deductions. The conference directory is gitignored; this note is a local
research artifact. No Lean source or generated project input was changed by
this audit, and no commit was created.
