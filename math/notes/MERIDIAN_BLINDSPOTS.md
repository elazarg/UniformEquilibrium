# MERIDIAN — adversarial Fin4 blind-spot audit

Author: `MERIDIAN`

Status: **one genuinely underexplored negative-law question; otherwise the
global route space inspected here is well covered.**  This notebook contains
ordinary mathematics, conjectures, and experiments only.  Nothing here is
Lean-checked, and no counterexample or universal producer is claimed.

The one route I could not match to existing work is the geometry of
**overlapping** first-quitter coalitions.  The conference has sharp clock laws
for disjoint coalitions, especially the two complementary pairs of `Fin 4`,
but I found no corresponding law for two pair events sharing a player, nor a
description of the six pair-event coordinates as one `K_4`-indexed feasible
set.  Section 4 gives a precise first conjecture, exact boundary examples, a
failed proof attempt, and a finite falsification program.

Everything else tested below either is a true semantic fact rather than a
hidden assumption, or already has an explicit theorem, obstruction, or
notebook.  In particular, plain quit-time compactification, Reny
better-reply security, finite-deadline Nash selection, invariant means,
degree, reward genericity, Möbius coordinates, public-correlation
purification, alternative debt weights, and projective/quantile clock
compactifications should not be advertised as new routes.

The next concrete question is:

> For independent `T_0,T_1,T_2` in `Nat union {Never}`, is
> `sqrt(a)+sqrt(b) <= 1`, where
> `a=P(T_0=T_1<T_2 and T_0 is finite)` and
> `b=P(T_0=T_2<T_1 and T_0 is finite)`?

The finite-minimum clause excludes only an all-`Never` tie.  The third clock
may equal `Never` in either event.

## 1. Self-contained audit question

Fix a reward table

```text
r : {S : Finset (Fin 4) // S.Nonempty} -> (Fin 4 -> Real).
```

Before absorption there is one public live history at every date.  An
ordinary behavioral profile is therefore equivalent, for terminal payoffs
and every unilateral behavioral replacement, to four **independent** planned
quit times

```text
T_i in Nat union {Never}.
```

If their finite minimum is `t`, the terminal coalition is the set of players
whose clock equals `t`; if every clock is `Never`, the payoff is zero.  For a
profile `sigma`, write `U_i(sigma)` for prescribed terminal payoff,
`B_i(sigma)` for the supremum after an arbitrary complete behavioral
replacement, and

```text
E_r(sigma) = max_i (B_i(sigma)-U_i(sigma)).
```

The exact positive endpoint asks for profiles with `E_r` arbitrarily small.
The exact negative endpoint asks for one `gamma>0` such that every behavioral
profile has `E_r >= gamma`.

This audit asked whether the conference has systematically excluded a route
by assuming a fixed semantic state, source ancestry, pure-time responses,
product roots, the maximum/minimum-debt objective, one chronology
orientation, one compactness topology, or a non-Fin4 argument.  A candidate
counted as new only if a narrow phrase/symbol search did not find its
mathematical content elsewhere.

## 2. Sources and declarations inspected

I first read `SOURCES.md`, `GOAL.md`, the conference filenames,
`docs/FRONTIER.md`, and `docs/TOOLKIT.md`, followed by the two project research
method documents.  I then used the following narrow source interfaces.

- `quittingUniformEquilibriumPayoffConjecture` in
  `UniformEquilibrium/Quitting/Conjecture/Basic.lean` states the open target.
- `quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
  in
  `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`
  is the exact target-free positive endpoint.
- `not_exists_uniformEquilibriumPayoff_iff_exists_terminalExploitabilityGap`
  in `UniformEquilibrium/Quitting/Terminal/ExploitabilityGap.lean` is the
  exact negative endpoint.
- `sSup_range_quittingTerminalPayoff_update_eq_pureTime` in
  `UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean` makes
  deterministic finite quit times plus `Never` an exact best-response class.
- `quittingControllerTesterValue_eq_minimum_rawMaximumDebt` and
  `quittingControllerTesterValue_eq_zero_iff_exists_uniformEquilibriumPayoff`
  in the controller--tester subtree identify the scalar semantic value with
  the conjecture.
- `terminalSemanticCarrier_eq_closure_neverGeneratedSemanticReachable` and
  `nonempty_closedInvariantBarrier_iff_le_controllerTesterValue` identify the
  exact reachable carrier and its barrier dual.

Architecture files inspected were `MARKOV_COMPLETE.md`,
`SUFFICIENT_STATE.md`, `STATE_TOPOLOGIES_AND_APPROXIMATION.md`,
`SUFFIX_INFORMATION_OBSTRUCTION.md`, `VANISHING_REACH_SUFFIX_NO_GO.md`,
`RECURRENCE_ARCHITECTURE_OBSTRUCTION.md`, `FIN4_NEUTRAL_CHRONOLOGY.md`,
`CONTROLLER_VS_TESTER.md`, `FINITE_WINDOW_SEMANTIC_VALUE.md`,
`SEMANTIC_BARRIER_DUALITY.md`, `DECIDE_CONTROLLER_TESTER.md`,
`EXECUTABLE_COMPACT_STATE.md`, `EXECUTABLE_COMPLETE.md`, `GRAMMAR.md`,
`ADAPTERS_COMPLETE.md`, `TESTER_LEDGER_AND_FLOW.md`, and
`CHRONOLOGICAL_OCCUPATION_DUALITY.md`.

I read all currently listed questions, with special attention to the direct
decision, controller--tester duality, escape-aware search, approximate
forward-packet/bounded-capacity, paid-port, all-summable exact-spine,
cardinality, and reverse-AGKRS questions.

The closest conference work inspected was:

- `CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION.md`;
- `CODEX_CEDAR__STOPPING_TIME_COMPACT_GAME.md`;
- `CODEX_SPINOZA__FINITE_TESTER_SEPARATION_AND_TWO_ESCAPE_BOUNDARY.md`;
- `CODEX_EULER__ESCAPE_AWARE_QUANTILE_CLOCK_SEMIALGEBRAIC_HIERARCHY.md`;
- `CODEX_CEDAR__ERGODIC_NASH_BELLMAN_RECURRENCE.md`;
- `CODEX_CEDAR__DISCOUNTED_RADIAL_DEBIASING.md`;
- `CODEX_GAUSS__CURL_FREE_TOGGLE_POTENTIAL.md`;
- `CODEX_CEDAR__INDEPENDENT_CLOCK_TOGGLE_GADGET.md`;
- `CODEX_CEDAR__TWO_PAIR_CLOCK_RIGIDITY_COMPILER.md`;
- `CODEX_GROTHENDIECK__BLINDSPOT_AUDIT.md`;
- `CODEX_BLINDSPOT__FIN4_GLOBAL_ROUTE_AUDIT.md`;
- `PAIRED_HULL_REVIEW__FIN4_PROGRAM_BLINDSPOTS_AND_DECISIVE_TESTS.md`;
- `CODEX_ROOT__GENERIC_REWARD_REDUCTION_FOR_FIN4.md`;
- `CODEX_HAHN__WEIGHTED_DEBT_AFFINE_BARRIER_NOGO.md`; and
- the Boolean--Möbius files named by
  `UniformEquilibrium/Quitting/Bellman/Finite/BooleanMobiusAdapter.lean` and
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticNashDefectMobiusIncidence.lean`.

The local literature inspected or traced through faithful transcriptions was
Simon 2007 and 2012, Solan 2001, Solan--Vieille 2001, Solan--Solan 2020, and
the 2024/2026 absorption-path papers.  I did not use a literature theorem in
the new conjecture below.

## 3. Hidden-assumption audit

### 3.1 Fixed semantic state and source ancestry

This is a genuine concentration of the current producer program, but not an
assumption of the conjecture or its semantic endpoints.  The terminal timing
normal form and any universal clock-law inequality quantify directly over
whole actual profiles, so they bypass source regeneration completely.

The limitation is already understood: a semantic point or cap witness need
not retain a common stopping-law source, and a suffix at zero reach has an
arbitrary fibre.  `SUFFICIENT_STATE.md`, `VANISHING_REACH_SUFFIX_NO_GO.md`,
and the source-preserving packet notes make this explicit.  Rephrasing the
same construction with a larger fixed semantic tuple is not a new route.

### 3.2 Pure-time parametrization

This is not a questionable restriction.  The named pure-time extremality
theorem identifies the supremum over all behavioral replacements exactly.
Any terminal proof may test deterministic finite dates and `Never` without
losing deviations.  What is noncompact is the **family** of dates, not the
purity reduction.

### 3.3 Product roots and independent clocks

These are also exact for the base game.  Conditional on the unique live
history, private behavioral coins give a product Bernoulli root at every
date; equivalently the four complete planned quit times are independent.
Allowing a public correlating signal changes the game.  The public-sunspot and
purification notebooks already track that agency distinction.

The underused issue is not whether product structure is optional, but what
**global algebraic inequalities** it imposes on first-coalition laws across
all dates.

### 3.4 Maximum debt and positive-minimum contact

The scalar maximum debt is an exact zero detector: its infimum vanishes if
and only if terminal approximate Nash profiles exist at every error.  Thus it
does not lose the target at the semantic level.  The stronger practice of
working at a positive attained minimum and differentiating one active face is
an architectural choice.  Weighted debt, affine barriers, lexicographic
ranks, social surplus, and finite-clock KKT conditions have all been tried.
Changing the norm alone cannot repair chronology or source provenance.

### 3.5 Chronology orientation

This is the principal real seam.  Root prefixing evaluates backward from a
tail, while a proposed execution must install roots in forward calendar
order.  A horizontal cycle or invariant occupation in a semantic relation is
not automatically a chronological strategy.

A law inequality on independent complete clocks bypasses this seam: it holds
after an arbitrary chronology has already been executed.  This is why the
surviving angle below is materially different from another paid-port or
cap-clock producer.

### 3.6 Compactness topology

Plain weak compactness on `Nat union {Never}` loses the relative order of
clocks escaping jointly.  The exact two-player graph-limit example in
`CODEX_CEDAR__STOPPING_TIME_COMPACT_GAME.md` kills direct Reny
better-reply security.  Operational total variation retains the needed
suffix tests but is noncompact; pointwise/program topologies are compact only
at fixed depth.  Quantile compression, split Late/Never states, absorption
clocks, projective transforms, and multiscale bubbles are already developed.

The conclusion is not that every topology is impossible.  It is that
“choose a better compactification” is not a new idea unless it comes with a
specific continuous complete tester family and an actual reconstruction
theorem.

### 3.7 Fin4 specificity

Many current arguments are cardinal-independent until a deletion or
pigeonhole step.  Exact deletion cannot leave a positive gap on at most three
players because the two- and three-player cases are checked.  The conference
does exploit complementary pairs and the six pair rows, but the searches
`overlapping clock`, `overlapping tie`, `Finner`, `Brascamp`, `MTP2`, `total
positivity`, and `competing risks` found no clock-law treatment of the
adjacent edges of `K_4`.

That is the one credible Fin4-specific representational gap found here.

## 4. Surviving angle: the overlapping-pair clock cone

### 4.1 Known law versus untested law

For four independent clocks, existing ordinary mathematics proves the sharp
complementary-pair inequality.  If

```text
a = P(T_1=T_2<min(T_3,T_4), with finite minimum),
b = P(T_3=T_4<min(T_1,T_2), with finite minimum),
ell = 1-a-b,
```

then

```text
sqrt(a)+sqrt(b) <= 1,
ell^2 >= 4*a*b.
```

The same notebook proves the disjoint equal-rank generalization.  I
independently rediscovered the pair inequality and rejected it as novelty
after finding Propositions 17--19 of
`CODEX_GAUSS__CURL_FREE_TOGGLE_POTENTIAL.md`.

Now take three independent clocks and two **overlapping** exact-pair events:

```text
A = {T_0=T_1<T_2, with finite minimum},
B = {T_0=T_2<T_1, with finite minimum},
a = P(A),  b = P(B).
```

The following is the smallest unlocated claim.

### Conjecture 4.1 (overlapping-pair square-root law)

Every three independent countable quit-time law satisfies

```text
sqrt(a)+sqrt(b) <= 1.                              (OP)
```

If true, (OP) immediately applies to any two incomparable first-quitter
coalitions sharing a player: choose one player in the intersection and one
exclusive player from each coalition, then drop all the other requirements
from the two events.

This is a **conjecture**, not a proved lemma.  It is false neither by the
standard one-date nor by the simplest staggered-time tests, but the backward
induction used for disjoint pairs does not prove it.

### 4.2 Exact one-date test

Suppose the only finite date is zero and put

```text
x_i = P(T_i=0).
```

Then

```text
a=x_0*x_1*(1-x_2),
b=x_0*x_2*(1-x_1).
```

Therefore

```text
sqrt(a)+sqrt(b)
= sqrt(x_0) *
  (sqrt(x_1)*sqrt(1-x_2)+sqrt(x_2)*sqrt(1-x_1))
<= sqrt(x_0)
<= 1,
```

where the first inequality is Cauchy--Schwarz applied to the two unit
vectors

```text
(sqrt(x_1),sqrt(1-x_1)),
(sqrt(1-x_2),sqrt(x_2)).
```

Thus (OP) is exact in the one-date game.

### 4.3 Exact multitime equality family

The constant one cannot be improved.  Fix `p in [0,1]` and use dates zero and
one:

```text
T_0 = 0 with probability p, and 1 with probability 1-p;
T_1 = 0 with probability p, and Never with probability 1-p;
T_2 = 1 surely.
```

Independence gives

```text
a=p^2,
b=(1-p)^2,
sqrt(a)+sqrt(b)=1.
```

This test matters: equality can use two different calendar dates, so a proof
cannot reduce the law to a one-stage product calculation.

### 4.4 Exact failure of the obvious backward induction

At one live date with all three hazards equal to `1/2`, the immediate masses
of `A`, `B`, and joint continuation are each `1/8`.  The local estimate used
for disjoint pairs would need

```text
sqrt(A_0)+sqrt(B_0)+sqrt(C_0) <= 1,
```

but its left side is

```text
3/sqrt(8) > 1.
```

For the stationary repetition of this same row, however,

```text
a=b=(1/8)/(1-1/8)=1/7,
sqrt(a)+sqrt(b)=2/sqrt(7)<1.
```

So (OP), if true, needs an invariant retaining more state than the two future
event probabilities.  The overlap player carries a renewal budget invisible
to the disjoint-pair proof.

### 4.5 Experiments, not evidence of proof

Two finite numerical tests were run locally.

1. For each of `K=2,3,4,6,10` finite dates plus `Never`, 40,000 independent
   random triples of marginal laws produced no value above `0.993`.
2. Coordinate ascent was then performed over the three marginal simplices.
   For fixed other marginals the objective depends on a marginal through two
   linear forms, so a Pareto-boundary optimizer can be searched on two-point
   supports.  Across the same values of `K`, the search repeatedly reached
   numerical value `1` and never exceeded it.

These are only falsification attempts.  They do not address arbitrary
support, prove global optimality of coordinate ascent, or justify rounding.

### 4.6 Why the full `K_4` law is the real target

One inequality involving three clocks cannot by itself refute a Fin4 game:
the three-player existence theorem is a warning that any incentive gadget
using only those players has an escape.  The serious object is the vector

```text
(q_12,q_13,q_14,q_23,q_24,q_34),
```

where `q_ij` is the probability that `{i,j}` is exactly the finite
first-quitter coalition.

The three perfect matchings of `K_4` give the already known disjoint-pair
inequalities.  Its twelve adjacent edge pairs would receive (OP)-type
inequalities.  More important than those pairwise projections may be a
three-edge star or four-edge cycle inequality.  These constraints are
reward-independent and quantify over every behavioral profile, so a reward
table whose pure-time Nash inequalities force an infeasible region would
give a literal all-behavior exploitability gap.

This should be treated as an algebraic-statistics/competing-risks problem:
characterize the image, or merely a separating inequality, of independent
ordered clocks under the “exact first coalition” map.  It is not the same as
the existing quantile semialgebraic hierarchy, which approximates the entire
semantic carrier for a fixed reward table but does not isolate a
reward-independent `K_4` pair-law cone.

### 4.7 Falsifiable next tests

The route should proceed in this order.

1. Prove or refute (OP) for laws supported on two finite dates plus `Never`.
   This is a small exact polynomial inequality and the equality family above
   shows the sharp boundary.
2. Find a one-step Bellman invariant with enough extra state to propagate
   (OP), or exhibit a three-date rational counterexample.  Do not infer the
   infinite law from the failed scalar induction.
3. Enumerate low-degree symmetric polynomial inequalities for the six
   `K_4` pair masses on supports of two and three dates.  Validate candidates
   exactly, not only by floating optimization.
4. Only after a nontrivial law inequality survives, ask for one rational
   four-player reward table whose deterministic-time deviation inequalities
   force its violation.  Pure sure-exit, stationary, and known period-two
   equilibria are mandatory escape tests.

Kill this route if (OP) has a rational three-date counterexample and exact
elimination on two/three-date `K_4` laws produces no inequality stronger than
probability simplex constraints plus the already known matching inequalities.
Do not kill it merely because a first reward gadget has a pure-pair escape.

## 5. Routes tested and rejected as new

### 5.1 Plain compact discontinuous-game existence

The quit-time normal form on the one-point compactification has a single pure
payoff singularity at joint `Never`, but it is not universally
better-reply secure.  The exact two-player table in
`CODEX_CEDAR__STOPPING_TIME_COMPACT_GAME.md` has finite-date Nash profiles
converging to non-Nash all-`Never` while their graph payoffs converge to a
coordinatewise reward maximum.  No Reny-style theorem based on that topology
can be invoked directly.

### 5.2 Coercive selection among finite-deadline equilibria

Selecting the earliest, most absorbing, proper, or otherwise refined finite
timing equilibrium is initially attractive because it rejects the artificial
sequence in which an available equilibrium is merely shifted from date `n`
to `n+1`.

It is not a universal route.  Proposition 9 of
`CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION.md` gives a solved two-player table
whose finite-deadline timing game has a **unique** Nash equilibrium at every
deadline and whose unrestricted debt stays at least `1/2`.  Dummy padding
preserves the obstruction in the open cardinal range.  Thus no refinement of
the exact finite-deadline Nash set can choose a good branch there.  The needed
repair is already the diffuse refusal boundary, not a missing selection rule.

### 5.3 Finitely additive or invariant-mean timing equilibria

This changes countable additivity or produces an occupation object whose
actuality still needs proof.  The project already has Banach-limit machinery
and an invariant-mean Nash--Bellman audit.  Positive invariant charge is
already consumed; under a positive debt barrier all invariant measures may
sit on phantom all-Continue loops.  A finitely additive equilibrium without a
tightness-or-reconstruction theorem only renames the boundary.

### 5.4 Degree, genericity, and alternative scalar objectives

Static Brouwer/Sperner degree can escape to the Late boundary.  Generic reward
reduction is already explicit: the value is Lipschitz in the reward table, so
dense general-position existence would suffice and counterexamples form an
open set.  Weighted affine debt, social weights, lexicographic ranks, KKT
contact cones, and equilibrium index have all been investigated.  None
changes the all-behavior endpoint without a chronological or reconstruction
lemma.

### 5.5 Boolean Fourier/Möbius decomposition

The special complement geometry of the `Fin 4` coalition lattice initially
looked neglected.  It is not.  Boolean--Möbius endpoint differences,
cardinality grades, incidence charges, and pair-base completions already
occur in checked source and multiple notebooks.  A new Fourier basis without
a sign or recurrence theorem would be coordinate renaming.

### 5.6 Online learning and convexified controller mixtures

No-regret dynamics naturally produce coarse correlated distributions over
profiles, not an independent product profile that is Nash against
schedule-adapted pure times.  Convexifying the controller side of the
controller--tester game has the same issue.  The finite-watchdog theorem
already supplies actual profiles safe against any fixed finite tester menu;
the exact obstruction is that positive-gap witnesses escape every such menu.
A proposed rank-one/product rounding theorem would need a zero-level
preservation result for arbitrary signed reward tables.  No structural reason
for that result survived the audit, and public or latent common randomization
would change the agency model.

### 5.7 Regular variation and projective transforms

Generating functions, regularly varying tails, or a blow-up of joint
`Never` could be useful coordinates, but this territory is already occupied
by projective clock transforms, quantile compression, split Late/Never
states, absorption paths, Puiseux germs, and multiscale bubble proposals.
Such a transform becomes new only when it reconstructs every pure-time
obstacle and an actual product law.

## 6. Ranking

| Rank | Candidate | Plausibility | Bypasses horizontal/temporal seam? | Concrete next test |
|---:|---|---|---|---|
| 1 | Overlapping-pair square-root law and the full `K_4` pair-event cone | Medium | Yes: it is a law of already executed arbitrary clocks | Prove/refute (OP) on two finite dates plus `Never`, then three dates |
| 2 | Reward-independent low-degree separation of the six pair-event coordinates | Medium-low until Rank 1 survives | Yes | Exact elimination/SOS search on two- and three-date supports; regress against all known pair and stationary equality families |
| 3 | Rank-one zero-level rounding from a convexified controller--tester certificate | Low | Potentially | First state a precise rounding implication and test it on two-date signed tables; abandon on one positive relaxed/actual gap |

The first two ranks are one research program at different levels: Rank 1 is a
sharp hand lemma; Rank 2 is the finite algebraic discovery mechanism.  Rank 3
is retained only because it would attack the endpoint globally.  It currently
has less support than the existing APS, Simon, KKT, and source-packet routes.

## 7. Overall conclusion

The conference is not broadly trapped by the listed hidden assumptions.
Most are either exact features of quitting-game semantics or have already
been attacked with the appropriate relaxation and an explicit no-go.  The
dominant unresolved seam—source-faithful chronology versus horizontal
semantic motion—is real and repeatedly rediscovered, not an artifact of the
maximum-debt language.

The only substantive representational omission found in this audit is that
independent-clock work jumps from one complementary-pair inequality directly
to reward gadgets, without first studying the complete `K_4` overlap
geometry.  This omission is narrow but worthwhile: a successful inequality
would bypass the chronology seam entirely and a rational violation forced by
Nash inequalities would be an all-behavior counterexample, not a
strategy-class screen.  Conversely, a small rational counterexample to (OP)
would cheaply close the most concrete new branch identified here.
