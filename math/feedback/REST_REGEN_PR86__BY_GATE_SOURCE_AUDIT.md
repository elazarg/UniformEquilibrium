# Source and freshness audit of `RESET_REGEN/RESPONSE.md` and PR #86

## Verdict

**FAIL as an export candidate and FAIL as a description of the current PR
surface.**

PR #86 contains one useful, genuinely new interface repair: it strengthens
`MaximalOneStepPaidResetRegeneration` so every inhabitant publicly carries the
canonical observer, conservative paid scalar, shifted pure-time witnesses,
coordinatewise debt scaling, total-debt scaling, and inherited-incidence
lower bound used inside the constructor.  This directly fixes the public-
record defect identified by the earlier `RESET_REGEN` reviews.

That repair is not a new consumer or conjecture-facing reduction.  The new
ray file mostly repackages already checked maximal-prefix identities around a
**supplied infinite ray**.  It does not construct the finite-stop/infinite-ray
alternative claimed in `RESPONSE.md`, it does not expose the claimed marked
causal atom theorem, and it supplies no finite rank, charged return, terminal
approximation, or contradiction.

There is also no checked Lean result at the PR head for the new ray file.  The
focused Lean job fails while compiling it, and the import-graph job fails
because the final PR commit removes its `Research.lean` import.  The modified
one-step module did compile before that failure.  Thus the one-step record
strengthening is the only validated new public surface in the PR branch; none
of PR #86 is merged into current `main`.

## Repository and PR identity

The supplied path is `../RESET_REGEN/RESPONSE.md`; no `../REST_REGEN/`
directory exists.  PR #86 is:

```text
title: Expose canonical paid/reset successor data and Zeno boundary
head:  research/paid-reset-canonical-zeno
head commit: 4349797df7b19b7ecccbef64941293df331ce57b
base: main
state: open
```

Its mathematical diff has exactly two files:

```text
Research/Quitting/PaidCapMaximalOneStepRegeneration.lean
Research/Quitting/PaidResetCanonicalZenoRay.lean
```

At the audited head, `Focused Lean` fails on
`PaidResetCanonicalZenoRay.lean`.  Two failures are proof/elaboration issues
in `futureAbsorption_tendsto_zero` and the Fin4 debt-coordinate theorem; the
same run reports an unnecessary-`simpa` linter error.  The separate import-
graph check fails because `PaidResetCanonicalZenoRay` is not reachable from
`Research.lean`.  The prior commit temporarily imported the file, but the PR
head deliberately removes that import.

## What the one-step change really exposes

The strengthened public record now adds the following fields to
`QuittingPaidCapLiftedSource.MaximalOneStepPaidResetRegeneration`:

```text
descendant_observer
descendant_gain
descendant_row_sourceWitness
descendant_row_receivingWitness
descendant_debt_coordinate
descendant_initialDebt
reset_incidence_lower
```

Together with the old `descendant_profile`, `descendant_minimum`, reset debt,
positive incidence, actual semantic/law carrier membership, and fixed-law
dispatch, these fields establish for an arbitrary record:

```text
descendant.profile = one literal maximal-root prefix of source.profile;
descendant.observer = source.observer;
descendant.gain = c * source.gain;
d_i(descendant) = c * d_i(source);
D(descendant) = c * D(source);
incidence(descendant) >= c * incidence(source),
```

where `c` is the joint all-Continue mass of the maximum-absorption exact root.
The two stored pure-time witnesses are shifted by exactly one date.

This is an honest and useful API improvement.  The equality for `gain` is an
equality for the deliberately chosen conservative certificate scalar, not an
identity for the entire physical pure-time payoff difference.  The latter is
transported by the observer's opponents-only survival, which can be larger
than `c`.  The PR's proof uses the correct inequality and then re-extracts a
paid row with certificate `c * source.gain`.

The one-step module's positive branch is an actual behavioral profile and its
root is exact Nash against the complete unrestricted behavioral cap.  It does
not replace that cap by a stationary or finite-horizon deviation class.

## What the new ray file actually states

The file defines

```text
CanonicalMaximalPositiveRay initial resetOwner other
```

as a structure whose fields already include:

```text
source : Nat -> QuittingPaidCapLiftedSource reward
step   : for every time, a positive one-step regeneration record
source_succ : source (time+1) = (step time).descendant
initial zero reset debt and positive aggregate incidence.
```

In other words, it **consumes a supplied coherent infinite positive branch**.
It does not produce one.  From that supplied structure it proves wrappers for:

- equality with the existing profile-indexed maximal-prefix chronology;
- exact total and coordinate debt products;
- exact conservative paid-certificate products;
- lower transport of aggregate incidence;
- uniform survival, paid, and incidence floors from the positive global
  minimum;
- invariance of positive-debt support and normalized debt;
- summability of the canonical absorption sequence; and
- Fin4 separation of the descendants from small terminal Nash error.

The file attempts, but at the audited PR head does not successfully compile,
the vanishing future-absorption tail and Fin4 coordinate-debt theorems.

There is no declaration named

```text
QuittingPaidResetInfiniteRay
finiteStop_or_nonempty_infiniteRay
stageMass_eq_reach_mul
```

in PR #86, current `main`, or the other searched remote branches.  These names
in `RESPONSE.md` are not descriptions of checked declarations.

Mathematically, a finite-stop-or-infinite-choice alternative can be obtained
classically from the one-step disjunction, after fixing coherent choices.
PR #86 does not state or prove it.  Moreover, the complete regeneration
record is not literally unique: row proof data, returned reset point, and
dispatch can vary.  The actual profile, cap-selected root, observer,
certificate scalar, and displayed semantic/law quantities are canonical
enough for the scalar ray account, but this distinction should be stated.

## Exact duplication with existing checked results

The scalar and causal ray content predates PR #86.

`Research/Quitting/MaximalCapSemanticPrefixOrbit.lean` already proves:

- `quittingTerminalSemanticDebt_maximalCapSemanticPrefixOrbit_eq` and
  `quittingTerminalSemanticDebtSum_maximalCapSemanticPrefixOrbit_eq`;
- `minimumDebt_div_sourceDebt_le_maximalCapSemanticPrefixSurvival`;
- `quittingMaximalCapSemanticPrefixOrbit_positiveDebtSupport_eq`;
- `quittingTerminalSemanticDebt_normalized_maximalCapSemanticPrefixOrbit_eq`;
- `quittingMaximalCapPrefixProfile_eq_semanticPrefixProfile`; and
- `quittingStageCoalitionMass_maximalCapSemanticPrefixProfile_add`.

These give the exact debt products, positive survival floor, invariant debt
support, invariant normalized debt, literal actual-profile realization, and
exact transport of every independently supplied marked suffix atom.

`Research/Quitting/MaximalCapSemanticPrefixReturn.lean` already proves, for
the positive-minimum maximal ray:

- `weightedAbsorption_hasSum`;
- `summable_absorption`;
- `absorptionTailSum_tendsto_zero`;
- `finiteAbsorptionTail_le_tailSup`; and
- `absorptionTailSup_tendsto_zero`.

Thus the new file's absorption summability and late-tail conclusion are
wrappers around existing theorems, not a new boundary.

`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/
PaidCapLiftedSummablePort.lean` already supplies the general paid cap-lifted
orbit, exact opponents-only pure-time transport, uniformly retained shifted
paid rows, and absorption summability.  The maximum-root selection matters for
the selector-independent unique-all-Continue alternative, but not for the
basic noncollapse calculation.

The combined normal form is already recorded in:

- `formalized/FIN4_FORCED_PAIR_MAXIMAL_PREFIX_RAY_DICHOTOMY.md`; and
- `notes/CHATGPT_EXTERNAL__NONCOLLAPSING_MAXIMAL_PAID_RESET_ORBIT.md`.

The latter already states the finite unique-cap versus infinite literal
paid/reset orbit, uniform paid and inherited-atom floors, summable absorption,
and fresh fixed-law dispatch at each finite stage.  PR #86 makes part of this
easier to refer to through a dependent Lean record, but does not add its
missing consumer.

## Marked atom versus aggregate incidence

The PR ray structure records only

```text
resetIncidence time
```

and proves an inherited lower bound for that aggregate terminal-law
functional.  It does not select a coalition or a date.

If an initial actual marked atom `(stage, coalition)` is independently
supplied, then `source_profile_eq` together with the already checked
`quittingStageCoalitionMass_maximalCapSemanticPrefixProfile_add` gives exact
mass `survival(n) * initialMass` at shifted date `n + stage`.  This is valid,
but it is old generic transport mathematics and is not packaged by PR #86.
The response's statement that the PR checks this marked transport is therefore
incorrect.  Positive aggregate incidence can select a positive finite law
coordinate and then a positive date by elementary countable additivity, but
that selection also is not a declaration in the PR.

The distinction is semantically important: aggregate incidence may receive
fresh prefix contributions, whereas the inherited contribution of one fixed
suffix atom is multiplied exactly by survival.

## Ordinary mathematics in `RESPONSE.md` but absent from PR #86

The following calculations are valid for a supplied coherent ray, subject to
the stated reward bound, but are not declarations in the PR:

- finite-stop versus infinite-ray production;
- marked coalition/date selection and exact shifted marked mass;
- the law recursion and its `L1` Cauchy estimate;
- the prescribed-payoff `L-infinity` Cauchy estimate; and
- the unrestricted-cap Cauchy estimate obtained from `B=U+d` and exact debt
  scaling.

These statements remain all-behavior statements because `B` is the complete
behavioral best-response envelope.  They do not imply that the limiting
semantic/law point is attained by one behavioral profile.  They also do not
make the fixed-law reset dispatch into an executable post-absorption restart.

## Consumer and maintained-question audit

PR #86 does not answer or strictly narrow
`questions/FIN4_PAID_RESET_REGENERATION_RANK.md`.  That question explicitly
rejects the one-step regeneration, a decreasing real debt, and an infinite
source chain without a finite rank or positive charged return.  The PR proves
that support and normalized debt remain constant, but those facts were
already known for the maximal semantic ray.

It also does not answer:

- `PAID_ADMISSIBLE_PAYOFF_NEAR_RETURN.md`: every sufficiently late block of
  the canonical ray has vanishing rather than fixed positive absorption;
- `FIN4_DOUBLE_UNIQUE_CAP_CLOSURE.md`: the finite stopping arm is precisely
  the unconsumed unique-all-Continue obstruction; or
- `FIN4_HARD_RESIDUAL_SEMANTIC_CLOSURE.md`: neither branch is closed.

Every finite step does retain a fresh `QuittingFixedLawResetDispatch`, but
that object is a semantic fixed-law return.  PR #86 proves no Nash--Bellman or
punishment-floor chronology from the descendant into the returned point.
Consequently the reset does not replenish admissible charge.

## Exact useful novelty

The only nonduplicated, validated contribution is the strengthened one-step
record.  It turns facts formerly hidden inside one existential constructor
into stable fields available to arbitrary downstream consumers.  This is
worth integrating after ordinary code review because it prevents future
proofs from silently choosing a weaker descendant annotation.

It is an interface completion, not mathematical completion of the
regeneration question.  The conditional ray structure is also a reasonable
organizational wrapper once its Lean errors and import path are fixed, but its
theorems do not change the conjecture-facing boundary.

## Required corrections

1. Replace `QuittingPaidResetInfiniteRay` by the actual structure name
   `CanonicalMaximalPositiveRay`, or add and check the claimed producer.
2. Remove the assertion that `finiteStop_or_nonempty_infiniteRay` is checked,
   unless that theorem is actually added.
3. Attribute marked-stage transport to the existing maximal-prefix theorem
   and say it requires a separately supplied/selected initial atom.
4. Separate checked declarations from the valid but unformalized Cauchy
   estimates.
5. Do not call `PaidResetCanonicalZenoRay.lean` checked until it compiles and
   is reachable from the Research umbrella.
6. Keep the conclusion conditional: canonical Zeno normalization does not
   produce a charged return, a rank, terminal approximants, or a positive-gap
   counterexample.

## Disposition

Do not export `RESPONSE.md` or PR #86 as mathematical progress through the
current gate.  Retain the Zeno description under `notes/` by consolidating it
with the existing reviewed noncollapsing-orbit note.  The one-step public-
record strengthening can be merged independently after its branch passes the
normal Lean and import checks.  Export becomes appropriate only after a
consumer renews fixed positive charge, a genuine finite rank or terminal exit
is produced, the infinite/unique-cap obstruction is eliminated, or a complete
positive-gap table realizes it.
