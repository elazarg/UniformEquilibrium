# Review of `FIN4_COUNTEREXAMPLE_DOSSIER`

Reviewer: `CODEX_ROOT`

Status: useful consolidation requiring substantive correction before it can
serve as the current reference dossier.

## Claim reviewed

The dossier aims to give a self-contained and status-labelled description of
all presently known necessary conditions on a four-player quitting-game
counterexample, to separate the finitely checkable table geometry from the
dynamic residual, and to identify the exact remaining alternatives.

I checked the relevant claims narrowly against:

- `Quitting/Bellman/Finite/NashBellmanClockReduction.lean`;
- `Quitting/Classification/Existence/NormalUniquePersistentNashBellmanSpine.lean`;
- `Diagnostics/Quitting/Collision/SingletonPacket/FullSupportHardNashBellmanSpine.lean`;
- `Quitting/Bellman/Finite/UnboundedExactBlockHazardCapacity.lean`;
- `Diagnostics/Quitting/FinFourUnboundedExactBlockHazardCapacity.lean`;
- `Quitting/Bellman/Finite/AllContinueBasinRigidity.lean`;
- `Quitting/Examples/SolanVieilleBoundaryTable.lean`;
- `Quitting/Examples/BlockPair/FourPlayerPairedSingletonResidualHard.lean`;
- the checked Research declarations recorded in
  `formalized/FIN4_SOURCE_PRESERVING_COMPLETION_ATLAS.md`; and
- the reviewed saturation theorem
  `exports/LAW_TIGHT_CAP_NASH_SATURATION_HULL.md`.

## What is solid

The following central pieces are correctly stated or have only presentational
issues.

1. The terminal positive and negative reductions, the debt equivalence, the
   compact terminal-semantic carrier, literal finite-clock density, passive
   padding, and the rational semidecision route are faithful to checked
   results.
2. The zero-diagonal two-player LCP classification and the five-regime gate
   are correct.  The hard-residual packet really does provide the full normal
   core, punishment normality, the full-support singleton packet, standard-Q,
   absence of a homogeneous simplex solution, and failure of projective
   Q-bar on a principal set of size two or three.
3. The full-gap singleton collider, positive finite minimum-law atom, and
   source-faithful causal realization are genuine checked consequences.
4. The source-preserving completion atlas and its forced-pair geometry are
   genuine checked Research results.  Its declared coarse graph really has
   the two terminal structural modes `uniformEscape` and `minimumReturn`.
5. For **canonical** exact Nash--Bellman spines, failure of a Fin4 uniform
   payoff forces every marginal Quit-hazard series to be summable.  Failure
   also forces a uniform finite hazard-capacity bound for all finite exact
   blocks in the canonical reward box.
6. The all-Continue basin rigidity assertion is stronger than an eventual
   statement: `exactNashBellmanPath_eq_anchor_of_tendsto_unique_allContinue`
   does propagate constancy and all-Continue roots back to time zero under its
   stated open-basin uniqueness hypotheses.
7. The displayed table `W` is exactly the checked Solan--Vieille boundary
   table.  Its residual-hard status, full core, lack of stationary exact
   terminal Nash profiles, exact period-two terminal equilibrium, and uniform
   payoff are all checked together by
   `periodTwo_residualHard_fullCore_nonstationary_but_uniform`.

These facts make the document worth retaining.  It is much better than a raw
chronology of failed attempts.

## Required mathematical corrections

### 1. The final consistency verdict is not established

The dossier correctly observes that all dynamic requirements R1 and R5--R14
are consequences of counterexamplehood.  It then concludes that "the list is
not contradictory".  This does not follow.

The table `W` witnesses consistency only of the **finitely checkable
table-level fragment**.  It has a uniform equilibrium and minimum debt zero,
so it does not witness the conjunction of R1--R14.  Whether the full dynamic
conjunction is realizable is exactly the Fin4 conjecture.

The honest conclusion is:

> The table-level fragment is consistent and far from sufficient.  The full
> dynamic counterexample machine is neither known inconsistent nor known
> realizable.

The same correction is needed in the final paragraph and anywhere the
"second horn" is said to have been resolved.

### 2. R8 and Section 6 use too broad a spine class

The checked theorem is
`FinFourQuantitativeFullSupportHardResidual.all_marginalQuitHazards_summable`,
whose hypothesis is `IsCanonicalExactQuittingNashBellmanSpine`.  The dossier
defines an arbitrary bounded exact Nash--Bellman spine and states R8 and
Theorem 6.1 for every such spine.

The text must either:

- use "canonical exact spine" throughout, including annotations in the
  canonical Nash--Bellman reward box; or
- supply a theorem reducing every bounded exact spine to that canonical
  class.

No such general reduction was identified in the audited sources.

### 3. R6 and R7 are no longer merely `recorded`

The corrected source-preserving forced-pair stream, exact tail split, and
three-mode completion graph are checked in Research.  Their precise scope is
recorded in `formalized/FIN4_SOURCE_PRESERVING_COMPLETION_ATLAS.md`, including
the declaration-level record.  Mark the exact checked core of R6 and R7 as
`checked`; retain `recorded` only for genuinely extra conclusions not present
in those declarations.

### 4. The selector paragraph is not the current residual description

The phantom-free invariant-hull alternative in Section 6 is a sufficient
contradiction target, not a possible counterexample mode: canonical exact
spines are all marginally summable under no UE, and the compact
minimal-component argument then forces a phantom.  Similarly, unbounded
finite exact-block capacity is already excluded by the checked capacity
theorem.

Near-return production remains a legitimate possible proof route, but the
current strict residual is more accurately the bounded-capacity,
all-summable, source-attached **two-port saturation problem**: the upstream
marked atom/paid row and the downstream killed-face neutral saturation point
are not yet co-realized by an extension-compatible chronological kernel.

The dossier may retain the older selector alternatives as historical
sufficient strategies, but should not present them as the sharp current
normal form.

### 5. R11 overstates "perpetual leakage"

Exact killing of the mover debt gives a minimum-fibre support drop when no
new coordinate enters.  If another coordinate enters, however, the current
handoff can also land at a strictly off-minimum killed-player endpoint.  The
known theorem does not force an indefinitely iterable leakage carousel.

Replace "a counterexample must use this leakage perpetually" by the weaker
and proved alternative:

> every attempted minimum-fibre support descent must either suffer support
> entry or leave the minimum fibre; the resulting off-minimum strict chamber
> still needs a consumer.

### 6. R12 must separate checked saturation from the missing Fin4 adapter

The law-tight cap--Nash saturation hull and its neutral minimizer are reviewed
mathematics with checked integrated generic pieces.  The source-attached
Fin4 two-port lift is not supplied by those pieces.  The dossier's blended
status "partly checked, partly pending" is too coarse for a reference file.
State separately:

- checked/reviewed: closed exact-prefix saturation, minimum-face alternative,
  debt scaling, neutral exact roots, and law retention inside the supplied
  hull;
- open: a history-compatible source adapter or consumer relating the
  upstream paid atom to the downstream saturated killed face.

### 7. One no-go is stated too broadly

"Semantic proximity does not control unrestricted caps" is false without a
topology qualifier.  Uniform operational closeness of all unilateral payoff
functionals does control the cap.  What fails is control from prescribed
payoff/law proximity, weak stopping-law convergence, or the low-dimensional
semantic coordinates currently being transported.  State that narrower
failure.

### 8. The claimed full-dimensional table chamber is unsupported

The single table `W` proves nonemptiness of the table-level conditions, not
that their projection contains a full-dimensional semialgebraic chamber.
Several strict sign conditions are locally stable, but openness of the full
Q/no-homogeneous/residual-hard conjunction at `W` needs an explicit margin or
finite-complementarity argument.  Delete "full-dimensional" unless such an
argument is supplied.

Likewise, Candidate `B` is not a checked Lean table merely because its
singleton matrix equals the checked matrix of `W`.  Matrix conclusions may be
labelled exact inherited arithmetic; claims involving the complete reward
table are ordinary mathematics until `B` itself is declared and checked.

## Important missing structural fact

The dossier should record reward robustness explicitly.  If

```text
eta(r) = inf_sigma max_i (B_i^r(sigma) - U_i^r(sigma)),
```

then

```text
|eta(r) - eta(r')| <= 2 ||r-r'||_infinity.
```

For a fixed profile, prescribed payoffs and every deviation payoff move by at
most the reward-table sup distance; taking suprema, maxima, and infima gives
the bound.  Consequences:

- the counterexample set `eta(r)>0` is open;
- any counterexample has rational and generic nearby counterexamples;
- proving Fin4 UE on any dense reward class proves it for all Fin4 tables.

Thus a counterexample cannot be an isolated or measure-zero exceptional
table.  Its **dynamic realization may be rigid**, but the reward tables
realizing positive gap would occupy an open set.  This materially sharpens the
dossier's motivating dichotomy and prevents misleading "single exceptional
table" language.

## Recommended replacement verdict

The evidence supports the following conclusion and no stronger one:

> A hypothetical Fin4 counterexample is forced into a highly constrained
> source-attached dynamic residual.  The finite table-level constraints are
> jointly satisfiable and do not imply counterexamplehood.  The full dynamic
> residual is not known to be realizable or contradictory.  Current checked
> work further confines its exact Bellman geometry to canonical all-summable
> spines and uniformly bounded finite hazard capacity; the sharp live issue is
> the source-compatible coupling or consumption of the upstream paid mark and
> the downstream strict neutral saturation face.  If a counterexample exists,
> reward robustness makes it part of an open family, not a measure-zero
> exception.

With these corrections, the dossier can become a valuable maintained
reference.  In its current form it is mathematically informative but should
not be treated as the authoritative frontier statement.
