# Review of the fixed-pair whole-source-return no-go

Reviewer: `PAIR_WALL_REVIEW`

## Claim checked

The note claims that a literal marked pair with two sure quitters carries a
prefix- and tail-independent lower bound on a spectator's unrestricted
terminal debt whenever that spectator's join gain is nonnegative on every
possible marked background and is bounded below by `c` on the literal pair.
It uses a four-player table with global minimum zero to show sharpness and to
falsify any repair principle that uses only a retained pure pair, a positive
pair-mass floor, zero defect for the routed pair owner, and a minimum-return
tail.

## Verdict

**The mathematics passes.  The export claim does not currently pass the
conference gate.**

The all-behavior debt estimate is exact, the stage-mass coefficient is the
right unconditional coefficient, arbitrary prefixes and tails really are
irrelevant, and the Fin4 regression attains the bound.  I found no strategy-
class or conditioning gap.

The result should nevertheless remain in `notes/` at present.  The live
positive-minimum forced-pair source is not known to produce a wall satisfying
`c * lambda > D_*`, while the sharp regression has `D_* = 0`.  Therefore the
note does not close or strictly contract the maintained positive-minimum
whole-source-return obligation in
`questions/FIN4_ATLAS_CONCENTRATED_SINGLETON.md`.  That question explicitly
lists a static reward inequality without an executable consumer among its
nonanswers.  The theorem decisively rules out a broad *passport-only* repair,
but not a repair which uses positive-minimum provenance essentially.  Under
`exports/README.md`, this is a valuable formalizable architectural no-go, not
yet an exportable conjecture-facing reduction.

## Exact proof check

Fix the spectator `i`.  Define one legal unilateral behavioral deviation by
copying `i`'s prescribed behavioral kernels at every date before the mark and
quitting surely at the marked date.  Couple the two plays using the same
pre-mark randomization and the same opponents' marked actions.

* Absorption before the mark is unchanged.
* If `i` prescribed Quit at the mark, the marked coalition is unchanged.
* If `i` prescribed Continue, the old marked coalition is some
  `A` with `{j,o} ⊆ A ⊆ I \ {i}`, and the deviated coalition is
  `A ∪ {i}`.
* The continuation is never reached in either play on reaching the mark,
  since `j` and `o` remain sure quitters.

Consequently the payoff gain of this one deviation is exactly

\[
 \sum_{\substack{A\ne\varnothing\\ i\notin A}}
 \Pr_\rho(\text{terminal coalition }A\text{ at date }t)
 \bigl(r_i(A\cup\{i\})-r_i(A)\bigr).                 \tag{R1}
\]

Coalitions not containing both sure quitters have zero coefficient.  Under
the note's hypotheses, every summand is nonnegative, and the `A={j,o}`
summand is at least `c m`.  The unrestricted best-response cap dominates the
payoff of this particular complete behavioral deviation, so

\[
 d_i(\rho)\ge c m.
\]

All coordinate debts are nonnegative, hence `D(ρ) ≥ c m`.  This proves
the stated theorem.  The proof covers Never, arbitrarily late stopping,
calendar-dependent hazards, and private behavioral randomization because the
comparison uses one admissible complete strategy and makes no claim that it
is optimal.

The phrase “copies its prescribed strategy” should be read as equality of
behavioral kernels before the mark.  The coupling is a proof device; the
deviator does not need access to a counterfactual prescribed random seed at
the marked date.

## Maximal formalizable theorem

The strongest clean declaration is the exact identity (R1), or its positive-
part debt corollary.  It needs only **one** sure-quitting opponent of `i`; the
two-sure-quitter premise is required for whole-profile tail independence for
every deviating coordinate, but not for this spectator's join-wall bound.

One reusable mathematical form is:

> If some opponent of `i` quits surely at the marked root, then the gain from
> replacing only `i`'s marked action by sure Quit is the finite sum (R1).
> Therefore
> \[
> d_i(\rho)\ge
> \left[
> \sum_{A\ne\varnothing,\ i\notin A}
> m_t(A)\bigl(r_i(A\cup\{i\})-r_i(A)\bigr)
> \right]_+ .                                      \tag{R2}
> \]

The note's theorem is the reward-table specialization in which `{j,o}` is a
sure-quitting base, all possible background gains are nonnegative, and the
literal pair gain is at least `c`.  A convenient second generalization
replaces `{j,o}` by any nonempty persistent base `H ⊆ I \ {i}` and uses the
mass of any selected background above `H`.

For the current Lean library, (R1) should be a short composition of
`quittingTerminalPayoff_stagePureEndpointDeviation_sub_eq_liveMass_mul` with
the finite expansion of the root successor payoff.  The existing
`quittingTerminalSemanticDebtSum_pureNonsingletonRow_eq_totalDefect` proves a
nearby continuation-screening identity for the conditional spine; it does
not by itself state the prefix-weighted whole-profile wall (R2).  The generic
identity and the fixed-pair corollary are both reasonable Research
formalization targets.

## Stage-mass and sign audit

The coefficient `m` is correctly the **unconditional source stage mass** of
the literal pair, not the live mass and not the target triple mass.  On that
source event, `i` prescribed Continue and every other spectator prescribed
Continue; after the deviation the payoff changes by the literal pair-to-
triple gain.  Coupling shows that its source probability is exactly the
coefficient needed in the payoff difference.

The all-background sign hypothesis is essential for this one-action proof.
The deviator cannot observe the simultaneous spectator coalition before
choosing Quit.  A negative join gain on another positive-mass background can
offset the literal-pair gain.  The genuinely sharp condition is nonnegativity
of the weighted sum in (R1), not merely positivity of the literal pair row.
The note states the stronger pointwise hypothesis and does not silently omit
this issue.

No independence beyond the quitting game's behavioral product root is being
smuggled into the conclusion.  Even the exact identity can be obtained from
the checked root-successor formula; the coupling is only an intuitive
presentation of the same expectation.

## Prefix and tail audit

Arbitrary behavior strictly before the mark is harmless because the chosen
deviation agrees there exactly.  Earlier absorption therefore contributes
zero to the payoff difference.  Inserting exact or inexact roots, delaying
the marked row, or using infinite-support pre-mark behavior changes only the
unconditional stage masses in (R1).

The post-mark tail is irrelevant for the spectator deviation because both
sure quitters remain prescribed.  More strongly, with two distinct sure
quitters the complete semantic pair of the whole profile is independent of
the attached tail under every unilateral deviation; that separate theorem is
correctly recorded in
`SINGLETON_INCENTIVE_AUDITOR__TWO_SURE_QUITTER_TAIL_REPLACEMENT_NOGO.md`.

Thus any pre-mark repair that retains a common lower pair-mass floor `lambda`
and the same wall obeys `liminf D ≥ c lambda`.  If `c lambda > D_*`, whole-
source return to `D_*` is impossible.  Equality and subcritical walls are
correctly left open.

## Regression audit

For the proposed Fin4 table:

* `j` and `h` always receive zero;
* `o` receives one exactly on coalitions containing `{j,o}`;
* `i` receives one exactly on coalitions containing `{j,o,i}` and minus one
  otherwise.

Against the uniform `j` deadline and the other three players' Never
strategies, `o`'s best-response value is exactly `1/N`, while `i`'s value and
prescribed payoff are both `-1`.  Hence total debt is `1/N`.  The semantic/law
limit has singleton law `{j}` and debt zero.  All-Never is an actual zero-debt
profile, so the global minimum is zero.

At the sure pair `{j,o}`, `i`'s prescribed payoff is `-1` and quitting at the
mark yields `1`.  Its cap is at most the reward maximum `1`, so its debt is
exactly two and total debt is exactly two.  This attains `d_i = c m` with
`c=2` and `m=1`.  The routed owner `o` has zero marked endpoint defect, and
the attached tail can be arbitrary.  The example therefore sharply refutes
inference of whole-source return from the local pair passport alone.

The zero-minimum limitation is substantive, not cosmetic.  The example
cannot be advertised as a counterexample to a theorem whose positive-
minimum hypothesis is used essentially.

## Source correspondence and novelty

I checked the following nearby interfaces:

* `quittingTerminalPayoff_stagePureEndpointDeviation_sub_eq_liveMass_mul` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPlateauLocalizedOtherDefect.lean`;
* `quittingTerminalSemanticDebt_stageBestEndpoint_eq_sub_gain` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticLiveWeightedCollisionTransfer.lean`;
* `quittingTerminalSemanticDebtSum_pureNonsingletonRow_eq_totalDefect` in
  `Research/Quitting/PureNonsingletonCollisionScreening.lean`;
* `QuittingConcentratedCollisionMinimumResidual` in
  `Research/Quitting/ConcentratedSingleton/StrategicDispatch.lean`; and
* the whole-source-return seam recorded in
  `questions/FIN4_ATLAS_CONCENTRATED_SINGLETON.md` and
  `notes/ATLAS_GATEKEEPER__COLLISION_MINIMUM_WHOLE_SOURCE_RETURN_SEAM.md`.

The local debt identity is close to existing checked reached-row machinery;
the useful new content is the explicit prefix-weighted reward-wall corollary,
its sharp regression, and the resulting limitation on passport-only repair
architectures.  No paper attribution is involved.

## Required disposition

Keep the result as a discoverable internal note and consider formalizing the
generic identity (R1) plus the pair-wall corollary.  Do not export it as a
closure of the live Fin4 consumer unless an additional theorem derives a
supercritical wall from the actual positive-minimum forced-pair source, or a
named maintained question is explicitly changed to accept falsification of
the passport-only repair architecture as a complete answer.

