Historical design record. Frozen source/review artifact; see Research/Pending/README.md.

# Sorin flat-security branch: primary-source discovery

## Outcome and evidence boundary

The cited Aumann survey has now been obtained and read in an author-hosted
reprint. More importantly, an explicit published construction for the missing
flat-security branch was found in Tristan Tomala's exposition of Sorin's
theorem. It supplies the missing construction blueprint; it is not a checked
Lean proof or a dependency-complete formalization. No claim here declares the
mathematics open. No proofs or implementation patches were drafted.

This was read-only source discovery. No Lean/Lake, compiler, Git, shared edits,
children, repository snapshots, cache duplication, or math-note edits occurred.
Remote PDFs were streamed for reading/hash computation, not saved locally.

## Aumann: the actual cited survey acquired

[Author bibliography](https://math.huji.ac.il/~raumann/publication.htm), item42,
links [Survey of Repeated Games](https://math.huji.ac.il/~raumann/pdf/23.pdf).
The scan is collected-paper chapter23, printed411–437, PDF pages1–27. Its title
page identifies the original 1981 Morgenstern volume, pp11–42, and permission
to reprint. All27 pages were read visually; the scan has no text layer. Original
1981 pagination should not be inferred from the reprint's changed pagination.

Theorem1, p412, concerns the limiting-average supergame. Page418 asserts
discounted Hausdorff convergence. Appendix2, pp432–433, constructs a prescribed
pure calendar with mixed minmax punishment, but proves limiting-average Nash,
not the required positive-discount boundary case. Appendix3 refers elsewhere.
Thus acquisition closes the availability gap, not the construction gap.

The linked [Aumann–Shapley chapter](https://math.huji.ac.il/~raumann/pdf/Long-Term%20Competition.pdf),
Section5, pp403–408, was read with its correction p409. It studies a particular
discounted punishment-cost example, not the general flat-security producer.
Its correction also prevents treating the displayed perfect-equilibrium
threshold calculations as an unchecked reusable shortcut.

## Sorin1992: exact weaker hypothesis and semantics

[Sorin, Handbook chapter4](https://perso.imj-prg.fr/sylvain-sorin/wp-content/uploads/sorin-pub/92.HandGT.pdf),
Theorem2.2, printed78, states Hausdorff convergence of discounted Nash payoffs
to weakly individually rational feasible payoffs when there are two players OR
there exists one feasible point strictly above every minmax coordinate.
Ambient full dimensionality is not required by that second alternative.

Definitions on pp72–75 use finite nonempty action sets, independent simultaneous
randomization, observation of realized actions, unrestricted history-dependent
behavioral strategies, and normalized weights λ(1−λ)^(t−1), 0<λ≤1. Feasibility
is the convex hull of pure payoff vectors; IR inequalities are non-strict.
Set convergence is expressly Hausdorff. These match the requested semantics.

Its flat-case explanation remains abbreviated: singleton security payoff or
only one player with a possible profitable deviation. It cites Sorin1986 and
does not spell out the needed construction. Relevant pp72–78 were read fully;
no claim that the entire37-page chapter was reviewed.

## Explicit construction located: Tomala2006

[Tristan Tomala, Jeux répétés](https://www.numdam.org/item/10.5802/xups.2006-02.pdf),
Théorème3.8, printed38–39, attributes the result to Sorin1986. The complete
22-page publisher PDF was read. It is an author-written mathematical exposition,
not the original1986 discovery paper. Its model uses actual behavioral Nash,
realized-action monitoring, mixed minmax, weak IR and normalized discounting
(pp24–30,32–33). Hausdorff uniform-target quantifiers are explicit on p36;
uniformity is discussed again on p39.

Case(2), p39, supplies the missing prescription. If the IR set is the singleton
security vector, repeat a stage Nash. Otherwise, one coordinate is everywhere
at security and the other is strictly above security somewhere. The source
identifies the flat security value as that player's global maximum. It applies
the preceding periodic trigger construction while ignoring that player's
deviations. This avoids a supplied favorable best-reply orbit.

Caution: p38 literally requests an approximation within ε of every weak-IR
target while exceeding every security coordinate by2ε. That cannot hold at a
security boundary. Retain the existing separately selected positive margin and
compact-cover argument, not these printed constants. The global-maximum claim
is stated without its elementary convex-geometric details. Full behavioral
inequalities still require formal verification.

## Existing draft reuse versus remaining formal obligations

The following are reviewed static drafts, not newly checked in this discovery:

- `exists_discountedNash_allSmallRates_of_strictIR` and
  `exists_discountedNash_close_allSmallRates_of_strictIR`, future
  `Literature/Sorin1986.lean`, staged in
  `/tmp/sorin-strict-ir-discounted-nash.mMVeEDdp/003_ACTUAL_STRICT_IR_DISCOUNTED_NASH.patch`.
- `FiniteStageGame.exists_strictIR_close_of_fullDimensional`, same future
  file, staged in
  `/tmp/sorin-full-dimensional-discounted-folk.zoOejcMu/001_ACTUAL_FULL_DIMENSIONAL_IR_GEOMETRY.patch`.
- `property_4_discounted_of_fullDimensional`, same future file, staged in
  `/tmp/sorin-full-dimensional-discounted-folk.zoOejcMu/002_ACTUAL_UNIFORM_FULL_DIMENSIONAL_HAUSDORFF.patch`.

As root already identified, the center-mixing/finite-cover proof can be factored
under existence of one strict-IR point, retaining full dimensionality as a
delegate. That is a reuse recommendation, not work performed here.

The original requested missing API remains the acceptance criterion: given the
actual finite two-player game and an actual player whose coordinate equals
security on ALL actual IR payoffs, for every positive accuracy produce ONE
positive threshold before ALL smaller positive rates and ALL weak-IR targets;
for each rate/target internally produce an actual profile with exact Nash
against every full behavioral unilateral replacement and the stated payoff
approximation. The final API must not take a calendar, cap, stage maximizer,
joint best-reply orbit, selected equilibrium, or favorable carrier as input.

Implementation must explicitly discharge the singleton branch, the actual
finite-game player identification, the internally derived payoff bounds, the
same prescribed calendar's delivery, and unrestricted deviation caps. The
existing compact-cover and security-inclusion owners should be delegated to,
not copied. The global maximum used in a helper must be proved by its actual
source caller; renaming it a certificate would not close the API.

In particular, all stages of the delivered flat-coordinate calendar must retain
the exact flat payoff. An arbitrary approximation in ambient payoff space
cannot silently provide that equality. This is an audit obligation on a future
implementation, not a new favorable assumption authorized here.

The currently read `property_4_discounted` in `Literature/Sorin1986.lean`
still contains `sorry`; `lemma_2` delegates to it. Nothing in this source search
changes that status. No subgame-perfection requirement is added. Nothing here
asserts the produced approximation is exact at zero discount or at rate1.

## Integrity and read scope

Remote byte hashes, computed directly from streamed PDFs:

- Aumann survey reprint: `f8bf6a69cd8118a39ea392aa8aaa043944f1c7de24de8bc604edf02170ef7451`.
- Aumann–Shapley linked chapter: `169e549adae8b945f44562ca9345ca009c2fb7b2b2fff2657fa3428dd31583e4`.
- Sorin1992 chapter: `b5c0436812da33b0a7bbc3ae5c8a3663f5842bd36bbb0e48a4366bc047cff657`.
- Tomala2006 publisher PDF: `5977a756d74adc80ecf9757aa493677fbd9354b9fef98323057126e5082a018f`.

Local records independently rehashed:

- Requested prior source/dependency audit:
  `/tmp/sorin-full-dimensional-discounted-folk.zoOejcMu/SOURCE_QUANTIFIERS_DEPENDENCIES_AND_BOUNDARY_AUDIT.txt`
  `ac47fb74764120c20d4b5ffcc28fe9a05a386208a1aba4b3d98bfa9a18caed78`.
- Local Sorin1986 PDF:
  `literature/SORIN_1986__ON_REPEATED_GAMES_WITH_COMPLETE_INFORMATION.pdf`
  `d09a8e78f37f9863ff40e969a90f03799967d05eb70ba28a93afab84ddfce56c`.
- Current `Literature/Sorin1986.lean`:
  `fba6f32df9e627384edd4e5e21fec63a5e6d14e5eef83e9b07d462b1439bdfa5`.

Searches also examined author/institutional listings and primary-paper leads.
Fudenberg–Maskin1986's strict-target result remains no substitute for the flat
case, as already recorded in the prior audit. One-memory results were not used:
their institutional abstract involves richer action spaces/additional scope,
and no applicable flat-boundary proof was verified there. This is a bounded
source discovery result, not an exhaustive literature review.
