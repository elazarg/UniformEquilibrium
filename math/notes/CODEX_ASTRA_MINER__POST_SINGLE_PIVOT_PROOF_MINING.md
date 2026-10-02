# Post-single-pivot proof mining

Identity: CODEX_ASTRA_MINER.

Status: independent read-only source audit after the single-pivot packet was
formalized. This note proposes literal consequences of existing mathematics;
it contains no new Lean declaration, production edit, build, or export. The
coordinator reported a successful full build of the packet at commit
`7c39bc0`. I did not repeat that check. Research declarations mentioned below
were inspected statically and were not checked here, including their axioms.

The most useful next APIs are: a full-cap finite-menu approximation theorem
and fixed-target scalar characterization; unconditional clipped punishment
transport; robust scalar floors with explicit deadline deviations; and linear
same-profile transport when the original own-singleton vector is nonnegative.

## Question and notation

For a finite nonempty player set, which stronger literal statements and actual
source connections already follow from the implemented normalization and
finite-menu proofs, without solving a new game-theoretic conjecture?

Let `r` be the original reward table, `s_i = r_i({i})`, `p` a fixed pivot,
`g = s_p > 0`, `c_p = 0`, and `c_i = s_i` for other players. Write
`r'_i(S) = (r_i(S) - c_i) / g`. Both games keep literal Never payoff zero.
For an actual independent behavioral profile write `U_i` for prescribed
terminal payoff, `B_i` for the unrestricted behavioral cap, `F_i` for the
supremum over all finite pure response dates, `d_i = B_i - U_i`, `E = max_i d_i`,
and `m` for its actual joint Never probability. Primes denote the same profile
in the normalized table, except where a new profile is explicitly constructed.
Write `v_i` for full behavioral punishment.

For a menu with dates strictly below `H` and Never, write `e` for menu
exploitability, `N_i` for the Never response payoff, `D_i` for the product of
opponents' Never probabilities, and `L = N_p + D_p - U_p`. Finite-menu laws are
independent product laws and deviations below are unrestricted behavioral
deviations unless a particular legal deterministic response is displayed.

## 1. Full-cap finite-menu approximation and a fixed-target characterization

**Candidate needing a literal Lean proof; proof ingredients are already in
production. Highest priority.**

For every actual profile, positive tolerance `eta`, and lower deadline `H0`,
there exist `H >= H0` and actual finite-menu laws `q` such that

    E(q) < E(profile) + eta,
    ||U(q) - U(profile)|| < eta.

There is no singleton-sign, normality, or canonical-table hypothesis. The
payoff conclusion and full-cap estimate concern the same selected `q`.

The existing proof of
`finiteMenuEarlyAbsorption_of_uniformEquilibriumPayoff_of_singleton_pos`
(`UniformEquilibrium/Quitting/Terminal/FiniteMenuEarlyAbsorptionNecessity.lean`)
already carries out the construction up to its separate use of the positive
singleton to control joint Never mass. Extract the preceding argument:

1. Replace the fixed profile by its actual stopping laws. The exact equality
   `quittingTerminalExploitability_stoppingLawProfile_behaviorLaws_eq` in the
   same file retains its unrestricted exploitability.
2. Choose a cutoff whose summed late finite mass is smaller than
   `eta / (8 * (M + 1))`, using
   `exists_horizon_sum_stoppingLawLateFiniteMass_lt` (exported from
   `UniformEquilibrium/Quitting/Paths/LateFiniteStoppingLawCensor.lean`).
3. Censor those late finite atoms to Never. The theorems
   `quittingTerminalExploitability_censored_le` and
   `abs_expectedPayoff_censorLateFiniteStoppingLaws_sub_le` in that file bound
   the exploitability change by `4M` times the summed mass and each payoff
   change by `2M` times that same mass. Finite-coordinate sup norm gives the
   vector estimate. Original Never atoms are retained; added mass is exactly
   the censored finite tail.
4. Choose `H = max H0 (cutoff + 1)`. Use
   `exists_finiteDeadlineTimingLaws_of_censoredLaws` and
   `finiteDeadlineTimingProfile_eq_stoppingLawProfile_of_laws`
   (`UniformEquilibrium/Quitting/Terminal/FiniteMenuEarlyAbsorptionNecessity.lean`).

Consequences worth naming:

- The infimum of **full** exploitability over all finite-menu product laws,
  allowing all deadlines, equals `quittingTerminalExploitabilityInf r`.
- A fixed target is a uniform-equilibrium payoff iff it is a payoff limit of
  finite-menu profiles with full exploitability tending to zero. Necessity
  starts with
  `exists_terminalProfile_sequence_exploitability_tendsto_zero_of_uniformPayoff`
  (`UniformEquilibrium/Quitting/Terminal/TargetTail/UniformTargetTerminalSequence.lean`)
  and applies the approximation separately at each index, with vanishing
  tolerance. Sufficiency uses
  `quittingGame_isUniformEquilibriumPayoff_of_terminalNash_tendsto`
  (`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`).
- For a canonical single-pivot table, the current scalar-source consumer is
  an equivalence: UE existence iff arbitrarily small simultaneous `e` and `L`
  occur at actual finite menus. The identity
  `singlePivot_fullExploitability_eq_max_menuExploitability_scalar`
  (`UniformEquilibrium/Quitting/Terminal/SinglePivotFiniteMenuSource.lean`)
  makes both directions immediate after the generic approximation theorem.
  The forward implication in
  `exists_uniformEquilibriumPayoff_of_singlePivot_finiteMenu_scalar_source`
  (`UniformEquilibrium/Quitting/Terminal/SinglePivotFiniteMenuCompletion.lean`)
  is already implemented in the source-to-UE direction.
- The fixed-target version requires `U(q_n)` to converge to that target;
  merely bounding `e(q_n)` and `L(q_n)` selects some target by compactness.

The infimum equality is not an exact-menu-Nash restriction. Approximation
retains full behavioral caps and yields approximate menu Nash. Nothing here
selects exact finite Nash laws with small `L`, imposes a universal deadline
bound, or proves uniform tightness of a changing family of stopping laws.

Related existing neighborhood: the toolkit points to the finite-clock exact
scale search and semantic-center results in Research. These already encode
finite-clock behavioral realizations and should be checked for naming and
adapter reuse before introducing a second finite-clock representation. The
construction above needs only production censoring and the actual menu API.

### Comparison with the newly reviewed geometric LP packet

After completing the initial audit I read the entire reviewed packet
`math/exports/GEOMETRIC_PIVOT_TAIL_COMPRESSION_AND_EXACT_REPAIR_LP.md`.
Its Theorem 4 already proves canonical Fin4 equivalence between small menu
scalar sources, small fixed-opponent LP values, and full early-absorption
sources. That reviewed mathematics is not yet a checked Lean API, and the
canonical source-equivalence part of this note should be coordinated with
its implementation instead of duplicated.

The reusable addition of item 1 is the generic signed, arbitrary finite-player
approximation theorem with **fixed target payoff control**. Combining it
with the packet's exact inner LP gives the stronger quantitative identity

    inf[H >= 1, finite opponent laws q_{-p} on F_H] z_*(q_{-p})
      = inf[all behavioral profiles] E(profile).

This identity does not assume `g > 0`, zero nonpivot singletons, or Fin4.
For every fixed finite opponent family, the packet identifies `z_*` with
the infimum over actual pivot laws; this restricted-profile infimum is at
least the unrestricted global infimum. Conversely, item 1 approximates
any actual complete profile by finite laws, and the inner optimum is at
most the exploitability of that finite pivot law against its finite
opponents. These two inequalities prove the identity without any outer
minimum, uniformly bounded deadline, or exact Nash selector.

The fixed-target version is also direct. A specified target `u` is a UE
payoff iff there are deadlines, finite opponent laws, and feasible inner-LP
points whose `z` coordinates tend to zero and whose prescribed payoff
vectors tend to `u`. Necessity uses item 1 and the packet's compression map;
compression preserves the whole payoff vector. Sufficiency implements each
feasible LP point with vanishing extra error. The packet explicitly preserves
the whole payoff vector even when approximating its nonliteral
`alpha = 0 < lambda` boundary. One may impose a finite linear payoff box
`|U_i - u_i| <= eta` in each fixed-opponent LP to express this condition.

These are candidates for literal corollaries **after** the reviewed geometric
packet's ingredients are formalized. They do not assert that any table
supplies small LP values. They strengthen the semantic statement of the
reduction and preserve the user's fixed target before accuracy.

## 2. Unconditional clipped punishment and an exact normality criterion

**Candidate needing a short literal Lean proof.**

Under `g > 0`, with no original normality assumption,

    v'_i = (min(v_i, s_i) - c_i) / g,
    s'_i - v'_i = max(s_i - v_i, 0) / g.

Moreover the un-clipped formula

    v'_i = (v_i - c_i) / g

holds **iff** `v_i <= s_i`. Thus normality is precisely the condition for
that particular affine punishment identity, not only a sufficient assumption
in its current theorem.

The proof of `quittingPunishmentValue_singlePivotNormalized`
(`UniformEquilibrium/Quitting/Punishment/SinglePivotPunishment.lean`) already
derives the first identity, then rewrites `min_eq_left hnormal`. Retain the
preceding expression. Its exact ingredients are
`quittingFinitePureReplyPunishmentValue_eq_min`
(`UniformEquilibrium/Quitting/Punishment/FinitePureReplyPunishment.lean`),
`quittingFinitePureReplyPunishmentValue_playerwiseAffine`
(`UniformEquilibrium/Quitting/Terminal/TerminalAffineReward.lean`), and the
normalized nonnegative-singleton finite/full punishment equality in
`SinglePivotPunishment.lean`. The margin identity and iff are ordered-field
consequences because `g > 0`.

For a nonpivot, this says `v'_i = min((v_i - s_i)/g, 0)`. In particular, a
strictly abnormal original coordinate becomes a zero-margin normalized
coordinate. A strictly positive normalized singleton-to-punishment margin is
equivalent to the strict original margin `v_i < s_i`. Canonical normality is
already established by `singlePivotSingletonTable_punishment_le_solo`
(`UniformEquilibrium/Quitting/Terminal/SinglePivotCanonicalConsequences.lean`),
so another normality wrapper alone adds little; the new content is exact
clipping and its iff.

The existing `nonnormal_boundary`
(`UniformEquilibrium/Diagnostics/Quitting/SinglePivotNonNormalRegression.lean`)
tests this formula: original nonpivot singleton `-1`, punishment `0`, and
normalized punishment `0`, agreeing with the clipped value and refuting the
un-clipped value `1`.

No fixed-target reverse implication without normality follows from this
clipped identity. It discards the original negative margin.

## 3. Robust scalar floors and an explicit full-gap deadline response

**Candidate needing short literal Lean proofs.**

Assume a canonical table and a supplied global floor `Gamma > 0`, so every
actual behavioral profile has `E >= Gamma`. For every actual menu law with
menu error `e < Gamma`,

    L >= Gamma,
    D_p >= Gamma - e.

The existing exact-source theorem
`singlePivot_exactMenuNash_scalar_and_deletedNever_ge`
(`UniformEquilibrium/Quitting/Terminal/SinglePivotCanonicalConsequences.lean`)
is the `e = 0` case. The general proof uses only `E = max(e,L)` and the fact
that Never is a displayed response, giving `N_p - U_p <= e`, hence
`L <= D_p + e`. With an externally supplied upper bound `epsilon` on menu
error and `epsilon < Gamma`, the same conclusions hold with
`D_p >= Gamma - epsilon`.

The floor is witnessed by a completely explicit strategy: player `p` quits
deterministically at date `H` (or any later finite date). The theorem
`quittingFiniteDeadlineTimingProfile_pureTime_eq_never_add_of_le`
(`UniformEquilibrium/Quitting/Terminal/FiniteDeadlineFullReplyCap.lean`) gives
its payoff exactly `N_p + D_p`. Its gain is therefore `L >= Gamma`.

This has no supremum-attainment loss. At exact menu Nash, this response
attains the pivot's unrestricted cap whenever `L >= 0`; if `L < 0`, a
displayed best response attains that cap. The global half-gap loss in
`hasTerminalExploitabilityGap_singlePivotNormalized`
(`UniformEquilibrium/Quitting/Punishment/SinglePivotTerminalGap.lean`) remains
appropriate for arbitrary behavioral profiles, whose cap need not be attained.

Actual source: `FinFourSinglePivotNormalization.profile_floor` and
`.every_deadline_nash`
(`UniformEquilibrium/Diagnostics/Quitting/FinFourSinglePivotNormalization.lean`)
provide the normalized table, one fixed pivot, the specific
`Gamma = residual.witness.terminalGap^2 / (16 * bound^2)`, and actual fresh
exact Nash laws for all deadlines. Thus this is a stronger output of the
already checked actual Fin4 source, not a new source assumption.

## 4. Every nonpivot Never atom is large at the actual hard source

**Candidate needing product and support adapter lemmas.**

At every exact mixed menu Nash law supplied by the canonical hard source,
the preceding `D_p >= Gamma` implies, for each `j != p`,

    q_j(Never) >= Gamma > 0.

All factors lie in `[0,1]`, so their product is at most each factor. The
adapter must explicitly identify the compact timing law's Never mass with
`(mixed j none).toReal`; this is not a statement about joint Never mass.

Apply `finiteDeadline_mixedNash_neverSupport_payoff_eq_never`
(`UniformEquilibrium/Quitting/Terminal/FiniteDeadlineNashExistence.lean`) to
each such `j`. It yields `U_j = N_j`. Combining with
`singlePivot_exactMenuNash_nonpivot_debt_eq_zero`
(`UniformEquilibrium/Quitting/Terminal/SinglePivotFiniteMenuSource.lean`)
shows that Never actually attains each nonpivot's unrestricted cap. Because
`s_j = 0`, every deterministic date at or after `H` attains that same cap.

This strengthens the actual-source record with concrete support and response
information. It does not force positive pivot Never mass: the existing
one-date canonical regression has zero pivot Never mass and positive debt.
If the pivot additionally has positive Never mass, the already implemented
`singlePivot_mixedNash_pivot_neverSupport_debt_eq_deletedNever` in that file
gives `E = d_p = D_p`, using the exact nonpivot debt equalities.

For approximate menus, `D_p >= Gamma - epsilon` still bounds each nonpivot
Never mass. Exact payoff equality then becomes approximate support
indifference; that additional weighted-average estimate should be proved
separately rather than reusing the exact Nash theorem.

## 5. Linear same-profile equivalence when all original singletons are nonnegative

**Candidate needing a short proof from existing profile identities.**

Assume `g > 0` and `s_i >= 0` for every player. Let `C >= 0` bound all offsets
`c_i` above; the sharp choice is their finite maximum. For every unchanged
actual profile,

    d_i = g * d'_i + c_i * m,
    g * E' <= E <= (g + C) * E'.

The exact debt identity
`quittingTerminalDeviationDebt_singlePivotNormalized`
(`UniformEquilibrium/Quitting/Punishment/SinglePivotProfileDebtTransport.lean`)
has `F_i` on its right. Under the displayed sign assumption,
`quittingContinuationBestResponseValue_eq_finitePureReplyValue_of_solo_nonneg`
(`UniformEquilibrium/Quitting/Punishment/FinitePureReplyValue.lean`) gives
`F_i = B_i`, yielding the first equation. Nonnegative offsets give the lower
comparison; the upper comparison uses `m <= E'`, already proved by
`quittingLiveMassLimit_singlePivotNormalized_le_exploitability`
(`UniformEquilibrium/Quitting/Punishment/SinglePivotProfileDebtTransport.lean`).

In particular, an original global floor `Gamma` gives a normalized global
floor `Gamma / (g + C)`. This is linear, unlike the general signed bound
`Gamma^2 / (16M^2)`, and it retains the literal profile. It also identifies
exact terminal Nash profiles in both games: `E = 0` iff `E' = 0`.
For approximate sequences it supplies the reverse fixed-target transport
using unchanged profiles, with the existing Never correction tending to zero.

All original singleton rewards nonnegative automatically implies original
punishment normality by comparison with all-Continue opponents. No sign
restriction on other coalition reward entries is needed.

For signed singletons, the forward estimate can separately replace the full
reward bound `M` by any `Cminus >= max_i max(-c_i,0)`:

    E' <= (1/g + Cminus/g^2) * E.

This follows from the current proof of
`quittingTerminalExploitability_singlePivotNormalized_le` in
`SinglePivotProfileDebtTransport.lean`, where the reward bound is used only
to control the negative part of the offsets. This refined one-way estimate
does not yield the preceding reverse same-profile theorem for signed tables.

## 6. A stronger positive pivot already exists in Research

**Existing Research declaration, statically inspected; not checked here.**

`HasTerminalExploitabilityGap.exists_singletonReward_ge`
(`Research/Quitting/FiniteClockDoubleFullGapCosource.lean`) proves for every
finite player type and actual positive terminal gap `Gamma` that some
singleton reward is at least `Gamma`. Its proof simply applies the supplied
actual deviation gap to all-Continue and compares that deviation with
`max(0,s_i)`. It does not use the finite-clock machinery in the surrounding
file and does not require original normality.

The production source
`exists_finFourHardResidual_and_positiveSingletonPivot_of_no_uniformPayoff`
(`UniformEquilibrium/Diagnostics/Quitting/FinFourSinglePivotActualSource.lean`)
currently selects a merely positive pivot after fixing the residual. Using
the stronger lemma would select, still from that one residual, a pivot with

    g >= residual.witness.terminalGap,
    |r'_i(S)| <= 2M / residual.witness.terminalGap.

This removes a separately unbounded `1/g` from that actual source's reward
estimate. It does not produce a universal unit-box bound: the residual gap
can be arbitrarily small. A maximizing singleton pivot is also possible, but
the weaker quantitative selection already supplies this bound.

If used by production, promote the game-semantic lemma and have Research
import it, following the lane policy. Do not import Research into production
or copy the surrounding finite-clock declarations. Its proof can also be
re-established directly in the production source using the existing
all-Continue cap theorem.

Related Research theorem
`exists_quittingFiniteClockDoubleFullGapCosource` in the same file supplies
two distinct full-gap debtors at one finite-clock profile. This is compatible
with the canonical single-debtor exact-menu theorem: that co-source is not
asserted to be exact menu Nash. It gives no contradiction or missing scalar
producer by itself.

## 7. General finite-player boundary of the normalization reduction

**Existing transport is general; the bare actual source is Fin4.**

`uniformEquilibriumPayoffSet_singlePivotNormalized`
(`UniformEquilibrium/Quitting/Punishment/SinglePivotUniformPayoff.lean`) is
already stated for arbitrary finite player types, with a positive pivot and
original all-player punishment normality. Consequently, within the class of
normal games, counterexample existence reduces to canonical single-pivot
tables at every finite cardinality. The singleton selection above supplies
the positive pivot from any positive-gap game. No four-player arithmetic is
used by the transport itself.

The additional source fact needed to remove normality is presently obtained
for Fin4 from `FinFourQuantitativeFullSupportHardResidual.all_punishmentNormal`
via the inspected Fin4 source theorem. This audit did not find or prove an
arbitrary-cardinality counterpart. Canonical tables' automatic normality is
not a proof that every original counterexample was normal. Accordingly,
do not upgrade `exists_finFour_no_uniformPayoff_iff_exists_singlePivot`
(`UniformEquilibrium/Diagnostics/Quitting/FinFourSinglePivotNormalization.lean`)
to arbitrary finite games by deleting the original-normality premise.

## Scope, checks, and next action

Read the root and math agent policies, source navigation, goal and research
methods. Followed the fixed-target, finite-only punishment, canonical source,
actual Fin4, late-finite censoring, and finite-clock toolkit links. Also
inspected the matrix and finite Bellman normalization transports to verify
that those existing equivalences do not provide behavioral minimum ancestry.
No broad mathematical-note or Lean-tree survey was used.

No Lean checks, trust scans, shared builds, git operations, or production edits
were run in this read-only audit. `python scripts/check_docs.py` passed; it
does not validate this ignored note's mathematical candidates. This ignored
note is the audit's sole write.

Recommended first implementation packet: extract full-cap finite-menu
approximation with payoff control, then prove the fixed-target and existential
scalar iff statements in coordination with the reviewed geometric packet.
Its source-equivalence theorem should not be duplicated. Items 2, 3, and 5 are small
independent theorem additions with explicit proofs above. Item 4 adds useful
actual-source structure after product-law adapters. Item 6 is a targeted
promotion opportunity rather than new mathematics. None produces a small
scalar from arbitrary reward data, closes the quitting conjecture, or changes
the fixed-target quantifier order.
