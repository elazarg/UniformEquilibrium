# Quantitative collapse to finite strategic models

Author: CODEX_LARCH_GEOMETRY. Internal theory sketch, 2026-09-07.

## Current status and question

The useful hidden theory here is quantitative stability of terminal-law
strata **including complete unilateral response caps**. Two elementary proof
drafts below improve the earlier unspecified semialgebraic power bound:

1. For four independent quitting players, singleton-plus-Never mass ε gives
   a two-sure-quitter product-root realization within 8ε^(1/3) in law and
   16Mε^(1/3) in both payoff and complete-cap coordinates. The exponent
   1/3 is optimal for this law-realization conclusion.
2. If leakage ℓ is all mass outside exact pairs, there is a pure-pair root,
   with zero or one padding row, within 512ℓ in law and 1024Mℓ in both
   payoff and complete-cap coordinates. Consequently

       1 − max_pair μ(pair) ≤ 512 (1 − sum_pair μ(pair)).

Here every reward has absolute value at most M, including the zero Never
reward. Constants are deliberately loose. These are ordinary mathematical
proof drafts, with no Lean changes or checks and no export. An
[independent mathematical review](../feedback/CODEX_LARCH_GEOMETRY__OBSERVATION_STABILITY_THEORY__BY_CODEX_LARCH_JOINT.md)
checked the core estimates and found no unresolved mathematical objection.
The stronger
quantitative claims were not found in the bounded source search; this is not
a claim of mathematical novelty beyond this repository.

The source remains one actual behavioral profile throughout. No public
correlation, averaging of profiles, finite-calendar source assumption, or
bounded-deviation class enters either argument. Approximation of payoff does
not solve exact payoff-fiber recovery. Neither theorem supplies low leakage
from arbitrary game data or proves UE.

## 1. Existing pieces inspected

The preceding [survey](CODEX_LARCH__MISSING_THEORY_SURVEY.md) used exact finite
observable compression and a semialgebraic inequality to obtain unspecified
power-law pair concentration. The more useful starting point is the existing
[zero-singleton product-base packet](../formalized/ZERO_SINGLETON_BEHAVIORAL_LAW_PRODUCT_BASE_AND_SURE_CORE_DESCENT.md).
Its first-efficient-root and counterfactual coupling proofs already contain
the mechanism needed for explicit quantitative estimates.

A concurrent independent [near-certain pair analysis](CODEX_FRECHET_CYCLE__PAIR_CONCENTRATION_FULL_CAP_TRANSFER_AND_FORCING_GAP.md)
already gives a sharper transfer from one pair mass q>1/2: conditioning on
a common-date product event changes each payoff and cap by at most
4M(1−q). It also derives the same six-pair reward screen. Those transfer
and screen conclusions are overlapping discoveries, not first supplied by
this note. The additional statements here are linear leakage-to-concentration,
the sharp cube-root low-singleton estimate, and explicit first-root selection
of a finite model. Both investigations retain the timing bit and leave the
upper leakage incentive account open.

Exact source declarations inspected:

- `exists_pair_terminalOutcomeMass_eq_one_of_terminalPairMass_eq_one`
  (`UniformEquilibrium/Quitting/Paths/PairOnlyTerminalLawRigidity.lean`):
  exact pair-only terminal laws concentrate on one pair.
- `exists_twoSureProductRoot_realizing_jointCarrierPoint_of_strictMargin`
  and `exists_twoSurePaddedProductRoot_realizing_jointCarrierPoint_of_margin`
  (`UniformEquilibrium/Diagnostics/Quitting/ZeroSingletonBehavioralLawProductBase.lean`):
  qualitative exact semantic realization on the zero-singleton/Never face,
  with the stated singleton-margin hypotheses.
- `no_uniformEquilibriumPayoff_of_forcedPairMasses`
  (`UniformEquilibrium/Quitting/Terminal/PairMassForcingConsumer.lean`):
  a consumer with supplied same-profile incentive forcing, currently based on
  two-pair square-root inequalities.

These statements were inspected statically under their displayed imports;
they were not compiled here. The current frontier explicitly records no
downstream consumer for the zero-singleton complete semantic realization.

## 2. Common setup and a counterfactual coupling lemma

There are four players. At date t, conditional on the unique live history,
they quit independently with probabilities qᵢ(t). Let Lₜ be prescribed
survival strictly before date t. Let μ be the terminal coalition law, U its
reward expectation, and Bᵢ the supremum of terminal payoff over every
behavioral replacement by i. The representation by independent complete
stopping laws is equivalent for these terminal calculations.

Suppose a date t is selected and q* is a replacement root containing two
distinct sure quitters. Put

    E = 1 − Lₜ,
    d = sum_i |qᵢ(t) − q*ᵢ|.

Construct ρₜ: all players Continue before t, play q* at t, then Never.
The terminal laws of the source and ρₜ have total variation distance at
most E+d. Their prescribed payoff coordinates differ by at most 2M(E+d).
Their complete cap coordinates also differ by at most 2M(E+d).

For the cap claim, fix one arbitrary replacement strategy of i and couple
it identically in the two games. The probability that a source opponent
quits before t is at most E: opponent-only survival is at least full-profile
survival Lₜ. Conditional on common survival, couple the opponents' product
draws at t; mismatch probability is at most the sum of their probability
changes, bounded by d. If the opponents' draws match, an opponent surely
Quits at t because deleting one player leaves one member of the sure pair.
The two terminal outcomes therefore agree unless a prefix or root mismatch
occurred. The estimate is uniform before taking the response supremum.

Finally replace t by 0 when t=0 and by 1 when t>0. This preserves U and B
exactly: against a two-sure root, a pure quitting-time response has only
three outcome types, strictly before, at, or strictly after the root; Never
belongs to the last type. A positive number of empty prefix rows gives the
same singleton response option as exactly one. Randomized responses are
mixtures of these endpoint types. This preserves complete cap values; it
does **not** preserve the intervention law of each fixed calendar-labeled
deviation after retiming.

Thus all later conclusions concern an actual zero- or one-padded finite
profile, chosen using the selected root's calendar case.

There is a useful margin corollary. If the cap comparison error is η and
every source cap satisfies Bᵢ>sᵢ+η, where sᵢ is the own-singleton reward,
then the output can be unpadded. Indeed its padded cap is within η of Bᵢ,
hence strictly above sᵢ. Since padded cap equals max(sᵢ, unpadded cap),
padding is redundant in every coordinate. Thus the existing strict margin
at a positive semantic minimum has a quantitative neighborhood version;
the low-defect source premise remains separate.

## 3. First theorem draft: quantitative zero-singleton stability

Let σ be total singleton mass and ζ the Never mass, and put ε=σ+ζ.
Work first with 0<ε<1/512 and use the fixed threshold δ=1/256.

For a root q, write a(q) for nonempty probability and s(q) for singleton
probability. Sort its probabilities q₁≥q₂≥q₃≥q₄. If a(q)>0, then

    a(q) ≤ 4q₁,
    s(q) ≥ q₁(1−q₂)(1−q₃)(1−q₄) ≥ q₁(1−q₂)³,
    s(q)/a(q) ≥ (1−q₂)³/4.                         (1)

Choose the first positive-absorption date t satisfying s(q(t))≤δa(q(t)).
It exists: otherwise σ≥δ(1−ζ), contradicting
σ≤ε<δ(1−ε). The latter inequality holds for ε<1/512.
Every earlier absorbing row has singleton fraction above δ, so

    E ≤ σ/δ ≤ 256ε < 1/2.                          (2)

At the selected root, (1) gives q₁,q₂≥3/4. Its contribution to total
singleton mass satisfies Lₜs(q(t))≤σ, hence s(q(t))≤2ε. The absolute
singleton bound in (1), now using q₁≥3/4, improves this to

    (1−q₂)³ ≤ (4/3)s(q(t)) ≤ (8/3)ε < 8ε.

Snap the largest two probabilities to 1 and leave the others unchanged.
The resulting two-sure root q* has

    d ≤ 4ε^(1/3),
    E+d ≤ 256ε+4ε^(1/3) ≤ 8ε^(1/3).                 (3)

The last step uses ε^(2/3)<1/64. The coupling lemma proves the announced
law bound 8ε^(1/3) and both semantic-coordinate bounds 16Mε^(1/3).
For ε≥1/512 the same estimates hold
trivially with any two-sure root: the displayed bounds already exceed the
maximum possible law and reward discrepancies. If ε=0, the first positive
absorption row exists, its earlier absorption is zero, and zero singleton
probability forces at least two sure quitters. The coupling error is zero.

The n-player version uses s/a≥(1−q₂)^(n−1)/n and a fixed sufficiently
small efficiency threshold, followed by the absolute singleton estimate.
It yields an explicit constant times ε^(1/(n−1)).

The exponent 1/3 is sharp for approximation by a two-sure product-root
law. For the one-root profile q=(1−h,1−h,1−h,1−h), followed by Never,
ε=4(1−h)h³+h⁴. Every law with a sure pair gives zero mass to the two
three-player coalitions that omit one of those pair members. Their combined
mass in the source is 2h(1−h)³. Consequently the law distance to every
two-sure product root is at least 2h(1−h)³, of order ε^(1/3).
This establishes optimality of the uniform exponent for law approximation;
it does not assert sharpness of the cap bound for each reward table.

### Why this is a stronger interface than outcome compactness

The estimate controls every response cap on the same actual source, before
and after a concrete finite replacement. It follows from opponent survival
and a surviving sure quitter, not from continuity of caps in terminal law.
No such continuity holds on arbitrary law strata. The preserved timing bit
is necessary: padding creates singleton deviations that may have been
unavailable at date zero.

## 4. Second theorem draft: linear stability of the pair-only face

Let b(q) be the probability of a nonempty coalition whose size is not two,
and let

    ℓ = ζ + sum_t Lₜ b(q(t)).

This is exactly terminal leakage outside the six pairs. Suppose first
0<ℓ<1/512, and set δ₀=1/256. Choose the first positive-absorption date
with b(q(t))≤δ₀a(q(t)). It exists because otherwise
ℓ≥δ₀(1−ζ), whereas ℓ<1/512 and ζ≤ℓ. Its prefix loss satisfies

    E ≤ ℓ/δ₀ = 256ℓ < 1/2.                          (4)

Write b=b(q(t)). Sorting the root probabilities, the singleton estimate
(1) applies because s≤b. Hence q₁,q₂≥3/4. Also b≤δ₀a≤1/256.
For j=3,4, the event that players 1,2,j all Quit is a nonpair outcome, so

    qⱼ ≤ (16/9)b < 1/4.                              (5)

The event that player 1 alone Quits gives

    b ≥ q₁(1−q₂)(1−q₃)(1−q₄)
      ≥ (27/64)(1−q₂).

Since 1−q₁≤1−q₂, snapping q₁,q₂ to 1 and q₃,q₄ to 0 has total change

    d ≤ [2·64/27 + 2·16/9]b = (224/27)b.             (6)

The selected row's contribution to leakage is Lₜb≤ℓ. By (4), b≤2ℓ,
and therefore

    E+d ≤ [256+448/27]ℓ < 273ℓ.                      (7)

The coupling lemma now compares the source to a pure-pair finite profile,
with the timing bit retained. For ℓ≥1/512, take any pure-pair profile and
use the trivial discrepancy bounds. Combining the two regimes gives

    TV(μ, δ_pair) ≤ 512ℓ,
    ||U(source)−U(pair profile)||∞ ≤ 1024Mℓ,
    ||B(source)−B(pair profile)||∞ ≤ 1024Mℓ.          (8)

The zero-leakage case follows directly by the earliest positive-absorption
argument in the existing rigidity proof. Since TV(μ,δ_pair)=1−μ(pair),
equation (8) proves the linear spread inequality stated at the beginning.

This avoids finite-observation compression and semialgebraic machinery
entirely. The latter remain appropriate for less rigid strata without such
an efficient absorbing row, but are unnecessary for this pair-only test.

## 5. Exact small tests and boundaries

1. A sure pair preceded by any number of empty rows has zero leakage.
   The result returns that pure pair with the required timing bit. Collapsing
   every case to date zero would fail: if player 1's singleton reward is 10
   and its rewards at the pair and remaining singleton are 0, the positive
   prefix permits a deviation worth 10, while the date-zero pair gives 0.
2. Let q=(1,1,h,0) at date zero. Pair mass is 1−h, triple mass h,
   so spread=leakage=h. A bound o(ℓ) is impossible in general. The linear
   order in (8) is therefore sharp even though its constant is very loose.
3. Let players 1 and 2 independently Quit at date zero with probability h;
   if neither Quits, players 3 and 4 surely Quit at date one. Terminal
   probabilities are h² on pair {1,2}, (1−h)² on pair {3,4}, and
   h(1−h) on each singleton {1},{2}. Thus leakage=2h(1−h), and for
   h≤1/2 spread=2h−h². The prefix-selection argument must charge early
   singleton loss; inspecting only the final almost-sure pair is inadequate.
4. The zero-singleton estimate is intentionally weaker: roots with two
   sure quitters and two nontrivial optional quitters have ε=0 and a
   nontrivial four-outcome product law. They cannot be collapsed to a pure
   pair. The output must retain the other two root coordinates.
5. The [STALL fixture](../gpt/STALL.md) obstructs a different, exact global
   finite-calendar cap-preservation claim. Nothing here preserves exact
   semantic pairs away from the low-leakage face or produces an exact
   finite-calendar equilibrium from an arbitrary equilibrium.
6. For an exact strategic screen, give every player reward 0 at pair
   coalitions and reward 1 at all other nonempty coalitions. Every pure-pair
   profile, padded or not, has U=0 and every cap equals 1: a pair member
   declines to Quit, or an outsider joins. Thus the screen below has g=1.
   The all-four-quit profile is an exact equilibrium. This tests the
   localization conclusion and demonstrates why excluding a small law
   stratum cannot by itself imply a global gap.

## 6. Actual incentive consumers and missing production

For terminal exploitability F=max_i(Bᵢ−Uᵢ), the first theorem changes F by
at most 32Mε^(1/3), and the pair theorem by at most 2048Mℓ. The same
source/profile is retained in all these inequalities.

**A finite strategic screen.** There are twelve timing-bit pure-pair
profiles, but only six reward-table checks are needed. For each pair S,
the date-zero profile has exploitability

    g_S = max(0,
      max_{i∈S} [r_i(S\{i})−r_i(S)],
      max_{i∉S} [r_i(S∪{i})−r_i(S)]).

Pair members can leave and outsiders can join; all other pure response
times duplicate following the prescription. Padding leaves U fixed and
replaces each cap by max(sᵢ,Bᵢ), so it can only increase exploitability.
Thus the minimum over twelve profiles equals g=min_pair g_S. Suppose g>0;
this also forces M>0. Then every actual source with pair leakage ℓ satisfies

    F(source) ≥ g − 2048Mℓ.                          (9)

Consequently any source with F(source)<g/2 must have
ℓ>g/(4096M). This is a complete-behavior localization theorem to the
complement of the near-pair region; it is not a global gap theorem.
If some unpadded pure-pair profile has zero exploitability, it is already an actual
terminal equilibrium and the existing terminal-to-uniform endpoint applies.

**Negative route.** If game-specific incentives force spread≥ρ and
ℓ≤AF(source), with ρ,A>0, for every source with F(source)<e₀, then the
linear law bound gives the global lower bound
F(source)≥min(e₀,ρ/(512A)). This is quantitatively stronger
than the survey's unspecified exponent. The same-profile forcing premise
remains missing, as in the existing pair-mass consumers.

**Near-minimum route.** A sequence whose literal singleton and Never masses
tend to zero is quantitatively shadowed by finite sure-core profiles with
the same limiting semantic pair. Its existence is not implied merely by a
positive minimum or a positive singleton-cap margin. The existing exact
zero-singleton face adapter already gives the limit conclusion. The new
estimate is useful only when a later repair/selector tolerates explicit cap
and payoff errors and supplies an actual small-mass source. A finite
near-minimizer is not an exact global minimum; exact-minimum paid-port
consumers cannot be applied without a new robust argument.

**Exact existing-table calibration.** For the VANISH reward table in the
[repair-duality sketch](CODEX_LARCH_DUAL__REPAIR_EXCLUSION_THEORY.md), the
minimum exploitability over all unpadded two-sure product roots is exactly
1/3. This includes continuously mixed optional players, not just pure pairs.
Write p for the pivot's quitting probability. If the pivot is sure, its
prescribed reward is 1 and its Never response gets 2 because another player
is sure, so its debt is 1. Otherwise two nonpivots are sure. Orient that
pair as a→b in the cyclic predecessor order, and write q for the third
nonpivot's quitting probability. The pivot debt is p; player b's
prescribed payoff is zero and its Never gain is

    (1−p)(2−q)−p ≥ 1−2p.

Hence exploitability is at least max(p,1−2p)≥1/3. Taking p=1/3 and all
three nonpivots sure makes all four debts exactly 1/3. Padding cannot lower
this minimum. Applying the cube-root theorem, with the table's M=2, gives
the concrete same-table localization

    E_source ≥ 1/3 − 64(σ+ζ)^(1/3).

Thus every actual VANISH source with E_source<1/6 has
σ+ζ>(1/384)³. This is a fully specified reward consumer of the stability
estimate. Its constant is very loose, and it excludes a law stratum rather
than proving a global gap; VANISH already has UE. Producing small σ+ζ
from low exploitability is neither asserted nor true for this table below
the displayed threshold. The coordinating agent supplied this calculation,
and it was independently checked during this investigation.

## 7. Theory ladder and decision

The small core worth developing is: root defect inequalities; first
efficient-root selection; coupling under deletion of one player; and exact
retiming of finite response categories. Together these yield quantitative
reduction of a behavioral law stratum to a finite strategic model.

The explicit estimates have passed one independent ordinary-math review.
Next test a
reward table where the six-pair screen leaves a positive localization
threshold and compare that threshold against an actual dual/exclusion
inequality on the same laws. Do not improve constants before locating that
consumer. Beyond pair strata, inspect support families whose zero-defect
product roots contain a surviving sure quitter under each tested
intervention; that is the structural reason full caps survive here.

Exact payoff-fiber correction is lower priority. A fixed support block with
uniform positivity and a right inverse for payoff directions can support a
local correction theorem, but the inspected material supplies no reason why
an unresolved near-minimum family retains that regularity. Ordinary implicit
function theory would repackage this missing hypothesis. The present
quantitative collapse is a more concrete output, while explicitly leaving
payoff correction and production of small leakage open.

## Verification

`python scripts/check_docs.py` passed. All displayed small tests are exact
hand calculations. CODEX_LARCH_JOINT independently reviewed the cube-root
and linear estimates, cap coupling, and screen; its six-screen simplification
and range clarifications were incorporated. The coordinating agent also
checked the coupling and screen. No Lean build, trust scan, or numerical
experiment was run. The tracked working tree contains
other concurrent mathematical changes; this investigation edited only this
gitignored conference note.
