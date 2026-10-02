# Bounded review of the added converse and composite equivalence

Reviewer: `CODEX_RENY`. Verdict: **PASS** for the added necessity,
quantifier strengthening, and composite statement in
[`CODEX_SKEPTIC__FINITE_MENU_EARLY_ABSORPTION_EQUIVALENCE.md`](../notes/CODEX_SKEPTIC__FINITE_MENU_EARLY_ABSORPTION_EQUIVALENCE.md).
I read that note completely. This is a bounded review of its added material,
not a third review of the original completion proof and not an export gate.
The original completion is separately covered by my
[`COMPLETION__BY_CODEX_RENY.md`](COMPLETION__BY_CODEX_RENY.md) and SKEPTIC's
independent original-first review.

## 1. Converse and quantifier order

Fix any nonempty finite player set, arbitrary bounded real rewards, zero
Never payoff, and independent privately randomized stopping laws. Assume
UE exists and sⱼ=rⱼ({j})>0 for one player j. The checked conclusion is

    ∀e>0, ∀H≥1, ∀ρ>0, ∀N₀≥0,
      ∃N≥max(H,N₀), ∃p on {0,…,N−1,Never},
        p is finite-menu e-Nash and R_p(N−H)<ρ.

The proof actually obtains the stronger E(p)<e bound for its selected
source, while the definition of EA correctly does NOT require that field.

For an arbitrary full profile p, move only j's own Never atom to a date k.
The all-Never event gains sⱼ, weighted by its original probability A(p).
All remaining changed events require j originally Never and an opponent's
finite quit at or after k. Their probability tends to zero. Bounded rewards
therefore give limiting gain sⱼA(p), hence

    dⱼ(p)≥sⱼA(p),       A(p)≤E(p)/sⱼ.

This is a unilateral update, not a correlated plan, and does not claim the
limiting gain is attained at a finite date.

For a FIXED full profile, move all finite marginal atoms at dates ≥L to
Never. Let θ_L be the sum of the moved masses. Then θ_L→0. The product
coupling changes prescribed payoff by at most 2Mθ_L. Against any fixed
complete unilateral replacement, only opponent coordinates are coupled,
giving the same bound uniformly over ALL replacements. Thus every cap
changes by at most 2Mθ_L, every debt by at most 4Mθ_L, and

    |E(pᴸ)−E(p)|≤4Mθ_L.

This is ordinary discrete tightness of the selected source, not a uniform
family tightness assumption or an estimate by joint survival alone.

For b=min(e,sⱼρ)/2, choose a full approximate Nash profile with E<b/2,
then L≥1 with 4Mθ_L<b/2. Thus E(pᴸ)<b<e and, applying the Never inequality
to pᴸ itself, A(pᴸ)<ρ. Finally choose N≥max(L+H,N₀). All its finite atoms
are before L, so R_pᴸ(N−H)=A(pᴸ). Its small FULL error proves Nash on the
enlarged finite menu. This is the correct order: truncation preserving full
error precedes deadline enlargement. An arbitrary finite-menu near-Nash law
could not be padded this way.

Every requested e,H,ρ,N₀ is fixed BEFORE selecting the source and deadline.
No consistency across separate requests is asserted or needed. The N₀
strengthening therefore passes without an inverse-limit or component-
selection premise.

## 2. Exact composite theorem

The previously independently reviewed completion gives EA⇒UE for every
finite nonempty game, with no singleton sign assumption. Its all-error
terminal approximants feed the existing fixed-target uniform-payoff
selection theorem; a payoff varying with accuracy is not substituted for
the repository's uniform-payoff conclusion.

Combining that implication with Section 1 gives UE⇔EA whenever some own
singleton is positive. The complementary case is genuinely trivial:
if every sᵢ≤0, all Never has payoff zero, and any unilateral deviation can
only cause singleton {i}, yielding nonpositive payoff, or keep Never at
zero. The same inequality holds at every finite horizon, so all Never
is a uniform equilibrium directly.

Equivalently, without any sign restriction the exact composite statement is

    UE(r) ⇔ [ (∀i, sᵢ≤0) OR EA(r) ].

Consequently the arbitrary-finite quitting conjecture reduces to producing
EA on positive-singleton tables. This is a reduction, not a proof that EA
holds there. The one-player negative-singleton example correctly shows that
the disjunct cannot be deleted: UE may hold while EA fails.

## 3. Narrow source match and limits of this review

The declaration
`quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
in `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`
has exactly the target-free UE existence versus all-positive-error terminal
approximation quantifiers used here. I checked its statement under the
file's imports. The related
`singletonReward_le_nashError_div_never` in
`UniformEquilibrium/Quitting/Classification/Existence/ApproximateEquilibriumVanishingNeverAlternative.lean`
matches the positive-Never consequence for global root-sequence Nash data.
The note's direct Never-mass argument proves the slightly more explicit
coordinate-debt inequality used in this converse. The truncation estimate
was checked directly by the product coupling, so no unproved continuity of
the unrestricted cap at weak stopping-law limits is required.

No mathematical objection remains in the added converse or assembled
equivalence. This review does not newly audit the source's qualification
discussion, claim unrestricted source existence, count either original
completion review twice, or authorize an export. No Lean file was changed
or built.
