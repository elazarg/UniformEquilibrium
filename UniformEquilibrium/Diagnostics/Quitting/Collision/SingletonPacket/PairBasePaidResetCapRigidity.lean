/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import
  UniformEquilibrium.Diagnostics.Quitting.Collision.SingletonPacket.PairBasePaidResetPayoffAlignment
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticFixedLawCapRigidity

/-!
# Complete semantic alignment of the Fin4 pair-base paid reset

The literal pair-base target has two sure quitters and both complementary
coordinates are solved.  Fixed-law cap rigidity therefore identifies every
returned debt minimizer with the complete semantic pair of that literal
stationary target, not merely with its prescribed payoff vector.

Rewriting the existing dynamic reset dispatch by this equality gives its
strict-child/all-Continue alternative literally at the original paid target.
This does not make the strict decrease renewable and does not eliminate the
all-Continue branch.
-/

noncomputable section

namespace GameTheory

open Finset

namespace FinFourPairBasePaidResetTarget

/-- A fixed-law reset dispatch from the Fin4 pair-base target returns that
target's complete semantic pair, including every unrestricted behavioral-cap
coordinate. -/
theorem returned_eq_of_fixedLawResetDispatch
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {witness : QuittingTerminalExploitabilityWitness reward}
    {minimum : QuittingTerminalSemanticPair (Fin 4)}
    {owner baseFirst baseSecond : Fin 4}
    (target : FinFourPairBasePaidResetTarget reward witness owner
      baseFirst baseSecond)
    {returned : QuittingTerminalSemanticPair (Fin 4)}
    (dispatch : QuittingFixedLawResetDispatch (reward := reward)
      minimum target.semanticPair target.mass owner baseFirst returned) :
    returned = target.semanticPair := by
  let base : Finset (Fin 4) := {baseFirst, baseSecond}
  let root := quittingPersistentBaseRoot base
    (finFourPairBaseComplement base) target.localization.point
  have hprofile : quittingRootThenContinuationProfile reward root
      target.profile = target.profile := by
    rw [show target.profile = quittingStationaryProfile reward root by rfl]
    exact quittingRootThenContinuationProfile_stationary reward root
  have hcard : 2 ≤ base.card := by
    simp [base, target.base_ne]
  have hsure : ∀ member ∈ base, root member = PMF.pure true := by
    intro member hmember
    exact quittingPersistentBaseRoot_apply_of_mem_base base
      (finFourPairBaseComplement base) target.localization.point hmember
  have hjoint :
      (returned, quittingTerminalOutcomeMass reward
        (quittingRootThenContinuationProfile reward root target.profile)) ∈
          quittingTerminalSemanticLawCarrier reward := by
    rw [hprofile]
    exact dispatch.joint
  have hsolved : ∀ player, player ∉ base →
      let source := quittingTerminalSemanticPair reward
        (quittingRootThenContinuationProfile reward root target.profile)
      source.2 player = source.1 player := by
    intro player hplayer
    have hfree : player ∈ finFourPairBaseComplement base := by
      simp [finFourPairBaseComplement, hplayer]
    have hdebt := (target.localization.free_solved player hfree).1
    rw [hprofile]
    change quittingTerminalSemanticDebt target.semanticPair player = 0 at hdebt
    change target.semanticPair.2 player = target.semanticPair.1 player
    unfold quittingTerminalSemanticDebt at hdebt
    exact sub_eq_zero.mp hdebt
  have hreturnedDebt :
      let source := quittingTerminalSemanticPair reward
        (quittingRootThenContinuationProfile reward root target.profile)
      quittingTerminalSemanticDebtSum returned ≤
        quittingTerminalSemanticDebtSum source := by
    rw [hprofile]
    exact dispatch.target_ge
  have hunique :=
    quittingSureBaseRoot_unique_fixedLawDebtMinimizer_of_complement_solved
      reward base hcard root hsure target.profile returned hjoint hsolved
        hreturnedDebt
  rw [hprofile] at hunique
  exact hunique

/-- The literal pair-base target minimizes total semantic debt throughout its
complete-law fibre. -/
theorem debtSum_le_of_sameLaw
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {witness : QuittingTerminalExploitabilityWitness reward}
    {owner baseFirst baseSecond : Fin 4}
    (target : FinFourPairBasePaidResetTarget reward witness owner
      baseFirst baseSecond)
    (candidate : QuittingTerminalSemanticPair (Fin 4))
    (hcandidate : (candidate, target.mass) ∈
      quittingTerminalSemanticLawCarrier reward) :
    quittingTerminalSemanticDebtSum target.semanticPair ≤
      quittingTerminalSemanticDebtSum candidate := by
  let base : Finset (Fin 4) := {baseFirst, baseSecond}
  let root := quittingPersistentBaseRoot base
    (finFourPairBaseComplement base) target.localization.point
  have hprofile : quittingRootThenContinuationProfile reward root
      target.profile = target.profile := by
    rw [show target.profile = quittingStationaryProfile reward root by rfl]
    exact quittingRootThenContinuationProfile_stationary reward root
  have hcard : 2 ≤ base.card := by
    simp [base, target.base_ne]
  have hsure : ∀ member ∈ base, root member = PMF.pure true := by
    intro member hmember
    exact quittingPersistentBaseRoot_apply_of_mem_base base
      (finFourPairBaseComplement base) target.localization.point hmember
  have hjoint :
      (candidate, quittingTerminalOutcomeMass reward
        (quittingRootThenContinuationProfile reward root target.profile)) ∈
          quittingTerminalSemanticLawCarrier reward := by
    rw [hprofile]
    exact hcandidate
  have hsolved : ∀ player, player ∉ base →
      let source := quittingTerminalSemanticPair reward
        (quittingRootThenContinuationProfile reward root target.profile)
      source.2 player = source.1 player := by
    intro player hplayer
    have hfree : player ∈ finFourPairBaseComplement base := by
      simp [finFourPairBaseComplement, hplayer]
    have hdebt := (target.localization.free_solved player hfree).1
    rw [hprofile]
    change quittingTerminalSemanticDebt target.semanticPair player = 0 at hdebt
    change target.semanticPair.2 player = target.semanticPair.1 player
    unfold quittingTerminalSemanticDebt at hdebt
    exact sub_eq_zero.mp hdebt
  have hminimum :=
    quittingSureBaseRoot_debt_le_sameLaw_of_complement_solved
      reward base hcard root hsure target.profile candidate hjoint hsolved
  rw [hprofile] at hminimum
  exact hminimum

/-- A strict semantic-debt child of the literal pair-base target cannot keep
the target's complete terminal law. -/
theorem strictDebtPrefix_lawPrefix_ne_mass
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {witness : QuittingTerminalExploitabilityWitness reward}
    {owner baseFirst baseSecond : Fin 4}
    (target : FinFourPairBasePaidResetTarget reward witness owner
      baseFirst baseSecond)
    (root : Fin 4 → PMF Bool)
    (hstrict : quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPrefix reward root target.semanticPair) <
      quittingTerminalSemanticDebtSum target.semanticPair)
    (hjoint : (quittingTerminalSemanticPrefix reward root target.semanticPair,
        quittingTerminalOutcomeLawPrefix root target.mass) ∈
      quittingTerminalSemanticLawCarrier reward) :
    quittingTerminalOutcomeLawPrefix root target.mass ≠ target.mass := by
  intro hlaw
  have hjointTarget :
      (quittingTerminalSemanticPrefix reward root target.semanticPair,
        target.mass) ∈ quittingTerminalSemanticLawCarrier reward := by
    rw [← hlaw]
    exact hjoint
  exact (not_lt_of_ge (target.debtSum_le_of_sameLaw _ hjointTarget) hstrict)

/-- After complete semantic alignment, the checked dynamic reset alternative
is literally based at the original pair-base stationary target.  Its strict
child also leaves the target's complete terminal-law fibre. -/
theorem fixedLawReset_absorbingChild_or_allContinueFace
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {witness : QuittingTerminalExploitabilityWitness reward}
    {minimum : QuittingTerminalSemanticPair (Fin 4)}
    {owner baseFirst baseSecond : Fin 4}
    (target : FinFourPairBasePaidResetTarget reward witness owner
      baseFirst baseSecond)
    {returned : QuittingTerminalSemanticPair (Fin 4)}
    (dispatch : QuittingFixedLawResetDispatch (reward := reward)
      minimum target.semanticPair target.mass owner baseFirst returned) :
    (∃ root : Fin 4 → PMF Bool,
      IsεQuittingRootNash reward target.semanticPair.2 0 root ∧
      0 < quittingRootAbsorptionMass root ∧
      0 < quittingStationaryContinueMass root ∧
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPrefix reward root target.semanticPair) <
        quittingTerminalSemanticDebtSum target.semanticPair ∧
      quittingTerminalOutcomeLawPrefix root target.mass ≠ target.mass ∧
      (quittingTerminalSemanticPrefix reward root target.semanticPair,
          quittingTerminalOutcomeLawPrefix root target.mass) ∈
        quittingTerminalSemanticLawCarrier reward ∧
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPrefix reward root target.semanticPair)
            owner = 0 ∧
      0 < quittingTerminalOpponentIncidenceMass owner baseFirst
        (quittingTerminalOutcomeLawPrefix root target.mass)) ∨
    (IsεQuittingRootNash reward target.semanticPair.2 0
        (quittingAllContinueRoot : Fin 4 → PMF Bool) ∧
      quittingTerminalSemanticPrefix reward quittingAllContinueRoot
        target.semanticPair = target.semanticPair) := by
  have heq := target.returned_eq_of_fixedLawResetDispatch dispatch
  rcases dispatch.dynamic_exit with hchild | hstall
  · rw [heq] at hchild
    obtain ⟨root, hnash, habsorption, hcontinue, hstrict, hjoint,
        hreset, hincidence⟩ := hchild
    exact Or.inl ⟨root, hnash, habsorption, hcontinue, hstrict,
      target.strictDebtPrefix_lawPrefix_ne_mass root hstrict hjoint,
      hjoint, hreset, hincidence⟩
  · exact Or.inr (by simpa only [heq] using hstall)

end FinFourPairBasePaidResetTarget

end GameTheory
