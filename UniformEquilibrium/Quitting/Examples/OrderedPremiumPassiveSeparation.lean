import UniformEquilibrium.Quitting.Classification.NonnegativeProductLowSupportPeelingConverse
import UniformEquilibrium.Quitting.Classification.QuittingPremiumReward
import UniformEquilibrium.Quitting.Classification.Existence.AcyclicSoloPreemption
import UniformEquilibrium.Quitting.Classification.Existence.QuittingPremiumSupportPeelingUniformPayoff

/-! # Zero premiums and the independent passive solo-preemption pattern -/

noncomputable section

namespace GameTheory.OrderedPremiumPassiveSeparation

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Replace every passive singleton reward by the receiving player's own
singleton minus one. Every participant reward is retained literally. -/
def lowerPassiveSingletons
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    {S : Finset ι // S.Nonempty} → Payoff ι := fun terminal player =>
  if terminal.val.card = 1 ∧ player ∉ terminal.val
  then reward (quittingSingletonTerminal player) player - 1
  else reward terminal player

omit [Fintype ι] in
theorem lowerPassiveSingletons_participant
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (terminal : {S : Finset ι // S.Nonempty}) (player : ι) (hmem : player ∈ terminal.val) :
    lowerPassiveSingletons reward terminal player = reward terminal player := by
  simp [lowerPassiveSingletons, hmem]

omit [Fintype ι] in
@[simp] theorem lowerPassiveSingletons_singleton
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (player : ι) :
    lowerPassiveSingletons reward (quittingSingletonTerminal player) player =
      reward (quittingSingletonTerminal player) player := by
  apply lowerPassiveSingletons_participant
  simp [quittingSingletonTerminal]

omit [Fintype ι] in
theorem lowerPassiveSingletons_nonnegativePremium_iff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    HasNonnegativeOwnQuittingPremium (lowerPassiveSingletons reward) ↔
      HasNonnegativeOwnQuittingPremium reward := by
  constructor <;> intro h terminal player hmem
  · simpa only [lowerPassiveSingletons_singleton,
      lowerPassiveSingletons_participant reward terminal player hmem] using h terminal player hmem
  · simpa only [lowerPassiveSingletons_singleton,
      lowerPassiveSingletons_participant reward terminal player hmem] using h terminal player hmem

omit [Fintype ι] in
theorem lowerPassiveSingletons_weakSupportPeeling_iff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    HasWeakQuittingPremiumSupportPeeling (lowerPassiveSingletons reward) ↔
      HasWeakQuittingPremiumSupportPeeling reward := by
  rw [hasWeakQuittingPremiumSupportPeeling_iff, hasWeakQuittingPremiumSupportPeeling_iff]
  constructor <;> intro h active hactive
  · obtain ⟨chosen, hchosen, hlow⟩ := h active hactive
    refine ⟨chosen, hchosen, ?_⟩
    intro terminal hterminal hsubset hmem
    simpa only [lowerPassiveSingletons_singleton,
      lowerPassiveSingletons_participant reward ⟨terminal, hterminal⟩ chosen hmem] using
        hlow terminal hterminal hsubset hmem
  · obtain ⟨chosen, hchosen, hlow⟩ := h active hactive
    refine ⟨chosen, hchosen, ?_⟩
    intro terminal hterminal hsubset hmem
    simpa only [lowerPassiveSingletons_singleton,
      lowerPassiveSingletons_participant reward ⟨terminal, hterminal⟩ chosen hmem] using
        hlow terminal hterminal hsubset hmem

omit [Fintype ι] in
/-- Every pair of distinct players now has both strict solo-preemption
directions, while the entire own-premium pattern is unchanged. -/
theorem lowerPassiveSingletons_preemption_edge
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {owner other : ι} (hne : other ≠ owner) :
    QuittingAugmentedSoloPreemptionEdge (lowerPassiveSingletons reward)
      (some owner) (some other) := by
  refine ⟨hne, ?_⟩
  simp [quittingSoloReward, lowerPassiveSingletons, quittingSingletonTerminal, hne]

theorem lowerPassiveSingletons_not_acyclic
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) :
    ¬ IsQuittingAugmentedSoloPreemptionAcyclic (lowerPassiveSingletons reward) := by
  intro hacyclic
  apply hacyclic
  refine ⟨{
    period := 2
    period_pos := by decide
    vertex := fun time => some (if time % 2 = 0 then 0 else 1)
    vertex_periodic := ?_
    edge := ?_ }⟩
  · intro time
    simp
  · intro time
    by_cases heven : time % 2 = 0
    · have hnext : (time + 1) % 2 ≠ 0 := by omega
      simp only [heven, hnext, if_true, if_false]
      exact lowerPassiveSingletons_preemption_edge reward (by decide)
    · have hnext : (time + 1) % 2 = 0 := by omega
      simp only [heven, hnext, if_true, if_false]
      exact lowerPassiveSingletons_preemption_edge reward (by decide)

/-- The zero-own-premium family keeps every passive coalition entry free. -/
def zeroPremiumReward (singleton : Payoff ι)
    (passive : {S : Finset ι // S.Nonempty} → Payoff ι) :
    {S : Finset ι // S.Nonempty} → Payoff ι := rewardOfOwnPremium singleton 0 passive

omit [Fintype ι] in
theorem zeroPremium_participant (singleton : Payoff ι)
    (passive : {S : Finset ι // S.Nonempty} → Payoff ι)
    (terminal : {S : Finset ι // S.Nonempty}) (player : ι) (hmem : player ∈ terminal.val) :
    zeroPremiumReward singleton passive terminal player = singleton player := by
  simp [zeroPremiumReward, rewardOfOwnPremium, hmem]

omit [Fintype ι] in
@[simp] theorem zeroPremium_singleton (singleton : Payoff ι)
    (passive : {S : Finset ι // S.Nonempty} → Payoff ι) (player : ι) :
    zeroPremiumReward singleton passive (quittingSingletonTerminal player) player =
      singleton player := by
  apply zeroPremium_participant
  simp [quittingSingletonTerminal]

omit [Fintype ι] in
theorem zeroPremium_weakSupportPeeling (singleton : Payoff ι)
    (passive : {S : Finset ι // S.Nonempty} → Payoff ι) :
    HasWeakQuittingPremiumSupportPeeling (zeroPremiumReward singleton passive) := by
  apply (hasWeakQuittingPremiumSupportPeeling_iff _).mpr
  intro active hactive
  obtain ⟨chosen, hchosen⟩ := hactive
  refine ⟨chosen, hchosen, ?_⟩
  intro terminal hterminal _ hmem
  rw [zeroPremium_singleton,
    zeroPremium_participant singleton passive ⟨terminal, hterminal⟩ chosen hmem]

theorem zeroPremium_nonnegativeSingleton_uniformPayoff [Nonempty ι]
    (singleton : Payoff ι) (passive : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hnonneg : ∀ player, 0 ≤ singleton player) :
    ∃ payoff : Payoff ι,
      (quittingGame (zeroPremiumReward singleton passive)).IsUniformEquilibriumPayoff
        none payoff := by
  apply exists_uniformEquilibriumPayoff_of_weakPremiumSupportPeeling
    (zeroPremiumReward singleton passive)
  · simpa only [zeroPremium_singleton] using hnonneg
  · exact zeroPremium_weakSupportPeeling singleton passive

omit [Fintype ι] in
/-- The positive-premium rule holds for the literal supplied rank, not only
for an existentially selected replacement order. -/
theorem zeroPremium_playerRanking_rule (singleton : Payoff ι)
    (passive : {S : Finset ι // S.Nonempty} → Payoff ι) (rank : ι → ℕ)
    (terminal : {S : Finset ι // S.Nonempty}) (player : ι) (hmem : player ∈ terminal.val)
    (hpositive : zeroPremiumReward singleton passive (quittingSingletonTerminal player) player <
      zeroPremiumReward singleton passive terminal player) :
    ∃ earlier ∈ terminal.val, rank earlier < rank player := by
  rw [zeroPremium_singleton, zeroPremium_participant singleton passive terminal player hmem]
    at hpositive
  exact (lt_irrefl _ hpositive).elim

/-- Every supplied injective cardinality-bounded player order works on the
zero-own-premium family, including arbitrary signed passive rewards. -/
theorem zeroPremium_every_playerRanking (singleton : Payoff ι)
    (passive : {S : Finset ι // S.Nonempty} → Payoff ι)
    (rank : ι → ℕ) (hinjective : Function.Injective rank)
    (hbound : ∀ player, rank player < Fintype.card ι) :
    HasPositiveQuittingPremiumPlayerRanking (zeroPremiumReward singleton passive) := by
  apply (hasPositiveQuittingPremiumPlayerRanking_iff _).mpr
  refine ⟨rank, hinjective, hbound, ?_⟩
  intro terminal hterminal player hmem hpositive
  exact zeroPremium_playerRanking_rule singleton passive rank ⟨terminal, hterminal⟩
    player hmem hpositive

/-- If all singleton rewards are zero, all-Never is already exact against
every behavioral replacement, independently of the passive reward table. -/
theorem zeroPremium_zeroSingleton_allContinue_exact
    (passive : {S : Finset ι // S.Nonempty} → Payoff ι) :
    (quittingGame (zeroPremiumReward 0 passive)).IsεAsymptoticNash
      (quittingTerminalPayoff (zeroPremiumReward 0 passive)) 0
      (quittingAlwaysContinueProfile (zeroPremiumReward 0 passive)) := by
  apply isZeroAsymptoticNash_quittingAlwaysContinue_of_zeroSolo
  intro player
  simp

end GameTheory.OrderedPremiumPassiveSeparation
