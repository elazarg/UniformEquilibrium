import UniformEquilibrium.Quitting.Classification.QuittingPremiumCoreExactRoot
import UniformEquilibrium.Quitting.Root.PositiveOpponentCoalition

/-! # A common leaver for premium traps with signed unprotected premiums -/

noncomputable section

namespace GameTheory

open _root_.Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Only the protected player has nonnegative participant premiums, and every
strict premium trap contains that player. Other participant rewards are signed. -/
def IsCommonQuittingPremiumLeaver
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (player : ι) : Prop :=
  (∀ terminal, player ∈ terminal.val →
    reward (quittingSingletonTerminal player) player ≤ reward terminal player) ∧
  ∀ active, IsQuittingPremiumTrap reward active → player ∈ active

theorem quittingRootQuitPayoff_le_singleton_of_support_participantReward
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (player : ι)
    (hupper : ∀ terminal : {S : Finset ι // S.Nonempty},
      terminal.val ⊆ insert player (quittingPositiveHazardSupport root) →
      player ∈ terminal.val →
        reward terminal player ≤ reward (quittingSingletonTerminal player) player) :
    quittingRootQuitPayoff reward tail root player ≤
      reward (quittingSingletonTerminal player) player := by
  rw [quittingRootQuitPayoff_eq_sum_opponentCoalitionMass]
  rw [← one_mul (reward (quittingSingletonTerminal player) player),
    ← quittingOpponentCoalitionMass_sum_powerset root player, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro coalition _
  by_cases hzero : quittingOpponentCoalitionMass root player coalition = 0
  · simp [hzero]
  · have hpositive : 0 < quittingOpponentCoalitionMass root player coalition :=
      lt_of_le_of_ne (quittingOpponentCoalitionMass_nonneg root player coalition)
        (Ne.symm hzero)
    have hsubset := quittingOpponentCoalition_subset_positiveHazardSupport_of_mass_pos
      root player coalition hpositive
    apply mul_le_mul_of_nonneg_left _ hpositive.le
    simp only [quittingStageCoalitionPayoff, Finset.insert_nonempty, dite_true]
    exact hupper ⟨insert player coalition, Finset.insert_nonempty _ _⟩
      (Finset.insert_subset_insert player hsubset) (Finset.mem_insert_self _ _)

theorem singleton_le_rootQuitPayoff_of_nonnegativeParticipantPremium
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (player : ι)
    (hparticipant : ∀ terminal, player ∈ terminal.val →
      reward (quittingSingletonTerminal player) player ≤ reward terminal player)
    (tail : Payoff ι) (root : ι → PMF Bool) :
    reward (quittingSingletonTerminal player) player ≤
      quittingRootQuitPayoff reward tail root player := by
  rw [quittingRootQuitPayoff_eq_sum_opponentCoalitionMass]
  rw [← one_mul (reward (quittingSingletonTerminal player) player),
    ← quittingOpponentCoalitionMass_sum_powerset root player, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro coalition _
  apply mul_le_mul_of_nonneg_left _
    (quittingOpponentCoalitionMass_nonneg root player coalition)
  simp only [quittingStageCoalitionPayoff, Finset.insert_nonempty, dite_true]
  exact hparticipant ⟨insert player coalition, Finset.insert_nonempty _ _⟩
    (Finset.mem_insert_self _ _)

theorem protected_singleton_le_rootQuitPayoff_of_commonLeaver
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (player : ι)
    (hcommon : IsCommonQuittingPremiumLeaver reward player)
    (tail : Payoff ι) (root : ι → PMF Bool) :
    reward (quittingSingletonTerminal player) player ≤
      quittingRootQuitPayoff reward tail root player :=
  singleton_le_rootQuitPayoff_of_nonnegativeParticipantPremium
    reward player hcommon.1 tail root

/-- A strict leaver chosen from the actual trap support contradicts exact
Nash at a source protecting that player's singleton floor. -/
theorem not_isZeroNash_of_premiumTrapSupport_strictLeave
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (player : ι)
    (tail : Payoff ι) (root : ι → PMF Bool)
    (htrap : IsQuittingPremiumTrap reward (quittingPositiveHazardSupport root))
    (hplayer : player ∈ quittingPositiveHazardSupport root)
    (hleave : ∀ (coalition : Finset ι) (hcoalition : coalition.Nonempty),
      coalition ⊆ (quittingPositiveHazardSupport root).erase player →
        reward ⟨insert player coalition, Finset.insert_nonempty _ _⟩ player <
          reward ⟨coalition, hcoalition⟩ player)
    (hfloor : reward (quittingSingletonTerminal player) player ≤ tail player)
    : ¬IsεQuittingRootNash reward tail 0 root := by
  classical
  intro hnash
  obtain ⟨other, hother, hne⟩ :
      ∃ other ∈ quittingPositiveHazardSupport root, other ≠ player := by
    by_contra hnot
    have hsubset : quittingPositiveHazardSupport root ⊆ {player} := by
      intro other hother
      apply Finset.mem_singleton.mpr
      by_contra hne
      exact hnot ⟨other, hother, hne⟩
    have heq : quittingPositiveHazardSupport root = {player} :=
      Finset.Subset.antisymm hsubset (Finset.singleton_subset_iff.mpr hplayer)
    exact not_isQuittingPremiumTrap_singleton reward player (heq ▸ htrap)
  have hotherPositive : 0 < (root other true).toReal :=
    (Finset.mem_filter.mp hother).2
  obtain ⟨witness, hwitness, hwitnessNonempty, hwitnessPositive⟩ :=
    exists_nonempty_opponentCoalition_of_positive_hazard root player other hne hotherPositive
  have htoggle : ∀ coalition ∈ (Finset.univ.erase player).powerset,
      0 < quittingOpponentCoalitionMass root player coalition → coalition.Nonempty →
        quittingEndpointInsertionToggle reward tail player coalition < 0 := by
    intro coalition hcoalition hmass hnonempty
    have hsubset := quittingOpponentCoalition_subset_positiveHazardSupport_of_mass_pos
      root player coalition hmass
    have hsupportSubset : coalition ⊆ (quittingPositiveHazardSupport root).erase player := by
      intro member hmember
      exact Finset.mem_erase.mpr
        ⟨Finset.ne_of_mem_erase (Finset.mem_powerset.mp hcoalition hmember),
          hsubset hmember⟩
    rw [quittingEndpointInsertionToggle_of_nonempty reward tail player coalition hnonempty]
    exact sub_neg.mpr (hleave coalition hnonempty hsupportSubset)
  have hgapNeg : quittingRootEndpointDifference reward tail root player < 0 := by
    rw [quittingRootEndpointDifference_eq_sum_opponentCoalitionToggle]
    apply Finset.sum_neg'
    · intro coalition hcoalition
      by_cases hzero : quittingOpponentCoalitionMass root player coalition = 0
      · simp [hzero]
      · have hmass : 0 < quittingOpponentCoalitionMass root player coalition :=
          lt_of_le_of_ne (quittingOpponentCoalitionMass_nonneg root player coalition)
            (Ne.symm hzero)
        apply mul_nonpos_of_nonneg_of_nonpos hmass.le
        by_cases hempty : coalition = ∅
        · subst coalition
          rw [quittingEndpointInsertionToggle_empty]
          exact sub_nonpos.mpr hfloor
        · exact (htoggle coalition hcoalition hmass
            (Finset.nonempty_iff_ne_empty.mpr hempty)).le
    · exact ⟨witness, hwitness, mul_neg_of_pos_of_neg hwitnessPositive
        (htoggle witness hwitness hwitnessPositive hwitnessNonempty)⟩
  have hpositive : 0 < (root player true).toReal := (Finset.mem_filter.mp hplayer).2
  have hendpoint :=
    (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash reward tail root).mpr hnash
  have hgapNonneg : 0 ≤ quittingRootEndpointDifference reward tail root player :=
    nonneg_of_mul_nonneg_left
      (by simpa [mul_comm] using (hendpoint player).2) hpositive
  exact (not_lt_of_ge hgapNonneg) hgapNeg

/-- The common-player criterion is a thin instance of the literal active
support leaver contradiction. -/
theorem not_premiumTrap_support_of_commonLeaver_strictLeave
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (player : ι)
    (hcommon : IsCommonQuittingPremiumLeaver reward player)
    (hleave : ∀ (coalition : Finset ι) (hcoalition : coalition.Nonempty),
      coalition ⊆ (quittingPremiumCore reward).erase player →
        reward ⟨insert player coalition, Finset.insert_nonempty _ _⟩ player <
          reward ⟨coalition, hcoalition⟩ player)
    (tail : Payoff ι)
    (hfloor : reward (quittingSingletonTerminal player) player ≤ tail player)
    (root : ι → PMF Bool) (hnash : IsεQuittingRootNash reward tail 0 root) :
    ¬IsQuittingPremiumTrap reward (quittingPositiveHazardSupport root) := by
  intro htrap
  apply not_isZeroNash_of_premiumTrapSupport_strictLeave reward player tail root htrap
    (hcommon.2 _ htrap) _ hfloor hnash
  intro coalition hnonempty hsubset
  apply hleave coalition hnonempty
  exact hsubset.trans (Finset.erase_subset_erase player
    (MathUE.IsFiniteCoalitionPremiumTrap.subset_core htrap))

/-- Signed rewards require only a nontrap actual support to obtain one weak
singleton sublevel. No other coordinate floor is inferred. -/
theorem exists_successor_le_singleton_of_exactRoot_nontrap_support
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool)
    (hnash : IsεQuittingRootNash reward tail 0 root)
    (habsorption : 0 < quittingRootAbsorptionMass root)
    (hnot : ¬IsQuittingPremiumTrap reward (quittingPositiveHazardSupport root)) :
    ∃ other, quittingRootSuccessorPayoff reward tail root other ≤
      reward (quittingSingletonTerminal other) other := by
  have hactive : (quittingPositiveHazardSupport root).Nonempty := by
    obtain ⟨other, hother⟩ :=
      (quittingRootAbsorptionMass_pos_iff_exists_quitProbability_pos root).mp habsorption
    exact ⟨other, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hother⟩⟩
  obtain ⟨other, hother, hnonpositive⟩ :=
    (MathUE.not_isFiniteCoalitionPremiumTrap_iff
      (HasPositiveOwnQuittingPremium reward) _ hactive).mp hnot
  refine ⟨other, ?_⟩
  have hpositive : 0 < (root other true).toReal := (Finset.mem_filter.mp hother).2
  have hquitNe : root other true ≠ 0 := by
    intro hzero
    rw [hzero] at hpositive
    norm_num at hpositive
  have hendpoint :=
    (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash reward tail root).mpr hnash
  rw [quittingRootSuccessorPayoff_eq_quitPayoff_of_isZeroEndpointNash hendpoint other hquitNe]
  apply quittingRootQuitPayoff_le_singleton_of_support_participantReward
  intro terminal hsubset hmember
  apply le_of_not_gt
  intro hpremium
  apply hnonpositive terminal.val _ hmember ⟨terminal.property, hpremium⟩
  simpa [Finset.insert_eq_of_mem hother] using hsubset

/-- Signed protected return gives a protected floor and some weak sublevel
coordinate. It does not assert floors or equality for every other player. -/
theorem exactRootSuccessor_protected_sublevel_of_commonLeaver_strictLeave
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (player : ι)
    (hcommon : IsCommonQuittingPremiumLeaver reward player)
    (hleave : ∀ (coalition : Finset ι) (hcoalition : coalition.Nonempty),
      coalition ⊆ (quittingPremiumCore reward).erase player →
        reward ⟨insert player coalition, Finset.insert_nonempty _ _⟩ player <
          reward ⟨coalition, hcoalition⟩ player)
    (tail : Payoff ι)
    (hfloor : reward (quittingSingletonTerminal player) player ≤ tail player)
    (root : ι → PMF Bool) (hnash : IsεQuittingRootNash reward tail 0 root)
    (habsorption : 0 < quittingRootAbsorptionMass root) :
    reward (quittingSingletonTerminal player) player ≤
        quittingRootSuccessorPayoff reward tail root player ∧
      ∃ other, quittingRootSuccessorPayoff reward tail root other ≤
        reward (quittingSingletonTerminal other) other := by
  refine ⟨(protected_singleton_le_rootQuitPayoff_of_commonLeaver reward player
    hcommon tail root).trans
      (quittingRootQuitPayoff_le_successor_of_isZeroNash reward tail root player hnash), ?_⟩
  exact exists_successor_le_singleton_of_exactRoot_nontrap_support reward tail root
    hnash habsorption (not_premiumTrap_support_of_commonLeaver_strictLeave
      reward player hcommon hleave tail hfloor root hnash)

end GameTheory
