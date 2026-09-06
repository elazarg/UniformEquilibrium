import UniformEquilibrium.Quitting.Classification.Existence.PerfectAbsorbingRow
import UniformEquilibrium.Quitting.Root.OpponentCoalitionPayoff

/-! # Supportwise weighted quitting premiums

One nonnegative weighting for each active support controls participant-only
premiums on all contained coalitions. The product identity yields a low active
Quit endpoint without Nash, continuation, or passive-reward assumptions.
-/

noncomputable section
namespace GameTheory

open Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Every nonempty support admits one normalized nonnegative weighting whose
participant-only premium is nonpositive on every contained coalition. -/
def IsSupportwiseBalancedQuittingPremiumTable
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Prop :=
  ∀ (active : Finset ι), active.Nonempty →
    ∃ weight : ι → ℝ,
      (∀ player, 0 ≤ weight player) ∧
      (∀ player, player ∉ active → weight player = 0) ∧
      (∑ player ∈ active, weight player) = 1 ∧
      ∀ (terminal : Finset ι) (hterminal : terminal.Nonempty),
        terminal ⊆ active →
        (∑ player ∈ terminal, weight player *
          (reward ⟨terminal, hterminal⟩ player -
            reward (quittingSingletonTerminal player) player)) ≤ 0

private theorem quitProbability_mul_opponentCoalitionMass
    (root : ι → PMF Bool) (who : ι) (coalition : Finset ι)
    (hcoalition : coalition ⊆ Finset.univ.erase who) :
    (root who true).toReal *
        quittingOpponentCoalitionMass root who coalition =
      quittingRootCoalitionMass root (insert who coalition) := by
  unfold quittingOpponentCoalitionMass quittingRootCoalitionMass
    quittingRootQuitRates coalitionMass
  have hnot : who ∉ coalition := fun hmem =>
    (Finset.mem_erase.mp (hcoalition hmem)).1 rfl
  have hdiff : Finset.univ \ insert who coalition =
      Finset.univ.erase who \ coalition := by
    ext player
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_erase]
    tauto
  rw [Finset.prod_insert hnot, Finset.compl_eq_univ_sdiff, hdiff]
  simp_rw [pmfBool_false_toReal]
  ring

omit [Fintype ι] in
private theorem sum_bernoulliMass_powerset
    (root : ι → PMF Bool) (carrier : Finset ι) :
    (∑ coalition ∈ carrier.powerset,
      (∏ player ∈ coalition, (root player true).toReal) *
        ∏ player ∈ carrier \ coalition, (root player false).toReal) = 1 := by
  rw [← Finset.prod_add]
  apply Finset.prod_eq_one
  intro player _
  simpa [add_comm] using
    quittingRoot_continueProbability_add_quitProbability root player

/-- The exact product identity, valid also at zero and sure-Quit coordinates. -/
theorem quittingQuitProbability_mul_quitPremium_eq_sum_coalitionPremium
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι) :
    (root who true).toReal *
        (quittingRootQuitPayoff reward 0 root who -
          reward (quittingSingletonTerminal who) who) =
      ∑ coalition ∈ (Finset.univ.erase who).powerset,
        quittingRootCoalitionMass root (insert who coalition) *
          (reward ⟨insert who coalition,
              Finset.insert_nonempty who coalition⟩ who -
            reward (quittingSingletonTerminal who) who) := by
  rw [quittingRootQuitPayoff_eq_sum_opponentCoalitionMass]
  rw [mul_sub, Finset.mul_sum]
  simp only [quittingStageCoalitionPayoff,
    Finset.insert_nonempty, dite_true]
  have hmass : (∑ coalition ∈ (Finset.univ.erase who).powerset,
      quittingOpponentCoalitionMass root who coalition) = 1 := by
    exact sum_bernoulliMass_powerset root (Finset.univ.erase who)
  have hconstant : (root who true).toReal *
      reward (quittingSingletonTerminal who) who =
      ∑ coalition ∈ (Finset.univ.erase who).powerset,
        (root who true).toReal *
          quittingOpponentCoalitionMass root who coalition *
            reward (quittingSingletonTerminal who) who := by
    calc
      _ = (root who true).toReal *
          (∑ coalition ∈ (Finset.univ.erase who).powerset,
            quittingOpponentCoalitionMass root who coalition) *
            reward (quittingSingletonTerminal who) who := by rw [hmass]; ring
      _ = _ := by rw [Finset.mul_sum, Finset.sum_mul]
  rw [hconstant]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro coalition hcoalition
  have hsubset := Finset.mem_powerset.mp hcoalition
  rw [← quitProbability_mul_opponentCoalitionMass root who coalition hsubset]
  ring

/-- The product identity indexed by the nonempty terminal coalitions carrying
the selected player. -/
theorem quittingQuitProbability_mul_quitPremium_eq_sum_terminalPremium
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι) :
    (root who true).toReal *
        (quittingRootQuitPayoff reward 0 root who -
          reward (quittingSingletonTerminal who) who) =
      ∑ terminal ∈ Finset.univ.filter (fun terminal => who ∈ terminal.val),
        quittingRootCoalitionMass root terminal.val *
          (reward terminal who -
            reward (quittingSingletonTerminal who) who) := by
  rw [quittingQuitProbability_mul_quitPremium_eq_sum_coalitionPremium]
  symm
  apply Finset.sum_bij (fun terminal _ => terminal.val.erase who)
  · intro terminal hterminal
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hterminal
    apply Finset.mem_powerset.mpr
    intro player hplayer
    exact Finset.mem_erase.mpr
      ⟨(Finset.mem_erase.mp hplayer).1, Finset.mem_univ player⟩
  · intro first hfirst second hsecond heq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hfirst hsecond
    apply Subtype.ext
    rw [← Finset.insert_erase hfirst, ← Finset.insert_erase hsecond, heq]
  · intro coalition hcoalition
    have hsubset := Finset.mem_powerset.mp hcoalition
    have hnot : who ∉ coalition := fun hmem =>
      (Finset.mem_erase.mp (hsubset hmem)).1 rfl
    let terminal : {S : Finset ι // S.Nonempty} :=
      ⟨insert who coalition, Finset.insert_nonempty who coalition⟩
    refine ⟨terminal, ?_, ?_⟩
    · simp [terminal]
    · simp [terminal, hnot]
  · intro terminal hterminal
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hterminal
    have hinsert : insert who (terminal.val.erase who) = terminal.val :=
      Finset.insert_erase hterminal
    simp only [hinsert]

/-- Supportwise balance makes the active weighted aggregate of endpoint
premiums nonpositive at every product root. -/
theorem weighted_quittingRootQuitPremium_sum_nonpos
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hbalanced : IsSupportwiseBalancedQuittingPremiumTable reward)
    (root : ι → PMF Bool)
    (active : Finset ι)
    (hactive : ∀ player, player ∈ active ↔ 0 < (root player true).toReal)
    (hne : active.Nonempty) :
    ∃ weight : ι → ℝ,
      (∀ player, 0 ≤ weight player) ∧
      (∑ player ∈ active, weight player) = 1 ∧
      (∑ player ∈ active, weight player * (root player true).toReal *
        (quittingRootQuitPayoff reward 0 root player -
          reward (quittingSingletonTerminal player) player)) ≤ 0 := by
  classical
  obtain ⟨weight, hweight, hsupport, hsum, hpremium⟩ :=
    hbalanced active hne
  refine ⟨weight, hweight, hsum, ?_⟩
  simp_rw [mul_assoc,
    quittingQuitProbability_mul_quitPremium_eq_sum_terminalPremium]
  simp_rw [Finset.mul_sum]
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_nonpos
  intro terminal _
  by_cases hsubset : terminal.val ⊆ active
  · have hinner : (∑ player ∈ active,
        if player ∈ terminal.val then
          weight player *
            (quittingRootCoalitionMass root terminal.val *
              (reward terminal player -
                reward (quittingSingletonTerminal player) player))
        else 0) = quittingRootCoalitionMass root terminal.val *
          (∑ player ∈ terminal.val, weight player *
            (reward terminal player -
              reward (quittingSingletonTerminal player) player)) := by
      rw [← Finset.sum_filter]
      have hfilter : active.filter (fun player => player ∈ terminal.val) =
          terminal.val := by
        ext player
        simp only [Finset.mem_filter]
        constructor
        · exact fun h => h.2
        · exact fun h => ⟨hsubset h, h⟩
      rw [hfilter, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro player _
      ring
    rw [hinner]
    exact mul_nonpos_of_nonneg_of_nonpos
      (quittingRootCoalitionMass_nonneg root terminal.val)
      (hpremium terminal terminal.property hsubset)
  · obtain ⟨outside, houtTerminal, houtActive⟩ :=
      Set.not_subset.mp hsubset
    have hquit : (root outside true).toReal = 0 := by
      have hnonpos : ¬0 < (root outside true).toReal := by
        simpa [hactive outside] using houtActive
      exact le_antisymm (le_of_not_gt hnonpos) ENNReal.toReal_nonneg
    have hmass : quittingRootCoalitionMass root terminal.val = 0 := by
      unfold quittingRootCoalitionMass coalitionMass quittingRootQuitRates
      rw [Finset.prod_eq_zero (s := terminal.val) houtTerminal hquit, zero_mul]
    simp [hmass]

/-- Every absorbing product root has an active player whose Quit endpoint is
at most that player's own singleton reward. -/
theorem exists_active_quitPayoff_le_singleton_of_supportwiseBalance
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hbalanced : IsSupportwiseBalancedQuittingPremiumTable reward)
    (root : ι → PMF Bool)
    (habsorption : 0 < quittingRootAbsorptionMass root) :
    ∃ who, 0 < (root who true).toReal ∧
      quittingRootQuitPayoff reward 0 root who ≤
        reward (quittingSingletonTerminal who) who := by
  classical
  let active := Finset.univ.filter
    (fun player => 0 < (root player true).toReal)
  have hactive : ∀ player, player ∈ active ↔
      0 < (root player true).toReal := by simp [active]
  have hne : active.Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty] at hempty
    have hquit : ∀ player, (root player true).toReal = 0 := by
      intro player
      have hout : player ∉ active := by rw [hempty]; simp
      have hnot : ¬0 < (root player true).toReal := fun hpos =>
        hout ((hactive player).mpr hpos)
      exact le_antisymm (le_of_not_gt hnot) ENNReal.toReal_nonneg
    unfold quittingRootAbsorptionMass at habsorption
    rw [quittingStationaryContinueMass_eq_prod_continueProbability] at habsorption
    have hfalse : (fun player => (root player false).toReal) =
        (fun _ => (1 : ℝ)) := by
      funext player
      have hsumRoot :=
        quittingRoot_continueProbability_add_quitProbability root player
      rw [hquit player] at hsumRoot
      linarith
    rw [hfalse] at habsorption
    simp at habsorption
  obtain ⟨weight, hweight, hsum, haggregate⟩ :=
    weighted_quittingRootQuitPremium_sum_nonpos
      reward hbalanced root active hactive hne
  have hpositive : ∃ player ∈ active, 0 < weight player := by
    by_contra hnone
    push Not at hnone
    have hzero : ∀ player ∈ active, weight player = 0 := by
      intro player hplayer
      exact le_antisymm (hnone player hplayer) (hweight player)
    have : (∑ player ∈ active, weight player) = 0 := by
      apply Finset.sum_eq_zero
      exact hzero
    linarith
  obtain ⟨marked, hmarked, hwmarked⟩ := hpositive
  by_contra hnone
  push Not at hnone
  have htermNonneg : ∀ player ∈ active,
      0 ≤ weight player * (root player true).toReal *
        (quittingRootQuitPayoff reward 0 root player -
          reward (quittingSingletonTerminal player) player) := by
    intro player hplayer
    by_cases hw : weight player = 0
    · simp [hw]
    · exact mul_nonneg
        (mul_nonneg (hweight player) (hactive player |>.mp hplayer).le)
        (sub_nonneg.mpr
          (hnone player (hactive player |>.mp hplayer)).le)
  have hmarkedPremium : reward (quittingSingletonTerminal marked) marked <
      quittingRootQuitPayoff reward 0 root marked := by
    exact hnone marked (hactive marked |>.mp hmarked)
  have hsumPositive : 0 < ∑ player ∈ active,
      weight player * (root player true).toReal *
        (quittingRootQuitPayoff reward 0 root player -
          reward (quittingSingletonTerminal player) player) := by
    apply Finset.sum_pos'
    · exact htermNonneg
    · exact ⟨marked, hmarked, mul_pos
        (mul_pos hwmarked (hactive marked |>.mp hmarked))
        (sub_pos.mpr hmarkedPremium)⟩
  linarith

/-- Unit own singleton rewards turn supportwise balance into the canonical
low-active-Quit-payoff condition consumed by the row producer. -/
theorem hasLowActiveQuittingRootQuitPayoff_of_supportwiseBalance
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hunit : ∀ player,
      reward (quittingSingletonTerminal player) player = 1)
    (hbalanced : IsSupportwiseBalancedQuittingPremiumTable reward) :
    HasLowActiveQuittingRootQuitPayoff reward := by
  intro root habsorption
  obtain ⟨who, hactive, hquit⟩ :=
    exists_active_quitPayoff_le_singleton_of_supportwiseBalance
      reward hbalanced root habsorption
  exact ⟨who, hactive, by simpa [hunit who] using hquit⟩

end GameTheory
