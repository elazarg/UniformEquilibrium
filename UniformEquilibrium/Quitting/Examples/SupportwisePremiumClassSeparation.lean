/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import UniformEquilibrium.Quitting.Classification.QuittingPremiumReward
import UniformEquilibrium.Quitting.Classification.QuittingPremiumSupportPeelingOrder

/-!
# Exact class-separation tables for supportwise quitting premiums

These finite examples compare raw participant-premium conditions.  Passive
payoff coordinates remain arbitrary wherever the comparison does not use
them.  No equilibrium nonexistence statement is inferred from failure of a
particular sufficient table condition.
-/

noncomputable section

namespace GameTheory.SupportwisePremiumClassSeparation

open GameTheory

/-! ## A cyclic Fin4 table: global equal weights, but no peeling -/

def cyclicFinFourPremium (terminal : Finset (Fin 4)) : Payoff (Fin 4) :=
  if terminal = {0, 1} then ![1, -1, 0, 0]
  else if terminal = {1, 2} then ![0, 1, -1, 0]
  else if terminal = {2, 3} then ![0, 0, 1, -1]
  else if terminal = {0, 3} then ![-1, 0, 0, 1]
  else 0

def cyclicFinFourReward
    (passive : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) :
    {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4) :=
  rewardOfOwnPremium 0 cyclicFinFourPremium passive

@[simp] theorem cyclicFinFourPremium_singleton (player : Fin 4) :
    cyclicFinFourPremium {player} player = 0 := by
  fin_cases player
  · simp [cyclicFinFourPremium,
      show ({0} : Finset (Fin 4)) ≠ {0, 1} by decide,
      show ({0} : Finset (Fin 4)) ≠ {1, 2} by decide,
      show ({0} : Finset (Fin 4)) ≠ {2, 3} by decide,
      show ({0} : Finset (Fin 4)) ≠ {0, 3} by decide]
  · simp [cyclicFinFourPremium,
      show ({1} : Finset (Fin 4)) ≠ {0, 1} by decide,
      show ({1} : Finset (Fin 4)) ≠ {1, 2} by decide,
      show ({1} : Finset (Fin 4)) ≠ {2, 3} by decide,
      show ({1} : Finset (Fin 4)) ≠ {0, 3} by decide]
  · simp [cyclicFinFourPremium,
      show ({2} : Finset (Fin 4)) ≠ {0, 1} by decide,
      show ({2} : Finset (Fin 4)) ≠ {1, 2} by decide,
      show ({2} : Finset (Fin 4)) ≠ {2, 3} by decide,
      show ({2} : Finset (Fin 4)) ≠ {0, 3} by decide]
  · simp [cyclicFinFourPremium,
      show ({3} : Finset (Fin 4)) ≠ {0, 1} by decide,
      show ({3} : Finset (Fin 4)) ≠ {1, 2} by decide,
      show ({3} : Finset (Fin 4)) ≠ {2, 3} by decide,
      show ({3} : Finset (Fin 4)) ≠ {0, 3} by decide]

theorem cyclicFinFour_premiumSum (terminal : Finset (Fin 4)) :
    (∑ player ∈ terminal, cyclicFinFourPremium terminal player) = 0 := by
  by_cases h01 : terminal = {0, 1}
  · subst terminal
    simp [cyclicFinFourPremium]
  by_cases h12 : terminal = {1, 2}
  · subst terminal
    simp [cyclicFinFourPremium, h01]
  by_cases h23 : terminal = {2, 3}
  · subst terminal
    simp [cyclicFinFourPremium, h01, h12]
  by_cases h03 : terminal = {0, 3}
  · subst terminal
    simp [cyclicFinFourPremium, h01, h12, h23]
  simp [cyclicFinFourPremium, h01, h12, h23, h03]

theorem cyclicFinFour_participantPremiumSum
    (passive : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (terminal : Finset (Fin 4)) (hterminal : terminal.Nonempty) :
    (∑ player ∈ terminal,
      (cyclicFinFourReward passive ⟨terminal, hterminal⟩ player -
        cyclicFinFourReward passive (quittingSingletonTerminal player) player)) = 0 := by
  calc
    _ = ∑ player ∈ terminal, cyclicFinFourPremium terminal player := by
      apply Finset.sum_congr rfl
      intro player hplayer
      exact rewardOfOwnPremium_sub_singleton 0 cyclicFinFourPremium passive
        ⟨terminal, hterminal⟩ player hplayer (cyclicFinFourPremium_singleton player)
    _ = 0 := cyclicFinFour_premiumSum terminal

theorem cyclicFinFour_supportwiseBalance
    (passive : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) :
    IsSupportwiseBalancedQuittingPremiumTable (cyclicFinFourReward passive) := by
  apply supportwiseBalance_of_globalPositiveWeight
    (cyclicFinFourReward passive) (fun _ => 1) (fun _ => by norm_num)
  intro terminal hterminal
  have hsum := cyclicFinFour_participantPremiumSum passive terminal hterminal
  simpa [Finset.sum_sub_distrib] using hsum.le

theorem cyclicFinFour_not_weakPremiumPeeling
    (passive : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) :
    ¬HasWeakQuittingPremiumSupportPeeling (cyclicFinFourReward passive) := by
  intro hpeel
  have hpeel := (hasWeakQuittingPremiumSupportPeeling_iff _).mp hpeel
  obtain ⟨chosen, _hchosen, hchosen⟩ := hpeel Finset.univ Finset.univ_nonempty
  fin_cases chosen
  · have h := hchosen ({0, 1} : Finset (Fin 4)) (by simp)
      (Finset.subset_univ _) (by simp)
    change cyclicFinFourReward passive ⟨{0, 1}, by simp⟩ 0 ≤
      cyclicFinFourReward passive (quittingSingletonTerminal 0) 0 at h
    have hdiff := rewardOfOwnPremium_sub_singleton 0 cyclicFinFourPremium passive
      ⟨{0, 1}, by simp⟩ 0 (by simp) (cyclicFinFourPremium_singleton 0)
    change cyclicFinFourReward passive ⟨{0, 1}, by simp⟩ 0 -
      cyclicFinFourReward passive (quittingSingletonTerminal 0) 0 =
        cyclicFinFourPremium {0, 1} 0 at hdiff
    norm_num [cyclicFinFourPremium] at hdiff
    linarith
  · have h := hchosen ({1, 2} : Finset (Fin 4)) (by simp)
      (Finset.subset_univ _) (by simp)
    change cyclicFinFourReward passive ⟨{1, 2}, by simp⟩ 1 ≤
      cyclicFinFourReward passive (quittingSingletonTerminal 1) 1 at h
    have hdiff : cyclicFinFourReward passive ⟨{1, 2}, by simp⟩ 1 -
        cyclicFinFourReward passive (quittingSingletonTerminal 1) 1 = 1 := by
      exact rewardOfOwnPremium_sub_singleton 0 cyclicFinFourPremium passive
        ⟨{1, 2}, by simp⟩ 1 (by simp) (by simp)
    linarith
  · have h := hchosen ({2, 3} : Finset (Fin 4)) (by simp)
      (Finset.subset_univ _) (by simp)
    change cyclicFinFourReward passive ⟨{2, 3}, by simp⟩ 2 ≤
      cyclicFinFourReward passive (quittingSingletonTerminal 2) 2 at h
    have hdiff : cyclicFinFourReward passive ⟨{2, 3}, by simp⟩ 2 -
        cyclicFinFourReward passive (quittingSingletonTerminal 2) 2 = 1 := by
      exact rewardOfOwnPremium_sub_singleton 0 cyclicFinFourPremium passive
        ⟨{2, 3}, by simp⟩ 2 (by simp) (by simp)
    linarith
  · have h := hchosen ({0, 3} : Finset (Fin 4)) (by simp)
      (Finset.subset_univ _) (by simp)
    change cyclicFinFourReward passive ⟨{0, 3}, by simp⟩ 3 ≤
      cyclicFinFourReward passive (quittingSingletonTerminal 3) 3 at h
    have hdiff : cyclicFinFourReward passive ⟨{0, 3}, by simp⟩ 3 -
        cyclicFinFourReward passive (quittingSingletonTerminal 3) 3 = 1 := by
      exact rewardOfOwnPremium_sub_singleton 0 cyclicFinFourPremium passive
        ⟨{0, 3}, by simp⟩ 3 (by simp) (by simp)
    linarith

/-! ## One positive premium: peeling, but no positive global weights -/

def onePositiveFinFourPremium (terminal : Finset (Fin 4)) : Payoff (Fin 4) :=
  if terminal = {0, 1} then ![0, 1, 0, 0] else 0

def onePositiveFinFourReward
    (passive : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) :
    {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4) :=
  rewardOfOwnPremium 0 onePositiveFinFourPremium passive

@[simp] theorem onePositiveFinFourPremium_singleton (player : Fin 4) :
    onePositiveFinFourPremium {player} player = 0 := by
  unfold onePositiveFinFourPremium
  split
  · rename_i h
    have hcard := congrArg Finset.card h
    simp at hcard
  · rfl

theorem onePositiveFinFour_weakPremiumPeeling
    (passive : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) :
    HasWeakQuittingPremiumSupportPeeling (onePositiveFinFourReward passive) := by
  apply (hasWeakQuittingPremiumSupportPeeling_iff _).mpr
  intro active hactive
  by_cases hzero : (0 : Fin 4) ∈ active
  · refine ⟨0, hzero, ?_⟩
    intro terminal hterminal _hsubset hmem
    have hpremium : onePositiveFinFourPremium terminal 0 = 0 := by
      unfold onePositiveFinFourPremium
      split <;> simp
    have hdiff := rewardOfOwnPremium_sub_singleton 0 onePositiveFinFourPremium
      passive ⟨terminal, hterminal⟩ 0 hmem (onePositiveFinFourPremium_singleton 0)
    change onePositiveFinFourReward passive ⟨terminal, hterminal⟩ 0 -
      onePositiveFinFourReward passive (quittingSingletonTerminal 0) 0 =
        onePositiveFinFourPremium terminal 0 at hdiff
    rw [hpremium] at hdiff
    linarith
  · let chosen := hactive.choose
    have hchosen : chosen ∈ active := hactive.choose_spec
    refine ⟨chosen, hchosen, ?_⟩
    intro terminal hterminal hsubset hmem
    have hterminalZero : (0 : Fin 4) ∉ terminal := fun h =>
      hzero (hsubset h)
    have hpremium : onePositiveFinFourPremium terminal chosen = 0 := by
      unfold onePositiveFinFourPremium
      split
      · rename_i hp
        subst terminal
        exact (hterminalZero (by simp)).elim
      · rfl
    have hdiff := rewardOfOwnPremium_sub_singleton 0 onePositiveFinFourPremium
      passive ⟨terminal, hterminal⟩ chosen hmem
      (onePositiveFinFourPremium_singleton chosen)
    change onePositiveFinFourReward passive ⟨terminal, hterminal⟩ chosen -
      onePositiveFinFourReward passive (quittingSingletonTerminal chosen) chosen =
        onePositiveFinFourPremium terminal chosen at hdiff
    rw [hpremium] at hdiff
    linarith

theorem onePositiveFinFour_no_strictlyPositiveGlobalWeight
    (passive : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) :
    ¬∃ weight : Fin 4 → ℝ, (∀ player, 0 < weight player) ∧
      ∀ (terminal : Finset (Fin 4)) (hterminal : terminal.Nonempty),
        (∑ player ∈ terminal, weight player *
          (onePositiveFinFourReward passive ⟨terminal, hterminal⟩ player -
            onePositiveFinFourReward passive
              (quittingSingletonTerminal player) player)) ≤ 0 := by
  rintro ⟨weight, hpositive, hpremium⟩
  have h := hpremium ({0, 1} : Finset (Fin 4)) (by simp)
  have hzeroDiff : onePositiveFinFourReward passive ⟨{0, 1}, by simp⟩ 0 -
      onePositiveFinFourReward passive (quittingSingletonTerminal 0) 0 = 0 := by
    exact rewardOfOwnPremium_sub_singleton 0 onePositiveFinFourPremium passive
      ⟨{0, 1}, by simp⟩ 0 (by simp) (by simp)
  have honeDiff : onePositiveFinFourReward passive ⟨{0, 1}, by simp⟩ 1 -
      onePositiveFinFourReward passive (quittingSingletonTerminal 1) 1 = 1 := by
    exact rewardOfOwnPremium_sub_singleton 0 onePositiveFinFourPremium passive
      ⟨{0, 1}, by simp⟩ 1 (by simp) (by simp)
  rw [Finset.sum_insert (by decide : (0 : Fin 4) ∉ ({1} : Finset (Fin 4))),
    Finset.sum_singleton] at h
  rw [hzeroDiff, honeDiff] at h
  ring_nf at h
  linarith [hpositive 1]

/-! ## A supportwise table outside both special subclasses -/

def combinedFinFourSingleton : Payoff (Fin 4) := ![1, 0, 0, 0]

def combinedFinFourPremium (terminal : Finset (Fin 4)) : Payoff (Fin 4) :=
  if terminal = {0, 1} then ![1, -1, 0, 0]
  else if terminal = {1, 2} then ![0, 1, -1, 0]
  else if terminal = {0, 2} then ![-1, 0, 1, 0]
  else if terminal = {0, 3} then ![0, 0, 0, 1]
  else 0

def combinedFinFourReward
    (passive : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) :
    {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4) :=
  rewardOfOwnPremium combinedFinFourSingleton combinedFinFourPremium passive

def combinedFinFourCore : Finset (Fin 4) := {0, 1, 2}

def combinedFinFourCarrier (active : Finset (Fin 4)) : Finset (Fin 4) :=
  if (active ∩ combinedFinFourCore).Nonempty then
    active ∩ combinedFinFourCore
  else active

def combinedFinFourWeight (active : Finset (Fin 4)) : Fin 4 → ℝ :=
  fun player => if player ∈ combinedFinFourCarrier active then
    ((combinedFinFourCarrier active).card : ℝ)⁻¹ else 0

@[simp] theorem combinedFinFourPremium_singleton (player : Fin 4) :
    combinedFinFourPremium {player} player = 0 := by
  unfold combinedFinFourPremium
  split <;> rename_i h
  · have hcard := congrArg Finset.card h
    simp at hcard
  · split <;> rename_i h
    · have hcard := congrArg Finset.card h
      simp at hcard
    · split <;> rename_i h
      · have hcard := congrArg Finset.card h
        simp at hcard
      · split <;> rename_i h
        · have hcard := congrArg Finset.card h
          simp at hcard
        · rfl

theorem combinedFinFour_weightCertificate
    (active : Finset (Fin 4)) (hactive : active.Nonempty) :
    (∀ player, 0 ≤ combinedFinFourWeight active player) ∧
    (∀ player, player ∉ active → combinedFinFourWeight active player = 0) ∧
    (∑ player ∈ active, combinedFinFourWeight active player) = 1 := by
  have hcarrier : (combinedFinFourCarrier active).Nonempty := by
    unfold combinedFinFourCarrier
    split
    · assumption
    · exact hactive
  have hcarrierSubset : combinedFinFourCarrier active ⊆ active := by
    unfold combinedFinFourCarrier
    split
    · exact Finset.inter_subset_left
    · exact fun _ h => h
  refine ⟨?_, ?_, ?_⟩
  · intro player
    unfold combinedFinFourWeight
    split <;> positivity
  · intro player hout
    unfold combinedFinFourWeight
    rw [if_neg (fun hmem => hout (hcarrierSubset hmem))]
  · unfold combinedFinFourWeight
    rw [← Finset.sum_filter]
    have hfilter : active.filter (fun player =>
        player ∈ combinedFinFourCarrier active) =
        combinedFinFourCarrier active := by
      ext player
      simp only [Finset.mem_filter]
      constructor
      · exact fun h => h.2
      · exact fun h => ⟨hcarrierSubset h, h⟩
    rw [hfilter]
    have hcard : ((combinedFinFourCarrier active).card : ℝ) ≠ 0 := by
      exact_mod_cast Finset.card_ne_zero.mpr hcarrier
    simp
    exact mul_inv_cancel₀ hcard

theorem combinedFinFour_weightedPremium_nonpos
    (passive : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (active terminal : Finset (Fin 4)) (hterminal : terminal.Nonempty)
    (hsubset : terminal ⊆ active) :
    (∑ player ∈ terminal, combinedFinFourWeight active player *
      (combinedFinFourReward passive ⟨terminal, hterminal⟩ player -
        combinedFinFourReward passive
          (quittingSingletonTerminal player) player)) ≤ 0 := by
  have hrewrite : ∀ player ∈ terminal,
      combinedFinFourReward passive ⟨terminal, hterminal⟩ player -
          combinedFinFourReward passive
            (quittingSingletonTerminal player) player =
        combinedFinFourPremium terminal player := by
    intro player hplayer
    exact rewardOfOwnPremium_sub_singleton combinedFinFourSingleton
      combinedFinFourPremium passive ⟨terminal, hterminal⟩ player hplayer
      (combinedFinFourPremium_singleton player)
  calc
    _ = ∑ player ∈ terminal, combinedFinFourWeight active player *
          combinedFinFourPremium terminal player := by
      apply Finset.sum_congr rfl
      intro player hplayer
      rw [hrewrite player hplayer]
    _ ≤ 0 := by
      by_cases h01 : terminal = {0, 1}
      · subst terminal
        have h0 : (0 : Fin 4) ∈ active := hsubset (by simp)
        have h1 : (1 : Fin 4) ∈ active := hsubset (by simp)
        have hcore : (active ∩ combinedFinFourCore).Nonempty := by
          exact ⟨0, by simp [combinedFinFourCore, h0]⟩
        rw [Finset.sum_insert
          (by decide : (0 : Fin 4) ∉ ({1} : Finset (Fin 4))),
          Finset.sum_singleton]
        unfold combinedFinFourWeight combinedFinFourCarrier
        rw [if_pos hcore]
        simp [combinedFinFourCore, combinedFinFourPremium, h0, h1]
      by_cases h12 : terminal = {1, 2}
      · subst terminal
        have h1 : (1 : Fin 4) ∈ active := hsubset (by simp)
        have h2 : (2 : Fin 4) ∈ active := hsubset (by simp)
        have hcore : (active ∩ combinedFinFourCore).Nonempty := by
          exact ⟨1, by simp [combinedFinFourCore, h1]⟩
        rw [Finset.sum_insert
          (by decide : (1 : Fin 4) ∉ ({2} : Finset (Fin 4))),
          Finset.sum_singleton]
        unfold combinedFinFourWeight combinedFinFourCarrier
        rw [if_pos hcore]
        simp [combinedFinFourCore, combinedFinFourPremium, h1, h2, h01]
      by_cases h02 : terminal = {0, 2}
      · subst terminal
        have h0 : (0 : Fin 4) ∈ active := hsubset (by simp)
        have h2 : (2 : Fin 4) ∈ active := hsubset (by simp)
        have hcore : (active ∩ combinedFinFourCore).Nonempty := by
          exact ⟨0, by simp [combinedFinFourCore, h0]⟩
        rw [Finset.sum_insert
          (by decide : (0 : Fin 4) ∉ ({2} : Finset (Fin 4))),
          Finset.sum_singleton]
        unfold combinedFinFourWeight combinedFinFourCarrier
        rw [if_pos hcore]
        simp [combinedFinFourCore, combinedFinFourPremium, h0, h2,
          h01, h12]
      by_cases h03 : terminal = {0, 3}
      · subst terminal
        have h0 : (0 : Fin 4) ∈ active := hsubset (by simp)
        have h3 : (3 : Fin 4) ∈ active := hsubset (by simp)
        have hcore : (active ∩ combinedFinFourCore).Nonempty := by
          exact ⟨0, by simp [combinedFinFourCore, h0]⟩
        rw [Finset.sum_insert
          (by decide : (0 : Fin 4) ∉ ({3} : Finset (Fin 4))),
          Finset.sum_singleton]
        unfold combinedFinFourWeight combinedFinFourCarrier
        rw [if_pos hcore]
        simp [combinedFinFourCore, combinedFinFourPremium, h0, h3,
          h01, h12, h02]
      simp [combinedFinFourPremium, h01, h12, h02, h03]

theorem combinedFinFour_supportwiseBalance
    (passive : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) :
    IsSupportwiseBalancedQuittingPremiumTable (combinedFinFourReward passive) := by
  intro active hactive
  obtain ⟨hweight, hsupport, hsum⟩ :=
    combinedFinFour_weightCertificate active hactive
  exact ⟨combinedFinFourWeight active, hweight, hsupport, hsum,
    fun terminal hterminal hsubset =>
      combinedFinFour_weightedPremium_nonpos passive active terminal
        hterminal hsubset⟩

theorem combinedFinFour_not_weakPremiumPeeling
    (passive : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) :
    ¬HasWeakQuittingPremiumSupportPeeling (combinedFinFourReward passive) := by
  intro hpeel
  have hpeel := (hasWeakQuittingPremiumSupportPeeling_iff _).mp hpeel
  let core : Finset (Fin 4) := {0, 1, 2}
  obtain ⟨chosen, hchosen, hpayoff⟩ := hpeel core (by simp [core])
  have hchosenCases : chosen = 0 ∨ chosen = 1 ∨ chosen = 2 := by
    simpa [core] using hchosen
  rcases hchosenCases with rfl | rfl | rfl
  · have h := hpayoff {0, 1} (by simp) (by simp [core]) (by simp)
    have hdiff := rewardOfOwnPremium_sub_singleton combinedFinFourSingleton
      combinedFinFourPremium passive ⟨{0, 1}, by simp⟩ 0 (by simp)
      (combinedFinFourPremium_singleton 0)
    change combinedFinFourReward passive ⟨{0, 1}, by simp⟩ 0 -
      combinedFinFourReward passive (quittingSingletonTerminal 0) 0 =
        combinedFinFourPremium {0, 1} 0 at hdiff
    norm_num [combinedFinFourPremium] at hdiff
    linarith
  · have h := hpayoff {1, 2} (by simp) (by simp [core]) (by simp)
    have hdiff := rewardOfOwnPremium_sub_singleton combinedFinFourSingleton
      combinedFinFourPremium passive ⟨{1, 2}, by simp⟩ 1 (by simp)
      (combinedFinFourPremium_singleton 1)
    change combinedFinFourReward passive ⟨{1, 2}, by simp⟩ 1 -
      combinedFinFourReward passive (quittingSingletonTerminal 1) 1 =
        combinedFinFourPremium {1, 2} 1 at hdiff
    norm_num [combinedFinFourPremium,
      show ({1, 2} : Finset (Fin 4)) ≠ {0, 1} by decide] at hdiff
    linarith
  · have h := hpayoff {0, 2} (by simp) (by simp [core]) (by simp)
    have hdiff := rewardOfOwnPremium_sub_singleton combinedFinFourSingleton
      combinedFinFourPremium passive ⟨{0, 2}, by simp⟩ 2 (by simp)
      (combinedFinFourPremium_singleton 2)
    change combinedFinFourReward passive ⟨{0, 2}, by simp⟩ 2 -
      combinedFinFourReward passive (quittingSingletonTerminal 2) 2 =
        combinedFinFourPremium {0, 2} 2 at hdiff
    norm_num [combinedFinFourPremium,
      show ({0, 2} : Finset (Fin 4)) ≠ {0, 1} by decide,
      show ({0, 2} : Finset (Fin 4)) ≠ {1, 2} by decide] at hdiff
    change combinedFinFourReward passive ⟨{0, 2}, by simp⟩ 2 -
      combinedFinFourReward passive (quittingSingletonTerminal 2) 2 = 1
      at hdiff
    linarith

theorem combinedFinFour_no_strictlyPositiveGlobalWeight
    (passive : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) :
    ¬∃ weight : Fin 4 → ℝ, (∀ player, 0 < weight player) ∧
      ∀ (terminal : Finset (Fin 4)) (hterminal : terminal.Nonempty),
        (∑ player ∈ terminal, weight player *
          (combinedFinFourReward passive ⟨terminal, hterminal⟩ player -
            combinedFinFourReward passive
              (quittingSingletonTerminal player) player)) ≤ 0 := by
  rintro ⟨weight, hpositive, hpremium⟩
  have h := hpremium ({0, 3} : Finset (Fin 4)) (by simp)
  have hzeroDiff := rewardOfOwnPremium_sub_singleton combinedFinFourSingleton
    combinedFinFourPremium passive ⟨{0, 3}, by simp⟩ 0 (by simp)
    (combinedFinFourPremium_singleton 0)
  have hthreeDiff := rewardOfOwnPremium_sub_singleton combinedFinFourSingleton
    combinedFinFourPremium passive ⟨{0, 3}, by simp⟩ 3 (by simp)
    (combinedFinFourPremium_singleton 3)
  change combinedFinFourReward passive ⟨{0, 3}, by simp⟩ 0 -
    combinedFinFourReward passive (quittingSingletonTerminal 0) 0 =
      combinedFinFourPremium {0, 3} 0 at hzeroDiff
  change combinedFinFourReward passive ⟨{0, 3}, by simp⟩ 3 -
    combinedFinFourReward passive (quittingSingletonTerminal 3) 3 =
      combinedFinFourPremium {0, 3} 3 at hthreeDiff
  norm_num [combinedFinFourPremium,
    show ({0, 3} : Finset (Fin 4)) ≠ {0, 1} by decide,
    show ({0, 3} : Finset (Fin 4)) ≠ {1, 2} by decide,
    show ({0, 3} : Finset (Fin 4)) ≠ {0, 2} by decide]
    at hzeroDiff hthreeDiff
  change combinedFinFourReward passive ⟨{0, 3}, by simp⟩ 3 -
    combinedFinFourReward passive (quittingSingletonTerminal 3) 3 = 1
    at hthreeDiff
  rw [Finset.sum_insert (by decide : (0 : Fin 4) ∉ ({3} : Finset (Fin 4))),
    Finset.sum_singleton] at h
  rw [hzeroDiff, hthreeDiff] at h
  ring_nf at h
  linarith [hpositive 3]

end GameTheory.SupportwisePremiumClassSeparation
