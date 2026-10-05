import UniformEquilibrium.Quitting.Classification.Existence.CommonQuittingPremiumLeaverUniformPayoff
import UniformEquilibrium.Quitting.Terminal.TerminalExploitabilityRewardRobustness

/-! # Weak common-leaver comparisons by passive reward perturbation -/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Increase only the protected player's passive rewards on the original
core face. Every participant reward, including every own singleton, is retained. -/
def commonLeaverPassivePerturbation
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (player : ι) (delta : ℝ)
    (terminal : {S : Finset ι // S.Nonempty}) (who : ι) : ℝ :=
  if who = player ∧ player ∉ terminal.val ∧ terminal.val ⊆ quittingPremiumCore reward
  then reward terminal who + delta else reward terminal who

theorem commonLeaverPassivePerturbation_participant
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (player : ι) (delta : ℝ)
    (terminal : {S : Finset ι // S.Nonempty}) (who : ι) (hwho : who ∈ terminal.val) :
    commonLeaverPassivePerturbation reward player delta terminal who = reward terminal who := by
  unfold commonLeaverPassivePerturbation
  split
  · rename_i hcondition
    exact (hcondition.2.1 (hcondition.1 ▸ hwho)).elim
  · rfl

theorem commonLeaverPassivePerturbation_trap_iff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (player : ι) (delta : ℝ)
    (active : Finset ι) :
    IsQuittingPremiumTrap (commonLeaverPassivePerturbation reward player delta) active ↔
      IsQuittingPremiumTrap reward active := by
  have hpositive : ∀ who coalition, who ∈ coalition →
      (HasPositiveOwnQuittingPremium (commonLeaverPassivePerturbation reward player delta)
          who coalition ↔ HasPositiveOwnQuittingPremium reward who coalition) := by
    intro who coalition hwho
    unfold HasPositiveOwnQuittingPremium
    have hsingleton := commonLeaverPassivePerturbation_participant reward player delta
      (quittingSingletonTerminal who) who (by simp [quittingSingletonTerminal])
    simp only [hsingleton]
    constructor
    · rintro ⟨hnonempty, hpositive⟩
      have hpart := commonLeaverPassivePerturbation_participant
        reward player delta ⟨coalition, hnonempty⟩ who hwho
      exact ⟨hnonempty, by simpa only [hpart] using hpositive⟩
    · rintro ⟨hnonempty, hpositive⟩
      have hpart := commonLeaverPassivePerturbation_participant
        reward player delta ⟨coalition, hnonempty⟩ who hwho
      exact ⟨hnonempty, by simpa only [hpart] using hpositive⟩
  constructor
  · rintro ⟨hactive, hwitness⟩
    refine ⟨hactive, ?_⟩
    intro who hwho
    obtain ⟨coalition, hsubset, hmember, hrelation⟩ := hwitness who hwho
    exact ⟨coalition, hsubset, hmember, (hpositive who coalition hmember).mp hrelation⟩
  · rintro ⟨hactive, hwitness⟩
    refine ⟨hactive, ?_⟩
    intro who hwho
    obtain ⟨coalition, hsubset, hmember, hrelation⟩ := hwitness who hwho
    exact ⟨coalition, hsubset, hmember, (hpositive who coalition hmember).mpr hrelation⟩

theorem commonLeaverPassivePerturbation_core
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (player : ι) (delta : ℝ) :
    quittingPremiumCore (commonLeaverPassivePerturbation reward player delta) =
      quittingPremiumCore reward := by
  ext who
  rw [quittingPremiumCore, quittingPremiumCore,
    MathUE.mem_finiteCoalitionPremiumCore_iff, MathUE.mem_finiteCoalitionPremiumCore_iff]
  constructor
  · rintro ⟨active, htrap, hmember⟩
    exact ⟨active, (commonLeaverPassivePerturbation_trap_iff
      reward player delta active).mp htrap, hmember⟩
  · rintro ⟨active, htrap, hmember⟩
    exact ⟨active, (commonLeaverPassivePerturbation_trap_iff
      reward player delta active).mpr htrap, hmember⟩

/-- The weak raw comparisons give a fixed-target uniform payoff by nearby
strict tables. This is not an assertion of weak analytic potential exclusion. -/
theorem exists_uniformEquilibriumPayoff_of_commonLeaver_weakLeave
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hsingleton : ∀ who, 0 ≤ reward (quittingSingletonTerminal who) who)
    (player : Fin 4) (hcommon : IsCommonQuittingPremiumLeaver reward player)
    (hleave : ∀ (coalition : Finset (Fin 4)) (hcoalition : coalition.Nonempty),
      coalition ⊆ (quittingPremiumCore reward).erase player →
        reward ⟨insert player coalition, Finset.insert_nonempty _ _⟩ player ≤
          reward ⟨coalition, hcoalition⟩ player) :
    ∃ payoff : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  apply exists_uniformEquilibriumPayoff_of_arbitrarily_close_reward_tables
  intro delta hdelta
  let nearby := commonLeaverPassivePerturbation reward player delta
  have hparticipant : ∀ terminal who, who ∈ terminal.val →
      nearby terminal who = reward terminal who :=
    commonLeaverPassivePerturbation_participant reward player delta
  have hsingletonEq : ∀ who,
      nearby (quittingSingletonTerminal who) who =
        reward (quittingSingletonTerminal who) who := by
    intro who
    exact hparticipant _ who (by simp [quittingSingletonTerminal])
  refine ⟨nearby, ?_, ?_⟩
  · intro terminal who
    dsimp [nearby, commonLeaverPassivePerturbation]
    split <;> simp [abs_of_pos hdelta, hdelta.le]
  · apply exists_uniformEquilibriumPayoff_of_commonLeaver_strictLeave nearby
      (fun who => by rw [hsingletonEq]; exact hsingleton who) player
    · refine ⟨?_, ?_⟩
      · intro terminal hmember
        rw [hsingletonEq, hparticipant terminal player hmember]
        exact hcommon.1 terminal hmember
      · intro active htrap
        exact hcommon.2 active
          ((commonLeaverPassivePerturbation_trap_iff reward player delta active).mp htrap)
    · intro coalition hcoalition hsubset
      rw [commonLeaverPassivePerturbation_core] at hsubset
      have hnot : player ∉ coalition := by
        intro hmember
        exact (Finset.mem_erase.mp (hsubset hmember)).1 rfl
      have hcore : coalition ⊆ quittingPremiumCore reward :=
        hsubset.trans (Finset.erase_subset _ _)
      have hinsert := hparticipant
        ⟨insert player coalition, Finset.insert_nonempty _ _⟩ player
        (Finset.mem_insert_self _ _)
      have hpassive : nearby ⟨coalition, hcoalition⟩ player =
          reward ⟨coalition, hcoalition⟩ player + delta := by
        simp [nearby, commonLeaverPassivePerturbation, hnot, hcore]
      rw [hinsert, hpassive]
      have hweak := hleave coalition hcoalition hsubset
      linarith

end GameTheory
