import UniformEquilibrium.Quitting.Classification.PlayerReindexNaturality
import UniformEquilibrium.Quitting.Examples.AdaptiveChildCenterQuantileRigidity
import UniformEquilibrium.Quitting.Paths.StoppingLawAtomMove

/-! # Literal restriction payoff adapters for the adaptive-child center -/

noncomputable section

namespace GameTheory.AdaptiveChildCenter

open _root_.Math.Probability _root_.Math.ProbabilityMassFunction Math.PMFProduct
open _root_.Math.Probability.DiscreteHazard.StoppingLaw

def childEmbedding (deleted : Fin 4) : Fin 3 ↪ Fin 4 :=
  (deletedEquiv deleted).toEmbedding.trans (Function.Embedding.subtype _)

@[simp] theorem childEmbedding_apply (deleted : Fin 4) (who : Fin 3) :
    childEmbedding deleted who = (deletedEquiv deleted who).1 := rfl

theorem childReward_eq_parent (deleted : Fin 4)
    (terminal : {S : Finset (Fin 3) // S.Nonempty}) (who : Fin 3) :
    childReward deleted terminal who =
      reward ⟨terminal.1.map (childEmbedding deleted),
        Finset.map_nonempty.mpr terminal.2⟩ (childEmbedding deleted who) := by
  change reward _ (childEmbedding deleted who) = reward _ (childEmbedding deleted who)
  apply congrArg (fun coalition => reward coalition (childEmbedding deleted who))
  apply Subtype.ext
  change (terminal.1.map (deletedEquiv deleted).toEmbedding).map
      (Function.Embedding.subtype _) = terminal.1.map (childEmbedding deleted)
  exact Finset.map_map (deletedEquiv deleted).toEmbedding
    (Function.Embedding.subtype _) terminal.1

theorem childReward_abs_le_two (deleted : Fin 4)
    (terminal : {S : Finset (Fin 3) // S.Nonempty}) (who : Fin 3) :
    |childReward deleted terminal who| ≤ 2 := by
  rw [childReward_eq_parent]
  exact reward_abs_le_two _ _

theorem deleted_not_mem_childCoalition (deleted : Fin 4) (terminal : Finset (Fin 3)) :
    deleted ∉ terminal.map (childEmbedding deleted) := by
  intro hmem
  obtain ⟨who, _, heq⟩ := Finset.mem_map.mp hmem
  exact (deletedEquiv deleted who).2 heq

theorem childReward_zero_selected (terminal : {S : Finset (Fin 3) // S.Nonempty}) :
    childReward 0 terminal 0 = -(if (0 : Fin 3) ∈ terminal.1 then 1 else 0) := by
  have hdeleted := deleted_not_mem_childCoalition 0 terminal.1
  have hpart : (1 : Fin 4) ∈ terminal.1.map (childEmbedding 0) ↔ 0 ∈ terminal.1 :=
    Finset.mem_map' (childEmbedding 0) (a := (0 : Fin 3)) (s := terminal.1)
  rw [childReward_eq_parent]
  change reward _ (1 : Fin 4) = _
  by_cases hmem : (0 : Fin 3) ∈ terminal.1 <;> simp [reward, hdeleted, hpart, hmem]

theorem childReward_one_selected (terminal : {S : Finset (Fin 3) // S.Nonempty}) :
    childReward 1 terminal 1 = -(if (1 : Fin 3) ∈ terminal.1 then 1 else 0) := by
  have hdeleted := deleted_not_mem_childCoalition 1 terminal.1
  have hpart : (2 : Fin 4) ∈ terminal.1.map (childEmbedding 1) ↔ 1 ∈ terminal.1 :=
    Finset.mem_map' (childEmbedding 1) (a := (1 : Fin 3)) (s := terminal.1)
  rw [childReward_eq_parent]
  change reward _ (2 : Fin 4) = _
  by_cases hmem : (1 : Fin 3) ∈ terminal.1 <;> simp [reward, hdeleted, hpart, hmem]

theorem childReward_two_selected (terminal : {S : Finset (Fin 3) // S.Nonempty}) :
    childReward 2 terminal 0 = if (0 : Fin 3) ∈ terminal.1 then 1 else 0 := by
  have hdeleted := deleted_not_mem_childCoalition 2 terminal.1
  have hpart : (0 : Fin 4) ∈ terminal.1.map (childEmbedding 2) ↔ 0 ∈ terminal.1 :=
    Finset.mem_map' (childEmbedding 2) (a := (0 : Fin 3)) (s := terminal.1)
  rw [childReward_eq_parent]
  change reward _ (0 : Fin 4) = _
  simp [reward, hdeleted, hpart]

theorem childReward_three_zero (terminal : {S : Finset (Fin 3) // S.Nonempty}) :
    childReward 3 terminal 0 =
      if (0 : Fin 3) ∈ terminal.1 then 1 else 2 * if (2 : Fin 3) ∈ terminal.1 then 1 else 0 := by
  have hzero : (0 : Fin 4) ∈ terminal.1.map (childEmbedding 3) ↔ 0 ∈ terminal.1 :=
    Finset.mem_map' (childEmbedding 3) (a := (0 : Fin 3)) (s := terminal.1)
  have htwo : (2 : Fin 4) ∈ terminal.1.map (childEmbedding 3) ↔ 2 ∈ terminal.1 :=
    Finset.mem_map' (childEmbedding 3) (a := (2 : Fin 3)) (s := terminal.1)
  rw [childReward_eq_parent]
  change reward _ (0 : Fin 4) = _
  simp [reward, hzero, htwo]

/-- This wrapper reuses existing behavioral reindexing and deletion lift.
Its right-hand side keeps every survivor law and replaces only the omitted
player by Never. No new deletion semantics is asserted independently. -/
theorem restrictedProfile_payoff_eq_never_lift
    (deleted : Fin 4) (laws : Fin 4 → PMF (Option ℕ)) (who : Fin 3) :
    quittingTerminalPayoff (childReward deleted) (restrictedProfile deleted laws) who =
      quittingStoppingLawExpectedPayoff reward
        (Function.update laws deleted (PMF.pure none)) (childEmbedding deleted who) := by
  classical
  let survivorReward := quittingDeletePlayerReward reward deleted
  let child := restrictedProfile deleted laws
  let pulled := quittingProfilePullback (deletedEquiv deleted).symm survivorReward child
  let lifted := quittingLiftDeletedProfile reward (fun player => player = deleted) pulled
  have hpayoff : quittingTerminalPayoff (childReward deleted) child who =
      quittingTerminalPayoff reward lifted (childEmbedding deleted who) := by
    have hreindex := quittingTerminalPayoff_profilePullback
      (deletedEquiv deleted).symm survivorReward child (deletedEquiv deleted who)
    have hlift := quittingTerminalPayoff_liftDeletedProfile
      reward (fun player => player = deleted) pulled (deletedEquiv deleted who)
    have hchild : quittingTerminalPayoff (childReward deleted) child who =
        quittingTerminalPayoff survivorReward pulled (deletedEquiv deleted who) := by
      simpa only [childReward, survivorReward, pulled, Equiv.symm_apply_apply] using hreindex
    exact hchild.trans hlift.symm
  have hlaws : quittingBehaviorStoppingLaws reward lifted =
      Function.update laws deleted (PMF.pure none) := by
    funext player
    by_cases hdeleted : player = deleted
    · subst player
      exact (quittingBehaviorStoppingLaw_liftDeletedProfile_of_deleted
        reward (fun player => player = deleted) pulled rfl).trans (by simp)
    · let survivor : QuittingDeletedPlayer deleted := ⟨player, hdeleted⟩
      change quittingBehaviorStoppingLaw reward (lifted survivor.1) = _
      rw [quittingBehaviorStoppingLaw_liftDeletedProfile
        reward (fun player => player = deleted) pulled survivor]
      change quittingBehaviorStoppingLaw survivorReward
          (quittingProfilePullback (deletedEquiv deleted).symm survivorReward child survivor) =
        Function.update laws deleted (PMF.pure none) player
      rw [quittingBehaviorStoppingLaw_profilePullback
        (deletedEquiv deleted).symm survivorReward child survivor]
      change quittingBehaviorStoppingLaw (childReward deleted)
          (restrictedProfile deleted laws ((deletedEquiv deleted).symm survivor)) =
        Function.update laws deleted (PMF.pure none) player
      rw [restrictedProfile_stoppingLaw, Equiv.apply_symm_apply]
      simp only [survivor, Function.update_of_ne hdeleted]
  rw [hpayoff, ← quittingStoppingLawExpectedPayoff_behaviorStoppingLaws_eq_terminalPayoff,
    hlaws]

theorem restrictedProfileOfParent_payoff_eq_never_lift
    (deleted : Fin 4) (parent : (quittingGame reward).BehaviorProfile) (who : Fin 3) :
    quittingTerminalPayoff (childReward deleted)
        (restrictedProfileOfParent deleted parent) who =
      quittingStoppingLawExpectedPayoff reward
        (Function.update (quittingBehaviorStoppingLaws reward parent) deleted (PMF.pure none))
        (childEmbedding deleted who) :=
  restrictedProfile_payoff_eq_never_lift deleted _ who

end GameTheory.AdaptiveChildCenter
