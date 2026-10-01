import UniformEquilibrium.Quitting.Examples.BlockPair.PairedResponseQuotientClass
import MathUE.Finset.FinFourNonemptyCoalitions
import Mathlib.Data.Finset.Max

/-!
# Thirty-three independent paired nonsingletons and four signed own singletons

This chart reconstructs the actual raw table, with Never still zero. Recipients
zero, two and three have arbitrary final rewards on all eleven nonsingleton
coalitions; recipient one is determined from the swapped recipient-zero row.
Every own-singleton level is an arbitrary signed real. The chart is injective
and covers exactly the centered paired class; it is not a full60 open set.
-/

noncomputable section

namespace GameTheory
namespace PairedResponseQuotient

open QuittingLCPClassification FourPlayerPairedSingleton

/-- The same actual nonempty four-player coalitions as the canonical row enumeration. -/
abbrev PairedTerminal := {S : Finset (Fin 4) // S.Nonempty}

/-- Eleven literal nonsingleton coalitions. -/
abbrev PairedNonsingletonCoalition := {terminal : PairedTerminal // terminal.1.card ≠ 1}

/-- The final reward coordinates independently assigned for recipients zero, two and three. -/
abbrev PairedFreeRewardCoordinate :=
  {coordinate : PairedTerminal × Fin 4 //
    coordinate.1.1.card ≠ 1 ∧ coordinate.2 ≠ 1}

abbrev PairedFreeRewardSpace := PairedFreeRewardCoordinate → ℝ

theorem card_pairedNonsingletonCoalition : Fintype.card PairedNonsingletonCoalition = 11 := by
  decide

theorem card_pairedFreeRewardCoordinate : Fintype.card PairedFreeRewardCoordinate = 33 := by
  decide

/-- Eleven freely chosen final entries belong to recipient zero. -/
theorem card_pairedRecipientZeroFreeCoordinate :
    Fintype.card {coordinate : PairedFreeRewardCoordinate // coordinate.1.2 = 0} = 11 := by
  decide

/-- The other twenty-two freely chosen final entries belong to recipients two and three. -/
theorem card_pairedOtherFreeCoordinate :
    Fintype.card {coordinate : PairedFreeRewardCoordinate //
      coordinate.1.2 = 2 ∨ coordinate.1.2 = 3} = 22 := by
  decide

/-- The chart has exactly thirty-seven independent scalar inputs. -/
theorem card_pairedCompletionScalarCoordinate :
    Fintype.card (Fin 4 ⊕ PairedFreeRewardCoordinate) = 37 := by
  rw [Fintype.card_sum, Fintype.card_fin, card_pairedFreeRewardCoordinate]

private theorem swappedTerminal_card (terminal : PairedTerminal) :
    (quittingCoalitionEquiv (Equiv.swap (0 : Fin 4) 1) terminal).1.card =
      terminal.1.card := by
  exact Finset.card_map _

private theorem pulledTerminal_card (terminal : PairedTerminal) :
    ((quittingCoalitionEquiv (Equiv.swap (0 : Fin 4) 1)).symm terminal).1.card =
      terminal.1.card := by
  exact Finset.card_map _

/-- Reconstruct every actual reward from its arbitrary signed singleton levels
and the thirty-three arbitrary signed final nonsingleton rewards. -/
def pairedCompletionReward (solo : Payoff (Fin 4)) (free : PairedFreeRewardSpace) :
    PairedTerminal → Payoff (Fin 4) :=
  fun terminal who =>
    if hsingle : terminal.1.card = 1 then
      solo who + pairedSingletonMatrix who (terminal.1.max' terminal.2)
    else if hwho : who = 1 then
      free ⟨((quittingCoalitionEquiv (Equiv.swap (0 : Fin 4) 1)).symm terminal, 0),
        by rw [pulledTerminal_card]; exact hsingle,
        by change (0 : Fin 4) ≠ 1; decide⟩ + solo 1 - solo 0
    else free ⟨(terminal, who), hsingle, hwho⟩

/-- Every singleton entry is its recipient's own level plus the printed Gamma entry. -/
theorem pairedCompletionReward_singleton (solo : Payoff (Fin 4))
    (free : PairedFreeRewardSpace) (owner who : Fin 4) :
    pairedCompletionReward solo free (quittingSingletonTerminal owner) who =
      solo who + pairedSingletonMatrix who owner := by
  simp [pairedCompletionReward, quittingSingletonTerminal]

/-- All four own-singleton levels are exactly the arbitrary signed input coordinates. -/
theorem pairedCompletionReward_ownSingleton (solo : Payoff (Fin 4))
    (free : PairedFreeRewardSpace) (who : Fin 4) :
    pairedCompletionReward solo free (quittingSingletonTerminal who) who = solo who := by
  rw [pairedCompletionReward_singleton]
  have hzero : pairedSingletonMatrix who who = 0 := by
    fin_cases who <;> rfl
  rw [hzero, add_zero]

/-- Every free coordinate is the actual final terminal reward, not a reward increment. -/
theorem pairedCompletionReward_free (solo : Payoff (Fin 4))
    (free : PairedFreeRewardSpace) (coordinate : PairedFreeRewardCoordinate) :
    pairedCompletionReward solo free coordinate.1.1 coordinate.1.2 = free coordinate := by
  simp [pairedCompletionReward, coordinate.property]

/-- Recipient one is determined by the actual pulled-back recipient-zero coalition. -/
theorem pairedCompletionReward_recipientOne (solo : Payoff (Fin 4))
    (free : PairedFreeRewardSpace) (terminal : PairedTerminal)
    (hnonsingleton : terminal.1.card ≠ 1) :
    pairedCompletionReward solo free terminal 1 =
      pairedCompletionReward solo free
        ((quittingCoalitionEquiv (Equiv.swap (0 : Fin 4) 1)).symm terminal) 0 +
          solo 1 - solo 0 := by
  simp [pairedCompletionReward, hnonsingleton]

/-- Every chart input has precisely the original full singleton comparison matrix. -/
theorem pairedCompletionReward_singletonMatrix (solo : Payoff (Fin 4))
    (free : PairedFreeRewardSpace) :
    quittingSingletonMatrix (pairedCompletionReward solo free) = pairedSingletonMatrix := by
  ext who owner
  change pairedCompletionReward solo free (quittingSingletonTerminal owner) who -
      pairedCompletionReward solo free (quittingSingletonTerminal who) who =
    pairedSingletonMatrix who owner
  rw [pairedCompletionReward_singleton, pairedCompletionReward_ownSingleton]
  ring

/-- Every signed coordinate input produces a member of the actual centered paired class. -/
theorem pairedCompletionReward_class (solo : Payoff (Fin 4)) (free : PairedFreeRewardSpace) :
    IsPairedCenteredCompletion (pairedCompletionReward solo free) := by
  refine ⟨pairedCompletionReward_singletonMatrix solo free, ?_⟩
  intro terminal
  change pairedCompletionReward solo free
      (quittingCoalitionEquiv (Equiv.swap (0 : Fin 4) 1) terminal) 1 -
        quittingSoloReward (pairedCompletionReward solo free) 1 1 =
    pairedCompletionReward solo free terminal 0 -
      quittingSoloReward (pairedCompletionReward solo free) 0 0
  rw [quittingSoloReward_self, quittingSoloReward_self,
    pairedCompletionReward_ownSingleton, pairedCompletionReward_ownSingleton]
  by_cases hsingle : terminal.1.card = 1
  · obtain ⟨owner, howner⟩ := Finset.card_eq_one.mp hsingle
    have hterminal : terminal = quittingSingletonTerminal owner := Subtype.ext howner
    rw [hterminal]
    have hswapped :
        quittingCoalitionEquiv (Equiv.swap (0 : Fin 4) 1)
            (quittingSingletonTerminal owner) =
          quittingSingletonTerminal ((Equiv.swap (0 : Fin 4) 1) owner) := by
      apply Subtype.ext
      simp [quittingCoalitionEquiv, quittingSingletonTerminal]
    rw [hswapped, pairedCompletionReward_singleton, pairedCompletionReward_singleton]
    have hmatrix : pairedSingletonMatrix 1 ((Equiv.swap (0 : Fin 4) 1) owner) =
        pairedSingletonMatrix 0 owner := by
      fin_cases owner <;> norm_num [pairedSingletonMatrix, Equiv.swap_apply_def]
    rw [hmatrix]
    ring
  · have hswapped :
        (quittingCoalitionEquiv (Equiv.swap (0 : Fin 4) 1) terminal).1.card ≠ 1 := by
      rwa [swappedTerminal_card]
    rw [pairedCompletionReward_recipientOne solo free _ hswapped,
      Equiv.symm_apply_apply]
    ring

/-- The four own levels and all thirty-three nonsingletons are jointly independent. -/
theorem pairedCompletionReward_injective :
    Function.Injective (fun parameters : Payoff (Fin 4) × PairedFreeRewardSpace =>
      pairedCompletionReward parameters.1 parameters.2) := by
  intro first second hequal
  apply Prod.ext
  · funext who
    have h := congrFun (congrFun hequal (quittingSingletonTerminal who)) who
    simpa only [pairedCompletionReward_ownSingleton] using h
  · funext coordinate
    have h := congrFun (congrFun hequal coordinate.1.1) coordinate.1.2
    simpa only [pairedCompletionReward_free] using h

/-- Every actual member is reconstructed from its own singleton levels and
its actual final reward coordinates. No favorable table is another input. -/
theorem pairedCompletionReward_reconstruct (reward : PairedTerminal → Payoff (Fin 4))
    (hclass : IsPairedCenteredCompletion reward) :
    pairedCompletionReward (fun who => quittingSoloReward reward who who)
      (fun coordinate => reward coordinate.1.1 coordinate.1.2) = reward := by
  funext terminal who
  by_cases hsingle : terminal.1.card = 1
  · obtain ⟨owner, howner⟩ := Finset.card_eq_one.mp hsingle
    have hterminal : terminal = quittingSingletonTerminal owner := Subtype.ext howner
    rw [hterminal, pairedCompletionReward_singleton]
    have hentry := congrFun (congrFun hclass.1 who) owner
    change reward (quittingSingletonTerminal owner) who -
        reward (quittingSingletonTerminal who) who = pairedSingletonMatrix who owner at hentry
    rw [quittingSoloReward_self]
    linarith
  · by_cases hwho : who = 1
    · subst who
      rw [pairedCompletionReward_recipientOne _ _ terminal hsingle,
        pairedCompletionReward_free _ _
          ⟨((quittingCoalitionEquiv (Equiv.swap (0 : Fin 4) 1)).symm terminal, 0),
            by rwa [pulledTerminal_card], by change (0 : Fin 4) ≠ 1; decide⟩]
      have hcenter := hclass.2
        ((quittingCoalitionEquiv (Equiv.swap (0 : Fin 4) 1)).symm terminal)
      change reward (quittingCoalitionEquiv (Equiv.swap (0 : Fin 4) 1)
          ((quittingCoalitionEquiv (Equiv.swap (0 : Fin 4) 1)).symm terminal)) 1 -
            quittingSoloReward reward 1 1 =
        reward ((quittingCoalitionEquiv (Equiv.swap (0 : Fin 4) 1)).symm terminal) 0 -
          quittingSoloReward reward 0 0 at hcenter
      rw [Equiv.apply_symm_apply] at hcenter
      dsimp only
      linarith
    · exact pairedCompletionReward_free _ _ ⟨(terminal, who), hsingle, hwho⟩

/-- The image of the coordinate chart is exactly the original paired class. -/
theorem isPairedCenteredCompletion_iff_exists_coordinates
    (reward : PairedTerminal → Payoff (Fin 4)) :
    IsPairedCenteredCompletion reward ↔
      ∃ solo : Payoff (Fin 4), ∃ free : PairedFreeRewardSpace,
        pairedCompletionReward solo free = reward := by
  constructor
  · intro hclass
    exact ⟨_, _, pairedCompletionReward_reconstruct reward hclass⟩
  · rintro ⟨solo, free, rfl⟩
    exact pairedCompletionReward_class solo free

/-- UE is produced anew for each completely arbitrary signed coordinate input. -/
theorem pairedCompletionReward_exists_uniformPayoff (solo : Payoff (Fin 4))
    (free : PairedFreeRewardSpace) :
    ∃ value, (quittingGame (pairedCompletionReward solo free)).IsUniformEquilibriumPayoff
      none value :=
  exists_uniformEquilibriumPayoff_of_pairedCenteredCompletion _
    (pairedCompletionReward_class solo free)

end PairedResponseQuotient
end GameTheory
