import UniformEquilibrium.Quitting.Examples.BlockPair.PairedResponseQuotientCoordinates

/-!
# A single-coordinate asymmetric paired completion

Changing only recipient two's final reward at coalition {0,2} preserves the
centered paired class. An internally chosen value breaks whole-table symmetry
under the swap of players zero and one. There is no sign restriction on any
coordinate, and no full-dimensional open-class assertion.
-/

noncomputable section

namespace GameTheory
namespace PairedResponseQuotient

open QuittingLCPClassification

/-- The actual coalition whose recipient-two reward is changed. -/
def pairedAsymmetryTerminal : PairedTerminal := ⟨{0, 2}, by decide⟩

/-- Its actual image under the swap of players zero and one. -/
def pairedAsymmetryMate : PairedTerminal := ⟨{1, 2}, by decide⟩

/-- Update exactly one actual terminal-recipient coordinate. -/
def pairedCoordinateUpdate (reward : PairedTerminal → Payoff (Fin 4)) (value : ℝ) :
    PairedTerminal → Payoff (Fin 4) :=
  fun terminal who =>
    if terminal = pairedAsymmetryTerminal ∧ who = 2 then value else reward terminal who

theorem pairedCoordinateUpdate_at (reward : PairedTerminal → Payoff (Fin 4)) (value : ℝ) :
    pairedCoordinateUpdate reward value pairedAsymmetryTerminal 2 = value := by
  exact ite_eq_left ⟨rfl, rfl⟩

/-- Every other actual terminal-recipient coordinate is unchanged. -/
theorem pairedCoordinateUpdate_eq_of_ne (reward : PairedTerminal → Payoff (Fin 4))
    (value : ℝ) (terminal : PairedTerminal) (who : Fin 4)
    (hother : terminal ≠ pairedAsymmetryTerminal ∨ who ≠ 2) :
    pairedCoordinateUpdate reward value terminal who = reward terminal who := by
  rcases hother with hterminal | hwho
  · simp only [pairedCoordinateUpdate, hterminal, false_and, ite_false]
  · simp only [pairedCoordinateUpdate, hwho, and_false, ite_false]

private theorem singleton_ne_asymmetryTerminal (owner : Fin 4) :
    quittingSingletonTerminal owner ≠ pairedAsymmetryTerminal := by
  intro hequal
  have hcard := congrArg (fun terminal : PairedTerminal => terminal.1.card) hequal
  norm_num [quittingSingletonTerminal, pairedAsymmetryTerminal] at hcard

theorem pairedCoordinateUpdate_singleton (reward : PairedTerminal → Payoff (Fin 4))
    (value : ℝ) (owner who : Fin 4) :
    pairedCoordinateUpdate reward value (quittingSingletonTerminal owner) who =
      reward (quittingSingletonTerminal owner) who :=
  pairedCoordinateUpdate_eq_of_ne reward value _ _ (Or.inl (singleton_ne_asymmetryTerminal _))

private theorem recipient_zero_unchanged (reward : PairedTerminal → Payoff (Fin 4))
    (value : ℝ) (terminal : PairedTerminal) :
    pairedCoordinateUpdate reward value terminal 0 = reward terminal 0 :=
  pairedCoordinateUpdate_eq_of_ne reward value terminal 0 (Or.inr (by decide))

private theorem recipient_one_unchanged (reward : PairedTerminal → Payoff (Fin 4))
    (value : ℝ) (terminal : PairedTerminal) :
    pairedCoordinateUpdate reward value terminal 1 = reward terminal 1 :=
  pairedCoordinateUpdate_eq_of_ne reward value terminal 1 (Or.inr (by decide))

/-- The one-coordinate update preserves the whole singleton matrix and both centered rows. -/
theorem pairedCoordinateUpdate_class (reward : PairedTerminal → Payoff (Fin 4)) (value : ℝ)
    (hclass : IsPairedCenteredCompletion reward) :
    IsPairedCenteredCompletion (pairedCoordinateUpdate reward value) := by
  constructor
  · refine Eq.trans (b := quittingSingletonMatrix reward) ?_ hclass.1
    ext who owner
    change pairedCoordinateUpdate reward value (quittingSingletonTerminal owner) who -
        pairedCoordinateUpdate reward value (quittingSingletonTerminal who) who =
      reward (quittingSingletonTerminal owner) who -
        reward (quittingSingletonTerminal who) who
    rw [pairedCoordinateUpdate_singleton, pairedCoordinateUpdate_singleton]
  · intro terminal
    change pairedCoordinateUpdate reward value
        (quittingCoalitionEquiv (Equiv.swap (0 : Fin 4) 1) terminal) 1 -
          quittingSoloReward (pairedCoordinateUpdate reward value) 1 1 =
      pairedCoordinateUpdate reward value terminal 0 -
        quittingSoloReward (pairedCoordinateUpdate reward value) 0 0
    rw [quittingSoloReward_self, quittingSoloReward_self,
      pairedCoordinateUpdate_singleton, pairedCoordinateUpdate_singleton,
      recipient_one_unchanged, recipient_zero_unchanged]
    exact hclass.2 terminal

private theorem swapped_asymmetryTerminal :
    quittingCoalitionEquiv (Equiv.swap (0 : Fin 4) 1) pairedAsymmetryTerminal =
      pairedAsymmetryMate := by
  apply Subtype.ext
  norm_num [quittingCoalitionEquiv, pairedAsymmetryTerminal, pairedAsymmetryMate,
    Equiv.swap_apply_def]

private theorem asymmetryMate_ne_terminal : pairedAsymmetryMate ≠ pairedAsymmetryTerminal := by
  decide

/-- An unequal scalar breaks literal whole-table covariance under the player swap. -/
theorem pairedCoordinateUpdate_not_swapCovariant
    (reward : PairedTerminal → Payoff (Fin 4)) (value : ℝ)
    (hvalue : value ≠ reward pairedAsymmetryMate 2) :
    ¬ ∀ terminal who,
      pairedCoordinateUpdate reward value
          (quittingCoalitionEquiv (Equiv.swap (0 : Fin 4) 1) terminal)
          ((Equiv.swap (0 : Fin 4) 1) who) =
        pairedCoordinateUpdate reward value terminal who := by
  intro hswap
  have hentry := hswap pairedAsymmetryTerminal 2
  have htwo : (Equiv.swap (0 : Fin 4) 1) 2 = 2 := by decide
  rw [swapped_asymmetryTerminal, htwo,
    pairedCoordinateUpdate_eq_of_ne reward value _ _ (Or.inl asymmetryMate_ne_terminal),
    pairedCoordinateUpdate_at] at hentry
  exact hvalue hentry.symm

/-- An explicit asymmetric member produced from every arbitrary signed chart input. -/
def pairedAsymmetricCompletionReward (solo : Payoff (Fin 4)) (free : PairedFreeRewardSpace) :
    PairedTerminal → Payoff (Fin 4) :=
  pairedCoordinateUpdate (pairedCompletionReward solo free)
    (max (pairedCompletionReward solo free pairedAsymmetryTerminal 2)
      (pairedCompletionReward solo free pairedAsymmetryMate 2) + 1)

/-- No chosen favorable table or unequal-scalar premise is needed for this construction. -/
theorem pairedAsymmetricCompletionReward_properties (solo : Payoff (Fin 4))
    (free : PairedFreeRewardSpace) :
    IsPairedCenteredCompletion (pairedAsymmetricCompletionReward solo free) ∧
      pairedAsymmetricCompletionReward solo free pairedAsymmetryTerminal 2 =
        max (pairedCompletionReward solo free pairedAsymmetryTerminal 2)
          (pairedCompletionReward solo free pairedAsymmetryMate 2) + 1 ∧
      pairedAsymmetricCompletionReward solo free pairedAsymmetryTerminal 2 ≠
        pairedCompletionReward solo free pairedAsymmetryTerminal 2 ∧
      (∀ terminal who, terminal ≠ pairedAsymmetryTerminal ∨ who ≠ 2 →
        pairedAsymmetricCompletionReward solo free terminal who =
          pairedCompletionReward solo free terminal who) ∧
      ¬ (∀ terminal who,
        pairedAsymmetricCompletionReward solo free
            (quittingCoalitionEquiv (Equiv.swap (0 : Fin 4) 1) terminal)
            ((Equiv.swap (0 : Fin 4) 1) who) =
          pairedAsymmetricCompletionReward solo free terminal who) := by
  refine ⟨pairedCoordinateUpdate_class _ _ (pairedCompletionReward_class solo free),
    pairedCoordinateUpdate_at _ _, ?_, ?_, ?_⟩
  · rw [show pairedAsymmetricCompletionReward solo free pairedAsymmetryTerminal 2 =
        max (pairedCompletionReward solo free pairedAsymmetryTerminal 2)
          (pairedCompletionReward solo free pairedAsymmetryMate 2) + 1 from
        pairedCoordinateUpdate_at _ _]
    linarith [le_max_left (pairedCompletionReward solo free pairedAsymmetryTerminal 2)
      (pairedCompletionReward solo free pairedAsymmetryMate 2)]
  · exact fun terminal who hother => pairedCoordinateUpdate_eq_of_ne _ _ terminal who hother
  · apply pairedCoordinateUpdate_not_swapCovariant
    linarith [le_max_right (pairedCompletionReward solo free pairedAsymmetryTerminal 2)
      (pairedCompletionReward solo free pairedAsymmetryMate 2)]

/-- Each asymmetric constructed table still has an actual fixed UE target. -/
theorem pairedAsymmetricCompletionReward_exists_uniformPayoff (solo : Payoff (Fin 4))
    (free : PairedFreeRewardSpace) :
    ∃ value, (quittingGame (pairedAsymmetricCompletionReward solo free)).IsUniformEquilibriumPayoff
      none value :=
  exists_uniformEquilibriumPayoff_of_pairedCenteredCompletion _
    (pairedAsymmetricCompletionReward_properties solo free).1

end PairedResponseQuotient
end GameTheory
