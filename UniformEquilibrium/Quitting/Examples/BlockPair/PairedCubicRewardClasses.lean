import UniformEquilibrium.Quitting.Examples.BlockPair.PairedCubicStationaryExample
import UniformEquilibrium.Quitting.Examples.BlockPair.PairedResponseQuotientClass

/-! # Literal reward-class attachments for the cubic stationary example

The original table has whole-table covariance under the swap of players zero
and one. Its canonical recipient translation retains the centered paired class
and singleton matrix but loses that covariance. Never remains zero throughout;
these identities are not arbitrary-profile strategic equivalence assertions.
-/

noncomputable section

namespace GameTheory.PairedCubicStationaryExample

open Math.Finset QuittingLCPClassification

/-- All four own-singleton rewards of the original literal table are one. -/
theorem reward_ownSingleton (who : Fin 4) :
    reward (quittingSingletonTerminal who) who = 1 := by
  fin_cases who <;>
    norm_num +decide [reward, rationalQuittingRewardToReal, rationalReward,
      quittingSingletonTerminal]

/-- The original fifteen-row table is covariant under the whole player swap. -/
theorem reward_swapCovariant
    (terminal : {S : Finset (Fin 4) // S.Nonempty}) (who : Fin 4) :
    reward (quittingCoalitionEquiv (Equiv.swap (0 : Fin 4) 1) terminal)
        ((Equiv.swap (0 : Fin 4) 1) who) = reward terminal who := by
  obtain ⟨row, rfl⟩ := finFourCoalitionRowEquiv.surjective terminal
  fin_cases row <;> fin_cases who <;>
    norm_num +decide [reward, rationalQuittingRewardToReal, rationalReward,
      quittingCoalitionEquiv, Equiv.swap_apply_def, finFourCoalitionRowEquiv,
      finFourCoalitionOfRow]

/-- The exact cubic table belongs to the actual centered paired reward class. -/
theorem reward_pairedCenteredCompletion :
    PairedResponseQuotient.IsPairedCenteredCompletion reward := by
  refine ⟨singletonMatrix, ?_⟩
  intro terminal
  change reward (quittingCoalitionEquiv (Equiv.swap (0 : Fin 4) 1) terminal) 1 -
      quittingSoloReward reward 1 1 =
    reward terminal 0 - quittingSoloReward reward 0 0
  have hrow :
      reward (quittingCoalitionEquiv (Equiv.swap (0 : Fin 4) 1) terminal) 1 =
        reward terminal 0 := by
    simpa only [Equiv.swap_apply_left] using reward_swapCovariant terminal 0
  rw [quittingSoloReward_self, quittingSoloReward_self,
    reward_ownSingleton, reward_ownSingleton, hrow]

/-- The literal canonical table retains the full original singleton matrix. -/
theorem canonicalReward_singletonMatrix :
    quittingSingletonMatrix canonicalReward =
      FourPlayerPairedSingleton.pairedSingletonMatrix := by
  change quittingSingletonMatrix (quittingPlayerwiseAffineReward reward 1 canonicalShift) = _
  rw [quittingSingletonMatrix_playerwiseTranslation]
  exact singletonMatrix

/-- Unequal own-singleton levels do not remove the canonical table from the centered class. -/
theorem canonicalReward_pairedCenteredCompletion :
    PairedResponseQuotient.IsPairedCenteredCompletion canonicalReward := by
  refine ⟨canonicalReward_singletonMatrix, ?_⟩
  intro terminal
  change canonicalReward (quittingCoalitionEquiv (Equiv.swap (0 : Fin 4) 1) terminal) 1 -
      quittingSoloReward canonicalReward 1 1 =
    canonicalReward terminal 0 - quittingSoloReward canonicalReward 0 0
  have hcenter := reward_pairedCenteredCompletion.2 terminal
  change reward (quittingCoalitionEquiv (Equiv.swap (0 : Fin 4) 1) terminal) 1 -
      quittingSoloReward reward 1 1 =
    reward terminal 0 - quittingSoloReward reward 0 0 at hcenter
  rw [quittingSoloReward_self, quittingSoloReward_self,
    reward_ownSingleton, reward_ownSingleton] at hcenter
  rw [quittingSoloReward_self, quittingSoloReward_self,
    canonicalReward_singleton, canonicalReward_singleton]
  simp [canonicalReward, quittingPlayerwiseAffineReward, canonicalShift]
  linarith [hcenter]

/-- The canonical table does not retain the original whole-table player-swap covariance. -/
theorem canonicalReward_not_swapCovariant :
    ¬ ∀ terminal who,
      canonicalReward (quittingCoalitionEquiv (Equiv.swap (0 : Fin 4) 1) terminal)
          ((Equiv.swap (0 : Fin 4) 1) who) = canonicalReward terminal who := by
  intro hswap
  have hterminal :
      quittingCoalitionEquiv (Equiv.swap (0 : Fin 4) 1) (quittingSingletonTerminal 0) =
        quittingSingletonTerminal 1 := by
    apply Subtype.ext
    norm_num [quittingCoalitionEquiv, quittingSingletonTerminal, Equiv.swap_apply_def]
  have hentry := hswap (quittingSingletonTerminal 0) (0 : Fin 4)
  rw [hterminal, Equiv.swap_apply_left,
    canonicalReward_singleton, canonicalReward_singleton] at hentry
  norm_num at hentry

/-- Scaling the canonical table by four gives the displayed normalized singleton vector. -/
theorem normalizedReward_singleton (who : Fin 4) :
    normalizedReward (quittingSingletonTerminal who) who = ![1 / 4, 0, 0, 0] who := by
  rw [normalizedReward_eq, canonicalReward_singleton]
  fin_cases who <;> norm_num

/-- The original literal reward-class identity supplies its actual response-invariant partition. -/
theorem reward_responseInvariant :
    QuittingResponseInvariantOnUnitCube reward PairedResponseQuotient.block :=
  PairedResponseQuotient.responseInvariant_of_pairedCenteredCompletion
    reward reward_pairedCenteredCompletion

/-- The canonical table retains the same response-invariant partition, despite lost symmetry. -/
theorem canonicalReward_responseInvariant :
    QuittingResponseInvariantOnUnitCube canonicalReward PairedResponseQuotient.block :=
  PairedResponseQuotient.responseInvariant_of_pairedCenteredCompletion
    canonicalReward canonicalReward_pairedCenteredCompletion

end GameTheory.PairedCubicStationaryExample
