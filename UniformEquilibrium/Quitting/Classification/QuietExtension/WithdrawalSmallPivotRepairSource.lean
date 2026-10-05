import UniformEquilibrium.Quitting.Classification.QuietExtension.WithdrawalFiniteQuietSource
import UniformEquilibrium.Quitting.Terminal.FiniteDeadlineTimingQuietTransport
import UniformEquilibrium.Quitting.Terminal.PivotRepairSmallValueSource

/-! # Original withdrawal certificates produce small pivot-repair values

The finite quiet profile is the actual LP competitor. Nonpivot marginals
are retained; no optimal-pivot compatibility hypothesis is required.
-/

noncomputable section

namespace GameTheory

open StochasticGame Filter Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Deleting one pivot and selecting a nonnegative low-player child supplies
actual finite nonpivot laws with arbitrarily small inner-LP objective. -/
theorem smallPivotRepairValue_of_nonnegativeSingleton_withdrawalFamily
    (reward : {A : Finset ι // A.Nonempty} → Payoff ι) (pivot : ι)
    (kind : {who : ι // who = pivot} → WithdrawalFutureJoinKind)
    (certificate : ∀ outside : {who : ι // who = pivot},
      WithdrawalFutureJoinRewardCertificate (kind outside)
        (quittingChildWithOutsiderReward reward (· = pivot) outside))
    (hcard : Fintype.card {who : ι // who ≠ pivot} ≤ 3)
    (childPivot : {who : ι // who ≠ pivot})
    (hsingleton : 0 ≤ reward (quittingSingletonTerminal childPivot.1) childPivot.1) :
    HasQuittingSmallPivotRepairValue reward pivot := by
  let : Nonempty ι := ⟨pivot⟩
  let : Nonempty {who : ι // who = pivot} := ⟨⟨pivot, rfl⟩⟩
  obtain ⟨deadlines, mixed, _, hdeadlines, hexploit, _, _⟩ :=
    exists_uniformFiniteQuietFamily_of_withdrawalFutureJoinFamily
      (· = pivot) reward kind certificate hcard childPivot hsingleton
  intro error herror
  obtain ⟨n, hn⟩ := ((tendsto_order.mp hexploit).2 error herror).exists
  let fullMixed := quittingExtendDeletedFiniteTimingLaws (· = pivot) (deadlines n) (mixed n)
  obtain ⟨mass, hmass, hobjective⟩ :=
    exists_pivotRepairMass_objective_le_finiteMenu_exploitability
      reward pivot (deadlines n) (hdeadlines n) fullMixed
  have hquiet : quittingTerminalExploitability reward
      (quittingFiniteDeadlineTimingProfile reward (deadlines n) fullMixed) < error := by
    rw [← quittingFiniteDeadlineTimingProfile_extendDeleted]
    exact hn
  refine ⟨deadlines n, hdeadlines n,
    (fun who => (quittingFiniteDeadlineTimingLaw (fullMixed who)).toPMF),
    (fun who => isFiniteClockStoppingLaw_finiteDeadlineTimingLaw (fullMixed who)),
    mass, hmass, hobjective.trans_lt hquiet⟩

/-- In Fin4, nonnegative nonpivot singleton rewards and original certificates
produce the small-pivot source. In particular this covers the normalized
own-singleton vector with one pivot equal to one and all others zero. -/
theorem smallPivotRepairValue_of_finFour_nonnegativeNonpivot_withdrawalFamily
    (reward : {A : Finset (Fin 4) // A.Nonempty} → Payoff (Fin 4)) (pivot : Fin 4)
    (kind : {who : Fin 4 // who = pivot} → WithdrawalFutureJoinKind)
    (certificate : ∀ outside : {who : Fin 4 // who = pivot},
      WithdrawalFutureJoinRewardCertificate (kind outside)
        (quittingChildWithOutsiderReward reward (· = pivot) outside))
    (hsingleton : ∀ who, who ≠ pivot → 0 ≤ reward (quittingSingletonTerminal who) who) :
    HasQuittingSmallPivotRepairValue reward pivot := by
  obtain ⟨childPivot, hchildPivot⟩ := exists_ne pivot
  have hlt : Fintype.card {who : Fin 4 // who ≠ pivot} < 4 := by
    simpa only [Fintype.card_fin] using
      (Fintype.card_subtype_lt (p := fun who : Fin 4 => who ≠ pivot)
        (x := pivot) (by simp))
  exact smallPivotRepairValue_of_nonnegativeSingleton_withdrawalFamily
    reward pivot kind certificate (Nat.le_of_lt_succ hlt)
    ⟨childPivot, hchildPivot⟩ (hsingleton childPivot hchildPivot)

/-- The normalized Fin4 own-singleton vector `(1,0,0,0)`, with its pivot
placed at any label, supplies the small-pivot source from original certificates. -/
theorem smallPivotRepairValue_of_finFour_singlePivotSingletons_withdrawalFamily
    (reward : {A : Finset (Fin 4) // A.Nonempty} → Payoff (Fin 4)) (pivot : Fin 4)
    (kind : {who : Fin 4 // who = pivot} → WithdrawalFutureJoinKind)
    (certificate : ∀ outside : {who : Fin 4 // who = pivot},
      WithdrawalFutureJoinRewardCertificate (kind outside)
        (quittingChildWithOutsiderReward reward (· = pivot) outside))
    (hsingletons : ∀ who, reward (quittingSingletonTerminal who) who =
      if who = pivot then 1 else 0) :
    HasQuittingSmallPivotRepairValue reward pivot := by
  apply smallPivotRepairValue_of_finFour_nonnegativeNonpivot_withdrawalFamily
    reward pivot kind certificate
  intro who hwho
  rw [hsingletons, ite_eq_right hwho]

end GameTheory
