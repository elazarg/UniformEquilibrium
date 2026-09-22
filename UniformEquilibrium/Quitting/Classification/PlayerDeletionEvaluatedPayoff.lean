import MathUE.PMFProduct.PrincipalRestriction
import MathUE.PMFProduct.Reindex
import UniformEquilibrium.Quitting.Classification.PlayerDeletionLift
import UniformEquilibrium.Quitting.Paths.StoppingLawEvaluatedPayoff

/-!
# Evaluated-payoff naturality for deleting Never players

The canonical Never lift from a deleted-player quitting game preserves every
survivor's stopping-law evaluated payoff and unrestricted evaluated replacement
cap.  The proof removes the pure-Never coordinates from the independent product
law and reindexes the remaining coordinates to the existing survivor subtype.
-/

noncomputable section

namespace GameTheory

open _root_.Math _root_.Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

private def extendDeletedClocks (deleted : ι → Prop) [DecidablePred deleted]
    (times : {who : ι // ¬ deleted who} → Option ℕ) : ι → Option ℕ :=
  fun who => if h : deleted who then none else times ⟨who, h⟩

private def extendDeletedStoppingLaws
    (deleted : ι → Prop) [DecidablePred deleted]
    (laws : {who : ι // ¬ deleted who} → PMF (Option ℕ)) :
    ι → PMF (Option ℕ) :=
  fun who => if h : deleted who then PMF.pure none else laws ⟨who, h⟩

section NonemptySurvivor

variable (deleted : ι → Prop) [DecidablePred deleted]
variable [Nonempty ι] [Nonempty {who : ι // ¬ deleted who}]

omit [DecidableEq ι] [Nonempty ι] in
private theorem quittingEarliestStoppingValue_extendDeletedClocks
    (times : {who : ι // ¬ deleted who} → Option ℕ) :
    quittingEarliestStoppingValue (extendDeletedClocks deleted times) =
      quittingEarliestStoppingValue times := by
  unfold quittingEarliestStoppingValue
  apply le_antisymm
  · obtain ⟨who, -, hwho⟩ := Finset.exists_mem_eq_inf
      (Finset.univ : Finset {who : ι // ¬ deleted who})
      Finset.univ_nonempty (fun i => quittingStoppingTimeValue (times i))
    calc
      Finset.univ.inf (fun i => quittingStoppingTimeValue
          (extendDeletedClocks deleted times i)) ≤
        quittingStoppingTimeValue (extendDeletedClocks deleted times who.1) :=
          Finset.inf_le (Finset.mem_univ who.1)
      _ = quittingStoppingTimeValue (times who) := by
        simp [extendDeletedClocks, who.2]
      _ = Finset.univ.inf
          (fun i => quittingStoppingTimeValue (times i)) := hwho.symm
  · apply Finset.le_inf
    intro player _
    by_cases hp : deleted player
    · simp [extendDeletedClocks, hp, quittingStoppingTimeValue]
    · simpa [extendDeletedClocks, hp] using
        (Finset.inf_le
          (f := fun i : {who : ι // ¬ deleted who} =>
            quittingStoppingTimeValue (times i))
          (Finset.mem_univ ⟨player, hp⟩))

omit [DecidableEq ι] in
private theorem quittingFirstStoppingOutcome_extendDeletedClocks
    (times : {who : ι // ¬ deleted who} → Option ℕ) :
    quittingFirstStoppingOutcome (extendDeletedClocks deleted times) =
      (quittingFirstStoppingOutcome times).map
        (quittingExtendDeletedCoalition deleted) := by
  let first := quittingEarliestStoppingValue times
  have hfirst : quittingEarliestStoppingValue
      (extendDeletedClocks deleted times) = first :=
    quittingEarliestStoppingValue_extendDeletedClocks
      (deleted := deleted) times
  by_cases htop : first = ⊤
  · simp only [quittingFirstStoppingOutcome, hfirst, first, htop,
      ↓reduceIte, Option.map_none]
  · have hcoalition : quittingEarliestStoppingCoalition
        (extendDeletedClocks deleted times) =
      (quittingEarliestStoppingCoalition times).map
        (Function.Embedding.subtype
          (p := fun who : ι => ¬ deleted who)) := by
      ext player
      have htop' : (⊤ : WithTop ℕ) ≠ first := by
        simpa [ne_comm] using htop
      by_cases hp : deleted player
      · simp [quittingEarliestStoppingCoalition, extendDeletedClocks,
          hfirst, first, hp, htop', quittingStoppingTimeValue]
      · simp [quittingEarliestStoppingCoalition, extendDeletedClocks,
          hfirst, first, hp]
    rw [quittingFirstStoppingOutcome, quittingFirstStoppingOutcome, hfirst]
    simp [first, htop, hcoalition, quittingExtendDeletedCoalition]

omit [DecidableEq ι] in
private theorem quittingPureClockEvaluatedPayoff_extendDeletedClocks
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (evaluation : WithTop ℕ → ℝ)
    (times : {who : ι // ¬ deleted who} → Option ℕ)
    (who : {who : ι // ¬ deleted who}) :
    quittingPureClockEvaluatedPayoff reward evaluation
        (extendDeletedClocks deleted times) who.1 =
      quittingPureClockEvaluatedPayoff
        (quittingDeleteReward reward deleted) evaluation times who := by
  unfold quittingPureClockEvaluatedPayoff
  rw [quittingFirstStoppingOutcome_extendDeletedClocks
      (deleted := deleted) times,
    quittingEarliestStoppingValue_extendDeletedClocks
      (deleted := deleted) times]
  cases quittingFirstStoppingOutcome times <;>
    simp [quittingDeleteReward]

end NonemptySurvivor

omit [Fintype ι] in
private theorem extendDeletedStoppingLaws_update
    (deleted : ι → Prop) [DecidablePred deleted]
    (laws : {who : ι // ¬ deleted who} → PMF (Option ℕ))
    (who : {who : ι // ¬ deleted who}) (replacement : PMF (Option ℕ)) :
    Function.update (extendDeletedStoppingLaws deleted laws) who.1 replacement =
      extendDeletedStoppingLaws deleted
        (Function.update laws who replacement) := by
  funext player
  by_cases heq : player = who.1
  · subst player
    simp [extendDeletedStoppingLaws, who.2]
  · by_cases hp : deleted player
    · simp [extendDeletedStoppingLaws, hp, Function.update_of_ne heq]
    · have hsub : (⟨player, hp⟩ : {who : ι // ¬ deleted who}) ≠ who := by
        intro h
        exact heq (congrArg Subtype.val h)
      simp [extendDeletedStoppingLaws, hp, Function.update_of_ne heq,
        Function.update_of_ne hsub]

section NonemptySurvivor

variable (deleted : ι → Prop) [DecidablePred deleted]
variable [Nonempty ι] [Nonempty {who : ι // ¬ deleted who}]

private theorem quittingStoppingLawEvaluatedPayoff_extendDeletedStoppingLaws
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (evaluation : WithTop ℕ → ℝ)
    (laws : {who : ι // ¬ deleted who} → PMF (Option ℕ))
    (who : {who : ι // ¬ deleted who}) :
    quittingStoppingLawEvaluatedPayoff reward evaluation
        (extendDeletedStoppingLaws deleted laws) who.1 =
      quittingStoppingLawEvaluatedPayoff
        (quittingDeleteReward reward deleted) evaluation laws who := by
  let players : Finset ι := Finset.univ.filter fun player => ¬ deleted player
  let playerEquiv : players ≃ {who : ι // ¬ deleted who} :=
    Equiv.subtypeEquivRight fun player => by simp [players]
  let clockEquiv : (players → Option ℕ) ≃
      ({who : ι // ¬ deleted who} → Option ℕ) :=
    playerEquiv.arrowCongr (Equiv.refl (Option ℕ))
  let fullLaws := extendDeletedStoppingLaws deleted laws
  have hpure : ∀ player, player ∉ players →
      fullLaws player = PMF.pure none := by
    intro player hplayer
    have hp : deleted player := by
      simpa [players] using hplayer
    simp [fullLaws, extendDeletedStoppingLaws, hp]
  have hprincipal := expect_pmfPi_eq_principal fullLaws players
    (fun _ => none) hpure
    (fun times => quittingPureClockEvaluatedPayoff reward evaluation times who.1)
  have hmap : PMF.map clockEquiv
        (pmfPi (principalMarginals fullLaws players)) =
      pmfPi laws := by
    calc
      PMF.map clockEquiv (pmfPi (principalMarginals fullLaws players)) =
          pmfPi (fun player =>
            principalMarginals fullLaws players (playerEquiv.symm player)) := by
        exact pmfPi_map_precompEquiv playerEquiv clockEquiv
          (fun _ _ => rfl) (principalMarginals fullLaws players)
      _ = pmfPi laws := by
        congr 1
        funext player
        simp [principalMarginals, fullLaws, extendDeletedStoppingLaws,
          playerEquiv, players, player.2]
  have hextend (times : players → Option ℕ) :
      principalExtend players (fun _ => none) times =
        extendDeletedClocks deleted (clockEquiv times) := by
    funext player
    by_cases hp : deleted player
    · have hnotmem : player ∉ players := by simp [players, hp]
      simp [principalExtend_apply_not_mem players (fun _ => none) times hnotmem,
        extendDeletedClocks, hp]
    · have hmem : player ∈ players := by simp [players, hp]
      let selected : players := ⟨player, hmem⟩
      have heq : playerEquiv selected =
          (⟨player, hp⟩ : {who : ι // ¬ deleted who}) := by
        rfl
      have hclock : clockEquiv times ⟨player, hp⟩ = times selected := by
        rw [← heq]
        rfl
      simp [principalExtend, extendDeletedClocks, hp, hmem, hclock, selected]
  have hexpect := congrArg
    (fun law => expect law (fun times =>
      quittingPureClockEvaluatedPayoff
        (quittingDeleteReward reward deleted) evaluation times who)) hmap
  rw [expect_map] at hexpect
  unfold quittingStoppingLawEvaluatedPayoff
  calc
    expect (pmfPi fullLaws)
        (fun times => quittingPureClockEvaluatedPayoff reward evaluation
          times who.1) =
      expect (pmfPi (principalMarginals fullLaws players))
        (fun times => quittingPureClockEvaluatedPayoff reward evaluation
          (principalExtend players (fun _ => none) times) who.1) := hprincipal
    _ = expect (pmfPi (principalMarginals fullLaws players))
        (fun times => quittingPureClockEvaluatedPayoff
          (quittingDeleteReward reward deleted) evaluation
            (clockEquiv times) who) := by
      apply congrArg
      funext times
      rw [hextend]
      exact quittingPureClockEvaluatedPayoff_extendDeletedClocks
        (deleted := deleted) reward evaluation (clockEquiv times) who
    _ = expect (pmfPi laws) (fun times =>
        quittingPureClockEvaluatedPayoff
          (quittingDeleteReward reward deleted) evaluation times who) := hexpect

private theorem
    quittingStoppingLawEvaluatedReplacementCap_extendDeletedStoppingLaws
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (evaluation : WithTop ℕ → ℝ)
    (laws : {who : ι // ¬ deleted who} → PMF (Option ℕ))
    (who : {who : ι // ¬ deleted who}) :
    quittingStoppingLawEvaluatedReplacementPayoffCap reward evaluation
        (extendDeletedStoppingLaws deleted laws) who.1 =
      quittingStoppingLawEvaluatedReplacementPayoffCap
        (quittingDeleteReward reward deleted) evaluation laws who := by
  unfold quittingStoppingLawEvaluatedReplacementPayoffCap
  apply congrArg sSup
  congr 1
  funext replacement
  rw [extendDeletedStoppingLaws_update]
  exact quittingStoppingLawEvaluatedPayoff_extendDeletedStoppingLaws
    (deleted := deleted) reward evaluation
      (Function.update laws who replacement) who

omit [Nonempty ι] [Nonempty {who : ι // ¬ deleted who}] in
private theorem
    quittingBehaviorStoppingLaws_liftDeletedProfile_eq_extendDeletedStoppingLaws
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame
      (quittingDeleteReward reward deleted)).BehaviorProfile) :
    quittingBehaviorStoppingLaws reward
        (quittingLiftDeletedProfile reward deleted profile) =
      extendDeletedStoppingLaws deleted
        (quittingBehaviorStoppingLaws
          (quittingDeleteReward reward deleted) profile) := by
  funext player
  by_cases hp : deleted player
  · exact (quittingBehaviorStoppingLaw_liftDeletedProfile_of_deleted
      reward deleted profile hp).trans (by
        simp [extendDeletedStoppingLaws, hp])
  · let survivor : {who : ι // ¬ deleted who} := ⟨player, hp⟩
    exact (quittingBehaviorStoppingLaw_liftDeletedProfile
      reward deleted profile survivor).trans (by
        simp [extendDeletedStoppingLaws, quittingBehaviorStoppingLaws,
          hp, survivor])

/-- The canonical Never lift preserves every survivor's evaluated payoff. -/
theorem quittingBehaviorEvaluatedPayoff_liftDeletedProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (evaluation : WithTop ℕ → ℝ)
    (profile : (quittingGame
      (quittingDeleteReward reward deleted)).BehaviorProfile)
    (who : {who : ι // ¬ deleted who}) :
    quittingBehaviorEvaluatedPayoff reward evaluation
        (quittingLiftDeletedProfile reward deleted profile) who.1 =
      quittingBehaviorEvaluatedPayoff
        (quittingDeleteReward reward deleted) evaluation profile who := by
  unfold quittingBehaviorEvaluatedPayoff
  rw [quittingBehaviorStoppingLaws_liftDeletedProfile_eq_extendDeletedStoppingLaws
    (deleted := deleted) (reward := reward) (profile := profile)]
  exact quittingStoppingLawEvaluatedPayoff_extendDeletedStoppingLaws
    (deleted := deleted) reward evaluation
      (quittingBehaviorStoppingLaws
        (quittingDeleteReward reward deleted) profile) who

/-- The canonical Never lift preserves every survivor's unrestricted evaluated
behavioral replacement cap. -/
theorem quittingBehaviorEvaluatedDeviationPayoffCap_liftDeletedProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (evaluation : WithTop ℕ → ℝ)
    (profile : (quittingGame
      (quittingDeleteReward reward deleted)).BehaviorProfile)
    (who : {who : ι // ¬ deleted who}) :
    quittingBehaviorEvaluatedDeviationPayoffCap reward evaluation
        (quittingLiftDeletedProfile reward deleted profile) who.1 =
      quittingBehaviorEvaluatedDeviationPayoffCap
        (quittingDeleteReward reward deleted) evaluation profile who := by
  rw [← quittingStoppingLawEvaluatedCap_behaviorStoppingLaws_eq_behaviorCap,
    ← quittingStoppingLawEvaluatedCap_behaviorStoppingLaws_eq_behaviorCap,
    quittingBehaviorStoppingLaws_liftDeletedProfile_eq_extendDeletedStoppingLaws
      (deleted := deleted) (reward := reward) (profile := profile)]
  exact
    quittingStoppingLawEvaluatedReplacementCap_extendDeletedStoppingLaws
      (deleted := deleted) reward evaluation
        (quittingBehaviorStoppingLaws
          (quittingDeleteReward reward deleted) profile) who

/-- Evaluated deviation debt is preserved coordinatewise by the Never lift. -/
theorem quittingBehaviorEvaluatedDeviationDebt_liftDeletedProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (evaluation : WithTop ℕ → ℝ)
    (profile : (quittingGame
      (quittingDeleteReward reward deleted)).BehaviorProfile)
    (who : {who : ι // ¬ deleted who}) :
    quittingBehaviorEvaluatedDeviationPayoffCap reward evaluation
          (quittingLiftDeletedProfile reward deleted profile) who.1 -
        quittingBehaviorEvaluatedPayoff reward evaluation
          (quittingLiftDeletedProfile reward deleted profile) who.1 =
      quittingBehaviorEvaluatedDeviationPayoffCap
          (quittingDeleteReward reward deleted) evaluation profile who -
        quittingBehaviorEvaluatedPayoff
          (quittingDeleteReward reward deleted) evaluation profile who := by
  rw [quittingBehaviorEvaluatedDeviationPayoffCap_liftDeletedProfile
      (deleted := deleted) (reward := reward) (evaluation := evaluation)
      (profile := profile) (who := who),
    quittingBehaviorEvaluatedPayoff_liftDeletedProfile
      (deleted := deleted) (reward := reward) (evaluation := evaluation)
      (profile := profile) (who := who)]

end NonemptySurvivor

end GameTheory
