/-
Pure-time continuity groundwork for root-sequence quitting values.

Fix a root sequence `roots : ℕ → ι → PMF Bool` and a deviator `who`.  The
pure-time deviation value `quittingRootSequencePureTimeTerminalValue` is the
terminal payoff of the deterministic reply that quits at a given date, or
never quits.  Four facts about that value are proved here.

* Finite-time determination: the value at a finite quit date `t` only reads
  the rows at dates `≤ t`.
* Continuity: the value at a finite quit date `t` is continuous in the
  finitely many row coordinates at dates `≤ t`.
* Never-tail truncation: the `Never` value differs from the finite collected
  ledger before `T` by at most the reward bound times the still-unabsorbed
  opponent survival mass beyond `T`.
* Row estimate: quitting at date `t` differs from "collect the ledger, then
  quit solo" by at most twice the reward bound times the opponents' deleted
  absorption mass at row `t`.

All four are statements about root sequences.  Two profile-level corollaries
are recorded at the end through `quittingProfileLiveRoot`.
-/
import UniformEquilibrium.Quitting.Stationary.MinMax
import UniformEquilibrium.Quitting.Boundary.Exceptional.BellmanTail
import UniformEquilibrium.Quitting.Cycles.BehaviorPureTimeExtremality
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPositiveSlopeRectangle

noncomputable section

namespace GameTheory

open StochasticGame Filter _root_.Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## Deleted per-date absorption mass -/

/-- The opponents' absorption mass deleted at date `t`: the drop in the
opponent survival weight across that single row. -/
def fableDeletedStopMass (roots : ℕ → ι → PMF Bool) (who : ι) (t : ℕ) : ℝ :=
  quittingOpponentSurvivalWeight roots who 0 t -
    quittingOpponentSurvivalWeight roots who 0 (t + 1)

theorem fableDeletedStopMass_nonneg (roots : ℕ → ι → PMF Bool) (who : ι)
    (t : ℕ) : 0 ≤ fableDeletedStopMass roots who t := by
  have hanti := antitone_quittingOpponentSurvivalWeight roots who 0
    (Nat.le_succ t)
  simpa [fableDeletedStopMass] using sub_nonneg.mpr hanti

/-- The deleted masses telescope: the total absorption deleted strictly
before `T` is one minus the survival weight at `T`. -/
theorem sum_fableDeletedStopMass (roots : ℕ → ι → PMF Bool) (who : ι)
    (T : ℕ) :
    ∑ t ∈ Finset.range T, fableDeletedStopMass roots who t =
      1 - quittingOpponentSurvivalWeight roots who 0 T := by
  induction T with
  | zero => simp [quittingOpponentSurvivalWeight]
  | succ T ih =>
      rw [Finset.sum_range_succ, ih]
      simp [fableDeletedStopMass]

/-! ## The collected ledger before a cutoff -/

/-- The payoff collected from the opponents' absorptions strictly before `T`
while `who` continues: the repo's live ledger read from date zero. -/
def fableNeverCollect (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (T : ℕ) : ℝ :=
  quittingLiveLedgerAccum reward roots who 0 T

/-- Explicit finite-sum form of the collected ledger. -/
theorem fableNeverCollect_eq_sum
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (T : ℕ) :
    fableNeverCollect reward roots who T =
      ∑ t ∈ Finset.range T,
        quittingOpponentSurvivalWeight roots who 0 t *
          quittingFixedOpponentsContinueReward reward roots who t := by
  simp [fableNeverCollect, quittingLiveLedgerAccum]

@[simp] theorem fableNeverCollect_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) :
    fableNeverCollect reward roots who 0 = 0 := by
  simp [fableNeverCollect]

theorem fableNeverCollect_succ
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (T : ℕ) :
    fableNeverCollect reward roots who (T + 1) =
      fableNeverCollect reward roots who T +
        quittingOpponentSurvivalWeight roots who 0 T *
          quittingFixedOpponentsContinueReward reward roots who T := by
  simp [fableNeverCollect, quittingLiveLedgerAccum_zero_succ]

/-! ## Target 1: finite-time determination -/

/-- Opponent survival weights before a cutoff only read the rows before that
cutoff. -/
theorem fable_survivalWeight_congr_of_agree
    (roots roots' : ℕ → ι → PMF Bool) (who : ι) {t k : ℕ} (hk : k ≤ t)
    (h : ∀ s, s ≤ t → roots s = roots' s) :
    quittingOpponentSurvivalWeight roots who 0 k =
      quittingOpponentSurvivalWeight roots' who 0 k := by
  unfold quittingOpponentSurvivalWeight
  refine Finset.prod_congr rfl ?_
  intro offset hoffset
  have hlt : offset < k := Finset.mem_range.mp hoffset
  unfold quittingFixedOpponentsContinueMass
  rw [h (0 + offset) (by omega)]

/-- The collected ledger before a cutoff only reads the rows before that
cutoff. -/
theorem fable_neverCollect_congr_of_agree
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots roots' : ℕ → ι → PMF Bool) (who : ι) {t k : ℕ} (hk : k ≤ t)
    (h : ∀ s, s ≤ t → roots s = roots' s) :
    fableNeverCollect reward roots who k =
      fableNeverCollect reward roots' who k := by
  rw [fableNeverCollect_eq_sum, fableNeverCollect_eq_sum]
  refine Finset.sum_congr rfl ?_
  intro offset hoffset
  have hlt : offset < k := Finset.mem_range.mp hoffset
  have hweight := fable_survivalWeight_congr_of_agree roots roots' who
    (t := t) (k := offset) (by omega) h
  have hcont : quittingFixedOpponentsContinueReward reward roots who offset =
      quittingFixedOpponentsContinueReward reward roots' who offset := by
    unfold quittingFixedOpponentsContinueReward
    rw [h offset (by omega)]
  rw [hweight, hcont]

/-- **Finite-time determination.**  Two root sequences agreeing at every date
up to `t` give the same value to the deterministic reply that quits at `t`. -/
theorem fable_pureTimeValue_congr_of_agree
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots roots' : ℕ → ι → PMF Bool) (who : ι) (t : ℕ)
    (h : ∀ s, s ≤ t → roots s = roots' s) :
    quittingRootSequencePureTimeTerminalValue reward roots who (some t) =
      quittingRootSequencePureTimeTerminalValue reward roots' who (some t) := by
  rw [quittingRootSequencePureTimeTerminalValue_some_eq,
    quittingRootSequencePureTimeTerminalValue_some_eq]
  have hledger := fable_neverCollect_congr_of_agree reward roots roots' who
    (t := t) (k := t) le_rfl h
  have hweight := fable_survivalWeight_congr_of_agree roots roots' who
    (t := t) (k := t) le_rfl h
  have hquit : quittingFixedOpponentsQuitValue reward roots who t =
      quittingFixedOpponentsQuitValue reward roots' who t := by
    unfold quittingFixedOpponentsQuitValue
    rw [h t le_rfl]
  rw [show quittingLiveLedgerAccum reward roots who 0 t =
    fableNeverCollect reward roots who t from rfl,
    show quittingLiveLedgerAccum reward roots' who 0 t =
      fableNeverCollect reward roots' who t from rfl,
    hledger, hweight, hquit]

/-! ## Target 2: continuity in the row coordinates -/

/-- Coordinatewise real convergence of a sequence of product rows. -/
def FableRowTendsto (rowSeq : ℕ → ι → PMF Bool) (row : ι → PMF Bool) : Prop :=
  ∀ (j : ι) (b : Bool),
    Tendsto (fun n => ((rowSeq n j) b).toReal) atTop (nhds ((row j b).toReal))

omit [Fintype ι] in
/-- Overwriting one coordinate by a fixed marginal preserves coordinatewise
convergence. -/
theorem fable_update_rowTendsto {rowSeq : ℕ → ι → PMF Bool}
    {row : ι → PMF Bool} (h : FableRowTendsto rowSeq row) (who : ι)
    (sub : PMF Bool) :
    FableRowTendsto (fun n => Function.update (rowSeq n) who sub)
      (Function.update row who sub) := by
  intro j b
  by_cases hj : j = who
  · subst hj
    simp only [Function.update_self]
    exact tendsto_const_nhds
  · simp only [Function.update_of_ne hj]
    exact h j b

omit [DecidableEq ι] in
/-- The all-continue mass of a product row is continuous in the row
coordinates. -/
theorem fable_continueMass_tendsto {rowSeq : ℕ → ι → PMF Bool}
    {row : ι → PMF Bool} (h : FableRowTendsto rowSeq row) :
    Tendsto (fun n => quittingStationaryContinueMass (rowSeq n)) atTop
      (nhds (quittingStationaryContinueMass row)) := by
  simp only [quittingStationaryContinueMass_eq_prod_continueProbability]
  exact tendsto_finsetProd _ fun j _ => h j false

omit [DecidableEq ι] in
/-- Each joint-action weight of a product row is continuous in the row
coordinates. -/
theorem fable_pmfPi_toReal_tendsto {rowSeq : ℕ → ι → PMF Bool}
    {row : ι → PMF Bool} (h : FableRowTendsto rowSeq row)
    (action : ι → Bool) :
    Tendsto (fun n => (pmfPi (rowSeq n) action).toReal) atTop
      (nhds ((pmfPi row action).toReal)) := by
  simp only [pmfPi_apply, ENNReal.toReal_prod]
  exact tendsto_finsetProd _ fun j _ => h j (action j)

omit [DecidableEq ι] in
/-- The one-stage absorbing contribution is continuous in the row
coordinates. -/
theorem fable_rootAbsorbingContribution_tendsto
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {rowSeq : ℕ → ι → PMF Bool} {row : ι → PMF Bool}
    (h : FableRowTendsto rowSeq row) (who : ι) :
    Tendsto (fun n => quittingRootAbsorbingContribution reward (rowSeq n) who)
      atTop (nhds (quittingRootAbsorbingContribution reward row who)) := by
  unfold quittingRootAbsorbingContribution quittingRootExpectedPayoff
  exact expect_tendsto_of_forall_toReal_tendsto _
    fun action => fable_pmfPi_toReal_tendsto h action

/-- **Continuity at a fixed finite quit date.**  If the rows at every date up
to `t` converge coordinatewise, the pure-time values at `some t` converge. -/
theorem fable_pureTimeValue_tendsto
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (rootsSeq : ℕ → ℕ → ι → PMF Bool) (roots : ℕ → ι → PMF Bool) (who : ι)
    (t : ℕ)
    (h : ∀ s, s ≤ t → ∀ (j : ι) (b : Bool),
      Tendsto (fun n => ((rootsSeq n s j) b).toReal) atTop
        (nhds ((roots s j b).toReal))) :
    Tendsto
      (fun n => quittingRootSequencePureTimeTerminalValue reward (rootsSeq n)
        who (some t))
      atTop
      (nhds (quittingRootSequencePureTimeTerminalValue reward roots who
        (some t))) := by
  simp only [quittingRootSequencePureTimeTerminalValue_some_eq]
  have hrow : ∀ s, s ≤ t →
      FableRowTendsto (fun n => rootsSeq n s) (roots s) := fun s hs => h s hs
  have hmass : ∀ s, s ≤ t →
      Tendsto (fun n => quittingFixedOpponentsContinueMass (rootsSeq n) who s)
        atTop (nhds (quittingFixedOpponentsContinueMass roots who s)) := by
    intro s hs
    unfold quittingFixedOpponentsContinueMass
    exact fable_continueMass_tendsto
      (fable_update_rowTendsto (hrow s hs) who (PMF.pure false))
  have hcont : ∀ s, s ≤ t →
      Tendsto
        (fun n => quittingFixedOpponentsContinueReward reward (rootsSeq n) who s)
        atTop
        (nhds (quittingFixedOpponentsContinueReward reward roots who s)) := by
    intro s hs
    unfold quittingFixedOpponentsContinueReward
    exact fable_rootAbsorbingContribution_tendsto reward
      (fable_update_rowTendsto (hrow s hs) who (PMF.pure false)) who
  have hweight : ∀ k, k ≤ t →
      Tendsto (fun n => quittingOpponentSurvivalWeight (rootsSeq n) who 0 k)
        atTop (nhds (quittingOpponentSurvivalWeight roots who 0 k)) := by
    intro k hk
    unfold quittingOpponentSurvivalWeight
    refine tendsto_finsetProd _ fun offset hoffset => ?_
    have hlt : offset < k := Finset.mem_range.mp hoffset
    exact hmass (0 + offset) (by omega)
  have hquit :
      Tendsto (fun n => quittingFixedOpponentsQuitValue reward (rootsSeq n) who t)
        atTop (nhds (quittingFixedOpponentsQuitValue reward roots who t)) := by
    unfold quittingFixedOpponentsQuitValue
    exact fable_rootAbsorbingContribution_tendsto reward
      (fable_update_rowTendsto (hrow t le_rfl) who (PMF.pure true)) who
  have hledger :
      Tendsto (fun n => quittingLiveLedgerAccum reward (rootsSeq n) who 0 t)
        atTop (nhds (quittingLiveLedgerAccum reward roots who 0 t)) := by
    unfold quittingLiveLedgerAccum
    refine tendsto_finsetSum _ fun offset hoffset => ?_
    have hlt : offset < t := Finset.mem_range.mp hoffset
    exact (hweight offset (by omega)).mul (hcont (0 + offset) (by omega))
  exact hledger.add ((hweight t le_rfl).mul hquit)

/-! ## Target 3: the `Never` tail truncation bound -/

/-- Between two cutoffs the collected ledger moves by at most the reward
bound times the opponents' absorption deleted in between. -/
theorem fable_abs_neverCollect_sub_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ S, |reward S who| ≤ M) (T : ℕ) :
    ∀ fuel, T ≤ fuel →
      |fableNeverCollect reward roots who fuel -
          fableNeverCollect reward roots who T| ≤
        M * (quittingOpponentSurvivalWeight roots who 0 T -
          quittingOpponentSurvivalWeight roots who 0 fuel) := by
  intro fuel hfuel
  induction fuel, hfuel using Nat.le_induction with
  | base => simp
  | succ fuel hfuel ih =>
      have hstep := abs_quittingFixedOpponentsContinueReward_le_hazard
        reward roots who fuel M hM hreward
      have hW := quittingOpponentSurvivalWeight_nonneg roots who 0 fuel
      have hsucc := quittingOpponentSurvivalWeight_zero_succ roots who fuel
      have hterm :
          |quittingOpponentSurvivalWeight roots who 0 fuel *
              quittingFixedOpponentsContinueReward reward roots who fuel| ≤
            quittingOpponentSurvivalWeight roots who 0 fuel *
              (M * (1 - quittingFixedOpponentsContinueMass roots who fuel)) := by
        rw [abs_mul, abs_of_nonneg hW]
        exact mul_le_mul_of_nonneg_left hstep hW
      have hexp : fableNeverCollect reward roots who (fuel + 1) -
          fableNeverCollect reward roots who T =
          (fableNeverCollect reward roots who fuel -
              fableNeverCollect reward roots who T) +
            quittingOpponentSurvivalWeight roots who 0 fuel *
              quittingFixedOpponentsContinueReward reward roots who fuel := by
        rw [fableNeverCollect_succ]
        ring
      rw [hexp]
      refine (abs_add_le _ _).trans ?_
      have hsum := add_le_add ih hterm
      rw [hsucc]
      nlinarith [hsum]

/-- **The `Never` tail truncation bound.**  The `Never` value is the ledger
collected before `T` up to the reward bound times the opponents' absorption
still to come after `T`, measured by the drop from the survival weight at `T`
to its infimum. -/
theorem fable_neverValue_tail_bound
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) {M : ℝ}
    (hreward : ∀ S player, |reward S player| ≤ M)
    (roots : ℕ → ι → PMF Bool) (who : ι) (T : ℕ) :
    |quittingRootSequencePureTimeTerminalValue reward roots who none -
        fableNeverCollect reward roots who T| ≤
      M * (quittingOpponentSurvivalWeight roots who 0 T -
        ⨅ T', quittingOpponentSurvivalWeight roots who 0 T') := by
  have hM : 0 ≤ M :=
    le_trans (abs_nonneg _) (hreward (quittingSingletonTerminal who) who)
  have hbdd : BddBelow
      (Set.range (quittingOpponentSurvivalWeight roots who 0)) := by
    refine ⟨0, ?_⟩
    rintro y ⟨n, rfl⟩
    exact quittingOpponentSurvivalWeight_nonneg roots who 0 n
  have hinf := tendsto_atTop_ciInf
    (antitone_quittingOpponentSurvivalWeight roots who 0) hbdd
  have hledger := tendsto_quittingLiveLedgerAccum reward roots who
  have hlhs : Tendsto
      (fun fuel => |fableNeverCollect reward roots who fuel -
        fableNeverCollect reward roots who T|) atTop
      (nhds |quittingRootSequencePureTimeTerminalValue reward roots who none 0 -
        fableNeverCollect reward roots who T|) :=
    (hledger.sub_const (fableNeverCollect reward roots who T)).abs
  have hrhs : Tendsto
      (fun fuel => M * (quittingOpponentSurvivalWeight roots who 0 T -
        quittingOpponentSurvivalWeight roots who 0 fuel)) atTop
      (nhds (M * (quittingOpponentSurvivalWeight roots who 0 T -
        ⨅ T', quittingOpponentSurvivalWeight roots who 0 T'))) :=
    (tendsto_const_nhds.sub hinf).const_mul M
  refine le_of_tendsto_of_tendsto hlhs hrhs ?_
  refine eventually_atTop.mpr ⟨T, fun fuel hfuel => ?_⟩
  exact fable_abs_neverCollect_sub_le reward roots who hM
    (fun S => hreward S who) T fuel hfuel

/-! ## Target 4: the quit-value row estimate -/

/-- **The row estimate.**  Quitting at date `t` differs from collecting the
ledger before `t` and then quitting alone by at most twice the reward bound
times the opponents' deleted absorption mass at row `t`. -/
theorem fable_pureTimeValue_row_estimate
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) {M : ℝ}
    (hreward : ∀ S player, |reward S player| ≤ M)
    (roots : ℕ → ι → PMF Bool) (who : ι) (t : ℕ) :
    |quittingRootSequencePureTimeTerminalValue reward roots who (some t) -
        (fableNeverCollect reward roots who t +
          quittingOpponentSurvivalWeight roots who 0 t *
            reward (quittingSingletonTerminal who) who)| ≤
      2 * M * (quittingOpponentSurvivalWeight roots who 0 t -
        quittingOpponentSurvivalWeight roots who 0 (t + 1)) := by
  have hM : 0 ≤ M :=
    le_trans (abs_nonneg _) (hreward (quittingSingletonTerminal who) who)
  have hsolo : |reward (quittingSingletonTerminal who) who| ≤ M :=
    hreward (quittingSingletonTerminal who) who
  have hmix := abs_quittingFixedOpponentsQuitValue_sub_continueMass_mul_solo_le
    reward roots who t M hM (fun S => hreward S who)
  have hm0 := quittingFixedOpponentsContinueMass_nonneg roots who t
  have hm1 := quittingFixedOpponentsContinueMass_le_one roots who t
  have hW := quittingOpponentSurvivalWeight_nonneg roots who 0 t
  have hdrop : |quittingFixedOpponentsQuitValue reward roots who t -
      reward (quittingSingletonTerminal who) who| ≤
      2 * M * (1 - quittingFixedOpponentsContinueMass roots who t) := by
    have hsplit : quittingFixedOpponentsContinueMass roots who t *
        reward (quittingSingletonTerminal who) who -
          reward (quittingSingletonTerminal who) who =
        -((1 - quittingFixedOpponentsContinueMass roots who t) *
          reward (quittingSingletonTerminal who) who) := by ring
    have hsecond : |quittingFixedOpponentsContinueMass roots who t *
        reward (quittingSingletonTerminal who) who -
          reward (quittingSingletonTerminal who) who| ≤
        (1 - quittingFixedOpponentsContinueMass roots who t) * M := by
      rw [hsplit, abs_neg, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤
        1 - quittingFixedOpponentsContinueMass roots who t)]
      exact mul_le_mul_of_nonneg_left hsolo (by linarith)
    have htri := abs_sub_le (quittingFixedOpponentsQuitValue reward roots who t)
      (quittingFixedOpponentsContinueMass roots who t *
        reward (quittingSingletonTerminal who) who)
      (reward (quittingSingletonTerminal who) who)
    nlinarith [htri, hmix, hsecond]
  rw [quittingRootSequencePureTimeTerminalValue_some_eq,
    quittingOpponentSurvivalWeight_zero_succ]
  have hcollect : quittingLiveLedgerAccum reward roots who 0 t =
      fableNeverCollect reward roots who t := rfl
  rw [hcollect]
  have hexp : fableNeverCollect reward roots who t +
      quittingOpponentSurvivalWeight roots who 0 t *
        quittingFixedOpponentsQuitValue reward roots who t -
      (fableNeverCollect reward roots who t +
        quittingOpponentSurvivalWeight roots who 0 t *
          reward (quittingSingletonTerminal who) who) =
      quittingOpponentSurvivalWeight roots who 0 t *
        (quittingFixedOpponentsQuitValue reward roots who t -
          reward (quittingSingletonTerminal who) who) := by ring
  rw [hexp, abs_mul, abs_of_nonneg hW]
  nlinarith [mul_le_mul_of_nonneg_left hdrop hW]

/-! ## Profile-level corollaries -/

/-- Finite-time determination for the profile-level pure-time deviation
payoff: only the live rows at dates up to `t` matter. -/
theorem fable_pureTimeDeviationPayoff_congr_of_agree
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile profile' : (quittingGame reward).BehaviorProfile) (observer : ι)
    (t : ℕ)
    (h : ∀ s, s ≤ t → quittingProfileLiveRoot reward profile s =
      quittingProfileLiveRoot reward profile' s) :
    quittingPureTimeDeviationPayoff reward profile observer (some t) =
      quittingPureTimeDeviationPayoff reward profile' observer (some t) := by
  unfold quittingPureTimeDeviationPayoff
  rw [quittingTerminalPayoff_update_pureTimeBehaviorStrategy,
    quittingTerminalPayoff_update_pureTimeBehaviorStrategy]
  exact fable_pureTimeValue_congr_of_agree reward
    (quittingProfileLiveRoot reward profile)
    (quittingProfileLiveRoot reward profile') observer t h

/-- Continuity for the profile-level pure-time deviation payoff at a fixed
finite quit date. -/
theorem fable_pureTimeDeviationPayoff_tendsto
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profileSeq : ℕ → (quittingGame reward).BehaviorProfile)
    (profile : (quittingGame reward).BehaviorProfile) (observer : ι) (t : ℕ)
    (h : ∀ s, s ≤ t → ∀ (j : ι) (b : Bool),
      Tendsto
        (fun n => ((quittingProfileLiveRoot reward (profileSeq n) s j) b).toReal)
        atTop
        (nhds ((quittingProfileLiveRoot reward profile s j b).toReal))) :
    Tendsto
      (fun n => quittingPureTimeDeviationPayoff reward (profileSeq n) observer
        (some t))
      atTop
      (nhds (quittingPureTimeDeviationPayoff reward profile observer
        (some t))) := by
  unfold quittingPureTimeDeviationPayoff
  simp only [quittingTerminalPayoff_update_pureTimeBehaviorStrategy]
  exact fable_pureTimeValue_tendsto reward
    (fun n => quittingProfileLiveRoot reward (profileSeq n))
    (quittingProfileLiveRoot reward profile) observer t h

end GameTheory
