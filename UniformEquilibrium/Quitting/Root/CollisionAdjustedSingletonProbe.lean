import UniformEquilibrium.Quitting.Root.SingletonRootEndpoints
import UniformEquilibrium.Quitting.Root.BoundedEndpoint

/-! # Literal collision-adjusted solo roots on singleton faces

The correction freezes upper coordinates. Every sufficiently small positive
rate gives the same explicit source formula, the canonical independent solo
root, and its exact successor. No equilibrium, box or favorable-root witness
is accepted as construction data.
-/

noncomputable section

namespace GameTheory

open Filter Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The nonowner's literal collision surplus over the owner's solo exit. -/
def quittingSingletonProbeCollision
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner other : ι) : ℝ :=
  quittingSingletonCollisionReward reward owner other - quittingSoloReward reward owner other

/-- Positive collision correction, frozen at the upper coordinate face. -/
def quittingSingletonProbeCorrection
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (upper : ℝ) (point : Payoff ι) (owner : ι) : Payoff ι :=
  fun other => if other = owner then 0 else
    if point other < upper then max (quittingSingletonProbeCollision reward owner other) 0
    else 0

/-- The literal source, defined for every real rate. -/
def quittingSingletonProbeSource
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (upper : ℝ) (point : Payoff ι) (owner : ι) (rate : ℝ) : Payoff ι :=
  fun other => point other + rate / (1 - rate) *
    quittingSingletonProbeCorrection reward upper point owner other

/-- The canonical independent solo root; rate bounds affect only proof arguments. -/
def quittingSingletonProbeRoot (owner : ι) (rate : ℝ)
    (hrate0 : 0 ≤ rate) (hrate1 : rate ≤ 1) : ι → PMF Bool :=
  quittingSoloStationaryRoot owner (quittingHazardCoin rate hrate0 hrate1)

/-- The actual product expectation at the literal source and solo root. -/
def quittingSingletonProbeSuccessor
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (upper : ℝ) (point : Payoff ι) (owner : ι) (rate : ℝ)
    (hrate0 : 0 ≤ rate) (hrate1 : rate ≤ 1) : Payoff ι :=
  quittingRootSuccessorPayoff reward
    (quittingSingletonProbeSource reward upper point owner rate)
    (quittingSingletonProbeRoot owner rate hrate0 hrate1)

omit [Fintype ι] in
theorem quittingSingletonProbeCorrection_nonneg
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (upper : ℝ) (point : Payoff ι) (owner other : ι) :
    0 ≤ quittingSingletonProbeCorrection reward upper point owner other := by
  unfold quittingSingletonProbeCorrection
  split
  · exact le_rfl
  · split
    · exact le_max_right _ _
    · exact le_rfl

omit [Fintype ι] in
@[simp] theorem quittingSingletonProbeSource_owner
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (upper : ℝ) (point : Payoff ι) (owner : ι) (rate : ℝ) :
    quittingSingletonProbeSource reward upper point owner rate owner = point owner := by
  simp [quittingSingletonProbeSource, quittingSingletonProbeCorrection]

omit [Fintype ι] in
theorem quittingSingletonProbeSource_eq_of_upper
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {upper : ℝ} {point : Payoff ι} (owner other : ι) (rate : ℝ)
    (hupper : point other = upper) :
    quittingSingletonProbeSource reward upper point owner rate other = point other := by
  simp [quittingSingletonProbeSource, quittingSingletonProbeCorrection, hupper]

theorem quittingSingletonProbeQuitPayoff_owner
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (upper : ℝ) (point : Payoff ι) (owner : ι) (rate : ℝ)
    (hrate0 : 0 ≤ rate) (hrate1 : rate ≤ 1) :
    quittingRootQuitPayoff reward (quittingSingletonProbeSource reward upper point owner rate)
      (quittingSingletonProbeRoot owner rate hrate0 hrate1) owner =
      quittingSoloReward reward owner owner := by
  exact quittingRootQuitPayoff_soloStationaryRoot_owner reward owner _ _

theorem quittingSingletonProbeContinuePayoff_owner
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (upper : ℝ) (point : Payoff ι) (owner : ι) (rate : ℝ)
    (hrate0 : 0 ≤ rate) (hrate1 : rate ≤ 1) :
    quittingRootContinuePayoff reward
      (quittingSingletonProbeSource reward upper point owner rate)
      (quittingSingletonProbeRoot owner rate hrate0 hrate1) owner = point owner := by
  rw [quittingSingletonProbeRoot, quittingRootContinuePayoff_soloStationaryRoot_owner,
    quittingSingletonProbeSource_owner]

theorem quittingSingletonProbeQuitPayoff_other
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (upper : ℝ) (point : Payoff ι) {owner other : ι} (hne : other ≠ owner)
    (rate : ℝ) (hrate0 : 0 ≤ rate) (hrate1 : rate ≤ 1) :
    quittingRootQuitPayoff reward (quittingSingletonProbeSource reward upper point owner rate)
      (quittingSingletonProbeRoot owner rate hrate0 hrate1) other =
      (1 - rate) * quittingSoloReward reward other other +
        rate * quittingSingletonCollisionReward reward owner other := by
  simp only [quittingSingletonProbeRoot,
    quittingRootQuitPayoff_soloStationaryRoot_other reward hne,
    quittingHazardCoin_false_toReal, quittingHazardCoin_true_toReal]

theorem quittingSingletonProbe_owner_endpoints
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (upper : ℝ) (point : Payoff ι) (owner : ι)
    (howner : point owner = quittingSoloReward reward owner owner)
    (rate : ℝ) (hrate0 : 0 ≤ rate) (hrate1 : rate ≤ 1) :
    quittingRootQuitPayoff reward (quittingSingletonProbeSource reward upper point owner rate)
        (quittingSingletonProbeRoot owner rate hrate0 hrate1) owner =
        quittingSoloReward reward owner owner ∧
      quittingRootContinuePayoff reward
        (quittingSingletonProbeSource reward upper point owner rate)
        (quittingSingletonProbeRoot owner rate hrate0 hrate1) owner =
        quittingSoloReward reward owner owner := by
  refine ⟨quittingSingletonProbeQuitPayoff_owner reward upper point owner rate hrate0 hrate1,
    ?_⟩
  rw [quittingSingletonProbeContinuePayoff_owner, howner]

theorem quittingSingletonProbeContinuePayoff_other
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (upper : ℝ) (point : Payoff ι) {owner other : ι} (hne : other ≠ owner)
    (rate : ℝ) (hrate0 : 0 ≤ rate) (hrate1 : rate ≤ 1) :
    quittingRootContinuePayoff reward
      (quittingSingletonProbeSource reward upper point owner rate)
      (quittingSingletonProbeRoot owner rate hrate0 hrate1) other =
      rate * quittingSoloReward reward owner other + (1 - rate) *
        quittingSingletonProbeSource reward upper point owner rate other := by
  simp only [quittingSingletonProbeRoot,
    quittingRootContinuePayoff_soloStationaryRoot_other reward hne,
    quittingHazardCoin_false_toReal, quittingHazardCoin_true_toReal]

theorem quittingSingletonProbeSuccessor_eq_mix
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (upper : ℝ) (point : Payoff ι) (owner : ι) (rate : ℝ)
    (hrate0 : 0 ≤ rate) (hrate1 : rate ≤ 1) (other : ι) :
    quittingSingletonProbeSuccessor reward upper point owner rate hrate0 hrate1 other =
      (1 - rate) * quittingSingletonProbeSource reward upper point owner rate other +
        rate * quittingSoloReward reward owner other := by
  simp only [quittingSingletonProbeSuccessor, quittingSingletonProbeRoot,
    quittingRootSuccessorPayoff_solo, quittingHazardCoin_true_toReal,
    quittingHazardCoin_false_toReal]
  ring

theorem quittingSingletonProbeSuccessor_eq_affine
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (upper : ℝ) (point : Payoff ι) (owner : ι) (rate : ℝ)
    (hrate0 : 0 ≤ rate) (hrate1 : rate ≤ 1) (hne : rate ≠ 1) (other : ι) :
    quittingSingletonProbeSuccessor reward upper point owner rate hrate0 hrate1 other =
      point other + rate * (quittingSingletonProbeCorrection reward upper point owner other +
        quittingSoloReward reward owner other - point other) := by
  rw [quittingSingletonProbeSuccessor_eq_mix, quittingSingletonProbeSource]
  have hdenom : 1 - rate ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  field_simp [hdenom]
  ring

theorem quittingSingletonProbeContinue_sub_quit
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (upper : ℝ) (point : Payoff ι) {owner other : ι} (hne : other ≠ owner)
    (rate : ℝ) (hrate0 : 0 ≤ rate) (hrate1 : rate ≤ 1) (hrate : rate ≠ 1) :
    quittingRootContinuePayoff reward
        (quittingSingletonProbeSource reward upper point owner rate)
        (quittingSingletonProbeRoot owner rate hrate0 hrate1) other -
      quittingRootQuitPayoff reward (quittingSingletonProbeSource reward upper point owner rate)
        (quittingSingletonProbeRoot owner rate hrate0 hrate1) other =
      (1 - rate) * (point other - quittingSoloReward reward other other) +
        rate * (quittingSingletonProbeCorrection reward upper point owner other -
          quittingSingletonProbeCollision reward owner other) := by
  rw [quittingSingletonProbeContinuePayoff_other reward upper point hne,
    quittingSingletonProbeQuitPayoff_other reward upper point hne]
  unfold quittingSingletonProbeSource quittingSingletonProbeCollision
  have hdenom : 1 - rate ≠ 0 := sub_ne_zero.mpr (Ne.symm hrate)
  field_simp [hdenom]
  ring

@[simp] theorem quittingSingletonProbeRoot_absorption
    (owner : ι) (rate : ℝ) (hrate0 : 0 ≤ rate) (hrate1 : rate ≤ 1) :
    quittingRootAbsorptionMass (quittingSingletonProbeRoot owner rate hrate0 hrate1) = rate := by
  simp [quittingSingletonProbeRoot]

theorem quittingSingletonProbeContinue_sub_quit_upper
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {upper : ℝ} {point : Payoff ι} {owner other : ι} (hne : other ≠ owner)
    (hupper : point other = upper) (rate : ℝ)
    (hrate0 : 0 ≤ rate) (hrate1 : rate ≤ 1) (hrate : rate ≠ 1) :
    quittingRootContinuePayoff reward
        (quittingSingletonProbeSource reward upper point owner rate)
        (quittingSingletonProbeRoot owner rate hrate0 hrate1) other -
      quittingRootQuitPayoff reward (quittingSingletonProbeSource reward upper point owner rate)
        (quittingSingletonProbeRoot owner rate hrate0 hrate1) other =
      (1 - rate) * (upper - quittingSoloReward reward other other) -
        rate * quittingSingletonProbeCollision reward owner other := by
  rw [quittingSingletonProbeContinue_sub_quit reward upper point hne rate hrate0 hrate1 hrate]
  simp [quittingSingletonProbeCorrection, hne, hupper, sub_eq_add_neg]

/-- Arbitrary bounded reward data produce one interval of rates, each giving the
literal boxed source, an exact Nash solo root, and its boxed exact successor. -/
theorem exists_small_rates_quittingSingletonProbe
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {M upper : ℝ} (hreward : ∀ terminal who, |reward terminal who| ≤ M)
    (hupper : M < upper) (point : Payoff ι) (owner : ι)
    (hpoint : ∀ who, quittingSoloReward reward who who ≤ point who ∧ point who ≤ upper)
    (howner : point owner = quittingSoloReward reward owner owner) :
    ∃ ε : ℝ, ∃ hε1 : ε < 1, 0 < ε ∧
      ∀ rate, (hrate0 : 0 < rate) → (hsmall : rate < ε) →
      (∀ who, |quittingSingletonProbeSource reward upper point owner rate who| ≤ upper) ∧
      IsεQuittingRootNash reward (quittingSingletonProbeSource reward upper point owner rate) 0
        (quittingSingletonProbeRoot owner rate hrate0.le (lt_trans hsmall hε1).le) ∧
      (∀ who, |quittingSingletonProbeSuccessor reward upper point owner rate
        hrate0.le (lt_trans hsmall hε1).le who| ≤ upper) ∧
      quittingRootAbsorptionMass
        (quittingSingletonProbeRoot owner rate hrate0.le (lt_trans hsmall hε1).le) = rate := by
  let correction := quittingSingletonProbeCorrection reward upper point owner
  let source := quittingSingletonProbeSource reward upper point owner
  let gap : ι → ℝ → ℝ := fun who rate =>
    (1 - rate) * (point who - quittingSoloReward reward who who) +
      rate * (correction who - quittingSingletonProbeCollision reward owner who)
  have hsourceSmall : ∀ᶠ rate : ℝ in 𝓝 0, ∀ who,
      source rate who ≤ upper ∧ (point who = upper → 0 < gap who rate) := by
    apply Filter.eventually_all.mpr
    intro who
    by_cases hinterior : point who < upper
    · have hcont : ContinuousAt (fun rate => source rate who) 0 := by
        unfold source quittingSingletonProbeSource
        exact continuousAt_const.add ((continuousAt_id.div
          (continuousAt_const.sub continuousAt_id) (by norm_num)).mul continuousAt_const)
      have hstrict : source 0 who < upper := by simpa [source,
        quittingSingletonProbeSource] using hinterior
      exact (hcont.eventually (gt_mem_nhds hstrict)).mono fun rate hrate =>
        ⟨hrate.le, fun heq => (hinterior.ne heq).elim⟩
    · have heq : point who = upper := le_antisymm (hpoint who).2 (le_of_not_gt hinterior)
      have hsolo : quittingSoloReward reward who who ≤ M :=
        (le_abs_self _).trans (hreward (quittingSingletonTerminal who) who)
      have hgap : 0 < gap who 0 := by dsimp [gap]; linarith
      have hcont : Continuous (gap who) := by unfold gap; fun_prop
      exact (hcont.continuousAt.eventually (lt_mem_nhds hgap)).mono fun rate hrate =>
        ⟨by
          dsimp only [source]
          rw [quittingSingletonProbeSource_eq_of_upper reward owner who rate heq]
          exact heq.le, fun _ => hrate⟩
  obtain ⟨radius, hradius, hball⟩ := Metric.eventually_nhds_iff.mp hsourceSmall
  have hε1 : min radius (1 / 2) < 1 :=
    lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  refine ⟨min radius (1 / 2), hε1, lt_min hradius (by norm_num), ?_⟩
  intro rate hrate0 hsmall
  let hrate1 : rate ≤ 1 := (lt_trans hsmall hε1).le
  have hrateLt : rate < 1 := lt_of_lt_of_le hsmall
    ((min_le_right radius (1 / 2)).trans (by norm_num))
  have hdenom : 0 < 1 - rate := sub_pos.mpr hrateLt
  have hnear := hball (show dist rate 0 < radius by
    simpa [Real.dist_eq, abs_of_pos hrate0] using
      lt_of_lt_of_le hsmall (min_le_left radius (1 / 2)))
  have hsourceBox : ∀ who, |source rate who| ≤ upper := by
    intro who
    apply abs_le.mpr
    constructor
    · have hsolo := neg_le_of_abs_le (hreward (quittingSingletonTerminal who) who)
      have hcorrection := quittingSingletonProbeCorrection_nonneg reward upper point owner who
      have hlift := mul_nonneg (div_nonneg hrate0.le hdenom.le) hcorrection
      change -upper ≤ point who + rate / (1 - rate) * correction who
      have hfloor := (hpoint who).1
      change quittingSoloReward reward who who ≤ point who at hfloor
      change -M ≤ quittingSoloReward reward who who at hsolo
      linarith
    · exact (hnear who).1
  have hnash : IsεQuittingRootNash reward (source rate) 0
      (quittingSingletonProbeRoot owner rate hrate0.le hrate1) := by
    apply (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash reward _ _).mp
    intro who
    by_cases heq : who = owner
    · subst who
      have hdifference : quittingRootEndpointDifference reward (source rate)
          (quittingSingletonProbeRoot owner rate hrate0.le hrate1) owner = 0 := by
        rw [quittingRootEndpointDifference,
          quittingSingletonProbeQuitPayoff_owner,
          quittingSingletonProbeContinuePayoff_owner, howner, sub_self]
      simp [hdifference]
    · have hgap : 0 ≤ gap who rate := by
        by_cases hinterior : point who < upper
        · have hcorrection : correction who =
              max (quittingSingletonProbeCollision reward owner who) 0 := by
            simp [correction, quittingSingletonProbeCorrection, heq, hinterior]
          have hfirst := mul_nonneg hdenom.le
            (sub_nonneg.mpr (hpoint who).1)
          have hsecond := mul_nonneg hrate0.le (sub_nonneg.mpr
            (le_max_left (quittingSingletonProbeCollision reward owner who) 0))
          dsimp only [gap]
          rw [hcorrection]
          exact add_nonneg hfirst hsecond
        · exact ((hnear who).2
            (le_antisymm (hpoint who).2 (le_of_not_gt hinterior))).le
      have hdifference : quittingRootEndpointDifference reward (source rate)
          (quittingSingletonProbeRoot owner rate hrate0.le hrate1) who ≤ 0 := by
        have hidentity := quittingSingletonProbeContinue_sub_quit reward upper point heq
          rate hrate0.le hrate1 (ne_of_lt hrateLt)
        change 0 ≤ gap who rate at hgap
        change quittingRootQuitPayoff reward (source rate)
          (quittingSingletonProbeRoot owner rate hrate0.le hrate1) who -
            quittingRootContinuePayoff reward (source rate)
              (quittingSingletonProbeRoot owner rate hrate0.le hrate1) who ≤ 0
        change _ = gap who rate at hidentity
        linarith
      constructor
      · exact mul_nonpos_of_nonneg_of_nonpos ENNReal.toReal_nonneg hdifference
      · simp [quittingSingletonProbeRoot, quittingSoloStationaryRoot, heq]
  refine ⟨hsourceBox, hnash, ?_, quittingSingletonProbeRoot_absorption _ _ _ _⟩
  intro who
  exact abs_quittingRootSuccessorPayoff_le_bound reward (source rate)
    (quittingSingletonProbeRoot owner rate hrate0.le hrate1) who
    (fun terminal receiver => (hreward terminal receiver).trans hupper.le) hsourceBox

end GameTheory
