import UniformEquilibrium.Quitting.Paths.SparseWholePayoffFiniteStoppingProfile
import UniformEquilibrium.Quitting.Paths.LateFiniteStoppingLawCensor
import UniformEquilibrium.Quitting.Terminal.FiniteDeadlineStoppingLawRealization
import MathUE.Probability.FinitePMF

/-! # Exact finite-calendar realization and compactness of terminal payoffs

The construction preserves the entire prescribed payoff vector. It makes no claim
of response-cap preservation.
-/

noncomputable section

namespace GameTheory

open Set Filter GameTheory.Math.Probability
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def quittingFiniteDeadlineTimingPayoffMap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (deadline : ℕ)
    (x : MixedSimplex ι
      (fun _ => QuittingFiniteDeadlineTimingAction deadline)) : Payoff ι := by
  letI : ∀ player,
      Fintype ((quittingFiniteDeadlineTimingGame reward deadline).Strategy player) :=
    fun _ => by
      change Fintype (Option (Fin deadline))
      infer_instance
  exact fun observer =>
    (quittingFiniteDeadlineTimingGame reward deadline).mixedExtension.eu
      ((quittingFiniteDeadlineTimingGame reward deadline).profileFromMixedSimplex x)
      observer

omit [DecidableEq ι] in
/-- The prescribed-payoff image of a fixed finite timing calendar is compact. -/
theorem isCompact_range_finiteDeadlineTimingPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (deadline : ℕ) :
    IsCompact (Set.range (quittingFiniteDeadlineTimingPayoffMap reward deadline)) := by
  letI : ∀ player,
      Fintype ((quittingFiniteDeadlineTimingGame reward deadline).Strategy player) :=
    fun _ => by
      change Fintype (Option (Fin deadline))
      infer_instance
  apply isCompact_range
  apply continuous_pi
  intro observer
  exact (quittingFiniteDeadlineTimingGame reward deadline)
    |>.continuous_mixedExtension_eu_profileFromMixedSimplex observer

theorem quittingFiniteDeadlineTimingPayoffMap_stdSimplexEquiv
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (deadline : ℕ)
    (mixed : ∀ who,
      PMF ((quittingFiniteDeadlineTimingGame reward deadline).Strategy who)) :
    quittingFiniteDeadlineTimingPayoffMap reward deadline
        (fun who => Math.ProbabilityMassFunction.stdSimplexEquiv (mixed who)) =
      fun observer =>
        quittingTerminalPayoff reward
          (quittingFiniteDeadlineTimingProfile reward deadline mixed) observer := by
  letI : ∀ player,
      Fintype ((quittingFiniteDeadlineTimingGame reward deadline).Strategy player) :=
    fun _ => by
      change Fintype (Option (Fin deadline))
      infer_instance
  funext observer
  rw [quittingTerminalPayoff_finiteDeadlineTimingProfile_eq_mixedEU]
  have hprofile :
      (quittingFiniteDeadlineTimingGame reward deadline).profileFromMixedSimplex
          (fun who => Math.ProbabilityMassFunction.stdSimplexEquiv (mixed who)) =
        mixed := by
    funext who
    unfold KernelGame.profileFromMixedSimplex KernelGame.profileFromWeights
    apply PMF.ext
    intro action
    apply (ENNReal.toReal_eq_toReal_iff'
      (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
    rw [KernelGame.realToPmf_toReal]
    rfl
  unfold quittingFiniteDeadlineTimingPayoffMap
  exact congrArg
    (fun profile =>
      (quittingFiniteDeadlineTimingGame reward deadline).mixedExtension.eu
        profile observer)
    hprofile

/-- A late-finite censor, packaged with its finite support witness. -/
def quittingCensoredFiniteStoppingLaw
    (law : PMF (Option ℕ)) (horizon : ℕ) : FinDist (Option ℕ) :=
  ⟨_root_.Math.Probability.censorLateFiniteStoppingLaw law horizon,
    (Finset.finite_toSet (_root_.Math.Probability.stoppingLawFinitePrefix horizon)).subset
      (_root_.Math.Probability.censorLateFiniteStoppingLaw_support_subset law horizon)⟩

@[simp]
theorem quittingCensoredFiniteStoppingLaw_toPMF
    (law : PMF (Option ℕ)) (horizon : ℕ) :
    (quittingCensoredFiniteStoppingLaw law horizon).toPMF =
      _root_.Math.Probability.censorLateFiniteStoppingLaw law horizon :=
  rfl

omit [Fintype ι] [DecidableEq ι] in
/-- A finite law supported below a deadline is represented exactly by a
mixed action of the finite timing game. -/
theorem exists_finiteDeadlineTimingLaws_of_finiteCalendar
    (laws : ι → FinDist (Option ℕ)) (deadline : ℕ)
    (hsupport : ∀ who time, some time ∈ (laws who).support → time < deadline) :
    ∃ mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline),
      ∀ who, (quittingFiniteDeadlineTimingLaw (mixed who)).toPMF =
        (laws who).toPMF := by
  classical
  have hzero (who : ι) (time : ℕ) (htime : deadline ≤ time) :
      (laws who).toPMF (some time) = 0 := by
    by_contra hne
    have hmem : some time ∈ (laws who).support := by
      change (laws who).toPMF (some time) ≠ 0
      exact hne
    exact (not_lt_of_ge htime) (hsupport who time hmem)
  have hexists (who : ι) : ∃ law : PMF (Option (Fin deadline)),
      law.map (_root_.Math.Probability.finiteStoppingTimeDecode deadline) =
        (laws who).toPMF := by
    obtain ⟨law, hlaw, _⟩ :=
      _root_.Math.Probability.exists_finiteStoppingTimePMF_map_eq
      (laws who).toPMF deadline (hzero who)
    exact ⟨law, hlaw⟩
  choose mixed hmixed using hexists
  refine ⟨mixed, fun who => ?_⟩
  rw [quittingFiniteDeadlineTimingLaw,
    _root_.Math.Probability.CompactStoppingLaw.toPMF_ofPMF]
  have hmaps : (mixed who).map quittingFiniteDeadlineTimingActionTime =
      (mixed who).map
        (_root_.Math.Probability.finiteStoppingTimeDecode deadline) := by
    congr 1
    funext action
    cases action <;> rfl
  rw [hmaps, hmixed who]

def quittingActualTerminalPayoffSet
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Set (Payoff ι) :=
  Set.range fun profile : (quittingGame reward).BehaviorProfile =>
    fun observer => quittingTerminalPayoff reward profile observer

/-- Every actual behavioral payoff is approximated on the one fixed calendar
of size `n(n+1)`. -/
theorem quittingTerminalPayoff_mem_closure_finiteCalendarPayoff
    [Nonempty ι] (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) :
    (fun observer => quittingTerminalPayoff reward profile observer) ∈
      closure (Set.range (quittingFiniteDeadlineTimingPayoffMap reward
        (Fintype.card ι * (Fintype.card ι + 1)))) := by
  rw [Metric.mem_closure_iff]
  intro error herror
  let laws := quittingBehaviorStoppingLaws reward profile
  let bound := quittingRewardBound reward + 1
  have hbound : 0 < bound := by
    have := quittingRewardBound_nonneg reward
    dsimp [bound]
    linarith
  have hreward : ∀ terminal player, |reward terminal player| ≤ bound := by
    intro terminal player
    exact (abs_reward_le_quittingRewardBound reward terminal player).trans (by
      dsimp [bound]
      linarith)
  obtain ⟨horizon, hhorizon⟩ :=
    exists_horizon_sum_stoppingLawLateFiniteMass_lt laws
      (div_pos herror (mul_pos (show (0 : ℝ) < 2 by norm_num) hbound))
  let finite : ι → FinDist (Option ℕ) := fun who =>
    quittingCensoredFiniteStoppingLaw (laws who) horizon
  let compressed := quittingFiniteCalendarPayoffLaws reward finite
  have hsupport : ∀ who time, some time ∈ (compressed who).support →
      time < Fintype.card ι * (Fintype.card ι + 1) := by
    intro who time htime
    exact quittingFiniteCalendarPayoffLaws_finiteDate_lt reward finite who htime
  obtain ⟨mixed, hmixed⟩ :=
    exists_finiteDeadlineTimingLaws_of_finiteCalendar compressed _ hsupport
  let point : MixedSimplex ι
      (fun _ => QuittingFiniteDeadlineTimingAction
        (Fintype.card ι * (Fintype.card ι + 1))) :=
    fun who => Math.ProbabilityMassFunction.stdSimplexEquiv (mixed who)
  refine ⟨quittingFiniteDeadlineTimingPayoffMap reward _ point,
    Set.mem_range_self point, ?_⟩
  rw [dist_pi_lt_iff herror]
  intro observer
  rw [Real.dist_eq]
  have hmap := quittingFiniteDeadlineTimingPayoffMap_stdSimplexEquiv
    reward _ mixed
  have hprofile := finiteDeadlineTimingProfile_eq_stoppingLawProfile_of_laws
    reward _ mixed (fun who => (compressed who).toPMF) hmixed
  have hcompressed := quittingFiniteCalendarPayoffLaws_wholePayoff_eq
    reward finite observer
  have hcensor := abs_expectedPayoff_censorLateFiniteStoppingLaws_sub_le
    reward laws horizon observer hreward
  have hscale : 2 * bound *
      (∑ player, stoppingLawLateFiniteMass (laws player) horizon) < error := by
    calc
      _ < 2 * bound * (error / (2 * bound)) := by gcongr
      _ = error := by field_simp
  rw [hmap]
  rw [hprofile]
  change |quittingTerminalPayoff reward profile observer -
      quittingTerminalPayoff reward
        (quittingStoppingLawProfile reward (fun who =>
          (quittingFiniteCalendarPayoffLaws reward finite who).toPMF)) observer| < error
  rw [hcompressed]
  rw [quittingTerminalPayoff_stoppingLawProfile_eq_expectedPayoff]
  rw [show (fun who => (finite who).toPMF) =
      censorLateFiniteStoppingLaws laws horizon by rfl]
  rw [← quittingStoppingLawExpectedPayoff_behaviorStoppingLaws_eq_terminalPayoff
    reward profile observer]
  change |quittingStoppingLawExpectedPayoff reward laws observer -
      quittingStoppingLawExpectedPayoff reward
        (censorLateFiniteStoppingLaws laws horizon) observer| < error
  rw [abs_sub_comm]
  exact hcensor.trans_lt hscale

/-- The closure of actual behavioral payoffs lies in the compact payoff image
of the fixed `n(n+1)`-date timing game. -/
theorem closure_quittingActualTerminalPayoffSet_subset_finiteCalendarPayoff
    [Nonempty ι] (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    closure (quittingActualTerminalPayoffSet reward) ⊆
      Set.range (quittingFiniteDeadlineTimingPayoffMap reward
        (Fintype.card ι * (Fintype.card ι + 1))) := by
  have hclosed := (isCompact_range_finiteDeadlineTimingPayoff reward
    (Fintype.card ι * (Fintype.card ι + 1))).isClosed
  have hmono : closure (quittingActualTerminalPayoffSet reward) ⊆
      closure (Set.range (quittingFiniteDeadlineTimingPayoffMap reward
        (Fintype.card ι * (Fintype.card ι + 1)))) := by
    apply closure_minimal
    rintro value ⟨profile, rfl⟩
    exact quittingTerminalPayoff_mem_closure_finiteCalendarPayoff reward profile
    exact isClosed_closure
  simpa only [hclosed.closure_eq] using hmono

/-- The full actual prescribed-payoff set is exactly the image of the fixed
finite timing calendar. -/
theorem quittingActualTerminalPayoffSet_eq_finiteCalendarPayoff
    [Nonempty ι] (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    quittingActualTerminalPayoffSet reward =
      Set.range (quittingFiniteDeadlineTimingPayoffMap reward
        (Fintype.card ι * (Fintype.card ι + 1))) := by
  apply Set.Subset.antisymm
  · intro value hvalue
    exact closure_quittingActualTerminalPayoffSet_subset_finiteCalendarPayoff
      reward (subset_closure hvalue)
  · rintro value ⟨point, rfl⟩
    let deadline := Fintype.card ι * (Fintype.card ι + 1)
    let mixed : ι → PMF (Option (Fin deadline)) := fun who =>
      Math.ProbabilityMassFunction.stdSimplexEquiv.symm (point who)
    refine ⟨quittingFiniteDeadlineTimingProfile reward deadline mixed, ?_⟩
    have hmap := quittingFiniteDeadlineTimingPayoffMap_stdSimplexEquiv
      reward deadline mixed
    have hrecover :
        (fun who => Math.ProbabilityMassFunction.stdSimplexEquiv (mixed who)) =
          point := by
      funext who
      exact Math.ProbabilityMassFunction.stdSimplexEquiv.apply_symm_apply
        (point who)
    rw [hrecover] at hmap
    simpa only [deadline] using hmap.symm

/-- The actual prescribed-payoff set is compact. -/
theorem isCompact_quittingActualTerminalPayoffSet
    [Nonempty ι] (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    IsCompact (quittingActualTerminalPayoffSet reward) := by
  rw [quittingActualTerminalPayoffSet_eq_finiteCalendarPayoff]
  exact isCompact_range_finiteDeadlineTimingPayoff reward _

/-- Every payoff in the closure of actual behavioral payoffs has an exact
finite-calendar realization with at most `n+1` atoms in each marginal. -/
theorem exists_sparse_finiteCalendarLaws_of_mem_closure_actualPayoff
    [Nonempty ι] (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {value : Payoff ι} (hvalue : value ∈
      closure (quittingActualTerminalPayoffSet reward)) :
    ∃ laws : ι → FinDist (Option ℕ),
      (∀ observer, quittingTerminalPayoff reward
          (quittingStoppingLawProfile reward (fun who => (laws who).toPMF))
          observer = value observer) ∧
      (∀ who time, some time ∈ (laws who).support →
        time < Fintype.card ι * (Fintype.card ι + 1)) ∧
      (∀ who, (laws who).supportFinset.card ≤ Fintype.card ι + 1) := by
  let deadline := Fintype.card ι * (Fintype.card ι + 1)
  obtain ⟨point, hpoint⟩ :=
    closure_quittingActualTerminalPayoffSet_subset_finiteCalendarPayoff reward hvalue
  let mixed : ι → PMF (Option (Fin deadline)) := fun who =>
    Math.ProbabilityMassFunction.stdSimplexEquiv.symm (point who)
  let decoded : ι → FinDist (Option ℕ) := fun who =>
    (Math.Probability.finDistOfPMF (mixed who)).map
      (_root_.Math.Probability.finiteStoppingTimeDecode deadline)
  let laws := quittingFiniteCalendarPayoffLaws reward decoded
  refine ⟨laws, ?_, ?_, ?_⟩
  · intro observer
    rw [quittingFiniteCalendarPayoffLaws_wholePayoff_eq]
    have hmixed : ∀ who,
        (quittingFiniteDeadlineTimingLaw (mixed who)).toPMF =
          (decoded who).toPMF := by
      intro who
      simp only [decoded, quittingFiniteDeadlineTimingLaw,
        _root_.Math.Probability.CompactStoppingLaw.toPMF_ofPMF,
        GameTheory.Math.Probability.FinDist.toPMF_map,
        Math.Probability.toPMF_finDistOfPMF]
      change (mixed who).map quittingFiniteDeadlineTimingActionTime =
        (mixed who).map
          (_root_.Math.Probability.finiteStoppingTimeDecode deadline)
      congr 1
      funext action
      cases action <;> rfl
    rw [← finiteDeadlineTimingProfile_eq_stoppingLawProfile_of_laws
      reward deadline mixed (fun who => (decoded who).toPMF) hmixed]
    have hmap := quittingFiniteDeadlineTimingPayoffMap_stdSimplexEquiv
      reward deadline mixed
    have hrecover :
        (fun who => Math.ProbabilityMassFunction.stdSimplexEquiv (mixed who)) =
          point := by
      funext who
      exact Math.ProbabilityMassFunction.stdSimplexEquiv.apply_symm_apply
        (point who)
    calc
      quittingTerminalPayoff reward
          (quittingFiniteDeadlineTimingProfile reward deadline mixed) observer =
          quittingFiniteDeadlineTimingPayoffMap reward deadline
            (fun who => Math.ProbabilityMassFunction.stdSimplexEquiv
              (mixed who)) observer := congrFun hmap.symm observer
      _ = quittingFiniteDeadlineTimingPayoffMap reward deadline point observer := by
        rw [hrecover]
      _ = value observer := congrFun hpoint observer
  · intro who time htime
    exact quittingFiniteCalendarPayoffLaws_finiteDate_lt reward decoded who htime
  · intro who
    exact card_support_quittingFiniteCalendarPayoffLaws_le reward decoded who

end GameTheory
