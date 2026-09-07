import MathUE.FiniteCappedSimplexPairReduction
import UniformEquilibrium.Quitting.Paths.FiniteCalendarRawPredicates

/-!
# Ordered-pair form of quitting group exclusion

The capped-simplex witness is reduced profile by profile to a distinct
ordered pair.  The complement `lambda` of the cap is uniform across all
profiles (or all raw finite-calendar points); the selected pair need not be.
-/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Actual terminal group exclusion expressed by profile-dependent ordered
pairs at one fixed mixture parameter. -/
def HasQuittingActualOrderedPairGroupExclusion
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (lambda : ℝ) : Prop :=
  ∀ profile : (quittingGame reward).BehaviorProfile,
    ∃ first second : ι, first ≠ second ∧
      (1 - lambda) *
          (quittingTerminalPayoff reward profile first -
            reward (quittingSingletonTerminal first) first) +
        lambda *
          (quittingTerminalPayoff reward profile second -
            reward (quittingSingletonTerminal second) second) ≤ 0

/-- Raw finite-calendar group exclusion expressed by point-dependent ordered
pairs at one fixed mixture parameter. -/
def HasQuittingFiniteCalendarRawOrderedPairGroupExclusion
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (lambda : ℝ) : Prop :=
  ∀ x : MixedSimplex ι (fun _ => QuittingFiniteDeadlineTimingAction
      (Fintype.card ι * (Fintype.card ι + 1))),
    ∃ first second : ι, first ≠ second ∧
      (1 - lambda) *
          (quittingFiniteCalendarRawPayoff reward _ x first -
            reward (quittingSingletonTerminal first) first) +
        lambda *
          (quittingFiniteCalendarRawPayoff reward _ x second -
            reward (quittingSingletonTerminal second) second) ≤ 0

/-- For a cap at least one half, actual capped-simplex exclusion is exactly
the ordered-pair condition at its complementary parameter. -/
theorem hasQuittingActualNonconcentratedGroupExclusion_iff_orderedPair
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (beta : ℝ)
    (hhalf : (1 : ℝ) / 2 ≤ beta) (hlt : beta < 1) :
    HasQuittingActualNonconcentratedGroupExclusion reward beta ↔
      HasQuittingActualOrderedPairGroupExclusion reward (1 - beta) := by
  unfold HasQuittingActualNonconcentratedGroupExclusion
    HasQuittingActualOrderedPairGroupExclusion
  apply forall_congr'
  intro profile
  let surplus : ι → ℝ := fun who =>
    quittingTerminalPayoff reward profile who -
      reward (quittingSingletonTerminal who) who
  constructor
  · intro hweight
    obtain ⟨first, second, hne, hpair⟩ :=
      (Math.exists_cappedWeight_weightedSum_nonpositive_iff_exists_pair
        surplus beta hhalf hlt).mp hweight
    refine ⟨first, second, hne, ?_⟩
    dsimp only [surplus] at hpair ⊢
    convert hpair using 1
    all_goals ring
  · rintro ⟨first, second, hne, hpair⟩
    apply (Math.exists_cappedWeight_weightedSum_nonpositive_iff_exists_pair
      surplus beta hhalf hlt).mpr
    refine ⟨first, second, hne, ?_⟩
    dsimp only [surplus] at hpair ⊢
    convert hpair using 1
    all_goals ring

/-- The full actual GE hypothesis has exactly one uniform parameter in
`(0, 1/2]`, while its ordered pair may depend on the profile. -/
theorem exists_actualNonconcentratedGroupExclusion_iff_exists_orderedPair
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    (∃ beta < 1,
      HasQuittingActualNonconcentratedGroupExclusion reward beta) ↔
      ∃ lambda, 0 < lambda ∧ lambda ≤ (1 : ℝ) / 2 ∧
        HasQuittingActualOrderedPairGroupExclusion reward lambda := by
  constructor
  · rintro ⟨beta, hbeta, hexclusion⟩
    let enlarged := max beta ((1 : ℝ) / 2)
    have hhalf : (1 : ℝ) / 2 ≤ enlarged := le_max_right _ _
    have hlt : enlarged < 1 := max_lt hbeta (by norm_num)
    have henlarged :
        HasQuittingActualNonconcentratedGroupExclusion reward enlarged := by
      intro profile
      obtain ⟨weight, hnonnegative, hsum, hcapped, hweighted⟩ :=
        hexclusion profile
      exact ⟨weight, hnonnegative, hsum,
        fun who => (hcapped who).trans (le_max_left _ _), hweighted⟩
    refine ⟨1 - enlarged, by linarith, by linarith, ?_⟩
    exact
      (hasQuittingActualNonconcentratedGroupExclusion_iff_orderedPair
        reward enlarged hhalf hlt).mp henlarged
  · rintro ⟨lambda, hlambda, hhalf, hpairs⟩
    have hcapHalf : (1 : ℝ) / 2 ≤ 1 - lambda := by
      linarith
    have hcapLt : 1 - lambda < 1 := by
      linarith
    refine ⟨1 - lambda, hcapLt, ?_⟩
    apply
      (hasQuittingActualNonconcentratedGroupExclusion_iff_orderedPair
        reward (1 - lambda) hcapHalf hcapLt).mpr
    have hcomplement : 1 - (1 - lambda) = lambda := by
      ring
    simpa only [hcomplement] using hpairs

variable [Nonempty ι]

/-- The raw ordered-pair condition and the actual-profile condition are
equivalent for the same uniform parameter. -/
theorem hasQuittingFiniteCalendarRawOrderedPairGroupExclusion_iff_actual
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (lambda : ℝ) :
    HasQuittingFiniteCalendarRawOrderedPairGroupExclusion reward lambda ↔
      HasQuittingActualOrderedPairGroupExclusion reward lambda := by
  unfold HasQuittingFiniteCalendarRawOrderedPairGroupExclusion
    HasQuittingActualOrderedPairGroupExclusion
  let predicate : Payoff ι → Prop := fun value =>
    ∃ first second : ι, first ≠ second ∧
      (1 - lambda) *
          (value first - reward (quittingSingletonTerminal first) first) +
        lambda *
          (value second - reward (quittingSingletonTerminal second) second) ≤ 0
  exact forall_finiteCalendarRawPayoff_iff_forall_actualTerminalPayoff
    reward predicate

/-- The raw finite-calendar GE hypothesis has the same uniform ordered-pair
parameter form as the actual-profile hypothesis. -/
theorem exists_finiteCalendarRawNonconcentratedGroupExclusion_iff_orderedPair
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    (∃ beta < 1,
      HasQuittingFiniteCalendarRawNonconcentratedGroupExclusion reward beta) ↔
      ∃ lambda, 0 < lambda ∧ lambda ≤ (1 : ℝ) / 2 ∧
        HasQuittingFiniteCalendarRawOrderedPairGroupExclusion reward lambda := by
  constructor
  · rintro ⟨beta, hbeta, hraw⟩
    have hactual :=
      (hasQuittingFiniteCalendarRawNonconcentratedGroupExclusion_iff_actual
        reward beta).mp hraw
    obtain ⟨lambda, hlambda, hhalf, hpairs⟩ :=
      (exists_actualNonconcentratedGroupExclusion_iff_exists_orderedPair
        reward).mp ⟨beta, hbeta, hactual⟩
    exact ⟨lambda, hlambda, hhalf,
      (hasQuittingFiniteCalendarRawOrderedPairGroupExclusion_iff_actual
        reward lambda).mpr hpairs⟩
  · rintro ⟨lambda, hlambda, hhalf, hpairs⟩
    have hactualPairs :=
      (hasQuittingFiniteCalendarRawOrderedPairGroupExclusion_iff_actual
        reward lambda).mp hpairs
    obtain ⟨beta, hbeta, hactual⟩ :=
      (exists_actualNonconcentratedGroupExclusion_iff_exists_orderedPair
        reward).mpr ⟨lambda, hlambda, hhalf, hactualPairs⟩
    exact ⟨beta, hbeta,
      (hasQuittingFiniteCalendarRawNonconcentratedGroupExclusion_iff_actual
        reward beta).mpr hactual⟩

end GameTheory
