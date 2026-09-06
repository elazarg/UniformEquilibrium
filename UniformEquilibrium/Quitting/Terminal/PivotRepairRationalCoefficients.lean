import MathUE.LinearAlgebra.RationalAffineCoefficients
import UniformEquilibrium.Quitting.Terminal.PivotRepairFiniteLPBoundary

/-! # Rational coefficients from actual finite pivot-repair source data -/

noncomputable section

namespace GameTheory

open _root_.Math
open _root_.Math.Probability
open scoped BigOperators

variable {ι : Type} [Fintype ι] [DecidableEq ι]

private theorem quittingTerminalPayoff_rational_of_finite_rational_laws
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (laws : ι → PMF (Option ℕ)) (bound : ℕ) (observer : ι)
    (hsupport : ∀ player, (laws player).support ⊆ ↑(stoppingLawFinitePrefix bound))
    (hlaws : ∀ player choice, IsRationalReal ((laws player choice).toReal))
    (hreward : ∀ terminal player, IsRationalReal (reward terminal player)) :
    IsRationalReal
      (quittingTerminalPayoff reward (quittingStoppingLawProfile reward laws) observer) := by
  letI : Nonempty ι := ⟨observer⟩
  rw [quittingTerminalPayoff_stoppingLawProfile_eq_expectedPayoff]
  unfold quittingStoppingLawExpectedPayoff quittingIndependentTerminalOutcomeLaw
  rw [expect_map]
  unfold expect
  let kept := Fintype.piFinset fun _ : ι ↦ stoppingLawFinitePrefix bound
  rw [tsum_eq_sum (s := kept)]
  · apply IsRationalReal.sum
    intro times htimes
    apply IsRationalReal.mul
    · rw [Math.PMFProduct.pmfPi_apply, ENNReal.toReal_prod]
      apply IsRationalReal.prod
      intro player _
      exact hlaws player (times player)
    · cases hterminal : quittingFirstStoppingOutcome times with
      | none => simpa [quittingTerminalOutcomeReward, hterminal] using IsRationalReal.zero
      | some terminal =>
          simpa [quittingTerminalOutcomeReward, hterminal] using hreward terminal observer
  · intro times htimes
    have houtside : ∃ player, times player ∉ stoppingLawFinitePrefix bound := by
      by_contra hall
      push Not at hall
      exact htimes (by simpa [kept] using hall)
    obtain ⟨player, hplayer⟩ := houtside
    have hzero : laws player (times player) = 0 := by
      by_contra hne
      exact hplayer (hsupport player (by simpa [PMF.mem_support_iff] using hne))
    rw [Math.PMFProduct.pmfPi_apply]
    have hprod : ∏ who, laws who (times who) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ player) hzero
    rw [hprod]
    simp

namespace QuittingPivotRepairLPInput

open _root_.Math.LinearProgramming

variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
variable (input : QuittingPivotRepairLPInput reward)

omit [Fintype ι] in
private theorem pureLaw_rational (choice drawn : Option ℕ) :
    IsRationalReal (((PMF.pure choice : PMF (Option ℕ)) drawn).toReal) := by
  by_cases hdrawn : drawn = choice
  · simpa [PMF.pure_apply, hdrawn] using IsRationalReal.one
  · simpa [PMF.pure_apply, hdrawn] using IsRationalReal.zero

omit [Fintype ι] in
private theorem pure_support_subset (choice : Option ℕ) (bound : ℕ)
    (hchoice : choice ∈ stoppingLawFinitePrefix bound) :
    (PMF.pure choice : PMF (Option ℕ)).support ⊆ ↑(stoppingLawFinitePrefix bound) := by
  intro drawn hdrawn
  have : drawn = choice := by
    by_contra hne
    exact hdrawn (by simp [PMF.pure_apply, hne])
  simpa [this] using hchoice

omit [Fintype ι] [DecidableEq ι] in
private theorem opponents_support_subset (player : ι) (hne : player ≠ input.pivot) :
    (input.opponents player).support ⊆ ↑(stoppingLawFinitePrefix input.deadline) := by
  intro choice hchoice
  rcases input.opponents_finite player hne choice hchoice with rfl | ⟨time, htime, rfl⟩
  · exact none_mem_stoppingLawFinitePrefix _
  · exact (some_mem_stoppingLawFinitePrefix _ _).mpr htime.le

theorem purePivotPayoff_rational_of_actual_source
    (hopponents : ∀ player, player ≠ input.pivot → ∀ choice,
      IsRationalReal ((input.opponents player choice).toReal))
    (hreward : ∀ terminal player, IsRationalReal (reward terminal player))
    (choice : Option ℕ) (hchoice : choice ∈ stoppingLawFinitePrefix input.deadline)
    (observer : ι) : IsRationalReal (input.purePivotPayoff choice observer) := by
  unfold purePivotPayoff
  apply quittingTerminalPayoff_rational_of_finite_rational_laws
    reward (Function.update input.opponents input.pivot (PMF.pure choice))
      input.deadline observer
  · intro player
    by_cases hplayer : player = input.pivot
    · subst player
      simp only [Function.update_self]
      exact pure_support_subset choice input.deadline hchoice
    · rw [Function.update_of_ne hplayer]
      exact input.opponents_support_subset player hplayer
  · intro player drawn
    by_cases hplayer : player = input.pivot
    · subst player
      simp only [Function.update_self]
      exact pureLaw_rational choice drawn
    · rw [Function.update_of_ne hplayer]
      exact hopponents player hplayer drawn
  · exact hreward

theorem purePivotResponderPayoff_rational_of_actual_source
    (hopponents : ∀ player, player ≠ input.pivot → ∀ choice,
      IsRationalReal ((input.opponents player choice).toReal))
    (hreward : ∀ terminal player, IsRationalReal (reward terminal player))
    (responder : ι) (choice response : Option ℕ)
    (hchoice : choice ∈ stoppingLawFinitePrefix input.deadline)
    (hresponse : response ∈ stoppingLawFinitePrefix input.deadline)
    (observer : ι) :
    IsRationalReal
      (input.purePivotResponderPayoff responder choice response observer) := by
  unfold purePivotResponderPayoff
  let laws := Function.update
    (Function.update input.opponents input.pivot (PMF.pure choice))
      responder (PMF.pure response)
  apply quittingTerminalPayoff_rational_of_finite_rational_laws
    reward laws input.deadline observer
  · intro player
    by_cases hresponder : player = responder
    · subst player
      simp only [laws, Function.update_self]
      exact pure_support_subset response input.deadline hresponse
    · simp only [laws, Function.update_of_ne hresponder]
      by_cases hpivot : player = input.pivot
      · subst player
        simp only [Function.update_self]
        exact pure_support_subset choice input.deadline hchoice
      · rw [Function.update_of_ne hpivot]
        exact input.opponents_support_subset player hpivot
  · intro player drawn
    by_cases hresponder : player = responder
    · subst player
      simp only [laws, Function.update_self]
      exact pureLaw_rational response drawn
    · simp only [laws, Function.update_of_ne hresponder]
      by_cases hpivot : player = input.pivot
      · subst player
        simp only [Function.update_self]
        exact pureLaw_rational choice drawn
      · rw [Function.update_of_ne hpivot]
        exact hopponents player hpivot drawn
  · exact hreward

omit [Fintype ι] [DecidableEq ι] in
private theorem head_rational
    (mass : PivotRepairMass input.deadline)
    (hmass : ∀ coordinate, IsRationalReal (mass coordinate))
    (time : Fin input.deadline) :
    IsRationalReal (pivotRepairHead mass time) := hmass (Sum.inl time)

omit [Fintype ι] [DecidableEq ι] in
private theorem late_rational
    (mass : PivotRepairMass input.deadline)
    (hmass : ∀ coordinate, IsRationalReal (mass coordinate)) :
    IsRationalReal (pivotRepairLate mass) := hmass (Sum.inr .late)

omit [Fintype ι] [DecidableEq ι] in
private theorem never_rational
    (mass : PivotRepairMass input.deadline)
    (hmass : ∀ coordinate, IsRationalReal (mass coordinate)) :
    IsRationalReal (pivotRepairNever mass) := hmass (Sum.inr .never)

omit [Fintype ι] [DecidableEq ι] in
private theorem firstAtom_rational
    (mass : PivotRepairMass input.deadline)
    (hmass : ∀ coordinate, IsRationalReal (mass coordinate)) :
    IsRationalReal (pivotRepairFirstAtom mass) := hmass (Sum.inr .firstAtom)

omit [Fintype ι] [DecidableEq ι] in
private theorem some_fin_mem_prefix (time : Fin input.deadline) :
    some time.val ∈ stoppingLawFinitePrefix input.deadline :=
  (some_mem_stoppingLawFinitePrefix _ _).mpr time.isLt.le

omit [Fintype ι] [DecidableEq ι] in
private theorem deadline_mem_prefix :
    some input.deadline ∈ stoppingLawFinitePrefix input.deadline :=
  (some_mem_stoppingLawFinitePrefix _ _).mpr le_rfl

omit [Fintype ι] [DecidableEq ι] in
private theorem none_mem_prefix :
    none ∈ stoppingLawFinitePrefix input.deadline :=
  none_mem_stoppingLawFinitePrefix _

theorem prescribedPayoff_rational_of_actual_source
    (hopponents : ∀ player, player ≠ input.pivot → ∀ choice,
      IsRationalReal ((input.opponents player choice).toReal))
    (hreward : ∀ terminal player, IsRationalReal (reward terminal player))
    (mass : PivotRepairMass input.deadline)
    (hmass : ∀ coordinate, IsRationalReal (mass coordinate)) (observer : ι) :
    IsRationalReal (input.prescribedPayoff mass observer) := by
  unfold prescribedPayoff
  apply IsRationalReal.add
  · apply IsRationalReal.add
    · apply IsRationalReal.sum
      intro time _
      exact (input.head_rational mass hmass time).mul
        (input.purePivotPayoff_rational_of_actual_source hopponents hreward
          (some time.val) (input.some_fin_mem_prefix time) observer)
    · exact (input.late_rational mass hmass).mul
        (input.purePivotPayoff_rational_of_actual_source hopponents hreward
          (some input.deadline) input.deadline_mem_prefix observer)
  · exact (input.never_rational mass hmass).mul
      (input.purePivotPayoff_rational_of_actual_source hopponents hreward
        none input.none_mem_prefix observer)

theorem pureResponsePayoff_rational_of_actual_source
    (hopponents : ∀ player, player ≠ input.pivot → ∀ choice,
      IsRationalReal ((input.opponents player choice).toReal))
    (hreward : ∀ terminal player, IsRationalReal (reward terminal player))
    (mass : PivotRepairMass input.deadline)
    (hmass : ∀ coordinate, IsRationalReal (mass coordinate))
    (responder : ι) (response : Option ℕ)
    (hresponse : response ∈ stoppingLawFinitePrefix input.deadline)
    (observer : ι) :
    IsRationalReal (input.pureResponsePayoff mass responder response observer) := by
  unfold pureResponsePayoff
  apply IsRationalReal.add
  · apply IsRationalReal.add
    · apply IsRationalReal.sum
      intro time _
      exact (input.head_rational mass hmass time).mul
        (input.purePivotResponderPayoff_rational_of_actual_source
          hopponents hreward responder (some time.val) response
            (input.some_fin_mem_prefix time) hresponse observer)
    · exact (input.late_rational mass hmass).mul
        (input.purePivotResponderPayoff_rational_of_actual_source
          hopponents hreward responder (some input.deadline) response
            input.deadline_mem_prefix hresponse observer)
  · exact (input.never_rational mass hmass).mul
      (input.purePivotResponderPayoff_rational_of_actual_source
        hopponents hreward responder none response input.none_mem_prefix hresponse observer)

theorem earlyContribution_rational_of_actual_source
    (hopponents : ∀ player, player ≠ input.pivot → ∀ choice,
      IsRationalReal ((input.opponents player choice).toReal))
    (hreward : ∀ terminal player, IsRationalReal (reward terminal player))
    (mass : PivotRepairMass input.deadline)
    (hmass : ∀ coordinate, IsRationalReal (mass coordinate))
    (responder : ι) : IsRationalReal (input.earlyContribution mass responder) := by
  unfold earlyContribution
  apply IsRationalReal.add
  · apply IsRationalReal.sum
    intro time _
    exact (input.head_rational mass hmass time).mul
      (input.purePivotResponderPayoff_rational_of_actual_source
        hopponents hreward responder (some time.val) none
          (input.some_fin_mem_prefix time) input.none_mem_prefix responder)
  · apply IsRationalReal.mul
    · exact (input.late_rational mass hmass).add (input.never_rational mass hmass)
    · exact input.purePivotResponderPayoff_rational_of_actual_source
        hopponents hreward responder none none input.none_mem_prefix
          input.none_mem_prefix responder

theorem otherNeverProduct_rational_of_actual_source
    (hopponents : ∀ player, player ≠ input.pivot → ∀ choice,
      IsRationalReal ((input.opponents player choice).toReal))
    (responder : ι) : IsRationalReal (input.otherNeverProduct responder) := by
  unfold otherNeverProduct
  apply IsRationalReal.prod
  intro player hplayer
  exact hopponents player (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hplayer)) none

theorem pivotCap_rational_of_actual_source
    (hopponents : ∀ player, player ≠ input.pivot → ∀ choice,
      IsRationalReal ((input.opponents player choice).toReal))
    (hreward : ∀ terminal player, IsRationalReal (reward terminal player)) :
    IsRationalReal input.pivotCap := by
  have hcandidate (index : Fin input.deadline ⊕ Bool) :
      IsRationalReal (input.pivotCapCandidateValue index) := by
    rcases index with time | late
    · exact input.purePivotPayoff_rational_of_actual_source
        hopponents hreward (some time.val) (input.some_fin_mem_prefix time) input.pivot
    · cases late
      · exact input.purePivotPayoff_rational_of_actual_source
          hopponents hreward none input.none_mem_prefix input.pivot
      · unfold pivotCapCandidateValue pivotLatePayoff pivotNeverPayoff
        apply IsRationalReal.add
        · exact input.purePivotPayoff_rational_of_actual_source
            hopponents hreward none input.none_mem_prefix input.pivot
        · apply IsRationalReal.mul (hreward _ _)
          apply IsRationalReal.prod
          intro player hplayer
          exact hopponents player (Finset.ne_of_mem_erase hplayer) none
  unfold pivotCap
  obtain ⟨index, _, heq⟩ :=
    Finset.exists_mem_eq_sup' Finset.univ_nonempty input.pivotCapCandidateValue
  rw [heq]
  exact hcandidate index

theorem responderNeverEndpoint_rational_of_actual_source
    (hopponents : ∀ player, player ≠ input.pivot → ∀ choice,
      IsRationalReal ((input.opponents player choice).toReal))
    (hreward : ∀ terminal player, IsRationalReal (reward terminal player))
    (mass : PivotRepairMass input.deadline)
    (hmass : ∀ coordinate, IsRationalReal (mass coordinate)) (responder : ι) :
    IsRationalReal (input.responderNeverEndpoint mass responder) := by
  unfold responderNeverEndpoint responderEarlierReward
  exact (input.earlyContribution_rational_of_actual_source
    hopponents hreward mass hmass responder).add
      ((input.otherNeverProduct_rational_of_actual_source hopponents responder).mul
        ((hreward _ _).mul (input.late_rational mass hmass)))

theorem responderFirstEndpoint_rational_of_actual_source
    (hopponents : ∀ player, player ≠ input.pivot → ∀ choice,
      IsRationalReal ((input.opponents player choice).toReal))
    (hreward : ∀ terminal player, IsRationalReal (reward terminal player))
    (mass : PivotRepairMass input.deadline)
    (hmass : ∀ coordinate, IsRationalReal (mass coordinate)) (responder : ι) :
    IsRationalReal (input.responderFirstEndpoint mass responder) := by
  unfold responderFirstEndpoint responderTieReward responderLaterReward
  apply IsRationalReal.add
  · exact input.earlyContribution_rational_of_actual_source
      hopponents hreward mass hmass responder
  · apply IsRationalReal.mul
    · exact input.otherNeverProduct_rational_of_actual_source hopponents responder
    · apply IsRationalReal.add
      · exact (hreward _ _).mul
          ((input.late_rational mass hmass).add (input.never_rational mass hmass))
      · exact ((hreward _ _).sub (hreward _ _)).mul
          (input.firstAtom_rational mass hmass)

theorem responderLimitEndpoint_rational_of_actual_source
    (hopponents : ∀ player, player ≠ input.pivot → ∀ choice,
      IsRationalReal ((input.opponents player choice).toReal))
    (hreward : ∀ terminal player, IsRationalReal (reward terminal player))
    (mass : PivotRepairMass input.deadline)
    (hmass : ∀ coordinate, IsRationalReal (mass coordinate)) (responder : ι) :
    IsRationalReal (input.responderLimitEndpoint mass responder) := by
  unfold responderLimitEndpoint responderEarlierReward responderLaterReward
  apply IsRationalReal.add
  · exact input.earlyContribution_rational_of_actual_source
      hopponents hreward mass hmass responder
  · apply IsRationalReal.mul
    · exact input.otherNeverProduct_rational_of_actual_source hopponents responder
    · exact ((hreward _ _).mul (input.late_rational mass hmass)).add
        ((hreward _ _).mul (input.never_rational mass hmass))

/-- Rational reward entries and actual finite opponent probabilities make
every finite LP constraint rational at every rational mass point. -/
theorem constraintGain_rational_of_actual_source
    (hopponents : ∀ player, player ≠ input.pivot → ∀ choice,
      IsRationalReal ((input.opponents player choice).toReal))
    (hreward : ∀ terminal player, IsRationalReal (reward terminal player))
    (mass : PivotRepairMass input.deadline)
    (hmass : ∀ coordinate, IsRationalReal (mass coordinate))
    (index : input.ConstraintIndex) : IsRationalReal (input.constraintGain mass index) := by
  rcases index with _ | (_ | ⟨responder, time | endpoint⟩)
  · exact IsRationalReal.zero
  · exact (input.pivotCap_rational_of_actual_source hopponents hreward).sub
      (input.prescribedPayoff_rational_of_actual_source
        hopponents hreward mass hmass input.pivot)
  · exact (input.pureResponsePayoff_rational_of_actual_source hopponents hreward
      mass hmass responder (some time.val)
        (input.some_fin_mem_prefix time) responder).sub
      (input.prescribedPayoff_rational_of_actual_source
        hopponents hreward mass hmass responder)
  · fin_cases endpoint
    · exact (input.responderNeverEndpoint_rational_of_actual_source
        hopponents hreward mass hmass responder).sub
        (input.prescribedPayoff_rational_of_actual_source
          hopponents hreward mass hmass responder)
    · exact (input.responderFirstEndpoint_rational_of_actual_source
        hopponents hreward mass hmass responder).sub
        (input.prescribedPayoff_rational_of_actual_source
          hopponents hreward mass hmass responder)
    · exact (input.responderLimitEndpoint_rational_of_actual_source
        hopponents hreward mass hmass responder).sub
        (input.prescribedPayoff_rational_of_actual_source
          hopponents hreward mass hmass responder)

theorem objective_rational_of_actual_source
    (hopponents : ∀ player, player ≠ input.pivot → ∀ choice,
      IsRationalReal ((input.opponents player choice).toReal))
    (hreward : ∀ terminal player, IsRationalReal (reward terminal player))
    (mass : PivotRepairMass input.deadline)
    (hmass : ∀ coordinate, IsRationalReal (mass coordinate)) :
    IsRationalReal (input.objective mass) := by
  unfold objective
  obtain ⟨index, _, heq⟩ :=
    Finset.exists_mem_eq_sup' Finset.univ_nonempty (input.constraintGain mass)
  rw [heq]
  exact input.constraintGain_rational_of_actual_source
    hopponents hreward mass hmass index

/-- Rational reward entries and actual finite opponent probabilities give
the finite pivot-repair LP rational affine constraint coefficients. -/
theorem hasRationalAffineConstraintCoefficients_of_actual_source
    (hopponents : ∀ player, player ≠ input.pivot → ∀ choice,
      IsRationalReal ((input.opponents player choice).toReal))
    (hreward : ∀ terminal player, IsRationalReal (reward terminal player))
    (index : input.ConstraintIndex) :
    HasRationalAffineCoefficients (fun mass ↦ input.constraintGain mass index) := by
  constructor
  · exact fun first second scale ↦ input.constraintGain_affine first second scale index
  · intro mass hmass
    exact input.constraintGain_rational_of_actual_source
      hopponents hreward mass hmass index

/-- The same actual source data packages every constraint as explicit exact
rational-affine coefficient data. -/
theorem exists_rationalAffineConstraintFunctional_of_actual_source
    (hopponents : ∀ player, player ≠ input.pivot → ∀ choice,
      IsRationalReal ((input.opponents player choice).toReal))
    (hreward : ∀ terminal player, IsRationalReal (reward terminal player))
    (index : input.ConstraintIndex) :
    ∃ coded : RationalAffineFunctional
        (Fin input.deadline ⊕ PivotRepairTailCoordinate),
      coded.eval = fun mass : PivotRepairMass input.deadline ↦
        input.constraintGain mass index := by
  exact (input.hasRationalAffineConstraintCoefficients_of_actual_source
    hopponents hreward index).exists_rationalAffineFunctional

end QuittingPivotRepairLPInput

end GameTheory
