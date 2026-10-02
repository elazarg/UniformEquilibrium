/-
The zero-Never/zero-singleton joint-law seam into the off-minimum paid port.

A joint terminal-semantic/law carrier point whose Never coordinate and whose
singleton coordinates all vanish is realized exactly, at a positive global
debt minimum, by a one-date-then-Never profile at a product root carrying two
sure quitters.  That realization is deadline bounded at date zero, because its
only nontrivial live root sits at date zero and every later live root is pure
Continue.  The finite-clock purification descent therefore applies to it
verbatim and returns an off-minimum profile carrying an average-debt paid
response.

Three seams are needed.  The strict margin the exact realization demands is
supplied by the production singleton margin at a positive global minimum: the
prescribed cap coordinate exceeds the solo quitting reward by at least the
whole debt sum, which is positive.  The realizing sequence the product-base
law and the realization consume is extracted from joint-carrier membership by
sequential closure, and the ordinary semantic-carrier membership the margin
needs is the production projection of the same joint point.  The deadline
bound is definitional.

Nothing here claims the product root is a one-stage cap-Nash root, that the
off-minimum target is an equilibrium, or that the paid response is charged
back into a uniform-equilibrium payoff.  The conclusion is the already open
actual off-minimum paid port.
-/
import FableProductBaseRealization
import FableSupportCounterfactual
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticAuxiliaryNashBudget
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticResetIncidenceReturn

noncomputable section

namespace GameTheory

open Filter
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## The strict singleton margin at a positive global minimum -/

/-- **O1.**  At a positive global minimum of total unrestricted behavioral
debt, every prescribed cap coordinate strictly exceeds its own solo quitting
reward.  This is the production singleton margin read as the strict form the
exact product-base realization consumes. -/
theorem fable_minimum_singletonReward_lt_prescribed
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (z : QuittingTerminalSemanticPair ι)
    (hz : z ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum z ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpositive : 0 < quittingTerminalSemanticDebtSum z) (who : ι) :
    reward (quittingSingletonTerminal who) who < z.2 who := by
  have hmargin :=
    minimumTerminalSemantic_singletonMargin z hz hminimum hpositive who
  linarith

/-! ## The one-date-then-Never profile is deadline bounded at date zero -/

omit [DecidableEq ι] in
/-- **O2.**  Every live root of a one-date-then-Never profile strictly after
date zero is pure Continue, so the profile is deadline bounded at `0`. -/
theorem fableDeadlineBounded_oneDateThenNeverProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (root : ι → PMF Bool) :
    FableDeadlineBounded reward
      (quittingOneDateThenNeverProfile reward root) 0 := by
  intro who time htime
  obtain ⟨step, rfl⟩ : ∃ step, time = step + 1 :=
    ⟨time - 1, by omega⟩
  rfl

/-! ## Sequential extraction from the joint semantic/law carrier -/

/-- A joint semantic/law carrier point is the joint limit of an executable
profile sequence, in the two separate limit shapes the product-base law and
the product-base realization consume. -/
theorem fable_exists_profiles_of_mem_terminalSemanticLawCarrier
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (z : QuittingTerminalSemanticPair ι)
    (mu : QuittingTerminalOutcome ι → ℝ)
    (hjoint : (z, mu) ∈ quittingTerminalSemanticLawCarrier reward) :
    ∃ profiles : ℕ → (quittingGame reward).BehaviorProfile,
      Tendsto (fun n => quittingTerminalSemanticPair reward (profiles n))
          atTop (nhds z) ∧
        ∀ outcome, Tendsto
          (fun n =>
            quittingTerminalOutcomeMass reward (profiles n) outcome)
          atTop (nhds (mu outcome)) := by
  classical
  rw [quittingTerminalSemanticLawCarrier, mem_closure_iff_seq_limit] at hjoint
  obtain ⟨points, hpoints, hlimit⟩ := hjoint
  simp only [quittingAttainableTerminalSemanticLawPoints, Set.mem_range]
    at hpoints
  choose profiles hprofiles using hpoints
  have hjointLimit : Tendsto
      (fun n => (quittingTerminalSemanticPair reward (profiles n),
        quittingTerminalOutcomeMass reward (profiles n)))
      atTop (nhds ((z, mu) : QuittingTerminalSemanticLawPoint ι)) := by
    refine hlimit.congr fun n => ?_
    exact (hprofiles n).symm
  refine ⟨profiles, ?_, fun outcome => ?_⟩
  · exact (continuous_fst.tendsto _).comp hjointLimit
  · exact (((continuous_apply outcome).comp continuous_snd).tendsto _).comp
      hjointLimit

/-! ## The exact deadline-bounded realization of the joint point -/

/-- The joint point is realized exactly by the one-date-then-Never profile at
a product root with two sure quitters, and that profile is deadline bounded at
date zero.  This packages the product-base realization with the strict margin
of `fable_minimum_singletonReward_lt_prescribed` and the deadline bound of
`fableDeadlineBounded_oneDateThenNeverProfile`. -/
theorem fable_minimumJointLaw_zeroNever_zeroSingleton_exists_realization
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (z : QuittingTerminalSemanticPair ι)
    (mu : QuittingTerminalOutcome ι → ℝ)
    (hjoint : (z, mu) ∈ quittingTerminalSemanticLawCarrier reward)
    (hNever : mu none = 0)
    (hsingleton : ∀ who, mu (some (quittingSingletonTerminal who)) = 0)
    (hcard : 1 < Fintype.card ι)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum z ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpositive : 0 < quittingTerminalSemanticDebtSum z) :
    ∃ (root : ι → PMF Bool) (i j : ι), i ≠ j ∧
      (root i true).toReal = 1 ∧ (root j true).toReal = 1 ∧
      quittingTerminalSemanticPair reward
          (quittingOneDateThenNeverProfile reward root) = z ∧
      (∀ outcome, quittingTerminalOutcomeMass reward
          (quittingOneDateThenNeverProfile reward root) outcome = mu outcome) ∧
      FableDeadlineBounded reward
        (quittingOneDateThenNeverProfile reward root) 0 := by
  classical
  obtain ⟨profiles, hsem, hlaw⟩ :=
    fable_exists_profiles_of_mem_terminalSemanticLawCarrier reward z mu hjoint
  obtain ⟨R, -, hR⟩ := exists_quittingRewardBound reward
  have hz : z ∈ quittingTerminalSemanticCarrier reward :=
    terminalSemanticLawCarrier_fst_mem_carrier (z, mu) hjoint
  have hstrict : ∀ k, reward (quittingSingletonTerminal k) k < z.2 k :=
    fun k =>
      fable_minimum_singletonReward_lt_prescribed z hz hminimum hpositive k
  obtain ⟨root, i, j, hij, hrooti, hrootj, hpair, hmass⟩ :=
    fable_zeroNever_zeroSingleton_semantic_productBase_realization reward
      profiles mu hlaw hNever hsingleton hcard hR z hsem hstrict
  exact ⟨root, i, j, hij, hrooti, hrootj, hpair, hmass,
    fableDeadlineBounded_oneDateThenNeverProfile reward root⟩

/-! ## The seam -/

/-- **O3, headline.**  A joint terminal-semantic/law carrier point `(z, mu)`
with zero Never mass and zero singleton masses, sitting at a positive global
minimum of total unrestricted behavioral debt, is realized exactly by the
one-date-then-Never profile at a product root with two sure quitters, and that
realization reaches an actual off-minimum profile carrying a pure-time or
Never response whose gain is at least the off-minimum average debt, hence
strictly above the minimum average debt.

The conclusion is the actual off-minimum paid port.  It does not claim the
product root is a one-stage cap-Nash root, that the off-minimum target is an
equilibrium, or that the response is charged back into a uniform-equilibrium
payoff. -/
theorem fable_minimumJointLaw_zeroNever_zeroSingleton_exists_offMinimumPaidPort
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (z : QuittingTerminalSemanticPair ι)
    (mu : QuittingTerminalOutcome ι → ℝ)
    (hjoint : (z, mu) ∈ quittingTerminalSemanticLawCarrier reward)
    (hNever : mu none = 0)
    (hsingleton : ∀ who, mu (some (quittingSingletonTerminal who)) = 0)
    (hcard : 1 < Fintype.card ι)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum z ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpositive : 0 < quittingTerminalSemanticDebtSum z) :
    ∃ (root : ι → PMF Bool) (i j : ι), i ≠ j ∧
      (root i true).toReal = 1 ∧ (root j true).toReal = 1 ∧
      quittingTerminalSemanticPair reward
          (quittingOneDateThenNeverProfile reward root) = z ∧
      (∀ outcome, quittingTerminalOutcomeMass reward
          (quittingOneDateThenNeverProfile reward root) outcome = mu outcome) ∧
      ∃ sigma : (quittingGame reward).BehaviorProfile,
        quittingTerminalSemanticDebtSum z <
            quittingTerminalSemanticDebtSum
              (quittingTerminalSemanticPair reward sigma) ∧
          ∃ (responder : ι) (choice : Option ℕ),
            quittingTerminalSemanticDebtSum
                  (quittingTerminalSemanticPair reward sigma) /
                (Fintype.card ι : ℝ) ≤
              quittingPureTimeDeviationPayoff reward sigma responder choice -
                quittingTerminalPayoff reward sigma responder ∧
            quittingTerminalSemanticDebtSum z / (Fintype.card ι : ℝ) <
              quittingPureTimeDeviationPayoff reward sigma responder choice -
                quittingTerminalPayoff reward sigma responder := by
  classical
  obtain ⟨root, i, j, hij, hrooti, hrootj, hpair, hmass, hbound⟩ :=
    fable_minimumJointLaw_zeroNever_zeroSingleton_exists_realization reward z mu
      hjoint hNever hsingleton hcard hminimum hpositive
  have hcardR : (0 : ℝ) < (Fintype.card ι : ℝ) := by
    have : 0 < Fintype.card ι := by omega
    exact_mod_cast this
  have hminimumProfile : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward
            (quittingOneDateThenNeverProfile reward root)) ≤
        quittingTerminalSemanticDebtSum candidate := by
    rw [hpair]; exact hminimum
  have hpositiveProfile : 0 < quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward
        (quittingOneDateThenNeverProfile reward root)) := by
    rw [hpair]; exact hpositive
  obtain ⟨sigma, hlt, responder, choice, hgain⟩ :=
    fable_deadlineBounded_minimum_offMinimum_paidPort reward
      (quittingOneDateThenNeverProfile reward root) hbound hminimumProfile
      hpositiveProfile
  rw [hpair] at hlt
  refine ⟨root, i, j, hij, hrooti, hrootj, hpair, hmass, sigma, hlt, responder,
    choice, hgain, ?_⟩
  have hdiv : quittingTerminalSemanticDebtSum z / (Fintype.card ι : ℝ) <
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward sigma) /
        (Fintype.card ι : ℝ) := by
    gcongr
  linarith

/-- **O4, row form.**  The same hypotheses, routed through the support
counterfactual, additionally expose the cap-attaining and support-source pure
witnesses on the off-minimum target and the literal paid first-disagreement
row at the off-minimum average debt floor. -/
theorem fable_minimumJointLaw_zeroNever_zeroSingleton_offMinimumPaidRow
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (z : QuittingTerminalSemanticPair ι)
    (mu : QuittingTerminalOutcome ι → ℝ)
    (hjoint : (z, mu) ∈ quittingTerminalSemanticLawCarrier reward)
    (hNever : mu none = 0)
    (hsingleton : ∀ who, mu (some (quittingSingletonTerminal who)) = 0)
    (hcard : 1 < Fintype.card ι)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum z ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpositive : 0 < quittingTerminalSemanticDebtSum z) :
    ∃ (root : ι → PMF Bool) (i j : ι), i ≠ j ∧
      (root i true).toReal = 1 ∧ (root j true).toReal = 1 ∧
      quittingTerminalSemanticPair reward
          (quittingOneDateThenNeverProfile reward root) = z ∧
      (∀ outcome, quittingTerminalOutcomeMass reward
          (quittingOneDateThenNeverProfile reward root) outcome = mu outcome) ∧
      ∃ (sigma : (quittingGame reward).BehaviorProfile) (bound : ℕ)
        (responder : ι) (capWitness sourceWitness : Option ℕ),
        FableDeadlineBounded reward sigma bound ∧
          quittingTerminalSemanticDebtSum z <
            quittingTerminalSemanticDebtSum
              (quittingTerminalSemanticPair reward sigma) ∧
          quittingPureTimeDeviationPayoff reward sigma responder capWitness =
            quittingContinuationBestResponseValue reward sigma responder ∧
          0 < quittingBehaviorStoppingLaw reward (sigma responder)
            sourceWitness ∧
          quittingTerminalSemanticDebtSum
                (quittingTerminalSemanticPair reward sigma) /
              (Fintype.card ι : ℝ) ≤
            quittingPureTimeDeviationPayoff reward sigma responder capWitness -
              quittingPureTimeDeviationPayoff reward sigma responder
                sourceWitness ∧
          ∃ row : QuittingPaidFirstDisagreementRow reward sigma responder
              (quittingTerminalSemanticDebtSum
                  (quittingTerminalSemanticPair reward sigma) /
                (Fintype.card ι : ℝ)),
            row.sourceWitness = sourceWitness ∧
              row.receivingWitness = capWitness := by
  classical
  obtain ⟨root, i, j, hij, hrooti, hrootj, hpair, hmass, hbound⟩ :=
    fable_minimumJointLaw_zeroNever_zeroSingleton_exists_realization reward z mu
      hjoint hNever hsingleton hcard hminimum hpositive
  have hminimumProfile : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward
            (quittingOneDateThenNeverProfile reward root)) ≤
        quittingTerminalSemanticDebtSum candidate := by
    rw [hpair]; exact hminimum
  have hpositiveProfile : 0 < quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward
        (quittingOneDateThenNeverProfile reward root)) := by
    rw [hpair]; exact hpositive
  obtain ⟨sigma, bound, responder, capWitness, sourceWitness, hsigmaBound, hlt,
    hcap, hsource, hgap, row, hrowSource, hrowReceiving⟩ :=
    fable_deadlineBounded_minimum_offMinimum_supportCounterfactualRow reward
      (quittingOneDateThenNeverProfile reward root) hbound hminimumProfile
      hpositiveProfile
  rw [hpair] at hlt
  exact ⟨root, i, j, hij, hrooti, hrootj, hpair, hmass, sigma, bound, responder,
    capWitness, sourceWitness, hsigmaBound, hlt, hcap, hsource, hgap, row,
    hrowSource, hrowReceiving⟩

end GameTheory
