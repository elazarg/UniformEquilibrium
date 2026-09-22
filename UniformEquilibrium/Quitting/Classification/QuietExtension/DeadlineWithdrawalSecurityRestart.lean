import UniformEquilibrium.Quitting.Classification.QuietExtension.DeadlineWithdrawalSecurityLP
import MathUE.ProbabilityMassFunction.GeometricPivotStoppingLaw
import UniformEquilibrium.Quitting.Paths.FirstStoppingOutcomeCoalition

/-!
# Private stationary restart laws after a withdrawal deadline

The clock starts strictly after the withdrawn atom. It is sampled privately
and does not read opponent clocks. These constructions realize positive LP
hazards as actual PMFs; their payoff-security estimate is a separate theorem.
-/

noncomputable section

namespace GameTheory

open _root_.Math.Probability

/-- Fresh positive stationary hazard beginning at `deadline + 1`. -/
def deadlineWithdrawalSecurityRestartLaw
    (deadline : ℕ) (hazard : ℝ) (hpositive : 0 < hazard) (hle : hazard ≤ 1) :
    PMF (Option ℕ) :=
  geometricFiniteStoppingLaw (deadline + 1) hazard hpositive hle

theorem deadlineWithdrawalSecurityRestartLaw_none
    (deadline : ℕ) (hazard : ℝ) (hpositive : 0 < hazard) (hle : hazard ≤ 1) :
    deadlineWithdrawalSecurityRestartLaw deadline hazard hpositive hle none = 0 := by
  exact geometricFiniteStoppingLaw_none _ _ _ _

theorem deadlineWithdrawalSecurityRestartLaw_before
    (deadline : ℕ) (hazard : ℝ) (hpositive : 0 < hazard) (hle : hazard ≤ 1)
    (time : ℕ) (htime : time ≤ deadline) :
    deadlineWithdrawalSecurityRestartLaw deadline hazard hpositive hle (some time) = 0 := by
  exact geometricFiniteStoppingLaw_some_of_lt _ _ _ _ (by omega)

theorem deadlineWithdrawalSecurityRestartLaw_mass
    (deadline : ℕ) (hazard : ℝ) (hpositive : 0 < hazard) (hle : hazard ≤ 1)
    (offset : ℕ) :
    (deadlineWithdrawalSecurityRestartLaw deadline hazard hpositive hle
      (some (deadline + 1 + offset))).toReal = hazard * (1 - hazard) ^ offset := by
  exact geometricFiniteStoppingLaw_add_apply_toReal _ _ _ _ _

/-- Restart only the exact finite deadline atom. Never deadlines and every
other source clock remain unchanged. -/
def deadlineWithdrawalSecurityRestartKernel
    (hazard : ℝ) (hpositive : 0 < hazard) (hle : hazard ≤ 1)
    (source deadline : Option ℕ) : PMF (Option ℕ) :=
  match deadline with
  | none => PMF.pure source
  | some time => if source = some time then
      deadlineWithdrawalSecurityRestartLaw time hazard hpositive hle
    else PMF.pure source

theorem deadlineWithdrawalSecurityRestartKernel_none
    (hazard : ℝ) (hpositive : 0 < hazard) (hle : hazard ≤ 1)
    (source : Option ℕ) :
    deadlineWithdrawalSecurityRestartKernel hazard hpositive hle source none =
      PMF.pure source := rfl

theorem deadlineWithdrawalSecurityRestartKernel_tie
    (hazard : ℝ) (hpositive : 0 < hazard) (hle : hazard ≤ 1) (time : ℕ) :
    deadlineWithdrawalSecurityRestartKernel hazard hpositive hle (some time) (some time) =
      deadlineWithdrawalSecurityRestartLaw time hazard hpositive hle := by
  simp [deadlineWithdrawalSecurityRestartKernel]

theorem deadlineWithdrawalSecurityRestartKernel_ne
    (hazard : ℝ) (hpositive : 0 < hazard) (hle : hazard ≤ 1)
    (source : Option ℕ) (time : ℕ) (hsource : source ≠ some time) :
    deadlineWithdrawalSecurityRestartKernel hazard hpositive hle source (some time) =
      PMF.pure source := by
  simp [deadlineWithdrawalSecurityRestartKernel, hsource]

/-- One complete unilateral law, using independent private source/deadline
draws and fresh stationary randomness only at the withdrawn atom. -/
def deadlineWithdrawalSecurityReplacementLaw
    (sourceLaw outsideLaw : PMF (Option ℕ))
    (hazard : ℝ) (hpositive : 0 < hazard) (hle : hazard ≤ 1) : PMF (Option ℕ) :=
  sourceLaw.bind fun source => outsideLaw.bind fun deadline =>
    deadlineWithdrawalSecurityRestartKernel hazard hpositive hle source deadline

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Against opponents who all use Never, every finite own clock absorbs
alone. This statement uses the actual first-coalition semantics. -/
theorem deadlineWithdrawalSecurity_terminalPayoff_opponentsNever
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (i : ι) (time : ℕ) :
    quittingPureClockTerminalPayoff reward
        (Function.update (fun _ : Option ι => none) (some i) (some time)) (some i) =
      reward ⟨{some i}, Finset.singleton_nonempty (some i)⟩ (some i) := by
  have houtcome := quittingFirstStoppingOutcome_eq_coalition_of_strictly_later
    (Function.update (fun _ : Option ι => none) (some i) (some time))
    {some i} (Finset.singleton_nonempty (some i)) time
    (by
      intro player hplayer
      have heq := Finset.mem_singleton.mp hplayer
      subst player
      simp)
    (by
      intro player hplayer
      have hne : player ≠ some i := by simpa using hplayer
      simp [Function.update_of_ne hne, quittingStoppingTimeValue])
  simp [quittingPureClockTerminalPayoff, houtcome]

/-- A positive restart hazard really obtains the singleton payoff against
opponent Never; its LP value is not assigned to a Never clock. -/
theorem deadlineWithdrawalSecurityRestartLaw_terminalPayoff_opponentsNever
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (i : ι) (deadline : ℕ) (hazard : ℝ)
    (hpositive : 0 < hazard) (hle : hazard ≤ 1) :
    expect (deadlineWithdrawalSecurityRestartLaw deadline hazard hpositive hle)
        (fun clock => quittingPureClockTerminalPayoff reward
          (Function.update (fun _ : Option ι => none) (some i) clock) (some i)) =
      reward ⟨{some i}, Finset.singleton_nonempty (some i)⟩ (some i) := by
  rw [deadlineWithdrawalSecurityRestartLaw, geometricFiniteStoppingLaw, expect_map]
  simp only [deadlineWithdrawalSecurity_terminalPayoff_opponentsNever]
  exact expect_const _ _

/-- Actual geometric restart data are produced from every reward table and
strict error request. The value premise consists only of the finite LP rows. -/
theorem exists_deadlineWithdrawalSecurityRestartLaw
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (i : ι) (deadline : ℕ) (error : ℝ) (herror : 0 < error) :
    ∃ (hazard : ℝ) (hpositive : 0 < hazard) (hle : hazard ≤ 1),
      DeadlineWithdrawalSecurityFeasible reward i hazard
        (deadlineWithdrawalSecurityValue reward i - error) ∧
      deadlineWithdrawalSecurityRestartLaw deadline hazard hpositive hle none = 0 ∧
      ∀ time ≤ deadline,
        deadlineWithdrawalSecurityRestartLaw deadline hazard hpositive hle (some time) = 0 := by
  obtain ⟨hazard, hpositive, hfeasible⟩ :=
    exists_deadlineWithdrawalSecurity_positive_approximation reward i error herror
  exact ⟨hazard, hpositive, hfeasible.1.2, hfeasible,
    deadlineWithdrawalSecurityRestartLaw_none _ _ _ _,
    fun time htime => deadlineWithdrawalSecurityRestartLaw_before _ _ _ _ time htime⟩

end GameTheory
