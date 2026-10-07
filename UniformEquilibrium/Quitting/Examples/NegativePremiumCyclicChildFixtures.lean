import UniformEquilibrium.Quitting.Cycles.NegativePremiumCyclicChildFiniteHorizon

/-! # Literal signed and cap-saturating negative-premium fixtures

These instances consume the raw source. No stationary, matrix or carrier
screen exclusion is asserted here.
-/

noncomputable section

namespace GameTheory.NegativePremiumCyclicChild.Fixtures

def loss : ℝ := 100 / 729
def lower : ℝ := 629 / 729
def upper : ℝ := 829 / 729

/-- All fifteen nonempty rows of the packet's sixty-coordinate table. -/
def survivorReward : Reward := fun coalition =>
  if coalition.val = {0} then ![1, 0, 0, 0]
  else if coalition.val = {1} then ![2, 1, 4, 0]
  else if coalition.val = {2} then ![2, 0, 1, 4]
  else if coalition.val = {3} then ![0, 4, 0, 1]
  else if coalition.val = {0, 1} then ![upper, lower, 3, -1]
  else if coalition.val = {0, 2} then ![1, -1, lower, 3]
  else if coalition.val = {0, 3} then ![lower, 3, -1, lower]
  else if coalition.val = {1, 2} then ![3, 1, upper, 3]
  else if coalition.val = {1, 3} then ![1, upper, 3, 1]
  else if coalition.val = {2, 3} then ![1, 3, 1, upper]
  else if coalition.val = {0, 1, 2} then ![upper, lower, 1, 2]
  else if coalition.val = {0, 1, 3} then ![1, 1, 2, lower]
  else if coalition.val = {0, 2, 3} then ![lower, 2, lower, 1]
  else if coalition.val = {1, 2, 3} then ![2, upper, upper, upper]
  else ![1, 1, 1, 1]

theorem survivor_raw : RawTable loss survivorReward := by
  constructor <;>
    norm_num [survivorReward, loss, lower, upper, quittingSingletonTerminal,
      Finset.ext_iff, Fin.forall_fin_succ]

/-- Each cap is saturated, and every otherwise unspecified coordinate is 37. -/
def boundaryReward : Reward := fun coalition =>
  if coalition.val = {0} then ![1, 0, 0, 0]
  else if coalition.val = {1} then ![2, 1, 4, 0]
  else if coalition.val = {2} then ![2, 0, 1, 4]
  else if coalition.val = {3} then ![0, 4, 0, 1]
  else if coalition.val = {0, 1} then ![2, 0, 37, 37]
  else if coalition.val = {0, 2} then ![1, 37, 0, 37]
  else if coalition.val = {0, 3} then ![0, 3, -1, 0]
  else if coalition.val = {1, 2} then ![37, 1, 2, 37]
  else if coalition.val = {1, 3} then ![37, 2, 37, 1]
  else if coalition.val = {2, 3} then ![37, 37, 1, 2]
  else if coalition.val = {0, 1, 3} then ![37, 1, 37, 37]
  else if coalition.val = {0, 2, 3} then ![37, 37, 0, 37]
  else ![37, 37, 37, 37]

theorem boundary_raw : RawTable 1 boundaryReward := by
  constructor <;>
    norm_num [boundaryReward, quittingSingletonTerminal, Finset.ext_iff, Fin.forall_fin_succ]

def lowOwn : Payoff Player := ![-3, -5, -1, -4]
def lowScale : Payoff Player := ![1, 2, 3, 4]
def lowSignedReward : Reward :=
  quittingPlayerwiseAffineReward survivorReward lowScale (fun who => lowOwn who - lowScale who)

def lowTarget (rates : Rates) : Payoff Player :=
  ![-3 - loss * rates.y, -5 + 2 * (3 * rates.y - rates.p), -1, -4 - 4 * loss * rates.p]

theorem lowScale_pos (who : Player) : 0 < lowScale who := by
  fin_cases who <;> norm_num [lowScale]

theorem lowSigned_raw : SignedRawTable loss lowOwn lowScale lowSignedReward := by
  refine ⟨lowScale_pos, ?_⟩
  have hnormalized : normalizedReward lowOwn lowScale lowSignedReward = survivorReward := by
    funext coalition who
    fin_cases who <;>
      simp [normalizedReward, lowSignedReward, quittingPlayerwiseAffineReward, lowOwn, lowScale]
    all_goals ring
  rw [hnormalized]
  exact survivor_raw

/-- The literal signed table has an actual negative target in every coordinate,
although Never still has payoff zero. -/
theorem lowSigned_negative_uniform_target : ∃ rates : Rates,
    (∀ who, lowTarget rates who < 0) ∧
    quittingTerminalPayoff lowSignedReward
      (quittingCyclicBehaviorProfile lowSignedReward (cycle rates) 0) = lowTarget rates ∧
    (quittingGame lowSignedReward).IsεAsymptoticNash
      (quittingTerminalPayoff lowSignedReward) 0
      (quittingCyclicBehaviorProfile lowSignedReward (cycle rates) 0) ∧
    (quittingGame lowSignedReward).IsUniformEquilibriumPayoff none (lowTarget rates) := by
  obtain ⟨canonical, hcase⟩ := survivor_raw.exists_certificate
  have hlow : canonical.value = lowValue loss canonical.rates ∧
      canonical.rates.p ∈ Set.Ioo (0 : ℝ) (1 / 2) ∧
      canonical.rates.y ∈ Set.Ioo (2 / 5 : ℝ) (2 / 3) := by
    rcases hcase with hlow | hhigh
    · exact hlow.2
    · norm_num [loss] at hhigh
  let source := canonical.affine lowScale (fun who => lowOwn who - lowScale who) lowScale_pos
  have hvalue : source.value 0 = lowTarget canonical.rates := by
    funext who
    change lowScale who * canonical.value 0 who + (lowOwn who - lowScale who) = _
    rw [hlow.1]
    fin_cases who <;> simp [lowValue, lowA, lowOwn, lowScale, lowTarget] <;> ring
  refine ⟨canonical.rates, ?_, ?_, ?_, ?_⟩
  · intro who
    have hloss : 0 < loss := by norm_num [loss]
    have hfirst := mul_pos hloss canonical.rates.y_mem.1
    have hsecond := mul_pos hloss hlow.2.1.1
    fin_cases who <;> norm_num [lowTarget] <;>
      nlinarith [hlow.2.1.1, hlow.2.2.2]
  · exact source.terminal_eq.trans hvalue
  · exact source.terminalNash
  · rw [← hvalue]
    exact source.uniformPayoff

def boundaryOwn : Payoff Player := ![-5, 2, -7, 0]
def boundaryScale : Payoff Player := ![2, 1 / 3, 5, 7 / 2]
def boundarySignedReward : Reward :=
  quittingPlayerwiseAffineReward boundaryReward boundaryScale
    (fun who => boundaryOwn who - boundaryScale who)

theorem boundaryScale_pos (who : Player) : 0 < boundaryScale who := by
  fin_cases who <;> norm_num [boundaryScale]

theorem boundarySigned_raw : SignedRawTable 1 boundaryOwn boundaryScale boundarySignedReward := by
  refine ⟨boundaryScale_pos, ?_⟩
  have hnormalized : normalizedReward boundaryOwn boundaryScale boundarySignedReward =
      boundaryReward := by
    funext coalition who
    fin_cases who <;>
      simp [normalizedReward, boundarySignedReward, quittingPlayerwiseAffineReward,
        boundaryOwn, boundaryScale]
    all_goals ring
  rw [hnormalized]
  exact boundary_raw

/-- Loss one, binding caps, unused reward 37, signed own levels and a zero
target coordinate are all retained in the actual original game. -/
theorem boundarySigned_exact_uniform_target :
    quittingTerminalPayoff boundarySignedReward
      (quittingCyclicBehaviorProfile boundarySignedReward (cycle highRates) 0) =
        ![-75 / 13, 8 / 3, -7, 0] ∧
    (quittingGame boundarySignedReward).IsεAsymptoticNash
      (quittingTerminalPayoff boundarySignedReward) 0
      (quittingCyclicBehaviorProfile boundarySignedReward (cycle highRates) 0) ∧
    (quittingGame boundarySignedReward).IsUniformEquilibriumPayoff none
      ![-75 / 13, 8 / 3, -7, 0] := by
  have hcert := high_certificate 1 boundaryReward boundary_raw (by norm_num)
  let canonical : Certificate boundaryReward := ⟨highRates, highValue, hcert.1, hcert.2⟩
  let source := canonical.affine boundaryScale
    (fun who => boundaryOwn who - boundaryScale who) boundaryScale_pos
  have hvalue : source.value 0 = ![-75 / 13, 8 / 3, -7, 0] := by
    funext who
    fin_cases who <;>
      norm_num [source, canonical, Certificate.affine, quittingPlayerwiseAffinePayoff,
        highValue, boundaryOwn, boundaryScale]
  exact ⟨source.terminal_eq.trans hvalue, source.terminalNash, hvalue ▸ source.uniformPayoff⟩

end GameTheory.NegativePremiumCyclicChild.Fixtures
