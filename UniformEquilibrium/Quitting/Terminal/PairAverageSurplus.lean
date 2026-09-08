import UniformEquilibrium.Quitting.Root.TerminalSemanticMoment

/-! # Two-coordinate surplus bounds from terminal reward moments -/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- Average singleton surplus of two coordinates. -/
def quittingTwoCoordinateAverageSurplus
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (first second : ι) (value : Payoff ι) : ℝ :=
  ((value first - reward (quittingSingletonTerminal first) first) +
    (value second - reward (quittingSingletonTerminal second) second)) / 2

/-- A four-case pointwise reward bound passes through the actual terminal
outcome law, with the Never contribution retained explicitly. -/
theorem quittingTwoCoordinateAverageSurplus_terminalPayoff_le
    (profile : (quittingGame reward).BehaviorProfile)
    (first second : ι)
    (primary secondary : {S : Finset ι // S.Nonempty})
    (hne : primary ≠ secondary) (primaryBound secondaryBound otherBound : ℝ)
    (hprimary : quittingTwoCoordinateAverageSurplus reward first second
      (reward primary) ≤ primaryBound)
    (hsecondary : quittingTwoCoordinateAverageSurplus reward first second
      (reward secondary) ≤ secondaryBound)
    (hother : ∀ terminal, terminal ≠ primary → terminal ≠ secondary →
      quittingTwoCoordinateAverageSurplus reward first second
        (reward terminal) ≤ otherBound) :
    quittingTwoCoordinateAverageSurplus reward first second
        (quittingTerminalPayoff reward profile) ≤
      primaryBound * quittingTerminalOutcomeMass reward profile (some primary) +
        secondaryBound * quittingTerminalOutcomeMass reward profile (some secondary) +
        otherBound * (1 - quittingTerminalOutcomeMass reward profile (some primary) -
          quittingTerminalOutcomeMass reward profile (some secondary) -
          quittingTerminalOutcomeMass reward profile none) -
        ((reward (quittingSingletonTerminal first) first +
          reward (quittingSingletonTerminal second) second) / 2) *
          quittingTerminalOutcomeMass reward profile none := by
  let mass := quittingTerminalOutcomeMass reward profile
  let singletonSum := reward (quittingSingletonTerminal first) first +
    reward (quittingSingletonTerminal second) second
  have hmoment := quittingTerminalRewardMoment_outcomeMass reward profile
  have hfirst := congrFun hmoment first
  have hsecond := congrFun hmoment second
  have htotal := (quittingTerminalOutcomeMass_mem_stdSimplex reward profile).2
  change (∑ outcome, mass outcome) = 1 at htotal
  have havg :
      quittingTwoCoordinateAverageSurplus reward first second
          (quittingTerminalPayoff reward profile) =
        ∑ outcome, mass outcome *
          ((quittingTerminalOutcomeReward reward outcome first +
              quittingTerminalOutcomeReward reward outcome second - singletonSum) / 2) := by
    unfold quittingTwoCoordinateAverageSurplus
    rw [← hfirst, ← hsecond]
    unfold quittingTerminalRewardMoment
    dsimp only [mass, singletonSum]
    calc
      ((∑ x, quittingTerminalOutcomeMass reward profile x *
            quittingTerminalOutcomeReward reward x first) -
          reward (quittingSingletonTerminal first) first +
        ((∑ x, quittingTerminalOutcomeMass reward profile x *
            quittingTerminalOutcomeReward reward x second) -
          reward (quittingSingletonTerminal second) second)) / 2 =
          ((∑ x, quittingTerminalOutcomeMass reward profile x *
            quittingTerminalOutcomeReward reward x first) +
          (∑ x, quittingTerminalOutcomeMass reward profile x *
            quittingTerminalOutcomeReward reward x second) - singletonSum) / 2 := by
              dsimp only [singletonSum]
              ring
      _ = ((∑ x, (quittingTerminalOutcomeMass reward profile x *
            quittingTerminalOutcomeReward reward x first +
              quittingTerminalOutcomeMass reward profile x *
                quittingTerminalOutcomeReward reward x second)) - singletonSum) / 2 := by
                  rw [Finset.sum_add_distrib]
      _ = ((∑ x, quittingTerminalOutcomeMass reward profile x *
            (quittingTerminalOutcomeReward reward x first +
              quittingTerminalOutcomeReward reward x second)) -
            (∑ x, quittingTerminalOutcomeMass reward profile x) * singletonSum) / 2 := by
              rw [htotal]
              simp only [one_mul]
              congr 2
              apply Finset.sum_congr rfl
              intro outcome _
              ring
      _ = _ := by
        rw [Finset.sum_mul, ← Finset.sum_sub_distrib, Finset.sum_div]
        apply Finset.sum_congr rfl
        intro outcome _
        ring
  rw [havg]
  calc
    (∑ outcome, mass outcome *
        ((quittingTerminalOutcomeReward reward outcome first +
          quittingTerminalOutcomeReward reward outcome second - singletonSum) / 2)) ≤
      ∑ outcome, mass outcome *
        (if outcome = some primary then primaryBound
         else if outcome = some secondary then secondaryBound
         else if outcome = none then -(singletonSum / 2) else otherBound) := by
      apply Finset.sum_le_sum
      intro outcome _
      apply mul_le_mul_of_nonneg_left
      · cases outcome with
        | none =>
          simp only [quittingTerminalOutcomeReward, reduceCtorEq,
            if_false, if_true, Pi.zero_apply]
          ring_nf
          exact le_rfl
        | some terminal =>
          by_cases hp : terminal = primary
          · subst terminal
            simp only [quittingTerminalOutcomeReward, Option.some.injEq,
              if_pos]
            dsimp only [singletonSum]
            unfold quittingTwoCoordinateAverageSurplus at hprimary
            linarith
          by_cases hs : terminal = secondary
          · subst terminal
            simp only [quittingTerminalOutcomeReward, Option.some.injEq,
              if_neg hne.symm, if_pos]
            dsimp only [singletonSum]
            unfold quittingTwoCoordinateAverageSurplus at hsecondary
            linarith
          · simp only [quittingTerminalOutcomeReward, Option.some.injEq,
              if_neg hp, if_neg hs, Option.some_ne_none, if_false]
            dsimp only [singletonSum]
            have hbound := hother terminal hp hs
            unfold quittingTwoCoordinateAverageSurplus at hbound
            linarith
      · exact (quittingTerminalOutcomeMass_mem_stdSimplex reward profile).1 outcome
    _ = primaryBound * mass (some primary) + secondaryBound * mass (some secondary) +
        otherBound * (1 - mass (some primary) - mass (some secondary) - mass none) -
          (singletonSum / 2) * mass none := by
      classical
      calc
        _ = ∑ outcome, (mass outcome * otherBound +
            (if outcome = some primary then
              mass outcome * (primaryBound - otherBound) else 0) +
            (if outcome = some secondary then
              mass outcome * (secondaryBound - otherBound) else 0) +
            (if outcome = none then
              mass outcome * (-(singletonSum / 2) - otherBound) else 0)) := by
                apply Finset.sum_congr rfl
                intro outcome _
                split_ifs with hp hs hn
                all_goals try { subst outcome; simp_all }
                all_goals ring
        _ = _ := by
          simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ,
            if_true]
          rw [← Finset.sum_mul, htotal]
          ring

end GameTheory
