import UniformEquilibrium.Quitting.Terminal.GroupExclusionExactPrefixStep
import UniformEquilibrium.Quitting.Root.FiniteWordSemanticSplice
import UniformEquilibrium.Quitting.Root.NashExistence

noncomputable section

namespace GameTheory

open Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Every literal finite word admits a probability weight whose coordinates
are bounded by one fixed concentration constant and which excludes positive
weighted singleton surplus. -/
def HasQuittingFiniteWordNonconcentratedGroupExclusion
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (beta : ℝ) : Prop :=
  ∀ roots : List (ι → PMF Bool), ∃ weight : ι → ℝ,
    (∀ who, 0 ≤ weight who) ∧
    (∑ who, weight who = 1) ∧
    (∀ who, weight who ≤ beta) ∧
    ∑ who, weight who *
      (quittingTerminalPayoff reward
          (quittingLiteralRootStackProfile reward roots
            (quittingAlwaysContinueProfile reward)) who -
        reward (quittingSingletonTerminal who) who) ≤ 0

def quittingGroupExclusionAuxiliary
    (pair : QuittingTerminalSemanticPair ι) (beta : ℝ) : Payoff ι :=
  pair.2 - fun _ => quittingTerminalSemanticDebtSum pair -
    (1 - beta) * quittingTerminalSemanticDebtSum pair / 2

def quittingGroupExclusionSelectedRoot
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι) (beta : ℝ) : ι → PMF Bool :=
  Classical.choose (exists_isZeroQuittingRootNash
    (reward := reward) (quittingGroupExclusionAuxiliary pair beta))

theorem quittingGroupExclusionSelectedRoot_isZeroNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι) (beta : ℝ) :
    IsεQuittingRootNash reward (quittingGroupExclusionAuxiliary pair beta) 0
      (quittingGroupExclusionSelectedRoot reward pair beta) :=
  Classical.choose_spec (exists_isZeroQuittingRootNash
    (reward := reward) (quittingGroupExclusionAuxiliary pair beta))

def quittingGroupExclusionExactWords
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (beta : ℝ) :
    ℕ → List (ι → PMF Bool)
  | 0 => []
  | time + 1 =>
      let old := quittingGroupExclusionExactWords reward beta time
      let profile := quittingLiteralRootStackProfile reward old
        (quittingAlwaysContinueProfile reward)
      let pair := quittingTerminalSemanticPair reward profile
      quittingGroupExclusionSelectedRoot reward pair beta :: old

@[simp] theorem quittingGroupExclusionExactWords_succ
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (beta : ℝ) (time : ℕ) :
    quittingGroupExclusionExactWords reward beta (time + 1) =
      quittingGroupExclusionSelectedRoot reward
          (quittingTerminalSemanticPair reward
            (quittingLiteralRootStackProfile reward
              (quittingGroupExclusionExactWords reward beta time)
              (quittingAlwaysContinueProfile reward))) beta ::
        quittingGroupExclusionExactWords reward beta time := rfl

/-- Each positive-debt generated word receives its possibly profile-dependent
exclusion weight and obeys the reciprocal-scale debt decrease. -/
theorem quittingGroupExclusionExactWords_step
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {M beta : ℝ} (hbeta : beta < 1)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hexclusion : HasQuittingFiniteWordNonconcentratedGroupExclusion reward beta)
    (time : ℕ)
    (hpositive : 0 < quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward
        (quittingLiteralRootStackProfile reward
          (quittingGroupExclusionExactWords reward beta time)
          (quittingAlwaysContinueProfile reward)))) :
    let old := quittingGroupExclusionExactWords reward beta time
    let profile := quittingLiteralRootStackProfile reward old
      (quittingAlwaysContinueProfile reward)
    let pair := quittingTerminalSemanticPair reward profile
    let root := quittingGroupExclusionSelectedRoot reward pair beta
    quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward
          (quittingLiteralRootStackProfile reward (root :: old)
            (quittingAlwaysContinueProfile reward))) ≤
      quittingTerminalSemanticDebtSum pair -
        (1 - beta) ^ 2 * quittingTerminalSemanticDebtSum pair ^ 2 /
          (8 * M + 2 * (1 - beta) * quittingTerminalSemanticDebtSum pair) := by
  dsimp only
  let old := quittingGroupExclusionExactWords reward beta time
  let profile := quittingLiteralRootStackProfile reward old
    (quittingAlwaysContinueProfile reward)
  let pair := quittingTerminalSemanticPair reward profile
  let root := quittingGroupExclusionSelectedRoot reward pair beta
  obtain ⟨weight, hweight, hsum, hmax, hexclude⟩ := hexclusion old
  have hpair : pair ∈ quittingTerminalSemanticCarrier reward :=
    subset_closure ⟨profile, rfl⟩
  have hnash := quittingGroupExclusionSelectedRoot_isZeroNash reward pair beta
  have hstep := nonconcentratedWeight_exactAuxiliaryPrefix_debtDrop
    reward pair root weight hreward hpair hpositive hbeta hweight hsum hmax
      hexclude (by simpa [quittingGroupExclusionAuxiliary] using hnash)
  have hsemantic : quittingTerminalSemanticPair reward
      (quittingLiteralRootStackProfile reward (root :: old)
        (quittingAlwaysContinueProfile reward)) =
      quittingTerminalSemanticPrefix reward root pair := by
    rw [quittingLiteralRootStackProfile_cons,
      quittingTerminalSemanticPair_rootThenContinuation]
  rw [hsemantic]
  exact hstep

end GameTheory
