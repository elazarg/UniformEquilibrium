import UniformEquilibrium.Quitting.Terminal.PayoffExclusionStrictDeficitStep
import UniformEquilibrium.Quitting.Root.FiniteWordSemanticSplice
import UniformEquilibrium.Quitting.Root.NashExistence

/-! # Literal finite words selected under strict singleton payoff exclusion -/

noncomputable section

namespace GameTheory

open Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def HasQuittingFiniteWordStrictSingletonDeficit
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (gap : ℝ) : Prop :=
  ∀ roots : List (ι → PMF Bool), ∃ who,
    quittingTerminalPayoff reward
        (quittingLiteralRootStackProfile reward roots
          (quittingAlwaysContinueProfile reward)) who ≤
      reward (quittingSingletonTerminal who) who - gap

def quittingStrictDeficitAuxiliary
    (pair : QuittingTerminalSemanticPair ι) (gap : ℝ) : Payoff ι :=
  pair.2 - fun _ => quittingTerminalSemanticDebtSum pair -
    min (quittingTerminalSemanticDebtSum pair) (gap / 2)

def quittingStrictDeficitSelectedRoot
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι) (gap : ℝ) : ι → PMF Bool :=
  Classical.choose (exists_isZeroQuittingRootNash
    (reward := reward) (quittingStrictDeficitAuxiliary pair gap))

theorem quittingStrictDeficitSelectedRoot_isZeroNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι) (gap : ℝ) :
    IsεQuittingRootNash reward (quittingStrictDeficitAuxiliary pair gap) 0
      (quittingStrictDeficitSelectedRoot reward pair gap) :=
  Classical.choose_spec (exists_isZeroQuittingRootNash
    (reward := reward) (quittingStrictDeficitAuxiliary pair gap))

def quittingStrictDeficitExactWords
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (gap : ℝ) :
    ℕ → List (ι → PMF Bool)
  | 0 => []
  | time + 1 =>
      let old := quittingStrictDeficitExactWords reward gap time
      let profile := quittingLiteralRootStackProfile reward old
        (quittingAlwaysContinueProfile reward)
      let pair := quittingTerminalSemanticPair reward profile
      quittingStrictDeficitSelectedRoot reward pair gap :: old

theorem quittingStrictDeficitExactWords_succ
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (gap : ℝ) (time : ℕ) :
    quittingStrictDeficitExactWords reward gap (time + 1) =
      quittingStrictDeficitSelectedRoot reward
          (quittingTerminalSemanticPair reward
            (quittingLiteralRootStackProfile reward
              (quittingStrictDeficitExactWords reward gap time)
              (quittingAlwaysContinueProfile reward))) gap ::
        quittingStrictDeficitExactWords reward gap time := rfl

/-- Each selected row prefixes the preceding literal word and obeys the
strict-deficit absorption and total-debt contraction. -/
theorem quittingStrictDeficitExactWords_step
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {M gap : ℝ} (hgap : 0 < gap)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hdeficit : HasQuittingFiniteWordStrictSingletonDeficit reward gap)
    (time : ℕ) :
    let old := quittingStrictDeficitExactWords reward gap time
    let oldProfile := quittingLiteralRootStackProfile reward old
      (quittingAlwaysContinueProfile reward)
    let pair := quittingTerminalSemanticPair reward oldProfile
    let root := quittingStrictDeficitSelectedRoot reward pair gap
    gap / (4 * M + gap) ≤ quittingRootAbsorptionMass root ∧
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward
            (quittingLiteralRootStackProfile reward (root :: old)
              (quittingAlwaysContinueProfile reward))) ≤
        quittingTerminalSemanticDebtSum pair -
          gap / (4 * M + gap) *
            min (quittingTerminalSemanticDebtSum pair) (gap / 2) := by
  dsimp only
  let old := quittingStrictDeficitExactWords reward gap time
  let oldProfile := quittingLiteralRootStackProfile reward old
    (quittingAlwaysContinueProfile reward)
  let pair := quittingTerminalSemanticPair reward oldProfile
  let root := quittingStrictDeficitSelectedRoot reward pair gap
  obtain ⟨who, hwho⟩ := hdeficit old
  have hpair : pair ∈ quittingTerminalSemanticCarrier reward :=
    subset_closure ⟨oldProfile, rfl⟩
  have hnash : IsεQuittingRootNash reward
      (quittingStrictDeficitAuxiliary pair gap) 0 root :=
    quittingStrictDeficitSelectedRoot_isZeroNash reward pair gap
  have hstep := strictDeficit_exactAuxiliaryPrefix_absorption_and_debt
    reward pair root who hgap hreward hpair hwho
      (by simpa [quittingStrictDeficitAuxiliary] using hnash)
  have hsemantic : quittingTerminalSemanticPair reward
      (quittingLiteralRootStackProfile reward (root :: old)
        (quittingAlwaysContinueProfile reward)) =
      quittingTerminalSemanticPrefix reward root pair := by
    rw [quittingLiteralRootStackProfile_cons,
      quittingTerminalSemanticPair_rootThenContinuation]
  constructor
  · exact hstep.1
  · rw [hsemantic]
    exact hstep.2

end GameTheory
