import UniformEquilibrium.Quitting.Root.SequencePayoff
import UniformEquilibrium.Quitting.Stationary.LiveMass

/-!
# A terminally silent prefix for a quitting root sequence

This low module contains only the root-word and canonical-profile mechanics
of prefixing one deterministic all-Continue row.
-/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Prefix one deterministic all-Continue row to a root word. -/
def quittingSilentPrefixRoots (roots : ℕ → ι → PMF Bool) :
    ℕ → ι → PMF Bool
  | 0 => quittingAllContinueRoot
  | step + 1 => roots step

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem quittingSilentPrefixRoots_zero (roots : ℕ → ι → PMF Bool) :
    quittingSilentPrefixRoots roots 0 = quittingAllContinueRoot := rfl

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem quittingSilentPrefixRoots_succ
    (roots : ℕ → ι → PMF Bool) (step : ℕ) :
    quittingSilentPrefixRoots roots (step + 1) = roots step := rfl

omit [DecidableEq ι] in
/-- Every suffix after the silent row is the corresponding original suffix. -/
theorem quittingRootSequenceProfile_silentPrefix_succ
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (start : ℕ) :
    quittingRootSequenceProfile reward (quittingSilentPrefixRoots roots)
        (start + 1) =
      quittingRootSequenceProfile reward roots start := by
  funext player time history
  show quittingSilentPrefixRoots roots (start + 1 + time) player =
    roots (start + time) player
  rw [show start + 1 + time = start + time + 1 by omega]
  rfl

end GameTheory
