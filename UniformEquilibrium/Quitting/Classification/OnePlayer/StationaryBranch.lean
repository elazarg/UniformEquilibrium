/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.ExistenceBranches
import UniformEquilibrium.Quitting.Punishment.OwnerSoloCertification
import UniformEquilibrium.Quitting.Punishment.ZeroSoloDisjunct

/-!
# The stationary classification branch for one-player quitting games

For a unique player, a nonpositive singleton reward makes all-Continue an
exact stationary terminal equilibrium.  A positive singleton reward makes
sure solo quitting an exact stationary terminal equilibrium.  Thus the
stronger AGKRS stationary branch holds, not merely existence of a uniform
payoff.
-/

noncomputable section

namespace GameTheory

open StochasticGame

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Every one-player finite quitting game belongs to the exact stationary
classification branch. -/
theorem quittingStationaryεEquilibriumExistence_onePlayer
    [Unique ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    QuittingStationaryεEquilibriumExistence reward := by
  intro ε hε
  by_cases hsolo : quittingSoloReward reward default default ≤ 0
  · let root : ι → PMF Bool := fun _ ↦ PMF.pure false
    have hzero : IsQuittingZeroSolo reward := by
      intro who
      rw [Unique.eq_default who]
      exact hsolo
    have hnash :=
      isZeroAsymptoticNash_quittingAlwaysContinue_of_zeroSolo reward hzero
    refine ⟨root, ?_⟩
    have hprofile : quittingStationaryProfile reward root =
        quittingAlwaysContinueProfile reward := by
      funext who time history
      rfl
    rw [hprofile]
    exact hnash.mono hε.le
  · have hsoloPositive : 0 < quittingSoloReward reward default default := by
      exact lt_of_not_ge hsolo
    let root : ι → PMF Bool :=
      quittingSoloStationaryRoot (default : ι) (PMF.pure true)
    refine ⟨root, ?_⟩
    have hnash := isεAsymptoticNash_soloStationary_exact
      reward (default : ι) (PMF.pure true) (by simp) hsoloPositive.le
      (fun other hother ↦ False.elim (hother (Unique.eq_default other)))
    exact hnash.mono hε.le

end GameTheory
