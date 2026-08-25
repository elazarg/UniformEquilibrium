/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Terminal.PassivePlayerPadding

/-!
# Canonical extrema for passive-player padding

Finite maxima package the sharp coordinate intervals and their largest width.
The resulting theorem is the literal extrema form of quantitative passive
padding.
-/

noncomputable section

namespace GameTheory

open StochasticGame

variable {I J : Type} [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J]

/-- Canonical upper endpoint: the maximum of zero and every terminal reward
coordinate. -/
def quittingPassivePaddingUpperEndpoint [Nonempty I]
    (reward : {S : Finset I // S.Nonempty} → Payoff I) (who : I) : ℝ :=
  let owner := Classical.choice (inferInstance : Nonempty I)
  let terminal : {S : Finset I // S.Nonempty} :=
    ⟨{owner}, Finset.singleton_nonempty owner⟩
  Finset.univ.sup' ⟨terminal, Finset.mem_univ terminal⟩
    (fun outcome => max 0 (reward outcome who))

/-- Canonical lower endpoint: the minimum of zero and every terminal reward
coordinate. -/
def quittingPassivePaddingLowerEndpoint [Nonempty I]
    (reward : {S : Finset I // S.Nonempty} → Payoff I) (who : I) : ℝ :=
  let owner := Classical.choice (inferInstance : Nonempty I)
  let terminal : {S : Finset I // S.Nonempty} :=
    ⟨{owner}, Finset.singleton_nonempty owner⟩
  Neg.neg (Finset.univ.sup' ⟨terminal, Finset.mem_univ terminal⟩
    (fun outcome => max 0 (-reward outcome who)))

/-- Canonical coordinate oscillation including the zero payoff of Never. -/
def quittingPassivePaddingCoordinateWidth [Nonempty I]
    (reward : {S : Finset I // S.Nonempty} → Payoff I) (who : I) : ℝ :=
  quittingPassivePaddingUpperEndpoint reward who -
    quittingPassivePaddingLowerEndpoint reward who

/-- Largest canonical coordinate oscillation. -/
def quittingPassivePaddingWidth [Nonempty I]
    (reward : {S : Finset I // S.Nonempty} → Payoff I) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (quittingPassivePaddingCoordinateWidth reward)

omit [DecidableEq I] in
theorem quittingPassivePaddingLowerEndpoint_nonpos [Nonempty I]
    (reward : {S : Finset I // S.Nonempty} → Payoff I) (who : I) :
    quittingPassivePaddingLowerEndpoint reward who ≤ 0 := by
  unfold quittingPassivePaddingLowerEndpoint
  let terminal : {S : Finset I // S.Nonempty} :=
    ⟨{Classical.choice (inferInstance : Nonempty I)},
      Finset.singleton_nonempty _⟩
  have hle := Finset.le_sup'
    (fun outcome : {S : Finset I // S.Nonempty} =>
      max 0 (-reward outcome who))
    (Finset.mem_univ terminal)
  have hnonneg : 0 ≤ max 0 (-reward terminal who) := le_max_left _ _
  linarith

omit [DecidableEq I] in
theorem quittingPassivePaddingUpperEndpoint_nonneg [Nonempty I]
    (reward : {S : Finset I // S.Nonempty} → Payoff I) (who : I) :
    0 ≤ quittingPassivePaddingUpperEndpoint reward who := by
  unfold quittingPassivePaddingUpperEndpoint
  let terminal : {S : Finset I // S.Nonempty} :=
    ⟨{Classical.choice (inferInstance : Nonempty I)},
      Finset.singleton_nonempty _⟩
  exact (le_max_left (0 : ℝ) (reward terminal who)).trans
    (Finset.le_sup' (fun outcome => max 0 (reward outcome who))
      (Finset.mem_univ terminal))

omit [DecidableEq I] in
theorem quittingPassivePaddingReward_mem_canonicalInterval [Nonempty I]
    (reward : {S : Finset I // S.Nonempty} → Payoff I)
    (terminal : {S : Finset I // S.Nonempty}) (who : I) :
    reward terminal who ∈ Set.Icc
      (quittingPassivePaddingLowerEndpoint reward who)
      (quittingPassivePaddingUpperEndpoint reward who) := by
  constructor
  · unfold quittingPassivePaddingLowerEndpoint
    have hle := Finset.le_sup'
      (fun outcome : {S : Finset I // S.Nonempty} =>
        max 0 (-reward outcome who)) (Finset.mem_univ terminal)
    linarith [le_max_right (0 : ℝ) (-reward terminal who)]
  · unfold quittingPassivePaddingUpperEndpoint
    exact (le_max_right (0 : ℝ) (reward terminal who)).trans
      (Finset.le_sup' (fun outcome => max 0 (reward outcome who))
        (Finset.mem_univ terminal))

omit [DecidableEq I] in
theorem quittingPassivePaddingCoordinateWidth_le_width [Nonempty I]
    (reward : {S : Finset I // S.Nonempty} → Payoff I) (who : I) :
    quittingPassivePaddingCoordinateWidth reward who ≤
      quittingPassivePaddingWidth reward := by
  unfold quittingPassivePaddingWidth
  exact Finset.le_sup' _ (Finset.mem_univ who)

omit [DecidableEq I] in
theorem quittingPassivePaddingWidth_nonneg [Nonempty I]
    (reward : {S : Finset I // S.Nonempty} → Payoff I) :
    0 ≤ quittingPassivePaddingWidth reward := by
  let who := Classical.choice (inferInstance : Nonempty I)
  exact (sub_nonneg.mpr <| (quittingPassivePaddingLowerEndpoint_nonpos
    reward who).trans (quittingPassivePaddingUpperEndpoint_nonneg reward who))
    |>.trans (quittingPassivePaddingCoordinateWidth_le_width reward who)

/-- Sharp canonical-extrema form of quantitative passive-player padding. -/
theorem HasTerminalExploitabilityGap.passivePlayerPadding_canonical
    [Nonempty I] [Nonempty J]
    (reward : {S : Finset I // S.Nonempty} → Payoff I)
    {penalty gap : ℝ} (hpenalty : 0 < penalty)
    (hexploit : HasTerminalExploitabilityGap reward gap) :
    HasTerminalExploitabilityGap
      (quittingPassivePaddingReward (J := J) reward
        (quittingPassivePaddingUpperEndpoint reward) penalty)
      (penalty / (penalty + (Fintype.card J : ℝ) *
        quittingPassivePaddingWidth reward) * gap) := by
  exact @HasTerminalExploitabilityGap.passivePlayerPadding
    I J _ _ _ _ _ reward
    (quittingPassivePaddingLowerEndpoint reward)
    (quittingPassivePaddingUpperEndpoint reward)
    penalty (quittingPassivePaddingWidth reward) gap
    hpenalty (quittingPassivePaddingWidth_nonneg reward)
    (quittingPassivePaddingLowerEndpoint_nonpos reward)
    (quittingPassivePaddingUpperEndpoint_nonneg reward)
    (quittingPassivePaddingReward_mem_canonicalInterval reward)
    (quittingPassivePaddingCoordinateWidth_le_width reward) hexploit

end GameTheory
