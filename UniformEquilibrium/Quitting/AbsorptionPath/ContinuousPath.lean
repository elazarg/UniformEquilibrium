/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.ExistenceBranches
import UniformEquilibrium.Quitting.Root.OpponentCoalitionMass

/-!
# Continuous absorption paths for quitting games

This module is the reusable game-semantic form of Ashkenazi--Golan--Krasikov--
Rainer--Solan's absorption paths.  A path records cumulative absorption mass
for every nonempty quitting coalition.  The four absorption-path conditions
control total mass, flat intervals, jumps induced by product rows, and
singleton support on continuous portions.  Sequential perfection compares
the induced continuation payoff with each player's solo-quitting payoff.
-/

noncomputable section

namespace GameTheory.QuittingAbsorptionPath

open Filter Set
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A coordinatewise nondecreasing cadlag path of coalition masses on
`[0,1]`.  The carrier is `ℝ` so ordinary one-sided filters can be used. -/
structure CadlagPath where
  value : ℝ → {S : Finset ι // S.Nonempty} → ℝ
  leftValue : ℝ → {S : Finset ι // S.Nonempty} → ℝ
  value_mem : ∀ t ∈ Icc (0 : ℝ) 1, ∀ a, 0 ≤ value t a ∧ value t a ≤ 1
  monotone : ∀ a, MonotoneOn (fun t => value t a) (Icc 0 1)
  right_continuous : ∀ a t, t ∈ Icc (0 : ℝ) 1 →
    Tendsto (fun s => value s a) (nhdsWithin t (Icc t 1)) (𝓝 (value t a))
  left_limit : ∀ a t, t ∈ Icc (0 : ℝ) 1 →
    Tendsto (fun s => value s a) (nhdsWithin t (Icc 0 t \ {t}))
      (𝓝 (leftValue t a))
  left_zero : ∀ a, leftValue 0 a = 0

/-- Total cumulative absorption mass at a time. -/
def pathTotal (path : CadlagPath (ι := ι)) (t : ℝ) : ℝ :=
  ∑ a, path.value t a

/-- The jump in one coalition coordinate at a time. -/
def pathJump (path : CadlagPath (ι := ι)) (t : ℝ)
    (a : {S : Finset ι // S.Nonempty}) : ℝ :=
  path.value t a - path.leftValue t a

/-- Times at which cumulative absorption mass equals the clock. -/
def pathTimes (path : CadlagPath (ι := ι)) : Set ℝ :=
  {t | t ∈ Icc 0 1 ∧ pathTotal path t = t}

/-- Times at which some coalition coordinate jumps. -/
def pathJumps (path : CadlagPath (ι := ι)) : Set ℝ :=
  {t | t ∈ Icc 0 1 ∧ ∃ a, pathJump path t a ≠ 0}

/-- Lower right derivative of one coalition coordinate. -/
def pathRightDerivative (path : CadlagPath (ι := ι)) (t : ℝ)
    (a : {S : Finset ι // S.Nonempty}) : ℝ :=
  Filter.liminf (fun s => (path.value s a - path.value t a) / (s - t))
    (nhdsWithin t (Ioo t 1))

/-- On a component outside the jump and clock sets, total mass is fixed at
the component's right endpoint. -/
def AbsorptionPathA2 (path : CadlagPath (ι := ι)) : Prop :=
  ∀ t ∈ Icc (0 : ℝ) 1 \ (pathJumps path ∪ pathTimes path),
    ∀ s ∈ connectedComponentIn
      (Icc 0 1 \ (pathJumps path ∪ pathTimes path)) t,
      pathTotal path s = sSup
        (connectedComponentIn (Icc 0 1 \ (pathJumps path ∪ pathTimes path)) t)

/-- The four defining conditions for an absorption path. -/
def IsAbsorptionPath (path : CadlagPath (ι := ι)) : Prop :=
  (∀ t ∈ Icc (0 : ℝ) 1, t ≤ pathTotal path t) ∧ AbsorptionPathA2 path ∧
    (∀ t ∈ pathJumps path, ∃ ξ : ι → PMF Bool, ∀ a,
      pathJump path t a / (1 - t) = quittingRootCoalitionMass ξ a.1) ∧
    (∀ t ∈ pathTimes path, t ≠ 1 → ∀ a,
      pathRightDerivative path t a ≠ 0 → a.1.card = 1)

/-- An absorption path, bundled with its four defining conditions. -/
abbrev AbsorptionPath := {path : CadlagPath (ι := ι) // IsAbsorptionPath path}

/-- Continuation payoff induced by the mass remaining after time `t`. -/
def absorptionPathPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (path : AbsorptionPath (ι := ι)) (t : ℝ) : Payoff ι :=
  if t ∈ Icc (0 : ℝ) 1 then
    if pathTotal path.1 t < 1 then
      fun who => (∑ a, (path.1.value 1 a - path.1.value t a) * reward a who) /
        (1 - pathTotal path.1 t)
    else 0
  else 0

/-- A continuous absorption path is one whose total mass equals the clock
throughout `[0,1]`. -/
def IsContinuousAbsorptionPath (path : AbsorptionPath (ι := ι)) : Prop :=
  pathTimes path.1 = Icc 0 1

/-- A product row realizes the normalized jump of an absorption path. -/
def AbsorptionPathJumpRelation (path : AbsorptionPath (ι := ι))
    (t : ℝ) (ξ : ι → PMF Bool) : Prop :=
  ∀ a, pathJump path.1 t a / (1 - t) = quittingRootCoalitionMass ξ a.1

/-- One product-row witness selected from the path at each jump time. -/
def absorptionPathJumpRoot
    (path : AbsorptionPath (ι := ι)) (t : ℝ) : ι → PMF Bool := by
  classical
  exact if ht : t ∈ pathJumps path.1 then
      Classical.choose (path.property.2.2.1 t ht)
    else
      fun _ => PMF.pure false

/-- The selected jump row realizes the normalized jump. -/
theorem absorptionPathJumpRoot_relation
    (path : AbsorptionPath (ι := ι)) {t : ℝ} (ht : t ∈ pathJumps path.1) :
    AbsorptionPathJumpRelation path t (absorptionPathJumpRoot path t) := by
  simp only [absorptionPathJumpRoot, dif_pos ht]
  exact Classical.choose_spec (path.property.2.2.1 t ht)

/-- Sequential `ε`-perfection for one player along an absorption path. -/
def IsPlayerSequentiallyPerfectAbsorptionPath
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (path : AbsorptionPath (ι := ι)) (who : ι) (ε : ℝ) : Prop :=
  (∀ t ∈ pathJumps path.1, pathTotal path.1 t < 1 →
      QuittingPlayerRowεPerfect reward (absorptionPathPayoff reward path t)
        (absorptionPathJumpRoot path t) who ε) ∧
    (∀ t ∈ pathTimes path.1, t ≠ 1 →
      reward ⟨{who}, Finset.singleton_nonempty who⟩ who - ε ≤
        absorptionPathPayoff reward path t who ∧
      (pathRightDerivative path.1 t
          ⟨{who}, Finset.singleton_nonempty who⟩ > 0 →
        absorptionPathPayoff reward path t who ≤
          reward ⟨{who}, Finset.singleton_nonempty who⟩ who + ε))

/-- Every player is sequentially `ε`-perfect along the absorption path. -/
def IsSequentiallyPerfectAbsorptionPath
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (path : AbsorptionPath (ι := ι)) (ε : ℝ) : Prop :=
  ∀ who, IsPlayerSequentiallyPerfectAbsorptionPath reward path who ε

end GameTheory.QuittingAbsorptionPath
