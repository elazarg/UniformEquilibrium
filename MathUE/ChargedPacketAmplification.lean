/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.ChargedPathExecution

/-!
# Amplification by uniformly available charged packets

This is the sound abstract core of the charged-packet argument.  A packet is
an actual finite path, so concatenation never introduces a source seam.  Its
path stays in a specified tube, its endpoint height has a one-packet drift
bound, and its charge is bounded below by a fixed multiple of the packet
scale.

The theorem does not construct packets, identify charge with any game payoff,
or infer a circulation from numerical residual columns.  Those are separate
producer obligations.
-/

noncomputable section

namespace Math.ChargedPathBudget.ChargedRelation

open Set

universe u v

variable {State : Type u} {Edge : Type v}

namespace Path

variable {R : ChargedRelation State Edge}

/-- Every vertex of a finite path lies in `tube`. -/
def StaysInTube (tube : Set State) :
    {s t : State} → R.Path s t → Prop
  | _, _, .nil s => s ∈ tube
  | _, _, .cons e rest => R.src e ∈ tube ∧ StaysInTube tube rest

@[simp] theorem staysInTube_nil (tube : Set State) (s : State) :
    StaysInTube (R := R) tube (Path.nil s) ↔ s ∈ tube := Iff.rfl

@[simp] theorem staysInTube_cons (tube : Set State) (e : Edge)
    {t : State} (rest : R.Path (R.tgt e) t) :
    StaysInTube tube (Path.cons e rest) ↔
      R.src e ∈ tube ∧ StaysInTube tube rest := Iff.rfl

theorem staysInTube_append (tube : Set State)
    {s t w : State} (p : R.Path s t) (q : R.Path t w)
    (hp : StaysInTube tube p) (hq : StaysInTube tube q) :
    StaysInTube tube (p.append q) := by
  induction p with
  | nil s => simpa [Path.append] using hq
  | cons e rest ih =>
      exact ⟨hp.1, ih q hp.2 hq⟩

end Path

/-- One legal charged packet at scale `h`. -/
structure TubePacket
    (R : ChargedRelation State Edge) (tube : Set State)
    (height : State → ℝ) (h omega c : ℝ)
    {source target : State} where
  path : R.Path source target
  stays : Path.StaysInTube tube path
  target_mem : target ∈ tube
  height_drift : height target ≤ height source + h * omega
  charge_lower : c * h ≤ path.chargeSum

/-- Repeated availability of a packet from every reachable tube state
produces a finite path of arbitrarily large charge. -/
theorem exists_path_charge_gt_of_uniform_tube_packet
    (R : ChargedRelation State Edge) (tube : Set State)
    (height : State → ℝ) (start : State) {h omega c : ℝ}
    (hstart : start ∈ tube) (hh : 0 < h) (homega : 0 ≤ omega)
    (hc : 0 < c)
    (packet : ∀ state, R.Reaches start state → state ∈ tube →
      ∃ target, Nonempty (TubePacket R tube height h omega c
        (source := state) (target := target))) :
    ∀ bound : ℝ, ∃ target, ∃ path : R.Path start target,
      bound < path.chargeSum := by
  have hscale : 0 < c * h := mul_pos hc hh
  have hdelta : 0 ≤ h * omega := mul_nonneg hh.le homega
  have hbuild : ∀ n : ℕ, ∃ (state : State) (path : R.Path start state),
      Path.StaysInTube tube path ∧ state ∈ tube ∧
        height state ≤ height start + (n : ℝ) * (h * omega) ∧
        (n : ℝ) * (c * h) ≤ path.chargeSum := by
    intro n
    induction n with
    | zero =>
        exact ⟨start, Path.nil start, hstart, hstart, by simp, by simp⟩
    | succ n ih =>
        obtain ⟨state, path, hpath, hstate, hheight, hcharge⟩ := ih
        obtain ⟨nextState, ⟨next⟩⟩ := packet state ⟨path⟩ hstate
        let joined := path.append next.path
        have hjoinedTube : Path.StaysInTube tube joined :=
          Path.staysInTube_append tube path next.path
            hpath next.stays
        refine ⟨nextState, joined, hjoinedTube, next.target_mem, ?_, ?_⟩
        · have hdrift := next.height_drift
          have hjoinedHeight : height nextState ≤
              height start + (n : ℝ) * (h * omega) + h * omega := by
            calc
              height nextState ≤ height state + h * omega := hdrift
              _ ≤ height start + (n : ℝ) * (h * omega) + h * omega := by
                linarith [hdelta]
          convert hjoinedHeight using 1
          push_cast
          ring
        · rw [Path.chargeSum_append]
          have hpacket := next.charge_lower
          have hnat : (n : ℝ) * (c * h) + c * h =
              ((n + 1 : ℕ) : ℝ) * (c * h) := by
            push_cast
            ring
          rw [← hnat]
          linarith
  intro bound
  obtain ⟨n, hn⟩ := exists_nat_gt (bound / (c * h))
  have hlarge : bound < (n : ℝ) * (c * h) := by
    exact (div_lt_iff₀ hscale).mp hn
  obtain ⟨state, path, -, -, -, hcharge⟩ := hbuild n
  exact ⟨state, path, hlarge.trans_le hcharge⟩

/-- A finite common path-capacity bound is incompatible with uniformly
available positive-charge packets in a reachable tube. -/
theorem not_finite_path_capacity_of_uniform_tube_packet
    (R : ChargedRelation State Edge) (tube : Set State)
    (height : State → ℝ) (start : State) {h omega c C : ℝ}
    (hstart : start ∈ tube) (hh : 0 < h) (homega : 0 ≤ omega)
    (hc : 0 < c)
    (packet : ∀ state, R.Reaches start state → state ∈ tube →
      ∃ target, Nonempty (TubePacket R tube height h omega c
        (source := state) (target := target)))
    (capacity : ∀ {source target : State} (path : R.Path source target),
      path.chargeSum ≤ C) :
    False := by
  obtain ⟨target, path, hpath⟩ :=
    exists_path_charge_gt_of_uniform_tube_packet R tube height start hstart hh
      homega hc packet C
  exact (not_lt_of_ge (capacity path)) hpath

end Math.ChargedPathBudget.ChargedRelation
