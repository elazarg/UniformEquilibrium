import Literature.Sorin1986
import UniformEquilibrium.ProofView.Concepts.Existence.NashExistenceMixed

noncomputable section

namespace Literature.Sorin1986

open GameTheory Set Filter
open scoped BigOperators Topology

namespace CompactNash

/-- Total mass of a finite weighted family. -/
def listWeight {S : Type*} (xs : List (ℝ × S)) : ℝ :=
  (xs.map Prod.fst).sum

@[simp] theorem listWeight_nil {S : Type*} :
    listWeight ([] : List (ℝ × S)) = 0 := rfl

@[simp] theorem listWeight_cons {S : Type*} (p : ℝ × S)
    (xs : List (ℝ × S)) :
    listWeight (p :: xs) = p.1 + listWeight xs := by
  simp [listWeight]

/-- A finite weighted family can be folded using only binary convex mixing.
The zero-total branch is irrelevant under probability weights. -/
def weightedPoint {S : Type*} (mix : ℝ → S → S → S) (fallback : S) :
    List (ℝ × S) → S
  | [] => fallback
  | p :: xs =>
      let total := p.1 + listWeight xs
      if total = 0 then fallback
      else mix (p.1 / total) p.2 (weightedPoint mix fallback xs)

@[simp] theorem weightedPoint_nil {S : Type*}
    (mix : ℝ → S → S → S) (fallback : S) :
    weightedPoint mix fallback [] = fallback := rfl

@[simp] theorem weightedPoint_cons {S : Type*}
    (mix : ℝ → S → S → S) (fallback : S)
    (p : ℝ × S) (xs : List (ℝ × S)) :
    weightedPoint mix fallback (p :: xs) =
      if p.1 + listWeight xs = 0 then fallback
      else mix (p.1 / (p.1 + listWeight xs)) p.2
        (weightedPoint mix fallback xs) := rfl

private theorem listWeight_nonneg {S : Type*} (xs : List (ℝ × S))
    (h : ∀ p ∈ xs, 0 ≤ p.1) : 0 ≤ listWeight xs := by
  induction xs with
  | nil => simp
  | cons p xs ih =>
      have hp : 0 ≤ p.1 := h p (by simp)
      have hxs : ∀ q ∈ xs, 0 ≤ q.1 := by
        intro q hq
        exact h q (by simp [hq])
      simpa using add_nonneg hp (ih hxs)

/-- Folding realizes the normalized weighted average of every function that
is affine along the supplied binary mixtures.  The mass-multiplied form also
covers zero total mass without a division convention. -/
theorem weightedPoint_spec {S : Type*}
    (mix : ℝ → S → S → S) (fallback : S) (f : S → ℝ)
    (haffine : ∀ t x y, 0 ≤ t → t ≤ 1 →
      f (mix t x y) = t * f x + (1 - t) * f y)
    (xs : List (ℝ × S))
    (hnonneg : ∀ p ∈ xs, 0 ≤ p.1) :
    listWeight xs * f (weightedPoint mix fallback xs) =
      (xs.map fun p => p.1 * f p.2).sum := by
  induction xs with
  | nil => simp
  | cons p xs ih =>
      rcases p with ⟨w, x⟩
      have hw : 0 ≤ w := hnonneg (w, x) (by simp)
      have hxs : ∀ q ∈ xs, 0 ≤ q.1 := by
        intro q hq
        exact hnonneg q (by simp [hq])
      have hW : 0 ≤ listWeight xs := listWeight_nonneg xs hxs
      have ih' := ih hxs
      simp only [listWeight_cons, weightedPoint_cons, Prod.fst, Prod.snd,
        List.map_cons, List.sum_cons]
      by_cases htotal : w + listWeight xs = 0
      · rw [if_pos htotal, htotal, zero_mul]
        have hw0 : w = 0 := by linarith
        have hW0 : listWeight xs = 0 := by linarith
        rw [hw0, zero_mul, zero_add, ← ih', hW0, zero_mul]
      · rw [if_neg htotal]
        have htotal_pos : 0 < w + listWeight xs :=
          lt_of_le_of_ne (add_nonneg hw hW) (Ne.symm htotal)
        have hq0 : 0 ≤ w / (w + listWeight xs) :=
          div_nonneg hw htotal_pos.le
        have hq1 : w / (w + listWeight xs) ≤ 1 :=
          (div_le_one htotal_pos).2 (by linarith)
        rw [haffine _ _ _ hq0 hq1, ← ih']
        field_simp [htotal]
        <;> ring

/-- Weighted entries associated with a finite probability law. -/
def probabilityEntries {α S : Type*} [Fintype α]
    (μ : PMF α) (point : α → S) : List (ℝ × S) :=
  (Finset.univ.toList.map fun a => ((μ a).toReal, point a))

private theorem probabilityEntries_nonneg {α S : Type*} [Fintype α]
    (μ : PMF α) (point : α → S) :
    ∀ p ∈ probabilityEntries μ point, 0 ≤ p.1 := by
  classical
  intro p hp
  simp only [probabilityEntries, List.mem_map] at hp
  obtain ⟨a, _ha, rfl⟩ := hp
  exact ENNReal.toReal_nonneg

private theorem listWeight_probabilityEntries {α S : Type*} [Fintype α]
    (μ : PMF α) (point : α → S) :
    listWeight (probabilityEntries μ point) = 1 := by
  classical
  simp [listWeight, probabilityEntries,
    Math.Probability.pmf_toReal_sum_one]

/-- Realize a finite mixed strategy inside one compact game's convex carrier. -/
def barycenter (G : CompactContinuousGame) (who : G.Player)
    {α : Type*} [Fintype α] (μ : PMF α)
    (point : α → G.Strategy who) : G.Strategy who :=
  weightedPoint (G.mix who)
    (Classical.choice (inferInstance : Nonempty (G.Strategy who)))
    (probabilityEntries μ point)

/-- The realized finite mixture has exactly the expected payoff against every
fixed opponents' profile, for every observer. -/
theorem payoff_update_barycenter (G : CompactContinuousGame)
    (profile : ∀ i, G.Strategy i) (who observer : G.Player)
    {α : Type*} [Fintype α] (μ : PMF α)
    (point : α → G.Strategy who) :
    G.payoff (Function.update profile who (barycenter G who μ point)) observer =
      ∑ a : α, (μ a).toReal *
        G.payoff (Function.update profile who (point a)) observer := by
  classical
  let fallback := Classical.choice (inferInstance : Nonempty (G.Strategy who))
  let f : G.Strategy who → ℝ := fun strategy =>
    G.payoff (Function.update profile who strategy) observer
  have hspec := weightedPoint_spec (G.mix who) fallback f
    (fun t x y ht0 ht1 => G.payoffAffine profile who x y t observer ht0 ht1)
    (probabilityEntries μ point)
    (probabilityEntries_nonneg μ point)
  have hmass := listWeight_probabilityEntries μ point
  rw [hmass, one_mul] at hspec
  simpa [barycenter, fallback, f, probabilityEntries] using hspec

end CompactNash

end Literature.Sorin1986
