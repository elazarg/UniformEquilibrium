/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Probability.Distributions.Uniform

/-!
# One-deviator-robust public randomness from a finite group sum

Two players simultaneously and independently contribute to a public group
element by multiplying an honest uniform draw with an arbitrary (possibly
adversarial) contribution. If one contributor's draw is exactly uniform on a
finite group `G` and independent of the other's, the product is uniform
*regardless* of the other contributor's law -- in either multiplication
order, and even when that other contributor's law is itself the result of
reacting to an independent private signal. This generalizes the two-player
Boolean XOR public coin of
`UniformEquilibrium.Certificates.Public.JointlyControlledPublicXor` (`(ZMod 2, +)`
under the `Bool`/`xor` presentation is the degenerate rank-two case) to an
arbitrary finite group and an arbitrary (not just two-valued) deviator law.

The final section shows this collapses completely once the deviator is
allowed to *observe* the honest draw before playing: a last mover who reacts
to `x` with `y := !x` can force the product to a single fixed outcome with
certainty. This is the sequential/observed counterpart contrasted with the
simultaneous/independent case proved above.

## Main statements

* `map_mul_left_uniform`, `map_mul_right_uniform`: left/right translation of
  the uniform law on `G` by a fixed group element is again uniform.
* `bind_uniform_mul_eq`: honest player on the left, `x ~ uniform`, arbitrary
  independent deviator law `q` for `y`; the product `x * y` is uniform.
* `bind_mul_uniform_eq`: the mirrored honest-right statement.
* `bind_uniform_mul_eq_of_kernel`: the deviator's law may itself be the
  result of reacting to an independent private signal `s ~ ps` through an
  arbitrary kernel `k : S → PMF G`; this is covered by
  `bind_uniform_mul_eq` because `s` (hence `k s`) is drawn independently of
  the honest draw `x`. This is the sense in which `bind_uniform_mul_eq` /
  `bind_mul_uniform_eq` are the strongest *one-shot, simultaneous*
  statements: the genuinely different case is a kernel indexed by the honest
  draw itself, `k : G → PMF G`, which is refuted (not merely left unproved)
  by `lastMover_forces` below.
* `lastMover_forces`: with `G := Bool`, a deviator who *observes* the honest
  draw `x` and replies `y := !x` forces the XOR-product `x ^^ y` to be `true`
  with certainty -- the sequential counterexample to the whole simultaneous
  story.

## Nonclaims

* **Marginal-only.** Every uniformity statement above is about the marginal
  law of the product `x * y`; nothing here says anything about a downstream
  transition/continuation kernel fed by `x * y` together with the individual
  actions. As in `JointPublicXorCoin`'s docstring
  (`UniformEquilibrium.Certificates.Public.JointlyControlledPublicXor`), a transition
  that does not factor through the product can still leak information about
  an individual contributor's draw even though the product marginal is
  perfectly uniform.
* **No persistent secrecy.** Nothing here bounds what the deviator learns
  about `x` from having observed the product `x * y`, across rounds, or
  after this one exchange. This is a single-round, single-shot statement.
* **One round only.** No claim is made about repeated or adaptively linked
  rounds; `lastMover_forces` shows that letting the deviator observe
  even *this* round's honest draw is enough to destroy uniformity, so no
  cross-round argument is even attempted.
-/


noncomputable section

namespace Math.ProbabilityMassFunction.GroupSumUniform

variable {G : Type} [Fintype G] [Group G]

/-- Left translation of the uniform law on a finite group by a fixed element
is again uniform. -/
theorem map_mul_left_uniform (g : G) :
    (PMF.uniformOfFintype G).map (fun x => g * x) = PMF.uniformOfFintype G := by
  classical
  ext a
  simp only [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply]
  have hpre : (fun x : G => g * x) ⁻¹' {a} = {g⁻¹ * a} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro h; rw [← h, inv_mul_cancel_left]
    · intro h; rw [h, mul_inv_cancel_left]
  rw [hpre]
  simp [PMF.uniformOfFintype_apply]

/-- Right translation of the uniform law on a finite group by a fixed element
is again uniform. -/
theorem map_mul_right_uniform (g : G) :
    (PMF.uniformOfFintype G).map (fun x => x * g) = PMF.uniformOfFintype G := by
  classical
  ext a
  simp only [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply]
  have hpre : (fun x : G => x * g) ⁻¹' {a} = {a * g⁻¹} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro h; rw [← h, mul_inv_cancel_right]
    · intro h; rw [h, inv_mul_cancel_right]
  rw [hpre]
  simp [PMF.uniformOfFintype_apply]

/-- Honest-left robustness: if one contributor's draw `x` is exactly uniform
and independent of the other contributor's arbitrary law `q` for `y`, the
product `x * y` is uniform no matter what `q` is. -/
theorem bind_uniform_mul_eq (q : PMF G) :
    (PMF.uniformOfFintype G).bind (fun x => q.map (fun y => x * y)) =
      PMF.uniformOfFintype G := by
  classical
  have hmap : ∀ x : G, q.map (fun y => x * y) = q.bind (fun y => PMF.pure (x * y)) :=
    fun _ => rfl
  simp_rw [hmap]
  rw [PMF.bind_comm]
  have hinner : ∀ y : G,
      (PMF.uniformOfFintype G).bind (fun x => PMF.pure (x * y)) =
        PMF.uniformOfFintype G := by
    intro y
    have heq : (fun x : G => PMF.pure (x * y)) = PMF.pure ∘ (fun x : G => x * y) := rfl
    rw [heq, PMF.bind_pure_comp]
    exact map_mul_right_uniform y
  simp_rw [hinner]
  exact PMF.bind_const _ _

/-- Honest-right robustness: the mirrored statement with the honest draw
multiplied on the right. -/
theorem bind_mul_uniform_eq (q : PMF G) :
    q.bind (fun y => (PMF.uniformOfFintype G).map (fun x => y * x)) =
      PMF.uniformOfFintype G := by
  classical
  simp_rw [map_mul_left_uniform]
  exact PMF.bind_const _ _

/-- Deviator-conditional form: the deviator may react to an independent
private signal `s ~ ps` through an arbitrary kernel `k : S → PMF G`, as long
as that signal is drawn independently of the honest draw `x` (not from `x`
itself). This is exactly `bind_uniform_mul_eq` applied to the pushed-forward
law `ps.bind k`, so no new argument is needed; contrast with
`lastMover_forces`, where the deviator instead reacts to `x` itself and
uniformity fails completely. -/
theorem bind_uniform_mul_eq_of_kernel {S : Type} (ps : PMF S) (k : S → PMF G) :
    (PMF.uniformOfFintype G).bind (fun x => (ps.bind k).map (fun y => x * y)) =
      PMF.uniformOfFintype G :=
  bind_uniform_mul_eq (ps.bind k)

/-! ## The sequential collapse: an observing last mover forces the outcome

The statements above all assume the two draws are independent (simultaneous
play, or a deviator reacting only to an independent private signal). The
following shows this independence assumption is load-bearing: if the second
mover instead *observes* the honest draw before replying, uniformity of the
product can fail completely, all the way down to a deterministic outcome. -/

/-- Sequential/observed counterexample: if the second mover *observes* the
honest uniform draw `x : Bool` and replies with `y := !x`, the induced law of
the XOR-product `x ^^ y` is deterministically `true` -- full collapse of the
uniformity guaranteed above once the deviator can react to the honest draw
itself, in sharp contrast to `bind_uniform_mul_eq`. -/
theorem lastMover_forces :
    (PMF.uniformOfFintype Bool).bind (fun x => PMF.pure (xor x (!x))) =
      PMF.pure true := by
  have hconst : (fun x : Bool => PMF.pure (xor x (!x))) = fun _ => PMF.pure true := by
    funext x
    cases x <;> rfl
  rw [hconst]
  exact PMF.bind_const _ _

end Math.ProbabilityMassFunction.GroupSumUniform
