import Mathlib.Data.Sign.Defs

/-!
# Executable Boolean formulas in exact signs

Boolean formulas depend only on a supplied negative/zero/positive sign assignment.
Their executable evaluator agrees with the propositional semantics.
-/

namespace Math
namespace PolynomialSignCell

variable {ι : Type*}

/-- A finite Boolean formula in exact sign atoms. -/
inductive SignFormula (ι : Type*)
  | atom (i : ι) (s : SignType)
  | top
  | bot
  | and (φ ψ : SignFormula ι)
  | or (φ ψ : SignFormula ι)
  | not (φ : SignFormula ι)
  deriving DecidableEq

namespace SignFormula

/-- Truth of a Boolean sign formula on a sign assignment. -/
def Holds : SignFormula ι → (ι → SignType) → Prop
  | atom i s, τ => τ i = s
  | top, _ => True
  | bot, _ => False
  | and φ ψ, τ => φ.Holds τ ∧ ψ.Holds τ
  | or φ ψ, τ => φ.Holds τ ∨ ψ.Holds τ
  | not φ, τ => ¬φ.Holds τ

/-- Executable truth evaluation of a Boolean sign formula. -/
def eval : SignFormula ι → (ι → SignType) → Bool
  | atom i s, τ => decide (τ i = s)
  | top, _ => true
  | bot, _ => false
  | and φ ψ, τ => φ.eval τ && ψ.eval τ
  | or φ ψ, τ => φ.eval τ || ψ.eval τ
  | not φ, τ => !(φ.eval τ)

@[simp]
theorem eval_eq_true_iff (φ : SignFormula ι) (τ : ι → SignType) :
    φ.eval τ = true ↔ φ.Holds τ := by
  induction φ with
  | atom i s => simp [eval, Holds]
  | top => simp [eval, Holds]
  | bot => simp [eval, Holds]
  | and φ ψ hφ hψ => simp [eval, Holds, hφ, hψ]
  | or φ ψ hφ hψ => simp [eval, Holds, hφ, hψ]
  | not φ hφ =>
      cases hEval : φ.eval τ <;> simp_all [eval, Holds]

@[simp]
theorem eval_eq_false_iff (φ : SignFormula ι) (τ : ι → SignType) :
    φ.eval τ = false ↔ ¬φ.Holds τ := by
  rw [← Bool.not_eq_true]
  simp

end SignFormula
end PolynomialSignCell
end Math
