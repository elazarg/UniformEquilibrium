import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Data.Sign.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Executable dense polynomials over operation-only coefficients

The coefficient type in this file need not satisfy ring laws.  This permits
the executable definitions to run directly on raw expression syntax.  Their
algebraic correctness is stated after applying an operation-preserving
evaluation into a genuine commutative ring.
-/

namespace Math

/-- Dense ascending-coefficient polynomials.  The list length is a formal
degree bound; trailing zero coefficients are retained unless an operation
explicitly removes them. -/
abbrev DensePolynomial (A : Type*) := List A

namespace DensePolynomial

variable {A R : Type*}

/-- Horner evaluation for ascending coefficients. -/
def eval [Zero A] [Add A] [Mul A] (p : DensePolynomial A) (x : A) : A :=
  p.foldr (fun coefficient value => coefficient + x * value) 0

/-- Coefficientwise addition, retaining the unused tail of the longer input. -/
def add [Add A] : DensePolynomial A → DensePolynomial A → DensePolynomial A
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => (a + b) :: add p q

/-- Coefficientwise negation. -/
def neg [Neg A] : DensePolynomial A → DensePolynomial A
  | [] => []
  | a :: p => -a :: neg p

/-- Coefficientwise subtraction. -/
def sub [Add A] [Neg A] (p q : DensePolynomial A) : DensePolynomial A :=
  add p (neg q)

/-- Coefficientwise scalar multiplication. -/
def scale [Mul A] (a : A) : DensePolynomial A → DensePolynomial A
  | [] => []
  | b :: p => a * b :: scale a p

/-- The monomial `a * X^degree`. -/
def monomial [Zero A] (degree : Nat) (a : A) : DensePolynomial A :=
  List.replicate degree 0 ++ [a]

/-- Multiplication by `X^degree`, retaining all formal coefficients. -/
def shift [Zero A] (degree : Nat) (p : DensePolynomial A) : DensePolynomial A :=
  List.replicate degree 0 ++ p

/-- Dense convolution product. -/
def mul [Zero A] [Add A] [Mul A] :
    DensePolynomial A → DensePolynomial A → DensePolynomial A
  | [], _ => []
  | a :: p, q => add (scale a q) (0 :: mul p q)

/-- Repeated addition, used by the derivative without requiring a natural-cast
operation on coefficient syntax. -/
def natMul [Zero A] [Add A] : Nat → A → A
  | 0, _ => 0
  | n + 1, a => a + natMul n a

/-- Auxiliary derivative whose first coefficient is multiplied by `index`. -/
def derivativeAux [Zero A] [Add A] : Nat → DensePolynomial A → DensePolynomial A
  | _, [] => []
  | index, a :: p => natMul index a :: derivativeAux (index + 1) p

/-- Formal derivative of an ascending coefficient list. -/
def derivative [Zero A] [Add A] (p : DensePolynomial A) : DensePolynomial A :=
  derivativeAux 1 p.tail

/-- Operation-preserving interpretation of raw coefficients in a commutative
ring.  No algebraic law is imposed on the source syntax. -/
structure Evaluator (A R : Type*) [Zero A] [One A] [Add A] [Neg A] [Mul A]
    [CommRing R] where
  toFun : A → R
  map_zero : toFun 0 = 0
  map_one : toFun 1 = 1
  map_add : ∀ a b, toFun (a + b) = toFun a + toFun b
  map_neg : ∀ a, toFun (-a) = -toFun a
  map_mul : ∀ a b, toFun (a * b) = toFun a * toFun b

namespace Evaluator

variable [Zero A] [One A] [Add A] [Neg A] [Mul A] [CommRing R]

instance : CoeFun (Evaluator A R) (fun _ => A → R) := ⟨Evaluator.toFun⟩

@[simp] theorem apply_zero (e : Evaluator A R) : e 0 = 0 := e.map_zero
@[simp] theorem apply_one (e : Evaluator A R) : e 1 = 1 := e.map_one
@[simp] theorem apply_add (e : Evaluator A R) (a b : A) : e (a + b) = e a + e b :=
  e.map_add a b
@[simp] theorem apply_neg (e : Evaluator A R) (a : A) : e (-a) = -e a := e.map_neg a
@[simp] theorem apply_mul (e : Evaluator A R) (a b : A) : e (a * b) = e a * e b :=
  e.map_mul a b

end Evaluator

/-- Horner evaluation after interpreting the coefficients. -/
def evalMap [Zero A] [One A] [Add A] [Neg A] [Mul A] [CommRing R]
    (e : Evaluator A R) (p : DensePolynomial A) (x : R) : R :=
  p.foldr (fun coefficient value => e coefficient + x * value) 0

section Evaluation

variable [Zero A] [One A] [Add A] [Neg A] [Mul A] [CommRing R]

@[simp] theorem evalMap_nil (e : Evaluator A R) (x : R) : evalMap e [] x = 0 := rfl

@[simp] theorem evalMap_cons (e : Evaluator A R) (a : A)
    (p : DensePolynomial A) (x : R) :
    evalMap e (a :: p) x = e a + x * evalMap e p x := rfl

theorem evalMap_add (e : Evaluator A R) (p q : DensePolynomial A) (x : R) :
    evalMap e (add p q) x = evalMap e p x + evalMap e q x := by
  induction p generalizing q with
  | nil => simp [add]
  | cons a p ih =>
      cases q with
      | nil => simp [add]
      | cons b q =>
          simp only [add, evalMap_cons, Evaluator.apply_add, ih]
          ring

theorem evalMap_neg (e : Evaluator A R) (p : DensePolynomial A) (x : R) :
    evalMap e (neg p) x = -evalMap e p x := by
  induction p with
  | nil => simp [neg]
  | cons a p ih =>
      rw [neg, evalMap_cons, Evaluator.apply_neg, evalMap_cons, ih]
      ring

theorem evalMap_sub (e : Evaluator A R) (p q : DensePolynomial A) (x : R) :
    evalMap e (sub p q) x = evalMap e p x - evalMap e q x := by
  rw [sub, evalMap_add, evalMap_neg]
  simp only [sub_eq_add_neg]

theorem evalMap_scale (e : Evaluator A R) (a : A)
    (p : DensePolynomial A) (x : R) :
    evalMap e (scale a p) x = e a * evalMap e p x := by
  induction p with
  | nil => simp [scale]
  | cons b p ih =>
      rw [scale, evalMap_cons, Evaluator.apply_mul, evalMap_cons, ih]
      ring

@[simp] theorem evalMap_replicate_zero (e : Evaluator A R) (n : Nat) (x : R) :
    evalMap e (List.replicate n (0 : A)) x = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [List.replicate_succ, evalMap_cons, Evaluator.apply_zero, ih]
      ring

theorem evalMap_append (e : Evaluator A R) (p q : DensePolynomial A) (x : R) :
    evalMap e (p ++ q) x = evalMap e p x + x ^ p.length * evalMap e q x := by
  induction p with
  | nil => simp
  | cons a p ih =>
      simp only [List.cons_append, evalMap_cons, ih, List.length_cons, pow_succ]
      ring

theorem evalMap_shift (e : Evaluator A R) (degree : Nat)
    (p : DensePolynomial A) (x : R) :
    evalMap e (shift degree p) x = x ^ degree * evalMap e p x := by
  rw [shift, evalMap_append, evalMap_replicate_zero, List.length_replicate, zero_add]

theorem evalMap_monomial (e : Evaluator A R) (degree : Nat) (a : A) (x : R) :
    evalMap e (monomial degree a) x = x ^ degree * e a := by
  rw [monomial, evalMap_append, evalMap_replicate_zero, List.length_replicate,
    zero_add]
  simp

theorem evalMap_mul (e : Evaluator A R) (p q : DensePolynomial A) (x : R) :
    evalMap e (mul p q) x = evalMap e p x * evalMap e q x := by
  induction p with
  | nil => simp [mul]
  | cons a p ih =>
      rw [mul, evalMap_add, evalMap_scale, evalMap_cons, ih]
      simp only [evalMap_cons, Evaluator.apply_zero, zero_add]
      ring

theorem evalMap_natMul (e : Evaluator A R) (n : Nat) (a : A) :
    e (natMul n a) = n • e a := by
  induction n with
  | zero => simp [natMul]
  | succ n ih =>
      rw [natMul, Evaluator.apply_add, ih, succ_nsmul]
      abel

end Evaluation

theorem length_add [Add A] (p q : DensePolynomial A) :
    (add p q).length = max p.length q.length := by
  induction p generalizing q with
  | nil => simp [add]
  | cons a p ih =>
      cases q with
      | nil => simp [add]
      | cons b q => simp [add, ih, Nat.succ_max_succ]

@[simp] theorem length_neg [Neg A] (p : DensePolynomial A) :
    (neg p).length = p.length := by
  induction p with
  | nil => rfl
  | cons a p ih => simp [neg, ih]

@[simp] theorem length_sub [Add A] [Neg A] (p q : DensePolynomial A) :
    (sub p q).length = max p.length q.length := by
  rw [sub, length_add, length_neg]

@[simp] theorem length_scale [Mul A] (a : A) (p : DensePolynomial A) :
    (scale a p).length = p.length := by
  induction p with
  | nil => rfl
  | cons b p ih => simp [scale, ih]

@[simp] theorem length_monomial [Zero A] (degree : Nat) (a : A) :
    (monomial degree a).length = degree + 1 := by
  simp [monomial]

@[simp] theorem length_shift [Zero A] (degree : Nat) (p : DensePolynomial A) :
    (shift degree p).length = degree + p.length := by
  simp [shift]

theorem length_mul_le [Zero A] [Add A] [Mul A] (p q : DensePolynomial A) :
    (mul p q).length ≤ p.length + q.length := by
  induction p with
  | nil => simp [mul]
  | cons a p ih =>
      rw [mul, length_add, length_scale, List.length_cons]
      apply max_le
      · omega
      · simp only [List.length_cons]
        omega

theorem length_derivativeAux [Zero A] [Add A] (index : Nat) (p : DensePolynomial A) :
    (derivativeAux index p).length = p.length := by
  induction p generalizing index with
  | nil => rfl
  | cons a p ih => simp [derivativeAux, ih]

theorem length_derivative [Zero A] [Add A] (p : DensePolynomial A) :
    (derivative p).length = p.length - 1 := by
  rw [derivative, length_derivativeAux, List.length_tail]

/-- The last formal coefficient, or zero for the empty polynomial. -/
def leadingCoeff [Zero A] : DensePolynomial A → A
  | [] => 0
  | [a] => a
  | _ :: b :: p => leadingCoeff (b :: p)

@[simp] theorem leadingCoeff_nil [Zero A] : leadingCoeff ([] : DensePolynomial A) = 0 :=
  rfl

@[simp] theorem leadingCoeff_singleton [Zero A] (a : A) : leadingCoeff [a] = a := rfl

theorem leadingCoeff_cons_cons [Zero A] (a b : A) (p : DensePolynomial A) :
    leadingCoeff (a :: b :: p) = leadingCoeff (b :: p) := rfl

theorem leadingCoeff_scale [Zero A] [Mul A] (a : A) (p : DensePolynomial A) :
    leadingCoeff (scale a p) = if p = [] then 0 else a * leadingCoeff p := by
  induction p with
  | nil => rfl
  | cons b p ih =>
      cases p with
      | nil => simp [scale]
      | cons c p => simpa only [scale, leadingCoeff_cons_cons, List.cons_ne_nil, ↓reduceIte]
          using ih

/-- One formal pseudo-division cancellation.  The algebraically canceled top
coefficient is explicitly removed with `dropLast`; no source-level ring
simplifier or decidable coefficient equality is used. -/
def pseudoRemainderStep [Zero A] [Add A] [Neg A] [Mul A]
    (divisor remainder : DensePolynomial A) : DensePolynomial A :=
  let degreeGap := remainder.length - divisor.length
  let full := sub (scale (leadingCoeff divisor) remainder)
    (shift degreeGap (scale (leadingCoeff remainder) divisor))
  full.dropLast

/-- Quotient update paired with `pseudoRemainderStep`. -/
def pseudoQuotientStep [Zero A] [Add A] [Mul A]
    (divisor remainder quotient : DensePolynomial A) : DensePolynomial A :=
  let degreeGap := remainder.length - divisor.length
  add (scale (leadingCoeff divisor) quotient)
    (monomial degreeGap (leadingCoeff remainder))

/-- Executable pseudo-division output. -/
structure PseudoDivisionResult (A : Type*) where
  exponent : Nat
  quotient : DensePolynomial A
  remainder : DensePolynomial A

/-- Fuel-bounded ordinary pseudo-division.  The public entry point supplies
`dividend.length` fuel. -/
def pseudoDivideLoop [Zero A] [Add A] [Neg A] [Mul A]
    (divisor : DensePolynomial A) :
    Nat → Nat → DensePolynomial A → DensePolynomial A → PseudoDivisionResult A
  | 0, exponent, quotient, remainder => ⟨exponent, quotient, remainder⟩
  | fuel + 1, exponent, quotient, remainder =>
      if remainder.length < divisor.length then
        ⟨exponent, quotient, remainder⟩
      else
        pseudoDivideLoop divisor fuel (exponent + 1)
          (pseudoQuotientStep divisor remainder quotient)
          (pseudoRemainderStep divisor remainder)

/-- Ordinary bounded pseudo-division, with a total fallback at the empty
divisor list. -/
def pseudoDivideRaw [Zero A] [Add A] [Neg A] [Mul A]
    (dividend divisor : DensePolynomial A) : PseudoDivisionResult A :=
  if divisor = [] then ⟨0, [], dividend⟩
  else pseudoDivideLoop divisor dividend.length 0 [] dividend

/-- Multiply quotient and remainder by the divisor leading coefficient and
increment the exponent. -/
def evenizePseudoDivision [Zero A] [Mul A] (divisor : DensePolynomial A)
    (result : PseudoDivisionResult A) : PseudoDivisionResult A :=
  if result.exponent % 2 = 0 then result
  else
    ⟨result.exponent + 1,
      scale (leadingCoeff divisor) result.quotient,
      scale (leadingCoeff divisor) result.remainder⟩

/-- Executable even-exponent pseudo-division. -/
def pseudoDivide [Zero A] [Add A] [Neg A] [Mul A]
    (dividend divisor : DensePolynomial A) : PseudoDivisionResult A :=
  evenizePseudoDivision divisor (pseudoDivideRaw dividend divisor)

theorem pseudoRemainderStep_length_lt [Zero A] [Add A] [Neg A] [Mul A]
    {divisor remainder : DensePolynomial A} (hdivisor : divisor ≠ [])
    (hle : divisor.length ≤ remainder.length) :
    (pseudoRemainderStep divisor remainder).length < remainder.length := by
  rw [pseudoRemainderStep]
  have hdivisorPos : 0 < divisor.length := List.length_pos_iff.mpr hdivisor
  have hremainderPos : 0 < remainder.length := lt_of_lt_of_le hdivisorPos hle
  have hshift :
      (shift (remainder.length - divisor.length)
          (scale (leadingCoeff remainder) divisor)).length = remainder.length := by
    rw [length_shift, length_scale, Nat.sub_add_cancel hle]
  rw [List.length_dropLast, length_sub, length_scale, hshift, max_self]
  omega

theorem pseudoQuotientStep_length [Zero A] [Add A] [Mul A]
    (divisor remainder quotient : DensePolynomial A) :
    (pseudoQuotientStep divisor remainder quotient).length =
      max quotient.length (remainder.length - divisor.length + 1) := by
  rw [pseudoQuotientStep, length_add, length_scale, length_monomial]

theorem leadingCoeff_eq_getLast [Zero A] {p : DensePolynomial A} (hp : p ≠ []) :
    leadingCoeff p = p.getLast hp := by
  induction p with
  | nil => exact (hp rfl).elim
  | cons a p ih =>
      cases p with
      | nil => rfl
      | cons b p =>
          rw [leadingCoeff_cons_cons, List.getLast_cons]
          exact ih (List.cons_ne_nil b p)

theorem leadingCoeff_append_of_ne [Zero A] (p : DensePolynomial A)
    {q : DensePolynomial A} (hq : q ≠ []) :
    leadingCoeff (p ++ q) = leadingCoeff q := by
  induction p with
  | nil => rfl
  | cons a p ih =>
      cases p with
      | nil =>
          cases q with
          | nil => exact (hq rfl).elim
          | cons b q => rfl
      | cons b p =>
          exact ih

theorem leadingCoeff_shift_of_ne [Zero A] (degree : Nat)
    {p : DensePolynomial A} (hp : p ≠ []) :
    leadingCoeff (shift degree p) = leadingCoeff p := by
  exact leadingCoeff_append_of_ne (List.replicate degree 0) hp

theorem leadingCoeff_neg_of_ne [Zero A] [Neg A]
    {p : DensePolynomial A} (hp : p ≠ []) :
    leadingCoeff (neg p) = -leadingCoeff p := by
  induction p with
  | nil => exact (hp rfl).elim
  | cons a p ih =>
      cases p with
      | nil => rfl
      | cons b p =>
          rw [neg, neg, leadingCoeff_cons_cons, leadingCoeff_cons_cons]
          exact ih (List.cons_ne_nil b p)

theorem leadingCoeff_scale_of_ne [Zero A] [Mul A] (a : A)
    {p : DensePolynomial A} (hp : p ≠ []) :
    leadingCoeff (scale a p) = a * leadingCoeff p := by
  induction p with
  | nil => exact (hp rfl).elim
  | cons b p ih =>
      cases p with
      | nil => rfl
      | cons c p =>
          rw [scale, scale, leadingCoeff_cons_cons, leadingCoeff_cons_cons]
          exact ih (List.cons_ne_nil c p)

theorem leadingCoeff_add_of_length_eq [Zero A] [Add A]
    {p q : DensePolynomial A} (hp : p ≠ []) (hlength : p.length = q.length) :
    leadingCoeff (add p q) = leadingCoeff p + leadingCoeff q := by
  induction p generalizing q with
  | nil => exact (hp rfl).elim
  | cons a p ih =>
      cases q with
      | nil => simp at hlength
      | cons b q =>
          cases p with
          | nil =>
              have hq : q = [] := by simpa using hlength
              subst q
              rfl
          | cons c p =>
              cases q with
              | nil => simp at hlength
              | cons d q =>
                  change leadingCoeff (add (c :: p) (d :: q)) =
                    leadingCoeff (c :: p) + leadingCoeff (d :: q)
                  apply ih (List.cons_ne_nil c p)
                  simpa using hlength

theorem leadingCoeff_sub_of_length_eq [Zero A] [Add A] [Neg A]
    {p q : DensePolynomial A} (hp : p ≠ []) (hlength : p.length = q.length) :
    leadingCoeff (sub p q) = leadingCoeff p + -leadingCoeff q := by
  have hq : q ≠ [] := by
    intro hq
    apply hp
    apply List.length_eq_zero_iff.mp
    rw [hlength, hq]
    rfl
  rw [sub, leadingCoeff_add_of_length_eq hp]
  · congr 1
    exact leadingCoeff_neg_of_ne hq
  · simpa using hlength

theorem evalMap_eq_dropLast_add_leading [Zero A] [One A] [Add A] [Neg A] [Mul A]
    [CommRing R] (e : Evaluator A R) {p : DensePolynomial A} (hp : p ≠ []) (x : R) :
    evalMap e p x = evalMap e p.dropLast x +
      x ^ p.dropLast.length * e (leadingCoeff p) := by
  calc
    evalMap e p x = evalMap e (p.dropLast ++ [p.getLast hp]) x := by
      rw [List.dropLast_append_getLast hp]
    _ = evalMap e p.dropLast x +
        x ^ p.dropLast.length * evalMap e [p.getLast hp] x :=
      evalMap_append e p.dropLast [p.getLast hp] x
    _ = evalMap e p.dropLast x +
        x ^ p.dropLast.length * e (leadingCoeff p) := by
      rw [evalMap_cons, evalMap_nil, mul_zero, add_zero, leadingCoeff_eq_getLast hp]

theorem evalMap_dropLast_of_leading_zero
    [Zero A] [One A] [Add A] [Neg A] [Mul A] [CommRing R]
    (e : Evaluator A R) {p : DensePolynomial A} (hp : p ≠ []) (x : R)
    (hleading : e (leadingCoeff p) = 0) :
    evalMap e p.dropLast x = evalMap e p x := by
  rw [evalMap_eq_dropLast_add_leading e hp x, hleading, mul_zero, add_zero]

theorem pseudoRemainderStep_evalMap [Zero A] [One A] [Add A] [Neg A] [Mul A]
    [CommRing R] (e : Evaluator A R) {divisor remainder : DensePolynomial A}
    (hdivisor : divisor ≠ []) (hle : divisor.length ≤ remainder.length) (x : R) :
    evalMap e (pseudoRemainderStep divisor remainder) x =
      e (leadingCoeff divisor) * evalMap e remainder x -
        evalMap e divisor x *
          (e (leadingCoeff remainder) * x ^ (remainder.length - divisor.length)) := by
  let gap := remainder.length - divisor.length
  let full := sub (scale (leadingCoeff divisor) remainder)
    (shift gap (scale (leadingCoeff remainder) divisor))
  have hremainder : remainder ≠ [] := by
    have hpos : 0 < remainder.length :=
      lt_of_lt_of_le (List.length_pos_iff.mpr hdivisor) hle
    exact List.length_pos_iff.mp hpos
  have hscaledRemainder : scale (leadingCoeff divisor) remainder ≠ [] := by
    intro h
    have := congrArg List.length h
    simp only [length_scale, List.length_nil] at this
    exact hremainder (List.length_eq_zero_iff.mp this)
  have hscaledDivisor : scale (leadingCoeff remainder) divisor ≠ [] := by
    intro h
    have := congrArg List.length h
    simp only [length_scale, List.length_nil] at this
    exact hdivisor (List.length_eq_zero_iff.mp this)
  have hshiftLength :
      (shift gap (scale (leadingCoeff remainder) divisor)).length = remainder.length := by
    rw [length_shift, length_scale]
    exact Nat.sub_add_cancel hle
  have hfullLength : full.length = remainder.length := by
    simp only [full, length_sub, length_scale, hshiftLength, max_self]
  have hfull : full ≠ [] := by
    intro h
    have := congrArg List.length h
    rw [hfullLength] at this
    exact hremainder (List.length_eq_zero_iff.mp this)
  have hleadingFull : e (leadingCoeff full) = 0 := by
    change e (leadingCoeff
      (sub (scale (leadingCoeff divisor) remainder)
        (shift gap (scale (leadingCoeff remainder) divisor)))) = 0
    rw [leadingCoeff_sub_of_length_eq hscaledRemainder]
    · rw [leadingCoeff_scale_of_ne _ hremainder,
        leadingCoeff_shift_of_ne gap hscaledDivisor,
        leadingCoeff_scale_of_ne _ hdivisor]
      simp only [Evaluator.apply_add, Evaluator.apply_neg, Evaluator.apply_mul]
      ring
    · rw [length_scale]
      exact hshiftLength.symm
  change evalMap e full.dropLast x = _
  rw [evalMap_dropLast_of_leading_zero e hfull x hleadingFull]
  simp only [full, evalMap_sub, evalMap_scale, evalMap_shift]
  ring

theorem pseudoQuotientStep_evalMap [Zero A] [One A] [Add A] [Neg A] [Mul A]
    [CommRing R] (e : Evaluator A R) (divisor remainder quotient : DensePolynomial A)
    (x : R) :
    evalMap e (pseudoQuotientStep divisor remainder quotient) x =
      e (leadingCoeff divisor) * evalMap e quotient x +
        x ^ (remainder.length - divisor.length) * e (leadingCoeff remainder) := by
  rw [pseudoQuotientStep, evalMap_add, evalMap_scale, evalMap_monomial]

/-- Semantic pseudo-division identity at one evaluation point. -/
def PseudoDivisionIdentity [Zero A] [One A] [Add A] [Neg A] [Mul A]
    [CommRing R] (e : Evaluator A R) (dividend divisor : DensePolynomial A)
    (result : PseudoDivisionResult A) (x : R) : Prop :=
  e (leadingCoeff divisor) ^ result.exponent * evalMap e dividend x =
    evalMap e divisor x * evalMap e result.quotient x +
      evalMap e result.remainder x

theorem pseudoDivideLoop_identity [Zero A] [One A] [Add A] [Neg A] [Mul A]
    [CommRing R] (e : Evaluator A R) {dividend divisor : DensePolynomial A}
    (hdivisor : divisor ≠ []) (x : R) (fuel exponent : Nat)
    (quotient remainder : DensePolynomial A)
    (hinvariant :
      e (leadingCoeff divisor) ^ exponent * evalMap e dividend x =
        evalMap e divisor x * evalMap e quotient x + evalMap e remainder x) :
    PseudoDivisionIdentity e dividend divisor
      (pseudoDivideLoop divisor fuel exponent quotient remainder) x := by
  induction fuel generalizing exponent quotient remainder with
  | zero => exact hinvariant
  | succ fuel ih =>
      rw [pseudoDivideLoop]
      split
      · exact hinvariant
      · rename_i hnotLess
        apply ih
        have hle : divisor.length ≤ remainder.length := Nat.le_of_not_gt hnotLess
        rw [pseudoQuotientStep_evalMap e divisor remainder quotient x,
          pseudoRemainderStep_evalMap e hdivisor hle x, pow_succ]
        calc
          e (leadingCoeff divisor) ^ exponent * e (leadingCoeff divisor) *
                evalMap e dividend x =
              e (leadingCoeff divisor) *
                (e (leadingCoeff divisor) ^ exponent * evalMap e dividend x) := by
            ring
          _ = e (leadingCoeff divisor) *
                (evalMap e divisor x * evalMap e quotient x +
                  evalMap e remainder x) := by rw [hinvariant]
          _ = evalMap e divisor x *
                (e (leadingCoeff divisor) * evalMap e quotient x +
                  x ^ (remainder.length - divisor.length) *
                    e (leadingCoeff remainder)) +
                (e (leadingCoeff divisor) * evalMap e remainder x -
                  evalMap e divisor x *
                    (e (leadingCoeff remainder) *
                      x ^ (remainder.length - divisor.length))) := by
            ring

theorem pseudoDivideLoop_remainder_length_lt [Zero A] [Add A] [Neg A] [Mul A]
    {divisor remainder quotient : DensePolynomial A} (hdivisor : divisor ≠ [])
    {fuel exponent : Nat} (hfuel : remainder.length ≤ fuel) :
    (pseudoDivideLoop divisor fuel exponent quotient remainder).remainder.length <
      divisor.length := by
  induction fuel generalizing exponent quotient remainder with
  | zero =>
      have hremainder : remainder = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hfuel)
      subst remainder
      rw [pseudoDivideLoop]
      exact List.length_pos_iff.mpr hdivisor
  | succ fuel ih =>
      rw [pseudoDivideLoop]
      split
      · assumption
      · rename_i hnotLess
        apply ih
        have hle : divisor.length ≤ remainder.length := Nat.le_of_not_gt hnotLess
        have hstep := pseudoRemainderStep_length_lt hdivisor hle
        omega

theorem pseudoDivideRaw_identity [Zero A] [One A] [Add A] [Neg A] [Mul A]
    [CommRing R] (e : Evaluator A R) (dividend divisor : DensePolynomial A) (x : R) :
    PseudoDivisionIdentity e dividend divisor (pseudoDivideRaw dividend divisor) x := by
  by_cases hdivisor : divisor = []
  · subst divisor
    simp [PseudoDivisionIdentity, pseudoDivideRaw, evalMap]
  · rw [pseudoDivideRaw, if_neg hdivisor]
    apply pseudoDivideLoop_identity e hdivisor x
    simp [evalMap]

theorem pseudoDivideRaw_remainder_length_lt [Zero A] [Add A] [Neg A] [Mul A]
    (dividend : DensePolynomial A) {divisor : DensePolynomial A} (hdivisor : divisor ≠ []) :
    (pseudoDivideRaw dividend divisor).remainder.length < divisor.length := by
  rw [pseudoDivideRaw, if_neg hdivisor]
  exact pseudoDivideLoop_remainder_length_lt hdivisor (le_refl dividend.length)

theorem evenizePseudoDivision_identity [Zero A] [One A] [Add A] [Neg A] [Mul A]
    [CommRing R] (e : Evaluator A R) (dividend divisor : DensePolynomial A)
    (result : PseudoDivisionResult A) (x : R)
    (hresult : PseudoDivisionIdentity e dividend divisor result x) :
    PseudoDivisionIdentity e dividend divisor (evenizePseudoDivision divisor result) x := by
  rw [evenizePseudoDivision]
  split
  · exact hresult
  · simp only [PseudoDivisionIdentity, evalMap_scale, pow_succ]
    rw [PseudoDivisionIdentity] at hresult
    calc
      e (leadingCoeff divisor) ^ result.exponent * e (leadingCoeff divisor) *
            evalMap e dividend x =
          e (leadingCoeff divisor) *
            (e (leadingCoeff divisor) ^ result.exponent * evalMap e dividend x) := by
        ring
      _ = e (leadingCoeff divisor) *
            (evalMap e divisor x * evalMap e result.quotient x +
              evalMap e result.remainder x) := by rw [hresult]
      _ = evalMap e divisor x *
            (e (leadingCoeff divisor) * evalMap e result.quotient x) +
          e (leadingCoeff divisor) * evalMap e result.remainder x := by
        ring

theorem evenizePseudoDivision_remainder_length [Zero A] [Mul A]
    (divisor : DensePolynomial A) (result : PseudoDivisionResult A) :
    (evenizePseudoDivision divisor result).remainder.length = result.remainder.length := by
  rw [evenizePseudoDivision]
  split
  · rfl
  · exact length_scale _ _

theorem evenizePseudoDivision_exponent_mod_two [Zero A] [Mul A]
    (divisor : DensePolynomial A) (result : PseudoDivisionResult A) :
    (evenizePseudoDivision divisor result).exponent % 2 = 0 := by
  rw [evenizePseudoDivision]
  split
  · assumption
  · rename_i hodd
    change (result.exponent + 1) % 2 = 0
    have hmod := Nat.mod_lt result.exponent (by omega : 0 < 2)
    omega

/-- The executable pseudo-division identity.  It is valid even at the total
empty-divisor fallback. -/
theorem pseudoDivide_identity [Zero A] [One A] [Add A] [Neg A] [Mul A]
    [CommRing R] (e : Evaluator A R) (dividend divisor : DensePolynomial A) (x : R) :
    PseudoDivisionIdentity e dividend divisor (pseudoDivide dividend divisor) x := by
  exact evenizePseudoDivision_identity e dividend divisor
    (pseudoDivideRaw dividend divisor) x (pseudoDivideRaw_identity e dividend divisor x)

/-- A nonempty divisor gives a formally shorter pseudo-remainder. -/
theorem pseudoDivide_remainder_length_lt [Zero A] [Add A] [Neg A] [Mul A]
    (dividend : DensePolynomial A) {divisor : DensePolynomial A} (hdivisor : divisor ≠ []) :
    (pseudoDivide dividend divisor).remainder.length < divisor.length := by
  rw [pseudoDivide, evenizePseudoDivision_remainder_length]
  exact pseudoDivideRaw_remainder_length_lt dividend hdivisor

/-- The public pseudo-division scale exponent is even. -/
theorem pseudoDivide_exponent_mod_two [Zero A] [Add A] [Neg A] [Mul A]
    (dividend divisor : DensePolynomial A) :
    (pseudoDivide dividend divisor).exponent % 2 = 0 := by
  exact evenizePseudoDivision_exponent_mod_two divisor (pseudoDivideRaw dividend divisor)

theorem pseudoDivide_exponent_even [Zero A] [Add A] [Neg A] [Mul A]
    (dividend divisor : DensePolynomial A) :
    Even (pseudoDivide dividend divisor).exponent := by
  rw [Nat.even_iff]
  exact pseudoDivide_exponent_mod_two dividend divisor

/-- Expanded pointwise form of `pseudoDivide_identity`. -/
theorem pseudoDivide_evalMap_identity [Zero A] [One A] [Add A] [Neg A] [Mul A]
    [CommRing R] (e : Evaluator A R) (dividend divisor : DensePolynomial A) (x : R) :
    e (leadingCoeff divisor) ^ (pseudoDivide dividend divisor).exponent *
        evalMap e dividend x =
      evalMap e divisor x * evalMap e (pseudoDivide dividend divisor).quotient x +
        evalMap e (pseudoDivide dividend divisor).remainder x :=
  pseudoDivide_identity e dividend divisor x

/-- Total coefficient lookup, returning the source zero beyond the formal
coefficient list. -/
def coefficient [Zero A] : DensePolynomial A → Nat → A
  | [], _ => 0
  | a :: _, 0 => a
  | _ :: p, n + 1 => coefficient p n

theorem coefficient_eq_zero_of_length_le [Zero A] {p : DensePolynomial A} {n : Nat}
    (h : p.length ≤ n) : coefficient p n = 0 := by
  induction p generalizing n with
  | nil => rfl
  | cons a p ih =>
      cases n with
      | zero => simp at h
      | succ n =>
          rw [coefficient]
          apply ih
          simpa using h

theorem coefficient_length_sub_one [Zero A] (p : DensePolynomial A) :
    coefficient p (p.length - 1) = leadingCoeff p := by
  induction p with
  | nil => rfl
  | cons a p ih =>
      cases p with
      | nil => rfl
      | cons b p =>
          change coefficient (b :: p) ((b :: p).length - 1) = leadingCoeff (b :: p)
          exact ih

/-- Polynomial interpretation of a dense list after coefficient evaluation. -/
noncomputable def toPolynomial [Zero A] [One A] [Add A] [Neg A] [Mul A] [CommRing R]
    (e : Evaluator A R) (p : DensePolynomial A) : Polynomial R :=
  p.foldr (fun coefficient value => Polynomial.C (e coefficient) + Polynomial.X * value) 0

@[simp] theorem toPolynomial_nil [Zero A] [One A] [Add A] [Neg A] [Mul A]
    [CommRing R] (e : Evaluator A R) : toPolynomial e [] = 0 := rfl

@[simp] theorem toPolynomial_cons [Zero A] [One A] [Add A] [Neg A] [Mul A]
    [CommRing R] (e : Evaluator A R) (a : A) (p : DensePolynomial A) :
    toPolynomial e (a :: p) = Polynomial.C (e a) + Polynomial.X * toPolynomial e p := rfl

theorem toPolynomial_eval [Zero A] [One A] [Add A] [Neg A] [Mul A]
    [CommRing R] (e : Evaluator A R) (p : DensePolynomial A) (x : R) :
    (toPolynomial e p).eval x = evalMap e p x := by
  induction p with
  | nil => simp
  | cons a p ih => simp [ih]

theorem toPolynomial_coeff [Zero A] [One A] [Add A] [Neg A] [Mul A]
    [CommRing R] (e : Evaluator A R) (p : DensePolynomial A) (n : Nat) :
    (toPolynomial e p).coeff n = e (coefficient p n) := by
  induction p generalizing n with
  | nil => simp [toPolynomial, coefficient]
  | cons a p ih =>
      cases n with
      | zero => simp [toPolynomial, coefficient]
      | succ n =>
          rw [toPolynomial_cons, Polynomial.coeff_add, Polynomial.coeff_X_mul, ih]
          simp [coefficient]

theorem toPolynomial_natDegree_le [Zero A] [One A] [Add A] [Neg A] [Mul A]
    [CommRing R] (e : Evaluator A R) (p : DensePolynomial A) :
    (toPolynomial e p).natDegree ≤ p.length - 1 := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro n hn
  rw [toPolynomial_coeff, coefficient_eq_zero_of_length_le, Evaluator.apply_zero]
  omega

theorem toPolynomial_coeff_length_sub_one [Zero A] [One A] [Add A] [Neg A] [Mul A]
    [CommRing R] (e : Evaluator A R) (p : DensePolynomial A) :
    (toPolynomial e p).coeff (p.length - 1) = e (leadingCoeff p) := by
  rw [toPolynomial_coeff, coefficient_length_sub_one]

theorem toPolynomial_natDegree_eq [Zero A] [One A] [Add A] [Neg A] [Mul A]
    [CommRing R] (e : Evaluator A R) (p : DensePolynomial A)
    (hleading : e (leadingCoeff p) ≠ 0) :
    (toPolynomial e p).natDegree = p.length - 1 := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero (toPolynomial_natDegree_le e p)
  rw [toPolynomial_coeff_length_sub_one e p]
  exact hleading

theorem toPolynomial_derivativeAux [Zero A] [One A] [Add A] [Neg A] [Mul A]
    [CommRing R] (e : Evaluator A R) (index : Nat) (p : DensePolynomial A) :
    toPolynomial e (derivativeAux index p) =
      index • toPolynomial e p + Polynomial.X * (toPolynomial e p).derivative := by
  induction p generalizing index with
  | nil => simp [derivativeAux]
  | cons a p ih =>
      rw [derivativeAux, toPolynomial_cons, toPolynomial_cons, evalMap_natMul,
        ih (index + 1)]
      simp only [Polynomial.derivative_add, Polynomial.derivative_C,
        Polynomial.derivative_mul, Polynomial.derivative_X, zero_add, one_mul,
        nsmul_eq_mul]
      push_cast
      have hconstant :
          Polynomial.C ((index : R) * e a) =
            (index : Polynomial R) * Polynomial.C (e a) := by
        rw [Polynomial.C_mul]
        simp
      rw [hconstant]
      ring

theorem toPolynomial_derivative [Zero A] [One A] [Add A] [Neg A] [Mul A]
    [CommRing R] (e : Evaluator A R) (p : DensePolynomial A) :
    toPolynomial e (derivative p) = (toPolynomial e p).derivative := by
  cases p with
  | nil => simp [derivative, derivativeAux, toPolynomial]
  | cons a p =>
      rw [derivative, List.tail_cons, toPolynomial_derivativeAux]
      simp

namespace Evaluator

/-- Identity evaluator for the scalar commutative-ring specialization. -/
def identity (R : Type*) [CommRing R] : Evaluator R R where
  toFun := id
  map_zero := rfl
  map_one := rfl
  map_add := fun _ _ => rfl
  map_neg := fun _ => rfl
  map_mul := fun _ _ => rfl

end Evaluator

theorem evalMap_identity [CommRing R] (p : DensePolynomial R) (x : R) :
    evalMap (Evaluator.identity R) p x = eval p x := by
  induction p with
  | nil => rfl
  | cons a p ih =>
      rw [evalMap_cons, eval, List.foldr_cons, ih]
      change a + x * eval p x = a + x * eval p x
      rfl

/-- Scalar-ring specialization of the pseudo-division identity. -/
theorem pseudoDivide_eval_identity [CommRing R]
    (dividend divisor : DensePolynomial R) (x : R) :
    leadingCoeff divisor ^ (pseudoDivide dividend divisor).exponent * eval dividend x =
      eval divisor x * eval (pseudoDivide dividend divisor).quotient x +
        eval (pseudoDivide dividend divisor).remainder x := by
  have h := pseudoDivide_evalMap_identity (Evaluator.identity R) dividend divisor x
  rw [evalMap_identity, evalMap_identity, evalMap_identity, evalMap_identity] at h
  change leadingCoeff divisor ^ (pseudoDivide dividend divisor).exponent *
      eval dividend x = _ at h
  exact h

/-- Under a nonzero specialized divisor leading coefficient, the even
pseudo-division scale is strictly positive. -/
theorem pseudoDivide_scale_pos [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    [Zero A] [One A] [Add A] [Neg A] [Mul A]
    (e : Evaluator A R) (dividend divisor : DensePolynomial A)
    (hleading : e (leadingCoeff divisor) ≠ 0) :
    0 < e (leadingCoeff divisor) ^ (pseudoDivide dividend divisor).exponent :=
  (pseudoDivide_exponent_even dividend divisor).pow_pos hleading

/-- At a specialized divisor root, even pseudo-division preserves the sign of
the dividend in the remainder whenever the specialized leading coefficient is
nonzero. -/
theorem pseudoDivide_sign_remainder_eq_sign_dividend_at_divisor_root
    [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    [Zero A] [One A] [Add A] [Neg A] [Mul A]
    (e : Evaluator A R) (dividend divisor : DensePolynomial A) (x : R)
    (hroot : evalMap e divisor x = 0) (hleading : e (leadingCoeff divisor) ≠ 0) :
    SignType.sign (evalMap e (pseudoDivide dividend divisor).remainder x) =
      SignType.sign (evalMap e dividend x) := by
  have hidentity := pseudoDivide_evalMap_identity e dividend divisor x
  rw [hroot, zero_mul, zero_add] at hidentity
  rw [← hidentity, sign_mul,
    sign_pos (pseudoDivide_scale_pos e dividend divisor hleading), one_mul]

end DensePolynomial

end Math
