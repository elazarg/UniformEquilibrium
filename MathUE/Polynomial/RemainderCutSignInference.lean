import MathUE.Polynomial.OrderedRealSignDiagram
import MathUE.Polynomial.DensePolynomial

/-!
# Executable sign inference at retained divisor roots

Aligned pseudo-remainder signs determine the removed polynomial's sign at any
cut where a divisor vanishes. A failed search identifies a removable cut.
-/

namespace MathUE.OrderedRealSignDiagram

open SignType

/-- Find the first zero divisor sign and return its aligned remainder sign. -/
def inferRootSign : List SignType → List SignType → Option SignType
  | divisor :: divisors, remainder :: remainders =>
      if divisor = 0 then some remainder else inferRootSign divisors remainders
  | _, _ => none

/-- With aligned rows, the search fails exactly when every divisor sign is nonzero. -/
theorem inferRootSign_eq_none_iff {divisors remainders : List SignType}
    (hlength : divisors.length = remainders.length) :
    inferRootSign divisors remainders = none ↔ ∀ s ∈ divisors, s ≠ 0 := by
  induction divisors generalizing remainders with
  | nil => simp [inferRootSign]
  | cons d divisors ih =>
      cases remainders with
      | nil => simp at hlength
      | cons r remainders =>
          have htail : divisors.length = remainders.length := Nat.succ.inj hlength
          by_cases hd : d = 0
          · simp [inferRootSign, hd]
          · simp [inferRootSign, hd, ih htail]

/-- Every successful result is the target sign if each zero-divisor pair is sound. -/
theorem inferRootSign_sound {divisors remainders : List SignType} {target result : SignType}
    (hpaired : List.Forall₂ (fun d r => d = 0 → r = target) divisors remainders)
    (hfound : inferRootSign divisors remainders = some result) : result = target := by
  induction hpaired with
  | nil => simp [inferRootSign] at hfound
  | @cons d r divisors remainders hhead htail ih =>
      by_cases hd : d = 0
      · have hr : r = result := by simpa only [inferRootSign, if_pos hd, Option.some.injEq]
          using hfound
        exact hr.symm.trans (hhead hd)
      · exact ih (by simpa only [inferRootSign, if_neg hd] using hfound)

/-- The first-zero scan both finds and correctly labels every available divisor root. -/
theorem inferRootSign_eq_some_iff {divisors remainders : List SignType} {target : SignType}
    (hpaired : List.Forall₂ (fun d r => d = 0 → r = target) divisors remainders) :
    inferRootSign divisors remainders = some target ↔ 0 ∈ divisors := by
  have hnone := inferRootSign_eq_none_iff hpaired.length_eq
  constructor
  · intro hfound
    by_contra hmem
    have hz := hnone.mpr (fun s hs hs0 => hmem (hs0 ▸ hs))
    simp [hz] at hfound
  · intro hmem
    cases hscan : inferRootSign divisors remainders with
    | none => exact False.elim ((hnone.mp hscan) 0 hmem rfl)
    | some result =>
        have hresult := inferRootSign_sound hpaired hscan
        exact congrArg some hresult

/-- Divisors and remainders are aligned, and the remainder has the dividend's sign
at every zero of its corresponding divisor. -/
def AlignedRootSigns (dividend : Polynomial ℝ)
    (divisors remainders : List (Polynomial ℝ)) : Prop :=
  List.Forall₂ (fun d r => ∀ x, d.eval x = 0 → sign (r.eval x) = sign (dividend.eval x))
    divisors remainders

theorem AlignedRootSigns.sign_pairs {dividend : Polynomial ℝ}
    {divisors remainders : List (Polynomial ℝ)}
    (hpaired : AlignedRootSigns dividend divisors remainders) (x : ℝ) :
    List.Forall₂ (fun d r => d = 0 → r = sign (dividend.eval x))
      (divisors.map (fun d => sign (d.eval x)))
      (remainders.map (fun r => sign (r.eval x))) := by
  induction hpaired with
  | nil => exact .nil
  | cons hhead htail ih =>
      exact .cons (fun hz => hhead x (sign_eq_zero_iff.mp hz)) ih

/-- Point-row data is enough to compute the dividend sign exactly at retained roots. -/
theorem inferRootSign_point_rows {dividend : Polynomial ℝ}
    {divisors remainders : List (Polynomial ℝ)} {x : ℝ}
    {divisorSigns remainderSigns : List SignType}
    (hpaired : AlignedRootSigns dividend divisors remainders)
    (hdivisors : RowOn divisors {x} divisorSigns)
    (hremainders : RowOn remainders {x} remainderSigns) :
    inferRootSign divisorSigns remainderSigns = some (sign (dividend.eval x)) ↔
      ∃ d ∈ divisors, d.eval x = 0 := by
  rw [hdivisors.eq_map_at (Set.mem_singleton x), hremainders.eq_map_at (Set.mem_singleton x)]
  simpa only [List.mem_map, sign_eq_zero_iff] using
    inferRootSign_eq_some_iff (hpaired.sign_pairs x)

/-- A point where the scan fails is removable from the retained divisor diagram. -/
theorem removableAt_of_inferRootSign_none {dividend : Polynomial ℝ}
    {divisors remainders : List (Polynomial ℝ)} {x : ℝ}
    {divisorSigns remainderSigns : List SignType}
    (hpaired : AlignedRootSigns dividend divisors remainders)
    (hdivisors : RowOn divisors {x} divisorSigns)
    (hremainders : RowOn remainders {x} remainderSigns)
    (hnone : inferRootSign divisorSigns remainderSigns = none) : RemovableAt divisors x := by
  intro d hd
  right
  intro hzero
  have hsome := (inferRootSign_point_rows hpaired hdivisors hremainders).mpr ⟨d, hd, hzero⟩
  simp [hnone] at hsome

section DensePseudoRemainders

open Math.DensePolynomial

variable {A : Type*} [Zero A] [One A] [Add A] [Neg A] [Mul A]

/-- Actual even pseudo-remainders supply the aligned-root-sign property; there is
no oracle or extra polynomial-sign hypothesis in this adapter. -/
theorem alignedRootSigns_pseudoRemainders (e : Evaluator A ℝ)
    (dividend : Math.DensePolynomial A) (divisors : List (Math.DensePolynomial A))
    (hleading : ∀ d ∈ divisors, e (leadingCoeff d) ≠ 0) :
    AlignedRootSigns (toPolynomial e dividend) (divisors.map (toPolynomial e))
      ((divisors.map (fun d => (pseudoDivide dividend d).remainder)).map (toPolynomial e)) := by
  induction divisors with
  | nil => exact .nil
  | cons divisor divisors ih =>
      apply List.Forall₂.cons
      · intro x hx
        have hroot : evalMap e divisor x = 0 := by simpa only [toPolynomial_eval] using hx
        simpa only [toPolynomial_eval] using
          pseudoDivide_sign_remainder_eq_sign_dividend_at_divisor_root e dividend divisor x
            hroot (hleading divisor List.mem_cons_self)
      · exact ih (fun d hd => hleading d (List.mem_cons_of_mem _ hd))

/-- The executable scan applied to actual pseudo-remainder point rows is sound and
complete for the presence of a divisor root at that point. -/
theorem inferRootSign_pseudoRemainder_point_rows (e : Evaluator A ℝ)
    (dividend : Math.DensePolynomial A) (divisors : List (Math.DensePolynomial A))
    (hleading : ∀ d ∈ divisors, e (leadingCoeff d) ≠ 0) (x : ℝ)
    {divisorSigns remainderSigns : List SignType}
    (hdivisors : RowOn (divisors.map (toPolynomial e)) {x} divisorSigns)
    (hremainders : RowOn
      ((divisors.map (fun d => (pseudoDivide dividend d).remainder)).map (toPolynomial e))
      {x} remainderSigns) :
    inferRootSign divisorSigns remainderSigns = some (sign (evalMap e dividend x)) ↔
      ∃ d ∈ divisors, evalMap e d x = 0 := by
  simpa [List.mem_map, toPolynomial_eval] using
    inferRootSign_point_rows (alignedRootSigns_pseudoRemainders e dividend divisors hleading)
      hdivisors hremainders

end DensePseudoRemainders

end MathUE.OrderedRealSignDiagram
