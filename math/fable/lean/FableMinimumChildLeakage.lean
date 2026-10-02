/-
Exact leakage rates on the minimum-child softening segment.

Fix a quit-rate vector `v` in the unit box whose sure set `K = {k | v k = 1}`
has at least two members, pick `p ∈ K`, and realize `v` by the
one-date-then-Never profile at its clamped product root.  Assume that pair is a
global minimum of total terminal semantic debt with every coordinate debt
strictly positive.  Soften `p` alone, writing the softened vector as
`v[p ↦ 1 - θ]` for `θ ∈ [0, 1]`.

The softening step splits into two arms.  This file develops the *second* arm:
some interior `θ₀ ∈ (0, 1)` at which total debt is again the same global
minimum.  On the whole segment `[0, θ₀]` the transfer of debt away from the
mover is then pinned coordinatewise, not merely in aggregate.

Four facts, in order.

* Each coordinate debt along the segment is a maximum of two affine functions
  of `θ` minus an affine function of `θ`, so it satisfies the two-point
  convexity inequality.  This rests on the coordinate multilinearity of the box
  polynomials and on the unpadded cap formula, both taken from the softening
  file.
* Hence total debt is convex on `[0, θ₀]`, is bounded below by the global
  minimum, and agrees with it at both ends: it is constant there.
* A constant sum of convex summands forces every summand to be affine, because
  the summed two-point defects are nonnegative and add to zero.
* The mover's own opponents are untouched by the softening and still contain a
  sure quitter, so the mover's cap is frozen while its prescribed payoff is the
  literal `θ`-mixture of the two frozen endpoints.  Its debt is therefore
  exactly `(1 - θ)` times its debt at `v`, and the recipients absorb the
  complementary `θ` times that debt.

Nothing here needs a general theory of convex functions: every step is the
explicit two-point inequality for a max of affine functions, summed over a
finite index type.
-/
import FableSureCoreSoftening

noncomputable section

namespace GameTheory

open _root_.Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## The two-point inequality for a max of affine functions

A maximum of two affine functions minus an affine function satisfies the
midpoint-free two-point convexity inequality on every pair of arguments.  This
is the only convexity used in the file. -/

private theorem fable_maxAffine_two_point
    (aQ bQ aB bB aU bU x y t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    max (aQ + bQ * ((1 - t) * x + t * y)) (aB + bB * ((1 - t) * x + t * y)) -
        (aU + bU * ((1 - t) * x + t * y)) ≤
      (1 - t) * (max (aQ + bQ * x) (aB + bB * x) - (aU + bU * x)) +
        t * (max (aQ + bQ * y) (aB + bB * y) - (aU + bU * y)) := by
  have ht1' : (0 : ℝ) ≤ 1 - t := by linarith
  have eQ : aQ + bQ * ((1 - t) * x + t * y) =
      (1 - t) * (aQ + bQ * x) + t * (aQ + bQ * y) := by ring
  have eB : aB + bB * ((1 - t) * x + t * y) =
      (1 - t) * (aB + bB * x) + t * (aB + bB * y) := by ring
  have eU : aU + bU * ((1 - t) * x + t * y) =
      (1 - t) * (aU + bU * x) + t * (aU + bU * y) := by ring
  have hmax : max ((1 - t) * (aQ + bQ * x) + t * (aQ + bQ * y))
      ((1 - t) * (aB + bB * x) + t * (aB + bB * y)) ≤
      (1 - t) * max (aQ + bQ * x) (aB + bB * x) +
        t * max (aQ + bQ * y) (aB + bB * y) :=
    max_le
      (add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) ht1')
        (mul_le_mul_of_nonneg_left (le_max_left _ _) ht0))
      (add_le_add (mul_le_mul_of_nonneg_left (le_max_right _ _) ht1')
        (mul_le_mul_of_nonneg_left (le_max_right _ _) ht0))
  have hexp : (1 - t) * (max (aQ + bQ * x) (aB + bB * x) - (aU + bU * x)) +
      t * (max (aQ + bQ * y) (aB + bB * y) - (aU + bU * y)) =
      ((1 - t) * max (aQ + bQ * x) (aB + bB * x) +
          t * max (aQ + bQ * y) (aB + bB * y)) -
        ((1 - t) * (aU + bU * x) + t * (aU + bU * y)) := by ring
  rw [eQ, eB, eU, hexp]
  linarith

/-! ## Coordinate debt along the softening segment

The softening file proves the affinity of each zero-tail endpoint and of the
opponents' all-Continue mass in the softened coordinate *inside* the proof of
its softening step, as local `have`s rather than as standalone lemmas.  The
underlying multilinearity statements `fable_endpointBox_update_mix` and
`fable_boxOppContinue_update_mix` are public, so the affinity route is redone
here in the softening parameter `θ` rather than in the raw rate `1 - θ`. -/

/-- Every coordinate debt along the softening segment is a maximum of two
affine functions of `θ` minus an affine function of `θ`, hence satisfies the
two-point convexity inequality. -/
private theorem fable_minChild_debt_repr
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (v : ι → ℝ) (hv0 : ∀ k, 0 ≤ v k) (hv1 : ∀ k, v k ≤ 1) (p : ι) :
    ∃ dbt : ι → ℝ → ℝ,
      (∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 → ∀ i,
          quittingTerminalSemanticDebt
            (fableSoftPair reward (Function.update v p (1 - θ))) i = dbt i θ) ∧
        ∀ (i : ι) (x y t : ℝ), 0 ≤ t → t ≤ 1 →
          dbt i ((1 - t) * x + t * y) ≤ (1 - t) * dbt i x + t * dbt i y := by
  classical
  have hub0 : ∀ x : ℝ, 0 ≤ x → ∀ k, 0 ≤ Function.update v p x k := by
    intro x hx k
    by_cases hk : k = p
    · subst hk
      rwa [Function.update_self]
    · rw [Function.update_of_ne hk]
      exact hv0 k
  have hub1 : ∀ x : ℝ, x ≤ 1 → ∀ k, Function.update v p x k ≤ 1 := by
    intro x hx k
    by_cases hk : k = p
    · subst hk
      rwa [Function.update_self]
    · rw [Function.update_of_ne hk]
      exact hv1 k
  have hrates : ∀ x : ℝ, 0 ≤ x → x ≤ 1 →
      (fun k => (fableClampRoot (Function.update v p x) k true).toReal) =
        Function.update v p x :=
    fun x hx0 hx1 => fableClampRoot_rates (hub0 x hx0) (hub1 x hx1)
  obtain ⟨qe, hqe⟩ : ∃ f : ℝ → ι → ℝ, ∀ b i,
      f b i = fableEndpointBox reward (Function.update v p b) i 1 :=
    ⟨_, fun _ _ => rfl⟩
  obtain ⟨ce, hce⟩ : ∃ f : ℝ → ι → ℝ, ∀ b i,
      f b i = fableEndpointBox reward (Function.update v p b) i 0 :=
    ⟨_, fun _ _ => rfl⟩
  obtain ⟨oc, hoc⟩ : ∃ f : ℝ → ι → ℝ, ∀ b i,
      f b i = fableBoxOppContinue (Function.update v p b) i :=
    ⟨_, fun _ _ => rfl⟩
  obtain ⟨mm, hmm⟩ : ∃ f : ι → ℝ, ∀ i,
      f i = max 0 (reward (quittingSingletonTerminal i) i) := ⟨_, fun _ => rfl⟩
  obtain ⟨uu, huu⟩ : ∃ f : ℝ → ι → ℝ, ∀ b i,
      f b i = Function.update v p b i * qe b i +
        (1 - Function.update v p b i) * ce b i := ⟨_, fun _ _ => rfl⟩
  have hqep : qe 1 p = qe 0 p := by
    rw [hqe, hqe, fable_endpointBox_update_self, fable_endpointBox_update_self]
  have hcep : ce 1 p = ce 0 p := by
    rw [hce, hce, fable_endpointBox_update_self, fable_endpointBox_update_self]
  have hQ : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → ∀ i,
      fableQuitEndpoint reward (fableClampRoot (Function.update v p x)) i =
        x * qe 1 i + (1 - x) * qe 0 i := by
    intro x hx0 hx1 i
    rw [fableQuitEndpoint_eq_endpointBox, hrates x hx0 hx1, hqe, hqe]
    exact fable_endpointBox_update_mix reward v p x i 1
  have hC : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → ∀ i,
      fableContinueEndpoint reward (fableClampRoot (Function.update v p x)) i =
        x * ce 1 i + (1 - x) * ce 0 i := by
    intro x hx0 hx1 i
    rw [fableContinueEndpoint_eq_endpointBox, hrates x hx0 hx1, hce, hce]
    exact fable_endpointBox_update_mix reward v p x i 0
  have hO : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → ∀ i,
      fableOppContinue (fableClampRoot (Function.update v p x)) i =
        x * oc 1 i + (1 - x) * oc 0 i := by
    intro x hx0 hx1 i
    rw [fableOppContinue_eq_boxOppContinue, hrates x hx0 hx1, hoc, hoc]
    exact fable_boxOppContinue_update_mix v p x i
  have hpay : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → ∀ i,
      (fableSoftPair reward (Function.update v p x)).1 i =
        x * uu 1 i + (1 - x) * uu 0 i := by
    intro x hx0 hx1 i
    have hrate : (fableClampRoot (Function.update v p x) i true).toReal =
        Function.update v p x i := congrFun (hrates x hx0 hx1) i
    have hrate' : (fableClampRoot (Function.update v p x) i false).toReal =
        1 - Function.update v p x i :=
      fableClampRoot_false_rate (hub0 x hx0) (hub1 x hx1) i
    show quittingTerminalPayoff reward
        (quittingOneDateThenNeverProfile reward
          (fableClampRoot (Function.update v p x))) i = _
    rw [fable_terminalPayoff_oneDateThenNever, hrate, hrate',
      hQ x hx0 hx1 i, hC x hx0 hx1 i]
    simp only [huu]
    by_cases hip : i = p
    · subst hip
      simp only [Function.update_self, hqep, hcep]
      ring
    · simp only [Function.update_of_ne hip]
      ring
  have hcap : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → ∀ i,
      (fableSoftPair reward (Function.update v p x)).2 i =
        max (x * qe 1 i + (1 - x) * qe 0 i)
          ((x * ce 1 i + (1 - x) * ce 0 i) +
            (x * oc 1 i + (1 - x) * oc 0 i) * mm i) := by
    intro x hx0 hx1 i
    show quittingContinuationBestResponseValue reward
        (quittingOneDateThenNeverProfile reward
          (fableClampRoot (Function.update v p x))) i = _
    rw [fableQuittingContinuationBestResponseValue_oneDateThenNever,
      hQ x hx0 hx1 i, hC x hx0 hx1 i, hO x hx0 hx1 i, hmm]
  refine ⟨fun i θ =>
      max (qe 1 i + (qe 0 i - qe 1 i) * θ)
        (ce 1 i + oc 1 i * mm i +
          (ce 0 i - ce 1 i + (oc 0 i - oc 1 i) * mm i) * θ) -
        (uu 1 i + (uu 0 i - uu 1 i) * θ), ?_, ?_⟩
  · intro θ hθ0 hθ1 i
    have hx0 : (0 : ℝ) ≤ 1 - θ := by linarith
    have hx1 : (1 : ℝ) - θ ≤ 1 := by linarith
    have e1 : (1 - θ) * qe 1 i + (1 - (1 - θ)) * qe 0 i =
        qe 1 i + (qe 0 i - qe 1 i) * θ := by ring
    have e2 : (1 - θ) * ce 1 i + (1 - (1 - θ)) * ce 0 i +
        ((1 - θ) * oc 1 i + (1 - (1 - θ)) * oc 0 i) * mm i =
        ce 1 i + oc 1 i * mm i +
          (ce 0 i - ce 1 i + (oc 0 i - oc 1 i) * mm i) * θ := by ring
    have e3 : (1 - θ) * uu 1 i + (1 - (1 - θ)) * uu 0 i =
        uu 1 i + (uu 0 i - uu 1 i) * θ := by ring
    show quittingTerminalSemanticDebt
        (fableSoftPair reward (Function.update v p (1 - θ))) i =
      max (qe 1 i + (qe 0 i - qe 1 i) * θ)
          (ce 1 i + oc 1 i * mm i +
            (ce 0 i - ce 1 i + (oc 0 i - oc 1 i) * mm i) * θ) -
        (uu 1 i + (uu 0 i - uu 1 i) * θ)
    unfold quittingTerminalSemanticDebt
    rw [hcap (1 - θ) hx0 hx1 i, hpay (1 - θ) hx0 hx1 i, e1, e2, e3]
  · intro i x y t ht0 ht1
    exact fable_maxAffine_two_point (qe 1 i) (qe 0 i - qe 1 i)
      (ce 1 i + oc 1 i * mm i)
      (ce 0 i - ce 1 i + (oc 0 i - oc 1 i) * mm i) (uu 1 i)
      (uu 0 i - uu 1 i) x y t ht0 ht1

/-! ## The mover's exact rate

Softening `p` changes no opponent of `p`, and `K` has a second member, so `p`
still faces a sure quitter: its opponents' all-Continue mass stays zero and its
cap is the frozen maximum of its two frozen endpoints.  Only its prescribed
payoff moves, and it moves affinely. -/

/-- **The mover's debt decays exactly linearly.**  Under the hypotheses of the
softening step, the softened player's terminal semantic debt at `v[p ↦ 1 - θ]`
is `(1 - θ)` times its debt at `v`, for every `θ` in `[0, 1]`. -/
theorem fable_minimumChild_mover_debt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (v : ι → ℝ) (hv0 : ∀ k, 0 ≤ v k) (hv1 : ∀ k, v k ≤ 1)
    (K : Finset ι) (hK : ∀ k, k ∈ K ↔ v k = 1)
    (p : ι) (hp : p ∈ K) (hK2 : 1 < K.card)
    (hdebt : 0 < quittingTerminalSemanticDebt (fableSoftPair reward v) p) :
    ∀ θ ∈ Set.Icc (0 : ℝ) 1,
      quittingTerminalSemanticDebt
          (fableSoftPair reward (Function.update v p (1 - θ))) p =
        (1 - θ) * quittingTerminalSemanticDebt (fableSoftPair reward v) p := by
  classical
  have hvp : v p = 1 := (hK p).mp hp
  have hup1 : Function.update v p (1 : ℝ) = v := by
    rw [← hvp]
    exact Function.update_eq_self p v
  obtain ⟨k', hk'⟩ : (K.erase p).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem hp]
    omega
  have hk'ne : k' ≠ p := Finset.ne_of_mem_erase hk'
  have hvk' : v k' = 1 := (hK k').mp (Finset.mem_of_mem_erase hk')
  have hub0 : ∀ x : ℝ, 0 ≤ x → ∀ k, 0 ≤ Function.update v p x k := by
    intro x hx k
    by_cases hk : k = p
    · subst hk
      rwa [Function.update_self]
    · rw [Function.update_of_ne hk]
      exact hv0 k
  have hub1 : ∀ x : ℝ, x ≤ 1 → ∀ k, Function.update v p x k ≤ 1 := by
    intro x hx k
    by_cases hk : k = p
    · subst hk
      rwa [Function.update_self]
    · rw [Function.update_of_ne hk]
      exact hv1 k
  have hrates : ∀ x : ℝ, 0 ≤ x → x ≤ 1 →
      (fun k => (fableClampRoot (Function.update v p x) k true).toReal) =
        Function.update v p x :=
    fun x hx0 hx1 => fableClampRoot_rates (hub0 x hx0) (hub1 x hx1)
  obtain ⟨Qp, hQpDef⟩ : ∃ r : ℝ, r = fableEndpointBox reward v p 1 := ⟨_, rfl⟩
  obtain ⟨Cp, hCpDef⟩ : ∃ r : ℝ, r = fableEndpointBox reward v p 0 := ⟨_, rfl⟩
  have hQP : ∀ x : ℝ, 0 ≤ x → x ≤ 1 →
      fableQuitEndpoint reward (fableClampRoot (Function.update v p x)) p =
        Qp := by
    intro x hx0 hx1
    rw [fableQuitEndpoint_eq_endpointBox, hrates x hx0 hx1, hQpDef]
    exact fable_endpointBox_update_self reward v p x 1
  have hCP : ∀ x : ℝ, 0 ≤ x → x ≤ 1 →
      fableContinueEndpoint reward (fableClampRoot (Function.update v p x)) p =
        Cp := by
    intro x hx0 hx1
    rw [fableContinueEndpoint_eq_endpointBox, hrates x hx0 hx1, hCpDef]
    exact fable_endpointBox_update_self reward v p x 0
  have hOP : ∀ x : ℝ, 0 ≤ x → x ≤ 1 →
      fableOppContinue (fableClampRoot (Function.update v p x)) p = 0 := by
    intro x hx0 hx1
    rw [fableOppContinue_eq_boxOppContinue, hrates x hx0 hx1]
    unfold fableBoxOppContinue
    refine Finset.prod_eq_zero
      (Finset.mem_erase.mpr ⟨hk'ne, Finset.mem_univ k'⟩) ?_
    rw [Function.update_of_ne hk'ne, hvk']
    ring
  have hcapP : ∀ x : ℝ, 0 ≤ x → x ≤ 1 →
      (fableSoftPair reward (Function.update v p x)).2 p = max Qp Cp := by
    intro x hx0 hx1
    show quittingContinuationBestResponseValue reward
        (quittingOneDateThenNeverProfile reward
          (fableClampRoot (Function.update v p x))) p = _
    rw [fableQuittingContinuationBestResponseValue_oneDateThenNever,
      hQP x hx0 hx1, hCP x hx0 hx1, hOP x hx0 hx1, zero_mul, add_zero]
  have hpayP : ∀ x : ℝ, 0 ≤ x → x ≤ 1 →
      (fableSoftPair reward (Function.update v p x)).1 p =
        x * Qp + (1 - x) * Cp := by
    intro x hx0 hx1
    have hrate : (fableClampRoot (Function.update v p x) p true).toReal = x := by
      rw [congrFun (hrates x hx0 hx1) p, Function.update_self]
    have hrate' :
        (fableClampRoot (Function.update v p x) p false).toReal = 1 - x := by
      rw [fableClampRoot_false_rate (hub0 x hx0) (hub1 x hx1) p,
        Function.update_self]
    show quittingTerminalPayoff reward
        (quittingOneDateThenNeverProfile reward
          (fableClampRoot (Function.update v p x))) p = _
    rw [fable_terminalPayoff_oneDateThenNever, hrate, hrate',
      hQP x hx0 hx1, hCP x hx0 hx1]
  have hdebtP : ∀ x : ℝ, 0 ≤ x → x ≤ 1 →
      quittingTerminalSemanticDebt
          (fableSoftPair reward (Function.update v p x)) p =
        max Qp Cp - (x * Qp + (1 - x) * Cp) := by
    intro x hx0 hx1
    unfold quittingTerminalSemanticDebt
    rw [hcapP x hx0 hx1, hpayP x hx0 hx1]
  have hbase : quittingTerminalSemanticDebt (fableSoftPair reward v) p =
      max Qp Cp - Qp := by
    rw [← hup1, hdebtP 1 zero_le_one le_rfl]
    ring
  have hlt : Qp < Cp := by
    rcases le_or_gt Cp Qp with hle | hgt
    · rw [hbase, max_eq_left hle] at hdebt
      linarith
    · exact hgt
  have hbase' : quittingTerminalSemanticDebt (fableSoftPair reward v) p =
      Cp - Qp := by
    rw [hbase, max_eq_right (le_of_lt hlt)]
  intro θ hθ
  rw [Set.mem_Icc] at hθ
  obtain ⟨hθ0, hθ1⟩ := hθ
  have hx0 : (0 : ℝ) ≤ 1 - θ := by linarith
  have hx1 : (1 : ℝ) - θ ≤ 1 := by linarith
  rw [hdebtP (1 - θ) hx0 hx1, hbase', max_eq_right (le_of_lt hlt)]
  ring

/-! ## Constancy of total debt on the segment -/

/-- **Interval constancy.**  If the softened target at some interior `θ₀`
attains the same total terminal semantic debt as the global minimum at `v`,
then every intermediate softening attains it too. -/
theorem fable_minimumChild_debtSum_const
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (v : ι → ℝ) (hv0 : ∀ k, 0 ≤ v k) (hv1 : ∀ k, v k ≤ 1)
    (K : Finset ι) (hK : ∀ k, k ∈ K ↔ v k = 1) (p : ι) (hp : p ∈ K)
    (hmin : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum (fableSoftPair reward v) ≤
        quittingTerminalSemanticDebtSum candidate)
    (θ₀ : ℝ) (hθ₀0 : 0 < θ₀) (hθ₀1 : θ₀ < 1)
    (heq : quittingTerminalSemanticDebtSum
        (fableSoftPair reward (Function.update v p (1 - θ₀))) =
      quittingTerminalSemanticDebtSum (fableSoftPair reward v)) :
    ∀ θ ∈ Set.Icc (0 : ℝ) θ₀,
      quittingTerminalSemanticDebtSum
          (fableSoftPair reward (Function.update v p (1 - θ))) =
        quittingTerminalSemanticDebtSum (fableSoftPair reward v) := by
  classical
  obtain ⟨dbt, hrepr, hconv⟩ := fable_minChild_debt_repr reward v hv0 hv1 p
  have hθ₀le : θ₀ ≤ 1 := le_of_lt hθ₀1
  have hθ₀ne : θ₀ ≠ 0 := ne_of_gt hθ₀0
  have hvp : v p = 1 := (hK p).mp hp
  have hsoft0 : Function.update v p (1 - (0 : ℝ)) = v := by
    rw [sub_zero, ← hvp]
    exact Function.update_eq_self p v
  have hsum : ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 →
      quittingTerminalSemanticDebtSum
        (fableSoftPair reward (Function.update v p (1 - θ))) = ∑ i, dbt i θ := by
    intro θ h0 h1
    unfold quittingTerminalSemanticDebtSum
    exact Finset.sum_congr rfl fun i _ => hrepr θ h0 h1 i
  have hsum0 : quittingTerminalSemanticDebtSum (fableSoftPair reward v) =
      ∑ i, dbt i 0 := by
    rw [← hsoft0]
    exact hsum 0 le_rfl zero_le_one
  have hminSum : ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 → ∑ i, dbt i 0 ≤ ∑ i, dbt i θ := by
    intro θ h0 h1
    rw [← hsum0, ← hsum θ h0 h1]
    exact hmin _ (fableSoftPair_mem_carrier reward (Function.update v p (1 - θ)))
  have hend : ∑ i, dbt i θ₀ = ∑ i, dbt i 0 := by
    rw [← hsum θ₀ (le_of_lt hθ₀0) hθ₀le, ← hsum0]
    exact heq
  have hconvSum : ∀ x y t : ℝ, 0 ≤ t → t ≤ 1 →
      ∑ i, dbt i ((1 - t) * x + t * y) ≤
        (1 - t) * (∑ i, dbt i x) + t * (∑ i, dbt i y) := by
    intro x y t ht0 ht1
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun i _ => hconv i x y t ht0 ht1
  intro θ hθ
  rw [Set.mem_Icc] at hθ
  obtain ⟨hθa, hθb⟩ := hθ
  have hθ1 : θ ≤ 1 := le_trans hθb hθ₀le
  have ht0 : 0 ≤ θ / θ₀ := div_nonneg hθa (le_of_lt hθ₀0)
  have ht1 : θ / θ₀ ≤ 1 := (div_le_one hθ₀0).mpr hθb
  have hmix : (1 - θ / θ₀) * 0 + (θ / θ₀) * θ₀ = θ := by
    field_simp
    ring
  have hupper : ∑ i, dbt i θ ≤ ∑ i, dbt i 0 := by
    have h := hconvSum 0 θ₀ (θ / θ₀) ht0 ht1
    rw [hmix, hend] at h
    linarith
  have hlower := hminSum θ hθa hθ1
  rw [hsum θ hθa hθ1, hsum0]
  linarith

/-! ## Coordinatewise affinity -/

/-- **Coordinate affinity.**  On the minimum-child segment every coordinate of
terminal semantic debt is an affine function of the softening parameter. -/
theorem fable_minimumChild_debt_affine
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (v : ι → ℝ) (hv0 : ∀ k, 0 ≤ v k) (hv1 : ∀ k, v k ≤ 1)
    (K : Finset ι) (hK : ∀ k, k ∈ K ↔ v k = 1) (p : ι) (hp : p ∈ K)
    (hmin : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum (fableSoftPair reward v) ≤
        quittingTerminalSemanticDebtSum candidate)
    (θ₀ : ℝ) (hθ₀0 : 0 < θ₀) (hθ₀1 : θ₀ < 1)
    (heq : quittingTerminalSemanticDebtSum
        (fableSoftPair reward (Function.update v p (1 - θ₀))) =
      quittingTerminalSemanticDebtSum (fableSoftPair reward v)) :
    ∀ i : ι, ∃ a b : ℝ, ∀ θ ∈ Set.Icc (0 : ℝ) θ₀,
      quittingTerminalSemanticDebt
          (fableSoftPair reward (Function.update v p (1 - θ))) i = a + b * θ := by
  classical
  obtain ⟨dbt, hrepr, hconv⟩ := fable_minChild_debt_repr reward v hv0 hv1 p
  have hθ₀le : θ₀ ≤ 1 := le_of_lt hθ₀1
  have hθ₀ne : θ₀ ≠ 0 := ne_of_gt hθ₀0
  have hvp : v p = 1 := (hK p).mp hp
  have hsoft0 : Function.update v p (1 - (0 : ℝ)) = v := by
    rw [sub_zero, ← hvp]
    exact Function.update_eq_self p v
  have hsum : ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 →
      quittingTerminalSemanticDebtSum
        (fableSoftPair reward (Function.update v p (1 - θ))) = ∑ i, dbt i θ := by
    intro θ h0 h1
    unfold quittingTerminalSemanticDebtSum
    exact Finset.sum_congr rfl fun i _ => hrepr θ h0 h1 i
  have hsum0 : quittingTerminalSemanticDebtSum (fableSoftPair reward v) =
      ∑ i, dbt i 0 := by
    rw [← hsoft0]
    exact hsum 0 le_rfl zero_le_one
  have hZ1 := fable_minimumChild_debtSum_const reward v hv0 hv1 K hK p hp hmin
    θ₀ hθ₀0 hθ₀1 heq
  have hconst : ∀ θ : ℝ, 0 ≤ θ → θ ≤ θ₀ → ∑ i, dbt i θ = ∑ i, dbt i 0 := by
    intro θ h0 h1
    rw [← hsum θ h0 (le_trans h1 hθ₀le), ← hsum0]
    exact hZ1 θ (Set.mem_Icc.mpr ⟨h0, h1⟩)
  have hkey : ∀ θ : ℝ, 0 ≤ θ → θ ≤ θ₀ → ∀ i,
      dbt i θ = (1 - θ / θ₀) * dbt i 0 + (θ / θ₀) * dbt i θ₀ := by
    intro θ h0 h1 i
    have ht0 : 0 ≤ θ / θ₀ := div_nonneg h0 (le_of_lt hθ₀0)
    have ht1 : θ / θ₀ ≤ 1 := (div_le_one hθ₀0).mpr h1
    have hmix : (1 - θ / θ₀) * 0 + (θ / θ₀) * θ₀ = θ := by
      field_simp
      ring
    have hnn : ∀ j ∈ (Finset.univ : Finset ι),
        0 ≤ (1 - θ / θ₀) * dbt j 0 + (θ / θ₀) * dbt j θ₀ - dbt j θ := by
      intro j _
      have h := hconv j 0 θ₀ (θ / θ₀) ht0 ht1
      rw [hmix] at h
      linarith
    have hsplit :
        ∑ j, ((1 - θ / θ₀) * dbt j 0 + (θ / θ₀) * dbt j θ₀ - dbt j θ) =
        ((1 - θ / θ₀) * ∑ j, dbt j 0 + (θ / θ₀) * ∑ j, dbt j θ₀) -
          ∑ j, dbt j θ := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
        ← Finset.sum_sub_distrib]
    have hzero :
        ∑ j, ((1 - θ / θ₀) * dbt j 0 + (θ / θ₀) * dbt j θ₀ - dbt j θ) = 0 := by
      rw [hsplit, hconst θ h0 h1, hconst θ₀ (le_of_lt hθ₀0) le_rfl]
      ring
    have hj := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hzero i (Finset.mem_univ i)
    linarith
  intro i
  refine ⟨dbt i 0, (dbt i θ₀ - dbt i 0) / θ₀, ?_⟩
  intro θ hθ
  rw [Set.mem_Icc] at hθ
  rw [hrepr θ hθ.1 (le_trans hθ.2 hθ₀le) i, hkey θ hθ.1 hθ.2 i]
  ring

/-! ## The recipients' law -/

/-- **Recipients' law.**  On the minimum-child segment the debt the softened
player sheds is absorbed exactly by the other players: the total change in
their debts is `θ` times the mover's debt at `v`. -/
theorem fable_minimumChild_leakage_sum
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (v : ι → ℝ) (hv0 : ∀ k, 0 ≤ v k) (hv1 : ∀ k, v k ≤ 1)
    (K : Finset ι) (hK : ∀ k, k ∈ K ↔ v k = 1)
    (p : ι) (hp : p ∈ K) (hK2 : 1 < K.card)
    (hmin : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum (fableSoftPair reward v) ≤
        quittingTerminalSemanticDebtSum candidate)
    (hdebt : ∀ i, 0 < quittingTerminalSemanticDebt (fableSoftPair reward v) i)
    (θ₀ : ℝ) (hθ₀0 : 0 < θ₀) (hθ₀1 : θ₀ < 1)
    (heq : quittingTerminalSemanticDebtSum
        (fableSoftPair reward (Function.update v p (1 - θ₀))) =
      quittingTerminalSemanticDebtSum (fableSoftPair reward v)) :
    ∀ θ ∈ Set.Icc (0 : ℝ) θ₀,
      ∑ i ∈ Finset.univ.erase p,
          (quittingTerminalSemanticDebt
              (fableSoftPair reward (Function.update v p (1 - θ))) i -
            quittingTerminalSemanticDebt (fableSoftPair reward v) i) =
        θ * quittingTerminalSemanticDebt (fableSoftPair reward v) p := by
  classical
  intro θ hθ
  rw [Set.mem_Icc] at hθ
  obtain ⟨hθa, hθb⟩ := hθ
  have hθ1 : θ ≤ 1 := le_trans hθb (le_of_lt hθ₀1)
  have hZ1 := fable_minimumChild_debtSum_const reward v hv0 hv1 K hK p hp hmin
    θ₀ hθ₀0 hθ₀1 heq θ (Set.mem_Icc.mpr ⟨hθa, hθb⟩)
  have hZ3 := fable_minimumChild_mover_debt reward v hv0 hv1 K hK p hp hK2
    (hdebt p) θ (Set.mem_Icc.mpr ⟨hθa, hθ1⟩)
  unfold quittingTerminalSemanticDebtSum at hZ1
  have hsplitA : quittingTerminalSemanticDebt
        (fableSoftPair reward (Function.update v p (1 - θ))) p +
      ∑ i ∈ Finset.univ.erase p, quittingTerminalSemanticDebt
        (fableSoftPair reward (Function.update v p (1 - θ))) i =
      ∑ i, quittingTerminalSemanticDebt
        (fableSoftPair reward (Function.update v p (1 - θ))) i :=
    Finset.add_sum_erase _ _ (Finset.mem_univ p)
  have hsplitB : quittingTerminalSemanticDebt (fableSoftPair reward v) p +
      ∑ i ∈ Finset.univ.erase p,
        quittingTerminalSemanticDebt (fableSoftPair reward v) i =
      ∑ i, quittingTerminalSemanticDebt (fableSoftPair reward v) i :=
    Finset.add_sum_erase _ _ (Finset.mem_univ p)
  rw [Finset.sum_sub_distrib]
  linarith [hsplitA, hsplitB, hZ1, hZ3]

/-- **Per-recipient rates.**  On the minimum-child segment each player's debt
change is a fixed real rate times the softening parameter, and the recipients'
rates sum to exactly the mover's debt at `v`. -/
theorem fable_minimumChild_leakage_rates
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (v : ι → ℝ) (hv0 : ∀ k, 0 ≤ v k) (hv1 : ∀ k, v k ≤ 1)
    (K : Finset ι) (hK : ∀ k, k ∈ K ↔ v k = 1)
    (p : ι) (hp : p ∈ K) (hK2 : 1 < K.card)
    (hmin : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum (fableSoftPair reward v) ≤
        quittingTerminalSemanticDebtSum candidate)
    (hdebt : ∀ i, 0 < quittingTerminalSemanticDebt (fableSoftPair reward v) i)
    (θ₀ : ℝ) (hθ₀0 : 0 < θ₀) (hθ₀1 : θ₀ < 1)
    (heq : quittingTerminalSemanticDebtSum
        (fableSoftPair reward (Function.update v p (1 - θ₀))) =
      quittingTerminalSemanticDebtSum (fableSoftPair reward v)) :
    ∃ rate : ι → ℝ,
      (∀ (i : ι), ∀ θ ∈ Set.Icc (0 : ℝ) θ₀,
          quittingTerminalSemanticDebt
              (fableSoftPair reward (Function.update v p (1 - θ))) i -
            quittingTerminalSemanticDebt (fableSoftPair reward v) i =
          rate i * θ) ∧
        ∑ i ∈ Finset.univ.erase p, rate i =
          quittingTerminalSemanticDebt (fableSoftPair reward v) p := by
  classical
  have haff := fable_minimumChild_debt_affine reward v hv0 hv1 K hK p hp hmin
    θ₀ hθ₀0 hθ₀1 heq
  choose a b hab using haff
  have hvp : v p = 1 := (hK p).mp hp
  have hsoft0 : Function.update v p (1 - (0 : ℝ)) = v := by
    rw [sub_zero, ← hvp]
    exact Function.update_eq_self p v
  have hzeroMem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) θ₀ :=
    Set.mem_Icc.mpr ⟨le_rfl, le_of_lt hθ₀0⟩
  have hfullMem : θ₀ ∈ Set.Icc (0 : ℝ) θ₀ :=
    Set.mem_Icc.mpr ⟨le_of_lt hθ₀0, le_rfl⟩
  have hbase : ∀ i,
      quittingTerminalSemanticDebt (fableSoftPair reward v) i = a i := by
    intro i
    have h := hab i 0 hzeroMem
    rw [hsoft0] at h
    rw [h]
    ring
  refine ⟨b, ?_, ?_⟩
  · intro i θ hθ
    rw [hab i θ hθ, hbase i]
    ring
  · have hsum := fable_minimumChild_leakage_sum reward v hv0 hv1 K hK p hp hK2
      hmin hdebt θ₀ hθ₀0 hθ₀1 heq θ₀ hfullMem
    have hrepl : ∑ i ∈ Finset.univ.erase p,
        (quittingTerminalSemanticDebt
            (fableSoftPair reward (Function.update v p (1 - θ₀))) i -
          quittingTerminalSemanticDebt (fableSoftPair reward v) i) =
        (∑ i ∈ Finset.univ.erase p, b i) * θ₀ := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hab i θ₀ hfullMem, hbase i]
      ring
    rw [hrepl] at hsum
    refine mul_right_cancel₀ (ne_of_gt hθ₀0) ?_
    rw [hsum]
    ring

end GameTheory
