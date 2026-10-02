/-
One literal sure-core softening step at a positive full-debt global minimum.

Fix a quit-rate vector `v` in the unit box whose sure set `K = {k | v k = 1}`
has at least two members, and realize it by the one-date-then-Never profile at
the clamped product root of `v`.  Assume that this profile's terminal semantic
pair is a global minimum of total terminal semantic debt and that every one of
its coordinatewise debts is strictly positive.

Pick `p ∈ K` and soften only that coordinate, from `1` down to `x ∈ [0, 1]`.
Three exact structural facts drive the step.

* Every zero-tail root endpoint, and the opponents' all-Continue mass, is
  *affine* in the softened coordinate: it is the literal `x`-mixture of its two
  values at `x = 1` and `x = 0`.  This is coordinate multilinearity of the box
  polynomials, proved here once and for all.
* The unpadded cap of a one-date-then-Never profile is the maximum of the Quit
  endpoint and the Continue endpoint raised by the opponents' all-Continue mass
  times the positive part of the solo reward.  No sure opponent quitter is
  needed, which matters exactly because softening `p` can leave the last
  remaining sure quitter without one.
* Hence total debt along the segment is a finite sum of `max`-of-affine minus
  affine, so it satisfies the two-point convexity inequality, and each debt
  coordinate is continuous.

Continuity gives a radius on which every debt stays positive; convexity turns
the global minimum at `x = 1` into monotonicity away from it.  The step then
splits: either the softened target already has strictly larger total debt, in
which case the full member-leaving endpoint `x = 0` does too, or the softened
target is another attained full-debt global minimum whose sure set is exactly
`K.erase p`.  In both branches player `p`'s prescribed payoff strictly rises by
the exact stated fraction of its own debt.
-/
import FableProductBaseRealization
import UniformEquilibrium.Quitting.Root.TerminalSemanticEqualityStratum
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauIncidence
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPositiveSlopeRectangle

noncomputable section

namespace GameTheory

open _root_.Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## Clamped product roots

Working with a quit-rate *vector* rather than a vector of `PMF`s keeps the
softening algebra elementary, but the production hazard coin carries its two
range proofs as arguments.  Clamping the rate first removes those arguments
without changing anything on the unit box. -/

/-- The Boolean quitting law of a real hazard clamped to the unit interval. -/
def fableClampCoin (h : ℝ) : PMF Bool :=
  quittingHazardCoin (max 0 (min 1 h)) (le_max_left _ _)
    (max_le zero_le_one (min_le_left _ _))

@[simp] theorem fableClampCoin_true_toReal (h : ℝ) :
    (fableClampCoin h true).toReal = max 0 (min 1 h) :=
  quittingHazardCoin_true_toReal _ _ _

@[simp] theorem fableClampCoin_false_toReal (h : ℝ) :
    (fableClampCoin h false).toReal = 1 - max 0 (min 1 h) :=
  quittingHazardCoin_false_toReal _ _ _

/-- Two hazard coins at equal rates are the same law, whatever range proofs
they carry. -/
theorem fable_hazardCoin_congr {a b : ℝ} {ha0 : 0 ≤ a} {ha1 : a ≤ 1}
    {hb0 : 0 ≤ b} {hb1 : b ≤ 1} (h : a = b) :
    quittingHazardCoin a ha0 ha1 = quittingHazardCoin b hb0 hb1 := by
  subst h
  rfl

/-- The clamped product root of a real quit-rate vector. -/
def fableClampRoot (w : ι → ℝ) : ι → PMF Bool := fun k => fableClampCoin (w k)

omit [Fintype ι] [DecidableEq ι] in
/-- **Bridge.**  On the unit box the clamped root is the production
hazard-coin root of the same rate vector. -/
theorem fableClampRoot_eq_hazardCoin {w : ι → ℝ} (h0 : ∀ k, 0 ≤ w k)
    (h1 : ∀ k, w k ≤ 1) :
    fableClampRoot w = fun k => quittingHazardCoin (w k) (h0 k) (h1 k) := by
  funext k
  show fableClampCoin (w k) = _
  exact fable_hazardCoin_congr
    (by rw [min_eq_right (h1 k), max_eq_right (h0 k)])

omit [Fintype ι] [DecidableEq ι] in
/-- On the unit box the clamped root has the given quit rates. -/
theorem fableClampRoot_rates {w : ι → ℝ} (h0 : ∀ k, 0 ≤ w k)
    (h1 : ∀ k, w k ≤ 1) :
    (fun k => (fableClampRoot w k true).toReal) = w := by
  funext k
  show (fableClampCoin (w k) true).toReal = w k
  rw [fableClampCoin_true_toReal, min_eq_right (h1 k), max_eq_right (h0 k)]

omit [Fintype ι] [DecidableEq ι] in
/-- On the unit box the clamped root has the complementary continue rates. -/
theorem fableClampRoot_false_rate {w : ι → ℝ} (h0 : ∀ k, 0 ≤ w k)
    (h1 : ∀ k, w k ≤ 1) (k : ι) :
    (fableClampRoot w k false).toReal = 1 - w k := by
  show (fableClampCoin (w k) false).toReal = 1 - w k
  rw [fableClampCoin_false_toReal, min_eq_right (h1 k), max_eq_right (h0 k)]

/-! ## The unpadded cap without a sure opponent quitter -/

/-- **Unpadded cap formula.**  With no padding rows the behavioral
best-response cap of a one-date-then-Never profile is the maximum of the
zero-tail Quit endpoint and the zero-tail Continue endpoint raised by the
opponents' all-Continue mass times the positive part of the solo reward.  The
bare solo reward is not an argument, and no opponent needs to quit surely. -/
theorem fableQuittingContinuationBestResponseValue_oneDateThenNever
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι) :
    quittingContinuationBestResponseValue reward
        (quittingOneDateThenNeverProfile reward root) who =
      max (fableQuitEndpoint reward root who)
        (fableContinueEndpoint reward root who +
          fableOppContinue root who *
            max 0 (reward (quittingSingletonTerminal who) who)) := by
  have hmass : 0 ≤ fableOppContinue root who := fableOppContinue_nonneg root who
  have hpart : 0 ≤ fableOppContinue root who *
      max 0 (reward (quittingSingletonTerminal who) who) :=
    mul_nonneg hmass (le_max_left _ _)
  have hsolo : fableOppContinue root who *
        reward (quittingSingletonTerminal who) who ≤
      fableOppContinue root who *
        max 0 (reward (quittingSingletonTerminal who) who) :=
    mul_le_mul_of_nonneg_left (le_max_right _ _) hmass
  have hbdd := bddAbove_range_quittingPureTimeDeviationPayoff reward
    (quittingOneDateThenNeverProfile reward root) who
  rw [quittingContinuationBestResponseValue_eq_sSup_pureTimeDeviationPayoff]
  apply le_antisymm
  · refine csSup_le (Set.range_nonempty _) ?_
    rintro value ⟨choice, rfl⟩
    cases choice with
    | none =>
        rw [fablePureTimeDeviationPayoff_oneDateThenNever_none]
        refine le_trans ?_ (le_max_right _ _)
        linarith
    | some q =>
        cases q with
        | zero =>
            rw [fablePureTimeDeviationPayoff_oneDateThenNever_zero]
            exact le_max_left _ _
        | succ late =>
            rw [fablePureTimeDeviationPayoff_oneDateThenNever_succ]
            refine le_trans ?_ (le_max_right _ _)
            linarith
  · refine max_le ?_ ?_
    · rw [← fablePureTimeDeviationPayoff_oneDateThenNever_zero reward root who]
      exact le_csSup hbdd ⟨some 0, rfl⟩
    · rcases le_total 0 (reward (quittingSingletonTerminal who) who) with
        hpos | hnonpos
      · rw [max_eq_right hpos, ←
          fablePureTimeDeviationPayoff_oneDateThenNever_succ reward root who 0]
        exact le_csSup hbdd ⟨some (0 + 1), rfl⟩
      · rw [max_eq_left hnonpos, mul_zero, add_zero, ←
          fablePureTimeDeviationPayoff_oneDateThenNever_none reward root who]
        exact le_csSup hbdd ⟨none, rfl⟩

/-- The prescribed payoff of a one-date-then-Never profile is the observer's
own Quit/Continue mixture of the two zero-tail root endpoints. -/
theorem fable_terminalPayoff_oneDateThenNever
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι) :
    quittingTerminalPayoff reward
        (quittingOneDateThenNeverProfile reward root) who =
      (root who true).toReal * fableQuitEndpoint reward root who +
        (root who false).toReal * fableContinueEndpoint reward root who := by
  unfold quittingOneDateThenNeverProfile
  rw [quittingTerminalPayoff_rootThenContinuation_eq,
    fableTerminalPayoff_alwaysContinueProfile]
  exact quittingRootSuccessorPayoff_eq_endpointMix reward (0 : Payoff ι) root who

/-! ## Coordinate mixing of the box polynomials

Every box polynomial is multilinear, so overwriting a single quit-rate
coordinate by `x` produces exactly the `x`-mixture of the two values at that
coordinate's Boolean extremes.  This is the whole source of affinity along a
softening segment. -/

omit [Fintype ι] in
private theorem fable_prod_update_eq {p : ι} {u : ι → ℝ} {x : ℝ} {s : Finset ι}
    (h : p ∉ s) (g : ℝ → ℝ) :
    ∏ i ∈ s, g (Function.update u p x i) = ∏ i ∈ s, g (u i) :=
  Finset.prod_congr rfl fun i hi => by
    have hne : i ≠ p := by
      rintro rfl
      exact h hi
    rw [Function.update_of_ne hne]

/-- **Coordinate mixing of an exact coalition polynomial.** -/
theorem fable_boxCoalition_update_mix (u : ι → ℝ) (p : ι) (x : ℝ)
    (S : Finset ι) :
    fableBoxCoalition (Function.update u p x) S =
      x * fableBoxCoalition (Function.update u p 1) S +
        (1 - x) * fableBoxCoalition (Function.update u p 0) S := by
  by_cases hp : p ∈ S
  · have hcompl : p ∉ (Sᶜ : Finset ι) := by
      simp only [Finset.mem_compl, not_not]
      exact hp
    have hout : ∀ y : ℝ,
        ∏ i ∈ (Sᶜ : Finset ι), (1 - Function.update u p y i) =
          ∏ i ∈ (Sᶜ : Finset ι), (1 - u i) := fun y =>
      fable_prod_update_eq hcompl fun t => 1 - t
    have hin : ∀ y : ℝ, ∏ i ∈ S, Function.update u p y i =
        y * ∏ i ∈ S.erase p, u i := by
      intro y
      rw [← Finset.mul_prod_erase S _ hp, Function.update_self]
      exact congrArg _ (fable_prod_update_eq (Finset.notMem_erase p S) fun t => t)
    simp only [fableBoxCoalition, hout, hin]
    ring
  · have hcompl : p ∈ (Sᶜ : Finset ι) := by
      simp only [Finset.mem_compl]
      exact hp
    have hin : ∀ y : ℝ, ∏ i ∈ S, Function.update u p y i = ∏ i ∈ S, u i :=
      fun y => fable_prod_update_eq hp fun t => t
    have hout : ∀ y : ℝ,
        ∏ i ∈ (Sᶜ : Finset ι), (1 - Function.update u p y i) =
          (1 - y) * ∏ i ∈ (Sᶜ : Finset ι).erase p, (1 - u i) := by
      intro y
      rw [← Finset.mul_prod_erase _ _ hcompl, Function.update_self]
      exact congrArg _
        (fable_prod_update_eq (Finset.notMem_erase p _) fun t => 1 - t)
    simp only [fableBoxCoalition, hout, hin]
    ring

/-- Overwriting the observer's own coordinate before the endpoint substitution
has no effect. -/
theorem fable_endpointBox_update_self
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (u : ι → ℝ) (p : ι) (x bit : ℝ) :
    fableEndpointBox reward (Function.update u p x) p bit =
      fableEndpointBox reward u p bit := by
  unfold fableEndpointBox
  simp only [Function.update_idem]

/-- **Coordinate mixing of an endpoint polynomial.** -/
theorem fable_endpointBox_update_mix
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (u : ι → ℝ) (p : ι) (x : ℝ) (who : ι) (bit : ℝ) :
    fableEndpointBox reward (Function.update u p x) who bit =
      x * fableEndpointBox reward (Function.update u p 1) who bit +
        (1 - x) * fableEndpointBox reward (Function.update u p 0) who bit := by
  by_cases hwho : who = p
  · subst hwho
    rw [fable_endpointBox_update_self, fable_endpointBox_update_self,
      fable_endpointBox_update_self]
    ring
  · have hcomm : ∀ y : ℝ, Function.update (Function.update u p y) who bit =
        Function.update (Function.update u who bit) p y := fun y =>
      Function.update_comm (Ne.symm hwho) y bit u
    unfold fableEndpointBox
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun S _ => ?_
    rw [hcomm, hcomm, hcomm,
      fable_boxCoalition_update_mix (Function.update u who bit) p x S.val]
    ring

/-- **Coordinate mixing of the opponents' all-Continue polynomial.** -/
theorem fable_boxOppContinue_update_mix (u : ι → ℝ) (p : ι) (x : ℝ) (who : ι) :
    fableBoxOppContinue (Function.update u p x) who =
      x * fableBoxOppContinue (Function.update u p 1) who +
        (1 - x) * fableBoxOppContinue (Function.update u p 0) who := by
  by_cases hp : p ∈ Finset.univ.erase who
  · have hP : ∀ y : ℝ, fableBoxOppContinue (Function.update u p y) who =
        (1 - y) * ∏ i ∈ (Finset.univ.erase who).erase p, (1 - u i) := by
      intro y
      unfold fableBoxOppContinue
      rw [← Finset.mul_prod_erase _ _ hp, Function.update_self]
      exact congrArg _
        (fable_prod_update_eq (Finset.notMem_erase p _) fun t => 1 - t)
    rw [hP, hP, hP]
    ring
  · have hP : ∀ y : ℝ, fableBoxOppContinue (Function.update u p y) who =
        ∏ i ∈ Finset.univ.erase who, (1 - u i) := by
      intro y
      unfold fableBoxOppContinue
      exact fable_prod_update_eq hp fun t => 1 - t
    rw [hP, hP, hP]
    ring

/-! ## The softened target -/

/-- The one-date-then-Never profile at the clamped product root of a real
quit-rate vector. -/
def fableSoftProfile (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (w : ι → ℝ) : (quittingGame reward).BehaviorProfile :=
  quittingOneDateThenNeverProfile reward (fableClampRoot w)

/-- Its literal terminal semantic pair. -/
def fableSoftPair (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (w : ι → ℝ) : QuittingTerminalSemanticPair ι :=
  quittingTerminalSemanticPair reward (fableSoftProfile reward w)

theorem fableSoftPair_mem_carrier
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (w : ι → ℝ) :
    fableSoftPair reward w ∈ quittingTerminalSemanticCarrier reward :=
  quittingTerminalSemanticPair_mem_carrier reward (fableSoftProfile reward w)

/-! ## One sure-core softening step -/

/-- **Theorem C: one literal sure-core softening step.**  Let `v` be a
quit-rate vector in the unit box whose sure set is exactly `K`, let `p ∈ K`,
and let `K` have at least two members.  Assume the one-date-then-Never target
at `v` is a global minimum of total terminal semantic debt with every debt
coordinate strictly positive.  Then either the pure member-leaving target
obtained by dropping `p`'s rate to zero has strictly larger total debt, or some
strictly interior softening of `p` is again an attained full-debt global
minimum whose sure set is exactly `K.erase p`.  In both branches `p`'s
prescribed payoff rises by exactly the stated positive multiple of its own
debt at `v`. -/
theorem fable_sureCore_softening_step
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (v : ι → ℝ) (hv0 : ∀ k, 0 ≤ v k) (hv1 : ∀ k, v k ≤ 1)
    (K : Finset ι) (hK : ∀ k, k ∈ K ↔ v k = 1)
    (p : ι) (hp : p ∈ K) (hK2 : 1 < K.card)
    (hmin : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum (fableSoftPair reward v) ≤
        quittingTerminalSemanticDebtSum candidate)
    (hdebt : ∀ i, 0 < quittingTerminalSemanticDebt (fableSoftPair reward v) i) :
    (quittingTerminalSemanticDebtSum (fableSoftPair reward v) <
          quittingTerminalSemanticDebtSum
            (fableSoftPair reward (Function.update v p 0)) ∧
        fableSoftPair reward (Function.update v p 0) ∈
          quittingTerminalSemanticCarrier reward ∧
        (fableSoftPair reward (Function.update v p 0)).1 p =
          (fableSoftPair reward v).1 p +
            quittingTerminalSemanticDebt (fableSoftPair reward v) p) ∨
      (∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧
        quittingTerminalSemanticDebtSum
            (fableSoftPair reward (Function.update v p (1 - θ))) =
          quittingTerminalSemanticDebtSum (fableSoftPair reward v) ∧
        (∀ i, 0 < quittingTerminalSemanticDebt
          (fableSoftPair reward (Function.update v p (1 - θ))) i) ∧
        (fableSoftPair reward (Function.update v p (1 - θ))).1 p =
          (fableSoftPair reward v).1 p +
            θ * quittingTerminalSemanticDebt (fableSoftPair reward v) p ∧
        ∀ k, k ∈ K.erase p ↔ Function.update v p (1 - θ) k = 1) := by
  classical
  -- The softened coordinate and a second sure quitter.
  have hvp : v p = 1 := (hK p).mp hp
  have hup1 : Function.update v p (1 : ℝ) = v := by
    rw [← hvp]
    exact Function.update_eq_self p v
  obtain ⟨k', hk'⟩ : (K.erase p).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem hp]
    omega
  have hk'ne : k' ≠ p := Finset.ne_of_mem_erase hk'
  have hvk' : v k' = 1 := (hK k').mp (Finset.mem_of_mem_erase hk')
  -- The softened vector stays in the unit box.
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
  -- The endpoint constants at the two extremes of the softening segment.
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
  -- Affinity of the two endpoints and of the opponents' all-Continue mass.
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
  -- The prescribed payoff and the cap along the segment.
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
  -- The explicit debt curve.
  obtain ⟨dbt, hdbt⟩ : ∃ f : ι → ℝ → ℝ, ∀ i x, f i x =
      max (x * qe 1 i + (1 - x) * qe 0 i)
        ((x * ce 1 i + (1 - x) * ce 0 i) +
          (x * oc 1 i + (1 - x) * oc 0 i) * mm i) -
        (x * uu 1 i + (1 - x) * uu 0 i) := ⟨_, fun _ _ => rfl⟩
  have hdbt1 : ∀ i, dbt i 1 = max (qe 1 i) (ce 1 i + oc 1 i * mm i) - uu 1 i := by
    intro i
    rw [hdbt]
    norm_num
  have hdbt0 : ∀ i, dbt i 0 = max (qe 0 i) (ce 0 i + oc 0 i * mm i) - uu 0 i := by
    intro i
    rw [hdbt]
    norm_num
  have hdebtEq : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → ∀ i,
      quittingTerminalSemanticDebt
          (fableSoftPair reward (Function.update v p x)) i = dbt i x := by
    intro x hx0 hx1 i
    unfold quittingTerminalSemanticDebt
    rw [hdbt, hcap x hx0 hx1 i, hpay x hx0 hx1 i]
  have hsumEq : ∀ x : ℝ, 0 ≤ x → x ≤ 1 →
      quittingTerminalSemanticDebtSum
          (fableSoftPair reward (Function.update v p x)) = ∑ i, dbt i x := by
    intro x hx0 hx1
    unfold quittingTerminalSemanticDebtSum
    exact Finset.sum_congr rfl fun i _ => hdebtEq x hx0 hx1 i
  have hsum1 : quittingTerminalSemanticDebtSum (fableSoftPair reward v) =
      ∑ i, dbt i 1 := by
    rw [← hup1]
    exact hsumEq 1 zero_le_one le_rfl
  have hpos1 : ∀ i, 0 < dbt i 1 := by
    intro i
    rw [← hdebtEq 1 zero_le_one le_rfl i, hup1]
    exact hdebt i
  -- Continuity of each debt coordinate.
  have haff : ∀ a b : ℝ, Continuous fun x : ℝ => x * a + (1 - x) * b := by
    intro a b
    exact (continuous_id.mul continuous_const).add
      ((continuous_const.sub continuous_id).mul continuous_const)
  have hcont : ∀ i, Continuous fun x : ℝ => dbt i x := by
    intro i
    simp only [hdbt]
    exact ((haff _ _).max ((haff _ _).add ((haff _ _).mul continuous_const))).sub
      (haff _ _)
  -- A positivity radius around the unsoftened endpoint.
  have hopen : IsOpen {x : ℝ | ∀ i : ι, 0 < dbt i x} := by
    have hEq : {x : ℝ | ∀ i : ι, 0 < dbt i x} = ⋂ i : ι, {x : ℝ | 0 < dbt i x} := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
    rw [hEq]
    exact isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (hcont i)
  obtain ⟨eps, heps, hball⟩ := Metric.isOpen_iff.mp hopen 1 hpos1
  obtain ⟨θ, hθ0, hθhalf, hθeps⟩ : ∃ θ : ℝ, 0 < θ ∧ θ ≤ 1 / 2 ∧ θ < eps :=
    ⟨min (eps / 2) (1 / 2), lt_min (by linarith) (by norm_num), min_le_right _ _,
      lt_of_le_of_lt (min_le_left _ _) (by linarith)⟩
  have hx0 : (0 : ℝ) ≤ 1 - θ := by linarith
  have hx1 : (1 : ℝ) - θ ≤ 1 := by linarith
  have hmem : ∀ i, 0 < dbt i (1 - θ) := by
    refine hball ?_
    rw [Metric.mem_ball, Real.dist_eq, show (1 : ℝ) - θ - 1 = -θ by ring, abs_neg,
      abs_of_pos hθ0]
    exact hθeps
  -- The two-point convexity inequality for total debt.
  have hconvex : ∀ x : ℝ, 0 ≤ x → x ≤ 1 →
      ∑ i, dbt i x ≤ x * (∑ i, dbt i 1) + (1 - x) * (∑ i, dbt i 0) := by
    intro x hxa hxb
    have hxc : (0 : ℝ) ≤ 1 - x := by linarith
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    have hmax : max (x * qe 1 i + (1 - x) * qe 0 i)
        ((x * ce 1 i + (1 - x) * ce 0 i) + (x * oc 1 i + (1 - x) * oc 0 i) * mm i) ≤
        x * max (qe 1 i) (ce 1 i + oc 1 i * mm i) +
          (1 - x) * max (qe 0 i) (ce 0 i + oc 0 i * mm i) := by
      refine max_le ?_ ?_
      · exact add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) hxa)
          (mul_le_mul_of_nonneg_left (le_max_left _ _) hxc)
      · have hring : (x * ce 1 i + (1 - x) * ce 0 i) +
            (x * oc 1 i + (1 - x) * oc 0 i) * mm i =
            x * (ce 1 i + oc 1 i * mm i) + (1 - x) * (ce 0 i + oc 0 i * mm i) := by
          ring
        rw [hring]
        exact add_le_add (mul_le_mul_of_nonneg_left (le_max_right _ _) hxa)
          (mul_le_mul_of_nonneg_left (le_max_right _ _) hxc)
    rw [hdbt, hdbt1, hdbt0]
    have hring : x * (max (qe 1 i) (ce 1 i + oc 1 i * mm i) - uu 1 i) +
        (1 - x) * (max (qe 0 i) (ce 0 i + oc 0 i * mm i) - uu 0 i) =
        (x * max (qe 1 i) (ce 1 i + oc 1 i * mm i) +
            (1 - x) * max (qe 0 i) (ce 0 i + oc 0 i * mm i)) -
          (x * uu 1 i + (1 - x) * uu 0 i) := by
      ring
    rw [hring]
    linarith [hmax]
  -- Global minimality read on the segment.
  have hminSum : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → ∑ i, dbt i 1 ≤ ∑ i, dbt i x := by
    intro x hxa hxb
    rw [← hsum1, ← hsumEq x hxa hxb]
    exact hmin _ (fableSoftPair_mem_carrier reward (Function.update v p x))
  -- Player `p`'s own endpoints, cap, payoff and debt.
  have hocp1 : oc 1 p = 0 := by
    rw [hoc, hup1]
    unfold fableBoxOppContinue
    refine Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hk'ne, Finset.mem_univ k'⟩) ?_
    rw [hvk']
    ring
  have huu1p : uu 1 p = qe 1 p := by
    rw [huu, Function.update_self]
    ring
  have huu0p : uu 0 p = ce 1 p := by
    rw [huu, Function.update_self, hcep]
    ring
  have hltp : qe 1 p < ce 1 p := by
    have hpos := hpos1 p
    rw [hdbt1 p, hocp1, zero_mul, add_zero, huu1p] at hpos
    rcases le_or_gt (ce 1 p) (qe 1 p) with h | h
    · rw [max_eq_left h] at hpos
      linarith
    · exact h
  have hdbtp : dbt p 1 = ce 1 p - qe 1 p := by
    rw [hdbt1 p, hocp1, zero_mul, add_zero, huu1p, max_eq_right (le_of_lt hltp)]
  have hdebtp : quittingTerminalSemanticDebt (fableSoftPair reward v) p =
      ce 1 p - qe 1 p := by
    rw [← hup1, hdebtEq 1 zero_le_one le_rfl p, hdbtp]
  have hpayv : (fableSoftPair reward v).1 p = qe 1 p := by
    rw [← hup1, hpay 1 zero_le_one le_rfl p, huu1p]
    ring
  -- The dichotomy.
  rcases eq_or_lt_of_le (hminSum (1 - θ) hx0 hx1) with heq | hlt
  · right
    refine ⟨θ, hθ0, by linarith, ?_, ?_, ?_, ?_⟩
    · rw [hsumEq (1 - θ) hx0 hx1, hsum1]
      exact heq.symm
    · intro i
      rw [hdebtEq (1 - θ) hx0 hx1 i]
      exact hmem i
    · rw [hpay (1 - θ) hx0 hx1 p, hpayv, hdebtp, huu1p, huu0p]
      ring
    · intro k
      constructor
      · intro hk
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
        exact (hK k).mp (Finset.mem_of_mem_erase hk)
      · intro hkval
        have hkp : k ≠ p := by
          rintro rfl
          rw [Function.update_self] at hkval
          linarith
        rw [Function.update_of_ne hkp] at hkval
        exact Finset.mem_erase.mpr ⟨hkp, (hK k).mpr hkval⟩
  · left
    have hkey : ∑ i, dbt i 1 < ∑ i, dbt i 0 := by
      have hc := hconvex (1 - θ) hx0 hx1
      rcases le_or_gt (∑ i, dbt i 0) (∑ i, dbt i 1) with hcon | hgood
      · exfalso
        have h1 : θ * (∑ i, dbt i 0) ≤ θ * (∑ i, dbt i 1) :=
          mul_le_mul_of_nonneg_left hcon (le_of_lt hθ0)
        linarith
      · exact hgood
    refine ⟨?_, fableSoftPair_mem_carrier reward (Function.update v p 0), ?_⟩
    · rw [hsum1, hsumEq 0 le_rfl zero_le_one]
      exact hkey
    · rw [hpay 0 le_rfl zero_le_one p, hpayv, hdebtp, huu0p]
      ring

/-! ## The remaining sure quitter's singleton atom in an equality child -/

/-- **Positive singleton atom at a two-element sure core.**  If the sure set of
`v` is exactly `{p, k}` and `p`'s rate is softened to `1 - θ` with
`0 < θ < 1`, then the child's terminal law puts mass exactly
`θ * ∏ j ∉ K, (1 - v j)` on the singleton coalition `{k}`, and that mass is
strictly positive. -/
theorem fable_sureCore_softening_singletonMass
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (v : ι → ℝ) (hv0 : ∀ j, 0 ≤ v j) (hv1 : ∀ j, v j ≤ 1)
    (K : Finset ι) (hK : ∀ j, j ∈ K ↔ v j = 1)
    (p k : ι) (hp : p ∈ K) (herase : K.erase p = {k})
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    quittingTerminalOutcomeMass reward
          (fableSoftProfile reward (Function.update v p (1 - θ)))
          (some (quittingSingletonTerminal k)) =
        θ * ∏ j ∈ Finset.univ \ K, (1 - v j) ∧
      0 < θ * ∏ j ∈ Finset.univ \ K, (1 - v j) := by
  classical
  have hkerase : k ∈ K.erase p := by
    rw [herase]
    exact Finset.mem_singleton_self k
  have hkp : k ≠ p := Finset.ne_of_mem_erase hkerase
  have hvk : v k = 1 := (hK k).mp (Finset.mem_of_mem_erase hkerase)
  have hKeq : K = insert p {k} := by
    rw [← herase, Finset.insert_erase hp]
  have hub0 : ∀ j, 0 ≤ Function.update v p (1 - θ) j := by
    intro j
    by_cases hj : j = p
    · subst hj
      rw [Function.update_self]
      linarith
    · rw [Function.update_of_ne hj]
      exact hv0 j
  have hub1 : ∀ j, Function.update v p (1 - θ) j ≤ 1 := by
    intro j
    by_cases hj : j = p
    · subst hj
      rw [Function.update_self]
      linarith
    · rw [Function.update_of_ne hj]
      exact hv1 j
  have hrates := fableClampRoot_rates hub0 hub1
  have hsure :
      (fableClampRoot (Function.update v p (1 - θ)) k true).toReal = 1 := by
    rw [congrFun hrates k, Function.update_of_ne hkp, hvk]
  have hmass : quittingTerminalOutcomeMass reward
      (fableSoftProfile reward (Function.update v p (1 - θ)))
      (some (quittingSingletonTerminal k)) =
      fableBoxCoalition (Function.update v p (1 - θ)) {k} := by
    show quittingTerminalOutcomeMass reward
      (quittingOneDateThenNeverProfile reward
        (fableClampRoot (Function.update v p (1 - θ))))
      (some (quittingSingletonTerminal k)) = _
    rw [fable_terminalOutcomeMass_oneDateThenNever_some reward _ hsure,
      fable_coalitionMass_eq_boxCoalition, hrates]
    rfl
  have hpmem : p ∈ Finset.univ \ ({k} : Finset ι) := by
    rw [Finset.mem_sdiff, Finset.mem_singleton]
    exact ⟨Finset.mem_univ p, fun h => hkp h.symm⟩
  have hset : (Finset.univ \ ({k} : Finset ι)).erase p = Finset.univ \ K := by
    ext j
    simp only [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_univ, true_and,
      Finset.mem_singleton, hKeq, Finset.mem_insert, not_or]
  have hcong : ∏ j ∈ Finset.univ \ K, (1 - Function.update v p (1 - θ) j) =
      ∏ j ∈ Finset.univ \ K, (1 - v j) := by
    refine Finset.prod_congr rfl fun j hj => ?_
    have hjp : j ≠ p := by
      rintro rfl
      rw [Finset.mem_sdiff] at hj
      exact hj.2 hp
    rw [Function.update_of_ne hjp]
  have hbox : fableBoxCoalition (Function.update v p (1 - θ)) {k} =
      θ * ∏ j ∈ Finset.univ \ K, (1 - v j) := by
    unfold fableBoxCoalition
    rw [Finset.prod_singleton, Function.update_of_ne hkp, hvk,
      Finset.compl_eq_univ_sdiff, ← Finset.mul_prod_erase _ _ hpmem,
      Function.update_self, hset, hcong]
    ring
  have hprodpos : 0 < ∏ j ∈ Finset.univ \ K, (1 - v j) := by
    refine Finset.prod_pos fun j hj => ?_
    rw [Finset.mem_sdiff] at hj
    have hne : v j ≠ 1 := fun h => hj.2 ((hK j).mpr h)
    rcases lt_or_eq_of_le (hv1 j) with h | h
    · linarith
    · exact absurd h hne
  exact ⟨hmass.trans hbox, mul_pos hθ0 hprodpos⟩

end GameTheory
