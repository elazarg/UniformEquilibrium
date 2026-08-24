/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.Probability.HarmonicStaticTransientVariation

/-!
# Backward-harmonic variation with one transient state

The scalar core is a one-atom peeling inequality.  If a unit-interval random variable has
mean `a`, and one distinguished atom has mass `q` and value `b`, then its mean absolute
deviation from `a`, together with the surviving Bernoulli potential of that atom, is at most
the Bernoulli potential of `a`.

For a finite Markov kernel with one transient state, this potential pays the variation at that
state.  Variation vanishes on the recurrent core, so the expected potential telescopes in
time.  This gives the sharp bound one for every bounded backward-harmonic orbit.
-/

namespace Math.Probability

noncomputable section

variable {Omega : Type*} [Fintype Omega] [DecidableEq Omega]

private theorem geometricBinaryPeeling_case_ge
    (q b e : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (hbe : e ≤ b) :
    (1 - q) * (q * b + (1 - q) * e) * (1 - e) + q * Real.sqrt (b * (1 - b)) ≤
      Real.sqrt ((q * b + (1 - q) * e) * (1 - (q * b + (1 - q) * e))) := by
  let a := q * b + (1 - q) * e
  have ha0 : 0 ≤ a := by
    dsimp [a]
    nlinarith
  have ha1 : a ≤ 1 := by
    dsimp [a]
    nlinarith
  have hsb0 : 0 ≤ Real.sqrt (b * (1 - b)) := Real.sqrt_nonneg _
  have hsa0 : 0 ≤ Real.sqrt (a * (1 - a)) := Real.sqrt_nonneg _
  have hbsq : (Real.sqrt (b * (1 - b))) ^ 2 = b * (1 - b) := by
    rw [Real.sq_sqrt]
    nlinarith
  have hasq : (Real.sqrt (a * (1 - a))) ^ 2 = a * (1 - a) := by
    rw [Real.sq_sqrt]
    nlinarith
  have haform : a = e + q * (b - e) := by
    dsimp [a]
    ring
  have hmixvar :
      a * (1 - a) =
        q * b * (1 - b) + (1 - q) * e * (1 - e) + q * (1 - q) * (b - e) ^ 2 := by
    rw [haform]
    ring
  let x := e * (1 - e)
  let y := q * (b - e) * (1 - e)
  let X := e * (1 - e)
  let Y := q * (b - e) ^ 2
  let u := e * (1 - e)
  let v := q * (1 - e) ^ 2
  have hX : 0 ≤ X := by
    dsimp [X]
    positivity
  have hY : 0 ≤ Y := by
    dsimp [Y]
    positivity
  have huv : u + v ≤ 1 := by
    have hinner : e + q * (1 - e) ≤ 1 := by nlinarith
    have hm := mul_le_mul_of_nonneg_left hinner (show 0 ≤ 1 - e by linarith)
    dsimp [u, v]
    calc
      e * (1 - e) + q * (1 - e) ^ 2 = (1 - e) * (e + q * (1 - e)) := by ring
      _ ≤ (1 - e) * 1 := hm
      _ ≤ 1 := by nlinarith
  have hcauchy : (x + y) ^ 2 ≤ (X + Y) * (u + v) := by
    have hfactor : 0 ≤ e * q * (1 - e) * (1 - b) ^ 2 := by positivity
    dsimp [x, y, X, Y, u, v]
    nlinarith
  have hA : (a * (1 - e)) ^ 2 ≤ e * (1 - e) + q * (b - e) ^ 2 := by
    have hxy : x + y = a * (1 - e) := by
      rw [haform]
      dsimp [x, y]
      ring
    rw [← hxy]
    calc
      (x + y) ^ 2 ≤ (X + Y) * (u + v) := hcauchy
      _ ≤ (X + Y) * 1 := mul_le_mul_of_nonneg_left huv (add_nonneg hX hY)
      _ = e * (1 - e) + q * (b - e) ^ 2 := by simp [X, Y]
  have hweighted :
      (1 - q) * (a * (1 - e)) ^ 2 + q * b * (1 - b) ≤ a * (1 - a) := by
    have hm := mul_le_mul_of_nonneg_left hA (sub_nonneg.mpr hq1)
    rw [hmixvar]
    nlinarith only [hm]
  change (1 - q) * a * (1 - e) + q * Real.sqrt (b * (1 - b)) ≤
    Real.sqrt (a * (1 - a))
  by_contra h
  have hlt : Real.sqrt (a * (1 - a)) <
      (1 - q) * a * (1 - e) + q * Real.sqrt (b * (1 - b)) := lt_of_not_ge h
  have hlhs0 :
      0 ≤ (1 - q) * a * (1 - e) + q * Real.sqrt (b * (1 - b)) := by
    positivity
  have hweightedCauchy :
      ((1 - q) * a * (1 - e) + q * Real.sqrt (b * (1 - b))) ^ 2 ≤
        (1 - q) * (a * (1 - e)) ^ 2 + q * (Real.sqrt (b * (1 - b))) ^ 2 := by
    have hfactor :
        0 ≤ q * (1 - q) * (a * (1 - e) - Real.sqrt (b * (1 - b))) ^ 2 := by
      positivity
    nlinarith only [hfactor]
  have hsquares :
      ((1 - q) * a * (1 - e) + q * Real.sqrt (b * (1 - b))) ^ 2 ≤
        (Real.sqrt (a * (1 - a))) ^ 2 := by
    calc
      ((1 - q) * a * (1 - e) + q * Real.sqrt (b * (1 - b))) ^ 2 ≤
          (1 - q) * (a * (1 - e)) ^ 2 + q * (Real.sqrt (b * (1 - b))) ^ 2 :=
        hweightedCauchy
      _ ≤ a * (1 - a) := by
        rw [hbsq]
        simpa only [mul_assoc] using hweighted
      _ = (Real.sqrt (a * (1 - a))) ^ 2 := hasq.symm
  exact (not_lt_of_ge hsquares) ((sq_lt_sq₀ hsa0 hlhs0).2 hlt)

private theorem geometricBinaryPeeling_case_le
    (q b e : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (hbe : b ≤ e) :
    (1 - q) * e * (1 - (q * b + (1 - q) * e)) + q * Real.sqrt (b * (1 - b)) ≤
      Real.sqrt ((q * b + (1 - q) * e) * (1 - (q * b + (1 - q) * e))) := by
  have h := geometricBinaryPeeling_case_ge q (1 - b) (1 - e) hq0 hq1
    (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
  have hmix : q * (1 - b) + (1 - q) * (1 - e) =
      1 - (q * b + (1 - q) * e) := by ring
  have hbmul : (1 - b) * b = b * (1 - b) := by ring
  have hamul : (1 - (q * b + (1 - q) * e)) * (q * b + (1 - q) * e) =
      (q * b + (1 - q) * e) * (1 - (q * b + (1 - q) * e)) := by ring
  rw [hmix] at h
  simp only [sub_sub_cancel] at h
  rw [hbmul, hamul] at h
  simpa only [mul_assoc, mul_comm, mul_left_comm] using h

/-- The binary envelope bounds the absolute deviation of two unit-interval numbers. -/
theorem abs_sub_le_binaryEnvelope
    {z a : ℝ} (hz : z ∈ Set.Icc (0 : ℝ) 1) (ha : a ∈ Set.Icc (0 : ℝ) 1) :
    |z - a| ≤ z * (1 - a) + (1 - z) * a := by
  rcases le_total z a with hza | haz
  · rw [abs_of_nonpos (sub_nonpos.mpr hza)]
    nlinarith [mul_nonneg hz.1 (sub_nonneg.mpr ha.2)]
  · rw [abs_of_nonneg (sub_nonneg.mpr haz)]
    nlinarith [mul_nonneg (sub_nonneg.mpr hz.2) ha.1]

/-- A distinguished atom of a unit-interval law can keep only its mass times the next
Bernoulli potential after the current mean absolute deviation is paid. -/
theorem expect_abs_sub_expect_add_atom_bernoulliPotential_le
    (law : PMF Omega) (atom : Omega) (next : Omega → ℝ)
    (bounded : ∀ state, next state ∈ Set.Icc (0 : ℝ) 1) :
    expect law (fun state ↦ |next state - expect law next|) +
        2 * (law atom).toReal * Real.sqrt (next atom * (1 - next atom)) ≤
      2 * Real.sqrt (expect law next * (1 - expect law next)) := by
  let p : Omega → ℝ := fun state ↦ (law state).toReal
  let q := p atom
  let b := next atom
  let a := expect law next
  have hp0 (state : Omega) : 0 ≤ p state := ENNReal.toReal_nonneg
  have hsum : ∑ state, p state = 1 := pmf_toReal_sum_one law
  have hq0 : 0 ≤ q := hp0 atom
  have hq1 : q ≤ 1 := by
    have hterm := Finset.single_le_sum (fun state _ ↦ hp0 state)
      (Finset.mem_univ atom)
    simpa [q] using hterm.trans_eq hsum
  have hb0 : 0 ≤ b := (bounded atom).1
  have hb1 : b ≤ 1 := (bounded atom).2
  have ha : a = ∑ state, p state * next state := by
    simp [a, p, expect_eq_sum]
  have ha0 : 0 ≤ a := by
    rw [ha]
    exact Finset.sum_nonneg fun state _ ↦ mul_nonneg (hp0 state) (bounded state).1
  have ha1 : a ≤ 1 := by
    rw [ha, ← hsum]
    apply Finset.sum_le_sum
    intro state _
    exact mul_le_of_le_one_right (hp0 state) (bounded state).2
  by_cases hqeq : q = 1
  · have hoffsum : ∑ state ∈ Finset.univ.erase atom, p state = 0 := by
      have hdecomp := Finset.sum_erase_add Finset.univ p (Finset.mem_univ atom)
      rw [hsum] at hdecomp
      change (∑ state ∈ Finset.univ.erase atom, p state) + q = 1 at hdecomp
      rw [hqeq] at hdecomp
      linarith
    have hpzero {state : Omega} (hne : state ≠ atom) : p state = 0 := by
      exact (Finset.sum_eq_zero_iff_of_nonneg
        (fun current _ ↦ hp0 current)).mp hoffsum state (by simp [hne])
    have haeq : a = b := by
      have hoffweighted :
          ∑ state ∈ Finset.univ.erase atom, p state * next state = 0 := by
        apply Finset.sum_eq_zero
        intro state membership
        rw [hpzero (Finset.ne_of_mem_erase membership), zero_mul]
      rw [ha, ← Finset.sum_erase_add Finset.univ
        (fun state ↦ p state * next state) (Finset.mem_univ atom)]
      rw [hoffweighted]
      simp [q, b, hqeq]
    rw [expect_eq_sum]
    change (∑ state, p state * |next state - a|) +
        2 * q * Real.sqrt (b * (1 - b)) ≤
      2 * Real.sqrt (a * (1 - a))
    have hoffabs :
        ∑ state ∈ Finset.univ.erase atom, p state * |next state - a| = 0 := by
      apply Finset.sum_eq_zero
      intro state membership
      rw [hpzero (Finset.ne_of_mem_erase membership), zero_mul]
    rw [← Finset.sum_erase_add Finset.univ
      (fun state ↦ p state * |next state - a|) (Finset.mem_univ atom)]
    rw [hoffabs]
    simp [q, b, hqeq, haeq]
  · have hq_lt : q < 1 := lt_of_le_of_ne hq1 hqeq
    let r := 1 - q
    let w := ∑ state ∈ Finset.univ.erase atom, p state * next state
    let e := w / r
    have hr0 : 0 < r := by simp [r, hq_lt]
    have hwoff : 0 ≤ w := by
      dsimp [w]
      exact Finset.sum_nonneg fun state _ ↦
        mul_nonneg (hp0 state) (bounded state).1
    have hmass : ∑ state ∈ Finset.univ.erase atom, p state = r := by
      calc
        (∑ state ∈ Finset.univ.erase atom, p state) =
            (∑ state, p state) - p atom := by
          rw [← Finset.sum_erase_add Finset.univ p (Finset.mem_univ atom)]
          ring
        _ = 1 - q := by rw [hsum]
        _ = r := rfl
    have hwle : w ≤ r := by
      rw [← hmass]
      dsimp [w]
      apply Finset.sum_le_sum
      intro state _
      exact mul_le_of_le_one_right (hp0 state) (bounded state).2
    have he0 : 0 ≤ e := div_nonneg hwoff hr0.le
    have he1 : e ≤ 1 := (div_le_one hr0).mpr hwle
    have hwe : w = r * e := by
      dsimp [e]
      field_simp
    have hadecomp : a = q * b + r * e := by
      rw [ha, ← Finset.sum_erase_add Finset.univ
        (fun state ↦ p state * next state) (Finset.mem_univ atom)]
      rw [show (∑ state ∈ Finset.univ.erase atom, p state * next state) = w by rfl,
        hwe]
      simp [q, b]
      ring
    have hlocal :
        expect law (fun state ↦ |next state - a|) ≤
          q * |b - a| + r * (e * (1 - a) + (1 - e) * a) := by
      rw [expect_eq_sum]
      change (∑ state, p state * |next state - a|) ≤ _
      rw [← Finset.sum_erase_add Finset.univ
        (fun state ↦ p state * |next state - a|) (Finset.mem_univ atom)]
      have hoff :
          (∑ state ∈ Finset.univ.erase atom, p state * |next state - a|) ≤
            r * (e * (1 - a) + (1 - e) * a) := by
        calc
          (∑ state ∈ Finset.univ.erase atom, p state * |next state - a|) ≤
              ∑ state ∈ Finset.univ.erase atom,
                p state * (next state * (1 - a) + (1 - next state) * a) := by
            apply Finset.sum_le_sum
            intro state _
            exact mul_le_mul_of_nonneg_left
              (abs_sub_le_binaryEnvelope (bounded state) ⟨ha0, ha1⟩) (hp0 state)
          _ = r * (e * (1 - a) + (1 - e) * a) := by
            simp_rw [mul_add]
            rw [Finset.sum_add_distrib]
            simp_rw [← mul_assoc]
            rw [← Finset.sum_mul, ← Finset.sum_mul]
            have hone :
                ∑ state ∈ Finset.univ.erase atom, p state * (1 - next state) =
                  r - w := by
              simp_rw [mul_sub, mul_one]
              rw [Finset.sum_sub_distrib]
              rw [hmass]
            rw [show (∑ state ∈ Finset.univ.erase atom,
                p state * next state) = w by rfl, hone, hwe]
            ring
      change (∑ state ∈ Finset.univ.erase atom, p state * |next state - a|) +
        p atom * |next atom - a| ≤ _
      dsimp [q, b]
      linarith
    rw [show expect law next = a by rfl]
    change expect law (fun state ↦ |next state - a|) +
        2 * q * Real.sqrt (b * (1 - b)) ≤ 2 * Real.sqrt (a * (1 - a))
    calc
      expect law (fun state ↦ |next state - a|) +
          2 * q * Real.sqrt (b * (1 - b)) ≤
          q * |b - a| + r * (e * (1 - a) + (1 - e) * a) +
            2 * q * Real.sqrt (b * (1 - b)) := by linarith
      _ ≤ 2 * Real.sqrt (a * (1 - a)) := by
        rw [hadecomp]
        dsimp [r] at *
        rcases le_total e b with heb | hbe
        · have habs : |b - (q * b + (1 - q) * e)| =
              (1 - q) * (b - e) := by
            rw [abs_of_nonneg]
            · ring
            · nlinarith
          rw [habs]
          have h := geometricBinaryPeeling_case_ge q b e hq0 hq1
            hb0 hb1 he0 he1 heb
          nlinarith
        · have habs : |b - (q * b + (1 - q) * e)| =
              (1 - q) * (e - b) := by
            rw [abs_of_nonpos]
            · ring
            · nlinarith
          rw [habs]
          have h := geometricBinaryPeeling_case_le q b e hq0 hq1
            hb0 hb1 he0 he1 hbe
          nlinarith

/-- The Bernoulli potential attached to one distinguished transient state. -/
def singleTransientBernoulliPotential
    (owner : Omega) (value : Omega → ℕ → ℝ) (state : Omega) (time : ℕ) : ℝ :=
  if state = owner then
    2 * Real.sqrt (value owner time * (1 - value owner time))
  else 0

omit [Fintype Omega] in
theorem singleTransientBernoulliPotential_nonneg
    (owner : Omega) (value : Omega → ℕ → ℝ) (state : Omega) (time : ℕ) :
    0 ≤ singleTransientBernoulliPotential owner value state time := by
  simp only [singleTransientBernoulliPotential]
  split_ifs
  · positivity
  · exact le_rfl

omit [Fintype Omega] in
theorem singleTransientBernoulliPotential_le_one
    (owner : Omega) (value : Omega → ℕ → ℝ)
    (bounded : ∀ state time, value state time ∈ Set.Icc (0 : ℝ) 1)
    (state : Omega) (time : ℕ) :
    singleTransientBernoulliPotential owner value state time ≤ 1 := by
  simp only [singleTransientBernoulliPotential]
  split_ifs with hstate
  · have hv := bounded owner time
    have hsqrt0 : 0 ≤ Real.sqrt (value owner time * (1 - value owner time)) :=
      Real.sqrt_nonneg _
    have hsquare :
        (Real.sqrt (value owner time * (1 - value owner time))) ^ 2 =
          value owner time * (1 - value owner time) := by
      rw [Real.sq_sqrt (mul_nonneg hv.1 (sub_nonneg.mpr hv.2))]
    nlinarith [sq_nonneg (value owner time - (1 / 2 : ℝ))]
  · norm_num

theorem expect_singleTransientBernoulliPotential
    (law : PMF Omega) (owner : Omega) (value : Omega → ℕ → ℝ) (time : ℕ) :
    expect law (fun state ↦ singleTransientBernoulliPotential owner value state time) =
      (law owner).toReal *
        (2 * Real.sqrt (value owner time * (1 - value owner time))) := by
  rw [expect_eq_sum]
  simp [singleTransientBernoulliPotential]

/-- With exactly one transient state, one-step variation plus next Bernoulli potential is at
most the current Bernoulli potential.  Recurrent-source increments vanish exactly. -/
theorem conditionalVariation_add_singleTransientPotential_le
    (kernel : Omega → PMF Omega) (owner : Omega) (value : Omega → ℕ → ℝ)
    (harmonic : IsUnitIntervalBackwardMarkovHarmonic kernel value)
    (uniqueTransient : finiteTransientStates kernel = {owner})
    (source : Omega) (time : ℕ) :
    expect (kernel source) (fun successor ↦
        |value successor (time + 1) - value source time|) +
      expect (kernel source) (fun successor ↦
        singleTransientBernoulliPotential owner value successor (time + 1)) ≤
      singleTransientBernoulliPotential owner value source time := by
  by_cases hsource : source = owner
  · subst source
    rw [expect_singleTransientBernoulliPotential]
    have honeAtom := expect_abs_sub_expect_add_atom_bernoulliPotential_le
      (kernel owner) owner (fun successor ↦ value successor (time + 1))
      (fun successor ↦ harmonic.1 successor (time + 1))
    rw [← harmonic.2 owner time] at honeAtom
    simp only [singleTransientBernoulliPotential, if_pos] at honeAtom ⊢
    nlinarith
  · have hsourceNotTransient : source ∉ finiteTransientStates kernel := by
      rw [uniqueTransient]
      simp [hsource]
    have hsourceRecurrent : source ∈ finiteRecurrentCore kernel :=
      not_not.mp (mt (mem_finiteTransientStates_iff kernel source).mpr
        hsourceNotTransient)
    have hvariation := expect_abs_increment_eq_zero_of_mem_finiteRecurrentCore
      kernel value harmonic hsourceRecurrent time
    have hownerTransient : owner ∉ finiteRecurrentCore kernel := by
      exact (mem_finiteTransientStates_iff kernel owner).mp (by rw [uniqueTransient]; simp)
    have hpotential :
        expect (kernel source) (fun successor ↦
          singleTransientBernoulliPotential owner value successor (time + 1)) = 0 := by
      rw [expect_eq_sum]
      apply Finset.sum_eq_zero
      intro successor _
      by_cases hsupport : successor ∈ (kernel source).support
      · have hsuccessorRecurrent :=
          finiteRecurrentCore_closed kernel hsourceRecurrent hsupport
        have hne : successor ≠ owner := by
          intro heq
          subst successor
          exact hownerTransient hsuccessorRecurrent
        simp [singleTransientBernoulliPotential, hne]
      · have hzero : kernel source successor = 0 := by
          simpa [PMF.mem_support_iff] using hsupport
        simp [hzero]
    rw [hvariation, hpotential]
    simp [singleTransientBernoulliPotential, hsource]

omit [DecidableEq Omega] in
/-- Chronology-preserving elimination telescope.  Any nonnegative time-dependent potential
whose one-step loss pays the conditional absolute increment bounds the full finite-horizon
variation by its initial value.  An induction over transient states can use this after one
state is eliminated, provided the reduced-chain potential is transported on the same clock. -/
theorem finiteExpectedSpaceTimeMarkovVariation_le_initialPotential
    (initial : Omega) (kernel : Omega → PMF Omega) (value : Omega → ℕ → ℝ)
    (potential : Omega → ℕ → ℝ)
    (potential_nonneg : ∀ state time, 0 ≤ potential state time)
    (step : ∀ source time,
      expect (kernel source) (fun successor ↦
          |value successor (time + 1) - value source time|) +
        expect (kernel source) (fun successor ↦ potential successor (time + 1)) ≤
      potential source time)
    (horizon : ℕ) :
    finiteExpectedSpaceTimeMarkovVariation initial kernel value horizon ≤
      potential initial 0 := by
  have hstep (time : ℕ) :
      expect (Math.PMFIter.iter kernel time initial) (fun source ↦
          potential source time - expect (kernel source) (fun successor ↦
            potential successor (time + 1))) =
        expect (Math.PMFIter.iter kernel time initial) (fun source ↦
          potential source time) -
          expect (Math.PMFIter.iter kernel (time + 1) initial) (fun successor ↦
            potential successor (time + 1)) := by
    rw [expect_sub, ← expect_bind, Math.PMFIter.iter_succ']
  rw [finiteExpectedSpaceTimeMarkovVariation_eq_sum_iter_conditional]
  calc
    (∑ time ∈ Finset.range horizon,
        expect (Math.PMFIter.iter kernel time initial) (fun source ↦
          expect (kernel source) (fun successor ↦
            |value successor (time + 1) - value source time|))) ≤
        ∑ time ∈ Finset.range horizon,
          expect (Math.PMFIter.iter kernel time initial) (fun source ↦
            potential source time - expect (kernel source) (fun successor ↦
              potential successor (time + 1))) := by
      apply Finset.sum_le_sum
      intro time _
      apply expect_mono
      intro source
      linarith [step source time]
    _ = potential initial 0 -
        expect (Math.PMFIter.iter kernel horizon initial) (fun successor ↦
          potential successor horizon) := by
      simp_rw [hstep]
      rw [Finset.sum_range_sub']
      simp [Math.PMFIter.iter_zero]
    _ ≤ potential initial 0 := by
      have hterminal :
          0 ≤ expect (Math.PMFIter.iter kernel horizon initial) (fun successor ↦
            potential successor horizon) := by
        apply expect_nonneg
        exact fun successor ↦ potential_nonneg successor horizon
      linarith

/-- Sharp time-dependent variation bound when the finite kernel has exactly one transient
state.  This is the one-state base case for a chronology-preserving transient elimination. -/
theorem finiteExpectedSpaceTimeMarkovVariation_le_one_of_singleTransient
    (initial : Omega) (kernel : Omega → PMF Omega) (owner : Omega)
    (value : Omega → ℕ → ℝ)
    (harmonic : IsUnitIntervalBackwardMarkovHarmonic kernel value)
    (uniqueTransient : finiteTransientStates kernel = {owner})
    (horizon : ℕ) :
    finiteExpectedSpaceTimeMarkovVariation initial kernel value horizon ≤ 1 := by
  let potential : Omega → ℕ → ℝ :=
    singleTransientBernoulliPotential owner value
  exact (finiteExpectedSpaceTimeMarkovVariation_le_initialPotential
    initial kernel value potential
      (singleTransientBernoulliPotential_nonneg owner value)
      (conditionalVariation_add_singleTransientPotential_le
        kernel owner value harmonic uniqueTransient) horizon).trans
    (singleTransientBernoulliPotential_le_one owner value harmonic.1 initial 0)

end

end Math.Probability
