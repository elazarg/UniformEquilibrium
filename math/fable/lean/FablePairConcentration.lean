/-
Local concentration on a quitting pair under a vanishing singleton ratio.

At a one-date product quitting root every player quits independently, so the
whole one-stage picture is a polynomial in the quit-rate vector
`w who = (root who true).toReal`.  Two bridges make that explicit: absorption
is the complement of the joint continuation product, and the mass of the exact
singleton coalition `{who}` is that player's quit rate times the opponents'
continuation product.

Suppose a sequence of roots has strictly positive absorption while the total
singleton mass is a vanishing fraction `delta n` of absorption.  The exact
split of absorption into singleton and collision mass, together with the
quadratic collision estimate, forces `1 - delta n ≤ C * absorption n` with
`C` the number of unordered player pairs, so absorption is eventually bounded
below by a positive constant.  The quit-rate vectors live in the compact unit
box, so a subsequence converges to a limit vector `w` with positive absorption
polynomial and vanishing singleton polynomial.  A limit vector with no
coordinate equal to one is identically zero, hence has zero absorption; a limit
vector with exactly one unit coordinate has strictly positive singleton
polynomial.  Both are excluded, so at least two coordinates of `w` equal one,
and along that subsequence the corresponding pair of quit rates has product
tending to one.

The production owners used here are
`quittingRootCollisionMass_le_choose_card_mul_absorption_sq` in
`UniformEquilibrium/Quitting/AbsorptionPath/CollisionConcentration.lean` and
`QuittingFiniteRootWindow.quittingRootAbsorptionMass_eq_sum_singletonMass_add_collisionMass`
in `UniformEquilibrium/Quitting/AbsorptionPath/NormalizedFiniteWindowOccupation.lean`.
-/
import UniformEquilibrium.Quitting.AbsorptionPath.CollisionConcentration
import UniformEquilibrium.Quitting.AbsorptionPath.NormalizedFiniteWindowOccupation

noncomputable section

namespace GameTheory

open scoped Topology

/-! ## The quit-rate box and the absorption polynomial -/

section QuitRateBox

variable {ι : Type} [Fintype ι]

/-- One-stage absorption read as a polynomial in the quit-rate vector. -/
def fableBoxAbsorption (w : ι → ℝ) : ℝ := 1 - ∏ who, (1 - w who)

omit [Fintype ι] in
/-- The quit-rate vector of a product root lies in the unit box. -/
theorem fable_quitRate_mem_unitBox (root : ι → PMF Bool) :
    (fun who => (root who true).toReal) ∈
      Set.univ.pi fun _ : ι => Set.Icc (0 : ℝ) 1 := by
  intro who _
  exact ⟨ENNReal.toReal_nonneg,
    ENNReal.toReal_mono ENNReal.one_ne_top ((root who).coe_le_one true)⟩

/-- The absorption polynomial is continuous on the quit-rate box. -/
theorem fable_continuous_boxAbsorption :
    Continuous (fableBoxAbsorption : (ι → ℝ) → ℝ) :=
  continuous_const.sub
    (continuous_finsetProd _ fun who _ => continuous_const.sub (continuous_apply who))

/-- **Bridge 1: absorption is the complement of the continuation product.**
One-stage absorption at a product root is `1 - ∏ who, (1 - quit rate who)`. -/
theorem fable_absorptionMass_eq_boxAbsorption (root : ι → PMF Bool) :
    quittingRootAbsorptionMass root =
      fableBoxAbsorption fun who => (root who true).toReal := by
  simp only [fableBoxAbsorption, quittingRootAbsorptionMass,
    quittingStationaryContinueMass_eq_prod_continueProbability]
  exact congrArg (fun total => 1 - total)
    (Finset.prod_congr rfl fun who _ => Math.PMFProduct.pmfBool_false_toReal (root who))

/-- One-stage absorption is at most one. -/
theorem fable_absorptionMass_le_one (root : ι → PMF Bool) :
    quittingRootAbsorptionMass root ≤ 1 := by
  have hcontinue := quittingStationaryContinueMass_nonneg root
  unfold quittingRootAbsorptionMass
  linarith

end QuitRateBox

/-! ## The singleton polynomial -/

section SingletonBox

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Total exact-singleton mass read as a polynomial in the quit-rate vector. -/
def fableBoxSingletonTotal (w : ι → ℝ) : ℝ :=
  ∑ who, w who * ∏ other ∈ Finset.univ.erase who, (1 - w other)

/-- The singleton polynomial is continuous on the quit-rate box. -/
theorem fable_continuous_boxSingletonTotal :
    Continuous (fableBoxSingletonTotal : (ι → ℝ) → ℝ) :=
  continuous_finsetSum _ fun who _ =>
    (continuous_apply who).mul
      (continuous_finsetProd _ fun other _ => continuous_const.sub (continuous_apply other))

/-- **Bridge 2: the exact singleton coalition mass.**  The mass of exactly
`{who}` quitting is that player's quit rate times the opponents' joint
continuation. -/
theorem fable_coalitionMass_singleton_eq (root : ι → PMF Bool) (who : ι) :
    quittingRootCoalitionMass root {who} =
      (root who true).toReal *
        ∏ other ∈ Finset.univ.erase who, (1 - (root other true).toReal) := by
  simp only [quittingRootCoalitionMass, Math.PMFProduct.coalitionMass,
    quittingRootQuitRates, Finset.prod_singleton, Finset.compl_singleton]

/-- The total singleton mass is the singleton polynomial at the quit rates. -/
theorem fable_sum_coalitionMass_singleton_eq (root : ι → PMF Bool) :
    (∑ who, quittingRootCoalitionMass root {who}) =
      fableBoxSingletonTotal fun who => (root who true).toReal := by
  simp only [fableBoxSingletonTotal]
  exact Finset.sum_congr rfl fun who _ => fable_coalitionMass_singleton_eq root who

/-- Every summand of the singleton polynomial is nonnegative on the box. -/
theorem fable_boxSingletonTotal_term_nonneg {w : ι → ℝ}
    (h0 : ∀ i, 0 ≤ w i) (h1 : ∀ i, w i ≤ 1) (who : ι) :
    0 ≤ w who * ∏ other ∈ Finset.univ.erase who, (1 - w other) :=
  mul_nonneg (h0 who) (Finset.prod_nonneg fun other _ => by linarith [h1 other])

/-! ## Pair concentration -/

/-- **Vanishing singleton ratio concentrates a pair.**  If the total exact
singleton mass of a root sequence is a vanishing fraction of its strictly
positive absorption mass, then some pair of distinct players has, along a
subsequence, a product of quit rates tending to one. -/
theorem fable_vanishing_singletonRatio_pairConcentration
    (roots : ℕ → ι → PMF Bool) (delta : ℕ → ℝ)
    (hdelta : Filter.Tendsto delta Filter.atTop (nhds 0))
    (hratio : ∀ n, ∑ who, quittingRootCoalitionMass (roots n) {who} ≤
      delta n * quittingRootAbsorptionMass (roots n))
    (hpos : ∀ n, 0 < quittingRootAbsorptionMass (roots n))
    (hcard : 1 < Fintype.card ι) :
    ∃ (i j : ι) (subseq : ℕ → ℕ), i ≠ j ∧ StrictMono subseq ∧
      Filter.Tendsto (fun k => (roots (subseq k) i true).toReal *
        (roots (subseq k) j true).toReal) Filter.atTop (nhds 1) := by
  classical
  obtain ⟨v, hv⟩ : ∃ v : ℕ → ι → ℝ, ∀ n who, v n who = (roots n who true).toReal :=
    ⟨fun n who => (roots n who true).toReal, fun _ _ => rfl⟩
  have hvfun : ∀ n, v n = fun who => (roots n who true).toReal := fun n => funext (hv n)
  have hA : ∀ n, quittingRootAbsorptionMass (roots n) = fableBoxAbsorption (v n) := by
    intro n
    rw [hvfun n]
    exact fable_absorptionMass_eq_boxAbsorption (roots n)
  have hB : ∀ n, (∑ who, quittingRootCoalitionMass (roots n) {who}) =
      fableBoxSingletonTotal (v n) := by
    intro n
    rw [hvfun n]
    exact fable_sum_coalitionMass_singleton_eq (roots n)
  have hCpos : (0 : ℝ) < ((Fintype.card ι).choose 2 : ℝ) := by
    exact_mod_cast Nat.choose_pos hcard
  -- Step 1: the split identity and the quadratic collision estimate give a floor.
  have hfloor : ∀ n, 1 - delta n ≤
      ((Fintype.card ι).choose 2 : ℝ) * quittingRootAbsorptionMass (roots n) := by
    intro n
    have hsplit :=
      QuittingFiniteRootWindow.quittingRootAbsorptionMass_eq_sum_singletonMass_add_collisionMass
        (roots n)
    have hcol := quittingRootCollisionMass_le_choose_card_mul_absorption_sq (roots n)
    have hr := hratio n
    have hkey : (1 - delta n) * quittingRootAbsorptionMass (roots n) ≤
        (((Fintype.card ι).choose 2 : ℝ) * quittingRootAbsorptionMass (roots n)) *
          quittingRootAbsorptionMass (roots n) := by
      nlinarith [hsplit, hcol, hr]
    exact le_of_mul_le_mul_right hkey (hpos n)
  have hdeltaSmall : ∀ᶠ n in Filter.atTop, delta n < 1 / 2 :=
    hdelta.eventually_lt_const (by norm_num)
  have hafloor : ∀ᶠ n in Filter.atTop,
      (1 : ℝ) ≤ 2 * ((Fintype.card ι).choose 2 : ℝ) * fableBoxAbsorption (v n) := by
    filter_upwards [hdeltaSmall] with n hn
    have h1 := hfloor n
    rw [hA n] at h1
    nlinarith [h1, hn]
  -- Step 2: the quit-rate vectors live in a compact box.
  have hbox : IsCompact (Set.univ.pi fun _ : ι => Set.Icc (0 : ℝ) 1) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  have hmem : ∀ n, v n ∈ Set.univ.pi fun _ : ι => Set.Icc (0 : ℝ) 1 := by
    intro n
    rw [hvfun n]
    exact fable_quitRate_mem_unitBox (roots n)
  obtain ⟨w, hwmem, phi, hphi, hlim⟩ := hbox.tendsto_subseq hmem
  have hw0 : ∀ i, 0 ≤ w i := fun i => (hwmem i (Set.mem_univ i)).1
  have hw1 : ∀ i, w i ≤ 1 := fun i => (hwmem i (Set.mem_univ i)).2
  -- Step 3: transport the two polynomials to the limit vector.
  have hlimA : Filter.Tendsto (fun k => fableBoxAbsorption (v (phi k))) Filter.atTop
      (nhds (fableBoxAbsorption w)) :=
    (fable_continuous_boxAbsorption.tendsto w).comp hlim
  have hlimB : Filter.Tendsto (fun k => fableBoxSingletonTotal (v (phi k))) Filter.atTop
      (nhds (fableBoxSingletonTotal w)) :=
    (fable_continuous_boxSingletonTotal.tendsto w).comp hlim
  have hAwpos : 0 < fableBoxAbsorption w := by
    have hev : ∀ᶠ k in Filter.atTop,
        (1 : ℝ) ≤ 2 * ((Fintype.card ι).choose 2 : ℝ) * fableBoxAbsorption (v (phi k)) :=
      hphi.tendsto_atTop.eventually hafloor
    have hlimA2 : Filter.Tendsto
        (fun k => 2 * ((Fintype.card ι).choose 2 : ℝ) * fableBoxAbsorption (v (phi k)))
        Filter.atTop
        (nhds (2 * ((Fintype.card ι).choose 2 : ℝ) * fableBoxAbsorption w)) :=
      hlimA.const_mul _
    nlinarith [ge_of_tendsto hlimA2 hev, hCpos]
  have hb0 : Filter.Tendsto (fun n => fableBoxSingletonTotal (v n)) Filter.atTop (nhds 0) := by
    have habs : Filter.Tendsto (fun n => |delta n|) Filter.atTop (nhds 0) := by
      simpa using hdelta.abs
    refine squeeze_zero (g := fun n => |delta n|) (fun n => ?_) (fun n => ?_) habs
    · rw [← hB n]
      exact Finset.sum_nonneg fun who _ => quittingRootCoalitionMass_nonneg (roots n) {who}
    · rw [← hB n]
      have hr := hratio n
      have ha0 := (hpos n).le
      have ha1 := fable_absorptionMass_le_one (roots n)
      nlinarith [abs_nonneg (delta n), le_abs_self (delta n), hr, ha0, ha1]
  have hBw : fableBoxSingletonTotal w = 0 :=
    tendsto_nhds_unique hlimB (hb0.comp hphi.tendsto_atTop)
  -- Step 4: the limit vector has at least two unit coordinates.
  have hterms : ∀ i : ι, w i * ∏ other ∈ Finset.univ.erase i, (1 - w other) = 0 := by
    have hnn : ∀ i ∈ (Finset.univ : Finset ι),
        0 ≤ w i * ∏ other ∈ Finset.univ.erase i, (1 - w other) :=
      fun i _ => fable_boxSingletonTotal_term_nonneg hw0 hw1 i
    have hsum : (∑ i, w i * ∏ other ∈ Finset.univ.erase i, (1 - w other)) = 0 := hBw
    intro i
    exact (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum i (Finset.mem_univ i)
  have hScard : 1 < (Finset.univ.filter fun i : ι => w i = 1).card := by
    by_contra hle
    rcases Nat.lt_or_ge (Finset.univ.filter fun i : ι => w i = 1).card 1 with h0 | h1
    · have hempty : (Finset.univ.filter fun i : ι => w i = 1) = ∅ :=
        Finset.card_eq_zero.mp (Nat.lt_one_iff.mp h0)
      have hne : ∀ k : ι, w k ≠ 1 := by
        intro k hk
        have hmem : k ∈ (Finset.univ.filter fun i : ι => w i = 1) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ k, hk⟩
        rw [hempty] at hmem
        exact absurd hmem (Finset.notMem_empty k)
      have hzero : ∀ k : ι, w k = 0 := by
        intro k
        have hprod : 0 < ∏ other ∈ Finset.univ.erase k, (1 - w other) :=
          Finset.prod_pos fun other _ =>
            sub_pos.mpr (lt_of_le_of_ne (hw1 other) (hne other))
        rcases mul_eq_zero.mp (hterms k) with hzeroleft | hzeroright
        · exact hzeroleft
        · exact absurd hzeroright hprod.ne'
      have hAzero : fableBoxAbsorption w = 0 := by
        simp [fableBoxAbsorption, hzero]
      rw [hAzero] at hAwpos
      exact lt_irrefl 0 hAwpos
    · have hcard1 : (Finset.univ.filter fun i : ι => w i = 1).card = 1 :=
        le_antisymm (Nat.not_lt.mp hle) h1
      obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hcard1
      have hmema : a ∈ (Finset.univ.filter fun i : ι => w i = 1) := by
        rw [ha]
        exact Finset.mem_singleton_self a
      have hwa : w a = 1 := (Finset.mem_filter.mp hmema).2
      have hne : ∀ k : ι, k ≠ a → w k ≠ 1 := by
        intro k hk hone
        have hmem : k ∈ (Finset.univ.filter fun i : ι => w i = 1) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ k, hone⟩
        rw [ha, Finset.mem_singleton] at hmem
        exact hk hmem
      have hprod : 0 < ∏ other ∈ Finset.univ.erase a, (1 - w other) :=
        Finset.prod_pos fun other hother =>
          sub_pos.mpr (lt_of_le_of_ne (hw1 other) (hne other (Finset.ne_of_mem_erase hother)))
      have hzeroterm := hterms a
      rw [hwa, one_mul] at hzeroterm
      rw [hzeroterm] at hprod
      exact lt_irrefl 0 hprod
  -- Step 5: the two unit coordinates give the concentrated pair.
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp hScard
  have hwi : w i = 1 := (Finset.mem_filter.mp hi).2
  have hwj : w j = 1 := (Finset.mem_filter.mp hj).2
  refine ⟨i, j, phi, hij, hphi, ?_⟩
  have hpi : Filter.Tendsto (fun k => v (phi k) i) Filter.atTop (nhds (w i)) :=
    (tendsto_pi_nhds.mp hlim) i
  have hpj : Filter.Tendsto (fun k => v (phi k) j) Filter.atTop (nhds (w j)) :=
    (tendsto_pi_nhds.mp hlim) j
  have hmul := hpi.mul hpj
  rw [hwi, hwj, one_mul] at hmul
  simpa only [hv] using hmul

end SingletonBox

end GameTheory
