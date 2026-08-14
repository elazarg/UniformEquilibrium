import Mathlib
import MathUE.CurveSelection.PositiveRoot
import UniformEquilibrium.Quitting.Cycles.ConditionedDiffuseProductRescaling
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticMacroscopicAtomNashProvenance
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticResetReprojectionDiffuseClockBridge
import UniformEquilibrium.Quitting.RewardBound

/-!
# Weighted-clock rank reduction

This experiment formalizes the finite mathematics behind the rank-reduction
addendum.  Here **rank** is the cardinality of a quitting coalition.  It is
never the cardinality of the player type.

The file deliberately records three logically different layers.

* `FiniteWeightedClock` is an abstract finite chronology.  Its stage clock is
  dominated by loss of live mass.  This gives an unconditional stopping-time
  bulk/tail hierarchy.
* `SharpClockCut` exposes the one genuinely analytic input used by the sharp
  logarithmic estimate.  The logarithmic potential inequality itself is
  proved below; it is not an axiom.
* The terminal-semantic section proves an aggregate, rank-blind collision
  charge.  It uses the whole collision event, not a sum of separately charged
  coalition estimates, and therefore has no factor counting coalitions.

Nothing below states an unconditional pair-only reduction.  A separate
finite regression at the end witnesses arbitrary rank at a finer blow-up
scale.

Two current-frontier fences are also preserved.  Question 173 shows that a
concentrated marked row attached to a minimum *tail* is automatic under the
hypothetical positive-debt regime; it is not itself a contradiction.  The
`ε`-Nash collision theorem below therefore assumes Nash provenance on the
displayed root/tail.  Question 175 gives a distinct player-deletion
alternative.  That is a reduction of ambient player cardinality, whereas all
clock estimates below reduce terminal-coalition rank.
-/


noncomputable section

namespace GameTheory.Experiments.WeightedClockRankReduction

open scoped BigOperators
open Finset Math.PMFProduct

/-! ## 1. Finite weighted clocks -/

/-- A finite opponent clock of length `horizon`.

`stage time = live time * hazard time` is the opponent-containing absorption
mass at `time`.  `stage_le_drop` is the only chronological input needed for
tail domination. -/
structure FiniteWeightedClock (horizon : ℕ) where
  live : ℕ → ℝ
  hazard : ℕ → ℝ
  stage : ℕ → ℝ
  live_nonneg : ∀ time, 0 ≤ live time
  hazard_nonneg : ∀ time, 0 ≤ hazard time
  hazard_le_one : ∀ time, hazard time ≤ 1
  stage_eq : ∀ time < horizon, stage time = live time * hazard time
  stage_le_drop : ∀ time < horizon,
    stage time ≤ live time - live (time + 1)

namespace FiniteWeightedClock

variable {horizon : ℕ} (clock : FiniteWeightedClock horizon)

/-- Clock mass in the half-open chronological interval `[start,horizon)`. -/
def tail (start : ℕ) : ℝ :=
  ∑ time ∈ Finset.Ico start horizon, clock.stage time

/-- Total opponent-clock mass. -/
def total : ℝ := clock.tail 0

/-- The `k`-th survival-weighted hazard moment. -/
def moment (k : ℕ) : ℝ :=
  ∑ time ∈ Finset.range horizon,
    clock.live time * clock.hazard time ^ k

theorem stage_nonneg {time : ℕ} (htime : time < horizon) :
    0 ≤ clock.stage time := by
  rw [clock.stage_eq time htime]
  exact mul_nonneg (clock.live_nonneg time) (clock.hazard_nonneg time)

theorem tail_nonneg (start : ℕ) : 0 ≤ clock.tail start := by
  exact Finset.sum_nonneg fun time htime ↦
    clock.stage_nonneg (Finset.mem_Ico.mp htime).2

@[simp] theorem tail_horizon : clock.tail horizon = 0 := by
  simp [tail]

theorem total_eq_sum_range :
    clock.total = ∑ time ∈ Finset.range horizon, clock.stage time := by
  simp [total, tail]

/-- Exact one-step removal of a clock atom from its future tail. -/
theorem tail_succ {time : ℕ} (htime : time < horizon) :
    clock.tail (time + 1) = clock.tail time - clock.stage time := by
  have hset : Finset.Ico time horizon =
      insert time (Finset.Ico (time + 1) horizon) := by
    ext index
    simp [Finset.mem_Ico]
    omega
  have hnot : time ∉ Finset.Ico (time + 1) horizon := by simp
  unfold tail
  rw [hset, Finset.sum_insert hnot]
  ring

/-- Later clock tails are smaller. -/
theorem tail_antitone {first second : ℕ}
    (hfirst : first ≤ second) :
    clock.tail second ≤ clock.tail first := by
  by_cases hsecond : horizon ≤ second
  · have hfirstTail : 0 ≤ clock.tail first := clock.tail_nonneg first
    have hzero : clock.tail second = 0 := by
      simp [tail, Finset.Ico_eq_empty (by omega : ¬ second < horizon)]
    linarith
  · have hsecondHorizon : second ≤ horizon := Nat.le_of_lt (lt_of_not_ge hsecond)
    rw [show clock.tail first =
        (∑ time ∈ Finset.Ico first second, clock.stage time) +
          clock.tail second by
      unfold tail
      exact (Finset.sum_Ico_consecutive clock.stage hfirst hsecondHorizon).symm]
    exact le_add_of_nonneg_left
      (Finset.sum_nonneg fun time htime ↦
        clock.stage_nonneg
          ((Finset.mem_Ico.mp htime).2.trans_le hsecondHorizon))

/-- **Tail domination.** All future clock mass is paid by current live mass.
This is derived from the one-step live-mass drop, rather than stored in the
clock structure. -/
theorem tail_le_live {start : ℕ} (hstart : start ≤ horizon) :
    clock.tail start ≤ clock.live start := by
  have hsum : clock.tail start ≤
      ∑ time ∈ Finset.Ico start horizon,
        (clock.live time - clock.live (time + 1)) := by
    exact Finset.sum_le_sum fun time htime ↦
      clock.stage_le_drop time (Finset.mem_Ico.mp htime).2
  have htelescope :
      (∑ time ∈ Finset.Ico start horizon,
        (clock.live time - clock.live (time + 1))) =
          clock.live start - clock.live horizon := by
    rw [Finset.sum_Ico_eq_sub _ hstart]
    simp only [Finset.sum_range_sub']
    ring
  rw [htelescope] at hsum
  linarith [clock.live_nonneg horizon]

theorem total_nonneg : 0 ≤ clock.total := clock.tail_nonneg 0

theorem total_le_live_zero : clock.total ≤ clock.live 0 := by
  exact clock.tail_le_live (Nat.zero_le horizon)

/-! ## 2. A fully unconditional bulk/tail hierarchy -/

/-- A cut before which hazards are at most `threshold`, while the whole
remaining clock tail has already fallen below `mesh / threshold`.

This is a predicate, not an assumption about all clocks: the producer below
constructs such a cut from a positive threshold and a stage-mesh bound. -/
structure HasBulkTailCut (mesh threshold : ℝ) where
  cut : ℕ
  cut_le : cut ≤ horizon
  before : ∀ time < cut, clock.hazard time ≤ threshold
  tail_le : clock.tail cut ≤ mesh / threshold

/-- A stage mesh bound and tail domination produce a bulk/tail cut at every
positive hazard threshold. -/
noncomputable def bulkTailCut
    {mesh threshold : ℝ} (hmesh0 : 0 ≤ mesh) (hthreshold : 0 < threshold)
    (hmesh : ∀ time < horizon, clock.stage time ≤ mesh) :
    clock.HasBulkTailCut mesh threshold := by
  classical
  by_cases hhigh : ∃ time, time < horizon ∧ threshold < clock.hazard time
  · let cut := Nat.find hhigh
    have hspec : cut < horizon ∧ threshold < clock.hazard cut :=
      Nat.find_spec hhigh
    have hbefore : ∀ time < cut, clock.hazard time ≤ threshold := by
      intro time htime
      exact le_of_not_gt fun hgt ↦
        (not_le_of_gt htime)
          (Nat.find_min' hhigh ⟨lt_trans htime hspec.1, hgt⟩)
    have hstageEq := clock.stage_eq cut hspec.1
    have htailLive := clock.tail_le_live hspec.1.le
    have hstageMesh := hmesh cut hspec.1
    have hliveLe : clock.live cut ≤ mesh / threshold := by
      have hhazard0 := clock.hazard_nonneg cut
      have hlive0 := clock.live_nonneg cut
      rw [hstageEq] at hstageMesh
      apply (le_div_iff₀ hthreshold).2
      nlinarith
    exact ⟨cut, hspec.1.le, hbefore, htailLive.trans hliveLe⟩
  · refine ⟨horizon, le_rfl, ?_, ?_⟩
    · intro time htime
      exact le_of_not_gt fun hgt ↦ hhigh ⟨time, htime, hgt⟩
    · simpa [tail] using div_nonneg hmesh0 hthreshold.le

/-- Generic summation engine: charge the bulk at `coefficient * stage` and
the remaining suffix once at full stage mass. -/
theorem sum_le_coefficient_total_add_tail
    (quantity : ℕ → ℝ) {cut : ℕ}
    {coefficient : ℝ} (hcoefficient : 0 ≤ coefficient)
    (hbulk : ∀ time < cut,
      quantity time ≤ coefficient * clock.stage time)
    (hsuffix : ∀ time, cut ≤ time → time < horizon →
      quantity time ≤ clock.stage time) :
    (∑ time ∈ Finset.range horizon, quantity time) ≤
      coefficient * clock.total + clock.tail cut := by
  have hpoint : ∀ time ∈ Finset.range horizon,
      quantity time ≤ coefficient * clock.stage time +
        if cut ≤ time then clock.stage time else 0 := by
    intro time htime
    have htimeHorizon := Finset.mem_range.mp htime
    by_cases hlate : cut ≤ time
    · simp only [if_pos hlate]
      exact (hsuffix time hlate htimeHorizon).trans
        (le_add_of_nonneg_left
          (mul_nonneg hcoefficient (clock.stage_nonneg htimeHorizon)))
    · simp only [if_neg hlate]
      simpa using hbulk time (Nat.lt_of_not_ge hlate)
  calc
    (∑ time ∈ Finset.range horizon, quantity time) ≤
        ∑ time ∈ Finset.range horizon,
          (coefficient * clock.stage time +
            if cut ≤ time then clock.stage time else 0) :=
      Finset.sum_le_sum hpoint
    _ = coefficient * clock.total + clock.tail cut := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      rw [← clock.total_eq_sum_range]
      congr 1
      unfold tail
      rw [show Finset.Ico cut horizon =
          (Finset.range horizon).filter (fun time ↦ cut ≤ time) by
        ext time
        simp [Finset.mem_Ico, and_comm]]
      rw [Finset.sum_filter]

/-- On the bulk, the `k`-th hazard moment costs `threshold^(k-1)` per clock
atom; on the suffix it costs at most the clock atom itself. -/
theorem moment_le_of_bulkTailCut
    {mesh threshold : ℝ} (hthreshold0 : 0 < threshold)
    (k : ℕ) (hk : 1 ≤ k)
    (cut : clock.HasBulkTailCut mesh threshold) :
    clock.moment k ≤
      threshold ^ (k - 1) * clock.total + mesh / threshold := by
  have hcoefficient : 0 ≤ threshold ^ (k - 1) :=
    pow_nonneg hthreshold0.le _
  have hbulk : ∀ time < cut.cut,
      clock.live time * clock.hazard time ^ k ≤
        threshold ^ (k - 1) * clock.stage time := by
    intro time htime
    have htimeHorizon := lt_of_lt_of_le htime cut.cut_le
    have ha0 := clock.hazard_nonneg time
    have haThreshold := cut.before time htime
    have hpow : clock.hazard time ^ (k - 1) ≤ threshold ^ (k - 1) :=
      pow_le_pow_left₀ ha0 haThreshold _
    rw [clock.stage_eq time htimeHorizon]
    calc
      clock.live time * clock.hazard time ^ k =
          clock.live time *
            (clock.hazard time * clock.hazard time ^ (k - 1)) := by
        rw [← pow_succ', Nat.sub_add_cancel hk]
      _ ≤ clock.live time *
          (clock.hazard time * threshold ^ (k - 1)) := by
        gcongr
        exact clock.live_nonneg time
      _ = threshold ^ (k - 1) *
          (clock.live time * clock.hazard time) := by ring
  have hsuffix : ∀ time, cut.cut ≤ time → time < horizon →
      clock.live time * clock.hazard time ^ k ≤ clock.stage time := by
    intro time _htimeCut htimeHorizon
    have ha0 := clock.hazard_nonneg time
    have ha1 := clock.hazard_le_one time
    have hpow : clock.hazard time ^ k ≤ clock.hazard time := by
      calc
        clock.hazard time ^ k =
            clock.hazard time * clock.hazard time ^ (k - 1) := by
          rw [← pow_succ', Nat.sub_add_cancel hk]
        _ ≤ clock.hazard time * 1 := by
          gcongr
          exact pow_le_one₀ ha0 ha1
        _ = clock.hazard time := mul_one _
    rw [clock.stage_eq time htimeHorizon]
    exact mul_le_mul_of_nonneg_left hpow (clock.live_nonneg time)
  exact (clock.sum_le_coefficient_total_add_tail
    (fun time ↦ clock.live time * clock.hazard time ^ k)
      hcoefficient hbulk hsuffix).trans
    (add_le_add le_rfl cut.tail_le)

/-- Fully unconditional threshold hierarchy.  No logarithm and no hidden
analytic premise: every positive threshold gives a valid estimate. -/
theorem moment_le_thresholdHierarchy
    {mesh threshold : ℝ} (hmesh0 : 0 ≤ mesh)
    (hthreshold0 : 0 < threshold)
    (k : ℕ) (hk : 1 ≤ k)
    (hmesh : ∀ time < horizon, clock.stage time ≤ mesh) :
    clock.moment k ≤
      threshold ^ (k - 1) * clock.total + mesh / threshold := by
  exact clock.moment_le_of_bulkTailCut hthreshold0 k hk
    (clock.bulkTailCut hmesh0 hthreshold0 hmesh)

end FiniteWeightedClock

/-! ## 3. The logarithmic potential, proved independently -/

/-- The discrete logarithmic inequality behind the sharp quadratic clock
bound.  It is stated for an arbitrary positive tail recursion so that the
analysis is reusable outside quitting games. -/
theorem sum_ratio_le_log_ratio
    (mass tail : ℕ → ℝ) (cut : ℕ)
    (htailPos : ∀ time ≤ cut, 0 < tail time)
    (hrec : ∀ time < cut,
      tail (time + 1) = tail time - mass time) :
    (∑ time ∈ Finset.range cut, mass time / tail time) ≤
      Real.log (tail 0 / tail cut) := by
  have hstep : ∀ time < cut,
      mass time / tail time ≤
        Real.log (tail time) - Real.log (tail (time + 1)) := by
    intro time htime
    have htail := htailPos time (Nat.le_of_lt htime)
    have htailNext := htailPos (time + 1) (Nat.succ_le_iff.mpr htime)
    have hratio : 0 < tail (time + 1) / tail time :=
      div_pos htailNext htail
    have hlog := Real.log_le_sub_one_of_pos hratio
    rw [Real.log_div htailNext.ne' htail.ne'] at hlog
    have hratioEq :
        tail (time + 1) / tail time - 1 =
          -(mass time / tail time) := by
      rw [hrec time htime]
      field_simp
      ring
    rw [hratioEq] at hlog
    linarith
  calc
    (∑ time ∈ Finset.range cut, mass time / tail time) ≤
        ∑ time ∈ Finset.range cut,
          (Real.log (tail time) - Real.log (tail (time + 1))) :=
      Finset.sum_le_sum fun time htime ↦
        hstep time (Finset.mem_range.mp htime)
    _ = Real.log (tail 0) - Real.log (tail cut) := by
      exact Finset.sum_range_sub' (fun time ↦ Real.log (tail time)) cut
    _ = Real.log (tail 0 / tail cut) := by
      rw [Real.log_div (htailPos 0 (Nat.zero_le cut)).ne'
        (htailPos cut le_rfl).ne']

/-- Reciprocal-potential analogue of `sum_ratio_le_log_ratio`.  This is the
integrable estimate which removes the logarithm at cubic and higher rank. -/
theorem sum_mass_div_tail_sq_le
    (mass tail : ℕ → ℝ) (cut : ℕ)
    (hmass : ∀ time < cut, 0 ≤ mass time)
    (htailPos : ∀ time ≤ cut, 0 < tail time)
    (hrec : ∀ time < cut,
      tail (time + 1) = tail time - mass time) :
    (∑ time ∈ Finset.range cut, mass time / tail time ^ 2) ≤
      1 / tail cut - 1 / tail 0 := by
  have hstep : ∀ time < cut,
      mass time / tail time ^ 2 ≤
        1 / tail (time + 1) - 1 / tail time := by
    intro time htime
    have htail := htailPos time (Nat.le_of_lt htime)
    have htailNext := htailPos (time + 1) (Nat.succ_le_iff.mpr htime)
    have htailNextLe : tail (time + 1) ≤ tail time := by
      rw [hrec time htime]
      linarith [hmass time htime]
    have hid : 1 / tail (time + 1) - 1 / tail time =
        mass time / (tail (time + 1) * tail time) := by
      field_simp [htail.ne', htailNext.ne']
      rw [hrec time htime]
      ring
    rw [hid]
    apply (div_le_div_iff₀ (sq_pos_of_pos htail)
      (mul_pos htailNext htail)).2
    exact mul_le_mul_of_nonneg_left
      (by simpa [pow_two] using
        mul_le_mul_of_nonneg_right htailNextLe htail.le)
      (hmass time htime)
  calc
    (∑ time ∈ Finset.range cut, mass time / tail time ^ 2) ≤
        ∑ time ∈ Finset.range cut,
          (1 / tail (time + 1) - 1 / tail time) :=
      Finset.sum_le_sum fun time htime ↦
        hstep time (Finset.mem_range.mp htime)
    _ = 1 / tail cut - 1 / tail 0 := by
      have htel := Finset.sum_range_sub'
        (fun time ↦ 1 / tail time) cut
      calc
        (∑ time ∈ Finset.range cut,
            (1 / tail (time + 1) - 1 / tail time)) =
            -(∑ time ∈ Finset.range cut,
              (1 / tail time - 1 / tail (time + 1))) := by
          rw [← Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl
          intro time _
          ring
        _ = 1 / tail cut - 1 / tail 0 := by rw [htel]; ring

namespace FiniteWeightedClock

variable {horizon : ℕ} (clock : FiniteWeightedClock horizon)

/-- The canonical two-mesh cut used by both sharp estimates. -/
structure SharpClockCut (mesh : ℝ) where
  cut : ℕ
  cut_le : cut ≤ horizon
  mesh_pos : 0 < mesh
  stage_le_mesh : ∀ time < horizon, clock.stage time ≤ mesh
  tail_gt_mesh : mesh < clock.tail cut
  tail_le_two_mesh : clock.tail cut ≤ 2 * mesh

theorem SharpClockCut.tail_pos {mesh : ℝ}
    (cut : clock.SharpClockCut mesh) :
    0 < clock.tail cut.cut := cut.mesh_pos.trans cut.tail_gt_mesh

theorem SharpClockCut.tail_pos_before {mesh : ℝ}
    (cut : clock.SharpClockCut mesh) {time : ℕ}
    (htime : time ≤ cut.cut) :
    0 < clock.tail time := by
  exact cut.tail_pos.trans_le (clock.tail_antitone htime)

/-- A mesh smaller than half the total clock mass canonically supplies the
two-mesh cut.  Thus the sharp estimates below have no unproduced stopping
premise. -/
noncomputable def sharpClockCut
    {mesh : ℝ} (hmeshPos : 0 < mesh)
    (htotal : 2 * mesh < clock.total)
    (hmesh : ∀ time < horizon, clock.stage time ≤ mesh) :
    clock.SharpClockCut mesh := by
  classical
  have hexists : ∃ time, time ≤ horizon ∧ clock.tail time ≤ 2 * mesh := by
    exact ⟨horizon, le_rfl, by simp [hmeshPos.le]⟩
  let cut := Nat.find hexists
  have hspec : cut ≤ horizon ∧ clock.tail cut ≤ 2 * mesh :=
    Nat.find_spec hexists
  have hcutPos : 0 < cut := by
    by_contra hnot
    have hzero : cut = 0 := Nat.eq_zero_of_not_pos hnot
    rw [hzero] at hspec
    exact (not_lt_of_ge hspec.2) htotal
  let before := cut - 1
  have hbeforeSucc : before + 1 = cut := by
    dsimp only [before]
    omega
  have hbeforeLt : before < cut := by omega
  have hbeforeHorizon : before < horizon := hbeforeLt.trans_le hspec.1
  have hbeforeTail : 2 * mesh < clock.tail before := by
    by_contra hnot
    have hwitness : before ≤ horizon ∧
        clock.tail before ≤ 2 * mesh :=
      ⟨le_trans (Nat.le_of_lt hbeforeLt) hspec.1, le_of_not_gt hnot⟩
    exact (not_le_of_gt hbeforeLt) (Nat.find_min' hexists hwitness)
  have htailStep := clock.tail_succ hbeforeHorizon
  rw [hbeforeSucc] at htailStep
  have hstage := hmesh before hbeforeHorizon
  refine ⟨cut, hspec.1, hmeshPos, hmesh, ?_, hspec.2⟩
  linarith

/-- Sharp quadratic/log estimate at a supplied two-mesh cut. -/
theorem moment_two_le_mesh_log_add_two_mesh
    {mesh : ℝ} (cut : clock.SharpClockCut mesh) :
    clock.moment 2 ≤
      mesh * Real.log (clock.total / mesh) + 2 * mesh := by
  let ratio : ℕ → ℝ := fun time ↦
    clock.stage time / clock.tail time
  have hprefixPoint : ∀ time < cut.cut,
      clock.live time * clock.hazard time ^ 2 ≤ mesh * ratio time := by
    intro time htime
    have htimeHorizon := lt_of_lt_of_le htime cut.cut_le
    have htailPos := cut.tail_pos_before clock (Nat.le_of_lt htime)
    have htailLive := clock.tail_le_live (Nat.le_of_lt htimeHorizon)
    have hstage0 := clock.stage_nonneg htimeHorizon
    have hstageMesh := cut.stage_le_mesh time htimeHorizon
    dsimp only [ratio]
    rw [← mul_div_assoc]
    apply (le_div_iff₀ htailPos).2
    have hfirst :
        (clock.live time * clock.hazard time ^ 2) * clock.tail time ≤
          (clock.live time * clock.hazard time ^ 2) * clock.live time :=
      mul_le_mul_of_nonneg_left htailLive
        (mul_nonneg (clock.live_nonneg time) (sq_nonneg _))
    have hsquare :
        (clock.live time * clock.hazard time ^ 2) * clock.live time =
          clock.stage time * clock.stage time := by
      rw [clock.stage_eq time htimeHorizon]
      ring
    rw [hsquare] at hfirst
    exact hfirst.trans
      (mul_le_mul_of_nonneg_right hstageMesh hstage0)
  have hprefix :
      (∑ time ∈ Finset.range cut.cut,
          clock.live time * clock.hazard time ^ 2) ≤
        mesh * Real.log (clock.total / clock.tail cut.cut) := by
    calc
      _ ≤ ∑ time ∈ Finset.range cut.cut, mesh * ratio time :=
        Finset.sum_le_sum fun time htime ↦
          hprefixPoint time (Finset.mem_range.mp htime)
      _ = mesh * (∑ time ∈ Finset.range cut.cut, ratio time) := by
        rw [Finset.mul_sum]
      _ ≤ mesh * Real.log (clock.tail 0 / clock.tail cut.cut) := by
        gcongr
        exact cut.mesh_pos.le
        exact sum_ratio_le_log_ratio clock.stage clock.tail cut.cut
          (fun time htime ↦ cut.tail_pos_before clock htime)
          (fun time htime ↦ clock.tail_succ
            (lt_of_lt_of_le htime cut.cut_le))
      _ = mesh * Real.log (clock.total / clock.tail cut.cut) := by
        rfl
  have htailPoint : ∀ time, cut.cut ≤ time → time < horizon →
      clock.live time * clock.hazard time ^ 2 ≤ clock.stage time := by
    intro time _ htime
    rw [clock.stage_eq time htime]
    have ha0 := clock.hazard_nonneg time
    have ha1 := clock.hazard_le_one time
    have hsquare : clock.hazard time ^ 2 ≤ clock.hazard time := by
      nlinarith [sq_nonneg (clock.hazard time)]
    exact mul_le_mul_of_nonneg_left hsquare (clock.live_nonneg time)
  have htail :
      (∑ time ∈ Finset.Ico cut.cut horizon,
          clock.live time * clock.hazard time ^ 2) ≤ clock.tail cut.cut :=
    Finset.sum_le_sum fun time htime ↦
      htailPoint time (Finset.mem_Ico.mp htime).1
        (Finset.mem_Ico.mp htime).2
  have hlogMono :
      Real.log (clock.total / clock.tail cut.cut) ≤
        Real.log (clock.total / mesh) := by
    have htotalPos : 0 < clock.total := by
      exact cut.tail_pos.trans_le (clock.tail_antitone (Nat.zero_le cut.cut))
    rw [Real.log_div htotalPos.ne' cut.tail_pos.ne',
      Real.log_div htotalPos.ne' cut.mesh_pos.ne']
    have hlog := Real.strictMonoOn_log.monotoneOn
      cut.mesh_pos cut.tail_pos cut.tail_gt_mesh.le
    linarith
  unfold moment
  rw [← Finset.sum_range_add_sum_Ico
    (fun time ↦ clock.live time * clock.hazard time ^ 2) cut.cut_le]
  calc
    _ ≤ mesh * Real.log (clock.total / clock.tail cut.cut) +
        clock.tail cut.cut := add_le_add hprefix htail
    _ ≤ mesh * Real.log (clock.total / mesh) + 2 * mesh :=
      add_le_add
        (mul_le_mul_of_nonneg_left hlogMono cut.mesh_pos.le)
        cut.tail_le_two_mesh

/-- Cubic and all higher moments have no logarithmic loss.  The constant `3`
is uniform in the rank. -/
theorem moment_higher_le_three_mesh
    {mesh : ℝ} (cut : clock.SharpClockCut mesh)
    (k : ℕ) (hk : 3 ≤ k) :
    clock.moment k ≤ 3 * mesh := by
  -- The reciprocal-potential proof is factored as a reusable bound on the
  -- cubic moment; higher powers only decrease on `[0,1]`.
  have hcubicPrefixPoint : ∀ time < cut.cut,
      clock.live time * clock.hazard time ^ 3 ≤
        mesh ^ 2 * (clock.stage time / clock.tail time ^ 2) := by
    intro time htime
    have htimeHorizon := lt_of_lt_of_le htime cut.cut_le
    have htailPos := cut.tail_pos_before clock (Nat.le_of_lt htime)
    have htailLive := clock.tail_le_live (Nat.le_of_lt htimeHorizon)
    have hstage0 := clock.stage_nonneg htimeHorizon
    have hstageMesh := cut.stage_le_mesh time htimeHorizon
    rw [← mul_div_assoc]
    apply (le_div_iff₀ (sq_pos_of_pos htailPos)).2
    have hfirst :
        (clock.live time * clock.hazard time ^ 3) * clock.tail time ^ 2 ≤
          (clock.live time * clock.hazard time ^ 3) * clock.live time ^ 2 :=
      mul_le_mul_of_nonneg_left
        ((sq_le_sq₀ (clock.tail_nonneg time) (clock.live_nonneg time)).2
          htailLive)
        (mul_nonneg (clock.live_nonneg time) (pow_nonneg (clock.hazard_nonneg time) _))
    have hrewrite :
        (clock.live time * clock.hazard time ^ 3) * clock.live time ^ 2 =
          clock.stage time ^ 3 := by
      rw [clock.stage_eq time htimeHorizon]
      ring
    rw [hrewrite] at hfirst
    have hcubic : clock.stage time ^ 3 ≤ mesh ^ 2 * clock.stage time := by
      have hfactor := mul_nonneg
        (mul_nonneg (sub_nonneg.mpr hstageMesh)
          (add_nonneg cut.mesh_pos.le hstage0)) hstage0
      nlinarith
    exact hfirst.trans hcubic
  have hcubicPrefix :
      (∑ time ∈ Finset.range cut.cut,
          clock.live time * clock.hazard time ^ 3) ≤ mesh := by
    calc
      _ ≤ ∑ time ∈ Finset.range cut.cut,
          mesh ^ 2 * (clock.stage time / clock.tail time ^ 2) :=
        Finset.sum_le_sum fun time htime ↦
          hcubicPrefixPoint time (Finset.mem_range.mp htime)
      _ = mesh ^ 2 * (∑ time ∈ Finset.range cut.cut,
          clock.stage time / clock.tail time ^ 2) := by rw [Finset.mul_sum]
      _ ≤ mesh ^ 2 * (1 / clock.tail cut.cut - 1 / clock.tail 0) := by
        gcongr
        exact sum_mass_div_tail_sq_le clock.stage clock.tail cut.cut
          (fun time htime ↦ clock.stage_nonneg
            (lt_of_lt_of_le htime cut.cut_le))
          (fun time htime ↦ cut.tail_pos_before clock htime)
          (fun time htime ↦ clock.tail_succ
            (lt_of_lt_of_le htime cut.cut_le))
      _ ≤ mesh := by
        have htailInv : 1 / clock.tail cut.cut ≤ 1 / mesh := by
          exact one_div_le_one_div_of_le cut.mesh_pos cut.tail_gt_mesh.le
        have hzeroInv : 0 ≤ 1 / clock.tail 0 :=
          div_nonneg zero_le_one
            (cut.tail_pos_before clock (Nat.zero_le cut.cut)).le
        have hmesh0 := cut.mesh_pos.le
        calc
          mesh ^ 2 * (1 / clock.tail cut.cut - 1 / clock.tail 0) ≤
              mesh ^ 2 * (1 / mesh) := by nlinarith [sq_nonneg mesh]
          _ = mesh := by field_simp
  have hcubicTail :
      (∑ time ∈ Finset.Ico cut.cut horizon,
          clock.live time * clock.hazard time ^ 3) ≤ 2 * mesh := by
    calc
      _ ≤ ∑ time ∈ Finset.Ico cut.cut horizon, clock.stage time := by
        apply Finset.sum_le_sum
        intro time htime
        have ht := (Finset.mem_Ico.mp htime).2
        rw [clock.stage_eq time ht]
        have ha0 := clock.hazard_nonneg time
        have ha1 := clock.hazard_le_one time
        have hp : clock.hazard time ^ 3 ≤ clock.hazard time := by
          nlinarith [sq_nonneg (clock.hazard time),
            mul_nonneg ha0 (sub_nonneg.mpr ha1)]
        exact mul_le_mul_of_nonneg_left hp (clock.live_nonneg time)
      _ = clock.tail cut.cut := rfl
      _ ≤ 2 * mesh := cut.tail_le_two_mesh
  have hcubic : clock.moment 3 ≤ 3 * mesh := by
    unfold moment
    rw [← Finset.sum_range_add_sum_Ico
      (fun time ↦ clock.live time * clock.hazard time ^ 3) cut.cut_le]
    linarith
  calc
    clock.moment k ≤ clock.moment 3 := by
      unfold moment
      apply Finset.sum_le_sum
      intro time _
      apply mul_le_mul_of_nonneg_left _ (clock.live_nonneg time)
      exact pow_le_pow_of_le_one (clock.hazard_nonneg time)
        (clock.hazard_le_one time) hk
    _ ≤ 3 * mesh := hcubic

/-- A rowwise union-bound interface for events requiring `rank` distinct
opponents.  `opponentCount` is a combinatorial coefficient; it is not a
claim that the game has been reduced to that many players. -/
structure RankDominatedMass
    (opponentCount rank : ℕ) (mass : ℕ → ℝ) : Prop where
  nonneg : ∀ time < horizon, 0 ≤ mass time
  le_moment : ∀ time < horizon,
    mass time ≤ (opponentCount.choose rank : ℝ) *
      (clock.live time * clock.hazard time ^ rank)

theorem sum_rankDominatedMass_le_moment
    {opponentCount rank : ℕ} {mass : ℕ → ℝ}
    (dominated : clock.RankDominatedMass opponentCount rank mass) :
    (∑ time ∈ Finset.range horizon, mass time) ≤
      (opponentCount.choose rank : ℝ) * clock.moment rank := by
  unfold moment
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun time htime ↦
    dominated.le_moment time (Finset.mem_range.mp htime)

/-- Quadratic/log union-bound hierarchy. -/
theorem sum_rankTwoMass_le
    {mesh : ℝ} (cut : clock.SharpClockCut mesh)
    {opponentCount : ℕ} {mass : ℕ → ℝ}
    (dominated : clock.RankDominatedMass opponentCount 2 mass) :
    (∑ time ∈ Finset.range horizon, mass time) ≤
      (opponentCount.choose 2 : ℝ) *
        (mesh * Real.log (clock.total / mesh) + 2 * mesh) := by
  exact (clock.sum_rankDominatedMass_le_moment dominated).trans
    (mul_le_mul_of_nonneg_left
      (clock.moment_two_le_mesh_log_add_two_mesh cut)
      (Nat.cast_nonneg _))

/-- Every opponent-rank at least three is mesh-scale, with one constant
uniform in the rank. -/
theorem sum_higherRankMass_le
    {mesh : ℝ} (cut : clock.SharpClockCut mesh)
    {opponentCount rank : ℕ} (hrank : 3 ≤ rank)
    {mass : ℕ → ℝ}
    (dominated : clock.RankDominatedMass opponentCount rank mass) :
    (∑ time ∈ Finset.range horizon, mass time) ≤
      (opponentCount.choose rank : ℝ) * (3 * mesh) := by
  exact (clock.sum_rankDominatedMass_le_moment dominated).trans
    (mul_le_mul_of_nonneg_left
      (clock.moment_higher_le_three_mesh cut rank hrank)
      (Nat.cast_nonneg _))

end FiniteWeightedClock

/-! ## 4b. Conditional scale statements and the high-rank fence -/

/-- An `O(mesh)` higher-rank remainder vanishes after division by a larger
positive strategic scale.  This is the one-way hypothesis needed for a pair
window; no converse is asserted. -/
theorem div_scale_le_of_mass_le_mesh
    {mass mesh scale coefficient epsilon : ℝ}
    (hcoefficient : 0 ≤ coefficient)
    (hscale : 0 < scale)
    (hmass : mass ≤ coefficient * mesh)
    (hmesh : mesh ≤ epsilon * scale) :
    mass / scale ≤ coefficient * epsilon := by
  apply (div_le_iff₀ hscale).2
  calc
    mass ≤ coefficient * mesh := hmass
    _ ≤ coefficient * (epsilon * scale) :=
      mul_le_mul_of_nonneg_left hmesh hcoefficient
    _ = coefficient * epsilon * scale := by ring

/-- Arithmetic regression: at any prescribed rank, independent hazards can
place exactly `scale` mass on the full rank coalition.  This protects the
formal package from an unconditional pair-only tangent claim. -/
theorem arbitraryRankFineBlowup
    (rank : ℕ) (hrank : 0 < rank)
    (live scale : ℝ) (hlive : 0 < live) (hscale : 0 < scale) :
    let hazard :=
      Math.CurveSelection.Internal.PositiveRoot.positiveNatRoot rank
        (scale / live)
    0 < hazard ∧ live * hazard ^ rank = scale := by
  dsimp only
  have hquot : 0 < scale / live := div_pos hscale hlive
  refine ⟨Math.CurveSelection.Internal.PositiveRoot.positiveNatRoot_pos hquot, ?_⟩
  rw [Math.CurveSelection.Internal.PositiveRoot.positiveNatRoot_pow hrank hquot.le]
  field_simp

/-- Sequential form of the regression: the common hazard tends to zero while
the exact full-rank atom remains equal to the chosen strategic scale. -/
theorem arbitraryRankFineBlowupSequence
    (rank : ℕ) (hrank : 0 < rank) (live : ℝ) (hlive : 0 < live)
    (scale : ℕ → ℝ) (hscalePos : ∀ index, 0 < scale index)
    (hscale : Filter.Tendsto scale Filter.atTop (nhds 0)) :
    let hazard : ℕ → ℝ := fun index ↦
      Math.CurveSelection.Internal.PositiveRoot.positiveNatRoot rank
        (scale index / live)
    Filter.Tendsto hazard Filter.atTop (nhdsWithin 0 (Set.Ioi 0)) ∧
      ∀ index, live * hazard index ^ rank = scale index := by
  dsimp only
  have hquotPos : ∀ index, 0 < scale index / live := fun index ↦
    div_pos (hscalePos index) hlive
  have hquot : Filter.Tendsto (fun index ↦ scale index / live)
      Filter.atTop (nhds 0) := by
    simpa only [zero_div] using hscale.div_const live
  refine ⟨Math.CurveSelection.Internal.PositiveRoot.tendsto_positiveNatRoot
      hrank hquotPos hquot, ?_⟩
  intro index
  rw [Math.CurveSelection.Internal.PositiveRoot.positiveNatRoot_pow
    hrank (hquotPos index).le]
  field_simp

/-! ## 4. A true total-variation repair lemma -/

section LawRepair

variable {Outcome : Type} [Fintype Outcome] [DecidableEq Outcome]

/-- Mass outside a chosen good set. -/
def badMass (law : Outcome → ℝ) (good : Finset Outcome) : ℝ :=
  ∑ outcome ∈ goodᶜ, law outcome

/-- Move all bad mass to one fixed good anchor. -/
def repairLaw (law : Outcome → ℝ) (good : Finset Outcome)
    (anchor : Outcome) : Outcome → ℝ := fun outcome ↦
  if outcome = anchor then law outcome + badMass law good
  else if outcome ∈ good then law outcome else 0

theorem badMass_nonneg (law : Outcome → ℝ) (good : Finset Outcome)
    (hlaw : ∀ outcome, 0 ≤ law outcome) :
    0 ≤ badMass law good := by
  exact Finset.sum_nonneg fun outcome _ ↦ hlaw outcome

theorem repairLaw_nonneg (law : Outcome → ℝ) (good : Finset Outcome)
    (anchor : Outcome) (hlaw : ∀ outcome, 0 ≤ law outcome) :
    ∀ outcome, 0 ≤ repairLaw law good anchor outcome := by
  intro outcome
  unfold repairLaw
  split_ifs
  · exact add_nonneg (hlaw outcome) (badMass_nonneg law good hlaw)
  · exact hlaw outcome
  · exact le_rfl

theorem repairLaw_supported (law : Outcome → ℝ) (good : Finset Outcome)
    {anchor outcome : Outcome} (hanchor : anchor ∈ good)
    (houtcome : outcome ∉ good) :
    repairLaw law good anchor outcome = 0 := by
  unfold repairLaw
  have hne : outcome ≠ anchor := fun heq ↦ houtcome (heq ▸ hanchor)
  simp [hne, houtcome]

/-- The repaired law has the same total mass. -/
theorem sum_repairLaw (law : Outcome → ℝ) (good : Finset Outcome)
    {anchor : Outcome} (hanchor : anchor ∈ good) :
    ∑ outcome, repairLaw law good anchor outcome = ∑ outcome, law outcome := by
  classical
  have hsplit :
      (∑ outcome ∈ good, law outcome) + badMass law good =
        ∑ outcome, law outcome := by
    simpa [badMass] using good.sum_add_sum_compl law
  calc
    (∑ outcome, repairLaw law good anchor outcome) =
        ∑ outcome, if outcome ∈ good then
          repairLaw law good anchor outcome else 0 := by
      apply Finset.sum_congr rfl
      intro outcome _
      by_cases hgood : outcome ∈ good
      · simp [hgood]
      · have hne : outcome ≠ anchor := fun heq ↦ hgood (heq ▸ hanchor)
        simp [hgood, hne, repairLaw]
    _ = ∑ outcome ∈ good, repairLaw law good anchor outcome := by
      rw [← Finset.sum_filter]
      simp
    _ = ∑ outcome ∈ good,
        (law outcome + if outcome = anchor then badMass law good else 0) := by
      apply Finset.sum_congr rfl
      intro outcome houtcome
      by_cases heq : outcome = anchor <;>
        simp [repairLaw, houtcome, heq]
    _ = (∑ outcome ∈ good, law outcome) + badMass law good := by
      rw [Finset.sum_add_distrib]
      simp [hanchor]
    _ = ∑ outcome, law outcome := hsplit

/-- Exact `L¹` cost of repairing a nonnegative law.  Consequently the
usual total-variation distance (half the displayed sum) is exactly the bad
mass. -/
theorem sum_abs_repairLaw_sub
    (law : Outcome → ℝ) (good : Finset Outcome)
    {anchor : Outcome} (hanchor : anchor ∈ good)
    (hlaw : ∀ outcome, 0 ≤ law outcome) :
    (∑ outcome, |repairLaw law good anchor outcome - law outcome|) =
      2 * badMass law good := by
  classical
  have hbad0 := badMass_nonneg law good hlaw
  have hpoint : ∀ outcome,
      |repairLaw law good anchor outcome - law outcome| =
        if outcome = anchor then badMass law good
        else if outcome ∈ good then 0 else law outcome := by
    intro outcome
    by_cases hanchorEq : outcome = anchor
    · subst outcome
      simp [repairLaw, abs_of_nonneg hbad0]
    · by_cases hgood : outcome ∈ good
      · simp [repairLaw, hanchorEq, hgood]
      · simp [repairLaw, hanchorEq, hgood, abs_of_nonneg (hlaw outcome)]
  calc
    (∑ outcome, |repairLaw law good anchor outcome - law outcome|) =
        ∑ outcome,
          (if outcome = anchor then badMass law good
          else if outcome ∈ good then 0 else law outcome) := by
      apply Finset.sum_congr rfl
      intro outcome _
      exact hpoint outcome
    _ = badMass law good + ∑ outcome ∈ goodᶜ, law outcome := by
      let rest : Outcome → ℝ := fun outcome ↦
        if outcome ∈ good then 0 else law outcome
      have hsplitAnchor :
          (∑ outcome,
              if outcome = anchor then badMass law good
              else if outcome ∈ good then 0 else law outcome) =
            badMass law good +
              ∑ outcome ∈ Finset.univ.erase anchor, rest outcome := by
        let expression : Outcome → ℝ := fun outcome ↦
          if outcome = anchor then badMass law good
          else if outcome ∈ good then 0 else law outcome
        have hsplit := Finset.sum_erase_add Finset.univ expression
          (Finset.mem_univ anchor)
        have hanchorValue : expression anchor = badMass law good := by
          simp [expression]
        have heraseExpression :
            (∑ outcome ∈ Finset.univ.erase anchor, expression outcome) =
              ∑ outcome ∈ Finset.univ.erase anchor, rest outcome := by
          apply Finset.sum_congr rfl
          intro outcome houtcome
          have hne := Finset.ne_of_mem_erase houtcome
          simp [expression, rest, hne]
        change (∑ outcome, expression outcome) = _
        rw [← hsplit, hanchorValue, heraseExpression, add_comm]
      rw [hsplitAnchor]
      congr 1
      have herase :
          (∑ outcome ∈ Finset.univ.erase anchor, rest outcome) =
            ∑ outcome, rest outcome := by
        have h := Finset.sum_erase_add Finset.univ rest
          (Finset.mem_univ anchor)
        have hzero : rest anchor = 0 := by simp [rest, hanchor]
        rw [hzero, add_zero] at h
        exact h
      rw [herase]
      unfold rest
      calc
        (∑ outcome, if outcome ∈ good then 0 else law outcome) =
            ∑ outcome, if outcome ∈ goodᶜ then law outcome else 0 := by
          apply Finset.sum_congr rfl
          intro outcome _
          simp
        _ = ∑ outcome ∈ goodᶜ, law outcome := by
          rw [← Finset.sum_filter]
          apply Finset.sum_congr
          · ext outcome
            simp
          · intro outcome _
            rfl
    _ = 2 * badMass law good := by
      simp [badMass]
      ring

/-- Full finite-law singletonization/repair package.  If `good` is the set
of exact singleton opponent outcomes, the conclusion is a same-mass law
supported on those outcomes at total-variation cost exactly `badMass`.
The statement is deliberately generic: a clock estimate supplies the bound
on `badMass`; this theorem performs the law-level transport. -/
theorem exists_supported_repair
    (law : Outcome → ℝ) (good : Finset Outcome)
    {anchor : Outcome} (hanchor : anchor ∈ good)
    (hlaw : ∀ outcome, 0 ≤ law outcome) :
    ∃ repaired : Outcome → ℝ,
      (∀ outcome, 0 ≤ repaired outcome) ∧
      (∀ outcome, outcome ∉ good → repaired outcome = 0) ∧
      (∑ outcome, repaired outcome = ∑ outcome, law outcome) ∧
      (∑ outcome, |repaired outcome - law outcome|) =
        2 * badMass law good := by
  exact ⟨repairLaw law good anchor,
    repairLaw_nonneg law good anchor hlaw,
    fun outcome houtcome ↦ repairLaw_supported law good hanchor houtcome,
    sum_repairLaw law good hanchor,
    sum_abs_repairLaw_sub law good hanchor hlaw⟩

end LawRepair

/-! ## 5. Aggregate collision energy -/

section CollisionEnergy

variable {Player : Type} [Fintype Player] [DecidableEq Player]

/-- Collision is contained in every player's opponent-absorption event.
This aggregate inclusion is stronger than charging each coalition and then
summing: no number-of-coalitions factor is introduced. -/
theorem collisionMass_le_opponentAbsorption
    (root : Player → PMF Bool) (owner : Player) :
    quittingRootCollisionMass root ≤
      quittingRootOpponentAbsorptionMass root owner := by
  let rate : Player → ℝ := quittingRootQuitRates root
  have hrate0 : ∀ who, 0 ≤ rate who := fun _ ↦ ENNReal.toReal_nonneg
  have hrate1 : ∀ who, rate who ≤ 1 := fun who ↦
    ENNReal.toReal_mono ENNReal.one_ne_top ((root who).coe_le_one true)
  let others : Finset Player := Finset.univ.erase owner
  have hownerNot : owner ∉ others := by simp [others]
  have huniv : (Finset.univ : Finset Player) = insert owner others := by
    exact (Finset.insert_erase (Finset.mem_univ owner)).symm
  have hcollisionRest0 : 0 ≤ collisionMassFormulaOn rate others :=
    collisionMassFormulaOn_nonneg rate others
      (fun who _ ↦ hrate0 who) (fun who _ ↦ hrate1 who)
  have habsorptionRest0 :
      0 ≤ 1 - ∏ who ∈ others, (1 - rate who) := by
    exact sub_nonneg.mpr (Finset.prod_le_one
      (fun who _ ↦ sub_nonneg.mpr (hrate1 who))
      (fun who _ ↦ by linarith [hrate0 who]))
  have hcollisionRestLe : collisionMassFormulaOn rate others ≤
      1 - ∏ who ∈ others, (1 - rate who) := by
    unfold collisionMassFormulaOn
    have hsingle0 : 0 ≤ ∑ who ∈ others,
        rate who * ∏ other ∈ others.erase who, (1 - rate other) := by
      exact Finset.sum_nonneg fun who hwho ↦ mul_nonneg (hrate0 who)
        (Finset.prod_nonneg fun other hother ↦
          sub_nonneg.mpr (hrate1 other))
    linarith
  have hformula : collisionMass rate =
      (1 - rate owner) * collisionMassFormulaOn rate others +
        rate owner * (1 - ∏ who ∈ others, (1 - rate who)) := by
    rw [collisionMass_eq_one_sub_continueMass_sub_singletonMass]
    change collisionMassFormulaOn rate Finset.univ = _
    rw [huniv, collisionMassFormulaOn_insert rate hownerNot]
  have hbound : collisionMass rate ≤
      1 - ∏ who ∈ others, (1 - rate who) := by
    rw [hformula]
    calc
      (1 - rate owner) * collisionMassFormulaOn rate others +
          rate owner * (1 - ∏ who ∈ others, (1 - rate who)) ≤
        (1 - rate owner) *
            (1 - ∏ who ∈ others, (1 - rate who)) +
          rate owner * (1 - ∏ who ∈ others, (1 - rate who)) := by
            gcongr
            exact sub_nonneg.mpr (hrate1 owner)
      _ = 1 - ∏ who ∈ others, (1 - rate who) := by ring
  rw [_root_.GameTheory.quittingRootOpponentAbsorptionMass_eq_one_sub_prod]
  simpa only [quittingRootCollisionMass, rate, others,
    quittingRootQuitRates] using hbound

/-- Abstract rank-blind collision charge. -/
theorem collisionMass_mul_debtSum_le_opponentCharge
    (root : Player → PMF Bool) (debt : Player → ℝ)
    (hdebt : ∀ who, 0 ≤ debt who) :
    quittingRootCollisionMass root * (∑ who, debt who) ≤
      ∑ who, quittingRootOpponentAbsorptionMass root who * debt who := by
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun who _ ↦
    mul_le_mul_of_nonneg_right
      (collisionMass_le_opponentAbsorption root who) (hdebt who)

/-- Two positive Quit marginals force strictly positive collision mass. -/
theorem collisionMass_pos_of_two_positive
    (root : Player → PMF Bool) {first second : Player}
    (hne : first ≠ second)
    (hfirst : 0 < (root first true).toReal)
    (hsecond : 0 < (root second true).toReal) :
    0 < quittingRootCollisionMass root := by
  classical
  let rate : Player → ℝ := quittingRootQuitRates root
  let support : Finset Player := Finset.univ.filter fun who ↦ 0 < rate who
  have hrate0 : ∀ who, 0 ≤ rate who := fun _ ↦ ENNReal.toReal_nonneg
  have hrate1 : ∀ who, rate who ≤ 1 := fun who ↦
    ENNReal.toReal_mono ENNReal.one_ne_top ((root who).coe_le_one true)
  have hfirstMem : first ∈ support := by
    simp [support, rate, quittingRootQuitRates, hfirst]
  have hsecondMem : second ∈ support := by
    simp [support, rate, quittingRootQuitRates, hsecond]
  have hcard : 2 ≤ support.card := by
    have hsubset : ({first, second} : Finset Player) ⊆ support := by
      intro who hwho
      simp only [Finset.mem_insert, Finset.mem_singleton] at hwho
      rcases hwho with rfl | rfl
      · exact hfirstMem
      · exact hsecondMem
    have hpairCard : ({first, second} : Finset Player).card = 2 := by
      simp [hne]
    rw [← hpairCard]
    exact Finset.card_le_card hsubset
  have hinside : 0 < ∏ who ∈ support, rate who := by
    exact Finset.prod_pos fun who hwho ↦
      (Finset.mem_filter.mp hwho).2
  have houtside : 0 < ∏ who ∈ supportᶜ, (1 - rate who) := by
    apply Finset.prod_pos
    intro who hwho
    have hnot : who ∉ support := by simpa using hwho
    have hzero : rate who = 0 := by
      have hnpos : ¬ 0 < rate who := by
        simpa [support] using hnot
      exact le_antisymm (le_of_not_gt hnpos) (hrate0 who)
    simp [hzero]
  have hcoalition : 0 < coalitionMass rate support := by
    unfold coalitionMass
    exact mul_pos hinside houtside
  have hmem : support ∈ Finset.univ.filter
      (fun coalition : Finset Player ↦ 2 ≤ coalition.card) := by
    simp [hcard]
  have hterms : ∀ coalition ∈
      Finset.univ.filter (fun coalition : Finset Player ↦ 2 ≤ coalition.card),
      0 ≤ coalitionMass rate coalition := by
    intro coalition _
    unfold coalitionMass
    exact mul_nonneg
      (Finset.prod_nonneg fun who _ ↦ hrate0 who)
      (Finset.prod_nonneg fun who _ ↦ sub_nonneg.mpr (hrate1 who))
  have hle : coalitionMass rate support ≤ collisionMass rate := by
    exact Finset.single_le_sum hterms hmem
  exact hcoalition.trans_le (by
    simpa [quittingRootCollisionMass, rate] using hle)

/-- Collision-freeness is a genuine rank-one statement about one product
root: any two positive Quit marginals name the same player.  It is not a
reduction in the cardinality of the ambient player type. -/
theorem atMostOnePositive_of_collisionMass_eq_zero
    (root : Player → PMF Bool)
    (hzero : quittingRootCollisionMass root = 0)
    {first second : Player}
    (hfirst : 0 < (root first true).toReal)
    (hsecond : 0 < (root second true).toReal) :
    first = second := by
  by_contra hne
  have hpos := collisionMass_pos_of_two_positive root hne hfirst hsecond
  rw [hzero] at hpos
  exact lt_irrefl 0 hpos

/-- **Aggregate minimum-debt inequality.** All coalition ranks at least two
are charged once by one collision scalar. -/
theorem collisionMass_mul_minimumDebt_le_tailExcess_add_totalDefect
    {reward : {S : Finset Player // S.Nonempty} → Payoff Player}
    (minimum tail : QuittingTerminalSemanticPair Player)
    (root : Player → PMF Bool)
    (hminimumCarrier : minimum ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (htail : tail ∈ quittingTerminalSemanticCarrier reward) :
    quittingRootCollisionMass root *
        quittingTerminalSemanticDebtSum minimum ≤
      (quittingTerminalSemanticDebtSum tail -
          quittingTerminalSemanticDebtSum minimum) +
        quittingRootTotalNashDefect reward tail.1 root := by
  obtain ⟨M, hM, hreward⟩ :=
    exists_quittingRewardBound reward
  have htailDebt : ∀ who, 0 ≤ quittingTerminalSemanticDebt tail who :=
    quittingTerminalSemanticDebt_nonneg_of_mem_carrier
      reward hM hreward htail
  have hcollision0 := quittingRootCollisionMass_nonneg root
  have hminimumLeTail := hminimum tail htail
  have htoTail :
      quittingRootCollisionMass root *
          quittingTerminalSemanticDebtSum minimum ≤
        quittingRootCollisionMass root *
          quittingTerminalSemanticDebtSum tail :=
    mul_le_mul_of_nonneg_left hminimumLeTail hcollision0
  have htoCharge := collisionMass_mul_debtSum_le_opponentCharge root
    (fun who ↦ quittingTerminalSemanticDebt tail who) htailDebt
  have hcharge :=
    minimumTerminalSemantic_sum_opponentAbsorption_charge_le_excess_add_defect
      reward minimum tail root hM hreward hminimumCarrier hminimum htail
  exact htoTail.trans (htoCharge.trans hcharge)

/-- `ε`-Nash specialization of the aggregate collision charge. -/
theorem collisionMass_mul_minimumDebt_le_tailExcess_add_card_mul_nashError
    {reward : {S : Finset Player // S.Nonempty} → Payoff Player}
    (minimum tail : QuittingTerminalSemanticPair Player)
    (root : Player → PMF Bool) (ε : ℝ)
    (hminimumCarrier : minimum ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (htail : tail ∈ quittingTerminalSemanticCarrier reward)
    (hnash : IsεQuittingRootNash reward tail.1 ε root) :
    quittingRootCollisionMass root *
        quittingTerminalSemanticDebtSum minimum ≤
      (quittingTerminalSemanticDebtSum tail -
          quittingTerminalSemanticDebtSum minimum) +
        Fintype.card Player * ε := by
  have haggregate :=
    collisionMass_mul_minimumDebt_le_tailExcess_add_totalDefect
      minimum tail root hminimumCarrier hminimum htail
  have hdefect :=
    quittingRootTotalNashDefect_le_card_mul_of_isεQuittingRootNash
      reward tail.1 root ε hnash
  linarith

/-- Exact Nash at a positive minimum semantic point has at most one active
quitter. -/
theorem minimumExactNash_atMostOnePositiveQuitter
    {reward : {S : Finset Player // S.Nonempty} → Payoff Player}
    (minimum : QuittingTerminalSemanticPair Player)
    (root : Player → PMF Bool)
    (hminimumCarrier : minimum ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpositive : 0 < quittingTerminalSemanticDebtSum minimum)
    (hnash : IsεQuittingRootNash reward minimum.1 0 root)
    {first second : Player}
    (hfirst : 0 < (root first true).toReal)
    (hsecond : 0 < (root second true).toReal) :
    first = second := by
  obtain ⟨M, hM, hreward⟩ :=
    exists_quittingRewardBound reward
  have hcollisionZero :=
    (minimumTerminalSemantic_exactNash_criticalFace
      (reward := reward) minimum root hM hreward hminimumCarrier hminimum
        hpositive hnash).1
  exact atMostOnePositive_of_collisionMass_eq_zero root hcollisionZero
    hfirst hsecond

end CollisionEnergy

/-! ## 6. Adapter to the landed diffuse-clock producer -/

section LandedAdapter

variable {Player : Type} [Fintype Player] [DecidableEq Player]
variable {reward : {S : Finset Player // S.Nonempty} → Payoff Player}

/-- Current HEAD already supplies the owner-sensitive part not encoded by
the abstract opponent moments: a fixed positive coalition on a complete
diffuse deleted-player clock is exactly one opponent singleton.  This
wrapper records the dependency explicitly.

It is a coalition-rank conclusion.  It neither deletes players nor bounds
the cardinality of `Player`; the distinct player-cardinality deletion
alternative of Question 175 is logically separate. -/
theorem landedDiffuseClock_fixedCoalition_eq_opponentSingleton
    {profiles : ℕ → (quittingGame reward).BehaviorProfile}
    {owner : Player}
    {terminal : {S : Finset Player // S.Nonempty}}
    {cutoff : ℕ → ℕ} {scale : ℕ → ℝ} {lower : ℝ}
    (packet : QuittingReprojectionDiffuseDeletedWindowPacket
      reward profiles owner terminal cutoff scale lower)
    (other : Player) (hother : other ∈ terminal.val)
    (hne : other ≠ owner) :
    terminal.val = {other} := by
  exact packet.terminal_eq_singleton other hother hne

end LandedAdapter

end GameTheory.Experiments.WeightedClockRankReduction
