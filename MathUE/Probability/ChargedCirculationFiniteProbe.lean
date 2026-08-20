/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.Probability.ChargedOccupationAlternative
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

/-!
# Finite probes detect a charged circulation

A circulation may balance every selected coordinate while drifting in an
unrecorded coordinate. If there are only finitely many moves, however, this
hidden obstruction is automatically finite-rank.

For an arbitrary (even infinite) type of probes, regard each probe as a row
vector on the finite move space.  A finite subset of those row vectors spans
all of them.  Therefore one finite set of probes has the following exact
property: a nonnegative normalized charged mass balances those probes if and
only if it balances *every* probe.

This is an abstract finite-rank reduction. Applications choose the probe
family and interpret the resulting finite packet or potential.
-/

noncomputable section

namespace Math
namespace Probability

open Finset BigOperators

variable {Move Probe : Type*} [Fintype Move]

/-- The row vector on move space detected by one scalar probe. -/
def chargedProbeRow (column : Move → Probe → ℝ) (probe : Probe) : Move → ℝ :=
  fun move ↦ column move probe

/-- Pairing with a fixed occupation mass is a linear functional on probe
rows. -/
def chargedProbePair (mass : Move → ℝ) : (Move → ℝ) →ₗ[ℝ] ℝ where
  toFun row := ∑ move, mass move * row move
  map_add' left right := by
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' scalar row := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro move _
    ring

/-! ## A finite spanning probe packet -/

/-- Any family of probe rows on a finite move space is spanned by finitely
many rows from the family. -/
theorem exists_finset_chargedProbeRow_span_eq
    (column : Move → Probe → ℝ) :
    ∃ probes : Finset Probe,
      probes.card ≤ Fintype.card Move ∧
        Submodule.span ℝ
          (chargedProbeRow column '' (probes : Set Probe)) =
        Submodule.span ℝ (Set.range (chargedProbeRow column)) := by
  classical
  let rows : Set (Move → ℝ) := Set.range (chargedProbeRow column)
  obtain ⟨basisRow, hbasisMem, hbasisSpan, _hbasisIndependent⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq ℝ rows
  let chooseProbe :
      Fin (Module.finrank ℝ (Submodule.span ℝ rows)) → Probe :=
    fun index ↦ (Set.mem_range.mp (hbasisMem index)).choose
  have hchooseProbe : ∀ index,
      chargedProbeRow column (chooseProbe index) = basisRow index := by
    intro index
    exact (Set.mem_range.mp (hbasisMem index)).choose_spec
  let probes : Finset Probe := Finset.univ.image chooseProbe
  have hcard : probes.card ≤ Fintype.card Move := by
    calc
      probes.card ≤ (Finset.univ : Finset
          (Fin (Module.finrank ℝ (Submodule.span ℝ rows)))).card := by
        dsimp only [probes]
        exact Finset.card_image_le
      _ = Module.finrank ℝ (Submodule.span ℝ rows) := by simp
      _ ≤ Module.finrank ℝ (Move → ℝ) :=
        Submodule.finrank_le (Submodule.span ℝ rows)
      _ = Fintype.card Move := Module.finrank_fintype_fun_eq_card ℝ
  refine ⟨probes, hcard, ?_⟩
  have hrowSet :
      chargedProbeRow column '' (probes : Set Probe) =
        Set.range basisRow := by
    ext row
    constructor
    · rintro ⟨probe, hprobe, rfl⟩
      have hprobe' : probe ∈ Finset.univ.image chooseProbe := hprobe
      obtain ⟨index, _hindex, rfl⟩ := Finset.mem_image.mp hprobe'
      exact ⟨index, (hchooseProbe index).symm⟩
    · rintro ⟨index, rfl⟩
      refine ⟨chooseProbe index, ?_, hchooseProbe index⟩
      dsimp only [probes]
      exact Finset.mem_image.mpr ⟨index, Finset.mem_univ index, rfl⟩
  rw [hrowSet, hbasisSpan]

/-- Balancing a spanning finite probe packet is equivalent to balancing all
probes. -/
theorem exists_finset_forall_probe_balance_iff
    (column : Move → Probe → ℝ) :
    ∃ probes : Finset Probe,
      probes.card ≤ Fintype.card Move ∧
        ∀ mass : Move → ℝ,
          (∀ probe ∈ probes,
              ∑ move, mass move * column move probe = 0) ↔
            ∀ probe, ∑ move, mass move * column move probe = 0 := by
  classical
  obtain ⟨probes, hcard, hspan⟩ :=
    exists_finset_chargedProbeRow_span_eq column
  refine ⟨probes, hcard, fun mass ↦ ?_⟩
  constructor
  · intro hfinite probe
    have hrowsKernel : chargedProbeRow column '' (probes : Set Probe) ⊆
        LinearMap.ker (chargedProbePair mass) := by
      rintro row ⟨selected, hselected, rfl⟩
      exact hfinite selected hselected
    have hspanKernel : Submodule.span ℝ
          (chargedProbeRow column '' (probes : Set Probe)) ≤
        LinearMap.ker (chargedProbePair mass) :=
      Submodule.span_le.mpr hrowsKernel
    have hprobeSpan : chargedProbeRow column probe ∈
        Submodule.span ℝ
          (chargedProbeRow column '' (probes : Set Probe)) := by
      rw [hspan]
      exact Submodule.subset_span (Set.mem_range_self probe)
    exact hspanKernel hprobeSpan
  · intro hall probe hprobe
    exact hall probe

/-! ## Exact finite-probe reduction -/

/-- **Finite-probe circulation theorem.** One finite probe packet
detects the existence of a normalized positive charged circulation of the
entire (possibly infinite) observable family. -/
theorem exists_finset_hasNormalizedPositiveChargedCirculation_iff
    (column : Move → Probe → ℝ) (charge : Move → ℝ) :
    ∃ probes : Finset Probe,
      probes.card ≤ Fintype.card Move ∧
        (HasNormalizedPositiveChargedCirculation column charge ↔
          HasNormalizedPositiveChargedCirculation
            (fun move (probe : {probe // probe ∈ probes}) ↦
              column move probe.1)
            charge) := by
  classical
  obtain ⟨probes, hcard, hbalance⟩ :=
    exists_finset_forall_probe_balance_iff column
  refine ⟨probes, hcard, ?_⟩
  constructor
  · rintro ⟨mass, hmass, hall, hcharge⟩
    exact ⟨mass, hmass, fun probe ↦ hall probe.1, hcharge⟩
  · rintro ⟨mass, hmass, hfinite, hcharge⟩
    refine ⟨mass, hmass, ?_, hcharge⟩
    apply (hbalance mass).mp
    intro probe hprobe
    exact hfinite ⟨probe, hprobe⟩

/-! ## Finite-probe Farkas certificate -/

/-- **Finite-probe charged alternative.** For finitely many moves and an
arbitrary family of scalar probes, one can select at most `card Move`
probes so that exactly one of the following holds:

* a normalized positive charged mass balances every probe;
* a linear combination of the selected probes has drift at least the charge
  on every move.

When probe columns are differences of bounded state observables, the
second branch is a bounded telescoping potential. -/
theorem exists_finset_normalizedPositiveChargedCirculation_xor_probePotential
    (column : Move → Probe → ℝ) (charge : Move → ℝ) :
    ∃ probes : Finset Probe,
      probes.card ≤ Fintype.card Move ∧
        Xor
          (HasNormalizedPositiveChargedCirculation column charge)
          (∃ potential : {probe // probe ∈ probes} → ℝ,
            IsChargedOccupationPotential
              (fun move (probe : {probe // probe ∈ probes}) ↦
                column move probe.1)
              charge potential) := by
  classical
  obtain ⟨probes, hcard, hbalance⟩ :=
    exists_finset_forall_probe_balance_iff column
  let restrictedColumn : Move → {probe // probe ∈ probes} → ℝ :=
    fun move probe ↦ column move probe.1
  have hcirculationIff :
      HasNormalizedPositiveChargedCirculation column charge ↔
        HasNormalizedPositiveChargedCirculation restrictedColumn charge := by
    constructor
    · rintro ⟨mass, hmass, hall, hcharge⟩
      exact ⟨mass, hmass, fun probe ↦ hall probe.1, hcharge⟩
    · rintro ⟨mass, hmass, hfinite, hcharge⟩
      refine ⟨mass, hmass, ?_, hcharge⟩
      apply (hbalance mass).mp
      intro probe hprobe
      exact hfinite ⟨probe, hprobe⟩
  have halt := normalizedPositiveChargedCirculation_xor_potential
    restrictedColumn charge
  refine ⟨probes, hcard, ?_⟩
  rw [xor_def] at halt ⊢
  rcases halt with ⟨hcirculation, hnotPotential⟩ |
      ⟨hpotential, hnotCirculation⟩
  · exact Or.inl ⟨hcirculationIff.mpr hcirculation, hnotPotential⟩
  · exact Or.inr ⟨hpotential, fun hcirculation ↦
      hnotCirculation (hcirculationIff.mp hcirculation)⟩

/-! ## What the finite potential buys on an actual path -/

omit [Fintype Move] in
/-- If the selected probe columns are consecutive differences, the finite
probe potential pays cumulative charge by a literal endpoint
telescope. -/
theorem sum_charge_le_probePotential_endpoint
    (probes : Finset Probe)
    (column : Move → Probe → ℝ) (charge : Move → ℝ)
    (potential : {probe // probe ∈ probes} → ℝ)
    (hpotential : IsChargedOccupationPotential
      (fun move (probe : {probe // probe ∈ probes}) ↦
        column move probe.1)
      charge potential)
    (move : ℕ → Move) (value : ℕ → Probe → ℝ) (steps : ℕ)
    (hcolumn : ∀ time < steps, ∀ probe ∈ probes,
      column (move time) probe =
        value (time + 1) probe - value time probe) :
    ∑ time ∈ Finset.range steps, charge (move time) ≤
      ∑ probe : {probe // probe ∈ probes},
        potential probe *
          (value steps probe.1 - value 0 probe.1) := by
  classical
  calc
    ∑ time ∈ Finset.range steps, charge (move time) ≤
        ∑ time ∈ Finset.range steps,
          ∑ probe : {probe // probe ∈ probes},
            potential probe * column (move time) probe.1 := by
      apply Finset.sum_le_sum
      intro time htime
      exact hpotential (move time)
    _ = ∑ time ∈ Finset.range steps,
          ∑ probe : {probe // probe ∈ probes},
            potential probe *
              (value (time + 1) probe.1 - value time probe.1) := by
      apply Finset.sum_congr rfl
      intro time htime
      apply Finset.sum_congr rfl
      intro probe _
      rw [hcolumn time (Finset.mem_range.mp htime) probe.1 probe.2]
    _ = ∑ probe : {probe // probe ∈ probes},
          ∑ time ∈ Finset.range steps,
            potential probe *
              (value (time + 1) probe.1 - value time probe.1) := by
      rw [Finset.sum_comm]
    _ = ∑ probe : {probe // probe ∈ probes},
        potential probe *
          (value steps probe.1 - value 0 probe.1) := by
      apply Finset.sum_congr rfl
      intro probe _
      rw [← Finset.mul_sum]
      exact congrArg (fun scalar : ℝ ↦ potential probe * scalar)
        (Finset.sum_range_sub (fun time ↦ value time probe.1) steps)

omit [Fintype Move] in
/-- Bounded probes impose an explicit finite budget on cumulative
charge along any path realizing their columns.  In particular, uniformly
positive charge cannot persist for arbitrarily many steps without leaving
the bounded semantic region. -/
theorem steps_mul_chargeFloor_le_probePotential_budget
    (probes : Finset Probe)
    (column : Move → Probe → ℝ) (charge : Move → ℝ)
    (potential : {probe // probe ∈ probes} → ℝ)
    (hpotential : IsChargedOccupationPotential
      (fun move (probe : {probe // probe ∈ probes}) ↦
        column move probe.1)
      charge potential)
    (move : ℕ → Move) (value : ℕ → Probe → ℝ) (steps : ℕ)
    (hcolumn : ∀ time < steps, ∀ probe ∈ probes,
      column (move time) probe =
        value (time + 1) probe - value time probe)
    (bound : Probe → ℝ)
    (hboundStart : ∀ probe, |value 0 probe| ≤ bound probe)
    (hboundEnd : ∀ probe, |value steps probe| ≤ bound probe)
    (chargeFloor : ℝ) (hchargeFloor : ∀ time < steps,
      chargeFloor ≤ charge (move time)) :
    (steps : ℝ) * chargeFloor ≤
      ∑ probe : {probe // probe ∈ probes},
        2 * |potential probe| * bound probe.1 := by
  classical
  have hlower : (steps : ℝ) * chargeFloor ≤
      ∑ time ∈ Finset.range steps, charge (move time) := by
    calc
      (steps : ℝ) * chargeFloor =
          ∑ time ∈ Finset.range steps, chargeFloor := by simp
      _ ≤ ∑ time ∈ Finset.range steps, charge (move time) := by
        apply Finset.sum_le_sum
        intro time htime
        exact hchargeFloor time (Finset.mem_range.mp htime)
  have htelescope := sum_charge_le_probePotential_endpoint
    probes column charge potential hpotential move value steps hcolumn
  have hterm : ∀ probe : {probe // probe ∈ probes},
      potential probe * (value steps probe.1 - value 0 probe.1) ≤
        2 * |potential probe| * bound probe.1 := by
    intro probe
    have hdiff : |value steps probe.1 - value 0 probe.1| ≤
        2 * bound probe.1 := by
      calc
        |value steps probe.1 - value 0 probe.1| ≤
            |value steps probe.1| + |value 0 probe.1| := abs_sub _ _
        _ ≤ bound probe.1 + bound probe.1 :=
          add_le_add (hboundEnd probe.1) (hboundStart probe.1)
        _ = 2 * bound probe.1 := by ring
    calc
      potential probe * (value steps probe.1 - value 0 probe.1) ≤
          |potential probe *
            (value steps probe.1 - value 0 probe.1)| := le_abs_self _
      _ = |potential probe| *
          |value steps probe.1 - value 0 probe.1| := abs_mul _ _
      _ ≤ |potential probe| * (2 * bound probe.1) :=
        mul_le_mul_of_nonneg_left hdiff (abs_nonneg _)
      _ = 2 * |potential probe| * bound probe.1 := by ring
  exact hlower.trans (htelescope.trans (Finset.sum_le_sum fun probe _ ↦ hterm probe))

/-! ## Common-source stars are not semantic circulations -/

/-- At a common source, balance of the source coordinate forces every move
carrying positive occupation mass to return to the source with probability
one. This is the sharp form of the common-source obstruction: common-source
columns can close at their base only on literal self-loops. -/
theorem commonSource_baseBalance_positiveMass_forces_baseReturn_one
    {State : Type*} [DecidableEq State]
    (kernel : Move → PMF State) (base : State) (mass : Move → ℝ)
    (hmass : ∀ move, 0 ≤ mass move)
    (hbaseBalance :
      ∑ move, mass move *
        actualOccupationColumn kernel (fun _move ↦ base) move base = 0)
    {move : Move} (hmove : 0 < mass move) :
    (kernel move base).toReal = 1 := by
  have hprob : ∀ other : Move, (kernel other base).toReal ≤ 1 := by
    intro other
    have h := ENNReal.toReal_mono ENNReal.one_ne_top
      ((kernel other).coe_le_one base)
    simpa using h
  have htermNonpos : ∀ other ∈ (Finset.univ : Finset Move),
      mass other * ((kernel other base).toReal - 1) ≤ 0 := by
    intro other _
    exact mul_nonpos_of_nonneg_of_nonpos (hmass other)
      (sub_nonpos.mpr (hprob other))
  have hbase :
      (∑ other, mass other * ((kernel other base).toReal - 1)) = 0 := by
    simpa [actualOccupationColumn] using hbaseBalance
  have htermZero :=
    (Finset.sum_eq_zero_iff_of_nonpos htermNonpos).mp hbase
  have hproduct := htermZero move (Finset.mem_univ move)
  exact sub_eq_zero.mp ((mul_eq_zero.mp hproduct).resolve_left hmove.ne')

/-- Consequently every nonnegative common-source mass with positive total
charge and balance at the base contains a positively charged literal
source-return move. A balanced collection of strict outgoing rays is
impossible; the only common-base charged branch is already a charged semantic
self-loop. -/
theorem exists_positiveCharge_baseReturn_one_of_commonSource
    {State : Type*} [DecidableEq State]
    (kernel : Move → PMF State) (base : State)
    (mass charge : Move → ℝ)
    (hmass : ∀ move, 0 ≤ mass move)
    (hbaseBalance : ∑ move, mass move *
      actualOccupationColumn kernel (fun _move ↦ base) move base = 0)
    (hcharge : 0 < ∑ move, mass move * charge move) :
    ∃ move, 0 < charge move ∧ (kernel move base).toReal = 1 := by
  have hexists : ∃ move ∈ (Finset.univ : Finset Move),
      0 < mass move * charge move := by
    by_contra hnone
    have hnonpos : ∀ move ∈ (Finset.univ : Finset Move),
        mass move * charge move ≤ 0 := by
      intro move hmove
      exact le_of_not_gt (fun hpos ↦ hnone ⟨move, hmove, hpos⟩)
    exact (not_lt_of_ge (Finset.sum_nonpos hnonpos)) hcharge
  rcases hexists with ⟨move, _hmoveMem, hproduct⟩
  have hmassPos : 0 < mass move := by
    rcases (mul_pos_iff.mp hproduct) with hboth | hboth
    · exact hboth.1
    · exact False.elim (not_lt_of_ge (hmass move) hboth.1)
  have hchargePos : 0 < charge move :=
    (mul_pos_iff.mp hproduct).resolve_right (fun hboth ↦
      not_lt_of_ge (hmass move) hboth.1)
      |>.2
  exact ⟨move, hchargePos,
    commonSource_baseBalance_positiveMass_forces_baseReturn_one
      kernel base mass hmass hbaseBalance hmassPos⟩

/-- A finite family of genuine transition kernels all based at one common
state cannot carry a positive charged occupation circulation if no positively
charged kernel returns there with probability one. Balance at the common
source forces any positive-charge support to contain a literal self-loop.

This is the exact obstruction to reading common-base difference columns as an
occupation cycle. A chattering construction must recompute transitions at
moving sources or contain a charged literal self-loop. -/
theorem not_normalizedPositiveChargedCirculation_actualOccupationColumn_commonSource
    {State : Type*} [DecidableEq State]
    (kernel : Move → PMF State) (base : State) (charge : Move → ℝ)
    (hnoReturn : ∀ move, 0 < charge move →
      (kernel move base).toReal ≠ 1) :
    ¬HasNormalizedPositiveChargedCirculation
      (actualOccupationColumn kernel (fun _move ↦ base)) charge := by
  rintro ⟨mass, hmass, hbalance, hcharge⟩
  obtain ⟨move, hchargeMove, hreturn⟩ :=
    exists_positiveCharge_baseReturn_one_of_commonSource
      kernel base mass charge hmass (hbalance base) (by simp [hcharge])
  exact hnoReturn move hchargeMove hreturn

end Probability
end Math
