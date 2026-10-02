/-
Postmark sequence-level packaging, section 4.

The per-profile dichotomy of `FablePostmarkAtomBlock` and the per-rank two-cut
coercivity outputs of `FablePostmarkTwoCutInstantiation` are packaged here at
the level of a whole sequence of behavior profiles.  Passing to one strict
subsequence fixes a single source arm -- immediate atom or postmark block --
and, on top of that, a single output arm: off the supplied minimum, or paid.
In the two paid arms a finite pigeonhole fixes one payer for every index of
the subsequence.

Nothing new is derived about the game here.  The eventual law floor and the
positive carrier minimum are supplied, and every emitted bound is literally
the constant that the per-rank coercivity theorems already produce.  The
later off-minimum arm keeps its exit cut existential, since that cut may vary
along the subsequence; only the source arm, the output arm, and the payer are
made uniform.
-/
import FablePostmarkAtomBlock
import FablePostmarkTwoCutInstantiation

noncomputable section

namespace GameTheory

open Filter

/-! ## J1: subsequence splitting utilities -/

/-- Frequently/eventually split of a per-index dichotomy: one strictly
monotone extraction carries a single side of the dichotomy at every step. -/
theorem fable_exists_strictMono_forall_or_forall {P Q : ℕ → Prop}
    (hdichotomy : ∀ index, P index ∨ Q index) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ((∀ step, P (φ step)) ∨ (∀ step, Q (φ step))) := by
  classical
  by_cases hfrequent : ∃ᶠ index in Filter.atTop, P index
  · obtain ⟨φ, hmono, hφ⟩ := extraction_of_frequently_atTop hfrequent
    exact ⟨φ, hmono, Or.inl hφ⟩
  · rw [Filter.not_frequently] at hfrequent
    obtain ⟨start, hstart⟩ := Filter.eventually_atTop.mp hfrequent
    refine ⟨fun step => start + step,
      fun a b hab => Nat.add_lt_add_left hab start, Or.inr fun step => ?_⟩
    exact (hdichotomy (start + step)).resolve_left
      (hstart (start + step) (Nat.le_add_right start step))

/-- Finite pigeonhole on the index line: a sequence into a finite type takes
some one value frequently. -/
theorem fable_exists_frequently_eq {α : Type*} [Finite α] (f : ℕ → α) :
    ∃ value : α, ∃ᶠ index in Filter.atTop, f index = value := by
  by_contra hcontra
  have hall : ∀ᶠ index in Filter.atTop, ∀ value : α, f index ≠ value := by
    refine Filter.eventually_all.mpr fun value => ?_
    rw [← Filter.not_frequently]
    exact fun hfrequent => hcontra ⟨value, hfrequent⟩
  obtain ⟨index, hindex⟩ := hall.exists
  exact hindex (f index) rfl

/-- Payer pigeonhole: a sequence into a finite type is constant along one
strictly monotone extraction. -/
theorem fable_exists_strictMono_comp_eq_const {α : Type*} [Finite α]
    (f : ℕ → α) :
    ∃ (value : α) (φ : ℕ → ℕ), StrictMono φ ∧ ∀ step, f (φ step) = value := by
  obtain ⟨value, hfrequent⟩ := fable_exists_frequently_eq f
  obtain ⟨φ, hmono, hφ⟩ := extraction_of_frequently_atTop hfrequent
  exact ⟨value, φ, hmono, hφ⟩

/-- Stacked split for a dichotomy whose second side is an existential over a
finite type: one strictly monotone extraction carries either the first side at
every step, or the second side at every step for one fixed witness. -/
theorem fable_exists_strictMono_forall_or_exists_const {α : Type*} [Finite α]
    {Off : ℕ → Prop} {Paid : ℕ → α → Prop}
    (hdichotomy : ∀ index, Off index ∨ ∃ value : α, Paid index value) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ((∀ step, Off (φ step)) ∨ ∃ value : α, ∀ step, Paid (φ step) value) := by
  classical
  obtain ⟨φ, hmono, harm⟩ := fable_exists_strictMono_forall_or_forall hdichotomy
  rcases harm with hoff | hpaid
  · exact ⟨φ, hmono, Or.inl hoff⟩
  · choose selector hselector using hpaid
    obtain ⟨value, ψ, hmonoψ, hψ⟩ :=
      fable_exists_strictMono_comp_eq_const selector
    refine ⟨fun step => φ (ψ step), hmono.comp hmonoψ,
      Or.inr ⟨value, fun step => ?_⟩⟩
    have hstep := hselector (ψ step)
    rwa [hψ step] at hstep

/-! ## J2: the four packaged outputs -/

/-- Immediate-arm off-minimum output at one profile: the date-one canonical
suffix total debt exceeds the supplied minimum by the production margin at
hazard floor `mu / 8`. -/
def FablePostmarkImmediateOffMinimum {ι : Type} [Fintype ι] [DecidableEq ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (μ : ℝ)
    (minimum : QuittingTerminalSemanticPair ι) : Prop :=
  quittingTerminalSemanticDebtSum
      (quittingRootSequenceTerminalSemanticPairAt reward
        (quittingProfileLiveRoot reward profile) 1) ≥
    quittingTerminalSemanticDebtSum minimum +
      (Real.exp (μ / 8) - 1) / 2 * quittingTerminalSemanticDebtSum minimum

/-- Immediate-arm paid output at one profile and one payer: that payer's debt
at the source's own terminal semantic pair exceeds the production coercive
threshold at hazard floor `mu / 8`. -/
def FablePostmarkImmediatePaid {ι : Type} [Fintype ι] [DecidableEq ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (μ : ℝ)
    (minimum : QuittingTerminalSemanticPair ι) (payer : ι) : Prop :=
  quittingTerminalSemanticDebt (quittingTerminalSemanticPair reward profile)
      payer >
    (1 - Real.exp (-(μ / 8))) * quittingTerminalSemanticDebtSum minimum /
      (2 * Fintype.card ι)

/-- Later-arm off-minimum output at one profile: some exit cut strictly after
date one whose canonical exit-suffix total debt exceeds the supplied minimum
by the production margin at hazard floor `mu / 2`.  The cut is existential
because it may vary along the subsequence. -/
def FablePostmarkLaterOffMinimum {ι : Type} [Fintype ι] [DecidableEq ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (μ : ℝ)
    (minimum : QuittingTerminalSemanticPair ι) : Prop :=
  ∃ exitCut : ℕ, 1 < exitCut ∧
    quittingTerminalSemanticDebtSum
        (quittingRootSequenceTerminalSemanticPairAt reward
          (quittingProfileLiveRoot reward profile) exitCut) ≥
      quittingTerminalSemanticDebtSum minimum +
        (Real.exp (μ / 2) - 1) / 2 * quittingTerminalSemanticDebtSum minimum

/-- Later-arm paid output at one profile and one payer: that payer's debt at
the canonical entry (date-one) suffix pair exceeds the production coercive
threshold at hazard floor `mu / 2`. -/
def FablePostmarkLaterPaid {ι : Type} [Fintype ι] [DecidableEq ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (μ : ℝ)
    (minimum : QuittingTerminalSemanticPair ι) (payer : ι) : Prop :=
  quittingTerminalSemanticDebt
      (quittingRootSequenceTerminalSemanticPairAt reward
        (quittingProfileLiveRoot reward profile) 1) payer >
    (1 - Real.exp (-(μ / 2))) * quittingTerminalSemanticDebtSum minimum /
      (2 * Fintype.card ι)

/-! ## J2: the per-arm packagings -/

/-- Immediate-arm packaging.  Given the immediate atom at every index, one
strictly monotone extraction carries either the off-minimum output at every
step, or the paid output at every step for one fixed payer. -/
theorem fablePostmark_exists_strictMono_immediateArm_packaging
    {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profiles : ℕ → (quittingGame reward).BehaviorProfile)
    (terminal : {S : Finset ι // S.Nonempty}) {μ : ℝ} (hμ : 0 < μ)
    (hatom : ∀ index,
      μ / 8 ≤ quittingStageCoalitionMass reward (profiles index) 0 terminal)
    (minimum : QuittingTerminalSemanticPair ι)
    (hminimumMem : minimum ∈ quittingTerminalSemanticCarrier reward)
    (hminimumLe : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hminimumPos : 0 < quittingTerminalSemanticDebtSum minimum) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ((∀ step,
          FablePostmarkImmediateOffMinimum reward (profiles (φ step)) μ
            minimum) ∨
        ∃ payer : ι, ∀ step,
          FablePostmarkImmediatePaid reward (profiles (φ step)) μ minimum
            payer) := by
  refine fable_exists_strictMono_forall_or_exists_const
    (Off := fun index =>
      FablePostmarkImmediateOffMinimum reward (profiles index) μ minimum)
    (Paid := fun index payer =>
      FablePostmarkImmediatePaid reward (profiles index) μ minimum payer)
    fun index => ?_
  exact fablePostmarkImmediateArm_offMinimum_or_exists_entryDebt_gt reward
    (profiles index) terminal hμ (hatom index) minimum hminimumMem hminimumLe
    hminimumPos

/-- Later-arm packaging.  Given the postmark block data at every index, one
strictly monotone extraction carries either the off-minimum output at every
step, or the paid output at every step for one fixed payer. -/
theorem fablePostmark_exists_strictMono_laterArm_packaging
    {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profiles : ℕ → (quittingGame reward).BehaviorProfile)
    (terminal : {S : Finset ι // S.Nonempty}) {μ : ℝ} (hμ : 0 < μ)
    (hblock : ∀ index,
      FablePostmarkBlockData reward (profiles index) terminal μ)
    (minimum : QuittingTerminalSemanticPair ι)
    (hminimumMem : minimum ∈ quittingTerminalSemanticCarrier reward)
    (hminimumLe : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hminimumPos : 0 < quittingTerminalSemanticDebtSum minimum) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ((∀ step,
          FablePostmarkLaterOffMinimum reward (profiles (φ step)) μ minimum) ∨
        ∃ payer : ι, ∀ step,
          FablePostmarkLaterPaid reward (profiles (φ step)) μ minimum
            payer) := by
  refine fable_exists_strictMono_forall_or_exists_const
    (Off := fun index =>
      FablePostmarkLaterOffMinimum reward (profiles index) μ minimum)
    (Paid := fun index payer =>
      FablePostmarkLaterPaid reward (profiles index) μ minimum payer)
    fun index => ?_
  obtain ⟨exitCut, hcut, -, hreach, hhazard⟩ := hblock index
  rcases fablePostmarkLaterArm_offMinimum_or_exists_entryDebt_gt reward
      (profiles index) hμ exitCut hcut hreach hhazard minimum hminimumMem
      hminimumLe hminimumPos with hoff | ⟨payer, hpayer⟩
  · exact Or.inl ⟨exitCut, hcut, hoff⟩
  · exact Or.inr ⟨payer, hpayer⟩

/-! ## J2: the four-way packaging -/

/-- Sequence-level postmark packaging.  From the eventual law floor for one
fixed nonempty coalition and a supplied positive carrier minimum, one strictly
monotone extraction realizes exactly one of four uniform outputs: the source
arm (immediate atom or postmark block) and the output arm (off the minimum or
paid) are both constant along the extraction, and in the two paid arms a
single payer serves every step. -/
theorem fablePostmark_exists_strictMono_twoCut_packaging
    {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profiles : ℕ → (quittingGame reward).BehaviorProfile)
    (terminal : {S : Finset ι // S.Nonempty}) {μ : ℝ} (hμ : 0 < μ)
    (hlaw : ∀ᶠ index in Filter.atTop,
      3 * μ / 4 < quittingAbsorbedMassLimit reward (profiles index) terminal)
    (minimum : QuittingTerminalSemanticPair ι)
    (hminimumMem : minimum ∈ quittingTerminalSemanticCarrier reward)
    (hminimumLe : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hminimumPos : 0 < quittingTerminalSemanticDebtSum minimum) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ((∀ step,
          FablePostmarkImmediateOffMinimum reward (profiles (φ step)) μ
            minimum) ∨
        (∃ payer : ι, ∀ step,
          FablePostmarkImmediatePaid reward (profiles (φ step)) μ minimum
            payer) ∨
        (∀ step,
          FablePostmarkLaterOffMinimum reward (profiles (φ step)) μ minimum) ∨
        ∃ payer : ι, ∀ step,
          FablePostmarkLaterPaid reward (profiles (φ step)) μ minimum
            payer) := by
  obtain ⟨φ, hmono, harm⟩ :=
    fablePostmark_exists_strictMono_immediate_atom_or_blockData reward profiles
      terminal hμ hlaw
  rcases harm with hatom | hblock
  · obtain ⟨ψ, hmonoψ, houtput⟩ :=
      fablePostmark_exists_strictMono_immediateArm_packaging reward
        (fun step => profiles (φ step)) terminal hμ hatom minimum hminimumMem
        hminimumLe hminimumPos
    rcases houtput with hoff | ⟨payer, hpaid⟩
    · exact ⟨fun step => φ (ψ step), hmono.comp hmonoψ, Or.inl hoff⟩
    · exact ⟨fun step => φ (ψ step), hmono.comp hmonoψ,
        Or.inr (Or.inl ⟨payer, hpaid⟩)⟩
  · obtain ⟨ψ, hmonoψ, houtput⟩ :=
      fablePostmark_exists_strictMono_laterArm_packaging reward
        (fun step => profiles (φ step)) terminal hμ hblock minimum hminimumMem
        hminimumLe hminimumPos
    rcases houtput with hoff | ⟨payer, hpaid⟩
    · exact ⟨fun step => φ (ψ step), hmono.comp hmonoψ,
        Or.inr (Or.inr (Or.inl hoff))⟩
    · exact ⟨fun step => φ (ψ step), hmono.comp hmonoψ,
        Or.inr (Or.inr (Or.inr ⟨payer, hpaid⟩))⟩

/-! ## J3: the Fin 4 later-arm paid splice with a fixed payer -/

/-- The Fin 4 later-arm paid splice output at one profile and one payer, at
the note's cap tolerance `K / 16` with `K = (1 - exp (-mu / 2)) * D`: a
behavioral replacement whose splice is one literal unilateral update of the
canonical parent, leaves every live root strictly before the entry cut
unchanged, has entry-suffix conditional gain above `K / 16` and updated
entry-suffix payer debt at most `K / 16`, and whose whole-profile gain --
exactly the parent-level payer debt decrease -- exceeds `mu / 2 * K / 16`. -/
def FablePostmarkLaterFinFourPaid
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (profile : (quittingGame reward).BehaviorProfile) (μ : ℝ)
    (minimum : QuittingTerminalSemanticPair (Fin 4)) (payer : Fin 4) : Prop :=
  ∃ deviation : (quittingGame reward).BehaviorStrategy payer,
    ∃ splice : (quittingGame reward).BehaviorProfile,
      splice = Function.update (quittingRootSequenceProfile reward
          (quittingProfileLiveRoot reward profile) 0) payer (splice payer) ∧
        (∀ time < 1, quittingProfileLiveRoot reward splice time =
          quittingProfileLiveRoot reward profile time) ∧
        quittingTerminalPayoff reward
              (Function.update (quittingRootSequenceProfile reward
                (quittingProfileLiveRoot reward profile) 1) payer
                deviation) payer -
            quittingTerminalPayoff reward
              (quittingRootSequenceProfile reward
                (quittingProfileLiveRoot reward profile) 1) payer >
          (1 - Real.exp (-(μ / 2))) *
            quittingTerminalSemanticDebtSum minimum / 16 ∧
        quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward
              (Function.update (quittingRootSequenceProfile reward
                (quittingProfileLiveRoot reward profile) 1) payer
                deviation)) payer ≤
          (1 - Real.exp (-(μ / 2))) *
            quittingTerminalSemanticDebtSum minimum / 16 ∧
        quittingTerminalPayoff reward splice payer -
            quittingTerminalPayoff reward
              (quittingRootSequenceProfile reward
                (quittingProfileLiveRoot reward profile) 0) payer >
          μ / 2 * ((1 - Real.exp (-(μ / 2))) *
            quittingTerminalSemanticDebtSum minimum) / 16 ∧
        quittingTerminalSemanticDebt
              (quittingTerminalSemanticPair reward
                (quittingRootSequenceProfile reward
                  (quittingProfileLiveRoot reward profile) 0)) payer -
            quittingTerminalSemanticDebt
              (quittingTerminalSemanticPair reward splice) payer =
          quittingTerminalPayoff reward splice payer -
            quittingTerminalPayoff reward
              (quittingRootSequenceProfile reward
                (quittingProfileLiveRoot reward profile) 0) payer

/-- Fin 4 later-arm splice packaging.  Given the postmark block data at every
index, one strictly monotone extraction carries either the later-arm
off-minimum output at every step, or -- for one fixed payer -- the note's
cap-tolerance `K / 16` paid splice at every step. -/
theorem fablePostmark_exists_strictMono_laterArm_finFour_packaging
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (profiles : ℕ → (quittingGame reward).BehaviorProfile)
    (terminal : {S : Finset (Fin 4) // S.Nonempty}) {μ : ℝ} (hμ : 0 < μ)
    (hblock : ∀ index,
      FablePostmarkBlockData reward (profiles index) terminal μ)
    (minimum : QuittingTerminalSemanticPair (Fin 4))
    (hminimumMem : minimum ∈ quittingTerminalSemanticCarrier reward)
    (hminimumLe : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hminimumPos : 0 < quittingTerminalSemanticDebtSum minimum) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ((∀ step,
          FablePostmarkLaterOffMinimum reward (profiles (φ step)) μ minimum) ∨
        ∃ payer : Fin 4, ∀ step,
          FablePostmarkLaterFinFourPaid reward (profiles (φ step)) μ minimum
            payer) := by
  refine fable_exists_strictMono_forall_or_exists_const
    (Off := fun index =>
      FablePostmarkLaterOffMinimum reward (profiles index) μ minimum)
    (Paid := fun index payer =>
      FablePostmarkLaterFinFourPaid reward (profiles index) μ minimum payer)
    fun index => ?_
  obtain ⟨exitCut, hcut, -, hreach, hhazard⟩ := hblock index
  rcases fablePostmarkLaterArm_finFour_offMinimum_or_exists_paidSplice
      (profiles index) hμ exitCut hcut hreach hhazard minimum hminimumMem
      hminimumLe hminimumPos with hoff | ⟨payer, hpaid⟩
  · exact Or.inl ⟨exitCut, hcut, hoff⟩
  · exact Or.inr ⟨payer, hpaid⟩

end GameTheory
