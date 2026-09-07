import GameTheory.Finite.Algorithm
import GameTheory.Analysis.Nash
import GameTheory.Finite.Correctness
import Mathlib.Algebra.Order.Floor.Ring
import MathUE.PMFProduct.BooleanCoordinateStability
import MathUE.Probability.FinitePMF
import MathUE.ProbabilityMassFunction.Simplex

/-! # Executable rational grid search for finite Boolean games -/

namespace GameTheory.Finite

variable {players : ℕ}

/-- A rational payoff table for a finite Boolean normal-form game. -/
abbrev RationalBooleanPayoff (players : ℕ) :=
  (Fin players → Bool) → Fin players → ℚ

/-- Independent weight of a Boolean action profile under Quit probabilities
`probability`. -/
def rationalBooleanProfileWeight
    (probability : Fin players → ℚ) (action : Fin players → Bool) : ℚ :=
  ∏ who, if action who then probability who else 1 - probability who

/-- Exact rational prescribed payoff of a Boolean product profile. -/
def rationalBooleanExpectedPayoff
    (payoff : RationalBooleanPayoff players) (probability : Fin players → ℚ)
    (who : Fin players) : ℚ :=
  ∑ action : Fin players → Bool,
    rationalBooleanProfileWeight probability action * payoff action who

/-- Compile the rational Boolean payoff table into the generic executable
finite-table frontend. -/
def rationalBooleanTableGame
    (payoff : RationalBooleanPayoff players) : TableGame (Fin players) where
  Action := fun _ => Bool
  actionFintype := fun _ => inferInstance
  actionDecEq := fun _ => inferInstance
  payoff := payoff

/-- The rational mixed profile represented by Quit probabilities. -/
def rationalBooleanMixedProfile
  (payoff : RationalBooleanPayoff players)
    (probability : Fin players → ℚ) :
    Profile (rationalBooleanTableGame payoff).mixedSig :=
  fun who action => if (show Bool from action) then probability who
    else 1 - probability who

/-- Exact rational payoff from forcing one pure action against the other
coordinates of a Boolean product profile. -/
def rationalBooleanPurePayoff
    (payoff : RationalBooleanPayoff players) (probability : Fin players → ℚ)
    (who : Fin players) (action : Bool) : ℚ :=
  rationalBooleanExpectedPayoff payoff
    (Function.update probability who (if action then 1 else 0)) who

/-- Ordinary one-coordinate regret: the larger of the two pure-action
payoffs minus the prescribed mixed payoff. -/
def rationalBooleanNashRegret
    (payoff : RationalBooleanPayoff players) (probability : Fin players → ℚ)
    (who : Fin players) : ℚ :=
  max (rationalBooleanPurePayoff payoff probability who false)
      (rationalBooleanPurePayoff payoff probability who true) -
    rationalBooleanExpectedPayoff payoff probability who

/-- Sum of positive one-coordinate regrets. This is the exact rational
counterpart of total root Nash defect and is the acceptance quantity used by
the auxiliary-row consumer. -/
def rationalBooleanTotalNashDefect
    (payoff : RationalBooleanPayoff players)
    (probability : Fin players → ℚ) : ℚ :=
  ∑ who, max (rationalBooleanNashRegret payoff probability who) 0

/-- A computable positive bound on every absolute pure payoff. -/
def rationalBooleanPayoffBound (payoff : RationalBooleanPayoff players) : ℚ :=
  1 + ∑ action : Fin players → Bool,
    ∑ who : Fin players, |payoff action who|

/-- Common grid resolution. The actual denominator is one larger, so it is
always positive even on arbitrary nonpositive accuracy inputs. -/
def rationalBooleanGridResolution
    (payoff : RationalBooleanPayoff players) (accuracy : ℚ) : ℕ :=
  Int.toNat <| Rat.ceil
    ((4 * rationalBooleanPayoffBound payoff * players ^ 2) / accuracy)

/-- Rational Quit probabilities represented by one common-denominator grid
point. -/
def rationalBooleanGridProbability (resolution : ℕ)
    (point : Fin players → Fin (resolution + 2)) : Fin players → ℚ :=
  fun who => (point who : ℚ) / (resolution + 1)

/-- Explicit recursive enumeration of every vector in the finite grid. This
list, unlike `Finset.toList`, is executable without choosing an order on an
abstract finite player type. -/
def rationalBooleanGridPoints :
    (players resolution : ℕ) → List (Fin players → Fin (resolution + 2))
  | 0, _ => [fun who => Fin.elim0 who]
  | players + 1, resolution =>
      (List.finRange (resolution + 2)).flatMap fun head =>
        (rationalBooleanGridPoints players resolution).map fun tail =>
          Fin.cons head tail

/-- Exact rational acceptance predicate for the common grid. -/
def rationalBooleanGridAccepts
    (payoff : RationalBooleanPayoff players) (accuracy : ℚ)
    (resolution : ℕ) (point : Fin players → Fin (resolution + 2)) : Bool :=
  decide (rationalBooleanTotalNashDefect payoff
    (rationalBooleanGridProbability resolution point) ≤ accuracy)

/-- Executable exhaustive search of the finite common-denominator grid. -/
def rationalBooleanRootGridSearch?
    (payoff : RationalBooleanPayoff players) (accuracy : ℚ) :
    Option (Fin players → Fin (rationalBooleanGridResolution payoff accuracy + 2)) :=
  let resolution := rationalBooleanGridResolution payoff accuracy
  (rationalBooleanGridPoints players resolution).find?
    (rationalBooleanGridAccepts payoff accuracy resolution)

/-- Total dependent selector obtained by running the executable search, once
its success theorem has supplied the erased proof that a result exists. -/
def rationalBooleanRootGridSelector
    (payoff : RationalBooleanPayoff players) (accuracy : ℚ)
    (hsuccess : (rationalBooleanRootGridSearch? payoff accuracy).isSome = true) :
    Fin players → ℚ :=
  rationalBooleanGridProbability (rationalBooleanGridResolution payoff accuracy)
    ((rationalBooleanRootGridSearch? payoff accuracy).get hsuccess)

theorem rationalBooleanPayoffBound_pos
    (payoff : RationalBooleanPayoff players) :
    0 < rationalBooleanPayoffBound payoff := by
  unfold rationalBooleanPayoffBound
  have hsum : 0 ≤ ∑ action : Fin players → Bool,
      ∑ who : Fin players, |payoff action who| :=
    Finset.sum_nonneg fun action _ =>
      Finset.sum_nonneg fun who _ => abs_nonneg _
  linarith

theorem abs_payoff_le_rationalBooleanPayoffBound
    (payoff : RationalBooleanPayoff players)
    (action : Fin players → Bool) (who : Fin players) :
    |payoff action who| ≤ rationalBooleanPayoffBound payoff := by
  unfold rationalBooleanPayoffBound
  have hinner : |payoff action who| ≤
      ∑ player : Fin players, |payoff action player| := by
    exact Finset.single_le_sum
      (f := fun player : Fin players => |payoff action player|)
      (fun player _ => abs_nonneg _) (Finset.mem_univ who)
  have houter : (∑ player : Fin players, |payoff action player|) ≤
      ∑ joint : Fin players → Bool,
        ∑ player : Fin players, |payoff joint player| := by
    exact Finset.single_le_sum
      (f := fun joint : Fin players → Bool =>
        ∑ player : Fin players, |payoff joint player|)
      (fun joint _ => Finset.sum_nonneg fun player _ => abs_nonneg _)
      (Finset.mem_univ action)
  exact hinner.trans (houter.trans (le_add_of_nonneg_left (by norm_num)))

theorem mem_rationalBooleanGridPoints
    (resolution : ℕ) (point : Fin players → Fin (resolution + 2)) :
    point ∈ rationalBooleanGridPoints players resolution := by
  induction players with
  | zero =>
      have hpoint : point = fun who => Fin.elim0 who := by
        funext who
        exact Fin.elim0 who
      simp [rationalBooleanGridPoints, hpoint]
  | succ players ih =>
      simp only [rationalBooleanGridPoints, List.mem_flatMap, List.mem_map,
        List.mem_finRange]
      refine ⟨point 0, trivial, Fin.tail point, ih (Fin.tail point), ?_⟩
      exact Fin.cons_self_tail point

theorem rationalBooleanGridProbability_mem_unitInterval
    (resolution : ℕ) (point : Fin players → Fin (resolution + 2))
    (who : Fin players) :
    0 ≤ rationalBooleanGridProbability resolution point who ∧
      rationalBooleanGridProbability resolution point who ≤ 1 := by
  unfold rationalBooleanGridProbability
  constructor
  · positivity
  · rw [div_le_iff₀ (by positivity : (0 : ℚ) < resolution + 1)]
    have hcast : ((point who : ℕ) : ℚ) ≤ ((resolution + 1 : ℕ) : ℚ) := by
      exact_mod_cast (Nat.le_of_lt_succ (point who).isLt)
    simpa using hcast

theorem rationalBooleanMixedProfile_isMixed
    (payoff : RationalBooleanPayoff players)
    (probability : Fin players → ℚ)
    (hunit : ∀ who, 0 ≤ probability who ∧ probability who ≤ 1) :
    (rationalBooleanTableGame payoff).isMixed
      (rationalBooleanMixedProfile payoff probability) = true := by
  rw [TableGame.isMixed_iff]
  intro who
  change (∀ action : Bool,
      0 ≤ if action then probability who else 1 - probability who) ∧
    (∑ action : Bool, if action then probability who else 1 - probability who) = 1
  constructor
  · intro action
    cases action <;> simp [hunit who]
  · simp

theorem rationalBooleanExpectedPayoff_eq_tableGame
    (payoff : RationalBooleanPayoff players)
    (probability : Fin players → ℚ) (who : Fin players) :
    rationalBooleanExpectedPayoff payoff probability who =
      (rationalBooleanTableGame payoff).expectedPayoff
        (rationalBooleanMixedProfile payoff probability) who := by
  unfold rationalBooleanExpectedPayoff TableGame.expectedPayoff
    TableGame.mixedWeight rationalBooleanProfileWeight
    rationalBooleanMixedProfile rationalBooleanTableGame
  rfl

theorem rationalBooleanPurePayoff_eq_tableGame
    (payoff : RationalBooleanPayoff players)
    (probability : Fin players → ℚ) (who : Fin players) (action : Bool) :
    rationalBooleanPurePayoff payoff probability who action =
      (rationalBooleanTableGame payoff).expectedPayoff
        (Profile.update (rationalBooleanMixedProfile payoff probability) who
          ((rationalBooleanTableGame payoff).pureMixed who action)) who := by
  rw [rationalBooleanPurePayoff, rationalBooleanExpectedPayoff_eq_tableGame]
  congr 1
  funext player choice
  by_cases hplayer : player = who
  · subst player
    simp only [Profile.update_same]
    unfold rationalBooleanMixedProfile TableGame.pureMixed
      rationalBooleanTableGame
    cases action <;> cases choice <;> simp
  · simp [rationalBooleanMixedProfile, hplayer]

section SemanticProof

open GameTheory.Math.Probability

theorem expectedUtility_rationalBooleanTableGame_eq_pmfPi
    (payoff : RationalBooleanPayoff players)
    (profile : Profile (rationalBooleanTableGame payoff).sig.mixed)
    (who : Fin players) :
    expectedUtility (rationalBooleanTableGame payoff).utility who
        ((rationalBooleanTableGame payoff).toForm.mixed.play profile) =
      _root_.Math.Probability.expect
        (_root_.Math.PMFProduct.pmfPi fun player => (profile player).toPMF)
        (fun action => (payoff action who : ℝ)) := by
  let game := rationalBooleanTableGame payoff
  have hplay : game.toForm.mixed.play profile = FinDist.pi profile := by
    rw [GameForm.mixed_play]
    exact FinDist.bind_pure _
  rw [hplay]
  unfold expectedUtility
  change FinDist.expect (FinDist.pi profile)
      (fun action => (payoff action who : ℝ)) = _
  rw [← _root_.Math.Probability.expect_finDistOfPMF]
  congr 1

/-- A uniform change `d` in Boolean marginal probabilities changes every
expected payoff by at most `2 R n d`. -/
theorem abs_expectedUtility_rationalBooleanTableGame_sub_le
    (payoff : RationalBooleanPayoff players)
    (first second : Profile (rationalBooleanTableGame payoff).sig.mixed)
    (who : Fin players) {d : ℝ}
    (hclose : ∀ player,
      |(first player).prob true - (second player).prob true| ≤ d) :
    |expectedUtility (rationalBooleanTableGame payoff).utility who
          ((rationalBooleanTableGame payoff).toForm.mixed.play first) -
        expectedUtility (rationalBooleanTableGame payoff).utility who
          ((rationalBooleanTableGame payoff).toForm.mixed.play second)| ≤
      2 * (rationalBooleanPayoffBound payoff : ℝ) * (players * d) := by
  rw [expectedUtility_rationalBooleanTableGame_eq_pmfPi,
    expectedUtility_rationalBooleanTableGame_eq_pmfPi]
  have htv := _root_.Math.PMFProduct.pmfTV_pmfPi_bool_le_card_mul_of_trueProbability_close
    (fun player => (first player).toPMF)
    (fun player => (second player).toPMF) hclose
  have hobservable : ∀ action : Fin players → Bool,
      |(payoff action who : ℝ)| ≤ (rationalBooleanPayoffBound payoff : ℝ) := by
    intro action
    exact_mod_cast abs_payoff_le_rationalBooleanPayoffBound payoff action who
  have hexpect := _root_.Math.Probability.abs_expect_sub_le_two_mul_pmfTV
    (_root_.Math.PMFProduct.pmfPi fun player => (first player).toPMF)
    (_root_.Math.PMFProduct.pmfPi fun player => (second player).toPMF)
    (fun action => (payoff action who : ℝ)) hobservable
  have hbound : 0 ≤ (rationalBooleanPayoffBound payoff : ℝ) := by
    exact_mod_cast (rationalBooleanPayoffBound_pos payoff).le
  refine hexpect.trans ?_
  calc
    2 * (rationalBooleanPayoffBound payoff : ℝ) *
          _root_.Math.Probability.pmfTV
            (_root_.Math.PMFProduct.pmfPi fun player => (first player).toPMF)
            (_root_.Math.PMFProduct.pmfPi fun player => (second player).toPMF) ≤
        2 * (rationalBooleanPayoffBound payoff : ℝ) *
          ((Fintype.card (Fin players) : ℝ) * d) :=
      mul_le_mul_of_nonneg_left htv (by positivity)
    _ = 2 * (rationalBooleanPayoffBound payoff : ℝ) * (players * d) := by simp

private noncomputable def roundedRationalBooleanGridPoint
    (payoff : RationalBooleanPayoff players)
    (profile : Profile (rationalBooleanTableGame payoff).sig.mixed)
    (resolution : ℕ) : Fin players → Fin (resolution + 2) :=
  fun who =>
    ⟨Nat.floor ((profile who).prob true * (resolution + 1 : ℝ)), by
      have hprobability := (profile who).prob_le_one true
      have hproduct : (profile who).prob true * (resolution + 1 : ℝ) ≤
          (resolution + 1 : ℕ) := by
        have hmul := mul_le_mul_of_nonneg_right hprobability
          (show (0 : ℝ) ≤ resolution + 1 by positivity)
        simpa using hmul
      have hfloor : Nat.floor
          ((profile who).prob true * (resolution + 1 : ℝ)) ≤ resolution + 1 :=
        Nat.floor_le_of_le hproduct
      omega⟩

private theorem abs_floor_div_sub_lt_one_div
    (probability : ℝ) (hprobability : 0 ≤ probability)
    (denominator : ℕ) (hdenominator : 0 < denominator) :
    |((Nat.floor (probability * denominator) : ℕ) : ℝ) / denominator -
        probability| < 1 / denominator := by
  have hdenominatorReal : (0 : ℝ) < denominator := by exact_mod_cast hdenominator
  have hlower := Nat.floor_le (mul_nonneg hprobability hdenominatorReal.le)
  have hupper := Nat.lt_floor_add_one (probability * denominator)
  have hquotientLe :
      ((Nat.floor (probability * denominator) : ℕ) : ℝ) / denominator ≤
        probability := by
    rw [div_le_iff₀ hdenominatorReal]
    simpa [mul_comm] using hlower
  rw [abs_of_nonpos (sub_nonpos.mpr hquotientLe)]
  rw [neg_sub, sub_lt_iff_lt_add]
  calc
    probability = probability * denominator / denominator := by
      field_simp
    _ < (((Nat.floor (probability * denominator) : ℕ) : ℝ) + 1) /
        denominator := (div_lt_div_iff_of_pos_right hdenominatorReal).2 hupper
    _ = ((Nat.floor (probability * denominator) : ℕ) : ℝ) /
          denominator + 1 / denominator := by ring
    _ = 1 / denominator +
          ((Nat.floor (probability * denominator) : ℕ) : ℝ) / denominator := by ring

private theorem roundedRationalBooleanGridPoint_close
    (payoff : RationalBooleanPayoff players)
    (profile : Profile (rationalBooleanTableGame payoff).sig.mixed)
    (resolution : ℕ) (who : Fin players) :
    |((rationalBooleanGridProbability resolution
          (roundedRationalBooleanGridPoint payoff profile resolution) who : ℚ) : ℝ) -
        (profile who).prob true| < 1 / (resolution + 1 : ℝ) := by
  unfold rationalBooleanGridProbability roundedRationalBooleanGridPoint
  simp only [Rat.cast_div, Rat.cast_natCast]
  convert abs_floor_div_sub_lt_one_div ((profile who).prob true)
    (FinDist.prob_nonneg (profile who) true)
    (resolution + 1) (by omega) using 1 <;> norm_num

private theorem rationalBooleanGrid_mesh_lt
    (payoff : RationalBooleanPayoff players) (accuracy : ℚ)
    (hplayers : 0 < players) (haccuracy : 0 < accuracy) :
    (1 : ℚ) / (rationalBooleanGridResolution payoff accuracy + 1) <
      accuracy /
        (4 * rationalBooleanPayoffBound payoff * players ^ 2) := by
  let scale : ℚ := 4 * rationalBooleanPayoffBound payoff * players ^ 2
  have hscale : 0 < scale := by
    dsimp only [scale]
    have hplayersRat : (0 : ℚ) < players := by exact_mod_cast hplayers
    have hbound := rationalBooleanPayoffBound_pos payoff
    exact mul_pos (mul_pos (by norm_num) hbound) (sq_pos_of_pos hplayersRat)
  let ratio : ℚ := scale / accuracy
  have hratio : 0 < ratio := div_pos hscale haccuracy
  have hceilRat : (0 : ℚ) ≤ (Rat.ceil ratio : ℤ) := by
    exact hratio.le.trans Rat.le_ceil
  have hceilInt : (0 : ℤ) ≤ Rat.ceil ratio := by
    exact_mod_cast hceilRat
  have hratio_lt : ratio < ((Int.toNat (Rat.ceil ratio) + 1 : ℕ) : ℚ) := by
    calc
      ratio ≤ (Rat.ceil ratio : ℤ) := Rat.le_ceil
      _ = ((Int.toNat (Rat.ceil ratio) : ℕ) : ℚ) := by
        exact_mod_cast (Int.toNat_of_nonneg hceilInt).symm
      _ < ((Int.toNat (Rat.ceil ratio) + 1 : ℕ) : ℚ) := by
        exact_mod_cast Nat.lt_succ_self (Int.toNat (Rat.ceil ratio))
  have hresolution : rationalBooleanGridResolution payoff accuracy =
      Int.toNat (Rat.ceil ratio) := by
    simp only [rationalBooleanGridResolution, ratio, scale]
  rw [hresolution]
  have hdenominator : (0 : ℚ) < Int.toNat (Rat.ceil ratio) + 1 := by positivity
  have hscaled : scale <
      accuracy * (Int.toNat (Rat.ceil ratio) + 1 : ℕ) := by
    simpa [mul_comm] using (div_lt_iff₀ haccuracy).mp hratio_lt
  rw [div_lt_div_iff₀ hdenominator hscale]
  simpa [scale] using hscaled

private theorem cast_rationalBooleanExpectedPayoff_eq
    (payoff : RationalBooleanPayoff players)
    (probability : Fin players → ℚ)
    (hunit : ∀ who, 0 ≤ probability who ∧ probability who ≤ 1)
    (who : Fin players) :
    (rationalBooleanExpectedPayoff payoff probability who : ℝ) =
      expectedUtility (rationalBooleanTableGame payoff).utility who
        ((rationalBooleanTableGame payoff).toForm.mixed.play
          ((rationalBooleanTableGame payoff).toMixed
            (rationalBooleanMixedProfile payoff probability)
            (rationalBooleanMixedProfile_isMixed payoff probability hunit))) := by
  rw [rationalBooleanExpectedPayoff_eq_tableGame]
  exact (TableGame.expectedUtility_toMixed
    (rationalBooleanTableGame payoff)
    (rationalBooleanMixedProfile payoff probability)
    (rationalBooleanMixedProfile_isMixed payoff probability hunit) who).symm

private theorem cast_rationalBooleanPurePayoff_eq
    (payoff : RationalBooleanPayoff players)
    (probability : Fin players → ℚ)
    (hunit : ∀ who, 0 ≤ probability who ∧ probability who ≤ 1)
    (who : Fin players) (action : Bool) :
    (rationalBooleanPurePayoff payoff probability who action : ℝ) =
      expectedUtility (rationalBooleanTableGame payoff).utility who
        ((rationalBooleanTableGame payoff).toForm.mixed.play
          (Profile.update
            ((rationalBooleanTableGame payoff).toMixed
              (rationalBooleanMixedProfile payoff probability)
              (rationalBooleanMixedProfile_isMixed payoff probability hunit))
            who (FinDist.pure action))) := by
  rw [rationalBooleanPurePayoff_eq_tableGame]
  let game := rationalBooleanTableGame payoff
  let mixed := rationalBooleanMixedProfile payoff probability
  let hmixed := rationalBooleanMixedProfile_isMixed payoff probability hunit
  have hupdated := game.isMixed_update_pureMixed mixed hmixed who action
  rw [← game.toMixed_update mixed hmixed who action]
  exact (game.expectedUtility_toMixed
    (Profile.update mixed who (game.pureMixed who action)) hupdated who).symm

end SemanticProof

open GameTheory.Math.Probability

/-- Positive rational accuracy guarantees that the executable finite search
returns a grid point. The proof layer rounds an exact mixed Nash profile; the
search itself performs only rational arithmetic and finite list traversal. -/
theorem rationalBooleanRootGridSearch_isSome_of_pos
    (payoff : RationalBooleanPayoff players) (accuracy : ℚ)
    (haccuracy : 0 < accuracy) :
    (rationalBooleanRootGridSearch? payoff accuracy).isSome = true := by
  classical
  by_cases hplayersZero : players = 0
  · subst players
    apply List.find?_isSome.mpr
    let point : Fin 0 → Fin (rationalBooleanGridResolution payoff accuracy + 2) :=
      fun who => Fin.elim0 who
    refine ⟨point, mem_rationalBooleanGridPoints _ point, ?_⟩
    simp [rationalBooleanGridAccepts, rationalBooleanTotalNashDefect, haccuracy.le]
  have hplayers : 0 < players := Nat.pos_of_ne_zero hplayersZero
  let game := rationalBooleanTableGame payoff
  letI (who : Fin players) : Nonempty (game.toForm.sig.Strategy who) :=
    ⟨(show Bool from false)⟩
  obtain ⟨exactProfile, hexactNash⟩ :=
    exists_isNash_mixed (F := game.toForm) game.utility
  let resolution := rationalBooleanGridResolution payoff accuracy
  let point := roundedRationalBooleanGridPoint payoff exactProfile resolution
  let probability := rationalBooleanGridProbability resolution point
  have hunit : ∀ who, 0 ≤ probability who ∧ probability who ≤ 1 := by
    intro who
    exact rationalBooleanGridProbability_mem_unitInterval resolution point who
  let mixed := rationalBooleanMixedProfile payoff probability
  have hmixed : game.isMixed mixed = true :=
    rationalBooleanMixedProfile_isMixed payoff probability hunit
  let candidate := game.toMixed mixed hmixed
  let mesh : ℝ := 1 / (resolution + 1 : ℝ)
  have hmeshNonnegative : 0 ≤ mesh := by
    dsimp only [mesh]
    positivity
  have hclose : ∀ who,
      |(candidate who).prob true - (exactProfile who).prob true| ≤ mesh := by
    intro who
    have hrounded := roundedRationalBooleanGridPoint_close
      payoff exactProfile resolution who
    have hcandidates : (candidate who).prob true = (probability who : ℝ) := by
      exact game.toMixed_prob mixed hmixed who true
    rw [hcandidates]
    exact hrounded.le
  have hbase := abs_expectedUtility_rationalBooleanTableGame_sub_le
    payoff candidate exactProfile
  have hforcedClose (who : Fin players) (action : Bool) :
      ∀ player,
        |((Profile.update candidate who (FinDist.pure action)) player).prob true -
            ((Profile.update exactProfile who (FinDist.pure action)) player).prob true| ≤
          mesh := by
    intro player
    by_cases hplayer : player = who
    · subst player
      simpa using hmeshNonnegative
    · rw [Profile.update_of_ne _ _ hplayer, Profile.update_of_ne _ _ hplayer]
      exact hclose player
  have hforced (who : Fin players) (action : Bool) :=
    abs_expectedUtility_rationalBooleanTableGame_sub_le payoff
      (Profile.update candidate who (FinDist.pure action))
      (Profile.update exactProfile who (FinDist.pure action)) who
      (hforcedClose who action)
  have hexactPure (who : Fin players) (action : Bool) :
      expectedUtility game.utility who
          (game.toForm.mixed.play
            (Profile.update exactProfile who (FinDist.pure action))) ≤
        expectedUtility game.utility who
          (game.toForm.mixed.play exactProfile) := by
    rw [isNash_iff] at hexactNash
    simpa only [euPreference_apply] using
      hexactNash who (FinDist.pure action)
  have hpureGain (who : Fin players) (action : Bool) :
      expectedUtility game.utility who
          (game.toForm.mixed.play
            (Profile.update candidate who (FinDist.pure action))) ≤
        expectedUtility game.utility who
            (game.toForm.mixed.play candidate) +
          4 * (rationalBooleanPayoffBound payoff : ℝ) * (players * mesh) := by
    have hforcedBounds := abs_le.mp (hforced who action)
    have hbaseBounds := abs_le.mp (hbase who hclose)
    have hexact := hexactPure who action
    linarith
  let rationalBound : ℚ :=
    4 * rationalBooleanPayoffBound payoff * players /
      (resolution + 1)
  have hpureRational (who : Fin players) (action : Bool) :
      rationalBooleanPurePayoff payoff probability who action ≤
        rationalBooleanExpectedPayoff payoff probability who + rationalBound := by
    have hpure := hpureGain who action
    have hpureCast := cast_rationalBooleanPurePayoff_eq
      payoff probability hunit who action
    have hexpectedCast := cast_rationalBooleanExpectedPayoff_eq
      payoff probability hunit who
    rw [← hpureCast, ← hexpectedCast] at hpure
    have hboundCast : (rationalBound : ℝ) =
        4 * (rationalBooleanPayoffBound payoff : ℝ) * (players * mesh) := by
      dsimp only [rationalBound, mesh]
      push_cast
      ring
    rw [← hboundCast] at hpure
    exact_mod_cast hpure
  have hregret (who : Fin players) :
      rationalBooleanNashRegret payoff probability who ≤ rationalBound := by
    rw [rationalBooleanNashRegret, sub_le_iff_le_add]
    exact max_le (by simpa [add_comm] using hpureRational who false)
      (by simpa [add_comm] using hpureRational who true)
  have hrationalBoundNonnegative : 0 ≤ rationalBound := by
    dsimp only [rationalBound]
    have hbound := (rationalBooleanPayoffBound_pos payoff).le
    positivity
  have htotalLe : rationalBooleanTotalNashDefect payoff probability ≤
      players * rationalBound := by
    unfold rationalBooleanTotalNashDefect
    calc
      (∑ who : Fin players,
          max (rationalBooleanNashRegret payoff probability who) 0) ≤
          ∑ _who : Fin players, rationalBound :=
        Finset.sum_le_sum fun who _ =>
          max_le (hregret who) hrationalBoundNonnegative
      _ = players * rationalBound := by simp
  have hmesh := rationalBooleanGrid_mesh_lt payoff accuracy hplayers haccuracy
  have hscale : 0 <
      (4 * rationalBooleanPayoffBound payoff * players ^ 2 : ℚ) := by
    have hplayersRat : (0 : ℚ) < players := by exact_mod_cast hplayers
    exact mul_pos (mul_pos (by norm_num) (rationalBooleanPayoffBound_pos payoff))
      (sq_pos_of_pos hplayersRat)
  have htotalBound : players * rationalBound < accuracy := by
    calc
      players * rationalBound =
          (4 * rationalBooleanPayoffBound payoff * players ^ 2) *
            (1 / (resolution + 1 : ℚ)) := by
        dsimp only [rationalBound]
        ring
      _ < (4 * rationalBooleanPayoffBound payoff * players ^ 2) *
          (accuracy /
            (4 * rationalBooleanPayoffBound payoff * players ^ 2)) := by
        apply mul_lt_mul_of_pos_left
        simpa only [resolution] using hmesh
        exact hscale
      _ = accuracy := by
        field_simp [ne_of_gt (rationalBooleanPayoffBound_pos payoff)]
  have haccepts : rationalBooleanGridAccepts payoff accuracy resolution point = true := by
    apply decide_eq_true
    exact htotalLe.trans htotalBound.le
  apply List.find?_isSome.mpr
  exact ⟨point, mem_rationalBooleanGridPoints resolution point, haccepts⟩

theorem rationalBooleanRootGridSelector_regret_le
    (payoff : RationalBooleanPayoff players) (accuracy : ℚ)
    (hsuccess : (rationalBooleanRootGridSearch? payoff accuracy).isSome = true)
    (who : Fin players) :
    rationalBooleanNashRegret payoff
      (rationalBooleanRootGridSelector payoff accuracy hsuccess) who ≤ accuracy := by
  let search := rationalBooleanRootGridSearch? payoff accuracy
  have hsome : search = some (search.get hsuccess) := (Option.some_get _).symm
  have haccepts :
      rationalBooleanGridAccepts payoff accuracy
        (rationalBooleanGridResolution payoff accuracy) (search.get hsuccess) = true := by
    exact List.find?_some hsome
  have htotal : rationalBooleanTotalNashDefect payoff
      (rationalBooleanRootGridSelector payoff accuracy hsuccess) ≤ accuracy :=
    of_decide_eq_true haccepts
  exact (le_max_left _ 0).trans <| (Finset.single_le_sum
    (f := fun player => max (rationalBooleanNashRegret payoff
      (rationalBooleanRootGridSelector payoff accuracy hsuccess) player) 0)
    (fun player _ => le_max_right _ _) (Finset.mem_univ who)).trans htotal

theorem rationalBooleanRootGridSelector_totalNashDefect_le
    (payoff : RationalBooleanPayoff players) (accuracy : ℚ)
    (hsuccess : (rationalBooleanRootGridSearch? payoff accuracy).isSome = true) :
    rationalBooleanTotalNashDefect payoff
      (rationalBooleanRootGridSelector payoff accuracy hsuccess) ≤ accuracy := by
  let search := rationalBooleanRootGridSearch? payoff accuracy
  have hsome : search = some (search.get hsuccess) := (Option.some_get _).symm
  have haccepts :
      rationalBooleanGridAccepts payoff accuracy
        (rationalBooleanGridResolution payoff accuracy) (search.get hsuccess) = true := by
    exact List.find?_some hsome
  exact of_decide_eq_true haccepts

end GameTheory.Finite
