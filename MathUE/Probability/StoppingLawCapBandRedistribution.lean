/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import MathUE.Probability.StoppingLawReconstruction
import MathUE.ProbabilityMassFunction.BoundedSupportAverage

/-!
# Cap-band redistribution of a complete stopping law

Mass on every stopping clock outside a supplied near-cap band is redirected
to one near-cap receiver.  The construction works on the complete law on
`Option Nat`, so `none` (Never) and infinitely supported finite clocks require
no separate finiteness assumption.

This module is game-independent.  A quitting-game adapter identifies `value`
with pure stopping-time payoffs and reconstructs a literal behavioral target.
-/

noncomputable section

namespace Math.Probability

open DiscreteHazard ProbabilityMassFunction

local instance capBandPropDecidable (proposition : Prop) :
    Decidable proposition :=
  Classical.propDecidable proposition

/-- A stopping clock lies outside the `epsilon`-near cap band. -/
def stoppingLawOutsideCapBand
    (value : Option ℕ → ℝ) (cap epsilon : ℝ) (choice : Option ℕ) : Prop :=
  epsilon < cap - value choice

/-- Redirect every clock outside the cap band to one receiver. -/
def stoppingLawCapBandRedirect
    (value : Option ℕ → ℝ) (cap epsilon : ℝ) (receiver choice : Option ℕ) :
    Option ℕ :=
  if stoppingLawOutsideCapBand value cap epsilon choice then receiver
  else choice

/-- Pushforward of a complete stopping law under cap-band redirection. -/
def stoppingLawCapBandPushforward
    (source : PMF (Option ℕ)) (value : Option ℕ → ℝ)
    (cap epsilon : ℝ) (receiver : Option ℕ) : PMF (Option ℕ) :=
  PMF.map (stoppingLawCapBandRedirect value cap epsilon receiver) source

/-- Source mass outside the cap band. -/
def stoppingLawOutsideCapBandMass
    (source : PMF (Option ℕ)) (value : Option ℕ → ℝ)
    (cap epsilon : ℝ) : ℝ :=
  expect source fun choice =>
    if stoppingLawOutsideCapBand value cap epsilon choice then 1 else 0

/-- The cap shortfall of the source average. -/
def stoppingLawSourceCapDebt
    (source : PMF (Option ℕ)) (value : Option ℕ → ℝ) (cap : ℝ) : ℝ :=
  cap - expect source value

private theorem expect_le_expect_of_bounded
    {Omega : Type*} (law : PMF Omega) (first second : Omega → ℝ)
    {firstBound secondBound : ℝ}
    (hfirst : ∀ point, |first point| ≤ firstBound)
    (hsecond : ∀ point, |second point| ≤ secondBound)
    (hle : ∀ point, first point ≤ second point) :
    expect law first ≤ expect law second := by
  have hfirstSum := expect_summable_of_bounded law first hfirst
  have hsecondSum := expect_summable_of_bounded law second hsecond
  exact hfirstSum.tsum_le_tsum
    (fun point => mul_le_mul_of_nonneg_left (hle point) ENNReal.toReal_nonneg)
    hsecondSum

private theorem expect_cap_sub
    {Omega : Type*} (law : PMF Omega) (value : Omega → ℝ) (cap M : ℝ)
    (hcap : |cap| ≤ M) (hvalue : ∀ point, |value point| ≤ M) :
    expect law (fun point => cap - value point) = cap - expect law value := by
  have hconstant : Summable (fun point : Omega => (law point).toReal * cap) :=
    expect_summable_of_bounded law (fun _ => cap) (fun _ => hcap)
  have hnegative : Summable
      (fun point => (law point).toReal * (-value point)) :=
    expect_summable_of_bounded law (fun point => -value point) (fun point => by
      simpa only [abs_neg] using hvalue point)
  calc
    expect law (fun point => cap - value point) =
        expect law (fun point => cap + -value point) := rfl
    _ = expect law (fun _ => cap) + expect law (fun point => -value point) :=
      expect_add_of_summable law _ _ hconstant hnegative
    _ = cap - expect law value := by rw [expect_const, expect_neg]; ring

@[simp] theorem stoppingLawCapBandRedirect_of_outside
    (value : Option ℕ → ℝ) (cap epsilon : ℝ) (receiver choice : Option ℕ)
    (houtside : stoppingLawOutsideCapBand value cap epsilon choice) :
    stoppingLawCapBandRedirect value cap epsilon receiver choice = receiver := by
  simp [stoppingLawCapBandRedirect, houtside]

@[simp] theorem stoppingLawCapBandRedirect_of_not_outside
    (value : Option ℕ → ℝ) (cap epsilon : ℝ) (receiver choice : Option ℕ)
    (houtside : ¬stoppingLawOutsideCapBand value cap epsilon choice) :
    stoppingLawCapBandRedirect value cap epsilon receiver choice = choice := by
  simp [stoppingLawCapBandRedirect, houtside]

/-- The supplied near-cap receiver is itself retained by the redirect map. -/
theorem stoppingLawCapBandRedirect_receiver
    (value : Option ℕ → ℝ) (cap epsilon : ℝ) (receiver : Option ℕ)
    (hepsilon : 0 < epsilon)
    (hreceiver : cap - epsilon / 2 < value receiver) :
    stoppingLawCapBandRedirect value cap epsilon receiver receiver = receiver := by
  apply stoppingLawCapBandRedirect_of_not_outside
  unfold stoppingLawOutsideCapBand
  linarith

/-- Every redirected clock has value at least `cap - epsilon`. -/
theorem stoppingLawCapBandRedirect_value_ge
    (value : Option ℕ → ℝ) (cap epsilon : ℝ) (receiver choice : Option ℕ)
    (hepsilon : 0 < epsilon)
    (hreceiver : cap - epsilon / 2 < value receiver) :
    cap - epsilon ≤
      value (stoppingLawCapBandRedirect value cap epsilon receiver choice) := by
  by_cases houtside : stoppingLawOutsideCapBand value cap epsilon choice
  · rw [stoppingLawCapBandRedirect_of_outside _ _ _ _ _ houtside]
    linarith
  · rw [stoppingLawCapBandRedirect_of_not_outside _ _ _ _ _ houtside]
    unfold stoppingLawOutsideCapBand at houtside
    linarith

/-- The pushed law has average value at least `cap - epsilon`. -/
theorem stoppingLawCapBandPushforward_expect_ge
    (source : PMF (Option ℕ)) (value : Option ℕ → ℝ)
    (cap epsilon M : ℝ) (receiver : Option ℕ)
    (hepsilon : 0 < epsilon)
    (hvalue : ∀ choice, |value choice| ≤ M)
    (hreceiver : cap - epsilon / 2 < value receiver) :
    cap - epsilon ≤
      expect (stoppingLawCapBandPushforward source value cap epsilon receiver)
        value := by
  rw [stoppingLawCapBandPushforward, expect_map]
  rw [← expect_const source (cap - epsilon)]
  apply expect_le_expect_of_bounded source
      (fun _ => cap - epsilon)
      (fun choice => value
        (stoppingLawCapBandRedirect value cap epsilon receiver choice))
      (fun _ => le_rfl) (fun choice => hvalue _) (fun choice => ?_)
  exact stoppingLawCapBandRedirect_value_ge value cap epsilon receiver choice
    hepsilon hreceiver

/-- Cap debt of the pushed average is at most the band width. -/
theorem stoppingLawCapBandPushforward_debt_le
    (source : PMF (Option ℕ)) (value : Option ℕ → ℝ)
    (cap epsilon M : ℝ) (receiver : Option ℕ)
    (hepsilon : 0 < epsilon)
    (hvalue : ∀ choice, |value choice| ≤ M)
    (hreceiver : cap - epsilon / 2 < value receiver) :
    cap - expect
      (stoppingLawCapBandPushforward source value cap epsilon receiver) value ≤
        epsilon := by
  linarith [stoppingLawCapBandPushforward_expect_ge source value cap epsilon M
    receiver hepsilon hvalue hreceiver]

/-- The pushed law gains at least source cap debt minus the band width. -/
theorem stoppingLawCapBandPushforward_gain_ge_debt_sub
    (source : PMF (Option ℕ)) (value : Option ℕ → ℝ)
    (cap epsilon M : ℝ) (receiver : Option ℕ)
    (hepsilon : 0 < epsilon)
    (hvalue : ∀ choice, |value choice| ≤ M)
    (hreceiver : cap - epsilon / 2 < value receiver) :
    stoppingLawSourceCapDebt source value cap - epsilon ≤
      expect (stoppingLawCapBandPushforward source value cap epsilon receiver)
          value - expect source value := by
  unfold stoppingLawSourceCapDebt
  linarith [stoppingLawCapBandPushforward_expect_ge source value cap epsilon M
    receiver hepsilon hvalue hreceiver]

/-- Source cap debt is paid by the band width plus twice the payoff bound
times the mass outside the band. -/
theorem stoppingLawSourceCapDebt_le_epsilon_add_two_mul_badMass
    (source : PMF (Option ℕ)) (value : Option ℕ → ℝ)
    (cap epsilon M : ℝ)
    (hM : 0 ≤ M) (hepsilon : 0 ≤ epsilon)
    (hcap : |cap| ≤ M) (hvalue : ∀ choice, |value choice| ≤ M)
    (hvalueCap : ∀ choice, value choice ≤ cap) :
    stoppingLawSourceCapDebt source value cap ≤
      epsilon + 2 * M *
        stoppingLawOutsideCapBandMass source value cap epsilon := by
  let indicator : Option ℕ → ℝ := fun choice =>
    if stoppingLawOutsideCapBand value cap epsilon choice then 1 else 0
  have hindicatorNonneg : ∀ choice, 0 ≤ indicator choice := by
    intro choice
    simp only [indicator]
    split <;> norm_num
  have hindicatorLe : ∀ choice, indicator choice ≤ 1 := by
    intro choice
    simp only [indicator]
    split <;> norm_num
  have hindicatorAbs : ∀ choice, |indicator choice| ≤ 1 := by
    intro choice
    rw [abs_of_nonneg (hindicatorNonneg choice)]
    exact hindicatorLe choice
  have hpointwise : ∀ choice,
      cap - value choice ≤ epsilon + 2 * M * indicator choice := by
    intro choice
    by_cases houtside : stoppingLawOutsideCapBand value cap epsilon choice
    · have hindicator : indicator choice = 1 := by simp [indicator, houtside]
      rw [hindicator]
      have hcapUpper := (abs_le.mp hcap).2
      have hvalueLower := (abs_le.mp (hvalue choice)).1
      linarith
    · have hindicator : indicator choice = 0 := by simp [indicator, houtside]
      rw [hindicator, mul_zero, add_zero]
      exact not_lt.mp houtside
  have hdefectBound : ∀ choice, |cap - value choice| ≤ 2 * M := by
    intro choice
    rw [abs_of_nonneg (sub_nonneg.mpr (hvalueCap choice))]
    have hcapUpper := (abs_le.mp hcap).2
    have hvalueLower := (abs_le.mp (hvalue choice)).1
    linarith
  have hrhsBound : ∀ choice,
      |epsilon + 2 * M * indicator choice| ≤ epsilon + 2 * M := by
    intro choice
    rw [abs_of_nonneg (add_nonneg hepsilon
      (mul_nonneg (mul_nonneg (by norm_num) hM) (hindicatorNonneg choice)))]
    nlinarith [hindicatorLe choice]
  have havg := expect_le_expect_of_bounded source
    (fun choice => cap - value choice)
    (fun choice => epsilon + 2 * M * indicator choice)
    hdefectBound hrhsBound hpointwise
  have hleft : expect source (fun choice => cap - value choice) =
      stoppingLawSourceCapDebt source value cap := by
    rw [expect_cap_sub source value cap M hcap hvalue]
    rfl
  have hconstant : Summable
      (fun choice : Option ℕ => (source choice).toReal * epsilon) :=
    expect_summable_of_bounded source (fun _ => epsilon) (fun _ => le_rfl)
  have hindicatorSum : Summable
      (fun choice => (source choice).toReal * (2 * M * indicator choice)) :=
    expect_summable_of_bounded source (fun choice => 2 * M * indicator choice)
      (fun choice => by
        rw [abs_of_nonneg (mul_nonneg (mul_nonneg (by norm_num) hM)
          (hindicatorNonneg choice))]
        exact mul_le_mul_of_nonneg_left (hindicatorLe choice)
          (mul_nonneg (by norm_num) hM))
  have hright : expect source (fun choice => epsilon + 2 * M * indicator choice) =
      epsilon + 2 * M * stoppingLawOutsideCapBandMass
        source value cap epsilon := by
    rw [expect_add_of_summable source _ _ hconstant hindicatorSum,
      expect_const, expect_const_mul]
    rfl
  rwa [hleft, hright] at havg

/-- Positive source debt above the band width forces positive bad mass. -/
theorem stoppingLawOutsideCapBandMass_pos
    (source : PMF (Option ℕ)) (value : Option ℕ → ℝ)
    (cap epsilon M : ℝ)
    (hM : 0 < M) (hepsilon : 0 ≤ epsilon)
    (hcap : |cap| ≤ M) (hvalue : ∀ choice, |value choice| ≤ M)
    (hvalueCap : ∀ choice, value choice ≤ cap)
    (hband : epsilon < stoppingLawSourceCapDebt source value cap) :
    0 < stoppingLawOutsideCapBandMass source value cap epsilon := by
  have hbound := stoppingLawSourceCapDebt_le_epsilon_add_two_mul_badMass
    source value cap epsilon M hM.le hepsilon hcap hvalue hvalueCap
  have hmassNonneg : 0 ≤ stoppingLawOutsideCapBandMass
      source value cap epsilon := by
    apply expect_nonneg
    intro choice
    split <;> norm_num
  nlinarith

/-- Positive cap-band bad mass is witnessed by a positive source atom. -/
theorem exists_mem_support_stoppingLawOutsideCapBand
    (source : PMF (Option ℕ)) (value : Option ℕ → ℝ)
    (cap epsilon : ℝ)
    (hmass : 0 < stoppingLawOutsideCapBandMass source value cap epsilon) :
    ∃ choice, choice ∈ source.support ∧
      stoppingLawOutsideCapBand value cap epsilon choice := by
  let indicator : Option ℕ → ℝ := fun choice =>
    if stoppingLawOutsideCapBand value cap epsilon choice then 1 else 0
  have hindicatorAbs : ∀ choice, |indicator choice| ≤ 1 := by
    intro choice
    simp only [indicator]
    split <;> norm_num
  obtain ⟨choice, hsupport, havg⟩ :=
    exists_mem_support_expect_le source indicator hindicatorAbs
  have havgPos : 0 < expect source indicator := by
    simpa only [stoppingLawOutsideCapBandMass, indicator] using hmass
  have hindicatorPos : 0 < indicator choice := havgPos.trans_le havg
  have houtside : stoppingLawOutsideCapBand value cap epsilon choice := by
    by_contra hnot
    simp [indicator, hnot] at hindicatorPos
  exact ⟨choice, hsupport, houtside⟩

/-! ## Prefix preservation under a supplied cut -/

/-- Redirecting no positive source mass from below the cut, and redirecting
no mass into a date below the cut, preserves each finite mass below the cut. -/
theorem stoppingLawCapBandPushforward_finiteMass_eq_of_lt
    (source : PMF (Option ℕ)) (value : Option ℕ → ℝ)
    (cap epsilon : ℝ) (receiver : Option ℕ) (cut time : ℕ)
    (hbadZero : ∀ earlier, earlier < cut →
      stoppingLawOutsideCapBand value cap epsilon (some earlier) →
        source (some earlier) = 0)
    (hreceiver : ∀ earlier, earlier < cut → receiver ≠ some earlier)
    (htime : time < cut) :
    StoppingLaw.finiteMass
        (stoppingLawCapBandPushforward source value cap epsilon receiver) time =
      StoppingLaw.finiteMass source time := by
  unfold StoppingLaw.finiteMass stoppingLawCapBandPushforward
  rw [PMF.map_apply]
  refine congrArg ENNReal.toReal (Eq.trans (tsum_congr (fun choice => ?_))
    (tsum_ite_eq (some time) (fun _ => source (some time))))
  by_cases houtside : stoppingLawOutsideCapBand value cap epsilon choice
  · rw [stoppingLawCapBandRedirect_of_outside _ _ _ _ _ houtside,
      if_neg (fun h => hreceiver time htime h.symm)]
    by_cases hchoice : choice = some time
    · subst choice
      rw [if_pos rfl, hbadZero time htime houtside]
    · rw [if_neg hchoice]
  · rw [stoppingLawCapBandRedirect_of_not_outside _ _ _ _ _ houtside]
    by_cases hchoice : choice = some time
    · subst choice
      simp
    · rw [if_neg hchoice, if_neg (fun h => hchoice h.symm)]

/-- Cap-band redirection preserves stopping-law survival through the cut. -/
theorem stoppingLawCapBandPushforward_survival_eq_of_le
    (source : PMF (Option ℕ)) (value : Option ℕ → ℝ)
    (cap epsilon : ℝ) (receiver : Option ℕ) (cut time : ℕ)
    (hbadZero : ∀ earlier, earlier < cut →
      stoppingLawOutsideCapBand value cap epsilon (some earlier) →
        source (some earlier) = 0)
    (hreceiver : ∀ earlier, earlier < cut → receiver ≠ some earlier)
    (htime : time ≤ cut) :
    StoppingLaw.survival
        (stoppingLawCapBandPushforward source value cap epsilon receiver) time =
      StoppingLaw.survival source time := by
  unfold StoppingLaw.survival
  apply congrArg (fun total => 1 - total)
  refine Finset.sum_congr rfl (fun earlier hearlier => ?_)
  rw [Finset.mem_range] at hearlier
  exact stoppingLawCapBandPushforward_finiteMass_eq_of_lt source value cap
    epsilon receiver cut earlier hbadZero hreceiver (hearlier.trans_le htime)

/-- Reconstructed conditional stop probabilities agree below the cut. -/
theorem stoppingLawCapBandPushforward_stop_eq_of_lt
    (source : PMF (Option ℕ)) (value : Option ℕ → ℝ)
    (cap epsilon : ℝ) (receiver : Option ℕ) (cut time : ℕ)
    (hbadZero : ∀ earlier, earlier < cut →
      stoppingLawOutsideCapBand value cap epsilon (some earlier) →
        source (some earlier) = 0)
    (hreceiver : ∀ earlier, earlier < cut → receiver ≠ some earlier)
    (htime : time < cut) :
    (StoppingLaw.toScalarHazard
        (stoppingLawCapBandPushforward source value cap epsilon receiver)).stop
          time =
      (StoppingLaw.toScalarHazard source).stop time := by
  have hsurvival := stoppingLawCapBandPushforward_survival_eq_of_le
    source value cap epsilon receiver cut time hbadZero hreceiver htime.le
  have hmass := stoppingLawCapBandPushforward_finiteMass_eq_of_lt
    source value cap epsilon receiver cut time hbadZero hreceiver htime
  simp only [StoppingLaw.toScalarHazard, hsurvival, hmass]

/-- On a positive-survival live prefix, the canonical Boolean hazard of the
redirected law is literally the original Boolean hazard. -/
theorem stoppingLawCapBandPushforward_toBoolean_apply_eq_of_lt
    (sourceHazard : BooleanHazard) (value : Option ℕ → ℝ)
    (cap epsilon : ℝ) (receiver : Option ℕ) (cut time : ℕ)
    (hbadZero : ∀ earlier, earlier < cut →
      stoppingLawOutsideCapBand value cap epsilon (some earlier) →
        sourceHazard.toScalar.stoppingLaw (some earlier) = 0)
    (hreceiver : ∀ earlier, earlier < cut → receiver ≠ some earlier)
    (htime : time < cut)
    (hsurvival : 0 < sourceHazard.toScalar.survival 0 time) :
    (StoppingLaw.toScalarHazard
        (stoppingLawCapBandPushforward sourceHazard.toScalar.stoppingLaw
          value cap epsilon receiver)).toBoolean time =
      sourceHazard time := by
  have htargetSource := stoppingLawCapBandPushforward_stop_eq_of_lt
    sourceHazard.toScalar.stoppingLaw value cap epsilon receiver cut time
      hbadZero hreceiver htime
  have hsource :=
    StoppingLaw.toScalarHazard_stoppingLaw_stop_eq_of_survival_pos
      sourceHazard.toScalar time hsurvival
  apply ProbabilityMassFunction.eq_of_forall_toReal_eq
  intro stop
  cases stop with
  | false =>
      have hcontinue := continue_add_stop sourceHazard time
      unfold continueProbability stopProbability at hcontinue
      have hstop := htargetSource.trans hsource
      change (StoppingLaw.toScalarHazard
        (stoppingLawCapBandPushforward sourceHazard.toScalar.stoppingLaw
          value cap epsilon receiver)).stop time =
            (sourceHazard time true).toReal at hstop
      simp only [ScalarHazard.toBoolean, booleanCoin_false_toReal]
      linarith
  | true =>
      simpa only [ScalarHazard.toBoolean, booleanCoin_true_toReal,
        BooleanHazard.toScalar, stopProbability] using
        htargetSource.trans hsource

end Math.Probability
