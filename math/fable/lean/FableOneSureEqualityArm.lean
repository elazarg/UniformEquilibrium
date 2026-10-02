/-
The equality arm of the exact one-sure owner response.

Fix a one-date-then-Never profile at a product root with one sure quitter
`owner`, assume its terminal semantic pair is a positive global carrier minimum
of total debt, and pass to the literal owner response of the previous file.
This file records the two facts the equality arm needs.

* **Positive opponent incidence.**  Write `a` for the probability that some
  opponent of `owner` quits at the root.  When the solo reward is nonnegative,
  the checked singleton margin at the minimum bounds the total debt by
  `2 R a`, so a bounded reward table with positive minimum debt forces
  `a > 0`.  When the solo reward is negative the response plays Never, the
  whole target law would then be the Never atom, and the checked four-player
  hard-residual finite-atom theorem excludes that; so again `a > 0`.
* **The same-target reset re-anchor.**  On the equality arm the response
  target's own joint semantic/law point is the origin, the minimum, and the
  retained point of its own law-tight cap--Nash saturation hull.  Its owner
  coordinate carries zero debt, and `a > 0` supplies positive total opponent
  incidence, so the checked positive-incidence reset theorem applies at that
  literal point.

Nothing here reselects a minimum semantic point, law, or profile: every
anchor is the response target produced by the previous file.
-/
import FableOneSureOwnerResponse
import UniformEquilibrium.Diagnostics.Quitting.LawTightCapNashStrictMinimum
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticAuxiliaryNashBudget
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticFinFourMinimumLawFiniteAtom

noncomputable section

namespace GameTheory

open _root_.Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## Opponent absorption at a product root -/

/-- The probability that at least one opponent of `who` quits at the product
root: the complement of the opponents' all-Continue mass. -/
def fableOppAbsorb (root : ι → PMF Bool) (who : ι) : ℝ :=
  1 - fableOppContinue root who

theorem fableOppAbsorb_eq (root : ι → PMF Bool) (who : ι) :
    fableOppAbsorb root who = 1 - fableOppContinue root who := rfl

/-- Opponent absorption is the production opponent-absorption hazard. -/
theorem fableOppAbsorb_eq_opponentAbsorptionMass
    (root : ι → PMF Bool) (who : ι) :
    fableOppAbsorb root who = quittingRootOpponentAbsorptionMass root who := rfl

theorem fableOppAbsorb_nonneg (root : ι → PMF Bool) (who : ι) :
    0 ≤ fableOppAbsorb root who := by
  have hle := fableOppContinue_le_one root who
  rw [fableOppAbsorb_eq]
  linarith

/-- Opponent absorption is the opponents' union quit probability. -/
theorem fableOppAbsorb_eq_one_sub_prod (root : ι → PMF Bool) (who : ι) :
    fableOppAbsorb root who =
      1 - ∏ other ∈ Finset.univ.erase who, (1 - (root other true).toReal) := by
  rw [fableOppAbsorb_eq_opponentAbsorptionMass,
    quittingRootOpponentAbsorptionMass_eq_one_sub_prod]

/-- Opponent absorption is the total nonempty exact-coalition mass of the row
in which `who` is forced to Continue. -/
theorem fable_sum_oppCoalitionMass_eq_oppAbsorb
    (root : ι → PMF Bool) (who : ι) :
    ∑ S : {S : Finset ι // S.Nonempty},
        quittingRootCoalitionMass
          (Function.update root who (PMF.pure false)) S.val =
      fableOppAbsorb root who :=
  fable_sum_rootCoalitionMass_eq_absorptionMass _

/-- The zero-tail Continue endpoint is the exact opponent-coalition average of
the observer's terminal rewards. -/
theorem fableContinueEndpoint_eq_sum_oppCoalitionMass
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι) :
    fableContinueEndpoint reward root who =
      ∑ S : {S : Finset ι // S.Nonempty},
        quittingRootCoalitionMass
            (Function.update root who (PMF.pure false)) S.val * reward S who :=
  fableContinueEndpoint_eq_rowMoment reward root who

/-! ## E1: the singleton margin transported to the source minimum -/

/-- **Theorem E1.**  At a positive global carrier minimum realized by the
one-date-then-Never profile, every cap coordinate exceeds its own solo reward
by at least the whole minimum debt. -/
theorem fable_oneSure_minimum_singletonMargin
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool)
    (hmin : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward
            (quittingOneDateThenNeverProfile reward root)) ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpos : 0 < quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward
        (quittingOneDateThenNeverProfile reward root)))
    (who : ι) :
    quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward
          (quittingOneDateThenNeverProfile reward root)) ≤
      (quittingTerminalSemanticPair reward
          (quittingOneDateThenNeverProfile reward root)).2 who -
        reward (quittingSingletonTerminal who) who :=
  minimumTerminalSemantic_singletonMargin (reward := reward) _
    (quittingTerminalSemanticPair_mem_carrier reward _) hmin hpos who

/-! ## E2: the quantitative incidence estimate at nonnegative solo reward -/

/-- **Theorem E2.**  With a sure owner carrying positive debt at a positive
global carrier minimum, and with nonnegative solo reward, the whole minimum
debt is at most twice the reward bound times the opponents' root absorption. -/
theorem fable_oneSure_nonnegSolo_debtSum_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (owner : ι) {R : ℝ}
    (hR : ∀ S player, |reward S player| ≤ R)
    (hsure : (root owner true).toReal = 1)
    (hdebt : 0 < quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward
        (quittingOneDateThenNeverProfile reward root)) owner)
    (hmin : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward
            (quittingOneDateThenNeverProfile reward root)) ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpos : 0 < quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward
        (quittingOneDateThenNeverProfile reward root)))
    (hsolo : 0 ≤ reward (quittingSingletonTerminal owner) owner) :
    quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward
          (quittingOneDateThenNeverProfile reward root)) ≤
      2 * R * fableOppAbsorb root owner := by
  classical
  set solo := reward (quittingSingletonTerminal owner) owner with hsolodef
  set mass : {S : Finset ι // S.Nonempty} → ℝ := fun S =>
    quittingRootCoalitionMass
      (Function.update root owner (PMF.pure false)) S.val with hmassdef
  have hmassNonneg : ∀ S : {S : Finset ι // S.Nonempty}, 0 ≤ mass S := fun S =>
    quittingRootCoalitionMass_nonneg _ _
  have hmassSum : ∑ S, mass S = fableOppAbsorb root owner :=
    fable_sum_oppCoalitionMass_eq_oppAbsorb root owner
  have hmassContinue : ∑ S, mass S = 1 - fableOppContinue root owner := by
    rw [hmassSum, fableOppAbsorb_eq]
  have hmargin :=
    fable_oneSure_minimum_singletonMargin reward root hmin hpos owner
  have hcap :=
    fable_oneSure_capCoordinate_eq_augmentedContinue reward root owner hsure
      hdebt
  have haug : fableAugmentedContinueValue reward root owner =
      fableContinueEndpoint reward root owner +
        fableOppContinue root owner * solo := by
    rw [fableAugmentedContinueValue_eq, max_eq_right hsolo]
  have hexpand : ∑ S : {S : Finset ι // S.Nonempty},
        mass S * (reward S owner - solo) =
      fableContinueEndpoint reward root owner +
        fableOppContinue root owner * solo - solo := by
    have hsplit : ∑ S : {S : Finset ι // S.Nonempty},
          mass S * (reward S owner - solo) =
        (∑ S : {S : Finset ι // S.Nonempty}, mass S * reward S owner) -
          (∑ S : {S : Finset ι // S.Nonempty}, mass S) * solo := by
      rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun S _ => by ring
    rw [hsplit, hmassContinue, ← fableContinueEndpoint_eq_sum_oppCoalitionMass]
    ring
  have hsoloBound : -R ≤ solo := (abs_le.mp (hR _ owner)).1
  have hterm : ∀ S ∈ (Finset.univ : Finset {S : Finset ι // S.Nonempty}),
      mass S * (reward S owner - solo) ≤ mass S * (2 * R) := by
    intro S _
    refine mul_le_mul_of_nonneg_left ?_ (hmassNonneg S)
    have hupper : reward S owner ≤ R := (abs_le.mp (hR S owner)).2
    linarith
  have hsumBound : ∑ S : {S : Finset ι // S.Nonempty},
      mass S * (reward S owner - solo) ≤ 2 * R * fableOppAbsorb root owner := by
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [← Finset.sum_mul, hmassSum]
    linarith
  rw [hexpand] at hsumBound
  rw [hcap, haug] at hmargin
  linarith

/-! ## E3: positive opponent incidence at nonnegative solo reward -/

/-- **Theorem E3.**  The same hypotheses without a displayed reward bound give
strictly positive opponent root absorption. -/
theorem fable_oneSure_nonnegSolo_oppAbsorb_pos
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (owner : ι)
    (hsure : (root owner true).toReal = 1)
    (hdebt : 0 < quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward
        (quittingOneDateThenNeverProfile reward root)) owner)
    (hmin : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward
            (quittingOneDateThenNeverProfile reward root)) ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpos : 0 < quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward
        (quittingOneDateThenNeverProfile reward root)))
    (hsolo : 0 ≤ reward (quittingSingletonTerminal owner) owner) :
    0 < fableOppAbsorb root owner := by
  obtain ⟨M, _, hM⟩ := exists_quittingRewardBound reward
  have hle := fable_oneSure_nonnegSolo_debtSum_le reward root owner hM hsure
    hdebt hmin hpos hsolo
  rcases (fableOppAbsorb_nonneg root owner).lt_or_eq with hlt | heq
  · exact hlt
  · rw [← heq, mul_zero] at hle
    linarith

/-! ## The response target's live rows and terminal law -/

/-- The response target's live row is the one-date-then-Never row with only
the owner's coordinate overwritten by the response plan's hazard. -/
theorem fable_liveRoot_ownerResponse
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (owner : ι) (time : ℕ) :
    quittingProfileLiveRoot reward
        (fableOneSureOwnerResponseProfile reward root owner) time =
      Function.update
        (quittingProfileLiveRoot reward
          (quittingOneDateThenNeverProfile reward root) time) owner
        (quittingPureTimeHazard (fableOneSureOwnerChoice reward owner) time) :=
  fable_liveRoot_update reward (quittingOneDateThenNeverProfile reward root)
    owner _ time

omit [DecidableEq ι] in
/-- The zero-date live row of a one-date-then-Never profile is its root. -/
theorem fable_liveRoot_oneDateThenNever_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (root : ι → PMF Bool) :
    quittingProfileLiveRoot reward
      (quittingOneDateThenNeverProfile reward root) 0 = root := rfl

omit [DecidableEq ι] in
/-- Every later live row of a one-date-then-Never profile is all-Continue. -/
theorem fable_liveRoot_oneDateThenNever_succ
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (root : ι → PMF Bool)
    (time : ℕ) :
    quittingProfileLiveRoot reward
        (quittingOneDateThenNeverProfile reward root) (time + 1) =
      (quittingAllContinueRoot : ι → PMF Bool) := rfl

omit [Fintype ι] [DecidableEq ι] in
/-- The response plan continues at the root whatever the sign of the solo
reward: the nonnegative branch quits one date later. -/
theorem fable_ownerResponse_hazard_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (owner : ι) :
    quittingPureTimeHazard (fableOneSureOwnerChoice reward owner) 0 =
      PMF.pure false := by
  unfold fableOneSureOwnerChoice
  by_cases hsolo : 0 ≤ reward (quittingSingletonTerminal owner) owner
  · rw [if_pos hsolo]
    exact quittingPureTimeHazard_some_of_ne (by omega)
  · rw [if_neg hsolo]
    exact quittingPureTimeHazard_none 0

/-- The response target's zero-date live row is the product root with the
owner forced to Continue. -/
theorem fable_liveRoot_ownerResponse_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (owner : ι) :
    quittingProfileLiveRoot reward
        (fableOneSureOwnerResponseProfile reward root owner) 0 =
      Function.update root owner (PMF.pure false) := by
  rw [fable_liveRoot_ownerResponse, fable_liveRoot_oneDateThenNever_zero,
    fable_ownerResponse_hazard_zero]

/-- **Law floor.**  Every nonempty opponent coalition of the product root keeps
at least its literal root mass in the response target's terminal law. -/
theorem fable_oppCoalitionMass_le_ownerResponse_outcomeMass
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (owner : ι)
    (terminal : {S : Finset ι // S.Nonempty}) :
    quittingRootCoalitionMass (Function.update root owner (PMF.pure false))
        terminal.val ≤
      quittingTerminalOutcomeMass reward
        (fableOneSureOwnerResponseProfile reward root owner)
        (some terminal) := by
  have hsum := fable_hasSum_stageCoalitionMass_absorbedMassLimit reward
    (fableOneSureOwnerResponseProfile reward root owner) terminal
  have hstage : quittingStageCoalitionMass reward
        (fableOneSureOwnerResponseProfile reward root owner) 0 terminal =
      quittingRootCoalitionMass (Function.update root owner (PMF.pure false))
        terminal.val := by
    rw [quittingStageCoalitionMass_eq_liveMass_mul_rootCoalitionMass,
      quittingLiveMass_zero, one_mul, fable_liveRoot_ownerResponse_zero]
  have hle := le_hasSum hsum 0 fun time _ =>
    quittingStageCoalitionMass_nonneg reward
      (fableOneSureOwnerResponseProfile reward root owner) time terminal
  rwa [hstage] at hle

/-! ## Positive total opponent incidence at the response target -/

/-- **Incidence bridge.**  Positive opponent root absorption gives the response
target's terminal law strictly positive total opponent incidence at the owner.
Total opponent incidence counts a terminal once per opponent it contains, so
this is a lower bound and not an identity. -/
theorem fable_ownerResponse_totalOpponentIncidence_pos
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (owner : ι)
    (habsorb : 0 < fableOppAbsorb root owner) :
    0 < quittingTerminalTotalOpponentIncidenceMass owner
      (quittingTerminalOutcomeMass reward
        (fableOneSureOwnerResponseProfile reward root owner)) := by
  set law := quittingTerminalOutcomeMass reward
    (fableOneSureOwnerResponseProfile reward root owner) with hlawdef
  have hlawNonneg : ∀ terminal : {S : Finset ι // S.Nonempty},
      0 ≤ law (some terminal) := fun terminal =>
    quittingAbsorbedMassLimit_nonneg reward _ terminal
  have hsum : ∑ S : {S : Finset ι // S.Nonempty}, (0 : ℝ) <
      ∑ S : {S : Finset ι // S.Nonempty},
        quittingRootCoalitionMass
          (Function.update root owner (PMF.pure false)) S.val := by
    rw [Finset.sum_const_zero, fable_sum_oppCoalitionMass_eq_oppAbsorb]
    exact habsorb
  obtain ⟨terminal, -, hterminal⟩ := Finset.exists_lt_of_sum_lt hsum
  have hownerNot : owner ∉ terminal.val := by
    intro hmem
    have hrate : quittingRootQuitRates
        (Function.update root owner (PMF.pure false)) owner = 0 := by
      show ((Function.update root owner (PMF.pure false) owner) true).toReal = 0
      rw [Function.update_self]
      simp
    have hzero : quittingRootCoalitionMass
        (Function.update root owner (PMF.pure false)) terminal.val = 0 := by
      rw [quittingRootCoalitionMass, coalitionMass,
        Finset.prod_eq_zero hmem hrate, zero_mul]
    rw [hzero] at hterminal
    exact lt_irrefl 0 hterminal
  obtain ⟨other, hother⟩ := terminal.2
  have hne : other ≠ owner := fun hself => hownerNot (hself ▸ hother)
  have hpositiveMass : 0 < law (some terminal) :=
    lt_of_lt_of_le hterminal
      (fable_oppCoalitionMass_le_ownerResponse_outcomeMass reward root owner
        terminal)
  have hcoordinate :
      0 < quittingTerminalOpponentIncidenceMass owner other law := by
    refine lt_of_lt_of_le hpositiveMass (Finset.single_le_sum
      (f := fun candidate : {S : Finset ι // S.Nonempty} => law (some candidate))
      (fun candidate _ => hlawNonneg candidate) ?_)
    simp [hother, hne]
  refine lt_of_lt_of_le hcoordinate (Finset.single_le_sum
    (f := fun player => quittingTerminalOpponentIncidenceMass owner player law)
    (fun player _ => ?_) (by simp [hne]))
  exact Finset.sum_nonneg fun candidate _ => hlawNonneg candidate

/-! ## E4: positive opponent incidence at negative solo reward -/

omit [Fintype ι] [DecidableEq ι] in
/-- With a negative solo reward the owner's response plan is literally Never. -/
theorem fable_ownerResponse_choice_eq_none
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (owner : ι)
    (hsolo : reward (quittingSingletonTerminal owner) owner < 0) :
    fableOneSureOwnerChoice reward owner = none := by
  unfold fableOneSureOwnerChoice
  rw [if_neg (not_le.mpr hsolo)]

omit [DecidableEq ι] in
/-- The all-Continue row absorbs no mass. -/
theorem fable_rootAbsorptionMass_allContinueRoot :
    quittingRootAbsorptionMass (quittingAllContinueRoot : ι → PMF Bool) = 0 := by
  unfold quittingRootAbsorptionMass
  rw [quittingStationaryContinueMass_eq_prod_continueProbability]
  simp [quittingAllContinueRoot]

/-- With zero opponent root absorption and a Never response plan, every live
row of the response target absorbs no mass. -/
theorem fable_ownerResponse_never_rootAbsorptionMass_eq_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (owner : ι)
    (hsolo : reward (quittingSingletonTerminal owner) owner < 0)
    (hzero : fableOppAbsorb root owner = 0) (time : ℕ) :
    quittingRootAbsorptionMass
      (quittingProfileLiveRoot reward
        (fableOneSureOwnerResponseProfile reward root owner) time) = 0 := by
  cases time with
  | zero =>
      rw [fable_liveRoot_ownerResponse_zero]
      exact hzero
  | succ past =>
      have hupdate : Function.update (quittingAllContinueRoot : ι → PMF Bool)
          owner (PMF.pure false) = quittingAllContinueRoot := by
        funext player
        by_cases hplayer : player = owner
        · rw [hplayer, Function.update_self]
          rfl
        · rw [Function.update_of_ne hplayer]
      rw [fable_liveRoot_ownerResponse, fable_liveRoot_oneDateThenNever_succ,
        fable_ownerResponse_choice_eq_none reward owner hsolo,
        quittingPureTimeHazard_none, hupdate]
      exact fable_rootAbsorptionMass_allContinueRoot

/-- Under those hypotheses the response target's terminal law puts no mass on
any finite coalition: it is the pure Never law. -/
theorem fable_ownerResponse_never_outcomeMass_eq_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (owner : ι)
    (hsolo : reward (quittingSingletonTerminal owner) owner < 0)
    (hzero : fableOppAbsorb root owner = 0)
    (terminal : {S : Finset ι // S.Nonempty}) :
    quittingTerminalOutcomeMass reward
      (fableOneSureOwnerResponseProfile reward root owner) (some terminal) =
      0 := by
  have hstage : ∀ time, quittingStageCoalitionMass reward
      (fableOneSureOwnerResponseProfile reward root owner) time terminal = 0 := by
    intro time
    have hle := fable_coalitionMass_le_absorptionMass
      (quittingProfileLiveRoot reward
        (fableOneSureOwnerResponseProfile reward root owner) time) terminal.2
    rw [fable_ownerResponse_never_rootAbsorptionMass_eq_zero reward root owner
      hsolo hzero time] at hle
    have hnn := quittingRootCoalitionMass_nonneg
      (quittingProfileLiveRoot reward
        (fableOneSureOwnerResponseProfile reward root owner) time) terminal.val
    rw [quittingStageCoalitionMass_eq_liveMass_mul_rootCoalitionMass,
      le_antisymm hle hnn, mul_zero]
  rw [fable_terminalOutcomeMass_some_eq_tsum_stage]
  simp [hstage]

/-- **Theorem E4.**  In the four-player hard residual, an equality-arm response
target with negative solo reward has strictly positive opponent root
absorption.  Zero absorption would make the target law pure Never, which the
checked positive finite-atom theorem excludes at a global minimum. -/
theorem fable_finFour_oneSure_negSolo_oppAbsorb_pos
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (bound : ℝ)
    (residual : FinFourQuantitativeFullSupportHardResidual reward bound)
    (root : Fin 4 → PMF Bool) (owner : Fin 4)
    (hmin : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward
            (quittingOneDateThenNeverProfile reward root)) ≤
        quittingTerminalSemanticDebtSum candidate)
    (heq : quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward
          (fableOneSureOwnerResponseProfile reward root owner)) =
      quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward
          (quittingOneDateThenNeverProfile reward root)))
    (hsolo : reward (quittingSingletonTerminal owner) owner < 0) :
    0 < fableOppAbsorb root owner := by
  rcases (fableOppAbsorb_nonneg root owner).lt_or_eq with hlt | hvanish
  · exact hlt
  · exfalso
    have hzero : fableOppAbsorb root owner = 0 := hvanish.symm
    have htarget : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
        quittingTerminalSemanticDebtSum (quittingTerminalSemanticPair reward
            (fableOneSureOwnerResponseProfile reward root owner)) ≤
          quittingTerminalSemanticDebtSum candidate := by
      intro candidate hcandidate
      rw [heq]
      exact hmin candidate hcandidate
    obtain ⟨terminal, hterminal⟩ :=
      exists_positive_finiteLawAtom_of_finFourHardResidual_minimum reward bound
        residual
        (quittingTerminalSemanticPair reward
            (fableOneSureOwnerResponseProfile reward root owner),
          quittingTerminalOutcomeMass reward
            (fableOneSureOwnerResponseProfile reward root owner))
        (quittingTerminalSemanticLawPoint_mem_carrier reward _) htarget
    have hpositive : 0 < quittingTerminalOutcomeMass reward
        (fableOneSureOwnerResponseProfile reward root owner) (some terminal) :=
      hterminal
    rw [fable_ownerResponse_never_outcomeMass_eq_zero reward root owner hsolo
      hzero terminal] at hpositive
    exact lt_irrefl 0 hpositive

/-- **Equality-arm incidence.**  Both signs of the solo reward give the
equality target strictly positive opponent root absorption. -/
theorem fable_finFour_oneSure_equality_oppAbsorb_pos
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (bound : ℝ)
    (residual : FinFourQuantitativeFullSupportHardResidual reward bound)
    (root : Fin 4 → PMF Bool) (owner : Fin 4)
    (hsure : (root owner true).toReal = 1)
    (hdebt : 0 < quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward
        (quittingOneDateThenNeverProfile reward root)) owner)
    (hmin : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward
            (quittingOneDateThenNeverProfile reward root)) ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpos : 0 < quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward
        (quittingOneDateThenNeverProfile reward root)))
    (heq : quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward
          (fableOneSureOwnerResponseProfile reward root owner)) =
      quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward
          (quittingOneDateThenNeverProfile reward root))) :
    0 < fableOppAbsorb root owner := by
  by_cases hsolo : 0 ≤ reward (quittingSingletonTerminal owner) owner
  · exact fable_oneSure_nonnegSolo_oppAbsorb_pos reward root owner hsure hdebt
      hmin hpos hsolo
  · exact fable_finFour_oneSure_negSolo_oppAbsorb_pos reward bound residual root
      owner hmin heq (not_le.mp hsolo)

/-! ## E5: the same-target reset re-anchor -/

/-- The joint semantic/law point of the owner's response target. -/
def fableOneSureOwnerResponsePoint
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (owner : ι) :
    QuittingTerminalSemanticLawPoint ι :=
  (quittingTerminalSemanticPair reward
      (fableOneSureOwnerResponseProfile reward root owner),
    quittingTerminalOutcomeMass reward
      (fableOneSureOwnerResponseProfile reward root owner))

theorem fableOneSureOwnerResponsePoint_mem_lawCarrier
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (owner : ι) :
    fableOneSureOwnerResponsePoint reward root owner ∈
      quittingTerminalSemanticLawCarrier reward :=
  quittingTerminalSemanticLawPoint_mem_carrier reward _

/-- The semantic projection of the joint carrier lands in the ordinary
terminal-semantic carrier. -/
theorem fable_fst_mem_terminalSemanticCarrier
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (point : QuittingTerminalSemanticLawPoint ι)
    (hpoint : point ∈ quittingTerminalSemanticLawCarrier reward) :
    point.1 ∈ quittingTerminalSemanticCarrier reward := by
  have hclosed : IsClosed
      (Prod.fst ⁻¹' quittingTerminalSemanticCarrier reward :
        Set (QuittingTerminalSemanticLawPoint ι)) :=
    isClosed_closure.preimage continuous_fst
  have hsubset : quittingAttainableTerminalSemanticLawPoints reward ⊆
      (Prod.fst ⁻¹' quittingTerminalSemanticCarrier reward :
        Set (QuittingTerminalSemanticLawPoint ι)) := by
    rintro candidate ⟨profile, rfl⟩
    exact quittingTerminalSemanticPair_mem_carrier reward profile
  exact closure_minimal hsubset hclosed hpoint

/-- A joint carrier point whose semantic pair is a global carrier minimum is
the debt minimum of its own law-tight cap--Nash saturation hull. -/
theorem fable_isLawTightSaturationMinimum_self
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (point : QuittingTerminalSemanticLawPoint ι)
    (hpoint : point ∈ quittingTerminalSemanticLawCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum point.1 ≤
        quittingTerminalSemanticDebtSum candidate) :
    IsQuittingLawTightCapNashSaturationMinimum reward point point where
  mem := quittingLawTightCapNashSaturationHull_origin_mem reward point
  debt_le := fun candidate hcandidate =>
    hminimum candidate.1 (fable_fst_mem_terminalSemanticCarrier reward candidate
      (quittingLawTightCapNashSaturationHull_subset_carrier reward point hpoint
        hcandidate))

/-- **Theorem E5.**  On the equality arm the response target's own joint point
is the origin, the minimum, and the retained point of its own law-tight
cap--Nash saturation hull; its owner coordinate carries zero debt and its law
carries positive total opponent incidence, so it enters the checked
reset-rigid same-law chamber at that literal point. -/
theorem fable_finFour_oneSure_equality_resetRigidChamber
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (bound : ℝ)
    (residual : FinFourQuantitativeFullSupportHardResidual reward bound)
    (root : Fin 4 → PMF Bool) (owner : Fin 4)
    (hsure : (root owner true).toReal = 1)
    (hdebt : 0 < quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward
        (quittingOneDateThenNeverProfile reward root)) owner)
    (hmin : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward
            (quittingOneDateThenNeverProfile reward root)) ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpos : 0 < quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward
        (quittingOneDateThenNeverProfile reward root)))
    (heq : quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward
          (fableOneSureOwnerResponseProfile reward root owner)) =
      quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward
          (quittingOneDateThenNeverProfile reward root))) :
    Nonempty (QuittingLawTightResetRigidChamber reward
      (fableOneSureOwnerResponsePoint reward root owner)
      (fableOneSureOwnerResponsePoint reward root owner)
      (fableOneSureOwnerResponsePoint reward root owner)
      (quittingTerminalSemanticPair reward
        (fableOneSureOwnerResponseProfile reward root owner))) := by
  have hpoint := fableOneSureOwnerResponsePoint_mem_lawCarrier reward root owner
  have htarget : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward
            (fableOneSureOwnerResponseProfile reward root owner)) ≤
        quittingTerminalSemanticDebtSum candidate := by
    intro candidate hcandidate
    rw [heq]
    exact hmin candidate hcandidate
  have hminimum := fable_isLawTightSaturationMinimum_self reward
    (fableOneSureOwnerResponsePoint reward root owner) hpoint htarget
  have hpositiveSum : 0 < quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward
        (fableOneSureOwnerResponseProfile reward root owner)) := by
    rw [heq]
    exact hpos
  have hreset :=
    fable_oneSure_ownerResponse_debt_eq_zero reward root owner hsure hdebt
  have hincidence := fable_ownerResponse_totalOpponentIncidence_pos reward root
    owner (fable_finFour_oneSure_equality_oppAbsorb_pos reward bound residual
      root owner hsure hdebt hmin hpos heq)
  exact exists_quittingLawTightResetRigidChamber residual.witness
    (quittingTerminalSemanticPair reward
      (fableOneSureOwnerResponseProfile reward root owner))
    htarget hpositiveSum _ _ _ hpoint hminimum hminimum.minimum_mem_face owner
    hreset hincidence

end GameTheory
