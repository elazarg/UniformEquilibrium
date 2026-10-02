/-
Through-mark ledger adapters: floor-to-defect, exact-stack no-go, option split.

The directed-transport ledger of the all-Continue spine, summed over players,
writes the total semantic debt of a profile as a live-mass-weighted sum of
one-stage total cap Nash defects through a cutoff, plus the survival-weighted
debt of the spine tail at that cutoff.  Reading that identity as an account of
the *reached cap-defect ledger* `C` through a mark supports three independent
adapters.

*Charge-normalized moat.*  With only global minimality of a source pair, `C`
is bounded below by absorption times the minimum debt, up to the tail's own
debt excess.  No tightness, reward bound, or limiting hypothesis enters.

*Floor-to-defect.*  Along a limit-tight sequence the pre-mark absorption floor
caps the survival factor by `(2 * M + sigma) / (2 * M + gamma)`, so the
absorption factor is at least `(gamma - sigma) / (2 * M + gamma)`, while the
tail debts converge to the minimum.  Both eventual facts combine into an
eventual floor on `C` at rate `(gamma - sigma) / (2 * M + gamma)` times the
minimum debt, with any prescribed additive slack.

*Exact-stack no-go.*  Exact cap--Nash prefixing multiplies total debt by the
word's joint survival product.  Over a base whose debt is within `e` of the
global minimum, minimality forces the product above `D / (D + e)`: the word's
absorption is at most `e / (D + e)`, so exactification over near-minimum tails
cannot retain absorption.

*Option-budget split.*  The checked one-row inequality subtracts the precise
own-Quit option budget from a cap defect to reach the literal
prescribed-side defect.  The option coefficient is exactly the singleton
coalition mass of the live root, so live weighting turns it into the singleton
stage mass.  Hence `C` splits into `2 * M` times the through-mark singleton
stage mass plus the live-weighted literal defect ledger, and any lower bound
on `C` is carried by one of the two summands.
-/
import FableNeverMassCeiling
import MathUE.PMFProduct.SmallHazardBounds
import UniformEquilibrium.Diagnostics.Quitting.TerminalCapNashChronology
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticDirectedTransport
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticOwnStrategyTransport
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauIncidence
import UniformEquilibrium.Quitting.Cycles.BehaviorPureTimeExtremality
import UniformEquilibrium.Quitting.Root.OpponentCoalitionMass

noncomputable section

namespace GameTheory

open _root_.Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## The through-mark ledgers -/

/-- **Reached cap-defect ledger through a mark.**  The live-mass-weighted sum
of the total one-stage Nash defects of the profile's live rows against their
own all-Continue spine caps, over the dates `0, …, m`. -/
def fableSpineReachedCapDefectLedger
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (m : ℕ) : ℝ :=
  ∑ time ∈ Finset.range (m + 1),
    quittingLiveMass reward profile time *
      quittingRootTotalNashDefect reward
        (quittingTerminalSemanticPair reward
          (quittingAllContinueProfileSpine reward profile (time + 1))).2
        (quittingProfileLiveRoot reward profile time)

/-- **Through-mark singleton stage mass.**  Total mass of the singleton
terminal coalitions carried by the dates `0, …, m`. -/
def fableThroughMarkSingletonStageMass
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (m : ℕ) : ℝ :=
  ∑ time ∈ Finset.range (m + 1),
    ∑ who, quittingStageCoalitionMass reward profile time
      (quittingSingletonTerminal who)

/-- **Through-mark literal defect ledger.**  The live-mass-weighted sum of the
total one-stage Nash defects of the live rows against the *prescribed*
coordinate of their own all-Continue spine tails. -/
def fableThroughMarkLiteralDefectLedger
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (m : ℕ) : ℝ :=
  ∑ time ∈ Finset.range (m + 1),
    quittingLiveMass reward profile time *
      (∑ who, quittingRootCoordinateNashDefect reward
        (quittingTerminalSemanticPair reward
          (quittingAllContinueProfileSpine reward profile (time + 1))).1
        (quittingProfileLiveRoot reward profile time) who)

theorem fableSpineReachedCapDefectLedger_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (m : ℕ) :
    fableSpineReachedCapDefectLedger reward profile m =
      ∑ time ∈ Finset.range (m + 1),
        quittingLiveMass reward profile time *
          quittingRootTotalNashDefect reward
            (quittingTerminalSemanticPair reward
              (quittingAllContinueProfileSpine reward profile (time + 1))).2
            (quittingProfileLiveRoot reward profile time) := rfl

theorem fableThroughMarkSingletonStageMass_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (m : ℕ) :
    fableThroughMarkSingletonStageMass reward profile m =
      ∑ time ∈ Finset.range (m + 1),
        ∑ who, quittingStageCoalitionMass reward profile time
          (quittingSingletonTerminal who) := rfl

theorem fableThroughMarkLiteralDefectLedger_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (m : ℕ) :
    fableThroughMarkLiteralDefectLedger reward profile m =
      ∑ time ∈ Finset.range (m + 1),
        quittingLiveMass reward profile time *
          (∑ who, quittingRootCoordinateNashDefect reward
            (quittingTerminalSemanticPair reward
              (quittingAllContinueProfileSpine reward profile (time + 1))).1
            (quittingProfileLiveRoot reward profile time) who) := rfl

/-! ## The summed spine ledger -/

/-- The directed-transport ledger of the all-Continue spine, summed over
players: total semantic debt of a profile is the live-mass-weighted sum of the
total one-stage Nash defects of its live rows before the cutoff, plus the
live-mass-weighted total debt of the spine tail at the cutoff. -/
private theorem fable_debtSum_eq_sum_liveMass_totalDefect_add_tail
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (cutoff : ℕ) :
    quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward profile) =
      (∑ time ∈ Finset.range cutoff,
          quittingLiveMass reward profile time *
            quittingRootTotalNashDefect reward
              (quittingTerminalSemanticPair reward
                (quittingAllContinueProfileSpine reward profile (time + 1))).2
              (quittingProfileLiveRoot reward profile time)) +
        quittingLiveMass reward profile cutoff *
          quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPair reward
              (quittingAllContinueProfileSpine reward profile cutoff)) := by
  have hweight :=
    reachedHistoryWeight_stationaryContinueMass_eq_quittingLiveMass
      reward profile
  have hledger : ∀ who : ι,
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward profile) who =
        (∑ time ∈ Finset.range cutoff,
            reachedHistoryWeight
                (fun stage => quittingStationaryContinueMass
                  (quittingProfileLiveRoot reward profile stage)) time *
              quittingRootCoordinateNashDefect reward
                (quittingTerminalSemanticPair reward
                  (quittingAllContinueProfileSpine reward profile
                    (time + 1))).2
                (quittingProfileLiveRoot reward profile time) who) +
          reachedHistoryWeight
              (fun stage => quittingStationaryContinueMass
                (quittingProfileLiveRoot reward profile stage)) cutoff *
            quittingTerminalSemanticDebt
              (quittingTerminalSemanticPair reward
                (quittingAllContinueProfileSpine reward profile cutoff)) who :=
    fun who => (QuittingTerminalSemanticPrefixChain.ofProfile
      (reward := reward) profile).debt_zero_eq_sum_reached_defect_add_tail
      who cutoff
  simp only [hweight] at hledger
  unfold quittingTerminalSemanticDebtSum
  simp only [hledger]
  rw [Finset.sum_add_distrib]
  congr 1
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun time _ => ?_
    simp only [quittingRootTotalNashDefect, Finset.mul_sum]
  · rw [Finset.mul_sum]

/-- The through-mark ledger is the profile's own total semantic debt minus the
survival-weighted debt of its post-mark spine tail. -/
private theorem fable_ledger_eq_debtSum_sub_survival_mul_tail
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (m : ℕ) :
    fableSpineReachedCapDefectLedger reward profile m =
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward profile) -
        quittingLiveMass reward profile (m + 1) *
          quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPair reward
              (quittingAllContinueProfileSpine reward profile (m + 1))) := by
  have hledger :=
    fable_debtSum_eq_sum_liveMass_totalDefect_add_tail reward profile (m + 1)
  rw [fableSpineReachedCapDefectLedger_eq]
  linarith

/-! ## Adapter 1b: the charge-normalized moat -/

/-- **Charge-normalized moat.**  Let `source` attain the minimum total
semantic debt over the semantic carrier.  For every profile and every mark,
the reached cap-defect ledger through the mark is at least the absorption
factor `1 - S` times the minimum debt, minus the post-mark spine tail's own
debt excess over that minimum.

No tightness, reward bound, or limiting hypothesis is used: the statement is
the summed spine ledger read against global minimality alone.  It is the
defect-per-absorption rate at scale the minimum debt. -/
theorem fable_throughMark_ledger_ge_absorption_mul_minimum
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source : QuittingTerminalSemanticPair ι)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum source ≤
        quittingTerminalSemanticDebtSum candidate)
    (profile : (quittingGame reward).BehaviorProfile) (m : ℕ) :
    (1 - quittingLiveMass reward profile (m + 1)) *
          quittingTerminalSemanticDebtSum source -
        (quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPair reward
              (quittingAllContinueProfileSpine reward profile (m + 1))) -
          quittingTerminalSemanticDebtSum source) ≤
      fableSpineReachedCapDefectLedger reward profile m := by
  have hledger := fable_ledger_eq_debtSum_sub_survival_mul_tail reward profile m
  have hwhole := hminimum (quittingTerminalSemanticPair reward profile)
    (quittingTerminalSemanticPair_mem_carrier reward profile)
  have htail := hminimum
    (quittingTerminalSemanticPair reward
      (quittingAllContinueProfileSpine reward profile (m + 1)))
    (quittingTerminalSemanticPair_mem_carrier reward
      (quittingAllContinueProfileSpine reward profile (m + 1)))
  have hle := quittingLiveMass_le_one reward profile (m + 1)
  have hslack :
      0 ≤ (1 - quittingLiveMass reward profile (m + 1)) *
        (quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPair reward
              (quittingAllContinueProfileSpine reward profile (m + 1))) -
          quittingTerminalSemanticDebtSum source) :=
    mul_nonneg (by linarith) (by linarith)
  rw [hledger]
  nlinarith [hslack]

/-! ## Adapter 1a: the eventual floor-to-defect -/

/-- **Eventual through-mark ledger floor under limit tightness.**  Under the
hypotheses of the eventual pre-mark absorption floor — a coordinate whose
prescribed value converges to its solo quitting reward, and post-mark spine
tail debts converging to the minimum debt `D` — for every positive slack the
reached cap-defect ledger through the mark eventually exceeds
`((gamma - sigma) / (2 * M + gamma)) * D` minus that slack.

The absorption factor is supplied by the pre-mark opponent survival ceiling,
transferred to the live mass by the per-date Continue-mass comparison; the
slack absorbs the tail's residual debt excess.  The conclusion is genuinely
eventual and carries no rate. -/
theorem fable_limitTight_throughMark_ledger_eventual_floor
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) {M : ℝ}
    (hreward : ∀ S player, |reward S player| ≤ M)
    (source : QuittingTerminalSemanticPair ι)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum source ≤
        quittingTerminalSemanticDebtSum candidate)
    (profile : ℕ → (quittingGame reward).BehaviorProfile) (mark : ℕ → ℕ)
    (who : ι)
    (hcap : Filter.Tendsto
      (fun n => (quittingTerminalSemanticPair reward (profile n)).2 who)
      Filter.atTop (nhds (reward (quittingSingletonTerminal who) who)))
    (htail : Filter.Tendsto
      (fun n => quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward
          (quittingAllContinueProfileSpine reward (profile n) (mark n + 1))))
      Filter.atTop (nhds (quittingTerminalSemanticDebtSum source)))
    {gamma sigma : ℝ} (hgamma : 0 < gamma)
    (hgammaD : gamma < quittingTerminalSemanticDebtSum source)
    (hsigma : 0 < sigma) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ n in Filter.atTop,
      ((gamma - sigma) / (2 * M + gamma)) *
            quittingTerminalSemanticDebtSum source - epsilon ≤
        fableSpineReachedCapDefectLedger reward (profile n) (mark n) := by
  have hM : (0 : ℝ) ≤ M :=
    (abs_nonneg _).trans (hreward (quittingSingletonTerminal who) who)
  have hden : (0 : ℝ) < 2 * M + gamma := by linarith
  have hDpos : 0 < quittingTerminalSemanticDebtSum source := by linarith
  have hratio :
      (gamma - sigma) / (2 * M + gamma) =
        1 - (2 * M + sigma) / (2 * M + gamma) := by
    field_simp
    ring
  have hfloor := fable_limitTight_premark_opponentAbsorption_eventual_floor
    reward hreward source hminimum profile mark who hcap htail hgamma hgammaD
    hsigma
  have hnear : ∀ᶠ n in Filter.atTop,
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward
            (quittingAllContinueProfileSpine reward (profile n)
              (mark n + 1))) ≤
        quittingTerminalSemanticDebtSum source + epsilon :=
    ((tendsto_order.1 htail).2
      (quittingTerminalSemanticDebtSum source + epsilon)
      (by linarith)).mono fun n hn => hn.le
  filter_upwards [hfloor, hnear] with n hproduct hexcess
  have hsurvival :
      quittingLiveMass reward (profile n) (mark n + 1) ≤
        (2 * M + sigma) / (2 * M + gamma) :=
    (fable_liveMass_le_liveWord_opponentSurvival reward (profile n) who
      (mark n)).trans hproduct
  have hmoat := fable_throughMark_ledger_ge_absorption_mul_minimum reward source
    hminimum (profile n) (mark n)
  have hgap :
      (1 - (2 * M + sigma) / (2 * M + gamma)) *
          quittingTerminalSemanticDebtSum source ≤
        (1 - quittingLiveMass reward (profile n) (mark n + 1)) *
          quittingTerminalSemanticDebtSum source :=
    mul_le_mul_of_nonneg_right (by linarith) hDpos.le
  rw [hratio]
  linarith

/-! ## Adapter 2: the exact-stack no-go -/

/-- **Exact-stack no-go.**  Let `source` attain the positive minimum total
semantic debt `D` over the semantic carrier, and let a base profile have pair
debt at most `D + e`.  Then every exact cap--Nash root word over that base has
joint survival product at least `D / (D + e)`, so its total absorption is at
most `e / (D + e)`.

Exact cap--Nash prefixing scales total debt by the word's joint survival, and
the scaled debt is still a carrier value, so minimality pins the product from
below.  Exactification over near-minimum tails therefore cannot retain
absorption. -/
theorem fable_exactStack_absorption_le_excess_ratio
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source : QuittingTerminalSemanticPair ι)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum source ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpos : 0 < quittingTerminalSemanticDebtSum source)
    (base : (quittingGame reward).BehaviorProfile) {e : ℝ}
    (hbase : quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward base) ≤
      quittingTerminalSemanticDebtSum source + e)
    (roots : List (ι → PMF Bool))
    (hstack : IsQuittingCapNashRootStack reward roots base) :
    quittingTerminalSemanticDebtSum source /
          (quittingTerminalSemanticDebtSum source + e) ≤
        quittingCapNashStackContinueProduct roots ∧
      1 - quittingCapNashStackContinueProduct roots ≤
        e / (quittingTerminalSemanticDebtSum source + e) := by
  have hbaseMin := hminimum (quittingTerminalSemanticPair reward base)
    (quittingTerminalSemanticPair_mem_carrier reward base)
  have hexcess : 0 ≤ e := by linarith
  have htotal : 0 < quittingTerminalSemanticDebtSum source + e := by linarith
  have hscaling :
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward
            (quittingLiteralRootStackProfile reward roots base)) =
        quittingCapNashStackContinueProduct roots *
          quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPair reward base) := by
    rw [← quittingTerminalDebtSum_eq_terminalSemanticDebtSum,
      ← quittingTerminalDebtSum_eq_terminalSemanticDebtSum]
    exact quittingTerminalDebtSum_capNashRootStack_eq
      (reward := reward) roots base hstack
  have hstackMin := hminimum
    (quittingTerminalSemanticPair reward
      (quittingLiteralRootStackProfile reward roots base))
    (quittingTerminalSemanticPair_mem_carrier reward
      (quittingLiteralRootStackProfile reward roots base))
  rw [hscaling] at hstackMin
  have hkey : quittingTerminalSemanticDebtSum source ≤
      quittingCapNashStackContinueProduct roots *
        (quittingTerminalSemanticDebtSum source + e) := by
    refine hstackMin.trans ?_
    exact mul_le_mul_of_nonneg_left hbase
      (quittingCapNashStackContinueProduct_nonneg roots)
  refine ⟨(div_le_iff₀ htotal).mpr ?_, (le_div_iff₀ htotal).mpr ?_⟩
  · linarith
  · nlinarith [hkey]

/-! ## Adapter 3: the option-budget split -/

/-- The exact singleton coalition mass of a product root is the own-Quit
option coefficient: the opponents' joint Continue mass times the player's own
Quit probability. -/
private theorem fable_rootCoalitionMass_singleton_eq_optionBudget
    (root : ι → PMF Bool) (who : ι) :
    quittingRootCoalitionMass root {who} =
      quittingRootOpponentContinueMass root who * (root who true).toReal := by
  classical
  have hopponent :
      quittingRootOpponentContinueMass root who =
        ∏ other ∈ Finset.univ.erase who, (root other false).toReal := by
    rw [quittingRootOpponentContinueMass,
      quittingStationaryContinueMass_eq_prod_continueProbability,
      ← Finset.mul_prod_erase Finset.univ
        (fun player =>
          ((Function.update root who (PMF.pure false)) player false).toReal)
        (Finset.mem_univ who), Function.update_self]
    simp only [PMF.pure_apply, if_true, ENNReal.toReal_one, one_mul]
    exact Finset.prod_congr rfl fun other hother => by
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hother)]
  have hcoalition :
      quittingRootCoalitionMass root {who} =
        (root who true).toReal *
          ∏ other ∈ Finset.univ.erase who, (root other false).toReal := by
    rw [quittingRootCoalitionMass, coalitionMass_singleton]
    refine congrArg (fun product => (root who true).toReal * product) ?_
    exact Finset.prod_congr rfl fun other _ =>
      (pmfBool_false_toReal (root other)).symm
  rw [hcoalition, hopponent, mul_comm]

/-- One live row of the through-mark ledger is bounded by its own singleton
stage mass at scale `2 * M`, plus its live-weighted literal defect. -/
private theorem fable_rowLedger_le_singletonMass_add_literalDefect
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) {M : ℝ}
    (hreward : ∀ S player, |reward S player| ≤ M)
    (profile : (quittingGame reward).BehaviorProfile) (time : ℕ) :
    quittingLiveMass reward profile time *
          quittingRootTotalNashDefect reward
            (quittingTerminalSemanticPair reward
              (quittingAllContinueProfileSpine reward profile (time + 1))).2
            (quittingProfileLiveRoot reward profile time) ≤
      2 * M *
          (∑ who, quittingStageCoalitionMass reward profile time
            (quittingSingletonTerminal who)) +
        quittingLiveMass reward profile time *
          (∑ who, quittingRootCoordinateNashDefect reward
            (quittingTerminalSemanticPair reward
              (quittingAllContinueProfileSpine reward profile (time + 1))).1
            (quittingProfileLiveRoot reward profile time) who) := by
  classical
  set tail := quittingAllContinueProfileSpine reward profile (time + 1)
    with htaildef
  set pair := quittingTerminalSemanticPair reward tail with hpairdef
  set root := quittingProfileLiveRoot reward profile time with hrootdef
  set live := quittingLiveMass reward profile time with hlivedef
  have hpairMem : pair ∈ quittingTerminalSemanticCarrier reward :=
    quittingTerminalSemanticPair_mem_carrier reward tail
  have hrow : ∀ who : ι,
      quittingRootCoordinateNashDefect reward pair.2 root who ≤
        quittingRootCoordinateNashDefect reward pair.1 root who +
          2 * M * quittingRootCoalitionMass root {who} := by
    intro who
    have hbudget := quittingRootCapDefect_sub_quitOptionBudget_le_literalDefect
      reward pair root who hpairMem
    have hcoefficient : 0 ≤ quittingRootOpponentContinueMass root who *
        (root who true).toReal :=
      mul_nonneg (quittingRootOpponentContinueMass_nonneg root who)
        ENNReal.toReal_nonneg
    have hdebt := quittingTerminalSemanticDebt_mem_Icc_zero_two_mul
      reward tail who hreward
    have hcap : quittingTerminalSemanticDebt pair who ≤ 2 * M := hdebt.2
    have hscaled : quittingRootOpponentContinueMass root who *
          (root who true).toReal * quittingTerminalSemanticDebt pair who ≤
        quittingRootOpponentContinueMass root who *
          (root who true).toReal * (2 * M) :=
      mul_le_mul_of_nonneg_left hcap hcoefficient
    rw [fable_rootCoalitionMass_singleton_eq_optionBudget root who]
    linarith
  have hsum :
      quittingRootTotalNashDefect reward pair.2 root ≤
        (∑ who, quittingRootCoordinateNashDefect reward pair.1 root who) +
          2 * M * ∑ who, quittingRootCoalitionMass root {who} := by
    rw [quittingRootTotalNashDefect, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun who _ => hrow who
  have hstage : ∀ who : ι,
      quittingStageCoalitionMass reward profile time
          (quittingSingletonTerminal who) =
        live * quittingRootCoalitionMass root {who} :=
    fun who => quittingStageCoalitionMass_eq_liveMass_mul_rootCoalitionMass
      reward profile time (quittingSingletonTerminal who)
  have hstageSum :
      (∑ who, quittingStageCoalitionMass reward profile time
          (quittingSingletonTerminal who)) =
        live * ∑ who, quittingRootCoalitionMass root {who} := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun who _ => hstage who
  rw [hstageSum]
  calc
    live * quittingRootTotalNashDefect reward pair.2 root ≤
        live * ((∑ who, quittingRootCoordinateNashDefect reward pair.1 root who) +
          2 * M * ∑ who, quittingRootCoalitionMass root {who}) :=
      mul_le_mul_of_nonneg_left hsum
        (quittingLiveMass_nonneg reward profile time)
    _ = 2 * M * (live * ∑ who, quittingRootCoalitionMass root {who}) +
          live * ∑ who, quittingRootCoordinateNashDefect reward pair.1 root who := by
      ring

/-- **Option-budget split of the through-mark ledger.**  Under a uniform
reward bound `M`, the reached cap-defect ledger through a mark is at most
`2 * M` times the through-mark singleton stage mass plus the through-mark
literal defect ledger.

Each row's cap defect exceeds its literal prescribed-side defect only by the
precise own-Quit option budget, whose coefficient is the root's singleton
coalition mass and whose debt factor is at most `2 * M`; live weighting turns
that coefficient into the singleton stage mass. -/
theorem fable_throughMark_ledger_le_singletonMass_add_literalDefect
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) {M : ℝ}
    (hreward : ∀ S player, |reward S player| ≤ M)
    (profile : (quittingGame reward).BehaviorProfile) (m : ℕ) :
    fableSpineReachedCapDefectLedger reward profile m ≤
      2 * M * fableThroughMarkSingletonStageMass reward profile m +
        fableThroughMarkLiteralDefectLedger reward profile m := by
  rw [fableSpineReachedCapDefectLedger_eq,
    fableThroughMarkSingletonStageMass_eq,
    fableThroughMarkLiteralDefectLedger_eq, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun time _ =>
    fable_rowLedger_le_singletonMass_add_literalDefect reward hreward profile time

/-- **The singleton-or-literal split.**  Any lower bound `c` on the reached
cap-defect ledger through a mark is carried by one of the two summands of the
option-budget split: either the through-mark singleton stage mass is at least
`c / (4 * M)`, or the through-mark literal defect ledger is at least `c / 2`.

Each summand of the literal ledger is an actual one-date best-endpoint
deviation gain against the prescribed spine tail, so the second branch is
genuine endpoint work rather than a cap artifact. -/
theorem fable_throughMark_singleton_or_literal_split
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) {M : ℝ} (hM : 0 < M)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (profile : (quittingGame reward).BehaviorProfile) (m : ℕ) {c : ℝ}
    (hc : c ≤ fableSpineReachedCapDefectLedger reward profile m) :
    c / (4 * M) ≤ fableThroughMarkSingletonStageMass reward profile m ∨
      c / 2 ≤ fableThroughMarkLiteralDefectLedger reward profile m := by
  rcases le_or_gt (c / (4 * M))
      (fableThroughMarkSingletonStageMass reward profile m) with hsing | hsing
  · exact Or.inl hsing
  rcases le_or_gt (c / 2)
      (fableThroughMarkLiteralDefectLedger reward profile m) with hlit | hlit
  · exact Or.inr hlit
  exfalso
  have hsplit := fable_throughMark_ledger_le_singletonMass_add_literalDefect
    reward hreward profile m
  have hMne : M ≠ 0 := ne_of_gt hM
  have hbudget : 2 * M * (c / (4 * M)) = c / 2 := by
    field_simp
    ring
  have hscaled :
      2 * M * fableThroughMarkSingletonStageMass reward profile m <
        2 * M * (c / (4 * M)) :=
    mul_lt_mul_of_pos_left hsing (by linarith)
  rw [hbudget] at hscaled
  linarith

end GameTheory
