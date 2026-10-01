import UniformEquilibrium.Quitting.Paths.ExecutableRationalChargedSourceStep
import UniformEquilibrium.Quitting.Paths.ExecutableRationalPayoffDebtThresholdBlock

/-! # Executable weak-subset macrosteps and fixed-working-level stages

Each renewal evaluates the literal rational source word anew. A failed column
threshold and its immediately forced charged row form one macrostep. Continuing
macrosteps spend a uniform positive debt amount and preserve the exact old tail.
A positive-column exit is instead a fresh word at the original final accuracy.
The fixed-level stage uses a rational-ceiling fuel and absorbing Nat recursion.
Real logarithms bound dates only; they are never used to produce runtime data.
This is the fixed-level bound, not the separate dyadic absolute-constant bound.
-/

namespace GameTheory

variable {players : ℕ}

/-- Only actual rational word data are carried between renewals. -/
inductive RationalWeakSubsetOutcome (players : ℕ) where
  | phaseDone (word : List (RationalQuittingRoot players))
  | globalExit (owner : Fin players) (word : List (RationalQuittingRoot players))
  | «continue» (word : List (RationalQuittingRoot players))

def RationalWeakSubsetOutcome.word :
    RationalWeakSubsetOutcome players → List (RationalQuittingRoot players)
  | .phaseDone word => word
  | .globalExit _ word => word
  | .«continue» word => word

/-- Uniform debt expenditure of a continuing macrostep, at fixed working accuracy. -/
def rationalWeakSubsetDebtDrop (M working : ℚ) : ℚ :=
  ((working / 8) / (4 * M + working / 8)) * (working / 8) / 8

theorem rationalWeakSubsetDebtDrop_pos {M working : ℚ}
    (hM : 0 < M) (hworking : 0 < working) :
    0 < rationalWeakSubsetDebtDrop M working := by
  unfold rationalWeakSubsetDebtDrop
  positivity

/-- The printed solo-threshold bound. It occurs only in proof specifications. -/
noncomputable def rationalWeakSubsetMacrostepDateBound (M working : ℚ) : ℕ :=
  Nat.ceil ((16 * (M : ℝ) / (working : ℝ)) *
    Real.log (8 * (M : ℝ) / (working : ℝ))) + 1

theorem rationalWeakSubset_players_pos
    (reward : RationalQuittingReward players) (owners : Finset (Fin players))
    (hWE : RationalQuittingFiniteWordOwnerExclusionOn reward owners) :
    0 < players := by
  obtain ⟨owner, _, _⟩ := hWE []
  exact lt_of_le_of_lt (Nat.zero_le owner.val) owner.isLt

instance rationalQuittingPositiveSingletonColumnAt_decidable
    (reward : RationalQuittingReward players) (owner : Fin players) (working : ℚ) :
    Decidable (RationalQuittingPositiveSingletonColumnAt reward owner working) := by
  unfold RationalQuittingPositiveSingletonColumnAt
  infer_instance

private theorem concentrated_of_not_charged
    (reward : RationalQuittingReward players) (old : List (RationalQuittingRoot players))
    (working : ℚ) (hdebt : working ≤ rationalFiniteSourceDebt reward old)
    (hcharged : ¬rationalFiniteSourceChargedMargin reward old working) :
    RationalQuittingConcentratedPayoffSource reward old working := by
  refine ⟨hdebt, ?_⟩
  intro who
  apply lt_of_not_ge
  intro hle
  exact hcharged ⟨who, hle⟩

private theorem threshold_rational_debt_and_endpoint
    (reward : RationalQuittingReward players) (old : List (RationalQuittingRoot players))
    (owner : Fin players) (M working : ℚ)
    (hM : 0 < M) (hworking : 0 < working) (hworkingM : working ≤ M)
    (hreward : ∀ terminal who, |reward terminal who| ≤ M)
    (hsource : RationalQuittingConcentratedPayoffSource reward old working)
    (howner : (rationalQuittingFiniteWordSemanticPair reward old).1 owner ≤
      reward (quittingSingletonTerminal owner) owner)
    (hcolumn : ¬RationalQuittingPositiveSingletonColumnAt reward owner working) :
    let reached := executableRationalPayoffDebtThresholdWord reward old owner M working
      hM hworking hworkingM hreward hsource howner hcolumn
    rationalFiniteSourceDebt reward reached ≤ rationalFiniteSourceDebt reward old ∧
      (rationalFiniteSourceDebt reward reached < working ∨
        rationalFiniteSourceChargedMargin reward reached working) := by
  dsimp only
  let reached := executableRationalPayoffDebtThresholdWord reward old owner M working
    hM hworking hworkingM hreward hsource howner hcolumn
  have hledger := (executableRationalPayoffDebtThresholdWord_ledger
    reward old owner M working hM hworking hworkingM hreward hsource howner hcolumn).2.2.1
  rw [quittingTerminalSemanticDebtSum_rationalFiniteWord_eq_cast,
    quittingTerminalSemanticDebtSum_rational_eq_cast] at hledger
  have hnonincrease : rationalFiniteSourceDebt reward reached ≤
      rationalFiniteSourceDebt reward old := by exact_mod_cast hledger
  refine ⟨hnonincrease, ?_⟩
  have hendpoint := executableRationalPayoffDebtThresholdWord_endpoint
    reward old owner M working hM hworking hworkingM hreward hsource howner hcolumn
  dsimp only at hendpoint
  rw [quittingTerminalSemanticDebtSum_rationalFiniteWord_eq_cast,
    quittingTerminalSemanticPair_rationalFiniteWord_eq_cast] at hendpoint
  rcases hendpoint with hsmall | ⟨who, _, _, hmargin⟩
  · left
    exact_mod_cast hsmall
  · right
    refine ⟨who, ?_⟩
    change ((rationalQuittingFiniteWordSemanticPair reward reached).2 who : ℝ) -
      (reward (quittingSingletonTerminal who) who : ℝ) <
      (rationalFiniteSourceDebt reward reached : ℝ) - (working : ℝ) / 8 at hmargin
    have hrational :
        (rationalQuittingFiniteWordSemanticPair reward reached).2 who -
          reward (quittingSingletonTerminal who) who <
        rationalFiniteSourceDebt reward reached - working / 8 := by exact_mod_cast hmargin
    exact hrational.le

private theorem threshold_charged_of_not_small
    (reward : RationalQuittingReward players) (old : List (RationalQuittingRoot players))
    (owner : Fin players) (M working : ℚ)
    (hM : 0 < M) (hworking : 0 < working) (hworkingM : working ≤ M)
    (hreward : ∀ terminal who, |reward terminal who| ≤ M)
    (hsource : RationalQuittingConcentratedPayoffSource reward old working)
    (howner : (rationalQuittingFiniteWordSemanticPair reward old).1 owner ≤
      reward (quittingSingletonTerminal owner) owner)
    (hcolumn : ¬RationalQuittingPositiveSingletonColumnAt reward owner working)
    (hnotsmall : ¬rationalFiniteSourceDebt reward
      (executableRationalPayoffDebtThresholdWord reward old owner M working
        hM hworking hworkingM hreward hsource howner hcolumn) < working) :
    rationalFiniteSourceChargedMargin reward
      (executableRationalPayoffDebtThresholdWord reward old owner M working
        hM hworking hworkingM hreward hsource howner hcolumn) working :=
  ((threshold_rational_debt_and_endpoint reward old owner M working
    hM hworking hworkingM hreward hsource howner hcolumn).2).resolve_left hnotsmall

section Source

variable (reward : RationalQuittingReward players) (owners : Finset (Fin players))
  (hWE : RationalQuittingFiniteWordOwnerExclusionOn reward owners)
  (M working accuracy : ℚ) (hworking : 0 < working)
  (hworkingM : working ≤ M) (haccuracy : 0 < accuracy)
  (hreward : ∀ terminal who, |reward terminal who| ≤ M)

local notation "hM" => lt_of_lt_of_le hworking hworkingM
local notation "debt" => rationalFiniteSourceDebt reward
local notation "drop" => rationalWeakSubsetDebtDrop M working
local notation "dateBound" => rationalWeakSubsetMacrostepDateBound M working

/-- The actual finite rational dispatch, including the forced charged row after
a nonterminal payoff threshold. Its fresh exit always uses ORIGINAL accuracy. -/
def executableRationalWeakSubsetMacrostep (old : List (RationalQuittingRoot players)) :
    RationalWeakSubsetOutcome players :=
  if hsmall : debt old < working then .phaseDone old
  else if hcharged : rationalFiniteSourceChargedMargin reward old working then
    .«continue» (rationalFiniteSourceChargedWord reward old M working hM hworking hcharged)
  else
    let concentrated := concentrated_of_not_charged reward old working
      (le_of_not_gt hsmall) hcharged
    let owner := rationalQuittingFiniteWordExcludedOwnerOn reward owners hWE old
    if hcolumn : RationalQuittingPositiveSingletonColumnAt reward owner working then
      .globalExit owner (rationalPositiveColumnWorkingWord
        owner M working hM hworking hworkingM accuracy haccuracy)
    else
      let ownerBound := rationalQuittingFiniteWordExcludedOwnerOn_payoff_le
        reward owners hWE old
      let reached := executableRationalPayoffDebtThresholdWord reward old owner M working
        hM hworking hworkingM hreward concentrated ownerBound hcolumn
      if hhit : debt reached < working then .phaseDone reached
      else .«continue» (rationalFiniteSourceChargedWord reward reached M working hM hworking
        (threshold_charged_of_not_small reward old owner M working hM hworking hworkingM
          hreward concentrated ownerBound hcolumn hhit))

local notation "macrostep" => executableRationalWeakSubsetMacrostep reward owners hWE
  M working accuracy hworking hworkingM haccuracy hreward

/-- Meaning of a FRESH positive-column exit, including its literal raw target
and separate logarithmic cutoff, with no old-tail or cross-exit debt claim. -/
def RationalWeakSubsetGlobalExitSpec (owner : Fin players)
    (word : List (RationalQuittingRoot players)) : Prop :=
  owner ∈ owners ∧
    RationalQuittingPositiveSingletonColumnAt reward owner working ∧
    word = rationalPositiveColumnWorkingWord
      owner M working hM hworking hworkingM accuracy haccuracy ∧
    debt word ≤ accuracy / 2 ∧
    (∀ who, |quittingTerminalPayoff (rationalQuittingRewardToReal reward)
      (quittingLiteralRootStackProfile (rationalQuittingRewardToReal reward)
        (word.map RationalQuittingRoot.toPMF)
        (quittingAlwaysContinueProfile (rationalQuittingRewardToReal reward))) who -
      (reward (quittingSingletonTerminal owner) who : ℝ)| ≤ (accuracy : ℝ) / 2) ∧
    (word.length : ℝ) ≤
      1 + Real.log (1 / (rationalSoloExitTolerance players M accuracy : ℝ)) /
        (-Real.log (1 - (rationalPositiveColumnWorkingHazard M working : ℝ)))

local notation "exitSpec" => RationalWeakSubsetGlobalExitSpec
  reward owners M working accuracy hworking hworkingM haccuracy

/-- The macrostep specification has no supplied cap, selected root or stopping rank. -/
noncomputable def RationalWeakSubsetMacrostepSpec
    (old : List (RationalQuittingRoot players)) (outcome : RationalWeakSubsetOutcome players) :
    Prop :=
  match outcome with
  | .phaseDone word => ∃ added, word = added ++ old ∧ added.length ≤ dateBound ∧
      debt word < working ∧ debt word ≤ debt old
  | .globalExit owner word => exitSpec owner word
  | .«continue» word => ∃ added, word = added ++ old ∧ added.length ≤ dateBound ∧
      debt word ≤ debt old - drop

local notation "stepSpec" => RationalWeakSubsetMacrostepSpec
  reward owners M working accuracy hworking hworkingM haccuracy

include hreward in
private theorem charged_prefix_spec
    (old : List (RationalQuittingRoot players))
    (hdebt : working ≤ debt old)
    (hcharged : rationalFiniteSourceChargedMargin reward old working) :
    ∃ added,
      rationalFiniteSourceChargedWord reward old M working hM hworking hcharged = added ++ old ∧
      added.length ≤ dateBound ∧
      debt (rationalFiniteSourceChargedWord reward old M working hM hworking hcharged) ≤
        debt old - drop := by
  have hspec := rationalFiniteSourceChargedWord_spec
    reward old M working hM hworking hreward hdebt hcharged
  refine ⟨[rationalFiniteSourceChargedRoot reward old M working hM hworking hcharged],
    rfl, ?_, hspec.2.2.2.1⟩
  change 1 ≤ Nat.ceil ((16 * (M : ℝ) / (working : ℝ)) *
    Real.log (8 * (M : ℝ) / (working : ℝ))) + 1
  exact Nat.succ_le_succ (Nat.zero_le _)

/-- Each continuing macrostep spends the SAME positive amount. A threshold
without this forced charged row is never counted as a continuing macrostep. -/
theorem executableRationalWeakSubsetMacrostep_spec
    (hsign : ∀ owner ∈ owners, 0 ≤ reward (quittingSingletonTerminal owner) owner)
    (old : List (RationalQuittingRoot players)) :
    stepSpec old (macrostep old) := by
  unfold executableRationalWeakSubsetMacrostep
  dsimp only
  split_ifs with hsmall hcharged hcolumn hhit
  · exact ⟨[], by simp, by simp,
      hsmall, le_rfl⟩
  · exact charged_prefix_spec reward M working hworking hworkingM hreward old
      (le_of_not_gt hsmall) hcharged
  · dsimp only [RationalWeakSubsetMacrostepSpec, RationalWeakSubsetGlobalExitSpec]
    let owner := rationalQuittingFiniteWordExcludedOwnerOn reward owners hWE old
    have hmem := rationalQuittingFiniteWordExcludedOwnerOn_mem reward owners hWE old
    have hdebt := rationalPositiveColumnWorkingWord_debtSum_le
      reward owner M working hM hworking hworkingM hreward (hsign owner hmem) hcolumn
      accuracy haccuracy
    dsimp only at hdebt
    rw [quittingTerminalSemanticDebtSum_rationalFiniteWord_eq_cast] at hdebt
    have hrational : debt (rationalPositiveColumnWorkingWord owner M working
        hM hworking hworkingM accuracy haccuracy) ≤ accuracy / 2 := by
      exact_mod_cast hdebt
    exact ⟨hmem, hcolumn, rfl, hrational,
      rationalPositiveColumnWorkingWord_delivery_le
        reward owner M working hM hworking hworkingM hreward accuracy haccuracy,
      rationalPositiveColumnWorkingWord_length_le_log
        owner M working hM hworking hworkingM accuracy haccuracy⟩
  · let owner := rationalQuittingFiniteWordExcludedOwnerOn reward owners hWE old
    let concentrated := concentrated_of_not_charged reward old working
      (le_of_not_gt hsmall) hcharged
    let ownerBound := rationalQuittingFiniteWordExcludedOwnerOn_payoff_le
      reward owners hWE old
    let index := executableRationalPayoffDebtThresholdIndex reward old owner M working
      hM hworking hworkingM hreward concentrated ownerBound hcolumn
    have hlength := executableRationalPayoffDebtThresholdIndex_le_log
      reward old owner M working hM hworking hworkingM hreward concentrated ownerBound hcolumn
    have hledger := (threshold_rational_debt_and_endpoint reward old owner M working
      hM hworking hworkingM hreward concentrated ownerBound hcolumn).1
    refine ⟨List.replicate index
      (rationalQuittingSoloRoot owner (rationalPositiveColumnWorkingHazard M working)),
      rfl, ?_, hhit, hledger⟩
    simp only [List.length_replicate]
    exact hlength.trans (Nat.le_succ _)
  · let owner := rationalQuittingFiniteWordExcludedOwnerOn reward owners hWE old
    let concentrated := concentrated_of_not_charged reward old working
      (le_of_not_gt hsmall) hcharged
    let ownerBound := rationalQuittingFiniteWordExcludedOwnerOn_payoff_le
      reward owners hWE old
    let index := executableRationalPayoffDebtThresholdIndex reward old owner M working
      hM hworking hworkingM hreward concentrated ownerBound hcolumn
    let reached := executableRationalPayoffDebtThresholdWord reward old owner M working
      hM hworking hworkingM hreward concentrated ownerBound hcolumn
    let charged := threshold_charged_of_not_small reward old owner M working
      hM hworking hworkingM hreward concentrated ownerBound hcolumn hhit
    let root := rationalFiniteSourceChargedRoot reward reached M working hM hworking charged
    have hledger := (threshold_rational_debt_and_endpoint reward old owner M working
      hM hworking hworkingM hreward concentrated ownerBound hcolumn).1
    have hdrop := (rationalFiniteSourceChargedWord_spec
      reward reached M working hM hworking hreward (le_of_not_gt hhit) charged).2.2.2.1
    have hlength := executableRationalPayoffDebtThresholdIndex_le_log
      reward old owner M working hM hworking hworkingM hreward concentrated ownerBound hcolumn
    refine ⟨root :: List.replicate index
      (rationalQuittingSoloRoot owner (rationalPositiveColumnWorkingHazard M working)),
      rfl, ?_, ?_⟩
    · simp only [List.length_cons, List.length_replicate]
      exact Nat.add_le_add_right hlength 1
    · exact hdrop.trans (sub_le_sub_right hledger drop)

/-- Absorbing primitive recursion: once complete or globally exited, the exact
selected word and exit owner are kept at every later fuel value. -/
def executableRationalWeakSubsetStageOrbit
    (initial : List (RationalQuittingRoot players)) : ℕ → RationalWeakSubsetOutcome players
  | 0 => .«continue» initial
  | time + 1 =>
      match executableRationalWeakSubsetStageOrbit initial time with
      | .«continue» word => macrostep word
      | .phaseDone word => .phaseDone word
      | .globalExit owner word => .globalExit owner word

local notation "orbit" => executableRationalWeakSubsetStageOrbit reward owners hWE
  M working accuracy hworking hworkingM haccuracy hreward

theorem executableRationalWeakSubsetStageOrbit_phaseDone_add
    (initial word : List (RationalQuittingRoot players)) (time extra : ℕ)
    (hdone : orbit initial time = .phaseDone word) :
    orbit initial (time + extra) = .phaseDone word := by
  induction extra with
  | zero => simpa only [Nat.add_zero] using hdone
  | succ extra ih =>
      rw [Nat.add_succ, executableRationalWeakSubsetStageOrbit, ih]

theorem executableRationalWeakSubsetStageOrbit_globalExit_add
    (initial word : List (RationalQuittingRoot players)) (owner : Fin players) (time extra : ℕ)
    (hexit : orbit initial time = .globalExit owner word) :
    orbit initial (time + extra) = .globalExit owner word := by
  induction extra with
  | zero => simpa only [Nat.add_zero] using hexit
  | succ extra ih =>
      rw [Nat.add_succ, executableRationalWeakSubsetStageOrbit, ih]

/-- Runtime fuel is computed only from the actual rational source debt. -/
def executableRationalWeakSubsetStageFuel
    (initial : List (RationalQuittingRoot players)) : ℕ :=
  Nat.ceil (debt initial / drop) + 1

local notation "fuel" => executableRationalWeakSubsetStageFuel reward M working

/-- No supplied stopping certificate: the finite stage is the primitive orbit
at its computed rational-ceiling fuel. -/
def executableRationalWeakSubsetStage
    (initial : List (RationalQuittingRoot players)) : RationalWeakSubsetOutcome players :=
  orbit initial (fuel initial)

local notation "stage" => executableRationalWeakSubsetStage reward owners hWE
  M working accuracy hworking hworkingM haccuracy hreward

/-- Active stages retain exact tails and additive debt descent. Completed
stages retain those tails; global exits retain their separate fresh-word proof. -/
noncomputable def RationalWeakSubsetStageInvariant
    (initial : List (RationalQuittingRoot players)) (time : ℕ)
    (outcome : RationalWeakSubsetOutcome players) : Prop :=
  match outcome with
  | .«continue» word => ∃ added, word = added ++ initial ∧
      added.length ≤ time * dateBound ∧ debt word ≤ debt initial - (time : ℚ) * drop
  | .phaseDone word => ∃ added, word = added ++ initial ∧
      added.length ≤ time * dateBound ∧ debt word < working ∧ debt word ≤ debt initial
  | .globalExit owner word => exitSpec owner word

local notation "stageInvariant" => RationalWeakSubsetStageInvariant
  reward owners M working accuracy hworking hworkingM haccuracy

theorem executableRationalWeakSubsetStageOrbit_invariant
    (hsign : ∀ owner ∈ owners, 0 ≤ reward (quittingSingletonTerminal owner) owner)
    (initial : List (RationalQuittingRoot players)) (time : ℕ) :
    stageInvariant initial time (orbit initial time) := by
  have hdrop0 := (rationalWeakSubsetDebtDrop_pos hM hworking).le
  induction time with
  | zero =>
      exact ⟨[], by simp, by simp, by simp⟩
  | succ time ih =>
      rw [executableRationalWeakSubsetStageOrbit]
      generalize hout : orbit initial time = previous at ih ⊢
      cases previous with
      | globalExit owner word => exact ih
      | phaseDone word =>
          obtain ⟨added, hword, hlength, hsmall, hdebt⟩ := ih
          exact ⟨added, hword,
            hlength.trans (Nat.mul_le_mul_right dateBound (Nat.le_succ time)),
            hsmall, hdebt⟩
      | «continue» word =>
          obtain ⟨oldPrefix, hword, hlength, hdebt⟩ := ih
          have hstep := executableRationalWeakSubsetMacrostep_spec reward owners hWE
            M working accuracy hworking hworkingM haccuracy hreward hsign word
          change stageInvariant initial (time + 1) (macrostep word)
          generalize hnext : macrostep word = next at hstep ⊢
          cases next with
          | globalExit owner result => exact hstep
          | phaseDone result =>
              obtain ⟨added, hresult, hprefixLength, hsmall, hnonincrease⟩ := hstep
              refine ⟨added ++ oldPrefix, ?_, ?_, hsmall, ?_⟩
              · rw [hresult, hword, List.append_assoc]
              · rw [List.length_append, Nat.succ_mul]
                omega
              · have htime : (0 : ℚ) ≤ (time : ℚ) * drop :=
                  mul_nonneg (Nat.cast_nonneg time) hdrop0
                linarith
          | «continue» result =>
              obtain ⟨added, hresult, hprefixLength, hspent⟩ := hstep
              refine ⟨added ++ oldPrefix, ?_, ?_, ?_⟩
              · rw [hresult, hword, List.append_assoc]
              · rw [List.length_append, Nat.succ_mul]
                omega
              · rw [Nat.cast_succ]
                linarith

/-- The computed fuel cannot end in the active state: a full additive descent
would contradict the canonical nonnegative actual source debt. -/
theorem executableRationalWeakSubsetStage_not_continue
    (hsign : ∀ owner ∈ owners, 0 ≤ reward (quittingSingletonTerminal owner) owner)
    (initial word : List (RationalQuittingRoot players)) :
    stage initial ≠ .«continue» word := by
  intro hactive
  have hinvariant := executableRationalWeakSubsetStageOrbit_invariant reward owners hWE
    M working accuracy hworking hworkingM haccuracy hreward hsign initial (fuel initial)
  change stageInvariant initial (fuel initial) (stage initial) at hinvariant
  rw [hactive] at hinvariant
  obtain ⟨_, _, _, hdebt⟩ := hinvariant
  have hdrop := rationalWeakSubsetDebtDrop_pos hM hworking
  have hceil : debt initial ≤
      (Nat.ceil (debt initial / drop) : ℚ) * drop :=
    (div_le_iff₀ hdrop).mp (Nat.le_ceil (debt initial / drop))
  have hnonnegative := rationalFiniteSourceDebt_nonneg reward word
  have hfuel : (fuel initial : ℚ) = (Nat.ceil (debt initial / drop) : ℚ) + 1 := by
    simp only [executableRationalWeakSubsetStageFuel, Nat.cast_add, Nat.cast_one]
  rw [hfuel] at hdebt
  nlinarith

/-- Fixed-level display (16), for the same literal rational output. A phase
completion is an extension by at most (L+1)(ceil(D_in/Delta)+1) dates. The only
other terminal outcome is the internally produced fresh ORIGINAL-accuracy exit. -/
theorem executableRationalWeakSubsetStage_spec
    (hsign : ∀ owner ∈ owners, 0 ≤ reward (quittingSingletonTerminal owner) owner)
    (initial : List (RationalQuittingRoot players)) :
    match stage initial with
    | .phaseDone word => ∃ added, word = added ++ initial ∧
        added.length ≤ dateBound * (Nat.ceil (debt initial / drop) + 1) ∧
        debt word < working ∧ debt word ≤ debt initial
    | .globalExit owner word => exitSpec owner word
    | .«continue» _ => False := by
  have hinvariant := executableRationalWeakSubsetStageOrbit_invariant reward owners hWE
    M working accuracy hworking hworkingM haccuracy hreward hsign initial (fuel initial)
  change stageInvariant initial (fuel initial) (stage initial) at hinvariant
  generalize hout : stage initial = outcome at hinvariant ⊢
  cases outcome with
  | «continue» word =>
      exact executableRationalWeakSubsetStage_not_continue reward owners hWE
        M working accuracy hworking hworkingM haccuracy hreward hsign initial word hout
  | globalExit owner word => exact hinvariant
  | phaseDone word =>
      obtain ⟨added, hword, hlength, hsmall, hdebt⟩ := hinvariant
      refine ⟨added, hword, ?_, hsmall, hdebt⟩
      simpa only [executableRationalWeakSubsetStageFuel, Nat.mul_comm] using hlength

theorem executableRationalWeakSubsetStage_debt_le
    (hsign : ∀ owner ∈ owners, 0 ≤ reward (quittingSingletonTerminal owner) owner)
    (initial : List (RationalQuittingRoot players)) :
    debt (stage initial).word ≤ max working (accuracy / 2) := by
  have hspec := executableRationalWeakSubsetStage_spec reward owners hWE
    M working accuracy hworking hworkingM haccuracy hreward hsign initial
  generalize hout : stage initial = outcome at hspec ⊢
  cases outcome with
  | «continue» word => exact False.elim hspec
  | phaseDone word => exact hspec.choose_spec.2.2.1.le.trans (le_max_left _ _)
  | globalExit owner word => exact hspec.2.2.2.1.trans (le_max_right _ _)

noncomputable section

/-- The SAME stage word has independent rational date/Never laws and its exact
full semantic pair, including the empty calendar and every behavioral reply. -/
theorem executableRationalWeakSubsetStage_finiteLaws
    (hsign : ∀ owner ∈ owners, 0 ≤ reward (quittingSingletonTerminal owner) owner)
    (initial : List (RationalQuittingRoot players)) :
    let word := (stage initial).word
    ∃ mixed : Fin players → PMF (Option (Fin word.length)),
      (∀ who choice, (mixed who choice).toReal =
        (rationalFiniteClockMass (rationalQuittingFiniteWordSequence word)
          word.length who choice : ℝ)) ∧
      quittingTerminalSemanticPair (rationalQuittingRewardToReal reward)
        (quittingFiniteDeadlineTimingProfile (rationalQuittingRewardToReal reward)
          word.length mixed) =
        (rationalQuittingFiniteWordSemanticPair reward word).toReal ∧
      (quittingGame (rationalQuittingRewardToReal reward)).IsεAsymptoticNash
        (quittingTerminalPayoff (rationalQuittingRewardToReal reward))
        (max (working : ℝ) ((accuracy : ℝ) / 2))
        (quittingFiniteDeadlineTimingProfile (rationalQuittingRewardToReal reward)
          word.length mixed) := by
  dsimp only
  let word := (stage initial).word
  obtain ⟨mixed, hmass, hpair⟩ := exists_rationalQuittingFiniteWordLaws_exact reward word
  refine ⟨mixed, hmass, hpair, ?_⟩
  apply isEpsilonAsymptoticNash_of_terminalSemanticDebtSum_le
  rw [hpair]
  change quittingTerminalSemanticDebtSum
      (rationalQuittingFiniteWordSemanticPair reward word).toReal ≤
    max (working : ℝ) ((accuracy : ℝ) / 2)
  rw [quittingTerminalSemanticDebtSum_rational_eq_cast]
  have hdebt := executableRationalWeakSubsetStage_debt_le reward owners hWE
    M working accuracy hworking hworkingM haccuracy hreward hsign initial
  exact_mod_cast hdebt

end
end Source
end GameTheory
