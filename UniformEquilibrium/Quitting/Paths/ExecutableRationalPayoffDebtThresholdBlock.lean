import UniformEquilibrium.Quitting.Root.RationalPayoffDebtThresholdScan
import UniformEquilibrium.Quitting.Root.RationalFiniteWordSearch
import UniformEquilibrium.Quitting.Paths.ExecutableRationalSelectedOwnerStep
import UniformEquilibrium.Quitting.Paths.RationalPositiveColumnWorkingExit

/-! # The actual rational payoff/debt threshold block

The concentrated branch is tested on the actual finite source payoff/full-cap
pair. The owner is the canonical weak-exclusion scan, not a supplied favorable
root. The new first-hit scan uses PAYOFF thresholds and retains the original
word literally as its tail. A failed positive column is not called preemption.

The working accuracy controls this block. It does not replace a separately
requested final accuracy or claim that this one block alone terminates the
complete weak-subset selector.
-/

namespace GameTheory

variable {players : ℕ}

/-- The actual charged-margin test has failed while total debt is still large. -/
def RationalQuittingConcentratedPayoffSource
    (reward : RationalQuittingReward players)
    (roots : List (RationalQuittingRoot players)) (working : ℚ) : Prop :=
  let source := rationalQuittingFiniteWordSemanticPair reward roots
  working ≤ rationalQuittingSemanticDebtSum source ∧
    ∀ who, rationalQuittingSemanticDebtSum source - working / 8 <
      source.2 who - reward (quittingSingletonTerminal who) who

instance rationalQuittingConcentratedPayoffSource_decidable
    (reward : RationalQuittingReward players)
    (roots : List (RationalQuittingRoot players)) (working : ℚ) :
    Decidable (RationalQuittingConcentratedPayoffSource reward roots working) := by
  unfold RationalQuittingConcentratedPayoffSource
  infer_instance

private theorem workingHazard_charge {M working : ℚ} (hM : 0 < M) :
    4 * M * rationalPositiveColumnWorkingHazard M working = working / 4 := by
  unfold rationalPositiveColumnWorkingHazard
  field_simp [ne_of_gt hM]
  ring

private theorem concentrated_real
    (reward : RationalQuittingReward players)
    (roots : List (RationalQuittingRoot players)) (working : ℚ)
    (hsource : RationalQuittingConcentratedPayoffSource reward roots working) :
    (working : ℝ) ≤ quittingTerminalSemanticDebtSum
        (rationalQuittingFiniteWordSemanticPair reward roots).toReal ∧
      ∀ who, quittingTerminalSemanticDebtSum
          (rationalQuittingFiniteWordSemanticPair reward roots).toReal - (working : ℝ) / 8 <
        (rationalQuittingFiniteWordSemanticPair reward roots).toReal.2 who -
          rationalQuittingRewardToReal reward (quittingSingletonTerminal who) who := by
  rcases hsource with ⟨hdebt, hmargins⟩
  constructor
  · rw [quittingTerminalSemanticDebtSum_rational_eq_cast]
    exact_mod_cast hdebt
  · intro who
    rw [quittingTerminalSemanticDebtSum_rational_eq_cast]
    change (rationalQuittingSemanticDebtSum
        (rationalQuittingFiniteWordSemanticPair reward roots) : ℝ) - (working : ℝ) / 8 <
      ((rationalQuittingFiniteWordSemanticPair reward roots).2 who : ℝ) -
        (reward (quittingSingletonTerminal who) who : ℝ)
    exact_mod_cast hmargins who

private theorem concentrated_owner_above
    (reward : RationalQuittingReward players)
    (roots : List (RationalQuittingRoot players)) (owner : Fin players)
    {working : ℚ} (hworking : 0 < working)
    (hsource : RationalQuittingConcentratedPayoffSource reward roots working)
    (howner : (rationalQuittingFiniteWordSemanticPair reward roots).1 owner ≤
      reward (quittingSingletonTerminal owner) owner) :
    working / 4 < (rationalQuittingFiniteWordSemanticPair reward roots).2 owner -
      reward (quittingSingletonTerminal owner) owner := by
  obtain ⟨hdebt, hmargins⟩ := concentrated_real reward roots working hsource
  have hownerReal : (rationalQuittingFiniteWordSemanticPair reward roots).toReal.1 owner ≤
      rationalQuittingRewardToReal reward (quittingSingletonTerminal owner) owner := by
    change ((rationalQuittingFiniteWordSemanticPair reward roots).1 owner : ℝ) ≤
      (reward (quittingSingletonTerminal owner) owner : ℝ)
    exact_mod_cast howner
  have habove := (terminalSemantic_concentrated_source_bounds
    (rationalQuittingRewardToReal reward)
    (rationalQuittingFiniteWordSemanticPair reward roots).toReal owner
    (by exact_mod_cast hworking)
    (rationalQuittingFiniteWordSemanticPair_mem_carrier reward roots)
    hdebt hmargins hownerReal).2.2.1
  change (working : ℝ) / 4 <
    ((rationalQuittingFiniteWordSemanticPair reward roots).2 owner : ℝ) -
      (reward (quittingSingletonTerminal owner) owner : ℝ) at habove
  exact_mod_cast habove

private theorem failedColumn_blocker
    (reward : RationalQuittingReward players) (owner : Fin players) (working : ℚ)
    (hcolumn : ¬RationalQuittingPositiveSingletonColumnAt reward owner working) :
    ∃ blocker, blocker ≠ owner ∧
      reward (quittingSingletonTerminal owner) blocker <
        reward (quittingSingletonTerminal blocker) blocker + working / 4 := by
  classical
  by_contra hnot
  apply hcolumn
  intro who hne
  apply le_of_not_gt
  intro hlt
  exact hnot ⟨who, hne, hlt⟩

private theorem source_hit_exists
    (reward : RationalQuittingReward players)
    (roots : List (RationalQuittingRoot players)) (owner : Fin players)
    {M working : ℚ} (hM : 0 < M) (hworking : 0 < working) (hworkingM : working ≤ M)
    (hreward : ∀ terminal who, |reward terminal who| ≤ M)
    (hsource : RationalQuittingConcentratedPayoffSource reward roots working)
    (howner : (rationalQuittingFiniteWordSemanticPair reward roots).1 owner ≤
      reward (quittingSingletonTerminal owner) owner)
    (hcolumn : ¬RationalQuittingPositiveSingletonColumnAt reward owner working) :
    ∃ steps, rationalSoloPayoffDebtThresholdHit reward owner
      (rationalPositiveColumnWorkingHazard M working) working
      (rationalQuittingFiniteWordSemanticPair reward roots) steps := by
  obtain ⟨blocker, hne, hblocker⟩ := failedColumn_blocker reward owner working hcolumn
  obtain ⟨steps, _, hhit⟩ := exists_rationalSoloPayoffDebtThreshold_hit_le_horizon
    reward roots owner blocker hM hworking hreward
    (rationalPositiveColumnWorkingHazard_pos hM hworking)
    (rationalPositiveColumnWorkingHazard_lt_one hM hworkingM)
    (workingHazard_charge hM)
    (concentrated_owner_above reward roots owner hworking hsource howner) hne hblocker
  exact ⟨steps, hhit⟩

/-- First actual payoff/debt hit at the unchanged working rate. All data are
computed from rational reward/source rows; source proofs are erased. -/
def executableRationalPayoffDebtThresholdIndex
    (reward : RationalQuittingReward players)
    (roots : List (RationalQuittingRoot players)) (owner : Fin players)
    (M working : ℚ) (hM : 0 < M) (hworking : 0 < working) (hworkingM : working ≤ M)
    (hreward : ∀ terminal who, |reward terminal who| ≤ M)
    (hsource : RationalQuittingConcentratedPayoffSource reward roots working)
    (howner : (rationalQuittingFiniteWordSemanticPair reward roots).1 owner ≤
      reward (quittingSingletonTerminal owner) owner)
    (hcolumn : ¬RationalQuittingPositiveSingletonColumnAt reward owner working) : ℕ :=
  rationalFirstSoloPayoffDebtThresholdIndex reward owner
    (rationalPositiveColumnWorkingHazard M working) working
    (rationalQuittingFiniteWordSemanticPair reward roots)
    (source_hit_exists reward roots owner hM hworking hworkingM
      hreward hsource howner hcolumn)

/-- Exactly K solo rows followed by the unchanged old source word. -/
def executableRationalPayoffDebtThresholdWord
    (reward : RationalQuittingReward players)
    (roots : List (RationalQuittingRoot players)) (owner : Fin players)
    (M working : ℚ) (hM : 0 < M) (hworking : 0 < working) (hworkingM : working ≤ M)
    (hreward : ∀ terminal who, |reward terminal who| ≤ M)
    (hsource : RationalQuittingConcentratedPayoffSource reward roots working)
    (howner : (rationalQuittingFiniteWordSemanticPair reward roots).1 owner ≤
      reward (quittingSingletonTerminal owner) owner)
    (hcolumn : ¬RationalQuittingPositiveSingletonColumnAt reward owner working) :
    List (RationalQuittingRoot players) :=
  List.replicate (executableRationalPayoffDebtThresholdIndex reward roots owner M working
    hM hworking hworkingM hreward hsource howner hcolumn)
      (rationalQuittingSoloRoot owner (rationalPositiveColumnWorkingHazard M working)) ++ roots

section Correctness

variable (reward : RationalQuittingReward players)
  (roots : List (RationalQuittingRoot players)) (owner : Fin players)
  (M working : ℚ) (hM : 0 < M) (hworking : 0 < working) (hworkingM : working ≤ M)
  (hreward : ∀ terminal who, |reward terminal who| ≤ M)
  (hsource : RationalQuittingConcentratedPayoffSource reward roots working)
  (howner : (rationalQuittingFiniteWordSemanticPair reward roots).1 owner ≤
    reward (quittingSingletonTerminal owner) owner)
  (hcolumn : ¬RationalQuittingPositiveSingletonColumnAt reward owner working)

local notation "index" => executableRationalPayoffDebtThresholdIndex reward roots owner M working
  hM hworking hworkingM hreward hsource howner hcolumn
local notation "word" => executableRationalPayoffDebtThresholdWord reward roots owner M working
  hM hworking hworkingM hreward hsource howner hcolumn
local notation "hazard" => rationalPositiveColumnWorkingHazard M working
local notation "source" => rationalQuittingFiniteWordSemanticPair reward roots

/-- Minimality and the logarithmic bound concern the PAYOFF test, not a cap hit. -/
theorem executableRationalPayoffDebtThresholdIndex_spec :
    0 < index ∧
    index ≤ quittingSoloCapThresholdHorizon (M : ℝ) (hazard : ℝ) ((working : ℝ) / 2) ∧
    rationalSoloPayoffDebtThresholdHit reward owner hazard working source index ∧
    ∀ steps, steps < index →
      ¬rationalSoloPayoffDebtThresholdHit reward owner hazard working source steps := by
  have hhit := rationalFirstSoloPayoffDebtThresholdIndex_spec reward owner hazard working
    source (source_hit_exists reward roots owner hM hworking hworkingM
      hreward hsource howner hcolumn)
  have hbefore (steps : ℕ) (hsteps : steps < index) :=
    rationalFirstSoloPayoffDebtThresholdIndex_before reward owner hazard working
      source (source_hit_exists reward roots owner hM hworking hworkingM
        hreward hsource howner hcolumn) hsteps
  have hnotzero : ¬rationalSoloPayoffDebtThresholdHit reward owner hazard working source 0 := by
    rw [rationalSoloPayoffDebtThresholdHit, rationalQuittingSoloSemanticIterate_zero]
    rintro (hsmall | ⟨who, hne, hpayoff⟩)
    · exact not_lt_of_ge hsource.1 hsmall
    · have hownerReal : (source).toReal.1 owner ≤
          rationalQuittingRewardToReal reward (quittingSingletonTerminal owner) owner := by
        change (source.1 owner : ℝ) ≤
          (reward (quittingSingletonTerminal owner) owner : ℝ)
        exact_mod_cast howner
      obtain ⟨_, houtside, _, _⟩ := terminalSemantic_concentrated_source_bounds
        (rationalQuittingRewardToReal reward) (source).toReal owner
        (by exact_mod_cast hworking)
        (rationalQuittingFiniteWordSemanticPair_mem_carrier reward roots)
        (concentrated_real reward roots working hsource).1
        (concentrated_real reward roots working hsource).2
        hownerReal
      have hlarge := houtside who hne
      change (reward (quittingSingletonTerminal who) who : ℝ) +
        3 * (working : ℝ) / 4 < (source.1 who : ℝ) at hlarge
      have hpayoffReal : (source.1 who : ℝ) ≤
          (reward (quittingSingletonTerminal who) who : ℝ) + (working : ℝ) / 2 := by
        exact_mod_cast hpayoff
      have hpositive : (0 : ℝ) < (working : ℝ) := by exact_mod_cast hworking
      linarith
  have hpositive : 0 < index := by
    apply Nat.pos_of_ne_zero
    intro hzero
    exact hnotzero (hzero ▸ hhit)
  obtain ⟨blocker, hne, hblocker⟩ := failedColumn_blocker reward owner working hcolumn
  obtain ⟨steps, hsteps, hstepsHit⟩ := exists_rationalSoloPayoffDebtThreshold_hit_le_horizon
    reward roots owner blocker hM hworking hreward
    (rationalPositiveColumnWorkingHazard_pos hM hworking)
    (rationalPositiveColumnWorkingHazard_lt_one hM hworkingM)
    (workingHazard_charge hM)
    (concentrated_owner_above reward roots owner hworking hsource howner) hne hblocker
  have hfirst := rationalFirstSoloPayoffDebtThresholdIndex_le reward owner hazard working source
    (source_hit_exists reward roots owner hM hworking hworkingM
      hreward hsource howner hcolumn) hstepsHit
  exact ⟨hpositive, hfirst.trans hsteps, hhit, fun steps hsteps => hbefore steps hsteps⟩

/-- The original source is the literal suffix, including its arbitrary old
length and complete behavioral tail. Exactly `index` dates have been added. -/
theorem executableRationalPayoffDebtThresholdWord_length :
    (word).length = index + roots.length := by
  simp only [executableRationalPayoffDebtThresholdWord,
    List.length_append, List.length_replicate]

/-- The packet's literal logarithmic date bound at the unchanged working rate. -/
theorem executableRationalPayoffDebtThresholdIndex_le_log :
    index ≤ Nat.ceil ((16 * (M : ℝ) / (working : ℝ)) *
      Real.log (8 * (M : ℝ) / (working : ℝ))) := by
  have hworkingReal : (0 : ℝ) < (working : ℝ) := by exact_mod_cast hworking
  have hMReal : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hh : (hazard : ℝ) = (working : ℝ) / (16 * (M : ℝ)) := by
    simp only [rationalPositiveColumnWorkingHazard, Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat]
  have hinverse : (hazard : ℝ)⁻¹ = 16 * (M : ℝ) / (working : ℝ) := by
    rw [hh]
    field_simp [ne_of_gt hworkingReal, ne_of_gt hMReal]
  have hratio : 4 * (M : ℝ) / ((working : ℝ) / 2) =
      8 * (M : ℝ) / (working : ℝ) := by
    field_simp [ne_of_gt hworkingReal]; ring
  simpa only [quittingSoloCapThresholdHorizon, hinverse, hratio] using
    (executableRationalPayoffDebtThresholdIndex_spec reward roots owner M working
      hM hworking hworkingM hreward hsource howner hcolumn).2.1

noncomputable section

/-- Exact actual iterate and first-hit ledger for the retained source word.
The full-cap/debt semantics quantify over every behavioral replacement. -/
theorem executableRationalPayoffDebtThresholdWord_ledger :
    let actualReward := rationalQuittingRewardToReal reward
    let initial := (source).toReal
    let reached := quittingTerminalSemanticPair actualReward
      (quittingLiteralRootStackProfile actualReward ((word).map RationalQuittingRoot.toPMF)
        (quittingAlwaysContinueProfile actualReward))
    reached =
      (fun who => actualReward (quittingSingletonTerminal owner) who +
        (1 - (hazard : ℝ)) ^ index *
          (initial.1 who - actualReward (quittingSingletonTerminal owner) who),
       fun who => if who = owner then initial.2 owner else
         actualReward (quittingSingletonTerminal owner) who +
           (1 - (hazard : ℝ)) ^ index *
             (initial.2 who - actualReward (quittingSingletonTerminal owner) who)) ∧
    quittingTerminalSemanticDebtSum reached =
      (1 - (hazard : ℝ)) ^ index * quittingTerminalSemanticDebtSum initial +
        (1 - (1 - (hazard : ℝ)) ^ index) *
          (initial.2 owner - actualReward (quittingSingletonTerminal owner) owner) ∧
    quittingTerminalSemanticDebtSum reached ≤ quittingTerminalSemanticDebtSum initial ∧
    (∑ who ∈ Finset.univ.erase owner, quittingTerminalSemanticDebt reached who) <
      (working : ℝ) / 8 := by
  dsimp only
  have hh0 := rationalPositiveColumnWorkingHazard_pos hM hworking
  have hh1 := rationalPositiveColumnWorkingHazard_lt_one hM hworkingM
  simp only [executableRationalPayoffDebtThresholdWord]
  rw [quittingTerminalSemanticPair_rationalSoloPrefix_eq_iterate
      reward roots owner ⟨hh0.le, hh1.le⟩,
    ← quittingSoloSemanticIterate_rational_eq_cast reward owner ⟨hh0.le, hh1.le⟩ source index]
  refine quittingSoloPayoffDebtThreshold_before_ledger
    (rationalQuittingRewardToReal reward) (source).toReal owner
    (M := (M : ℝ)) (working := (working : ℝ)) (θ := (hazard : ℝ))
    ?_ (rationalQuittingFiniteWordSemanticPair_mem_carrier reward roots)
    (by exact_mod_cast hworking) (by exact_mod_cast hh0) (by exact_mod_cast hh1)
    (by exact_mod_cast workingHazard_charge (working := working) hM)
    (concentrated_real reward roots working hsource).1
    (concentrated_real reward roots working hsource).2 ?_ index ?_
  · intro terminal who
    change |(reward terminal who : ℝ)| ≤ (M : ℝ)
    exact_mod_cast hreward terminal who
  · change (source.1 owner : ℝ) ≤
      (reward (quittingSingletonTerminal owner) owner : ℝ)
    exact_mod_cast howner
  · intro steps hsteps hhit
    exact (executableRationalPayoffDebtThresholdIndex_spec reward roots owner M working
      hM hworking hworkingM hreward hsource howner hcolumn).2.2.2 steps hsteps
      ((rationalSoloPayoffDebtThresholdHit_iff_real reward owner ⟨hh0.le, hh1.le⟩
        working source steps).mpr hhit)

/-- The nonterminal first hit produces the next ACTUAL charged-margin
witness. This is the source handoff, not an inferred strict preemptor. -/
theorem executableRationalPayoffDebtThresholdWord_endpoint :
    let actualReward := rationalQuittingRewardToReal reward
    let reached := quittingTerminalSemanticPair actualReward
      (quittingLiteralRootStackProfile actualReward ((word).map RationalQuittingRoot.toPMF)
        (quittingAlwaysContinueProfile actualReward))
    quittingTerminalSemanticDebtSum reached < (working : ℝ) ∨
      ∃ who, who ≠ owner ∧
        reached.2 who - actualReward (quittingSingletonTerminal who) who < 5 * (working : ℝ) / 8 ∧
        reached.2 who - actualReward (quittingSingletonTerminal who) who <
          quittingTerminalSemanticDebtSum reached - (working : ℝ) / 8 := by
  dsimp only
  have hh0 := rationalPositiveColumnWorkingHazard_pos hM hworking
  have hh1 := rationalPositiveColumnWorkingHazard_lt_one hM hworkingM
  have hhit := (rationalSoloPayoffDebtThresholdHit_iff_real reward owner ⟨hh0.le, hh1.le⟩
    working source index).mp
      (executableRationalPayoffDebtThresholdIndex_spec reward roots owner M working
        hM hworking hworkingM hreward hsource howner hcolumn).2.2.1
  have houtside := (executableRationalPayoffDebtThresholdWord_ledger reward roots owner M working
    hM hworking hworkingM hreward hsource howner hcolumn).2.2.2
  simp only [executableRationalPayoffDebtThresholdWord] at houtside ⊢
  rw [quittingTerminalSemanticPair_rationalSoloPrefix_eq_iterate
      reward roots owner ⟨hh0.le, hh1.le⟩,
    ← quittingSoloSemanticIterate_rational_eq_cast reward owner ⟨hh0.le, hh1.le⟩ source index]
    at houtside ⊢
  by_cases hsmall : quittingTerminalSemanticDebtSum
      (quittingSoloSemanticIterate (rationalQuittingRewardToReal reward) owner
        (quittingHazardCoin (hazard : ℝ)
          (by exact_mod_cast hh0.le) (by exact_mod_cast hh1.le)) (source).toReal index) <
      (working : ℝ)
  · exact Or.inl hsmall
  · right
    exact quittingSoloPayoffDebtThreshold_charged_margin_of_nonterminal_hit
      (rationalQuittingRewardToReal reward) (source).toReal owner _
      (by exact_mod_cast hworking)
      (rationalQuittingFiniteWordSemanticPair_mem_carrier reward roots) index hhit
      (le_of_not_gt hsmall) houtside

/-- EVERY actual intermediate prefix has the same retained tail, and total
debt is nonincreasing up to and including the first payoff hit. -/
theorem executableRationalPayoffDebtThresholdWord_debt_antitone
    {earlier later : ℕ} (horder : earlier ≤ later) (hlater : later ≤ index) :
    let actualReward := rationalQuittingRewardToReal reward
    let row := rationalQuittingSoloRoot owner hazard
    let pair := fun steps => quittingTerminalSemanticPair actualReward
      (quittingLiteralRootStackProfile actualReward
        ((List.replicate steps row ++ roots).map RationalQuittingRoot.toPMF)
        (quittingAlwaysContinueProfile actualReward))
    quittingTerminalSemanticDebtSum (pair later) ≤
      quittingTerminalSemanticDebtSum (pair earlier) := by
  dsimp only
  have hh0 := rationalPositiveColumnWorkingHazard_pos hM hworking
  have hh1 := rationalPositiveColumnWorkingHazard_lt_one hM hworkingM
  rw [quittingTerminalSemanticPair_rationalSoloPrefix_eq_iterate
      reward roots owner ⟨hh0.le, hh1.le⟩ later,
    quittingTerminalSemanticPair_rationalSoloPrefix_eq_iterate
      reward roots owner ⟨hh0.le, hh1.le⟩ earlier,
    ← quittingSoloSemanticIterate_rational_eq_cast reward owner ⟨hh0.le, hh1.le⟩ source later,
    ← quittingSoloSemanticIterate_rational_eq_cast reward owner ⟨hh0.le, hh1.le⟩ source earlier]
  refine quittingSoloPayoffDebtThreshold_debtSum_antitone_until_hit
    (rationalQuittingRewardToReal reward) (source).toReal owner
    (M := (M : ℝ)) (working := (working : ℝ)) (θ := (hazard : ℝ))
    ?_ (rationalQuittingFiniteWordSemanticPair_mem_carrier reward roots)
    (by exact_mod_cast hworking) (by exact_mod_cast hh0) (by exact_mod_cast hh1)
    (by exact_mod_cast workingHazard_charge (working := working) hM)
    (concentrated_real reward roots working hsource).1
    (concentrated_real reward roots working hsource).2 ?_ horder ?_
  · intro terminal who
    change |(reward terminal who : ℝ)| ≤ (M : ℝ)
    exact_mod_cast hreward terminal who
  · change (source.1 owner : ℝ) ≤
      (reward (quittingSingletonTerminal owner) owner : ℝ)
    exact_mod_cast howner
  · intro steps hsteps hhit
    exact (executableRationalPayoffDebtThresholdIndex_spec reward roots owner M working
      hM hworking hworkingM hreward hsource howner hcolumn).2.2.2 steps
      (hsteps.trans_le hlater)
      ((rationalSoloPayoffDebtThresholdHit_iff_real reward owner ⟨hh0.le, hh1.le⟩
        working source steps).mpr hhit)

/-- The SAME retained word compiles to exact independent rational date/Never
laws with its full actual payoff and unrestricted response-cap vector. -/
theorem executableRationalPayoffDebtThresholdWord_finiteLaws :
    ∃ mixed : Fin players → PMF (Option (Fin (word).length)),
      (∀ who choice, (mixed who choice).toReal =
        (rationalFiniteClockMass (rationalQuittingFiniteWordSequence word)
          (word).length who choice : ℝ)) ∧
      quittingTerminalSemanticPair (rationalQuittingRewardToReal reward)
        (quittingFiniteDeadlineTimingProfile (rationalQuittingRewardToReal reward)
          (word).length mixed) =
        quittingTerminalSemanticPair (rationalQuittingRewardToReal reward)
          (quittingLiteralRootStackProfile (rationalQuittingRewardToReal reward)
            ((word).map RationalQuittingRoot.toPMF)
            (quittingAlwaysContinueProfile (rationalQuittingRewardToReal reward))) := by
  obtain ⟨mixed, hmass, hpair⟩ := exists_rationalQuittingFiniteWordLaws_exact reward word
  exact ⟨mixed, hmass,
    hpair.trans (quittingTerminalSemanticPair_rationalFiniteWord_eq_cast reward word).symm⟩

end
end Correctness

/-- The weak-exclusion owner is computed BEFORE the first payoff-hit scan.
No strategic owner, cap, root or successful scan is supplied as an oracle. -/
def executableRationalWeakExclusionPayoffThresholdWord
    (reward : RationalQuittingReward players) (owners : Finset (Fin players))
    (hWE : RationalQuittingFiniteWordOwnerExclusionOn reward owners)
    (roots : List (RationalQuittingRoot players))
    (M working : ℚ) (hM : 0 < M) (hworking : 0 < working) (hworkingM : working ≤ M)
    (hreward : ∀ terminal who, |reward terminal who| ≤ M)
    (hsource : RationalQuittingConcentratedPayoffSource reward roots working)
    (hcolumn : ¬RationalQuittingPositiveSingletonColumnAt reward
      (rationalQuittingFiniteWordExcludedOwnerOn reward owners hWE roots) working) :
    List (RationalQuittingRoot players) :=
  executableRationalPayoffDebtThresholdWord reward roots
    (rationalQuittingFiniteWordExcludedOwnerOn reward owners hWE roots)
    M working hM hworking hworkingM hreward hsource
    (rationalQuittingFiniteWordExcludedOwnerOn_payoff_le reward owners hWE roots) hcolumn

noncomputable section

/-- Source-complete weak-exclusion facade: the produced owner's first hit,
actual retained word, full debt nonincrease and next charged witness. -/
theorem executableRationalWeakExclusionPayoffThresholdWord_spec
    (reward : RationalQuittingReward players) (owners : Finset (Fin players))
    (hWE : RationalQuittingFiniteWordOwnerExclusionOn reward owners)
    (roots : List (RationalQuittingRoot players))
    (M working : ℚ) (hM : 0 < M) (hworking : 0 < working) (hworkingM : working ≤ M)
    (hreward : ∀ terminal who, |reward terminal who| ≤ M)
    (hsource : RationalQuittingConcentratedPayoffSource reward roots working)
    (hcolumn : ¬RationalQuittingPositiveSingletonColumnAt reward
      (rationalQuittingFiniteWordExcludedOwnerOn reward owners hWE roots) working) :
    let owner := rationalQuittingFiniteWordExcludedOwnerOn reward owners hWE roots
    let ownerBound := rationalQuittingFiniteWordExcludedOwnerOn_payoff_le reward owners hWE roots
    let index := executableRationalPayoffDebtThresholdIndex reward roots owner M working
      hM hworking hworkingM hreward hsource ownerBound hcolumn
    let word := executableRationalWeakExclusionPayoffThresholdWord reward owners hWE roots
      M working hM hworking hworkingM hreward hsource hcolumn
    let actualReward := rationalQuittingRewardToReal reward
    let reached := quittingTerminalSemanticPair actualReward
      (quittingLiteralRootStackProfile actualReward ((word).map RationalQuittingRoot.toPMF)
        (quittingAlwaysContinueProfile actualReward))
    owner ∈ owners ∧
    word = List.replicate index
      (rationalQuittingSoloRoot owner (rationalPositiveColumnWorkingHazard M working)) ++ roots ∧
    0 < index ∧
    index ≤ Nat.ceil ((16 * (M : ℝ) / (working : ℝ)) *
      Real.log (8 * (M : ℝ) / (working : ℝ))) ∧
    quittingTerminalSemanticDebtSum reached ≤
      (rationalQuittingSemanticDebtSum
        (rationalQuittingFiniteWordSemanticPair reward roots) : ℝ) ∧
    (quittingTerminalSemanticDebtSum reached < (working : ℝ) ∨
      ∃ who, who ≠ owner ∧
        reached.2 who - actualReward (quittingSingletonTerminal who) who < 5 * (working : ℝ) / 8 ∧
        reached.2 who - actualReward (quittingSingletonTerminal who) who <
          quittingTerminalSemanticDebtSum reached - (working : ℝ) / 8) := by
  dsimp only
  let owner := rationalQuittingFiniteWordExcludedOwnerOn reward owners hWE roots
  have howner := rationalQuittingFiniteWordExcludedOwnerOn_payoff_le reward owners hWE roots
  have hindex := executableRationalPayoffDebtThresholdIndex_spec reward roots owner M working
    hM hworking hworkingM hreward hsource howner hcolumn
  have hlog := executableRationalPayoffDebtThresholdIndex_le_log reward roots owner M working
    hM hworking hworkingM hreward hsource howner hcolumn
  have hledger := (executableRationalPayoffDebtThresholdWord_ledger reward roots owner M working
    hM hworking hworkingM hreward hsource howner hcolumn).2.2.1
  rw [quittingTerminalSemanticDebtSum_rational_eq_cast] at hledger
  exact ⟨rationalQuittingFiniteWordExcludedOwnerOn_mem reward owners hWE roots,
    rfl, hindex.1, hlog, hledger,
    executableRationalPayoffDebtThresholdWord_endpoint reward roots owner M working
      hM hworking hworkingM hreward hsource howner hcolumn⟩

/-- The actual source of the weak-exclusion scan is not replaced by a payoff
realization: this is the SAME word's independent rational finite calendar. -/
theorem executableRationalWeakExclusionPayoffThresholdWord_finiteLaws
    (reward : RationalQuittingReward players) (owners : Finset (Fin players))
    (hWE : RationalQuittingFiniteWordOwnerExclusionOn reward owners)
    (roots : List (RationalQuittingRoot players))
    (M working : ℚ) (hM : 0 < M) (hworking : 0 < working) (hworkingM : working ≤ M)
    (hreward : ∀ terminal who, |reward terminal who| ≤ M)
    (hsource : RationalQuittingConcentratedPayoffSource reward roots working)
    (hcolumn : ¬RationalQuittingPositiveSingletonColumnAt reward
      (rationalQuittingFiniteWordExcludedOwnerOn reward owners hWE roots) working) :
    let word := executableRationalWeakExclusionPayoffThresholdWord reward owners hWE roots
      M working hM hworking hworkingM hreward hsource hcolumn
    ∃ mixed : Fin players → PMF (Option (Fin (word).length)),
      (∀ who choice, (mixed who choice).toReal =
        (rationalFiniteClockMass (rationalQuittingFiniteWordSequence word)
          (word).length who choice : ℝ)) ∧
      quittingTerminalSemanticPair (rationalQuittingRewardToReal reward)
        (quittingFiniteDeadlineTimingProfile (rationalQuittingRewardToReal reward)
          (word).length mixed) =
        quittingTerminalSemanticPair (rationalQuittingRewardToReal reward)
          (quittingLiteralRootStackProfile (rationalQuittingRewardToReal reward)
            ((word).map RationalQuittingRoot.toPMF)
            (quittingAlwaysContinueProfile (rationalQuittingRewardToReal reward))) := by
  dsimp only [executableRationalWeakExclusionPayoffThresholdWord]
  exact executableRationalPayoffDebtThresholdWord_finiteLaws reward roots
    (rationalQuittingFiniteWordExcludedOwnerOn reward owners hWE roots)
    M working hM hworking hworkingM hreward hsource
    (rationalQuittingFiniteWordExcludedOwnerOn_payoff_le reward owners hWE roots) hcolumn

end

end GameTheory
