import UniformEquilibrium.Quitting.Classification.LCP.MatrixClasses
import UniformEquilibrium.Quitting.Classification.LCP.NormalCore
import UniformEquilibrium.Quitting.Classification.LCP.StationaryExistence
import UniformEquilibrium.Quitting.Classification.LCP.StrategicTransport
import UniformEquilibrium.Quitting.Classification.TableExistenceBranches
import MathUE.CaristiFixedPoint
import MathUE.DivergentChargeRecurrence
import MathUE.ProbabilityMassFunction.Simplex
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-!
# Solan--Solan (2020) — paper-order audit

E. Solan and O. N. Solan, *Quitting Games and Linear Complementarity
Problems*, *Mathematics of Operations Research* 45(2), 434--454. The
accepted May 2018 manuscript is the authoritative complete text available
for this audit; it is used where arXiv:1707.02598v1 differs and supplies the
final theorem numbering.

One correction is mathematically material. The arXiv v1 building-block
condition (F.1) mentions only segments starting at `w`, although its final
construction uses a segment starting at `y`; the accepted manuscript states
the necessary disjunction. The paper's normal players are defined by their
min--max values. Its distinct-witness recursion occurs only in Section 5,
where it defines the different, generally smaller set of alpha players.

Public randomization is represented by an actual finite public-signal
stochastic game, and all payoffs and deviation payoffs below are induced by
behavior profiles. The stationary and LCP statements use the full payoff
table, including the nontermination payoff.
-/

namespace Literature.SolanAndSolan2020

open GameTheory StochasticGame QuittingLCPClassification
open Math.Probability
open Math.LinearProgramming
open Filter
open scoped BigOperators
open scoped Topology

noncomputable section

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## Section 2.1 — model -/

/-! **Definition 2.1 (paper).** A quitting game is a finite player set
`I=[N]` and a payoff vector `r_S ∈ [-1,1]^N` for every `S ⊆ I`. At every
stage every player chooses Continue or Quit; the first nonempty quitter set
`S*` ends the game and pays `r_{S*}`, while never quitting pays `r_∅`.
The paper also defines pure strategies `N ∪ {∞}`, behavior strategies
`x_i=(x_i^t)_{t∈N}`, profiles `X_i`, `X`, the induced law `P_x`, expected
payoff `γ(x)`, and the undiscounted ε-equilibrium inequality.

The repository's `QuittingPayoffTable` is the faithful finite-player adapter:
`terminal` is `r_S` for nonempty `S`, and `never` is `r_∅`. Its
`terminalPayoff` supplies the induced expected payoff for a repository
behavior profile. The paper's pure-strategy presentation is equivalent to
the behavioral presentation but has no separate declaration here.
-/

/-! `Table` carries `(r_S)_{S ⊆ I}` together with `r_∅`. -/
abbrev Table (ι : Type) [Fintype ι] [DecidableEq ι] :=
  QuittingPayoffTable ι

/-! Paper ε-equilibrium adapter:
`γ_i(x) ≥ γ_i(x'_i,x_{-i}) - ε`. -/
def EpsilonEquilibrium
    (table : Table ι) (ε : ℝ)
    (profile : (quittingGame table.terminal).BehaviorProfile) : Prop :=
  (quittingGame table.terminal).IsεAsymptoticNash table.terminalPayoff ε profile

/-! `StationaryEpsilonEquilibria table` means stationary ε-equilibria
exist for every `ε>0`. -/
abbrev StationaryEpsilonEquilibria (table : Table ι) : Prop :=
  table.StationaryεEquilibriumExistence

/-! **Assumption 2.1.** The paper assumes `r_i^i = 0` for every player.
This is a standing condition, not a theorem. -/

def SoloExitNormalized (table : Table ι) : Prop :=
  ∀ i : ι, table.terminal (quittingProjectiveSingletonTerminal i) i = 0

/-! The source's global payoff normalization `r_S∈[-1,1]^N`. -/
def TablePayoffsBounded (table : Table ι) : Prop :=
  (∀ S who, |table.terminal S who| ≤ 1) ∧
    ∀ who, |table.never who| ≤ 1

/-! **Definition 2.3 (sunspot ε-equilibrium, paper).** At every stage the
players observe an independent uniform signal in `[0,1]`; a strategy is a
sequence of measurable functions from public signal histories to quit
probabilities. The local profile below packages the paper's induced payoff and
unilateral-deviation payoff functions; the probability construction is not
silently identified with the repository's terminal-only profile. -/

/-! The finite-support public randomizations used by the proof are exactly
coarsenings of the source's uniform `[0,1]` signal. We represent a coarsening
by a law on `ℕ`; its atoms are the publicly observed labels. -/

inductive PublicQuittingState (ι : Type) [Fintype ι] [DecidableEq ι]
    (Signal : Type) [Fintype Signal]
  | draw
  | active (signal : Signal)
  | absorbed (quitters : {S : Finset ι // S.Nonempty})
deriving Fintype

/-! The induced public-signal quitting game. The action-irrelevant `draw`
state samples a label before every live decision, including the first one.
At an `active` state a nonempty quitter set absorbs, while unanimous Continue
returns to `draw`. Thus no strategic decision is made before the first public
signal, exactly as in Definition 2.3. -/
def publicQuittingGame {Signal : Type} [Fintype Signal] (table : Table ι)
    (signalLaw : PMF Signal) :
    StochasticGame ι where
  State := PublicQuittingState ι Signal
  Act := fun _ => Bool
  stagePayoff := fun state _ who =>
    match state with
    | .draw => table.never who
    | .active _ => table.never who
    | .absorbed quitters => table.terminal quitters who
  transition := fun state action =>
    match state with
    | .draw => signalLaw.map PublicQuittingState.active
    | .active _ =>
        if h : ({who | action who = true} : Finset ι).Nonempty then
          PMF.pure (.absorbed ⟨_, h⟩)
        else
          PMF.pure .draw
    | .absorbed quitters => PMF.pure (.absorbed quitters)
  discount := 0
  discount_nonneg := le_rfl
  discount_lt_one := zero_lt_one

/-! Indicator and time-`t` mass of one absorbing quitter set. -/
def publicAbsorbedIndicator {Signal : Type} [Fintype Signal]
    (quitters : {S : Finset ι // S.Nonempty})
    (state : PublicQuittingState ι Signal) : ℝ := by
  classical
  exact if state = .absorbed quitters then 1 else 0

def publicAbsorbedMass
    {signalCount : ℕ} (table : Table ι)
    (signalLaw : PMF (Fin (signalCount + 1)))
    (strategy : (publicQuittingGame table signalLaw).BehaviorProfile)
    (t : ℕ) (quitters : {S : Finset ι // S.Nonempty}) : ℝ :=
  (publicQuittingGame table signalLaw).expectedStateValue strategy
    .draw t (publicAbsorbedIndicator quitters)

/-! Limiting probability of absorption at one quitter set. -/
def publicAbsorbedMassLimit
    {signalCount : ℕ} (table : Table ι)
    (signalLaw : PMF (Fin (signalCount + 1)))
    (strategy : (publicQuittingGame table signalLaw).BehaviorProfile)
    (quitters : {S : Finset ι // S.Nonempty}) : ℝ :=
  ⨆ t, publicAbsorbedMass table signalLaw strategy t quitters

theorem publicAbsorbedMass_succ_ge
    {signalCount : ℕ} (table : Table ι)
    (signalLaw : PMF (Fin (signalCount + 1)))
    (strategy : (publicQuittingGame table signalLaw).BehaviorProfile)
    (t : ℕ) (quitters : {S : Finset ι // S.Nonempty}) :
    publicAbsorbedMass table signalLaw strategy t quitters ≤
      publicAbsorbedMass table signalLaw strategy (t + 1) quitters := by
  letI : Finite (publicQuittingGame table signalLaw).State :=
    inferInstanceAs (Finite (PublicQuittingState ι (Fin (signalCount + 1))))
  letI : ∀ i : ι, Finite ((publicQuittingGame table signalLaw).Act i) :=
    fun _ => inferInstanceAs (Finite Bool)
  rw [publicAbsorbedMass, publicAbsorbedMass,
    (publicQuittingGame table signalLaw).expectedStateValue_succ]
  unfold StochasticGame.expectedStateValue
  apply expect_mono
  intro history
  cases hstate : history.2 with
  | draw =>
      rw [show publicAbsorbedIndicator quitters .draw = 0 by
        simp [publicAbsorbedIndicator]]
      exact expect_nonneg _ _ fun action =>
        expect_nonneg _ _ fun state => by
          unfold publicAbsorbedIndicator
          split <;> norm_num
  | active signal =>
      rw [show publicAbsorbedIndicator quitters (.active signal) = 0 by
        simp [publicAbsorbedIndicator]]
      exact expect_nonneg _ _ fun action =>
        expect_nonneg _ _ fun state => by
          unfold publicAbsorbedIndicator
          split <;> norm_num
  | absorbed terminal =>
      simp [publicQuittingGame, publicAbsorbedIndicator]

theorem publicAbsorbedMass_le_one
    {signalCount : ℕ} (table : Table ι)
    (signalLaw : PMF (Fin (signalCount + 1)))
    (strategy : (publicQuittingGame table signalLaw).BehaviorProfile)
    (t : ℕ) (quitters : {S : Finset ι // S.Nonempty}) :
    publicAbsorbedMass table signalLaw strategy t quitters ≤ 1 := by
  letI : Finite (publicQuittingGame table signalLaw).State :=
    inferInstanceAs (Finite (PublicQuittingState ι (Fin (signalCount + 1))))
  letI : ∀ i : ι, Finite ((publicQuittingGame table signalLaw).Act i) :=
    fun _ => inferInstanceAs (Finite Bool)
  unfold publicAbsorbedMass StochasticGame.expectedStateValue
  calc
    expect ((publicQuittingGame table signalLaw).histDist strategy
        .draw t)
        (fun history => publicAbsorbedIndicator quitters history.2) ≤
        expect ((publicQuittingGame table signalLaw).histDist strategy
          .draw t) (fun _ => 1) := by
      apply expect_mono
      intro history
      unfold publicAbsorbedIndicator
      split <;> norm_num
    _ = 1 := expect_const _ _

theorem tendsto_publicAbsorbedMass
    {signalCount : ℕ} (table : Table ι)
    (signalLaw : PMF (Fin (signalCount + 1)))
    (strategy : (publicQuittingGame table signalLaw).BehaviorProfile)
    (quitters : {S : Finset ι // S.Nonempty}) :
    Tendsto (fun t => publicAbsorbedMass table signalLaw strategy t quitters)
      atTop (nhds (publicAbsorbedMassLimit table signalLaw strategy quitters)) := by
  apply tendsto_atTop_ciSup
  · exact monotone_nat_of_le_succ fun t =>
      publicAbsorbedMass_succ_ge table signalLaw strategy t quitters
  · refine ⟨1, ?_⟩
    rintro _ ⟨t, rfl⟩
    exact publicAbsorbedMass_le_one table signalLaw strategy t quitters

/-! The expected terminal payoff induced by a public profile. Absorption at
`S` changes the payoff from `r_∅` to `r_S`; the residual nonabsorption mass
therefore receives `r_∅` exactly as in the source. -/
def publicQuittingPayoff
    {signalCount : ℕ} (table : Table ι)
    (signalLaw : PMF (Fin (signalCount + 1)))
    (strategy : (publicQuittingGame table signalLaw).BehaviorProfile)
    (who : ι) : ℝ :=
  table.never who +
    ∑ quitters, publicAbsorbedMassLimit table signalLaw strategy quitters *
      (table.terminal quitters who - table.never who)

/-! A sunspot profile is a public-signal law together with an actual behavior
profile of the induced quitting game. Its payoff is computed from play. -/
structure SunspotProfile (table : Table ι) where
  signalCount : ℕ
  signalLaw : PMF (Fin (signalCount + 1))
  strategy : (publicQuittingGame table signalLaw).BehaviorProfile

/-! The payoff generated by a sunspot profile. -/
def SunspotProfile.payoff {table : Table ι}
    (profile : SunspotProfile table) : Payoff ι :=
  publicQuittingPayoff table profile.signalLaw profile.strategy

/-! `ξ` is a sunspot ε-equilibrium iff
`γ_i(ξ) ≥ γ_i(ξ'_i,ξ_{-i})-ε` for every behavior deviation. -/
def SunspotEpsilonEquilibrium
    (table : Table ι) (ε : ℝ)
    (profile : SunspotProfile table) : Prop :=
  (publicQuittingGame table profile.signalLaw).IsεAsymptoticNash
    (publicQuittingPayoff table profile.signalLaw) ε profile.strategy

/-! At every live public history, at most one player assigns positive
probability to Quit. -/
def AtMostOneQuitter {table : Table ι}
    (profile : SunspotProfile table) : Prop :=
  ∀ t (history : (publicQuittingGame table profile.signalLaw).Hist t),
    match history.2 with
    | .draw => True
    | .active _ =>
        (Finset.filter (fun who =>
          0 < ((profile.strategy who t history) true).toReal)
          Finset.univ).card ≤ 1
    | .absorbed _ => True

/-! **Theorem 2.4 (paper).** Every quitting game admits a sunspot
ε-equilibrium for every `ε > 0`. -/

theorem theorem2_4 (table : Table ι)
    (hnormalized : SoloExitNormalized table)
    (hbounded : TablePayoffsBounded table) :
    ∀ ε : ℝ, 0 < ε → ∃ profile : SunspotProfile table,
      SunspotEpsilonEquilibrium table ε profile := by
  sorry

/-! ## Section 2.3 — normal and abnormal players -/

/-! **Definition 2.5 (paper).** Player `i` is normal when its min--max value
is nonpositive, and abnormal when that value is positive. -/
def IsNormalPlayer (table : Table ι) (who : ι) : Prop :=
  table.punishmentValue who ≤ 0

/-! `I*`, the finite set of normal players. -/
def NormalPlayers (table : Table ι) : Finset ι := by
  classical
  exact Finset.univ.filter (IsNormalPlayer table)

@[simp] theorem mem_normalPlayers_iff (table : Table ι) (who : ι) :
    who ∈ NormalPlayers table ↔ IsNormalPlayer table who := by
  classical
  simp [NormalPlayers]

/-! A normal player, used as the row and column type of the paper's matrix
`R̂`. -/
abbrev NormalPlayer (table : Table ι) :=
  {who : ι // who ∈ NormalPlayers table}

/-! `R̂`: singleton-quitting payoffs restricted in both coordinates to
normal players. -/
def NormalMatrix (table : Table ι) :
    NormalPlayer table → NormalPlayer table → ℝ :=
  fun who owner =>
    table.terminal (quittingProjectiveSingletonTerminal owner.1) who.1

/-! Under Assumption 2.1, the production normalization of the translated
zero-never table recovers the paper's raw singleton-payoff matrix. -/
theorem normalizedSoloMatrix_zeroNeverReward_eq_singletonMatrix
    (table : Table ι) (hnormalized : SoloExitNormalized table) :
    normalizedSoloMatrix table.zeroNeverReward = table.singletonMatrix := by
  funext who owner
  simp only [normalizedSoloMatrix, QuittingPayoffTable.singletonMatrix,
    normalizedQuittingPayoffTable, QuittingPayoffTable.translate,
    repositoryQuittingPayoffTable,
    QuittingLCPClassification.quittingSoloBaseline,
    QuittingPayoffTable.zeroNeverReward]
  rw [hnormalized who]
  ring

def HasNormalPlayers (table : Table ι) : Prop :=
  (NormalPlayers table).Nonempty

def AllPlayersAbnormal (table : Table ι) : Prop :=
  NormalPlayers table = ∅

/-! **Lemma 2.6 (paper).** If `i` is abnormal and `j≠i`, then player `i`
strictly benefits when `j` quits alone: `rʲ_i>0`. -/
theorem lemma2_6
    (table : Table ι) (hnormalized : SoloExitNormalized table)
    (hbounded : TablePayoffsBounded table) {who owner : ι}
    (habnormal : ¬IsNormalPlayer table who) (hne : owner ≠ who) :
    0 < table.terminal (quittingProjectiveSingletonTerminal owner) who := by
  by_contra hpositive
  have howner :
      table.terminal (quittingProjectiveSingletonTerminal owner) who ≤ 0 :=
    le_of_not_gt hpositive
  apply habnormal
  unfold IsNormalPlayer
  refine le_of_forall_pos_le_add fun ε hε => ?_
  let p : ℝ := min (ε / 2) 1
  have hp : 0 < p := by
    change 0 < min (ε / 2) 1
    exact lt_min (half_pos hε) zero_lt_one
  have hp0 : 0 ≤ p := hp.le
  have hp1 : p ≤ 1 := min_le_right _ _
  have hpε : 2 * p ≤ ε := by
    have := min_le_left (ε / 2) 1
    linarith
  let hazard := quittingHazardCoin p hp0 hp1
  have hhazard : 0 < (hazard true).toReal := by
    simpa only [hazard, quittingHazardCoin_true_toReal] using hp
  have hcap := quittingPunishmentValue_le_stationaryUnilateralCap
    table.zeroNeverReward who (quittingSoloStationaryRoot owner hazard)
  rw [table.punishmentValue_eq_add_never]
  calc
    quittingPunishmentValue table.zeroNeverReward who + table.never who ≤
        quittingStationaryUnilateralCap table.zeroNeverReward
            (quittingSoloStationaryRoot owner hazard) who +
          table.never who := by linarith
    _ ≤ ε := by
      rw [quittingStationaryUnilateralCap_solo_other table.zeroNeverReward
          hne.symm hazard hhazard,
        quittingStationaryFixedOpponentsQuitValue_solo_other_eq_mix
          table.zeroNeverReward hne.symm hazard]
      simp only [hazard, quittingHazardCoin_false_toReal,
        quittingHazardCoin_true_toReal]
      unfold quittingSoloReward quittingSingletonCollisionReward
        QuittingPayoffTable.zeroNeverReward
      have hsolo : table.terminal ⟨{who}, by simp⟩ who = 0 := by
        simpa only [quittingProjectiveSingletonTerminal] using hnormalized who
      have howner' : table.terminal ⟨{owner}, by simp⟩ who ≤ 0 := by
        simpa only [quittingProjectiveSingletonTerminal] using howner
      rw [hsolo]
      have hcollision :
          table.terminal ⟨{owner, who}, by simp⟩ who ≤ 1 :=
        (le_abs_self _).trans (hbounded.1 _ who)
      rw [← max_add_add_right, max_le_iff]
      constructor <;> nlinarith
    _ = 0 + ε := by ring

/-! **Lemma 2.7 (paper).** If every player is abnormal, a stationary
`ε`-equilibrium exists for every positive `ε`. -/
theorem lemma2_7
    (table : Table ι) (hnormalized : SoloExitNormalized table)
    (hbounded : TablePayoffsBounded table)
    (habnormal : AllPlayersAbnormal table) :
    StationaryEpsilonEquilibria table := by
  have hlayer : normalLayer
      (normalizedSoloMatrix table.zeroNeverReward) 1 = ∅ := by
    ext who
    simp only [normalLayer, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨owner, hne, hnonpositive⟩
      have hnotmem : who ∉ NormalPlayers table := by
        rw [habnormal]
        simp
      have habnormalWho : ¬IsNormalPlayer table who := by
        simpa only [mem_normalPlayers_iff] using hnotmem
      have hpositive := lemma2_6 table hnormalized hbounded
        habnormalWho hne
      have hmatrix := congr_fun
        (congr_fun
          (normalizedSoloMatrix_zeroNeverReward_eq_singletonMatrix
            table hnormalized) who) owner
      rw [hmatrix] at hnonpositive
      exact False.elim ((not_lt_of_ge hnonpositive) hpositive)
    · simp
  obtain ⟨value, hvalue⟩ :=
    exists_stationaryUniformEquilibriumPayoff_of_normalLayer_one_eq_empty
      table.zeroNeverReward hlayer
  change table.StationaryεEquilibriumExistence
  rw [QuittingPayoffTable.stationaryεEquilibriumExistence_iff]
  exact hvalue.hasApproximateEquilibria

/-! The payoff to `who` from the paper's distribution over unilateral
quittings by normal players. -/
def NormalMixturePayoff (table : Table ι)
    (weight : stdSimplex ℝ (NormalPlayer table)) (who : ι) : ℝ :=
  wsum weight fun owner =>
    table.terminal (quittingProjectiveSingletonTerminal owner.1) who

/-! Zero-extension of a distribution on the paper's normal players to all
players. -/
def extendNormalPlayerWeight (table : Table ι)
    (weight : NormalPlayer table → ℝ) : ι → ℝ :=
  fun who => if hwho : who ∈ NormalPlayers table then
    weight ⟨who, hwho⟩ else 0

@[simp] theorem extendNormalPlayerWeight_of_mem
    (table : Table ι) (weight : NormalPlayer table → ℝ)
    {who : ι} (hwho : who ∈ NormalPlayers table) :
    extendNormalPlayerWeight table weight who = weight ⟨who, hwho⟩ := by
  simp [extendNormalPlayerWeight, hwho]

@[simp] theorem extendNormalPlayerWeight_of_notMem
    (table : Table ι) (weight : NormalPlayer table → ℝ)
    {who : ι} (hwho : who ∉ NormalPlayers table) :
    extendNormalPlayerWeight table weight who = 0 := by
  simp [extendNormalPlayerWeight, hwho]

/-! Zero-extension preserves nonnegativity and total mass one. -/
def extendNormalPlayerSimplex (table : Table ι)
    (weight : stdSimplex ℝ (NormalPlayer table)) : stdSimplex ℝ ι := by
  classical
  refine ⟨extendNormalPlayerWeight table weight.1, ?_, ?_⟩
  · intro who
    by_cases hwho : who ∈ NormalPlayers table
    · rw [extendNormalPlayerWeight_of_mem table weight.1 hwho]
      exact weight.2.1 ⟨who, hwho⟩
    · simp [extendNormalPlayerWeight, hwho]
  · calc
      (∑ who, extendNormalPlayerWeight table weight.1 who) =
          ∑ who ∈ NormalPlayers table,
            extendNormalPlayerWeight table weight.1 who := by
        symm
        apply Finset.sum_subset (Finset.subset_univ _)
        intro who _ hwho
        exact extendNormalPlayerWeight_of_notMem table weight.1 hwho
      _ = ∑ who : NormalPlayer table, weight.1 who := by
        calc
          (∑ who ∈ NormalPlayers table,
              extendNormalPlayerWeight table weight.1 who) =
              ∑ who : NormalPlayer table,
                extendNormalPlayerWeight table weight.1 who.1 :=
            Finset.sum_subtype (NormalPlayers table) (fun _ => Iff.rfl) _
          _ = ∑ who : NormalPlayer table, weight.1 who := by
            apply Finset.sum_congr rfl
            intro who _
            exact extendNormalPlayerWeight_of_mem table weight.1 who.2
      _ = 1 := weight.2.2

@[simp] theorem extendNormalPlayerSimplex_apply_of_mem
    (table : Table ι) (weight : stdSimplex ℝ (NormalPlayer table))
    {who : ι} (hwho : who ∈ NormalPlayers table) :
    (extendNormalPlayerSimplex table weight).1 who = weight.1 ⟨who, hwho⟩ := by
  simp [extendNormalPlayerSimplex, hwho]

@[simp] theorem extendNormalPlayerSimplex_apply_of_notMem
    (table : Table ι) (weight : stdSimplex ℝ (NormalPlayer table))
    {who : ι} (hwho : who ∉ NormalPlayers table) :
    (extendNormalPlayerSimplex table weight).1 who = 0 := by
  simp [extendNormalPlayerSimplex, hwho]

/-! On a normal coordinate, the full zero-extended singleton residual is
the mixture appearing in Lemma 2.8. -/
theorem singletonLCPResidual_extendNormalPlayerSimplex
    (table : Table ι) (hnormalized : SoloExitNormalized table)
    (weight : stdSimplex ℝ (NormalPlayer table))
    (who : NormalPlayer table) :
    singletonLCPResidual (normalizedSoloMatrix table.zeroNeverReward)
        (extendNormalPlayerSimplex table weight) who.1 =
      NormalMixturePayoff table weight who.1 := by
  classical
  unfold singletonLCPResidual NormalMixturePayoff wsum
  rw [normalizedSoloMatrix_zeroNeverReward_eq_singletonMatrix
    table hnormalized]
  calc
    (∑ owner,
        (extendNormalPlayerSimplex table weight).1 owner *
          table.singletonMatrix who.1 owner) =
        ∑ owner ∈ NormalPlayers table,
          (extendNormalPlayerSimplex table weight).1 owner *
            table.singletonMatrix who.1 owner := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro owner _ howner
      rw [extendNormalPlayerSimplex_apply_of_notMem table weight howner,
        zero_mul]
    _ = ∑ owner : NormalPlayer table,
        weight.1 owner * table.singletonMatrix who.1 owner.1 := by
      calc
        (∑ owner ∈ NormalPlayers table,
            (extendNormalPlayerSimplex table weight).1 owner *
              table.singletonMatrix who.1 owner) =
            ∑ owner : NormalPlayer table,
              (extendNormalPlayerSimplex table weight).1 owner.1 *
                table.singletonMatrix who.1 owner.1 :=
          Finset.sum_subtype (NormalPlayers table) (fun _ => Iff.rfl) _
        _ = ∑ owner : NormalPlayer table,
            weight.1 owner * table.singletonMatrix who.1 owner.1 := by
          apply Finset.sum_congr rfl
          intro owner _
          rw [extendNormalPlayerSimplex_apply_of_mem
            table weight owner.2]
    _ = ∑ owner : NormalPlayer table,
        weight.1 owner *
          table.terminal (quittingProjectiveSingletonTerminal owner.1)
            who.1 := by
      apply Finset.sum_congr rfl
      intro owner _
      rfl

/-! **Lemma 2.8 (paper).** A distribution over normal players whose mixture
payoff is nonnegative in every normal coordinate, and zero on every used
coordinate, yields stationary approximate equilibria. The displayed proof
misses the case where the distribution is concentrated on one player: then
that player's deviation to Continue leaves the game unabsorbed. The final
hypothesis is the exact missing condition in that case; it is vacuous for a
nonvertex distribution. -/
theorem lemma2_8
    (table : Table ι) (hnormalized : SoloExitNormalized table)
    (hbounded : TablePayoffsBounded table)
    (weight : stdSimplex ℝ (NormalPlayer table))
    (hnonnegative : ∀ who : NormalPlayer table,
      0 ≤ NormalMixturePayoff table weight who.1)
    (hcomplementary : ∀ who : NormalPlayer table,
      0 < weight.1 who → NormalMixturePayoff table weight who.1 = 0)
    (hvertexNever : ∀ owner : NormalPlayer table,
      weight.1 owner = 1 → table.never owner.1 ≤ 0) :
    StationaryEpsilonEquilibria table := by
  classical
  let fullWeight := extendNormalPlayerSimplex table weight
  have hfullResidual : ∀ who,
      0 ≤ singletonLCPResidual
        (normalizedSoloMatrix table.zeroNeverReward) fullWeight who := by
    intro who
    by_cases hwho : who ∈ NormalPlayers table
    · rw [singletonLCPResidual_extendNormalPlayerSimplex
        table hnormalized weight ⟨who, hwho⟩]
      exact hnonnegative ⟨who, hwho⟩
    · rw [normalizedSoloMatrix_zeroNeverReward_eq_singletonMatrix
        table hnormalized]
      unfold singletonLCPResidual wsum
      apply Finset.sum_nonneg
      intro owner _
      by_cases howner : owner ∈ NormalPlayers table
      · have hne : owner ≠ who := fun heq => hwho (heq ▸ howner)
        exact mul_nonneg (fullWeight.2.1 owner)
          (lemma2_6 table hnormalized hbounded
            (by simpa only [mem_normalPlayers_iff] using hwho) hne).le
      · change 0 ≤ (extendNormalPlayerSimplex table weight).1 owner * _
        rw [extendNormalPlayerSimplex_apply_of_notMem
          table weight howner, zero_mul]
  have hfullComplementary : ∀ who,
      fullWeight.1 who * singletonLCPResidual
        (normalizedSoloMatrix table.zeroNeverReward) fullWeight who = 0 := by
    intro who
    by_cases hwho : who ∈ NormalPlayers table
    · rw [singletonLCPResidual_extendNormalPlayerSimplex
        table hnormalized weight ⟨who, hwho⟩,
      extendNormalPlayerSimplex_apply_of_mem table weight hwho]
      by_cases hweight : weight.1 ⟨who, hwho⟩ = 0
      · rw [hweight, zero_mul]
      · have hpositive : 0 < weight.1 ⟨who, hwho⟩ :=
          lt_of_le_of_ne (weight.2.1 _) (Ne.symm hweight)
        rw [hcomplementary ⟨who, hwho⟩ hpositive, mul_zero]
    · rw [extendNormalPlayerSimplex_apply_of_notMem
        table weight hwho, zero_mul]
  change table.StationaryεEquilibriumExistence
  rw [QuittingPayoffTable.stationaryεEquilibriumExistence_iff]
  by_cases hvertex : ∃ owner, fullWeight.1 owner = 1
  · obtain ⟨owner, howner⟩ := hvertex
    have hownerMem : owner ∈ NormalPlayers table := by
      by_contra hnot
      have hzero := extendNormalPlayerSimplex_apply_of_notMem
        table weight hnot
      rw [howner] at hzero
      norm_num at hzero
    have hownerWeight : weight.1 ⟨owner, hownerMem⟩ = 1 := by
      rw [← extendNormalPlayerSimplex_apply_of_mem
        table weight hownerMem]
      exact howner
    have hnever : table.never owner ≤ 0 :=
      hvertexNever ⟨owner, hownerMem⟩ hownerWeight
    have hcolumn : ∀ who,
        0 ≤ table.terminal (quittingProjectiveSingletonTerminal owner) who := by
      intro who
      have hresidual := hfullResidual who
      rw [singletonLCPResidual_eq_column_of_weight_eq_one
        (normalizedSoloMatrix table.zeroNeverReward) fullWeight howner who,
        normalizedSoloMatrix_zeroNeverReward_eq_singletonMatrix
          table hnormalized] at hresidual
      exact hresidual
    intro ε hε
    let p : ℝ := min ε 1
    have hp : 0 < p := by
      change 0 < min ε 1
      exact lt_min hε zero_lt_one
    have hp1 : p ≤ 1 := min_le_right _ _
    have hpε : p ≤ ε := min_le_left _ _
    let hazard := quittingHazardCoin p hp.le hp1
    have hhazard : 0 < (hazard true).toReal := by
      simpa only [hazard, quittingHazardCoin_true_toReal] using hp
    refine ⟨quittingSoloStationaryRoot owner hazard, ?_⟩
    intro who deviation
    have hdeviation := quittingTerminalPayoff_update_stationary_le_cap
      table.zeroNeverReward (quittingSoloStationaryRoot owner hazard)
        who deviation
    rw [quittingTerminalPayoff_soloStationary table.zeroNeverReward
      owner who hazard hhazard]
    refine hdeviation.trans ?_
    by_cases hwho : who = owner
    · subst who
      rw [quittingStationaryUnilateralCap_solo_owner]
      unfold quittingSoloReward QuittingPayoffTable.zeroNeverReward
      have hsolo : table.terminal ⟨{owner}, by simp⟩ owner = 0 := by
        simpa only [quittingProjectiveSingletonTerminal] using
          hnormalized owner
      rw [hsolo]
      exact max_le (le_add_of_nonneg_right hε.le) (by linarith)
    · rw [quittingStationaryUnilateralCap_solo_other
          table.zeroNeverReward hwho hazard hhazard,
        quittingStationaryFixedOpponentsQuitValue_solo_other_eq_mix
          table.zeroNeverReward hwho hazard]
      simp only [hazard, quittingHazardCoin_false_toReal,
        quittingHazardCoin_true_toReal]
      unfold quittingSoloReward quittingSingletonCollisionReward
        QuittingPayoffTable.zeroNeverReward
      have hsolo : table.terminal ⟨{who}, by simp⟩ who = 0 := by
        simpa only [quittingProjectiveSingletonTerminal] using
          hnormalized who
      have hcollision : table.terminal ⟨{owner, who}, by simp⟩ who ≤ 1 :=
        (le_abs_self _).trans (hbounded.1 _ who)
      have hownerColumn : 0 ≤ table.terminal ⟨{owner}, by simp⟩ who := by
        simpa only [quittingProjectiveSingletonTerminal] using hcolumn who
      rw [hsolo, max_le_iff]
      constructor <;> nlinarith
  · have hnonvertex : ∀ who, fullWeight.1 who < 1 := by
      intro who
      have hle : fullWeight.1 who ≤ 1 := by
        rw [← fullWeight.2.2]
        exact Finset.single_le_sum
          (fun owner _ => fullWeight.2.1 owner) (Finset.mem_univ who)
      exact lt_of_le_of_ne hle (fun heq => hvertex ⟨who, heq⟩)
    exact
      (isQuittingStationaryUniformEquilibriumPayoff_of_nonvertexHomogeneousWitness
        table.zeroNeverReward fullWeight hfullResidual hfullComplementary
        hnonvertex).hasApproximateEquilibria

/-! **Remark 2.9 (paper).** For an `n×n` matrix `R` and `q`, the
paper recalls the textbook LCP: find `w,z ≥ 0` with `w=q+Rz` and
`w_i z_i=0`. -/

/-! The paper's projective LCP `LCP(M,q)` is solvable. -/
abbrev LCP (M : ι → ι → ℝ) (q : ι → ℝ) : Prop :=
  HasProjectiveLCPSolution M q

/-! **Definition 2.10 (paper).** `R` is a Q-matrix when the paper's
projective/simplex LCP `LCP(R,q)` has a solution for every `q`. -/

/-! `QMatrix M ↔ ∀q, LCP(M,q)` is solvable. -/
abbrev QMatrix (M : ι → ι → ℝ) : Prop := IsProjectiveQMatrix M

/-! **Example 2.11 (paper).** For the displayed cyclic `3×3` sign pattern
with zero diagonal, Berman--Plemmons implies Q iff the determinant is
positive. This numerical example is retained here as paper text; no
repository matrix-example declaration is introduced. -/

/-! **Lemma 2.12 (paper, repaired vertex case).** If the projective LCP with
right-hand side zero has a solution with `z₀<1`, then a stationary
ε-equilibrium exists for every positive ε. As in Lemma 2.8, the manuscript's
one-vertex construction also needs the nontermination payoff of a normal
owner to be nonpositive. -/

/-! Lemma 2.12: a zero-LCP solution with cemetery weight `<1` yields
stationary ε-equilibria for every `ε>0`. -/
theorem lemma2_12
    (table : Table ι) (hnormalized : SoloExitNormalized table)
    (hbounded : TablePayoffsBounded table)
    (hnormalNever : ∀ owner : NormalPlayer table, table.never owner.1 ≤ 0)
    (h : HasNontrivialZeroProjectiveLCPSolution
      (NormalMatrix table)) :
    StationaryEpsilonEquilibria table := by
  rw [hasNontrivialZeroProjectiveLCPSolution_iff_homogeneous] at h
  obtain ⟨weight, hnonnegative, hcomplementary⟩ := h
  apply lemma2_8 table hnormalized hbounded weight
  · intro who
    exact hnonnegative who
  · intro who hpositive
    have hproduct := hcomplementary who
    change weight.1 who * NormalMixturePayoff table weight who.1 = 0 at hproduct
    exact (mul_eq_zero.mp hproduct).resolve_left hpositive.ne'
  · intro owner _
    exact hnormalNever owner

/-! Extend a right-hand side on the min--max normal players by the fixed
positive value one on abnormal coordinates, as in the proof of Theorem
2.13(1). -/
def extendNormalPlayerDirection (table : Table ι)
    (q : NormalPlayer table → ℝ) : ι → ℝ :=
  fun who => if hwho : who ∈ NormalPlayers table then q ⟨who, hwho⟩ else 1

@[simp] theorem extendNormalPlayerDirection_of_mem
    (table : Table ι) (q : NormalPlayer table → ℝ)
    {who : ι} (hwho : who ∈ NormalPlayers table) :
    extendNormalPlayerDirection table q who = q ⟨who, hwho⟩ := by
  simp [extendNormalPlayerDirection, hwho]

@[simp] theorem extendNormalPlayerDirection_of_notMem
    (table : Table ι) (q : NormalPlayer table → ℝ)
    {who : ι} (hwho : who ∉ NormalPlayers table) :
    extendNormalPlayerDirection table q who = 1 := by
  simp [extendNormalPlayerDirection, hwho]

/-! Restrict a full projective solution whose positive singleton support is
normal to the paper's principal normal-player matrix. -/
def restrictProjectiveLCPSolutionToNormalPlayers
    (table : Table ι) (hnormalized : SoloExitNormalized table)
    (q : NormalPlayer table → ℝ)
    (solution : ProjectiveLCPSolution
      (normalizedSoloMatrix table.zeroNeverReward)
      (extendNormalPlayerDirection table q))
    (hsupport : ∀ who, 0 < solution.singleton who →
      who ∈ NormalPlayers table) :
    ProjectiveLCPSolution (NormalMatrix table) q := by
  classical
  have hzeroOff : ∀ who, who ∉ NormalPlayers table →
      solution.singleton who = 0 := by
    intro who hwho
    by_contra hne
    have hpositive : 0 < solution.singleton who :=
      lt_of_le_of_ne (solution.singleton_nonneg who) (Ne.symm hne)
    exact hwho (hsupport who hpositive)
  have hsumRestrict (f : ι → ℝ)
      (hoff : ∀ who, who ∉ NormalPlayers table → f who = 0) :
      (∑ who, f who) = ∑ who : NormalPlayer table, f who.1 := by
    calc
      (∑ who, f who) = ∑ who ∈ NormalPlayers table, f who := by
        symm
        apply Finset.sum_subset (Finset.subset_univ _)
        intro who _ hwho
        exact hoff who hwho
      _ = ∑ who : NormalPlayer table, f who.1 :=
        Finset.sum_subtype (NormalPlayers table) (fun _ => Iff.rfl) f
  refine
    { cemetery := solution.cemetery
      singleton := fun who => solution.singleton who.1
      cemetery_nonneg := solution.cemetery_nonneg
      singleton_nonneg := fun who => solution.singleton_nonneg who.1
      total := ?_
      residual_nonneg := ?_
      complementary := ?_ }
  · calc
      solution.cemetery +
          ∑ who : NormalPlayer table, solution.singleton who.1 =
          solution.cemetery + ∑ who, solution.singleton who := by
        rw [hsumRestrict solution.singleton hzeroOff]
      _ = 1 := solution.total
  · intro who
    have h := solution.residual_nonneg who.1
    rw [extendNormalPlayerDirection_of_mem table q who.2] at h
    have hmatrix (row owner : ι) :
        normalizedSoloMatrix table.zeroNeverReward row owner =
          table.singletonMatrix row owner := by
      exact congr_fun (congr_fun
        (normalizedSoloMatrix_zeroNeverReward_eq_singletonMatrix
          table hnormalized) row) owner
    simp_rw [hmatrix] at h
    change 0 ≤ solution.cemetery * q who +
      ∑ owner : NormalPlayer table,
        solution.singleton owner.1 *
          table.singletonMatrix who.1 owner.1
    calc
      0 ≤ solution.cemetery * q who +
          ∑ owner, solution.singleton owner *
            table.singletonMatrix who.1 owner := h
      _ = solution.cemetery * q who +
          ∑ owner : NormalPlayer table,
            solution.singleton owner.1 *
              table.singletonMatrix who.1 owner.1 := by
        congr 1
        exact hsumRestrict
          (fun owner => solution.singleton owner *
            table.singletonMatrix who.1 owner)
          (fun owner howner => by rw [hzeroOff owner howner, zero_mul])
  · intro who
    have h := solution.complementary who.1
    rw [extendNormalPlayerDirection_of_mem table q who.2] at h
    have hmatrix (row owner : ι) :
        normalizedSoloMatrix table.zeroNeverReward row owner =
          table.singletonMatrix row owner := by
      exact congr_fun (congr_fun
        (normalizedSoloMatrix_zeroNeverReward_eq_singletonMatrix
          table hnormalized) row) owner
    simp_rw [hmatrix] at h
    change solution.singleton who.1 *
      (solution.cemetery * q who +
        ∑ owner : NormalPlayer table,
          solution.singleton owner.1 *
            table.singletonMatrix who.1 owner.1) = 0
    rw [← hsumRestrict
      (fun owner => solution.singleton owner *
        table.singletonMatrix who.1 owner)
      (fun owner howner => by rw [hzeroOff owner howner, zero_mul])]
    exact h

/-! **Theorem 2.13 (paper).** Assume the normal-player set is nonempty and
the zero-right-hand-side projective LCP has no nontrivial solution. If the
normal-player matrix is not Q, then ordinary ε-equilibria exist for every
positive ε. If it is Q, then a sunspot ε-equilibrium exists for every
positive ε in which at most one player quits with positive probability at
each stage. The paper-local public-signal relation is the
`SunspotProfile` relation above. -/

/-! Theorem 2.13(1): the non-Q branch yields ordinary ε-equilibria. The
paper does not claim stationarity here; that stronger conclusion belongs to
the alpha-player variant in Theorem 5.1. -/
theorem theorem2_13_nonQ
    (table : Table ι)
    (hnormalized : SoloExitNormalized table)
    (hbounded : TablePayoffsBounded table)
    (_hnormal : HasNormalPlayers table)
    (_hzero : ¬HasNontrivialZeroProjectiveLCPSolution
      (NormalMatrix table))
    (hnotQ : ¬QMatrix (NormalMatrix table)) :
    ∀ ε : ℝ, 0 < ε →
      ∃ profile : (quittingGame table.terminal).BehaviorProfile,
        EpsilonEquilibrium table ε profile := by
  classical
  let reward := table.zeroNeverReward
  obtain ⟨q, hno⟩ := exists_direction_without_projectiveLCPSolution
    (NormalMatrix table) hnotQ
  let qfull := extendNormalPlayerDirection table q
  obtain ⟨g⟩ := nonempty_analyticBellmanGerm_quittingGame
    (quittingRewardShift reward (fun who =>
      QuittingLCPClassification.quittingSoloBaseline reward who + qfull who))
  have hmassLe : quittingStationaryContinueMass
      (g.endpointProfile none) ≤ 1 :=
    quittingStationaryContinueMass_le_one (g.endpointProfile none)
  have hzeroGame : ∀ ε : ℝ, 0 < ε →
      ∃ profile : (quittingGame reward).BehaviorProfile,
        (quittingGame reward).IsεAsymptoticNash
          (quittingTerminalPayoff reward) ε profile := by
    intro ε hε
    rcases lt_or_eq_of_le hmassLe with habsorbs | hcontinue
    · rcases two_positive_or_isolated_of_continueMass_lt_one
          (g.endpointProfile none) habsorbs with htwo | hisolated
      · have hcontracts := fixedOpponents_contract_of_two_positive
          (g.endpointProfile none) htwo
        have hvalue :=
          isQuittingStationaryUniformEquilibriumPayoff_of_shiftedGerm_absorbingEndpoint
            reward (fun who =>
              QuittingLCPClassification.quittingSoloBaseline reward who +
                qfull who) g habsorbs hcontracts
        obtain ⟨root, hnash, _⟩ := hvalue ε hε
        exact ⟨quittingStationaryProfile reward root, hnash⟩
      · obtain ⟨owner, howner, hother⟩ := hisolated
        have hownerNormal : IsNormalPlayer table owner := by
          by_contra habnormal
          have hownerNotMem : owner ∉ NormalPlayers table := by
            simpa only [mem_normalPlayers_iff]
          have hqfull : 0 < qfull owner := by
            rw [show qfull owner = 1 by
              exact extendNormalPlayerDirection_of_notMem
                table q hownerNotMem]
            norm_num
          obtain ⟨blocker, hne, hentry⟩ :=
            exists_normalizedSoloMatrix_blocker_of_isolated_endpoint
              reward qfull g owner howner hother hqfull
          have hmatrix := congr_fun (congr_fun
            (normalizedSoloMatrix_zeroNeverReward_eq_singletonMatrix
              table hnormalized) owner) blocker
          rw [show reward = table.zeroNeverReward by rfl, hmatrix] at hentry
          have hpositive := lemma2_6 table hnormalized hbounded
            habnormal hne
          exact (not_lt_of_ge hentry) hpositive
        let root := g.endpointProfile none
        let hazard := root owner
        have hroot : root = quittingSoloStationaryRoot owner hazard :=
          eq_quittingSoloStationaryRoot_of_others_continue hother
        let target := quittingPayoffUnshift (fun who =>
          QuittingLCPClassification.quittingSoloBaseline reward who +
            qfull who) (quittingGermValue g 0)
        have hfixedShift := quittingGerm_endpoint_fixedPoint g
        have hfixed : target =
            quittingRootSuccessorPayoff reward target root :=
          quittingRootFixedPoint_unshift reward (fun who =>
            QuittingLCPClassification.quittingSoloBaseline reward who +
              qfull who)
            (quittingGermValue g 0) root hfixedShift
        have hnashEndpoint : IsεQuittingRootEndpointNash
            reward target 0 root :=
          (isεQuittingRootEndpointNash_zero_shift_iff reward (fun who =>
            QuittingLCPClassification.quittingSoloBaseline reward who +
              qfull who)
            (quittingGermValue g 0) root).mp
              (quittingGerm_endpoint_endpointNash g)
        have hnashRoot : IsεQuittingRootNash reward target 0 root :=
          (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
            reward target root).mp hnashEndpoint
        let cycle : Fin 1 → ι → PMF Bool := fun _ => root
        let value : Fin 1 → Payoff ι := fun _ => target
        have hpolicy : ∀ phase : Fin 1,
            value phase = quittingRootSuccessorPayoff reward
              (value (finRotate 1 phase)) (cycle phase) := by
          intro phase
          simpa only [value, cycle] using hfixed
        have hnash : ∀ phase : Fin 1,
            IsεQuittingRootNash reward
              (value (finRotate 1 phase)) 0 (cycle phase) := by
          intro phase
          simpa only [value, cycle] using hnashRoot
        have hcycleAbsorbs :
            (∏ phase : Fin 1,
              quittingStationaryContinueMass (cycle phase)) < 1 := by
          simpa only [cycle, Fin.prod_univ_one] using habsorbs
        have hadmissible :
            IsQuittingCyclePunishmentAdmissible reward cycle := by
          intro who
          unfold IsQuittingCyclePunishmentAdmissibleAt
          by_cases hwho : who = owner
          · subst who
            right
            have hpunishment := hownerNormal
            unfold IsNormalPlayer at hpunishment
            rw [table.punishmentValue_eq_add_never] at hpunishment
            change quittingPunishmentValue table.zeroNeverReward owner ≤
              table.zeroNeverReward
                (quittingSingletonTerminal owner) owner
            unfold QuittingPayoffTable.zeroNeverReward
            have hsolo : table.terminal
                (quittingSingletonTerminal owner) owner = 0 := by
              simpa [quittingSingletonTerminal,
                quittingProjectiveSingletonTerminal] using hnormalized owner
            rw [hsolo]
            change quittingPunishmentValue
                (fun S who => table.terminal S who - table.never who)
                owner + table.never owner ≤ 0 at hpunishment
            linarith
          · left
            have hpositive : 0 < (hazard true).toReal := howner
            have hcontract :=
              quittingStationaryFixedOpponentsContinueMass_solo_other_lt_one
                hwho hazard hpositive
            rw [← hroot] at hcontract
            simpa only [cycle, Fin.prod_univ_one] using hcontract
        obtain ⟨profile, hnashProfile, _⟩ :=
          exists_isεAsymptoticNash_close_of_punishmentAdmissibleCycle
            reward cycle value 0 hpolicy hnash hcycleAbsorbs
              hadmissible hε
        exact ⟨profile, hnashProfile⟩
    · obtain ⟨normalOwner, hqnegative⟩ :=
        exists_negative_of_no_projectiveLCPSolution
          (NormalMatrix table) q hno
      have hnegative : qfull normalOwner.1 < 0 := by
        simpa only [qfull, extendNormalPlayerDirection_of_mem
          table q normalOwner.2] using hqnegative
      have hnotZero : ¬IsQuittingZeroSolo
          (quittingRewardShift reward (fun who =>
            QuittingLCPClassification.quittingSoloBaseline reward who +
              qfull who)) :=
        not_isQuittingZeroSolo_baselineShift_of_negative
          reward qfull hnegative
      rcases quittingGerm_allContinue_zeroSolo_or_supportedProjectivePacket
          (quittingRewardShift reward (fun who =>
            QuittingLCPClassification.quittingSoloBaseline reward who +
              qfull who)) g hcontinue with
        hzeroSolo | hsupported
      · exact False.elim (hnotZero hzeroSolo)
      · let solution : ProjectiveLCPSolution
            (normalizedSoloMatrix reward) qfull :=
          projectiveLCPSolutionOfBaselineShiftedPacket
            reward qfull hsupported.some.packet
        have hsupport : ∀ who, 0 < solution.singleton who →
            who ∈ NormalPlayers table := by
          intro who hpositive
          by_contra hnotNormal
          have habnormal : ¬IsNormalPlayer table who := by
            simpa only [mem_normalPlayers_iff] using hnotNormal
          have hactive : QuittingGermEventuallyActive g who :=
            hsupported.some.positive_eventuallyActive who (by
              simpa only [solution,
                projectiveLCPSolutionOfBaselineShiftedPacket_singleton]
                using hpositive)
          have hfixed : quittingStationaryFixedOpponentsContinueMass
              (g.endpointProfile none) who = 1 := by
            have hlower :=
              quittingStationaryContinueMass_le_fixedOpponentsContinueMass
                (g.endpointProfile none) who
            have hupper := quittingStationaryContinueMass_le_one
              (Function.update (g.endpointProfile none) who
                (PMF.pure false))
            change quittingStationaryFixedOpponentsContinueMass
              (g.endpointProfile none) who ≤ 1 at hupper
            linarith
          obtain ⟨data⟩ :=
            nonempty_quittingGermOpponentLeadingData g who
          have hqfull : 0 < qfull who := by
            rw [show qfull who = 1 by
              exact extendNormalPlayerDirection_of_notMem
                table q hnotNormal]
            norm_num
          obtain ⟨blocker, hweight, hentry⟩ :=
            exists_weighted_nonpositive_normalizedSoloMatrix_of_eventuallyActive
              reward qfull g who hfixed hactive data hqfull
          have hne : blocker ≠ who := by
            intro heq
            subst blocker
            rw [data.singletonWeight_self] at hweight
            exact (lt_irrefl 0) hweight
          have hmatrix := congr_fun (congr_fun
            (normalizedSoloMatrix_zeroNeverReward_eq_singletonMatrix
              table hnormalized) who) blocker
          rw [show reward = table.zeroNeverReward by rfl, hmatrix] at hentry
          have hpositiveEntry := lemma2_6 table hnormalized hbounded
            habnormal hne
          exact (not_lt_of_ge hentry) hpositiveEntry
        have hrestricted := restrictProjectiveLCPSolutionToNormalPlayers
          table hnormalized q solution (by
            simpa only [reward] using hsupport)
        exact False.elim (hno ⟨hrestricted⟩)
  intro ε hε
  obtain ⟨profile, hnash⟩ := hzeroGame ε hε
  refine ⟨profile, ?_⟩
  exact (table.isεAsymptoticNash_iff ε profile).2 hnash

/-! Theorem 2.13(2): the Q branch yields a unilateral-quitting sunspot
ε-equilibrium for every `ε>0`. -/
theorem theorem2_13_sunspot
    (table : Table ι)
    (hnormalized : SoloExitNormalized table)
    (hbounded : TablePayoffsBounded table)
    (hnormal : HasNormalPlayers table)
    (hzero : ¬HasNontrivialZeroProjectiveLCPSolution
      (NormalMatrix table))
    (hQ : QMatrix (NormalMatrix table)) :
    ∀ ε : ℝ, 0 < ε → ∃ profile : SunspotProfile table,
      SunspotEpsilonEquilibrium table ε profile ∧
      AtMostOneQuitter profile := by
  sorry

/-! ## Section 2.5 — example -/

/-! The paper gives a four-player example with
`r¹=(0,4,-1,-1)`, `r²=(4,0,-1,-1)`, `r³=(-1,-1,0,4)`, and
`r⁴=(-1,-1,4,0)`, then describes two public-signal constructions, with
identities (5)--(8), and concludes that the first construction is a sunspot
`ε`-equilibrium and the second a sunspot `5ε`-equilibrium. These are
construction-specific probability statements, so they remain paper notes
rather than generic repository declarations. -/

/-! ## Section 3 — proof of Theorem 2.13 -/

/-! **Section 3.1 (paper definitions).** The paper defines the
`λ`-discounted quitting game, its payoff `γ^λ`, stationary payoff formula (9),
λ-discounted equilibrium, and invokes Fink/Takahashi and Bewley--Kohlberg to
choose a semi-algebraic stationary equilibrium branch `λ ↦ x^λ` with a
limit. The checked carrier below uses the repository's analytic Bellman germ
after playerwise normalization of the nontermination payoff. -/

/-! Subtracting `r^∅` identifies the paper's discounted game with the
repository quitting game `quittingGame table.zeroNeverReward`, up to the
playerwise payoff constant `r^∅`. -/
abbrev DiscountedGame (table : Table ι) :=
  quittingGame table.zeroNeverReward

/-! A semi-algebraic stationary equilibrium branch on `(0,1)` with a limit
as `λ→0+`. -/
abbrev SemiAlgebraicSelection (table : Table ι) :=
  (DiscountedGame table).AnalyticBellmanGerm

/-! Existence of the paper's discounted-equilibrium selection. -/
abbrev HasSemiAlgebraicSelection (table : Table ι) : Prop :=
  Nonempty ((DiscountedGame table).AnalyticBellmanGerm)

/-! Fink/Takahashi plus Bewley--Kohlberg selection claim. -/
theorem discountedSelection
    (table : Table ι) : HasSemiAlgebraicSelection table :=
  nonempty_analyticBellmanGerm_quittingGame table.zeroNeverReward

/-! The displayed stationary formula (9) is the stationary specialization of
the Bellman values on this germ. The formal carrier uses the reusable checked
stochastic-game semantics rather than an unconstrained payoff field. -/

/-! **Lemma 3.2 (published paper).** For
`D = conv(r̂¹,…,r̂ⁿ) ∩ ℝⁿ_≥0`, if `q̂` is in the column hull but not
the nonnegative orthant, every solution `(w,z)` of `LCP(R̂,q̂)` has
`w ∈ D₀`. -/

/-! `ColumnConvexHull M = conv{M_{·i}:i∈I}`. -/
def ColumnConvexHull (M : ι → ι → ℝ) : Set (ι → ℝ) :=
  convexHull ℝ (Set.range fun owner => fun who => M who owner)

/-! `D = conv{r̂¹,…,r̂ⁿ} ∩ ℝ^n_≥0`. -/
def D (M : ι → ι → ℝ) : Set (ι → ℝ) :=
  ColumnConvexHull M ∩ {w | ∀ who, 0 ≤ w who}

/-! The source normalizes every payoff coordinate to `[-1,1]`. -/
def MatrixPayoffsBounded (M : ι → ι → ℝ) : Prop :=
  ∀ who owner, |M who owner| ≤ 1

/-! `D₀` consists of the points of `D` with a zero coordinate. The paper
only observes that this set lies in the relative boundary of `D`; replacing
it by the ambient frontier would be vacuous because `n` columns in `ℝⁿ`
have lower-dimensional convex hull. -/
def DZero (M : ι → ι → ℝ) (w : ι → ℝ) : Prop :=
  w ∈ D M ∧ ∃ who, w who = 0

omit [Fintype ι] [DecidableEq ι] in
theorem abs_le_one_of_mem_D
    {M : ι → ι → ℝ} (hbound : MatrixPayoffsBounded M)
    {value : ι → ℝ} (hvalue : value ∈ D M) (who : ι) :
    |value who| ≤ 1 := by
  let cube : Set (ι → ℝ) :=
    Set.univ.pi (fun _ => Set.Icc (-1 : ℝ) 1)
  have hcubeConvex : Convex ℝ cube := by
    exact convex_pi fun _ _ => convex_Icc (-1 : ℝ) 1
  have hcolumns : Set.range (fun owner => fun row => M row owner) ⊆ cube := by
    rintro value ⟨owner, rfl⟩ row _
    exact abs_le.mp (hbound row owner)
  have hcube : value ∈ cube :=
    convexHull_min hcolumns hcubeConvex hvalue.1
  exact abs_le.mpr (hcube who (Set.mem_univ who))

/-! The coordinatewise nonnegative orthant. -/
def NonnegativeOrthant (ι : Type) :=
  {w : ι → ℝ | ∀ who, 0 ≤ w who}

omit [DecidableEq ι] in
theorem isClosed_D (M : ι → ι → ℝ) : IsClosed (D M) := by
  apply IsClosed.inter
  · exact (Set.finite_range (fun owner => fun who => M who owner)).isClosed_convexHull ℝ
  · rw [show {w : ι → ℝ | ∀ who, 0 ≤ w who} =
        ⋂ who, {w | 0 ≤ w who} by ext; simp]
    exact isClosed_iInter fun who => isClosed_le
      (continuous_const : Continuous (fun _ : (ι → ℝ) => (0 : ℝ)))
      (continuous_apply who)

omit [Fintype ι] [DecidableEq ι] in
theorem convex_D (M : ι → ι → ℝ) : Convex ℝ (D M) := by
  apply (convex_convexHull ℝ _).inter
  rw [show {w : ι → ℝ | ∀ who, 0 ≤ w who} =
      ⋂ who, (LinearMap.proj (R := ℝ) who) ⁻¹' Set.Ici 0 by ext; simp]
  apply convex_iInter
  intro who
  exact (convex_Ici (𝕜 := ℝ) (0 : ℝ)).linear_preimage
    (LinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) who)

omit [Fintype ι] [DecidableEq ι] in
theorem mem_D_of_DZero {M : ι → ι → ℝ} {y : ι → ℝ}
    (hy : DZero M y) : y ∈ D M :=
  hy.1

omit [DecidableEq ι] in
private theorem frontier_nonnegativeOrthant_has_zero
    {w : ι → ℝ} (hw : w ∈ frontier (NonnegativeOrthant ι)) :
    w ∈ NonnegativeOrthant ι ∧ ∃ who, w who = 0 := by
  have hclosed : IsClosed (NonnegativeOrthant ι) := by
    rw [NonnegativeOrthant, show {x : ι → ℝ | ∀ who, 0 ≤ x who} =
      ⋂ who, {x | 0 ≤ x who} by ext; simp]
    exact isClosed_iInter fun who => isClosed_le
      (continuous_const : Continuous (fun _ : (ι → ℝ) => (0 : ℝ)))
      (continuous_apply who)
  have hwmem : w ∈ NonnegativeOrthant ι := hclosed.frontier_subset hw
  refine ⟨hwmem, ?_⟩
  by_contra hzero
  push Not at hzero
  have hpos : ∀ who, 0 < w who := fun who =>
    lt_of_le_of_ne (hwmem who) (Ne.symm (hzero who))
  have hwInterior : w ∈ interior (NonnegativeOrthant ι) := by
    have heq : {x : ι → ℝ | ∀ who, 0 ≤ x who} =
        Set.univ.pi (fun _ => Set.Ici 0) := by
      ext x
      constructor
      · intro hx who _
        exact hx who
      · intro hx who
        exact hx who (Set.mem_univ who)
    rw [NonnegativeOrthant, heq, interior_pi_set Set.finite_univ,
      Set.mem_pi]
    intro who _
    simpa only [interior_Ici, Set.mem_Ioi] using hpos who
  exact (mem_frontier_iff_notMem_interior hwmem).1 hw hwInterior

private theorem exists_frontier_on_segment_of_mem_notMem
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : Set E} {u v : E} (hu : u ∈ s) (hv : v ∉ s) :
    ∃ w ∈ segment ℝ u v, w ∈ frontier s := by
  by_contra hnone
  push Not at hnone
  have havoid : segment ℝ u v ⊆ (frontier s)ᶜ := fun w hw => hnone w hw
  rw [compl_frontier_eq_union_interior] at havoid
  have huInterior : u ∈ interior s := by
    by_contra huNot
    exact hnone u (left_mem_segment ℝ u v)
      ((mem_frontier_iff_notMem_interior hu).2 huNot)
  have hvInterior : v ∈ interior sᶜ := by
    by_contra hvNot
    exact hnone v (right_mem_segment ℝ u v) <| by
      rw [← frontier_compl]
      exact (mem_frontier_iff_notMem_interior (show v ∈ sᶜ from hv)).2 hvNot
  have hdisjoint : Disjoint (interior s) (interior sᶜ) :=
    (Set.disjoint_compl_right_iff_subset.mpr fun _ hx => hx).mono
      interior_subset interior_subset
  have hsubset :=
    (convex_segment u v).isPreconnected.subset_left_of_subset_union
      isOpen_interior isOpen_interior hdisjoint havoid
      ⟨u, left_mem_segment ℝ u v, huInterior⟩
  exact hv (interior_subset (hsubset (right_mem_segment ℝ u v)))

private theorem endpoint_not_mem_tail_segment
    {E : Type*} [AddCommGroup E] [Module ℝ E] {y p c : E}
    (hp : p ∈ segment ℝ y c) (hpy : p ≠ y) (hcy : c ≠ y) :
    y ∉ segment ℝ p c := by
  rw [segment_eq_image_lineMap] at hp ⊢
  obtain ⟨t, ht, rfl⟩ := hp
  rintro ⟨s, hs, heq⟩
  have htpos : 0 < t := by
    apply lt_of_le_of_ne ht.1
    intro htzero
    apply hpy
    rw [← htzero]
    simp [AffineMap.lineMap_apply_module]
  have hcoeff : 0 < s + (1 - s) * t := by
    have hs0 := hs.1
    have hs1 := hs.2
    by_cases hspos : 0 < s
    · positivity
    · have hs0eq : s = 0 := le_antisymm (le_of_not_gt hspos) hs0
      rw [hs0eq]
      simpa using htpos
  have hv : (s + (1 - s) * t) • (c - y) = 0 := by
    rw [AffineMap.lineMap_apply_module, AffineMap.lineMap_apply_module] at heq
    linear_combination (norm := module) heq
  have hcsub : c - y = 0 :=
    (smul_eq_zero.mp hv).resolve_left (ne_of_gt hcoeff)
  exact hcy (sub_eq_zero.mp hcsub)

/-! **Lemma 3.1 (paper).** If the homogeneous projective LCP has no
nontrivial solution, no singleton column lies in the nonnegative orthant. -/
omit [DecidableEq ι] in
theorem lemma3_1
    (M : ι → ι → ℝ) (hdiag : ∀ who, M who who = 0)
    (hzero : ¬HasNontrivialZeroProjectiveLCPSolution M) (owner : ι) :
    (fun who => M who owner) ∉ NonnegativeOrthant ι := by
  intro hcolumn
  apply hzero
  rw [hasNontrivialZeroProjectiveLCPSolution_iff_homogeneous]
  exact singletonLCPFeasible_of_diag_eq_zero owner (hdiag owner) hcolumn

/-! Lemma 3.2: `q∈conv{r̂ᶦ} ∖ ℝⁿ_≥0` forces every LCP residual into
`D₀`. -/
omit [DecidableEq ι] in
theorem lemma3_2
    (M : ι → ι → ℝ) (q : ι → ℝ)
    (hq : q ∈ ColumnConvexHull M)
    (hqNegative : q ∉ NonnegativeOrthant ι)
    (solution : ProjectiveLCPSolution M q) :
    DZero M (fun who => solution.cemetery * q who +
      ∑ owner, solution.singleton owner * M who owner) := by
  let weight : Option ι → ℝ
    | none => solution.cemetery
    | some i => solution.singleton i
  let point : Option ι → (ι → ℝ)
    | none => q
    | some i => fun who => M who i
  have hweight_nonneg (a : Option ι) : 0 ≤ weight a := by
    cases a with
    | none => exact solution.cemetery_nonneg
    | some i => exact solution.singleton_nonneg i
  have hweight_total : ∑ a : Option ι, weight a = 1 := by
    simp [weight, solution.total]
  have hpoint (a : Option ι) : point a ∈ ColumnConvexHull M := by
    cases a with
    | none => exact hq
    | some i => exact subset_convexHull ℝ _ ⟨i, rfl⟩
  have hconvex : (∑ a : Option ι, weight a • point a) ∈
      ColumnConvexHull M := by
    exact (convex_convexHull ℝ _).sum_mem
      (fun a _ => hweight_nonneg a) hweight_total (fun a _ => hpoint a)
  have hresidual : (fun who => solution.cemetery * q who +
      ∑ owner, solution.singleton owner * M who owner) ∈
      ColumnConvexHull M := by
    convert hconvex using 1
    funext who
    simp [weight, point, smul_eq_mul]
  have hwD : (fun who => solution.cemetery * q who +
      ∑ owner, solution.singleton owner * M who owner) ∈ D M :=
    ⟨hresidual, solution.residual_nonneg⟩
  have hsumNonneg : 0 ≤ ∑ owner, solution.singleton owner :=
    Finset.sum_nonneg fun owner _ => solution.singleton_nonneg owner
  have hcemeteryLe : solution.cemetery ≤ 1 := by
    linarith [solution.total]
  have hcemeteryLt : solution.cemetery < 1 := by
    apply lt_of_le_of_ne hcemeteryLe
    intro hcemetery
    have hsumZero : ∑ owner, solution.singleton owner = 0 := by
      linarith [solution.total]
    have hsingletonZero (owner : ι) : solution.singleton owner = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun i _ => solution.singleton_nonneg i)).mp hsumZero owner
        (Finset.mem_univ owner)
    apply hqNegative
    intro who
    simpa only [hcemetery, one_mul, hsingletonZero, zero_mul,
      Finset.sum_const_zero, add_zero] using solution.residual_nonneg who
  have hsumPositive : 0 < ∑ owner, solution.singleton owner := by
    linarith [solution.total]
  obtain ⟨who, _, hwho⟩ :=
    (Finset.sum_pos_iff_of_nonneg
      (fun i _ => solution.singleton_nonneg i)).mp hsumPositive
  refine ⟨hwD, who, ?_⟩
  exact (mul_eq_zero.mp (solution.complementary who)).resolve_left
    (ne_of_gt hwho)

/-! **Theorem 3.3 (published paper).** For every `y∈D₀` and `ε>0`,
there are `w∈D₀`, vectors `w¹,…,wⁿ`, and simplex weights `z`
satisfying (F.1)--(F.5).
The following paper-local structures spell out those five conditions. -/

/-! `Segment a b x` means `x∈conv{a,b}`. -/
def Segment (a b x : ι → ℝ) : Prop :=
  ∃ weight : ℝ, 0 ≤ weight ∧ weight ≤ 1 ∧
    ∀ who, x who = weight * a who + (1 - weight) * b who

omit [Fintype ι] [DecidableEq ι] in
private theorem segment_of_mem_segment {a b x : ι → ℝ}
    (hx : x ∈ segment ℝ a b) : Segment a b x := by
  rw [segment_eq_image_lineMap] at hx
  obtain ⟨t, ht, rfl⟩ := hx
  refine ⟨1 - t, sub_nonneg.mpr ht.2, by linarith [ht.1], ?_⟩
  intro who
  simp only [AffineMap.lineMap_apply_module, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul]
  ring

omit [Fintype ι] [DecidableEq ι] in
private theorem mem_segment_of_Segment {a b x : ι → ℝ}
    (hx : Segment a b x) : x ∈ segment ℝ a b := by
  obtain ⟨weight, hweight0, hweight1, hx⟩ := hx
  rw [segment_eq_image_lineMap]
  refine ⟨1 - weight, ⟨by linarith, by linarith⟩, ?_⟩
  ext who
  rw [hx]
  simp only [AffineMap.lineMap_apply_module, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul]
  ring

/-! `J_y={i:y_i=0}`. -/
def ZeroCoordinates (y : ι → ℝ) : Finset ι :=
  Finset.univ.filter (fun i => y i = 0)

/-! `SubfamilyHull M J = conv{M_{·i}:i∈J}`. -/
def SubfamilyHull (M : ι → ι → ℝ) (J : Finset ι) : Set (ι → ℝ) :=
  convexHull ℝ (Set.range fun i : J => fun who => M who i)

/-! Simplex weights `z=(z₀,zᵢ)` satisfy `z₀+Σᵢzᵢ=1`. -/
structure SimplexWeights (ι : Type) [Fintype ι] [DecidableEq ι] where
  cemetery : ℝ
  singleton : ι → ℝ
  cemetery_nonneg : 0 ≤ cemetery
  singleton_nonneg : ∀ i, 0 ≤ singleton i
  total : cemetery + ∑ i, singleton i = 1

/-! The lottery on `{0}∪I` represented by the paper's vector
`z=(z₀,(zᵢ)ᵢ)`. -/
def SimplexWeights.toStdSimplex (weight : SimplexWeights ι) :
    stdSimplex ℝ (Option ι) := by
  refine ⟨fun choice => match choice with
    | none => weight.cemetery
    | some owner => weight.singleton owner, ?_, ?_⟩
  · intro choice
    cases choice with
    | none => exact weight.cemetery_nonneg
    | some owner => exact weight.singleton_nonneg owner
  · rw [Fintype.sum_option]
    exact weight.total

/-! The corresponding finite public lottery. -/
noncomputable def SimplexWeights.toPMF (weight : SimplexWeights ι) :
    PMF (Option ι) :=
  Math.ProbabilityMassFunction.ofVector
    weight.toStdSimplex.1 weight.toStdSimplex.2

@[simp] theorem SimplexWeights.toPMF_none_toReal
    (weight : SimplexWeights ι) :
    (weight.toPMF none).toReal = weight.cemetery := by
  change ((Math.ProbabilityMassFunction.ofVector
    weight.toStdSimplex.1 weight.toStdSimplex.2) none).toReal = _
  rw [Math.ProbabilityMassFunction.ofVector_toReal]
  rfl

@[simp] theorem SimplexWeights.toPMF_some_toReal
    (weight : SimplexWeights ι) (owner : ι) :
    (weight.toPMF (some owner)).toReal = weight.singleton owner := by
  change ((Math.ProbabilityMassFunction.ofVector
    weight.toStdSimplex.1 weight.toStdSimplex.2) (some owner)).toReal = _
  rw [Math.ProbabilityMassFunction.ofVector_toReal]
  rfl

/-! Conditions (F.1)--(F.5) of the published Theorem 3.3 for `(M,y,ε)`.
The published condition (F.1) allows the segment containing `wⁱ` to start
at either `w` or `y`. This disjunction is essential in the second case of the
proof; the arXiv v1 statement omitted it even though its printed construction
uses the segment starting at `y`. -/
structure BuildingBlock (M : ι → ι → ℝ) (y : ι → ℝ) (ε : ℝ) where
  w : ι → ℝ
  wi : ι → ι → ℝ
  z : SimplexWeights ι
  y_boundary : DZero M y
  w_boundary : DZero M w
  approach : ∀ i,
    (Segment w (fun who => M who i) (wi i) ∧ wi i ≠ w) ∨
      (Segment y (fun who => M who i) (wi i) ∧ wi i ≠ y)
  lower : ∀ i who, -ε ≤ wi i who
  balance : ∀ who, w who = z.cemetery * y who +
    ∑ i, z.singleton i * wi i who
  complementary : ∀ i, z.singleton i > 0 → wi i i = 0
  nontrivial : 0 < ∑ i, z.singleton i

theorem BuildingBlock.wi_abs_le_one
    {M : ι → ι → ℝ} {y : ι → ℝ} {ε : ℝ}
    (block : BuildingBlock M y ε) (hbound : MatrixPayoffsBounded M)
    (owner who : ι) :
    |block.wi owner who| ≤ 1 := by
  rcases block.approach owner with
    ⟨⟨weight, hweight0, hweight1, hvalue⟩, _⟩ |
      ⟨⟨weight, hweight0, hweight1, hvalue⟩, _⟩
  · have hbase := abs_le_one_of_mem_D hbound block.w_boundary.1 who
    have hcolumn := hbound who owner
    rw [hvalue who]
    calc
      |weight * block.w who + (1 - weight) * M who owner| ≤
          |weight * block.w who| + |(1 - weight) * M who owner| :=
        abs_add_le _ _
      _ = weight * |block.w who| + (1 - weight) * |M who owner| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hweight0,
          abs_of_nonneg (sub_nonneg.mpr hweight1)]
      _ ≤ weight * 1 + (1 - weight) * 1 := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hbase hweight0)
          (mul_le_mul_of_nonneg_left hcolumn
            (sub_nonneg.mpr hweight1))
      _ = 1 := by ring
  · have hbase := abs_le_one_of_mem_D hbound block.y_boundary.1 who
    have hcolumn := hbound who owner
    rw [hvalue who]
    calc
      |weight * y who + (1 - weight) * M who owner| ≤
          |weight * y who| + |(1 - weight) * M who owner| :=
        abs_add_le _ _
      _ = weight * |y who| + (1 - weight) * |M who owner| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hweight0,
          abs_of_nonneg (sub_nonneg.mpr hweight1)]
      _ ≤ weight * 1 + (1 - weight) * 1 := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hbase hweight0)
          (mul_le_mul_of_nonneg_left hcolumn
            (sub_nonneg.mpr hweight1))
      _ = 1 := by ring

/-! Equation (14): `‖w(y)-y‖∞ ≤ 2 ∑ᵢ zᵢ(y)`. -/
theorem BuildingBlock.displacement_le_twice_singletonMass
    {M : ι → ι → ℝ} {y : ι → ℝ} {ε : ℝ}
    (block : BuildingBlock M y ε) (hbound : MatrixPayoffsBounded M) :
    dist y block.w ≤ 2 * ∑ owner, block.z.singleton owner := by
  have hmass : 0 ≤ ∑ owner, block.z.singleton owner :=
    Finset.sum_nonneg fun owner _ => block.z.singleton_nonneg owner
  rw [dist_eq_norm]
  rw [pi_norm_le_iff_of_nonneg
    (show 0 ≤ (2 : ℝ) * ∑ owner, block.z.singleton owner by
      exact mul_nonneg (by norm_num) hmass)]
  intro who
  rw [Pi.sub_apply, Real.norm_eq_abs]
  have hidentity : y who - block.w who =
      ∑ owner, block.z.singleton owner *
        (y who - block.wi owner who) := by
    rw [block.balance who]
    have htotal := block.z.total
    calc
      y who - (block.z.cemetery * y who +
          ∑ owner, block.z.singleton owner * block.wi owner who) =
          (1 - block.z.cemetery) * y who -
            ∑ owner, block.z.singleton owner * block.wi owner who := by
          ring
      _ = (∑ owner, block.z.singleton owner) * y who -
            ∑ owner, block.z.singleton owner * block.wi owner who := by
          congr 2
          linarith
      _ = ∑ owner, block.z.singleton owner *
            (y who - block.wi owner who) := by
          rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro owner _
          ring
  rw [hidentity]
  calc
    |∑ owner, block.z.singleton owner *
        (y who - block.wi owner who)| ≤
        ∑ owner, |block.z.singleton owner *
          (y who - block.wi owner who)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ owner, block.z.singleton owner * 2 := by
      apply Finset.sum_le_sum
      intro owner _
      rw [abs_mul, abs_of_nonneg (block.z.singleton_nonneg owner)]
      apply mul_le_mul_of_nonneg_left _ (block.z.singleton_nonneg owner)
      apply (abs_sub (y who) (block.wi owner who)).trans
      have hadd := add_le_add
        (abs_le_one_of_mem_D hbound block.y_boundary.1 who)
        (block.wi_abs_le_one hbound owner who)
      norm_num at hadd
      exact hadd
    _ = 2 * ∑ owner, block.z.singleton owner := by
      rw [← Finset.sum_mul]
      ring

/-! The value assigned to a public type draw: type zero advances directly
to `y`, while type `i` runs the corresponding attempt with value `wⁱ`. -/
def BuildingBlock.choiceValue
    {M : ι → ι → ℝ} {y : ι → ℝ} {ε : ℝ}
    (block : BuildingBlock M y ε) (choice : Option ι) (who : ι) : ℝ :=
  match choice with
  | none => y who
  | some owner => block.wi owner who

/-! Condition (F.4) is exactly the harmonicity of the public type draw. -/
theorem BuildingBlock.expect_choiceValue
    {M : ι → ι → ℝ} {y : ι → ℝ} {ε : ℝ}
    (block : BuildingBlock M y ε) (who : ι) :
    expect block.z.toPMF (fun choice => block.choiceValue choice who) =
      block.w who := by
  rw [expect_eq_sum, Fintype.sum_option]
  simp only [BuildingBlock.choiceValue,
    SimplexWeights.toPMF_none_toReal,
    SimplexWeights.toPMF_some_toReal]
  rw [block.balance who]

/-! A type-`i` block either returns to the current auxiliary-game root `w`
after no quit, or exits the auxiliary game to its continuation target `y`.
This is the operational distinction in the two branches of (F.1). -/
inductive AttemptContinuation
  | restart
  | advance
deriving DecidableEq

/-! The branch-sensitive data of one type-`i` attempt. The strict upper
bound on `quitWeight` is what permits the total quit probability to be spread
over an arbitrarily long finite block. -/
structure BuildingAttempt (M : ι → ι → ℝ) (y : ι → ℝ)
    (ε : ℝ) (block : BuildingBlock M y ε) (owner : ι) where
  continuation : AttemptContinuation
  quitWeight : ℝ
  quitWeight_pos : 0 < quitWeight
  quitWeight_lt_one : quitWeight < 1
  payoff : ∀ who,
    block.wi owner who =
      quitWeight * M who owner + (1 - quitWeight) *
        match continuation with
        | .restart => block.w who
        | .advance => y who

/-! Extract the operational branch and its quit weight from (F.1). The
negative coordinate required in Section 3.3.5 rules out quit weight one;
(F.2) would otherwise be violated at that coordinate. -/
theorem BuildingBlock.exists_attempt
    {M : ι → ι → ℝ} {y : ι → ℝ} {ε : ℝ}
    (block : BuildingBlock M y ε) (owner : ι)
    (hnegative : ∃ who, M who owner < -ε) :
    Nonempty (BuildingAttempt M y ε block owner) := by
  classical
  rcases block.approach owner with hrestart | hadvance
  · obtain ⟨⟨weight, hweight0, hweight1, hpayoff⟩, hne⟩ := hrestart
    obtain ⟨negative, hnegative⟩ := hnegative
    have hweightPos : 0 < weight := by
      apply lt_of_le_of_ne hweight0
      intro hweight
      have hlow := block.lower owner negative
      have hcolumn := hpayoff negative
      rw [← hweight] at hcolumn
      norm_num at hcolumn
      linarith
    have hweightLt : weight < 1 := by
      apply lt_of_le_of_ne hweight1
      intro hweight
      apply hne
      funext who
      rw [hpayoff who, hweight]
      ring
    exact ⟨
      { continuation := .restart
        quitWeight := 1 - weight
        quitWeight_pos := sub_pos.mpr hweightLt
        quitWeight_lt_one := by linarith
        payoff := by
          intro who
          rw [hpayoff who]
          ring }⟩
  · obtain ⟨⟨weight, hweight0, hweight1, hpayoff⟩, hne⟩ := hadvance
    obtain ⟨negative, hnegative⟩ := hnegative
    have hweightPos : 0 < weight := by
      apply lt_of_le_of_ne hweight0
      intro hweight
      have hlow := block.lower owner negative
      have hcolumn := hpayoff negative
      rw [← hweight] at hcolumn
      norm_num at hcolumn
      linarith
    have hweightLt : weight < 1 := by
      apply lt_of_le_of_ne hweight1
      intro hweight
      apply hne
      funext who
      rw [hpayoff who, hweight]
      ring
    exact ⟨
      { continuation := .advance
        quitWeight := 1 - weight
        quitWeight_pos := sub_pos.mpr hweightLt
        quitWeight_lt_one := by linarith
        payoff := by
          intro who
          rw [hpayoff who]
          ring }⟩

noncomputable def BuildingBlock.attempt
    {M : ι → ι → ℝ} {y : ι → ℝ} {ε : ℝ}
    (block : BuildingBlock M y ε) (owner : ι)
    (hnegative : ∃ who, M who owner < -ε) :
    BuildingAttempt M y ε block owner :=
  Classical.choice (block.exists_attempt owner hnegative)

/-! Any interior total quit weight can be spread over a sufficiently long
block so that the per-stage quit probability is below a prescribed positive
accuracy, while preserving the total survival probability exactly. -/
theorem BuildingAttempt.exists_mesh
    {M : ι → ι → ℝ} {y : ι → ℝ} {ε : ℝ}
    {block : BuildingBlock M y ε} {owner : ι}
    (attempt : BuildingAttempt M y ε block owner)
    {η : ℝ} (hη : 0 < η) :
    ∃ mesh : ℕ, 0 < mesh ∧
      quittingMeshHazard attempt.quitWeight mesh < η ∧
      (1 - quittingMeshHazard attempt.quitWeight mesh) ^ mesh =
        1 - attempt.quitWeight := by
  obtain ⟨mesh, hmesh⟩ := exists_nat_gt
    (max 1 (quittingMeshIntensity attempt.quitWeight / η))
  have hmeshOne : 1 < (mesh : ℝ) :=
    (le_max_left 1 _).trans_lt hmesh
  have hmeshPosReal : 0 < (mesh : ℝ) := zero_lt_one.trans hmeshOne
  have hmeshPos : 0 < mesh := by exact_mod_cast hmeshPosReal
  have hratio : quittingMeshIntensity attempt.quitWeight / (mesh : ℝ) < η := by
    have hquotient :
        quittingMeshIntensity attempt.quitWeight / η < (mesh : ℝ) :=
      (le_max_right 1 _).trans_lt hmesh
    have hintermediate :
        quittingMeshIntensity attempt.quitWeight < (mesh : ℝ) * η :=
      (div_lt_iff₀ hη).mp hquotient
    exact (div_lt_iff₀ hmeshPosReal).mpr (by
      simpa only [mul_comm] using hintermediate)
  refine ⟨mesh, hmeshPos, ?_, ?_⟩
  · exact (quittingMeshHazard_le_intensity_div
      attempt.quitWeight_lt_one).trans_lt hratio
  · exact one_sub_quittingMeshHazard_pow
      attempt.quitWeight_lt_one.le hmeshPos

/-! The continuation value with `remaining` independent stages left in a
mesh implementation of an attempt. Survival leads to the branch endpoint;
the first Quit leads to the owner's singleton column. -/
def BuildingAttempt.remainingValue
    {M : ι → ι → ℝ} {y : ι → ℝ} {ε : ℝ}
    {block : BuildingBlock M y ε} {owner : ι}
    (attempt : BuildingAttempt M y ε block owner)
    (mesh remaining : ℕ) (who : ι) : ℝ :=
  let survival :=
    (1 - quittingMeshHazard attempt.quitWeight mesh) ^ remaining
  survival *
      (match attempt.continuation with
      | .restart => block.w who
      | .advance => y who) +
    (1 - survival) * M who owner

@[simp]
theorem BuildingAttempt.remainingValue_zero
    {M : ι → ι → ℝ} {y : ι → ℝ} {ε : ℝ}
    {block : BuildingBlock M y ε} {owner : ι}
    (attempt : BuildingAttempt M y ε block owner)
    (mesh : ℕ) (who : ι) :
    attempt.remainingValue mesh 0 who =
      match attempt.continuation with
      | .restart => block.w who
      | .advance => y who := by
  simp [BuildingAttempt.remainingValue]

theorem BuildingAttempt.remainingValue_succ
    {M : ι → ι → ℝ} {y : ι → ℝ} {ε : ℝ}
    {block : BuildingBlock M y ε} {owner : ι}
    (attempt : BuildingAttempt M y ε block owner)
    (mesh remaining : ℕ) (who : ι) :
    attempt.remainingValue mesh (remaining + 1) who =
      quittingMeshHazard attempt.quitWeight mesh * M who owner +
        (1 - quittingMeshHazard attempt.quitWeight mesh) *
          attempt.remainingValue mesh remaining who := by
  simp only [BuildingAttempt.remainingValue, pow_succ]
  ring

theorem BuildingAttempt.remainingValue_mesh
    {M : ι → ι → ℝ} {y : ι → ℝ} {ε : ℝ}
    {block : BuildingBlock M y ε} {owner : ι}
    (attempt : BuildingAttempt M y ε block owner)
    (mesh : ℕ)
    (hsurvival :
      (1 - quittingMeshHazard attempt.quitWeight mesh) ^ mesh =
        1 - attempt.quitWeight)
    (who : ι) :
    attempt.remainingValue mesh mesh who = block.wi owner who := by
  rw [BuildingAttempt.remainingValue, hsurvival, attempt.payoff who]
  ring

/-! The existential conclusion of Theorem 3.3. -/
def Theorem33Conclusion (M : ι → ι → ℝ) (y : ι → ℝ) (ε : ℝ) : Prop :=
  Nonempty (BuildingBlock M y ε)

private theorem subfamilyHull_weights
    (M : ι → ι → ℝ) (J : Finset ι) {y : ι → ℝ}
    (hy : y ∈ SubfamilyHull M J) :
    ∃ weight : ι → ℝ, (∀ i, 0 ≤ weight i) ∧
      (∑ i, weight i) = 1 ∧
      (∀ i, 0 < weight i → i ∈ J) ∧
      (∀ who, ∑ i, weight i * M who i = y who) := by
  rw [SubfamilyHull, mem_convexHull_iff_exists_fintype] at hy
  obtain ⟨κ, hκ, a, point, ha, hatotal, hpoint, hsum⟩ := hy
  letI : Fintype κ := hκ
  choose owner howner using hpoint
  let weight : ι → ℝ := fun i =>
    ∑ k, if (owner k : ι) = i then a k else 0
  refine ⟨weight, ?_, ?_, ?_, ?_⟩
  · intro i
    exact Finset.sum_nonneg fun k _ => by split <;> simp_all
  · simp only [weight]
    calc
      ∑ i, ∑ k, (if (owner k : ι) = i then a k else 0) =
          ∑ k, ∑ i, (if (owner k : ι) = i then a k else 0) := Finset.sum_comm
      _ = ∑ k, a k := by
        apply Finset.sum_congr rfl
        intro k _
        exact Fintype.sum_ite_eq (owner k : ι) (fun _ => a k)
      _ = 1 := hatotal
  · intro i hi
    by_contra hnot
    have hne (k : κ) : (owner k : ι) ≠ i := fun heq =>
      hnot (heq ▸ (owner k).property)
    simp [weight, hne] at hi
  · intro who
    have happly := congr_fun hsum who
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at happly
    simp only [weight, Finset.sum_mul]
    calc
      ∑ i, ∑ k, (if (owner k : ι) = i then a k else 0) * M who i =
          ∑ k, ∑ i, (if (owner k : ι) = i then a k else 0) * M who i :=
        Finset.sum_comm
      _ = ∑ k, a k * M who (owner k) := by
        apply Finset.sum_congr rfl
        intro k _
        simpa only [ite_mul, zero_mul] using
          (Fintype.sum_ite_eq (owner k : ι) (fun i => a k * M who i))
      _ = y who := by
        rw [← happly]
        apply Finset.sum_congr rfl
        intro k _
        rw [← howner k]

private theorem column_ne_of_no_nontrivial_zero_solution
    (M : ι → ι → ℝ) {y : ι → ℝ} (hy : y ∈ D M)
    (hdiag : ∀ i, M i i = 0)
    (hzero : ¬HasNontrivialZeroProjectiveLCPSolution M) (owner : ι) :
    (fun who => M who owner) ≠ y := by
  intro heq
  apply hzero
  let solution : ProjectiveLCPSolution M (0 : ι → ℝ) :=
    { cemetery := 0
      singleton := fun i => if i = owner then 1 else 0
      cemetery_nonneg := le_rfl
      singleton_nonneg := fun i => by split <;> simp_all
      total := by simp
      residual_nonneg := fun who => by
        simp only [zero_mul, zero_add, ite_mul, one_mul, zero_mul,
          Fintype.sum_ite_eq']
        rw [congr_fun heq who]
        exact hy.2 who
      complementary := fun who => by
        by_cases hwho : who = owner
        · subst who
          simp [hdiag]
        · simp [hwho] }
  exact ⟨solution, by simp [solution]⟩

private theorem column_not_mem_D_of_no_nontrivial_zero_solution
    (M : ι → ι → ℝ) (hdiag : ∀ i, M i i = 0)
    (hzero : ¬HasNontrivialZeroProjectiveLCPSolution M) (owner : ι) :
    (fun who => M who owner) ∉ D M := by
  intro hcolumn
  apply hzero
  let solution : ProjectiveLCPSolution M (0 : ι → ℝ) :=
    { cemetery := 0
      singleton := fun i => if i = owner then 1 else 0
      cemetery_nonneg := le_rfl
      singleton_nonneg := fun i => by split <;> simp_all
      total := by simp
      residual_nonneg := fun who => by
        simp only [zero_mul, zero_add, ite_mul, one_mul, zero_mul,
          Fintype.sum_ite_eq']
        exact hcolumn.2 who
      complementary := fun who => by
        by_cases hwho : who = owner
        · subst who
          simp [hdiag]
        · simp [hwho] }
  exact ⟨solution, by simp [solution]⟩

/-! The first case in the proof of Theorem 3.3: `y` already lies in the
convex hull of the columns whose own coordinate vanishes. -/
theorem theorem33Conclusion_of_mem_subfamilyHull
    (M : ι → ι → ℝ) {y : ι → ℝ} (hy : DZero M y)
    (hbound : MatrixPayoffsBounded M) (hdiag : ∀ i, M i i = 0)
    (hzero : ¬HasNontrivialZeroProjectiveLCPSolution M)
    (hmember : y ∈ SubfamilyHull M (ZeroCoordinates y))
    {ε : ℝ} (hε : 0 < ε) : Theorem33Conclusion M y ε := by
  let δ := min ε 1
  have hδpos : 0 < δ := lt_min hε zero_lt_one
  have hδnonneg : 0 ≤ δ := hδpos.le
  have hδε : δ ≤ ε := min_le_left _ _
  have hδone : δ ≤ 1 := min_le_right _ _
  have hyD : y ∈ D M := mem_D_of_DZero hy
  obtain ⟨weight, hweight, htotal, hsupport, haverage⟩ :=
    subfamilyHull_weights M (ZeroCoordinates y) hmember
  let wi : ι → ι → ℝ := fun i who =>
    (1 - δ) * y who + δ * M who i
  let z : SimplexWeights ι :=
    { cemetery := 0
      singleton := weight
      cemetery_nonneg := le_rfl
      singleton_nonneg := hweight
      total := by simpa using htotal }
  refine ⟨{
    w := y
    wi := wi
    z := z
    y_boundary := hy
    w_boundary := hy
    approach := ?_
    lower := ?_
    balance := ?_
    complementary := ?_
    nontrivial := ?_ }⟩
  · intro i
    left
    constructor
    · refine ⟨1 - δ, sub_nonneg.mpr hδone, by linarith, ?_⟩
      intro who
      simp only [wi]
      ring
    · intro hwi
      apply column_ne_of_no_nontrivial_zero_solution M hyD hdiag hzero i
      funext who
      have hcoordinate := congr_fun hwi who
      simp only [wi] at hcoordinate
      nlinarith
  · intro i who
    have hMlower : -1 ≤ M who i := (abs_le.mp (hbound who i)).1
    have hscaled : -δ ≤ δ * M who i := by
      nlinarith [mul_nonneg hδnonneg (show 0 ≤ M who i + 1 by linarith)]
    have hy_nonneg := hyD.2 who
    have hfactor : 0 ≤ 1 - δ := sub_nonneg.mpr hδone
    dsimp only [wi]
    nlinarith [mul_nonneg hfactor hy_nonneg]
  · intro who
    simp only [z, zero_mul, zero_add, wi]
    symm
    calc
      ∑ i, weight i * ((1 - δ) * y who + δ * M who i) =
          (1 - δ) * y who * (∑ i, weight i) +
            δ * (∑ i, weight i * M who i) := by
        simp_rw [mul_add]
        rw [Finset.sum_add_distrib]
        congr 1
        · rw [← Finset.sum_mul]
          ring
        · rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
      _ = y who := by rw [htotal, haverage]; ring
  · intro i hi
    have hmem := hsupport i hi
    rw [ZeroCoordinates, Finset.mem_filter] at hmem
    simp only [wi, hmem.2, hdiag i]
    ring
  · simpa only [z, htotal] using (zero_lt_one : (0 : ℝ) < 1)

/-! The first subcase of Lemma 3.4: a segment from `y` to a zero-coordinate
column reaches a second boundary point of `D`. -/
theorem theorem33Conclusion_of_segment_boundary
    (M : ι → ι → ℝ) {y w : ι → ℝ}
    (hy : DZero M y)
    (hbound : MatrixPayoffsBounded M) (hdiag : ∀ i, M i i = 0)
    (hzero : ¬HasNontrivialZeroProjectiveLCPSolution M)
    (i : ι) (hyi : y i = 0) (hw : DZero M w)
    (hsegment : Segment y (fun who => M who i) w) (hwy : w ≠ y)
    {ε : ℝ} (hε : 0 < ε) : Theorem33Conclusion M y ε := by
  obtain ⟨a, ha0, ha1, haw⟩ := hsegment
  let δ := 1 - a
  have hδ0 : 0 ≤ δ := sub_nonneg.mpr ha1
  have hδpos : 0 < δ := by
    apply lt_of_le_of_ne hδ0
    intro hzeroδ
    have haeq : a = 1 := by
      dsimp only [δ] at hzeroδ
      linarith
    apply hwy
    funext who
    rw [haw, haeq]
    ring
  have hδone : δ ≤ 1 := by dsimp only [δ]; linarith
  have hwD : w ∈ D M := mem_D_of_DZero hw
  have hcolumn_ne : (fun who => M who i) ≠ w := by
    exact column_ne_of_no_nontrivial_zero_solution M hwD hdiag hzero i
  have hδlt : δ < 1 := by
    apply lt_of_le_of_ne hδone
    intro hδeq
    apply hcolumn_ne
    have haeq : a = 0 := by
      dsimp only [δ] at hδeq
      linarith
    funext who
    rw [haw, haeq]
    ring
  have hw_affine (who : ι) :
      w who = (1 - δ) * y who + δ * M who i := by
    have := haw who
    dsimp only [δ]
    nlinarith
  let η := min ε 1
  have hηpos : 0 < η := lt_min hε zero_lt_one
  have hη0 : 0 ≤ η := hηpos.le
  have hηε : η ≤ ε := min_le_left _ _
  have hηone : η ≤ 1 := min_le_right _ _
  let denominator := η * (1 - δ) + δ
  have hdenominator : 0 < denominator := by
    dsimp only [denominator]
    have : 0 ≤ η * (1 - δ) :=
      mul_nonneg hη0 (sub_nonneg.mpr hδone)
    linarith
  let wi : ι → ι → ℝ := fun owner who =>
    (1 - η) * w who + η * M who owner
  let z : SimplexWeights ι :=
    { cemetery := η * (1 - δ) / denominator
      singleton := fun owner => if owner = i then δ / denominator else 0
      cemetery_nonneg := div_nonneg
        (mul_nonneg hη0 (sub_nonneg.mpr hδone)) hdenominator.le
      singleton_nonneg := fun owner => by
        split
        · exact div_nonneg hδ0 hdenominator.le
        · exact le_rfl
      total := by
        simp only [Fintype.sum_ite_eq', denominator]
        field_simp [show η * (1 - δ) + δ ≠ 0 by positivity] }
  refine ⟨{
    w := w
    wi := wi
    z := z
    y_boundary := hy
    w_boundary := hw
    approach := ?_
    lower := ?_
    balance := ?_
    complementary := ?_
    nontrivial := ?_ }⟩
  · intro owner
    left
    constructor
    · refine ⟨1 - η, sub_nonneg.mpr hηone, by linarith, ?_⟩
      intro who
      simp only [wi]
      ring
    · intro hwi
      apply column_ne_of_no_nontrivial_zero_solution M hwD hdiag hzero owner
      funext who
      have hcoordinate := congr_fun hwi who
      simp only [wi] at hcoordinate
      nlinarith
  · intro owner who
    have hMlower : -1 ≤ M who owner :=
      (abs_le.mp (hbound who owner)).1
    have hscaled : -η ≤ η * M who owner := by
      nlinarith [mul_nonneg hη0 (show 0 ≤ M who owner + 1 by linarith)]
    have hw_nonneg := hwD.2 who
    have hfactor : 0 ≤ 1 - η := sub_nonneg.mpr hηone
    dsimp only [wi]
    nlinarith [mul_nonneg hfactor hw_nonneg]
  · intro who
    change w who = η * (1 - δ) / denominator * y who +
      ∑ owner, (if owner = i then δ / denominator else 0) * wi owner who
    have hsum :
        (∑ owner, (if owner = i then δ / denominator else 0) * wi owner who) =
          δ / denominator * wi i who := by
      simpa only [ite_mul, zero_mul] using
        (Fintype.sum_ite_eq' i fun owner => δ / denominator * wi owner who)
    rw [hsum]
    simp only [wi]
    rw [hw_affine]
    field_simp [ne_of_gt hdenominator]
    dsimp only [denominator]
    ring
  · intro owner howner
    by_cases hoi : owner = i
    · subst owner
      have hwi : w i = 0 := by rw [hw_affine, hyi, hdiag]; ring
      simp only [wi, hwi, hdiag]
      ring
    · simp [z, hoi] at howner
  · simp only [z, Fintype.sum_ite_eq', denominator]
    exact div_pos hδpos hdenominator

/-! The published second subcase of Lemma 3.5. Here `w` is a boundary
point of the small slice `(1-η)y+ηS(J_y)`. Its extreme points approach
the singleton columns from `y`, which is the second alternative in the
published condition (F.1). -/
theorem theorem33Conclusion_of_slice_boundary
    (M : ι → ι → ℝ) {y w : ι → ℝ}
    (hy : DZero M y) (hw : DZero M w)
    (hbound : MatrixPayoffsBounded M) (hdiag : ∀ i, M i i = 0)
    (hzero : ¬HasNontrivialZeroProjectiveLCPSolution M)
    {η ε : ℝ} (hηpos : 0 < η) (hηone : η ≤ 1) (hηε : η ≤ ε)
    (hwSlice : w ∈ SubfamilyHull
      (fun who owner => (1 - η) * y who + η * M who owner)
      (ZeroCoordinates y)) :
    Theorem33Conclusion M y ε := by
  have hyD : y ∈ D M := mem_D_of_DZero hy
  obtain ⟨weight, hweight, htotal, hsupport, haverage⟩ :=
    subfamilyHull_weights
      (fun who owner => (1 - η) * y who + η * M who owner)
      (ZeroCoordinates y) hwSlice
  let wi : ι → ι → ℝ := fun owner who =>
    (1 - η) * y who + η * M who owner
  let z : SimplexWeights ι :=
    { cemetery := 0
      singleton := weight
      cemetery_nonneg := le_rfl
      singleton_nonneg := hweight
      total := by simpa using htotal }
  refine ⟨{
    w := w
    wi := wi
    z := z
    y_boundary := hy
    w_boundary := hw
    approach := ?_
    lower := ?_
    balance := ?_
    complementary := ?_
    nontrivial := ?_ }⟩
  · intro owner
    right
    constructor
    · refine ⟨1 - η, sub_nonneg.mpr hηone, by linarith, ?_⟩
      intro who
      simp only [wi]
      ring
    · intro hwi
      apply column_ne_of_no_nontrivial_zero_solution M hyD hdiag hzero owner
      funext who
      have hcoordinate := congr_fun hwi who
      simp only [wi] at hcoordinate
      nlinarith
  · intro owner who
    have hMlower : -1 ≤ M who owner :=
      (abs_le.mp (hbound who owner)).1
    have hscaled : -η ≤ η * M who owner := by
      nlinarith [mul_nonneg hηpos.le (show 0 ≤ M who owner + 1 by linarith)]
    have hy_nonneg := hyD.2 who
    have hfactor : 0 ≤ 1 - η := sub_nonneg.mpr hηone
    dsimp only [wi]
    nlinarith [mul_nonneg hfactor hy_nonneg]
  · intro who
    simp only [z, zero_mul, zero_add, wi]
    exact (haverage who).symm
  · intro owner howner
    have hmem := hsupport owner howner
    rw [ZeroCoordinates, Finset.mem_filter] at hmem
    simp only [wi, hmem.2, hdiag owner]
    ring
  · simpa only [z, htotal] using (zero_lt_one : (0 : ℝ) < 1)

/-! Rescaling a nontrivial projective complementarity packet gives the
first construction in the published Lemma 3.4. -/
theorem theorem33Conclusion_of_projective_packet
    (M : ι → ι → ℝ) {y w : ι → ℝ}
    (hy : DZero M y) (hw : DZero M w)
    (hbound : MatrixPayoffsBounded M)
    (hdiag : ∀ i, M i i = 0)
    (hzero : ¬HasNontrivialZeroProjectiveLCPSolution M)
    (cemetery : ℝ) (singleton : ι → ℝ)
    (hcemetery : 0 ≤ cemetery) (hsingleton : ∀ i, 0 ≤ singleton i)
    (htotal : cemetery + ∑ i, singleton i = 1)
    (hbalance : ∀ who, w who = cemetery * y who +
      ∑ i, singleton i * M who i)
    (hcomplementary : ∀ i, singleton i > 0 → w i = 0)
    (hnontrivial : 0 < ∑ i, singleton i)
    {ε : ℝ} (hε : 0 < ε) : Theorem33Conclusion M y ε := by
  let η := min ε 1
  have hηpos : 0 < η := lt_min hε zero_lt_one
  have hηnonneg : 0 ≤ η := hηpos.le
  have hηε : η ≤ ε := min_le_left _ _
  have hηone : η ≤ 1 := min_le_right _ _
  let mass := ∑ i, singleton i
  let denominator := η * cemetery + mass
  have hdenominator : 0 < denominator := by
    dsimp only [denominator]
    exact add_pos_of_nonneg_of_pos (mul_nonneg hηnonneg hcemetery) hnontrivial
  let wi : ι → ι → ℝ := fun owner who =>
    (1 - η) * w who + η * M who owner
  let z : SimplexWeights ι :=
    { cemetery := η * cemetery / denominator
      singleton := fun owner => singleton owner / denominator
      cemetery_nonneg := div_nonneg (mul_nonneg hηnonneg hcemetery)
        hdenominator.le
      singleton_nonneg := fun owner =>
        div_nonneg (hsingleton owner) hdenominator.le
      total := by
        change η * cemetery / denominator +
          ∑ owner, singleton owner / denominator = 1
        rw [← Finset.sum_div]
        field_simp [ne_of_gt hdenominator]
        rfl }
  refine ⟨{
    w := w
    wi := wi
    z := z
    y_boundary := hy
    w_boundary := hw
    approach := ?_
    lower := ?_
    balance := ?_
    complementary := ?_
    nontrivial := ?_ }⟩
  · intro owner
    left
    constructor
    · refine ⟨1 - η, sub_nonneg.mpr hηone, by linarith, ?_⟩
      intro who
      simp only [wi]
      ring
    · intro hwi
      have hcolumn : (fun who => M who owner) = w := by
        funext who
        have hcoordinate := congr_fun hwi who
        simp only [wi] at hcoordinate
        nlinarith
      exact column_not_mem_D_of_no_nontrivial_zero_solution M hdiag
        hzero owner (hcolumn ▸ hw.1)
  · intro owner who
    have hMlower : -1 ≤ M who owner :=
      (abs_le.mp (hbound who owner)).1
    have hscaled : -η ≤ η * M who owner := by
      nlinarith [mul_nonneg hηnonneg (show 0 ≤ M who owner + 1 by linarith)]
    have hwNonnegative := hw.1.2 who
    have hfactor : 0 ≤ 1 - η := sub_nonneg.mpr hηone
    dsimp only [wi]
    nlinarith [mul_nonneg hfactor hwNonnegative]
  · intro who
    change w who = η * cemetery / denominator * y who +
      ∑ owner, singleton owner / denominator * wi owner who
    simp_rw [div_mul_eq_mul_div]
    rw [← Finset.sum_div]
    simp_rw [wi, mul_add]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul]
    have hweighted : ∑ owner, singleton owner * (η * M who owner) =
        η * (∑ owner, singleton owner * M who owner) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro owner _
      ring
    rw [hweighted]
    field_simp [ne_of_gt hdenominator]
    rw [hbalance]
    dsimp only [denominator, mass]
    have hmass : ∑ i, singleton i = 1 - cemetery := by
      linarith [htotal]
    rw [hmass]
    ring
  · intro owner howner
    have hsinglePos : 0 < singleton owner := by
      rcases div_pos_iff.mp howner with hpositive | hnegative
      · exact hpositive.1
      · exact False.elim ((not_lt_of_ge hdenominator.le) hnegative.2)
    have hwzero := hcomplementary owner hsinglePos
    simp only [wi, hwzero, hdiag owner]
    ring
  · change 0 < ∑ owner, singleton owner / denominator
    rw [← Finset.sum_div]
    exact div_pos hnontrivial hdenominator

/-! **Lemmas 3.3 and 3.4 (paper).** Put `J_y={i:y_i=0}` and
`S(J_y)=conv{r̂^i:i∈J_y}`. In the two geometric cases
`conv(S(J_y),y)∩D={y}` and `conv(S(J_y),y)∩D ⊋ {y}`, respectively, the
paper proves the same `Theorem33Conclusion` represented above. -/

/-! `conv(S(J),y)`, the convex hull after adjoining `y`. -/
def AugmentedHull (M : ι → ι → ℝ) (J : Finset ι)
    (y : ι → ℝ) : Set (ι → ℝ) :=
  convexHull ℝ (SubfamilyHull M J ∪ {y})

omit [Fintype ι] [DecidableEq ι] in
private theorem affine_slice_mem_subfamilyHull
    (M : ι → ι → ℝ) (J : Finset ι) {y s : ι → ℝ}
    (η : ℝ) (hs : s ∈ SubfamilyHull M J) :
    (fun who => (1 - η) * y who + η * s who) ∈
      SubfamilyHull
        (fun who owner => (1 - η) * y who + η * M who owner) J := by
  let slice : (ι → ℝ) →ᵃ[ℝ] (ι → ℝ) :=
    AffineMap.mk (fun x => (1 - η) • y + η • x)
      (η • LinearMap.id)
      (by
        intro p v
        ext who
        simp
        ring)
  have himage : slice ''
      (Set.range fun i : J => fun who => M who i) =
      Set.range (fun i : J =>
        fun who => (1 - η) * y who + η * M who i) := by
    ext x
    constructor
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      refine ⟨i, ?_⟩
      ext who
      simp [slice, smul_eq_mul]
    · rintro ⟨i, rfl⟩
      refine ⟨fun who => M who i, ⟨i, rfl⟩, ?_⟩
      ext who
      simp [slice, smul_eq_mul]
  have hsImage : slice s ∈ slice ''
      convexHull ℝ (Set.range fun i : J => fun who => M who i) :=
    ⟨s, hs, rfl⟩
  rw [slice.image_convexHull, himage] at hsImage
  change (fun who => (1 - η) * y who + η * s who) ∈
    convexHull ℝ (Set.range fun i : J =>
      fun who => (1 - η) * y who + η * M who i)
  convert hsImage using 1
  ext who
  simp [slice, smul_eq_mul]

omit [Fintype ι] [DecidableEq ι] in
private theorem mem_augmentedHull
    (M : ι → ι → ℝ) (J : Finset ι) (hJ : J.Nonempty)
    {y q : ι → ℝ} (hq : q ∈ AugmentedHull M J y) :
    ∃ s ∈ SubfamilyHull M J, q ∈ segment ℝ y s := by
  have hS : (SubfamilyHull M J).Nonempty := by
    obtain ⟨i, hi⟩ := hJ
    exact ⟨fun who => M who i, subset_convexHull ℝ _ ⟨⟨i, hi⟩, rfl⟩⟩
  have hconvexS : Convex ℝ (SubfamilyHull M J) :=
    convex_convexHull ℝ _
  have heq : convexHull ℝ (SubfamilyHull M J ∪ {y}) =
      convexJoin ℝ (SubfamilyHull M J) {y} :=
    hconvexS.convexHull_union (convex_singleton y)
      hS (Set.singleton_nonempty y)
  rw [AugmentedHull, heq, mem_convexJoin] at hq
  obtain ⟨s, hs, b, hb, hsegment⟩ := hq
  have hb' : b = y := Set.mem_singleton_iff.mp hb
  subst b
  exact ⟨s, hs, segment_symm ℝ s y ▸ hsegment⟩

omit [Fintype ι] [DecidableEq ι] in
private theorem endpoint_not_mem_augmentedHull
    {C : Set (ι → ℝ)} (hC : Convex ℝ C) (hCnonempty : C.Nonempty)
    {y s q : ι → ℝ} (hy : y ∉ C) (hs : s ∈ C)
    (hq : Segment y s q) (hqy : q ≠ y) :
    y ∉ convexHull ℝ (C ∪ {q}) := by
  intro hyHull
  have heq : convexHull ℝ (C ∪ {q}) = convexJoin ℝ C {q} :=
    hC.convexHull_union (convex_singleton q) hCnonempty
      (Set.singleton_nonempty q)
  rw [heq, mem_convexJoin] at hyHull
  obtain ⟨c, hc, q', hq', hySegment⟩ := hyHull
  have hq'eq : q' = q := Set.mem_singleton_iff.mp hq'
  subst q'
  obtain ⟨b, hb0, hb1, hqb⟩ := hq
  have hbne : b ≠ 1 := by
    intro hb
    apply hqy
    funext who
    rw [hqb who, hb]
    ring
  obtain ⟨a, ha0, ha1, hya⟩ :=
    segment_of_mem_segment hySegment
  let denominator := a + (1 - a) * (1 - b)
  have hdenominator : 0 < denominator := by
    dsimp only [denominator]
    have hbone : 0 < 1 - b := lt_of_le_of_ne
      (sub_nonneg.mpr hb1) (Ne.symm (sub_ne_zero.mpr hbne.symm))
    by_cases hapos : 0 < a
    · positivity
    · have haeq : a = 0 := le_antisymm (le_of_not_gt hapos) ha0
      rw [haeq]
      simpa using hbone
  have hySegmentCS : Segment c s y := by
    refine ⟨a / denominator, div_nonneg ha0 hdenominator.le, ?_, ?_⟩
    · rw [div_le_one hdenominator]
      dsimp only [denominator]
      exact le_add_of_nonneg_right
        (mul_nonneg (sub_nonneg.mpr ha1) (sub_nonneg.mpr hb1))
    · intro who
      field_simp [ne_of_gt hdenominator]
      dsimp only [denominator]
      linear_combination hya who + (1 - a) * (hqb who)
  exact hy <| hC.segment_subset hc hs (mem_segment_of_Segment hySegmentCS)

/-! Lemma 3.4: the singleton-intersection case yields (F.1)--(F.5). -/
theorem lemma3_4
    (M : ι → ι → ℝ) {y : ι → ℝ} (hy : DZero M y)
    (hbound : MatrixPayoffsBounded M) (hdiag : ∀ i, M i i = 0) (hzero :
      ¬HasNontrivialZeroProjectiveLCPSolution M) (hQ : QMatrix M)
    (hnot : y ∉ SubfamilyHull M (ZeroCoordinates y))
    (hpoint : AugmentedHull M (ZeroCoordinates y) y ∩
      D M = {y}) {ε : ℝ} (hε : 0 < ε) :
    Theorem33Conclusion M y ε := by
  let J := ZeroCoordinates y
  let C := SubfamilyHull M J
  obtain ⟨pivot, hpivotZero⟩ := hy.2
  have hpivot : pivot ∈ J := by
    simp only [J, ZeroCoordinates, Finset.mem_filter, Finset.mem_univ,
      true_and]
    exact hpivotZero
  have hCconvex : Convex ℝ C := convex_convexHull ℝ _
  have hCnonempty : C.Nonempty := by
    exact ⟨fun who => M who pivot,
      subset_convexHull ℝ _ ⟨⟨pivot, hpivot⟩, rfl⟩⟩
  let δ : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  let q : ℕ → ι → ℝ := fun n who =>
    y who + δ n * (M who pivot - y who)
  have hδpos (n : ℕ) : 0 < δ n := by
    dsimp only [δ]
    positivity
  have hδone (n : ℕ) : δ n ≤ 1 := by
    dsimp only [δ]
    rw [div_le_one (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
    norm_num
  have hqSegment (n : ℕ) :
      Segment y (fun who => M who pivot) (q n) := by
    refine ⟨1 - δ n, sub_nonneg.mpr (hδone n), by linarith [hδpos n], ?_⟩
    intro who
    simp only [q]
    ring
  have hqNe (n : ℕ) : q n ≠ y := by
    intro hqy
    have hcolumnNe := column_ne_of_no_nontrivial_zero_solution
      M hy.1 hdiag hzero pivot
    apply hcolumnNe
    funext who
    have hcoordinate := congr_fun hqy who
    simp only [q] at hcoordinate
    nlinarith [hδpos n]
  have hqHull (n : ℕ) : q n ∈ ColumnConvexHull M :=
    (convex_convexHull ℝ _).segment_subset hy.1.1
      (subset_convexHull ℝ _ ⟨pivot, rfl⟩)
      (mem_segment_of_Segment (hqSegment n))
  have hqAugmented (n : ℕ) : q n ∈ AugmentedHull M J y := by
    have hcolumnC : (fun who => M who pivot) ∈ C := by
      exact subset_convexHull ℝ _ ⟨⟨pivot, hpivot⟩, rfl⟩
    apply (convex_convexHull ℝ _).segment_subset
      (subset_convexHull ℝ _ <| Set.mem_union_right _ (Set.mem_singleton y))
      (subset_convexHull ℝ _ <| Set.mem_union_left _ <|
        (show (fun who => M who pivot) ∈ SubfamilyHull M J from hcolumnC))
    exact mem_segment_of_Segment (hqSegment n)
  have hqNegative (n : ℕ) : q n ∉ NonnegativeOrthant ι := by
    intro hnonnegative
    have hqD : q n ∈ D M := ⟨hqHull n, hnonnegative⟩
    have hsingleton : q n ∈ ({y} : Set (ι → ℝ)) := by
      rw [← hpoint]
      exact ⟨by simpa only [J] using hqAugmented n, hqD⟩
    exact hqNe n (Set.mem_singleton_iff.mp hsingleton)
  let solution (n : ℕ) : ProjectiveLCPSolution M (q n) :=
    Classical.choice (hQ (q n))
  let residual (n : ℕ) : ι → ℝ := fun who =>
    (solution n).cemetery * q n who +
      ∑ owner, (solution n).singleton owner * M who owner
  have hresidualDZero (n : ℕ) : DZero M (residual n) :=
    lemma3_2 M (q n) (hqHull n) (hqNegative n) (solution n)
  let coefficient (n : ℕ) : Option ι → ℝ
    | none => (solution n).cemetery
    | some owner => (solution n).singleton owner
  have hcoefficient (n : ℕ) : coefficient n ∈
      Set.univ.pi (fun _ : Option ι => Set.Icc (0 : ℝ) 1) := by
    intro index _
    constructor
    · cases index with
      | none => exact (solution n).cemetery_nonneg
      | some owner => exact (solution n).singleton_nonneg owner
    · cases index with
      | none =>
          have hsum : 0 ≤ ∑ owner, (solution n).singleton owner :=
            Finset.sum_nonneg fun owner _ =>
              (solution n).singleton_nonneg owner
          linarith [(solution n).total]
      | some owner =>
          have hsingleSum : (solution n).singleton owner ≤
              ∑ i, (solution n).singleton i :=
            Finset.single_le_sum
              (fun i _ => (solution n).singleton_nonneg i)
              (Finset.mem_univ owner)
          have hsum : ∑ i, (solution n).singleton i ≤ 1 := by
            linarith [(solution n).total, (solution n).cemetery_nonneg]
          exact hsingleSum.trans hsum
  have hcubeCompact : IsCompact
      (Set.univ.pi (fun _ : Option ι => Set.Icc (0 : ℝ) 1)) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  obtain ⟨limit, hlimitCube, subseq, hsubseq, hlimit⟩ :=
    hcubeCompact.tendsto_subseq hcoefficient
  let cemetery := limit none
  let singleton : ι → ℝ := fun owner => limit (some owner)
  have hcoefficientLimit (index : Option ι) :
      Tendsto (fun n => coefficient (subseq n) index) atTop
        (nhds (limit index)) :=
    ((continuous_apply index).tendsto limit).comp hlimit
  have hδTendsto : Tendsto δ atTop (nhds 0) := by
    simpa only [δ, one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hqTendsto : Tendsto q atTop (nhds y) := by
    rw [tendsto_pi_nhds]
    intro who
    simpa only [q, zero_mul, add_zero] using
      tendsto_const_nhds.add (hδTendsto.mul_const (M who pivot - y who))
  have hqSubseq : Tendsto (q ∘ subseq) atTop (nhds y) :=
    hqTendsto.comp hsubseq.tendsto_atTop
  let w : ι → ℝ := fun who => cemetery * y who +
    ∑ owner, singleton owner * M who owner
  have hresidualTendsto : Tendsto (residual ∘ subseq) atTop (nhds w) := by
    rw [tendsto_pi_nhds]
    intro who
    have hcemetery := hcoefficientLimit none
    have hqWho : Tendsto (fun n => q (subseq n) who) atTop (nhds (y who)) :=
      (continuous_apply who).tendsto y |>.comp hqSubseq
    have hsum := tendsto_finsetSum Finset.univ fun owner _ =>
      (hcoefficientLimit (some owner)).mul_const (M who owner)
    simpa only [residual, Function.comp_apply, coefficient, w, cemetery,
      singleton] using hcemetery.mul hqWho |>.add hsum
  have hcemeteryNonneg : 0 ≤ cemetery := hlimitCube none (Set.mem_univ _)|>.1
  have hsingletonNonneg (owner : ι) : 0 ≤ singleton owner :=
    hlimitCube (some owner) (Set.mem_univ _)|>.1
  have htotal : cemetery + ∑ owner, singleton owner = 1 := by
    have htendsto : Tendsto
        (fun n => coefficient (subseq n) none +
          ∑ owner, coefficient (subseq n) (some owner)) atTop
        (nhds (cemetery + ∑ owner, singleton owner)) := by
      exact (hcoefficientLimit none).add <|
        tendsto_finsetSum Finset.univ fun owner _ =>
          hcoefficientLimit (some owner)
    have hone : Tendsto
        (fun n => coefficient (subseq n) none +
          ∑ owner, coefficient (subseq n) (some owner)) atTop
        (nhds 1) := by
      simpa only [coefficient, (solution _).total] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1))
    exact tendsto_nhds_unique htendsto hone
  have hcomplementary (owner : ι) :
      singleton owner * w owner = 0 := by
    have htendsto := (hcoefficientLimit (some owner)).mul <|
      (continuous_apply owner).tendsto w |>.comp hresidualTendsto
    have hzero : Tendsto
        (fun n => coefficient (subseq n) (some owner) *
          residual (subseq n) owner) atTop (nhds 0) := by
      have heq : (fun n => coefficient (subseq n) (some owner) *
          residual (subseq n) owner) = fun _ : ℕ => (0 : ℝ) := by
        funext n
        exact (solution (subseq n)).complementary owner
      rw [heq]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique htendsto hzero
  have hwD : w ∈ D M := (isClosed_D M).mem_of_tendsto
    hresidualTendsto (Filter.Eventually.of_forall fun n =>
      (hresidualDZero (subseq n)).1)
  have hwZero : ∃ owner, w owner = 0 := by
    have hprodTendsto := tendsto_finsetProd Finset.univ fun owner _ =>
      (continuous_apply owner).tendsto w |>.comp hresidualTendsto
    have hprodZero : Tendsto
        (fun n => ∏ owner, residual (subseq n) owner) atTop (nhds 0) := by
      have heq : (fun n => ∏ owner, residual (subseq n) owner) =
          fun _ : ℕ => (0 : ℝ) := by
        funext n
        obtain ⟨owner, howner⟩ := (hresidualDZero (subseq n)).2
        exact Finset.prod_eq_zero (Finset.mem_univ owner) howner
      rw [heq]
      exact tendsto_const_nhds
    have hprod : ∏ owner, w owner = 0 :=
      tendsto_nhds_unique hprodTendsto hprodZero
    obtain ⟨owner, _, howner⟩ := Finset.prod_eq_zero_iff.mp hprod
    exact ⟨owner, howner⟩
  have hw : DZero M w := ⟨hwD, hwZero⟩
  have hwy : w ≠ y := by
    intro hwyeq
    have heventuallyPositive : ∀ᶠ n in atTop,
        ∀ owner ∈ Finset.univ, owner ∉ J →
          0 < residual (subseq n) owner := by
      rw [Finset.eventually_all]
      intro owner _
      by_cases howner : owner ∈ J
      · exact Filter.Eventually.of_forall fun _ hnotOwner =>
          False.elim (hnotOwner howner)
      · have hyowner : 0 < y owner := by
          have hyNonnegative := hy.1.2 owner
          have hyne : y owner ≠ 0 := by
            simpa only [J, ZeroCoordinates, Finset.mem_filter,
              Finset.mem_univ, true_and] using howner
          exact lt_of_le_of_ne hyNonnegative hyne.symm
        have htendsto : Tendsto (fun n => residual (subseq n) owner)
            atTop (nhds (y owner)) := by
          have ht :=
            (continuous_apply owner).tendsto w |>.comp hresidualTendsto
          change Tendsto (fun n => residual (subseq n) owner) atTop
            (nhds (w owner)) at ht
          simpa only [hwyeq] using ht
        filter_upwards [htendsto.eventually_const_lt hyowner] with n hn
        exact fun _ => hn
    obtain ⟨n, hn⟩ := heventuallyPositive.exists
    have hsingleOutside (owner : ι) (howner : owner ∉ J) :
        (solution (subseq n)).singleton owner = 0 := by
      have hcomp := (solution (subseq n)).complementary owner
      change (solution (subseq n)).singleton owner *
        residual (subseq n) owner = 0 at hcomp
      exact (mul_eq_zero.mp hcomp).resolve_right
        (ne_of_gt (hn owner (Finset.mem_univ owner) howner))
    let point : Option ι → (ι → ℝ)
      | none => q (subseq n)
      | some owner => if owner ∈ J then (fun who => M who owner)
        else q (subseq n)
    have hpointMem (index : Option ι) : point index ∈
        C ∪ {q (subseq n)} := by
      cases index with
      | none => exact Set.mem_union_right _ (Set.mem_singleton _)
      | some owner =>
          by_cases howner : owner ∈ J
          · change (if owner ∈ J then (fun who => M who owner)
                else q (subseq n)) ∈ C ∪ {q (subseq n)}
            rw [if_pos howner]
            apply Set.mem_union_left
            exact subset_convexHull ℝ _ ⟨⟨owner, howner⟩, rfl⟩
          · exact Set.mem_union_right _ (by simp [point, howner])
    have hpacketHull : residual (subseq n) ∈
        convexHull ℝ (C ∪ {q (subseq n)}) := by
      have hsum := (convex_convexHull ℝ _).sum_mem
        (t := Finset.univ) (w := fun index => coefficient (subseq n) index)
        (z := point)
        (fun index _ => by
          cases index with
          | none => exact (solution (subseq n)).cemetery_nonneg
          | some owner => exact (solution (subseq n)).singleton_nonneg owner)
        (by simpa only [coefficient, Fintype.sum_option] using
          (solution (subseq n)).total)
        (fun index _ => subset_convexHull ℝ _ (hpointMem index))
      convert hsum using 1
      funext who
      simp only [residual]
      rw [Fintype.sum_option]
      simp only [coefficient, point]
      congr 1
      rw [Finset.sum_apply]
      simp only [Pi.smul_apply, smul_eq_mul]
      apply Finset.sum_congr rfl
      intro owner _
      by_cases howner : owner ∈ J
      · simp [howner]
      · simp [howner, hsingleOutside owner howner]
    have hnotEndpoint := endpoint_not_mem_augmentedHull hCconvex
      hCnonempty (by simpa only [C, J] using hnot)
      (show (fun who => M who pivot) ∈ C from
        subset_convexHull ℝ _ ⟨⟨pivot, hpivot⟩, rfl⟩)
      (hqSegment (subseq n)) (hqNe (subseq n))
    have hpacketAugmented : residual (subseq n) ∈
        AugmentedHull M J y := by
      apply (convexHull_min ?_ (convex_convexHull ℝ _)) hpacketHull
      intro x hx
      rcases hx with hx | hx
      · exact subset_convexHull ℝ _ (Set.mem_union_left _ hx)
      · rw [Set.mem_singleton_iff] at hx
        subst x
        exact hqAugmented (subseq n)
    have hresidualEq : residual (subseq n) = y := by
      apply Set.mem_singleton_iff.mp
      rw [← hpoint]
      exact ⟨by simpa only [J] using hpacketAugmented,
        (hresidualDZero (subseq n)).1⟩
    exact hnotEndpoint (hresidualEq ▸ hpacketHull)
  have hnontrivial : 0 < ∑ owner, singleton owner := by
    have hsumNonnegative : 0 ≤ ∑ owner, singleton owner :=
      Finset.sum_nonneg fun owner _ => hsingletonNonneg owner
    apply lt_of_le_of_ne hsumNonnegative
    intro hsumZero
    have hcemeteryOne : cemetery = 1 := by linarith [htotal]
    have hsingleZero (owner : ι) : singleton owner = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (s := Finset.univ)
        (fun i _ => hsingletonNonneg i)).mp hsumZero.symm owner
        (Finset.mem_univ owner)
    apply hwy
    funext who
    simp [w, hcemeteryOne, hsingleZero]
  apply theorem33Conclusion_of_projective_packet M hy hw hbound hdiag hzero
    cemetery singleton hcemeteryNonneg hsingletonNonneg htotal
  · exact fun who => rfl
  · intro owner howner
    exact (mul_eq_zero.mp (hcomplementary owner)).resolve_left
      (ne_of_gt howner)
  · exact hnontrivial
  · exact hε

/-! Lemma 3.5: the strict-intersection case yields (F.1)--(F.5). -/
theorem lemma3_5
    (M : ι → ι → ℝ) {y : ι → ℝ} (hy : DZero M y)
    (hbound : MatrixPayoffsBounded M) (hdiag : ∀ i, M i i = 0) (hzero :
      ¬HasNontrivialZeroProjectiveLCPSolution M) (_hQ : QMatrix M)
    (_hnot : y ∉ SubfamilyHull M (ZeroCoordinates y))
    (hstrict : AugmentedHull M (ZeroCoordinates y) y ∩
      D M ≠ {y}) {ε : ℝ} (hε : 0 < ε) :
    Theorem33Conclusion M y ε := by
  have hyD : y ∈ D M := mem_D_of_DZero hy
  have hyAugmented : y ∈ AugmentedHull M (ZeroCoordinates y) y := by
    apply subset_convexHull ℝ
    exact Set.mem_union_right _ (Set.mem_singleton y)
  have hyIntersection : y ∈
      AugmentedHull M (ZeroCoordinates y) y ∩ D M :=
    ⟨hyAugmented, hyD⟩
  obtain ⟨q, hqIntersection, hqy⟩ :
      ∃ q ∈ AugmentedHull M (ZeroCoordinates y) y ∩ D M, q ≠ y := by
    by_contra hnone
    push Not at hnone
    apply hstrict
    apply Set.Subset.antisymm
    · intro x hx
      rw [Set.mem_singleton_iff]
      exact hnone x hx
    · intro x hx
      rw [Set.mem_singleton_iff] at hx
      simpa only [hx] using hyIntersection
  have hJ : (ZeroCoordinates y).Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty] at hempty
    letI : IsEmpty (ZeroCoordinates y : Type) :=
      ⟨fun owner => by simpa [hempty] using owner.property⟩
    have hrange : (Set.range fun i : ZeroCoordinates y =>
        fun who => M who i) = ∅ :=
      Set.range_eq_empty_iff.mpr inferInstance
    have hSempty : SubfamilyHull M (ZeroCoordinates y) = ∅ := by
      simp only [SubfamilyHull, hrange, convexHull_empty]
    have hqy' : q = y := by
      have := hqIntersection.1
      simp [AugmentedHull, hSempty] at this
      exact this
    exact hqy hqy'
  obtain ⟨s, hs, hqSegment⟩ :=
    mem_augmentedHull M (ZeroCoordinates y) hJ hqIntersection.1
  by_cases hsegmentCase :
      ∃ owner ∈ ZeroCoordinates y,
        ∃ p ∈ segment ℝ y (fun who => M who owner), p ∈ D M ∧ p ≠ y
  · obtain ⟨owner, howner, p, hpSegment, hpD, hpy⟩ := hsegmentCase
    have hcolumnNotD :=
      column_not_mem_D_of_no_nontrivial_zero_solution M hdiag hzero owner
    have hcolumnHull : (fun who => M who owner) ∈ ColumnConvexHull M :=
      subset_convexHull ℝ _ ⟨owner, rfl⟩
    have hcolumnNotOrthant :
        (fun who => M who owner) ∉ NonnegativeOrthant ι := by
      intro hnonnegative
      exact hcolumnNotD ⟨hcolumnHull, hnonnegative⟩
    obtain ⟨w, hwTail, hwFrontier⟩ :=
      exists_frontier_on_segment_of_mem_notMem hpD.2 hcolumnNotOrthant
    obtain ⟨hwNonnegative, hwZero⟩ :=
      frontier_nonnegativeOrthant_has_zero hwFrontier
    have hwHull : w ∈ ColumnConvexHull M :=
      (convex_convexHull ℝ _).segment_subset hpD.1 hcolumnHull hwTail
    have hwDZero : DZero M w := ⟨⟨hwHull, hwNonnegative⟩, hwZero⟩
    have hwFull : w ∈ segment ℝ y (fun who => M who owner) :=
      (convex_segment y (fun who => M who owner)).segment_subset
        hpSegment (right_mem_segment ℝ y (fun who => M who owner)) hwTail
    have hcolumnNe : (fun who => M who owner) ≠ y := by
      intro heq
      exact hcolumnNotD (heq ▸ hyD)
    have hwy : w ≠ y := by
      intro hwy
      exact endpoint_not_mem_tail_segment hpSegment hpy hcolumnNe (hwy ▸ hwTail)
    have hyowner : y owner = 0 := by
      simpa [ZeroCoordinates] using howner
    exact theorem33Conclusion_of_segment_boundary M hy hbound hdiag hzero
      owner hyowner hwDZero (segment_of_mem_segment hwFull) hwy hε
  · push Not at hsegmentCase
    obtain ⟨a, ha0, ha1, hq⟩ := segment_of_mem_segment hqSegment
    let ρ := 1 - a
    have hρpos : 0 < ρ := by
      have hane : a ≠ 1 := by
        intro ha
        apply hqy
        funext who
        rw [hq who, ha]
        ring
      dsimp only [ρ]
      exact lt_of_le_of_ne (sub_nonneg.mpr ha1)
        (Ne.symm (sub_ne_zero.mpr hane.symm))
    have hqAffine (who : ι) :
        q who = (1 - ρ) * y who + ρ * s who := by
      rw [hq who]
      dsimp only [ρ]
      ring
    let η := min ε (min ρ 1)
    have hηpos : 0 < η := lt_min hε (lt_min hρpos zero_lt_one)
    have hηε : η ≤ ε := min_le_left _ _
    have hηρ : η ≤ ρ := (min_le_right _ _).trans (min_le_left _ _)
    have hηone : η ≤ 1 := (min_le_right _ _).trans (min_le_right _ _)
    let inside : ι → ℝ := fun who =>
      (1 - η) * y who + η * s who
    have hinsideSegment : inside ∈ segment ℝ y q := by
      rw [segment_eq_image_lineMap]
      refine ⟨η / ρ, ⟨div_nonneg hηpos.le hρpos.le,
        (div_le_one hρpos).mpr hηρ⟩, ?_⟩
      ext who
      simp only [inside, AffineMap.lineMap_apply_module, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul]
      rw [hqAffine]
      field_simp [ne_of_gt hρpos]
      ring
    have hinsideD : inside ∈ D M :=
      (convex_D M).segment_subset hyD hqIntersection.2 hinsideSegment
    obtain ⟨owner, howner⟩ := hJ
    let extreme : ι → ℝ := fun who =>
      (1 - η) * y who + η * M who owner
    have hextremeSegment : extreme ∈
        segment ℝ y (fun who => M who owner) := by
      apply mem_segment_of_Segment
      refine ⟨1 - η, sub_nonneg.mpr hηone, by linarith, ?_⟩
      intro who
      simp only [extreme]
      ring
    have hextremeNe : extreme ≠ y := by
      intro heq
      have hcolumnNe := column_ne_of_no_nontrivial_zero_solution
        M hyD hdiag hzero owner
      apply hcolumnNe
      funext who
      have hcoordinate := congr_fun heq who
      simp only [extreme] at hcoordinate
      nlinarith
    have hextremeNotD : extreme ∉ D M := by
      intro hextremeD
      exact hextremeNe <|
        hsegmentCase owner howner extreme hextremeSegment hextremeD
    have hextremeHull : extreme ∈ ColumnConvexHull M :=
      (convex_convexHull ℝ _).segment_subset hyD.1
        (subset_convexHull ℝ _ ⟨owner, rfl⟩) hextremeSegment
    have hextremeNotOrthant : extreme ∉ NonnegativeOrthant ι := by
      intro hnonnegative
      exact hextremeNotD ⟨hextremeHull, hnonnegative⟩
    obtain ⟨w, hwSegment, hwFrontier⟩ :=
      exists_frontier_on_segment_of_mem_notMem hinsideD.2
        hextremeNotOrthant
    obtain ⟨hwNonnegative, hwZero⟩ :=
      frontier_nonnegativeOrthant_has_zero hwFrontier
    have hwHull : w ∈ ColumnConvexHull M :=
      (convex_convexHull ℝ _).segment_subset hinsideD.1
        hextremeHull hwSegment
    have hwDZero : DZero M w := ⟨⟨hwHull, hwNonnegative⟩, hwZero⟩
    have hinsideSlice : inside ∈ SubfamilyHull
        (fun who owner => (1 - η) * y who + η * M who owner)
        (ZeroCoordinates y) :=
      affine_slice_mem_subfamilyHull M (ZeroCoordinates y) η hs
    have hextremeSlice : extreme ∈ SubfamilyHull
        (fun who owner => (1 - η) * y who + η * M who owner)
        (ZeroCoordinates y) := by
      apply subset_convexHull ℝ
      exact ⟨⟨owner, howner⟩, rfl⟩
    have hwSlice : w ∈ SubfamilyHull
        (fun who owner => (1 - η) * y who + η * M who owner)
        (ZeroCoordinates y) :=
      (convex_convexHull ℝ _).segment_subset
        hinsideSlice hextremeSlice hwSegment
    exact theorem33Conclusion_of_slice_boundary M hy hwDZero hbound
      hdiag hzero hηpos hηone hηε hwSlice

/-! Theorem 3.3, under Theorem 2.13(2)'s standing hypotheses: the derived
matrix has zero diagonal, is Q, and its homogeneous projective problem has no
nontrivial solution. Every `y∈D₀` and `ε>0` then admits a building block. -/
theorem theorem3_3
    (M : ι → ι → ℝ) {y : ι → ℝ} (hy : DZero M y)
    (hbound : MatrixPayoffsBounded M) (hdiag : ∀ i, M i i = 0) (hzero :
      ¬HasNontrivialZeroProjectiveLCPSolution M) (hQ : QMatrix M)
    {ε : ℝ} (hε : 0 < ε) : Theorem33Conclusion M y ε := by
  by_cases hmember : y ∈ SubfamilyHull M (ZeroCoordinates y)
  · exact theorem33Conclusion_of_mem_subfamilyHull M hy hbound hdiag
      hzero hmember hε
  · by_cases hintersection :
        AugmentedHull M (ZeroCoordinates y) y ∩ D M = {y}
    · exact lemma3_4 M hy hbound hdiag hzero hQ hmember hintersection hε
    · exact lemma3_5 M hy hbound hdiag hzero hQ hmember hintersection hε

/-! **Theorem 3.6 (paper, corrected endpoint).** If `(X,d)` is a nonempty
complete metric space and `f:X→X` has no fixed point, then for every `c>0`
and `C≥0` there are `K` and `x¹,…,xᴷ` with
`Σ_k d(xᵏ,f(xᵏ))>C` and `Σ_{k<K}d(xᵏ⁺¹,f(xᵏ))<c`. The paper proof uses
transfinite recursion. The printed `c≥0` cannot include `c=0`, because the
second conclusion is then a strict inequality between a nonnegative sum and
zero. -/

/-! The displacement along a finite list `x¹,…,xᵏ`. -/
def PathDisplacement {X : Type*} [PseudoMetricSpace X]
    (f : X → X) : List X → ℝ
  | [] => 0
  | x :: xs => dist x (f x) + PathDisplacement f xs

/-! The tracking error of a finite list whose first point is intended to
follow `anchor`; subsequent points are intended to follow their predecessor
under `f`. -/
def PathTrackingFrom {X : Type*} [PseudoMetricSpace X]
    (f : X → X) (anchor : X) : List X → ℝ
  | [] => 0
  | x :: xs => dist x anchor + PathTrackingFrom f (f x) xs

theorem pathTrackingFrom_nonneg {X : Type*} [PseudoMetricSpace X]
    (f : X → X) (anchor : X) (xs : List X) :
    0 ≤ PathTrackingFrom f anchor xs := by
  induction xs generalizing anchor with
  | nil => simp [PathTrackingFrom]
  | cons x xs ih =>
      simp only [PathTrackingFrom]
      exact add_nonneg dist_nonneg (ih (f x))

/-! The finite-sequence conclusion of Theorem 3.6. The head is `x¹`; the
list contains `x²,…,xᵏ`, so its tracking error starts at `f(x¹)`. -/
def ApproximationWitness {X : Type*} [PseudoMetricSpace X]
    (f : X → X) (c C : ℝ) : Prop :=
  ∃ x : X, ∃ xs : List X,
    C < dist x (f x) + PathDisplacement f xs ∧
    PathTrackingFrom f (f x) xs < c

/-! Supremum of the displacement attainable from `anchor` while spending
less than half of the tracking budget. This is the Caristi potential in the
short proof of Theorem 3.6. -/
def RemainingDisplacement {X : Type*} [PseudoMetricSpace X]
    (f : X → X) (c : ℝ) (anchor : X) : ℝ :=
  sSup {value | ∃ xs : List X,
    PathTrackingFrom f anchor xs < c / 2 ∧
    value = PathDisplacement f xs}

/-! Theorem 3.6: a fixed-point-free map admits large displacement with small
tracking error on a finite sequence. -/
theorem theorem3_6 {X : Type*} [MetricSpace X] [Nonempty X]
    [CompleteSpace X] (f : X → X) (hfixed : ∀ x, f x ≠ x)
    (c C : ℝ) (hc : 0 < c) (hC : 0 ≤ C) :
    ApproximationWitness f c C := by
  by_contra hno
  have hpathBound {x : X} {xs : List X}
      (htracking : PathTrackingFrom f (f x) xs < c) :
      dist x (f x) + PathDisplacement f xs ≤ C := by
    by_contra hnot
    exact hno ⟨x, xs, lt_of_not_ge hnot, htracking⟩
  have hset_nonempty (anchor : X) :
      {value | ∃ xs : List X,
        PathTrackingFrom f anchor xs < c / 2 ∧
        value = PathDisplacement f xs}.Nonempty := by
    refine ⟨0, [], ?_, rfl⟩
    simp [PathTrackingFrom, hc]
  have hset_bdd (anchor : X) : BddAbove
      {value | ∃ xs : List X,
        PathTrackingFrom f anchor xs < c / 2 ∧
        value = PathDisplacement f xs} := by
    refine ⟨C, ?_⟩
    rintro value ⟨xs, htracking, rfl⟩
    cases xs with
    | nil => simpa [PathDisplacement] using hC
    | cons x xs =>
        apply hpathBound
        have htail := pathTrackingFrom_nonneg f (f x) xs
        have hdistance : 0 ≤ dist x anchor := dist_nonneg
        simp only [PathTrackingFrom] at htracking
        linarith
  let φ : X → ℝ := RemainingDisplacement f c
  have hφ_nonneg (anchor : X) : 0 ≤ φ anchor := by
    apply le_csSup (hset_bdd anchor)
    exact ⟨[], by simp [PathTrackingFrom, hc], rfl⟩
  have hφ_bdd : BddBelow (Set.range φ) := by
    exact ⟨0, by rintro _ ⟨anchor, rfl⟩; exact hφ_nonneg anchor⟩
  have hφ_lsc : LowerSemicontinuous φ := by
    rw [lowerSemicontinuous_iff]
    intro anchor y hy
    dsimp [φ, RemainingDisplacement] at hy ⊢
    obtain ⟨value, hvalue, hyvalue⟩ := exists_lt_of_lt_csSup
      (hset_nonempty anchor) hy
    obtain ⟨xs, htracking, rfl⟩ := hvalue
    have hcontinuous : ContinuousAt
        (fun nextAnchor => PathTrackingFrom f nextAnchor xs) anchor := by
      cases xs with
      | nil => simpa [PathTrackingFrom] using continuousAt_const
      | cons x xs =>
          simp only [PathTrackingFrom]
          fun_prop
    filter_upwards [hcontinuous.eventually (gt_mem_nhds htracking)]
      with nextAnchor hnext
    exact hyvalue.trans_le
      (le_csSup (hset_bdd nextAnchor) ⟨xs, hnext, rfl⟩)
  have hcaristi (x : X) : dist x (f x) ≤ φ x - φ (f x) := by
    have hsuple : φ (f x) ≤ φ x - dist x (f x) := by
      apply csSup_le (hset_nonempty (f x))
      intro value hvalue
      obtain ⟨xs, htracking, rfl⟩ := hvalue
      have hmem : dist x (f x) + PathDisplacement f xs ∈
          {value | ∃ ys : List X,
            PathTrackingFrom f x ys < c / 2 ∧
            value = PathDisplacement f ys} := by
        refine ⟨x :: xs, ?_, ?_⟩
        · simpa [PathTrackingFrom] using htracking
        · simp [PathDisplacement]
      have hupper := le_csSup (hset_bdd x) hmem
      dsimp [φ, RemainingDisplacement]
      linarith
    linarith
  obtain ⟨x, hx⟩ := MathUE.exists_fixedPoint_of_caristi
    f φ hφ_lsc hφ_bdd hcaristi
  exact hfixed x hx

/-! **Lemmas 3.8--3.10 (paper).** For the kiloblock strategy `ξ*` built from
Theorem 3.3 and Theorem 3.6, the paper proves (i) its payoff is within
`2ε` of `w(yᴷ)` for normal players, (ii) continuation by any normal player
still terminates with probability at least `1-ε` before the final kiloblock,
and (iii) every pure deviation gains at most `5ε`. -/

/-! A kiloblock construction carries the actual public-signal behavior
profile, its finite chain of Theorem 3.3 blocks, and the history event that the
final kiloblock has not started. It carries no asserted payoff or deviation
bound. -/

/-! The control state between live decisions. `choose k` means that the next
signal selects a type in kiloblock `k`; `resume` ignores the next signal and
continues a previously selected type. The source's order is reversed: the
construction starts at the last index and ends after index zero. -/
inductive KiloblockPhase (table : Table ι) (lastIndex : ℕ)
  | choose (k : Fin (lastIndex + 1))
  | resume (k : Fin (lastIndex + 1))
      (choice : Option (NormalPlayer table)) (remaining : ℕ)
  | final

/-! The schedule state at an actual history. Draw and active states are
separated because the public-signal adapter draws before every decision. -/
inductive KiloblockMode (table : Table ι) (lastIndex : ℕ)
  | draw (phase : KiloblockPhase table lastIndex)
  | active (k : Fin (lastIndex + 1))
      (choice : Option (NormalPlayer table)) (remaining : ℕ)
  | finalActive
  | absorbed (origin : Option (Fin (lastIndex + 1)))

/-! Move from original index `k` to `k-1`, or to the final infinite tail
when `k=0`. -/
def precedingKiloblockPhase (table : Table ι) {lastIndex : ℕ}
    (k : Fin (lastIndex + 1)) : KiloblockPhase table lastIndex :=
  if hk : k.1 = 0 then .final else .choose ⟨k.1 - 1, by omega⟩

/-! A type-zero draw always advances. A failed type-`i` attempt restarts the
same auxiliary game in the `w` branch of (F.1), but advances in its `y`
branch. The latter exit is implicit in Figures 1--2 and is omitted from the
later prose partition; recording it here is the necessary source correction. -/
def phaseAfterAttempt (table : Table ι) {lastIndex : ℕ}
    (continuation : Fin (lastIndex + 1) → NormalPlayer table →
      AttemptContinuation)
    (k : Fin (lastIndex + 1)) (choice : Option (NormalPlayer table)) :
    KiloblockPhase table lastIndex :=
  match choice with
  | none => precedingKiloblockPhase table k
  | some owner =>
      match continuation k owner with
      | .restart => .choose k
      | .advance => precedingKiloblockPhase table k

/-! The schedule mode agrees with the actual public-game state. -/
def KiloblockMode.MatchesState
    {table : Table ι} {Signal : Type} [Fintype Signal] {lastIndex : ℕ}
    (mode : KiloblockMode table lastIndex)
    (state : PublicQuittingState ι Signal) : Prop :=
  match mode, state with
  | .draw _, .draw => True
  | .active _ _ _, .active _ => True
  | .finalActive, .active _ => True
  | .absorbed _, .absorbed _ => True
  | _, _ => False

/-! Exact one-step automaton of the accepted manuscript's kiloblock
schedule. A selected player is kept for `mesh k` active decisions. Failure
then follows the branch-sensitive exit rule above; type zero advances after
an all-Continue block of the same length. -/
def KiloblockModeStep
    {table : Table ι} {Signal : Type} [Fintype Signal] {lastIndex : ℕ}
    (mesh : Fin (lastIndex + 1) → ℕ)
    (selector : Fin (lastIndex + 1) → Signal →
      Option (NormalPlayer table))
    (continuation : Fin (lastIndex + 1) → NormalPlayer table →
      AttemptContinuation)
    (mode : KiloblockMode table lastIndex) (action : ι → Bool)
    (nextState : PublicQuittingState ι Signal)
    (nextMode : KiloblockMode table lastIndex) : Prop := by
  classical
  exact match mode with
  | .draw (.choose k) =>
      match nextState with
      | .active signal =>
          nextMode = .active k (selector k signal) (mesh k)
      | _ => False
  | .draw (.resume k choice remaining) =>
      match nextState with
      | .active _ => nextMode = .active k choice remaining
      | _ => False
  | .draw .final =>
      match nextState with
      | .active _ => nextMode = .finalActive
      | _ => False
  | .active k choice remaining =>
      if hquit : ({who | action who = true} : Finset ι).Nonempty then
        nextState = .absorbed ⟨_, hquit⟩ ∧ nextMode = .absorbed (some k)
      else if remaining ≤ 1 then
        nextState = .draw ∧
          nextMode = .draw
            (phaseAfterAttempt table continuation k choice)
      else
        nextState = .draw ∧
          nextMode = .draw (.resume k choice (remaining - 1))
  | .finalActive =>
      if hquit : ({who | action who = true} : Finset ι).Nonempty then
        nextState = .absorbed ⟨_, hquit⟩ ∧ nextMode = .absorbed none
      else nextState = .draw ∧ nextMode = .draw .final
  | .absorbed origin =>
      match nextState with
      | .absorbed _ => nextMode = .absorbed origin
      | _ => False

/-! The total displacement in (A.1''). -/
def KiloblockDisplacement {table : Table ι} {ε : ℝ} {lastIndex : ℕ}
    (point : Fin (lastIndex + 1) → NormalPlayer table → ℝ)
    (block : ∀ k, BuildingBlock (NormalMatrix table) (point k) ε) : ℝ :=
  ∑ k, dist (point k) (block k).w

/-! The adjacent mismatch in (A.2''):
`Σ_{k<K} ‖y^{k+1}-w(y^k)‖∞`. -/
def KiloblockTracking {table : Table ι} {ε : ℝ} {lastIndex : ℕ}
    (point : Fin (lastIndex + 1) → NormalPlayer table → ℝ)
    (block : ∀ k, BuildingBlock (NormalMatrix table) (point k) ε) : ℝ :=
  ∑ k : Fin lastIndex,
    dist (point ⟨k.1 + 1, by omega⟩) (block ⟨k.1, by omega⟩).w

/-! The displacement threshold `C` chosen in Section 3.3.5. -/
def KiloblockDisplacementThreshold (table : Table ι) (ε : ℝ) : ℝ :=
  ((Nat.choose (Fintype.card (NormalPlayer table)) 2 : ℕ) : ℝ) *
    (2 * (1 + ε)) / ε ^ 2

structure KiloblockConstruction
    (table : Table ι) (ε : ℝ) where
  soloExitNormalized : SoloExitNormalized table
  payoffsBounded : TablePayoffsBounded table
  profile : SunspotProfile table
  blockCount : ℕ
  point : Fin (blockCount + 1) → NormalPlayer table → ℝ
  point_boundary : ∀ k, DZero (NormalMatrix table) (point k)
  buildingBlock : ∀ k,
    BuildingBlock (NormalMatrix table) (point k) ε
  epsilon_pos : 0 < ε
  epsilon_lt_one : ε < 1
  negativeMargin : ℝ
  negativeMargin_pos : 0 < negativeMargin
  accuracy_below_margin :
    ((2 * Fintype.card (NormalPlayer table) + 1 : ℕ) : ℝ) * ε <
      negativeMargin
  displacement_large : KiloblockDisplacementThreshold table ε <
    KiloblockDisplacement point buildingBlock
  tracking_small : KiloblockTracking point buildingBlock < ε
  column_negative : ∀ owner,
    ∃ who, NormalMatrix table who owner <
      -negativeMargin
  attempt : ∀ k owner,
    BuildingAttempt (NormalMatrix table) (point k) ε
      (buildingBlock k) owner
  mesh : Fin (blockCount + 1) → ℕ
  mesh_pos : ∀ k, 0 < mesh k
  mesh_hazard_small : ∀ k owner,
    quittingMeshHazard (attempt k owner).quitWeight (mesh k) < ε
  mesh_survival : ∀ k owner,
    (1 - quittingMeshHazard (attempt k owner).quitWeight (mesh k)) ^
        mesh k =
      1 - (attempt k owner).quitWeight
  signalSelector : Fin (blockCount + 1) →
    Fin (profile.signalCount + 1) → Option (NormalPlayer table)
  signalSelector_law : ∀ k,
    profile.signalLaw.map (signalSelector k) = (buildingBlock k).z.toPMF
  mode : ∀ t,
    (publicQuittingGame table profile.signalLaw).Hist t →
      KiloblockMode table blockCount
  mode_initial : mode 0
    ((publicQuittingGame table profile.signalLaw).emptyHist
      (PublicQuittingState.draw)) =
      .draw (.choose (Fin.last blockCount))
  mode_state : ∀ t history, (mode t history).MatchesState history.2
  mode_remaining_pos : ∀ t history k choice remaining,
    mode t history = .active k choice remaining ∨
      mode t history = .draw (.resume k choice remaining) →
        0 < remaining
  mode_step : ∀ t history action nextState,
    nextState ∈ ((publicQuittingGame table profile.signalLaw).transition
      history.2 action).support →
    KiloblockModeStep mesh signalSelector
      (fun k owner => (attempt k owner).continuation)
      (mode t history) action nextState
      (mode (t + 1) (Fin.snoc history.1 (history.2, action), nextState))
  strategy_eq : ∀ who t history,
    profile.strategy who t history =
      match mode t history with
      | .active k (some owner) _ =>
          if _hwho : who = owner.1 then
            quittingMeshHazardCoin (attempt k owner).quitWeight (mesh k)
              (attempt k owner).quitWeight_pos.le
              (attempt k owner).quitWeight_lt_one
          else PMF.pure false
      | _ => PMF.pure false

theorem KiloblockConstruction.normalMatrix_bounded
    {table : Table ι} {ε : ℝ}
    (construction : KiloblockConstruction table ε) :
    MatrixPayoffsBounded (NormalMatrix table) := by
  intro who owner
  exact construction.payoffsBounded.1
    (quittingProjectiveSingletonTerminal owner.1) who.1

/-! Total type-`i` mass across the finite kiloblock chain. -/
def KiloblockConstruction.singletonMass
    {table : Table ι} {ε : ℝ}
    (construction : KiloblockConstruction table ε) : ℝ :=
  ∑ k, ∑ owner, (construction.buildingBlock k).z.singleton owner

theorem KiloblockConstruction.displacement_le_twice_singletonMass
    {table : Table ι} {ε : ℝ}
    (construction : KiloblockConstruction table ε) :
    KiloblockDisplacement construction.point construction.buildingBlock ≤
      2 * construction.singletonMass := by
  unfold KiloblockDisplacement KiloblockConstruction.singletonMass
  calc
    ∑ k, dist (construction.point k)
        (construction.buildingBlock k).w ≤
        ∑ k, 2 * ∑ owner,
          (construction.buildingBlock k).z.singleton owner := by
      apply Finset.sum_le_sum
      intro k _
      exact BuildingBlock.displacement_le_twice_singletonMass
        (construction.buildingBlock k) construction.normalMatrix_bounded
    _ = 2 * ∑ k, ∑ owner,
        (construction.buildingBlock k).z.singleton owner := by
      rw [Finset.mul_sum]

theorem KiloblockConstruction.half_displacementThreshold_lt_singletonMass
    {table : Table ι} {ε : ℝ}
    (construction : KiloblockConstruction table ε) :
    KiloblockDisplacementThreshold table ε / 2 <
      construction.singletonMass := by
  have hle := construction.displacement_le_twice_singletonMass
  have hlarge := construction.displacement_large
  linarith

/-! Unnormalized mass with which a type draw leaves the restart loop of one
kiloblock. A restart attempt leaves only when its owner quits; an advance
attempt leaves whether or not its owner quits. -/
def KiloblockConstruction.attemptExitWeight
    {table : Table ι} {ε : ℝ}
    (construction : KiloblockConstruction table ε)
    (k : Fin (construction.blockCount + 1))
    (owner : NormalPlayer table) : ℝ :=
  match (construction.attempt k owner).continuation with
  | .restart => (construction.attempt k owner).quitWeight
  | .advance => 1

def KiloblockConstruction.exitMass
    {table : Table ι} {ε : ℝ}
    (construction : KiloblockConstruction table ε)
    (k : Fin (construction.blockCount + 1)) : ℝ :=
  (construction.buildingBlock k).z.cemetery +
    ∑ owner, (construction.buildingBlock k).z.singleton owner *
      construction.attemptExitWeight k owner

def KiloblockConstruction.absorbMass
    {table : Table ι} {ε : ℝ}
    (construction : KiloblockConstruction table ε)
    (k : Fin (construction.blockCount + 1))
    (owner : NormalPlayer table) : ℝ :=
  (construction.buildingBlock k).z.singleton owner *
    (construction.attempt k owner).quitWeight

def KiloblockConstruction.attemptAdvanceWeight
    {table : Table ι} {ε : ℝ}
    (construction : KiloblockConstruction table ε)
    (k : Fin (construction.blockCount + 1))
    (owner : NormalPlayer table) : ℝ :=
  match (construction.attempt k owner).continuation with
  | .restart => 0
  | .advance => 1 - (construction.attempt k owner).quitWeight

def KiloblockConstruction.advanceMass
    {table : Table ι} {ε : ℝ}
    (construction : KiloblockConstruction table ε)
    (k : Fin (construction.blockCount + 1)) : ℝ :=
  (construction.buildingBlock k).z.cemetery +
    ∑ owner, (construction.buildingBlock k).z.singleton owner *
      construction.attemptAdvanceWeight k owner

theorem KiloblockConstruction.exitMass_eq
    {table : Table ι} {ε : ℝ}
    (construction : KiloblockConstruction table ε)
    (k : Fin (construction.blockCount + 1)) :
    construction.exitMass k = construction.advanceMass k +
      ∑ owner, construction.absorbMass k owner := by
  unfold KiloblockConstruction.exitMass
    KiloblockConstruction.advanceMass
    KiloblockConstruction.absorbMass
    KiloblockConstruction.attemptAdvanceWeight
    KiloblockConstruction.attemptExitWeight
  rw [add_assoc, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro owner _
  cases (construction.attempt k owner).continuation <;> ring

theorem KiloblockConstruction.exitMass_pos
    {table : Table ι} {ε : ℝ}
    (construction : KiloblockConstruction table ε)
    (k : Fin (construction.blockCount + 1)) :
    0 < construction.exitMass k := by
  obtain ⟨owner, _, howner⟩ :=
    (Finset.sum_pos_iff_of_nonneg (fun owner _ =>
      (construction.buildingBlock k).z.singleton_nonneg owner)).mp
      (construction.buildingBlock k).nontrivial
  have habsorb : 0 < construction.absorbMass k owner :=
    mul_pos howner (construction.attempt k owner).quitWeight_pos
  rw [construction.exitMass_eq k]
  have hadvance : 0 ≤ construction.advanceMass k := by
    unfold KiloblockConstruction.advanceMass
    apply add_nonneg (construction.buildingBlock k).z.cemetery_nonneg
    apply Finset.sum_nonneg
    intro other _
    apply mul_nonneg
    · exact (construction.buildingBlock k).z.singleton_nonneg other
    · unfold KiloblockConstruction.attemptAdvanceWeight
      split
      · exact le_rfl
      · exact sub_nonneg.mpr
          (construction.attempt k other).quitWeight_lt_one.le
  have hsumAbsorb : 0 < ∑ other, construction.absorbMass k other :=
    (Finset.sum_pos_iff_of_nonneg (fun other _ =>
      mul_nonneg ((construction.buildingBlock k).z.singleton_nonneg other)
        (construction.attempt k other).quitWeight_pos.le)).mpr
      ⟨owner, Finset.mem_univ owner, habsorb⟩
  exact add_pos_of_nonneg_of_pos hadvance hsumAbsorb

def KiloblockConstruction.macroAbsorbProbability
    {table : Table ι} {ε : ℝ}
    (construction : KiloblockConstruction table ε)
    (k : Fin (construction.blockCount + 1))
    (owner : NormalPlayer table) : ℝ :=
  construction.absorbMass k owner / construction.exitMass k

def KiloblockConstruction.macroAdvanceProbability
    {table : Table ι} {ε : ℝ}
    (construction : KiloblockConstruction table ε)
    (k : Fin (construction.blockCount + 1)) : ℝ :=
  construction.advanceMass k / construction.exitMass k

theorem KiloblockConstruction.macroProbability_total
    {table : Table ι} {ε : ℝ}
    (construction : KiloblockConstruction table ε)
    (k : Fin (construction.blockCount + 1)) :
    construction.macroAdvanceProbability k +
      ∑ owner, construction.macroAbsorbProbability k owner = 1 := by
  unfold KiloblockConstruction.macroAdvanceProbability
    KiloblockConstruction.macroAbsorbProbability
  rw [← Finset.sum_div, ← add_div, ← construction.exitMass_eq k]
  exact div_self (ne_of_gt (construction.exitMass_pos k))

private theorem KiloblockConstruction.attempt_account
    {table : Table ι} {ε : ℝ}
    (construction : KiloblockConstruction table ε)
    (k : Fin (construction.blockCount + 1))
    (owner who : NormalPlayer table) :
    construction.attemptExitWeight k owner *
          (construction.buildingBlock k).w who -
        construction.attemptAdvanceWeight k owner *
          construction.point k who -
        (construction.attempt k owner).quitWeight *
          NormalMatrix table who owner =
      (construction.buildingBlock k).w who -
        (construction.buildingBlock k).wi owner who := by
  unfold KiloblockConstruction.attemptExitWeight
    KiloblockConstruction.attemptAdvanceWeight
  cases hbranch : (construction.attempt k owner).continuation with
  | restart =>
      rw [(construction.attempt k owner).payoff who]
      simp only [hbranch]
      ring
  | advance =>
      rw [(construction.attempt k owner).payoff who]
      simp only [hbranch]
      ring

/-! Collapsing all restart attempts in one kiloblock gives the exact macro
balance between singleton absorption and advancement to `y`. -/
theorem KiloblockConstruction.exitMass_mul_w
    {table : Table ι} {ε : ℝ}
    (construction : KiloblockConstruction table ε)
    (k : Fin (construction.blockCount + 1))
    (who : NormalPlayer table) :
    construction.exitMass k * (construction.buildingBlock k).w who =
      construction.advanceMass k * construction.point k who +
        ∑ owner, construction.absorbMass k owner *
          NormalMatrix table who owner := by
  have htotal := (construction.buildingBlock k).z.total
  have hbalance := (construction.buildingBlock k).balance who
  have haccount :
      ∑ owner, (construction.buildingBlock k).z.singleton owner *
          (construction.attemptExitWeight k owner *
              (construction.buildingBlock k).w who -
            construction.attemptAdvanceWeight k owner *
              construction.point k who -
            (construction.attempt k owner).quitWeight *
              NormalMatrix table who owner) =
        ∑ owner, (construction.buildingBlock k).z.singleton owner *
          ((construction.buildingBlock k).w who -
            (construction.buildingBlock k).wi owner who) := by
    apply Finset.sum_congr rfl
    intro owner _
    rw [construction.attempt_account k owner who]
  unfold KiloblockConstruction.exitMass
    KiloblockConstruction.advanceMass
    KiloblockConstruction.absorbMass
  have haccount' := haccount
  simp only [mul_sub] at haccount'
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib] at haccount'
  rw [Finset.sum_sub_distrib] at haccount'
  rw [add_mul, add_mul, Finset.sum_mul, Finset.sum_mul]
  simp_rw [mul_assoc]
  have hsingletonMul :
      ∑ owner, (construction.buildingBlock k).z.singleton owner *
          (construction.buildingBlock k).w who =
        (∑ owner, (construction.buildingBlock k).z.singleton owner) *
          (construction.buildingBlock k).w who := by
    rw [Finset.sum_mul]
  linear_combination haccount' +
    ((construction.buildingBlock k).w who) * htotal + hbalance + hsingletonMul

theorem KiloblockConstruction.macroAbsorbProbability_nonneg
    {table : Table ι} {ε : ℝ}
    (construction : KiloblockConstruction table ε)
    (k : Fin (construction.blockCount + 1))
    (owner : NormalPlayer table) :
    0 ≤ construction.macroAbsorbProbability k owner := by
  exact div_nonneg
    (mul_nonneg ((construction.buildingBlock k).z.singleton_nonneg owner)
      (construction.attempt k owner).quitWeight_pos.le)
    (construction.exitMass_pos k).le

theorem KiloblockConstruction.macroAdvanceProbability_nonneg
    {table : Table ι} {ε : ℝ}
    (construction : KiloblockConstruction table ε)
    (k : Fin (construction.blockCount + 1)) :
    0 ≤ construction.macroAdvanceProbability k := by
  unfold KiloblockConstruction.macroAdvanceProbability
  apply div_nonneg _ (construction.exitMass_pos k).le
  unfold KiloblockConstruction.advanceMass
  apply add_nonneg (construction.buildingBlock k).z.cemetery_nonneg
  apply Finset.sum_nonneg
  intro owner _
  apply mul_nonneg ((construction.buildingBlock k).z.singleton_nonneg owner)
  unfold KiloblockConstruction.attemptAdvanceWeight
  split
  · exact le_rfl
  · exact sub_nonneg.mpr (construction.attempt k owner).quitWeight_lt_one.le

/-! Exact normalized form of the collapsed kiloblock balance. -/
theorem KiloblockConstruction.macro_balance
    {table : Table ι} {ε : ℝ}
    (construction : KiloblockConstruction table ε)
    (k : Fin (construction.blockCount + 1))
    (who : NormalPlayer table) :
    (construction.buildingBlock k).w who =
      construction.macroAdvanceProbability k * construction.point k who +
        ∑ owner, construction.macroAbsorbProbability k owner *
          NormalMatrix table who owner := by
  have hbalance := construction.exitMass_mul_w k who
  have hne : construction.exitMass k ≠ 0 := ne_of_gt (construction.exitMass_pos k)
  unfold KiloblockConstruction.macroAdvanceProbability
    KiloblockConstruction.macroAbsorbProbability
  simp_rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div, ← add_div]
  apply (eq_div_iff hne).2
  simpa only [mul_comm] using hbalance

/-! The collapsed version of Eq. (14): displacement is bounded by twice
the actual probability of absorption while crossing the kiloblock. Unlike
the printed `z`-bound, this remains valid for both branches of (F.1). -/
theorem KiloblockConstruction.blockDisplacement_le_two_mul_macroAbsorption
    {table : Table ι} {ε : ℝ}
    (construction : KiloblockConstruction table ε)
    (k : Fin (construction.blockCount + 1)) :
    dist (construction.point k) (construction.buildingBlock k).w ≤
      2 * ∑ owner, construction.macroAbsorbProbability k owner := by
  rw [dist_eq_norm]
  have hright : 0 ≤ 2 *
      ∑ owner, construction.macroAbsorbProbability k owner :=
    mul_nonneg (by norm_num) (Finset.sum_nonneg fun owner _ =>
      construction.macroAbsorbProbability_nonneg k owner)
  apply (pi_norm_le_iff_of_nonneg hright).2
  intro who
  rw [Real.norm_eq_abs, Pi.sub_apply]
  have htotal := construction.macroProbability_total k
  have hbalance := construction.macro_balance k who
  have hidentity : construction.point k who -
      (construction.buildingBlock k).w who =
        ∑ owner, construction.macroAbsorbProbability k owner *
          (construction.point k who - NormalMatrix table who owner) := by
    calc
      construction.point k who - (construction.buildingBlock k).w who =
          construction.point k who -
            (construction.macroAdvanceProbability k * construction.point k who +
              ∑ owner, construction.macroAbsorbProbability k owner *
                NormalMatrix table who owner) := by rw [hbalance]
      _ = (∑ owner, construction.macroAbsorbProbability k owner) *
            construction.point k who -
          ∑ owner, construction.macroAbsorbProbability k owner *
            NormalMatrix table who owner := by
          have hcoefficient :
              1 - construction.macroAdvanceProbability k =
                ∑ owner, construction.macroAbsorbProbability k owner := by
            linarith
          rw [← hcoefficient]
          ring
      _ = _ := by
        rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro owner _
        ring
  rw [hidentity]
  calc
    |∑ owner, construction.macroAbsorbProbability k owner *
        (construction.point k who - NormalMatrix table who owner)| ≤
        ∑ owner, |construction.macroAbsorbProbability k owner *
          (construction.point k who - NormalMatrix table who owner)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ owner, construction.macroAbsorbProbability k owner * 2 := by
      apply Finset.sum_le_sum
      intro owner _
      rw [abs_mul, abs_of_nonneg
        (construction.macroAbsorbProbability_nonneg k owner)]
      apply mul_le_mul_of_nonneg_left _
        (construction.macroAbsorbProbability_nonneg k owner)
      apply (abs_sub _ _).trans
      have hpoint := abs_le_one_of_mem_D construction.normalMatrix_bounded
        (construction.point_boundary k).1 who
      have hmatrix := construction.normalMatrix_bounded who owner
      linarith
    _ = 2 * ∑ owner, construction.macroAbsorbProbability k owner := by
      rw [← Finset.sum_mul]
      ring

def KiloblockConstruction.totalMacroAbsorption
    {table : Table ι} {ε : ℝ}
    (construction : KiloblockConstruction table ε) : ℝ :=
  ∑ k, ∑ owner, construction.macroAbsorbProbability k owner

theorem KiloblockConstruction.half_displacementThreshold_lt_totalMacroAbsorption
    {table : Table ι} {ε : ℝ}
    (construction : KiloblockConstruction table ε) :
    KiloblockDisplacementThreshold table ε / 2 <
      construction.totalMacroAbsorption := by
  have hbound : KiloblockDisplacement construction.point
      construction.buildingBlock ≤ 2 * construction.totalMacroAbsorption := by
    unfold KiloblockDisplacement KiloblockConstruction.totalMacroAbsorption
    calc
      ∑ k, dist (construction.point k) (construction.buildingBlock k).w ≤
          ∑ k, 2 * ∑ owner,
            construction.macroAbsorbProbability k owner := by
        apply Finset.sum_le_sum
        intro k _
        exact construction.blockDisplacement_le_two_mul_macroAbsorption k
      _ = 2 * ∑ k, ∑ owner,
          construction.macroAbsorbProbability k owner := by
        rw [Finset.mul_sum]
  linarith [construction.displacement_large]

def KiloblockConstruction.macroAbsorptionProbability
    {table : Table ι} {ε : ℝ}
    (construction : KiloblockConstruction table ε)
    (k : Fin (construction.blockCount + 1)) : ℝ :=
  ∑ owner, construction.macroAbsorbProbability k owner

theorem KiloblockConstruction.macroAbsorptionProbability_nonneg
    {table : Table ι} {ε : ℝ}
    (construction : KiloblockConstruction table ε)
    (k : Fin (construction.blockCount + 1)) :
    0 ≤ construction.macroAbsorptionProbability k :=
  Finset.sum_nonneg fun owner _ =>
    construction.macroAbsorbProbability_nonneg k owner

theorem KiloblockConstruction.macroAbsorptionProbability_le_one
    {table : Table ι} {ε : ℝ}
    (construction : KiloblockConstruction table ε)
    (k : Fin (construction.blockCount + 1)) :
    construction.macroAbsorptionProbability k ≤ 1 := by
  have htotal := construction.macroProbability_total k
  have hadvance := construction.macroAdvanceProbability_nonneg k
  unfold KiloblockConstruction.macroAbsorptionProbability
  linarith

theorem KiloblockConstruction.macroAdvanceProbability_eq_one_sub
    {table : Table ι} {ε : ℝ}
    (construction : KiloblockConstruction table ε)
    (k : Fin (construction.blockCount + 1)) :
    construction.macroAdvanceProbability k =
      1 - construction.macroAbsorptionProbability k := by
  have htotal := construction.macroProbability_total k
  unfold KiloblockConstruction.macroAbsorptionProbability
  linarith

def KiloblockConstruction.macroSurvivalProbability
    {table : Table ι} {ε : ℝ}
    (construction : KiloblockConstruction table ε) : ℝ :=
  ∏ k, construction.macroAdvanceProbability k

theorem KiloblockConstruction.two_le_normalPlayer_card
    {table : Table ι} {ε : ℝ}
    (construction : KiloblockConstruction table ε) :
    2 ≤ Fintype.card (NormalPlayer table) := by
  let k : Fin (construction.blockCount + 1) := ⟨0, by omega⟩
  obtain ⟨owner, _, howner⟩ :=
    (Finset.sum_pos_iff_of_nonneg (fun owner _ =>
      (construction.buildingBlock k).z.singleton_nonneg owner)).mp
      (construction.buildingBlock k).nontrivial
  obtain ⟨who, hnegative⟩ := construction.column_negative owner
  have hne : who ≠ owner := by
    intro heq
    subst who
    have hzero : NormalMatrix table owner owner = 0 :=
      construction.soloExitNormalized owner.1
    linarith [construction.negativeMargin_pos]
  by_contra hcard
  have hcardOne : Fintype.card (NormalPlayer table) ≤ 1 := by omega
  exact hne ((Fintype.card_le_one_iff.mp hcardOne) who owner)

theorem KiloblockConstruction.one_le_choose_normalPlayer_two
    {table : Table ι} {ε : ℝ}
    (construction : KiloblockConstruction table ε) :
    1 ≤ Nat.choose (Fintype.card (NormalPlayer table)) 2 := by
  have hpositive := Nat.choose_pos construction.two_le_normalPlayer_card
  omega

theorem KiloblockConstruction.inv_epsilon_lt_totalMacroAbsorption
    {table : Table ι} {ε : ℝ}
    (construction : KiloblockConstruction table ε) :
    ε⁻¹ < construction.totalMacroAbsorption := by
  have hlarge := construction.half_displacementThreshold_lt_totalMacroAbsorption
  have hchoose : (1 : ℝ) ≤
      (Nat.choose (Fintype.card (NormalPlayer table)) 2 : ℝ) := by
    exact_mod_cast construction.one_le_choose_normalPlayer_two
  have hε := construction.epsilon_pos
  have hthreshold : ε⁻¹ < KiloblockDisplacementThreshold table ε / 2 := by
    unfold KiloblockDisplacementThreshold
    rw [inv_eq_one_div]
    apply (div_lt_iff₀ hε).2
    have hεsq : 0 < ε ^ 2 := sq_pos_of_pos hε
    field_simp [ne_of_gt hε]
    nlinarith [mul_pos hε hε]
  exact hthreshold.trans hlarge

theorem KiloblockConstruction.macroSurvival_mul_one_add_total_le_one
    {table : Table ι} {ε : ℝ}
    (construction : KiloblockConstruction table ε) :
    construction.macroSurvivalProbability *
      (1 + construction.totalMacroAbsorption) ≤ 1 := by
  let charge : ℕ → ℝ := fun j =>
    if hj : j < construction.blockCount + 1 then
      construction.macroAbsorptionProbability ⟨j, hj⟩
    else 0
  have hcharge0 : ∀ j, 0 ≤ charge j := by
    intro j
    simp only [charge]
    split
    · exact construction.macroAbsorptionProbability_nonneg _
    · exact le_rfl
  have hcharge1 : ∀ j, charge j ≤ 1 := by
    intro j
    simp only [charge]
    split
    · exact construction.macroAbsorptionProbability_le_one _
    · exact zero_le_one
  have hmain := Math.prod_one_sub_mul_one_add_sum_range_le_one
    charge hcharge0 hcharge1 0 (construction.blockCount + 1)
  have hsum : (∑ j ∈ Finset.range (construction.blockCount + 1), charge j) =
      construction.totalMacroAbsorption := by
    rw [← Fin.sum_univ_eq_sum_range]
    unfold KiloblockConstruction.totalMacroAbsorption
    apply Finset.sum_congr rfl
    intro k _
    rw [show charge k.1 = construction.macroAbsorptionProbability k by
      simp only [charge, dif_pos k.isLt]]
    rfl
  have hprod : (∏ j ∈ Finset.range (construction.blockCount + 1),
      (1 - charge j)) = construction.macroSurvivalProbability := by
    rw [← Fin.prod_univ_eq_prod_range]
    unfold KiloblockConstruction.macroSurvivalProbability
    apply Finset.prod_congr rfl
    intro k _
    simp only [charge, dif_pos k.isLt]
    exact (construction.macroAdvanceProbability_eq_one_sub k).symm
  simp only [zero_add] at hmain
  rw [hsum, hprod] at hmain
  exact hmain

theorem KiloblockConstruction.inv_epsilon_sq_lt_totalMacroAbsorption
    {table : Table ι} {ε : ℝ}
    (construction : KiloblockConstruction table ε) :
    (ε ^ 2)⁻¹ < construction.totalMacroAbsorption := by
  have hlarge := construction.half_displacementThreshold_lt_totalMacroAbsorption
  have hchoose : (1 : ℝ) ≤
      (Nat.choose (Fintype.card (NormalPlayer table)) 2 : ℝ) := by
    exact_mod_cast construction.one_le_choose_normalPlayer_two
  have hεsq : 0 < ε ^ 2 := sq_pos_of_pos construction.epsilon_pos
  have hnumerator : (1 : ℝ) <
      (Nat.choose (Fintype.card (NormalPlayer table)) 2 : ℝ) * (1 + ε) := by
    nlinarith [construction.epsilon_pos]
  have hthreshold : (ε ^ 2)⁻¹ <
      KiloblockDisplacementThreshold table ε / 2 := by
    calc
      (ε ^ 2)⁻¹ = (1 : ℝ) / (ε ^ 2) := by simp
      _ < (Nat.choose (Fintype.card (NormalPlayer table)) 2 : ℝ) *
          (1 + ε) / (ε ^ 2) :=
        (div_lt_div_iff_of_pos_right hεsq).2 hnumerator
      _ = KiloblockDisplacementThreshold table ε / 2 := by
        unfold KiloblockDisplacementThreshold
        ring
  exact hthreshold.trans hlarge

/-! The corrected global estimate. The source applies (14) to the raw type
mass `z`; the branch-sensitive construction instead applies the collapsed
identity above to actual macro hazards. The original `1/ε²` displacement
budget actually gives the stronger survival bound `ε²`. -/
theorem KiloblockConstruction.macroSurvivalProbability_lt_epsilon_sq
    {table : Table ι} {ε : ℝ}
    (construction : KiloblockConstruction table ε) :
    construction.macroSurvivalProbability < ε ^ 2 := by
  have hmain := construction.macroSurvival_mul_one_add_total_le_one
  have hfactor : 0 < 1 + construction.totalMacroAbsorption := by
    have hinv : 0 < (ε ^ 2)⁻¹ := inv_pos.mpr
      (sq_pos_of_pos construction.epsilon_pos)
    linarith [construction.inv_epsilon_sq_lt_totalMacroAbsorption]
  have hepsilonFactor :
      1 < ε ^ 2 * (1 + construction.totalMacroAbsorption) := by
    have hmul : 1 < ε ^ 2 * construction.totalMacroAbsorption := by
      rw [← inv_mul_cancel₀ (ne_of_gt (sq_pos_of_pos construction.epsilon_pos))]
      simpa only [mul_comm] using
        mul_lt_mul_of_pos_left
          construction.inv_epsilon_sq_lt_totalMacroAbsorption
          (sq_pos_of_pos construction.epsilon_pos)
    nlinarith [sq_pos_of_pos construction.epsilon_pos]
  by_contra hnot
  have hεle : ε ^ 2 ≤ construction.macroSurvivalProbability := le_of_not_gt hnot
  have := mul_le_mul_of_nonneg_right hεle hfactor.le
  linarith

theorem KiloblockConstruction.macroSurvivalProbability_lt_epsilon
    {table : Table ι} {ε : ℝ}
    (construction : KiloblockConstruction table ε) :
    construction.macroSurvivalProbability < ε := by
  exact construction.macroSurvivalProbability_lt_epsilon_sq.trans_le
    (by nlinarith [construction.epsilon_pos, construction.epsilon_lt_one])

def KiloblockConstruction.macroAdvanceAt
    {table : Table ι} {ε : ℝ}
    (construction : KiloblockConstruction table ε) (j : ℕ) : ℝ :=
  if hj : j < construction.blockCount + 1 then
    construction.macroAdvanceProbability ⟨j, hj⟩
  else 1

def KiloblockConstruction.macroAbsorbAt
    {table : Table ι} {ε : ℝ}
    (construction : KiloblockConstruction table ε) (j : ℕ)
    (owner : NormalPlayer table) : ℝ :=
  if hj : j < construction.blockCount + 1 then
    construction.macroAbsorbProbability ⟨j, hj⟩ owner
  else 0

/-! Survival after crossing blocks `fuel-1,...,0` in the source's reverse
order. -/
def KiloblockConstruction.macroSurvivalFuel
    {table : Table ι} {ε : ℝ}
    (construction : KiloblockConstruction table ε) : ℕ → ℝ
  | 0 => 1
  | fuel + 1 => construction.macroAdvanceAt fuel *
      construction.macroSurvivalFuel fuel

/-! Total probability that `owner` absorbs while crossing the first `fuel`
blocks, with block `fuel-1` crossed first. -/
def KiloblockConstruction.macroOwnerMassFuel
    {table : Table ι} {ε : ℝ}
    (construction : KiloblockConstruction table ε)
    (owner : NormalPlayer table) : ℕ → ℝ
  | 0 => 0
  | fuel + 1 => construction.macroAbsorbAt fuel owner +
      construction.macroAdvanceAt fuel *
        construction.macroOwnerMassFuel owner fuel

def KiloblockConstruction.macroOtherMassFuel
    {table : Table ι} {ε : ℝ}
    (construction : KiloblockConstruction table ε)
    (excluded : NormalPlayer table) : ℕ → ℝ
  | 0 => 0
  | fuel + 1 =>
      (∑ owner ∈ Finset.univ.erase excluded,
        construction.macroAbsorbAt fuel owner) +
      construction.macroAdvanceAt fuel *
        construction.macroOtherMassFuel excluded fuel

theorem KiloblockConstruction.macroAdvanceAt_nonneg
    {table : Table ι} {ε : ℝ}
    (construction : KiloblockConstruction table ε) (j : ℕ) :
    0 ≤ construction.macroAdvanceAt j := by
  unfold KiloblockConstruction.macroAdvanceAt
  split
  · exact construction.macroAdvanceProbability_nonneg _
  · exact zero_le_one

theorem KiloblockConstruction.macroAbsorbAt_nonneg
    {table : Table ι} {ε : ℝ}
    (construction : KiloblockConstruction table ε) (j : ℕ)
    (owner : NormalPlayer table) :
    0 ≤ construction.macroAbsorbAt j owner := by
  unfold KiloblockConstruction.macroAbsorbAt
  split
  · exact construction.macroAbsorbProbability_nonneg _ owner
  · exact le_rfl

theorem KiloblockConstruction.macroSurvivalFuel_nonneg
    {table : Table ι} {ε : ℝ}
    (construction : KiloblockConstruction table ε) :
    ∀ fuel, 0 ≤ construction.macroSurvivalFuel fuel
  | 0 => by simp [KiloblockConstruction.macroSurvivalFuel]
  | fuel + 1 => by
      rw [KiloblockConstruction.macroSurvivalFuel]
      exact mul_nonneg (construction.macroAdvanceAt_nonneg fuel)
        (construction.macroSurvivalFuel_nonneg fuel)

theorem KiloblockConstruction.macroOwnerMassFuel_nonneg
    {table : Table ι} {ε : ℝ}
    (construction : KiloblockConstruction table ε)
    (owner : NormalPlayer table) :
    ∀ fuel, 0 ≤ construction.macroOwnerMassFuel owner fuel
  | 0 => by simp [KiloblockConstruction.macroOwnerMassFuel]
  | fuel + 1 => by
      rw [KiloblockConstruction.macroOwnerMassFuel]
      exact add_nonneg (construction.macroAbsorbAt_nonneg fuel owner)
        (mul_nonneg (construction.macroAdvanceAt_nonneg fuel)
          (construction.macroOwnerMassFuel_nonneg owner fuel))

theorem KiloblockConstruction.macroOtherMassFuel_nonneg
    {table : Table ι} {ε : ℝ}
    (construction : KiloblockConstruction table ε)
    (excluded : NormalPlayer table) :
    ∀ fuel, 0 ≤ construction.macroOtherMassFuel excluded fuel
  | 0 => by simp [KiloblockConstruction.macroOtherMassFuel]
  | fuel + 1 => by
      rw [KiloblockConstruction.macroOtherMassFuel]
      exact add_nonneg
        (Finset.sum_nonneg fun owner _ =>
          construction.macroAbsorbAt_nonneg fuel owner)
        (mul_nonneg (construction.macroAdvanceAt_nonneg fuel)
          (construction.macroOtherMassFuel_nonneg excluded fuel))

theorem KiloblockConstruction.macroAt_total
    {table : Table ι} {ε : ℝ}
    (construction : KiloblockConstruction table ε)
    (j : ℕ) (hj : j < construction.blockCount + 1) :
    construction.macroAdvanceAt j +
      ∑ owner, construction.macroAbsorbAt j owner = 1 := by
  simp only [KiloblockConstruction.macroAdvanceAt,
    KiloblockConstruction.macroAbsorbAt, dif_pos hj]
  exact construction.macroProbability_total ⟨j, hj⟩

theorem KiloblockConstruction.macroMassFuel_total
    {table : Table ι} {ε : ℝ}
    (construction : KiloblockConstruction table ε) :
    ∀ fuel, fuel ≤ construction.blockCount + 1 →
      construction.macroSurvivalFuel fuel +
        ∑ owner, construction.macroOwnerMassFuel owner fuel = 1
  | 0, _ => by simp [KiloblockConstruction.macroSurvivalFuel,
      KiloblockConstruction.macroOwnerMassFuel]
  | fuel + 1, hfuel => by
      have hprevious := construction.macroMassFuel_total fuel (by omega)
      have hlocal := construction.macroAt_total fuel (by omega)
      rw [KiloblockConstruction.macroSurvivalFuel]
      simp_rw [KiloblockConstruction.macroOwnerMassFuel]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      calc
        construction.macroAdvanceAt fuel * construction.macroSurvivalFuel fuel +
              ((∑ owner, construction.macroAbsorbAt fuel owner) +
                construction.macroAdvanceAt fuel *
                  ∑ owner, construction.macroOwnerMassFuel owner fuel) =
            construction.macroAdvanceAt fuel *
                (construction.macroSurvivalFuel fuel +
                  ∑ owner, construction.macroOwnerMassFuel owner fuel) +
              ∑ owner, construction.macroAbsorbAt fuel owner := by ring
        _ = construction.macroAdvanceAt fuel +
            ∑ owner, construction.macroAbsorbAt fuel owner := by
          rw [hprevious, mul_one]
        _ = 1 := hlocal

theorem KiloblockConstruction.macroOwner_add_otherMassFuel
    {table : Table ι} {ε : ℝ}
    (construction : KiloblockConstruction table ε)
    (excluded : NormalPlayer table) :
    ∀ fuel, construction.macroOwnerMassFuel excluded fuel +
        construction.macroOtherMassFuel excluded fuel =
      ∑ owner, construction.macroOwnerMassFuel owner fuel
  | 0 => by simp [KiloblockConstruction.macroOwnerMassFuel,
      KiloblockConstruction.macroOtherMassFuel]
  | fuel + 1 => by
      rw [KiloblockConstruction.macroOwnerMassFuel,
        KiloblockConstruction.macroOtherMassFuel]
      have hdecompose :
          construction.macroAbsorbAt fuel excluded +
              ∑ owner ∈ Finset.univ.erase excluded,
                construction.macroAbsorbAt fuel owner =
            ∑ owner, construction.macroAbsorbAt fuel owner := by
        rw [← Finset.sum_erase_add _ _ (Finset.mem_univ excluded)]
        ring
      simp_rw [KiloblockConstruction.macroOwnerMassFuel]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      rw [← construction.macroOwner_add_otherMassFuel excluded fuel]
      linear_combination hdecompose

theorem KiloblockConstruction.macroSurvivalFuel_full
    {table : Table ι} {ε : ℝ}
    (construction : KiloblockConstruction table ε) :
    construction.macroSurvivalFuel (construction.blockCount + 1) =
      construction.macroSurvivalProbability := by
  have hprefix : ∀ fuel, fuel ≤ construction.blockCount + 1 →
      construction.macroSurvivalFuel fuel =
        ∏ j ∈ Finset.range fuel, construction.macroAdvanceAt j := by
    intro fuel hfuel
    induction fuel with
    | zero => simp [KiloblockConstruction.macroSurvivalFuel]
    | succ fuel ih =>
        rw [KiloblockConstruction.macroSurvivalFuel, Finset.prod_range_succ]
        rw [ih (by omega)]
        ring
  calc
    construction.macroSurvivalFuel (construction.blockCount + 1) =
        ∏ j ∈ Finset.range (construction.blockCount + 1),
          construction.macroAdvanceAt j := hprefix _ le_rfl
    _ = ∏ k : Fin (construction.blockCount + 1),
        construction.macroAdvanceAt k.1 := by
      rw [Fin.prod_univ_eq_prod_range]
    _ = construction.macroSurvivalProbability := by
      unfold KiloblockConstruction.macroSurvivalProbability
      apply Finset.prod_congr rfl
      intro k _
      rw [show construction.macroAdvanceAt k.1 =
          construction.macroAdvanceProbability k by
        simp only [KiloblockConstruction.macroAdvanceAt, dif_pos k.isLt]]

/-! The coordinate error in (A.2'') between the endpoint of block `j` and
the next point in the chain. It is zero outside the actual chain, which lets
the cumulative correction below be indexed by an ordinary natural number. -/
def KiloblockConstruction.trackingIncrement
    {table : Table ι} {ε : ℝ}
    (construction : KiloblockConstruction table ε) (j : ℕ)
    (who : NormalPlayer table) : ℝ :=
  if hj : j < construction.blockCount then
    (construction.buildingBlock ⟨j, by omega⟩).w who -
      construction.point ⟨j + 1, by omega⟩ who
  else 0

def KiloblockConstruction.trackingDistanceIncrement
    {table : Table ι} {ε : ℝ}
    (construction : KiloblockConstruction table ε) (j : ℕ) : ℝ :=
  if hj : j < construction.blockCount then
    dist (construction.point ⟨j + 1, by omega⟩)
      (construction.buildingBlock ⟨j, by omega⟩).w
  else 0

/-! The accumulated (A.2'') correction below point `yᵏ`. Adding this
correction makes the prescribed value telescope exactly when the schedule
advances from kiloblock `k` to `k-1`. -/
def KiloblockConstruction.trackingCorrection
    {table : Table ι} {ε : ℝ}
    (construction : KiloblockConstruction table ε)
    (k : Fin (construction.blockCount + 1))
    (who : NormalPlayer table) : ℝ :=
  ∑ j ∈ Finset.range k.1, construction.trackingIncrement j who

@[simp]
theorem KiloblockConstruction.trackingCorrection_zero
    {table : Table ι} {ε : ℝ}
    (construction : KiloblockConstruction table ε)
    (who : NormalPlayer table) :
    construction.trackingCorrection ⟨0, by omega⟩ who = 0 := by
  simp [KiloblockConstruction.trackingCorrection]

theorem KiloblockConstruction.trackingCorrection_succ
    {table : Table ι} {ε : ℝ}
    (construction : KiloblockConstruction table ε)
    (j : ℕ) (hj : j < construction.blockCount)
    (who : NormalPlayer table) :
    construction.trackingCorrection ⟨j + 1, by omega⟩ who =
      construction.trackingCorrection ⟨j, by omega⟩ who +
        (construction.buildingBlock ⟨j, by omega⟩).w who -
          construction.point ⟨j + 1, by omega⟩ who := by
  simp [KiloblockConstruction.trackingCorrection,
    Finset.sum_range_succ, KiloblockConstruction.trackingIncrement, hj]
  ring

/-! Exact telescope at an advance from index `j+1` to index `j`. -/
theorem KiloblockConstruction.point_add_trackingCorrection_succ
    {table : Table ι} {ε : ℝ}
    (construction : KiloblockConstruction table ε)
    (j : ℕ) (hj : j < construction.blockCount)
    (who : NormalPlayer table) :
    construction.point ⟨j + 1, by omega⟩ who +
        construction.trackingCorrection ⟨j + 1, by omega⟩ who =
      (construction.buildingBlock ⟨j, by omega⟩).w who +
        construction.trackingCorrection ⟨j, by omega⟩ who := by
  rw [construction.trackingCorrection_succ j hj who]
  ring

theorem KiloblockConstruction.abs_trackingCorrection_lt
    {table : Table ι} {ε : ℝ}
    (construction : KiloblockConstruction table ε)
    (k : Fin (construction.blockCount + 1))
    (who : NormalPlayer table) :
    |construction.trackingCorrection k who| < ε := by
  calc
    |construction.trackingCorrection k who| ≤
        ∑ j ∈ Finset.range k.1,
          |construction.trackingIncrement j who| := by
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range k.1,
        construction.trackingDistanceIncrement j := by
      apply Finset.sum_le_sum
      intro j hj
      have hjk : j < k.1 := Finset.mem_range.mp hj
      have hjcount : j < construction.blockCount := by omega
      simp only [KiloblockConstruction.trackingIncrement,
        KiloblockConstruction.trackingDistanceIncrement, hjcount,
        dif_pos]
      rw [dist_eq_norm]
      simpa only [Pi.sub_apply, Real.norm_eq_abs, abs_sub_comm] using
        norm_le_pi_norm
          (construction.point ⟨j + 1, by omega⟩ -
            (construction.buildingBlock ⟨j, by omega⟩).w) who
    _ ≤ ∑ j ∈ Finset.range construction.blockCount,
        construction.trackingDistanceIncrement j := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro j hj
        simp only [Finset.mem_range] at hj ⊢
        omega
      · intro j hj _
        simp only [KiloblockConstruction.trackingDistanceIncrement]
        split <;> positivity
    _ = KiloblockTracking construction.point construction.buildingBlock := by
      rw [← Fin.sum_univ_eq_sum_range]
      apply Finset.sum_congr rfl
      intro j _
      simp [KiloblockConstruction.trackingDistanceIncrement]
    _ < ε := construction.tracking_small

/-! Value of the currently selected type with `remaining` active decisions
left. Type zero has no Quit hazard and keeps the point value until it
advances; type `i` uses the exact mesh continuation value above. -/
def KiloblockConstruction.selectedValue
    {table : Table ι} {ε : ℝ}
    (construction : KiloblockConstruction table ε)
    (k : Fin (construction.blockCount + 1))
    (choice : Option (NormalPlayer table)) (remaining : ℕ)
    (who : NormalPlayer table) : ℝ :=
  match choice with
  | none => construction.point k who
  | some owner =>
      (construction.attempt k owner).remainingValue
        (construction.mesh k) remaining who

theorem KiloblockConstruction.selectedValue_mesh
    {table : Table ι} {ε : ℝ}
    (construction : KiloblockConstruction table ε)
    (k : Fin (construction.blockCount + 1))
    (choice : Option (NormalPlayer table))
    (who : NormalPlayer table) :
    construction.selectedValue k choice (construction.mesh k) who =
      (construction.buildingBlock k).choiceValue choice who := by
  cases choice with
  | none => rfl
  | some owner =>
      exact (construction.attempt k owner).remainingValue_mesh
        (construction.mesh k) (construction.mesh_survival k owner) who

theorem KiloblockConstruction.selectedValue_some_succ
    {table : Table ι} {ε : ℝ}
    (construction : KiloblockConstruction table ε)
    (k : Fin (construction.blockCount + 1))
    (owner : NormalPlayer table) (remaining : ℕ)
    (who : NormalPlayer table) :
    construction.selectedValue k (some owner) (remaining + 1) who =
      quittingMeshHazard (construction.attempt k owner).quitWeight
          (construction.mesh k) * NormalMatrix table who owner +
        (1 - quittingMeshHazard (construction.attempt k owner).quitWeight
          (construction.mesh k)) *
          construction.selectedValue k (some owner) remaining who := by
  exact (construction.attempt k owner).remainingValue_succ
    (construction.mesh k) remaining who

/-! The actual public signal realizes the type lottery `z`, so a fresh draw
has exactly value `w(yᵏ)`. -/
theorem KiloblockConstruction.expect_selectedValue_mesh
    {table : Table ι} {ε : ℝ}
    (construction : KiloblockConstruction table ε)
    (k : Fin (construction.blockCount + 1))
    (who : NormalPlayer table) :
    expect construction.profile.signalLaw (fun signal =>
      construction.selectedValue k (construction.signalSelector k signal)
        (construction.mesh k) who) =
      (construction.buildingBlock k).w who := by
  simp_rw [construction.selectedValue_mesh k]
  calc
    expect construction.profile.signalLaw (fun signal =>
        (construction.buildingBlock k).choiceValue
          (construction.signalSelector k signal) who) =
        expect (construction.profile.signalLaw.map
          (construction.signalSelector k))
          (fun choice => (construction.buildingBlock k).choiceValue
            choice who) := by
      symm
      exact Math.Probability.expect_map _ _ _
    _ = _ := by
      rw [construction.signalSelector_law k]
      exact (construction.buildingBlock k).expect_choiceValue who

/-! `w(yᴷ)`, in the normal coordinates where the paper defines it. -/
def KiloblockConstruction.normalTarget
    {table : Table ι} {ε : ℝ}
    (construction : KiloblockConstruction table ε) :
    NormalPlayer table → ℝ :=
  (construction.buildingBlock (Fin.last construction.blockCount)).w

def KiloblockConstruction.macroTrackingAt
    {table : Table ι} {ε : ℝ}
    (construction : KiloblockConstruction table ε) (j : ℕ)
    (who : NormalPlayer table) : ℝ :=
  if hj : j < construction.blockCount + 1 then
    construction.trackingCorrection ⟨j, hj⟩ who
  else 0

/-! Expected corrected normal payoff after crossing blocks
`fuel-1,...,0`, with the final endpoint `y⁰` if all blocks advance. -/
def KiloblockConstruction.macroCorrectedValueFuel
    {table : Table ι} {ε : ℝ}
    (construction : KiloblockConstruction table ε)
    (who : NormalPlayer table) : ℕ → ℝ
  | 0 => construction.point ⟨0, by omega⟩ who
  | fuel + 1 =>
      construction.macroAdvanceAt fuel *
          construction.macroCorrectedValueFuel who fuel +
        ∑ owner, construction.macroAbsorbAt fuel owner *
          (NormalMatrix table who owner +
            construction.macroTrackingAt fuel who)

private theorem KiloblockConstruction.macroCorrectedValueFuel_step
    {table : Table ι} {ε : ℝ}
    (construction : KiloblockConstruction table ε)
    (who : NormalPlayer table) (j : ℕ)
    (hj : j < construction.blockCount + 1)
    (hprevious : construction.macroCorrectedValueFuel who j =
      construction.point ⟨j, hj⟩ who +
        construction.trackingCorrection ⟨j, hj⟩ who) :
    construction.macroCorrectedValueFuel who (j + 1) =
      (construction.buildingBlock ⟨j, hj⟩).w who +
        construction.trackingCorrection ⟨j, hj⟩ who := by
  rw [KiloblockConstruction.macroCorrectedValueFuel, hprevious]
  have hadvance : construction.macroAdvanceAt j =
      construction.macroAdvanceProbability ⟨j, hj⟩ := by
    simp only [KiloblockConstruction.macroAdvanceAt, dif_pos hj]
  have habsorb : ∀ owner, construction.macroAbsorbAt j owner =
      construction.macroAbsorbProbability ⟨j, hj⟩ owner := by
    intro owner
    simp only [KiloblockConstruction.macroAbsorbAt, dif_pos hj]
  have htracking : construction.macroTrackingAt j who =
      construction.trackingCorrection ⟨j, hj⟩ who := by
    simp only [KiloblockConstruction.macroTrackingAt, dif_pos hj]
  rw [hadvance]
  simp_rw [habsorb, htracking, mul_add]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul]
  have hbalance := construction.macro_balance ⟨j, hj⟩ who
  have htotal := construction.macroProbability_total ⟨j, hj⟩
  linear_combination -hbalance +
    htotal * construction.trackingCorrection ⟨j, hj⟩ who

theorem KiloblockConstruction.macroCorrectedValueFuel_eq
    {table : Table ι} {ε : ℝ}
    (construction : KiloblockConstruction table ε)
    (who : NormalPlayer table) (j : ℕ)
    (hj : j < construction.blockCount + 1) :
    construction.macroCorrectedValueFuel who (j + 1) =
      (construction.buildingBlock ⟨j, hj⟩).w who +
        construction.trackingCorrection ⟨j, hj⟩ who := by
  induction j with
  | zero =>
      apply construction.macroCorrectedValueFuel_step who 0 hj
      rw [KiloblockConstruction.macroCorrectedValueFuel,
        construction.trackingCorrection_zero]
      simp
  | succ j ih =>
      apply construction.macroCorrectedValueFuel_step who (j + 1) hj
      have hjcount : j < construction.blockCount := by omega
      have hvalue := ih (by omega)
      have htelescope := construction.point_add_trackingCorrection_succ
        j hjcount who
      exact hvalue.trans htelescope.symm

theorem KiloblockConstruction.macroCorrectedValueFuel_full
    {table : Table ι} {ε : ℝ}
    (construction : KiloblockConstruction table ε)
    (who : NormalPlayer table) :
    construction.macroCorrectedValueFuel who
        (construction.blockCount + 1) =
      construction.normalTarget who +
        construction.trackingCorrection
          (Fin.last construction.blockCount) who := by
  unfold KiloblockConstruction.normalTarget
  let last : Fin (construction.blockCount + 1) :=
    ⟨construction.blockCount, by omega⟩
  have hlast : Fin.last construction.blockCount = last := by
    apply Fin.ext
    rfl
  rw [hlast]
  exact construction.macroCorrectedValueFuel_eq who construction.blockCount
    (by omega)

theorem KiloblockConstruction.macroTrackingAt_abs_lt
    {table : Table ι} {ε : ℝ}
    (construction : KiloblockConstruction table ε)
    (j : ℕ) (hj : j < construction.blockCount + 1)
    (who : NormalPlayer table) :
    |construction.macroTrackingAt j who| < ε := by
  rw [show construction.macroTrackingAt j who =
      construction.trackingCorrection ⟨j, hj⟩ who by
    simp only [KiloblockConstruction.macroTrackingAt, dif_pos hj]]
  exact construction.abs_trackingCorrection_lt ⟨j, hj⟩ who

private theorem KiloblockConstruction.macro_terminal_sum_le
    {table : Table ι} {ε : ℝ}
    (construction : KiloblockConstruction table ε)
    (excluded negative : NormalPlayer table)
    (hnegative : NormalMatrix table negative excluded <
      -construction.negativeMargin)
    (j : ℕ) (hj : j < construction.blockCount + 1) :
    (∑ owner, construction.macroAbsorbAt j owner *
        (NormalMatrix table negative owner +
          construction.macroTrackingAt j negative)) ≤
      construction.macroAbsorbAt j excluded *
          (-construction.negativeMargin + ε) +
        (∑ owner ∈ Finset.univ.erase excluded,
          construction.macroAbsorbAt j owner) * (1 + ε) := by
  have htracking := construction.macroTrackingAt_abs_lt j hj negative
  calc
    (∑ owner, construction.macroAbsorbAt j owner *
        (NormalMatrix table negative owner +
          construction.macroTrackingAt j negative)) =
        construction.macroAbsorbAt j excluded *
            (NormalMatrix table negative excluded +
              construction.macroTrackingAt j negative) +
          ∑ owner ∈ Finset.univ.erase excluded,
            construction.macroAbsorbAt j owner *
              (NormalMatrix table negative owner +
                construction.macroTrackingAt j negative) := by
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ excluded)]
      ring
    _ ≤ construction.macroAbsorbAt j excluded *
          (-construction.negativeMargin + ε) +
        ∑ owner ∈ Finset.univ.erase excluded,
          construction.macroAbsorbAt j owner * (1 + ε) := by
      apply add_le_add
      · apply mul_le_mul_of_nonneg_left _
          (construction.macroAbsorbAt_nonneg j excluded)
        linarith [(abs_lt.mp htracking).2]
      · apply Finset.sum_le_sum
        intro owner _
        apply mul_le_mul_of_nonneg_left _
          (construction.macroAbsorbAt_nonneg j owner)
        have hmatrix := (abs_le.mp
          (construction.normalMatrix_bounded negative owner)).2
        linarith [(abs_lt.mp htracking).2]
    _ = construction.macroAbsorbAt j excluded *
          (-construction.negativeMargin + ε) +
        (∑ owner ∈ Finset.univ.erase excluded,
          construction.macroAbsorbAt j owner) * (1 + ε) := by
      congr 1
      rw [Finset.sum_mul]

private theorem KiloblockConstruction.macroCorrectedValueFuel_upper
    {table : Table ι} {ε : ℝ}
    (construction : KiloblockConstruction table ε)
    (excluded negative : NormalPlayer table)
    (hnegative : NormalMatrix table negative excluded <
      -construction.negativeMargin) :
    ∀ fuel, fuel ≤ construction.blockCount + 1 →
      construction.macroCorrectedValueFuel negative fuel ≤
        (-construction.negativeMargin + ε) *
            construction.macroOwnerMassFuel excluded fuel +
          (1 + ε) * construction.macroOtherMassFuel excluded fuel +
          construction.macroSurvivalFuel fuel
  | 0, _ => by
      simp only [KiloblockConstruction.macroCorrectedValueFuel,
        KiloblockConstruction.macroOwnerMassFuel,
        KiloblockConstruction.macroOtherMassFuel,
        KiloblockConstruction.macroSurvivalFuel, mul_zero, add_zero]
      simpa only [zero_add] using
        (abs_le.mp (abs_le_one_of_mem_D construction.normalMatrix_bounded
          (construction.point_boundary ⟨0, by omega⟩).1 negative)).2
  | fuel + 1, hfuel => by
      have hfuelLt : fuel < construction.blockCount + 1 := by omega
      have hprevious := construction.macroCorrectedValueFuel_upper
        excluded negative hnegative fuel (by omega)
      have hterminal := construction.macro_terminal_sum_le
        excluded negative hnegative fuel hfuelLt
      rw [KiloblockConstruction.macroCorrectedValueFuel]
      calc
        construction.macroAdvanceAt fuel *
              construction.macroCorrectedValueFuel negative fuel +
            ∑ owner, construction.macroAbsorbAt fuel owner *
              (NormalMatrix table negative owner +
                construction.macroTrackingAt fuel negative) ≤
            construction.macroAdvanceAt fuel *
                ((-construction.negativeMargin + ε) *
                    construction.macroOwnerMassFuel excluded fuel +
                  (1 + ε) *
                    construction.macroOtherMassFuel excluded fuel +
                  construction.macroSurvivalFuel fuel) +
              (construction.macroAbsorbAt fuel excluded *
                  (-construction.negativeMargin + ε) +
                (∑ owner ∈ Finset.univ.erase excluded,
                  construction.macroAbsorbAt fuel owner) * (1 + ε)) := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left hprevious
              (construction.macroAdvanceAt_nonneg fuel))
            hterminal
        _ = (-construction.negativeMargin + ε) *
                construction.macroOwnerMassFuel excluded (fuel + 1) +
              (1 + ε) *
                construction.macroOtherMassFuel excluded (fuel + 1) +
              construction.macroSurvivalFuel (fuel + 1) := by
          rw [KiloblockConstruction.macroOwnerMassFuel,
            KiloblockConstruction.macroOtherMassFuel,
            KiloblockConstruction.macroSurvivalFuel]
          ring

theorem KiloblockConstruction.negativeMargin_lt_one
    {table : Table ι} {ε : ℝ}
    (construction : KiloblockConstruction table ε) :
    construction.negativeMargin < 1 := by
  let k : Fin (construction.blockCount + 1) := ⟨0, by omega⟩
  obtain ⟨owner, _, _⟩ :=
    (Finset.sum_pos_iff_of_nonneg (fun owner _ =>
      (construction.buildingBlock k).z.singleton_nonneg owner)).mp
      (construction.buildingBlock k).nontrivial
  obtain ⟨negative, hnegative⟩ := construction.column_negative owner
  have hlower := (abs_le.mp
    (construction.normalMatrix_bounded negative owner)).1
  linarith

theorem KiloblockConstruction.epsilon_lt_macroOther_add_survival
    {table : Table ι} {ε : ℝ}
    (construction : KiloblockConstruction table ε)
    (excluded : NormalPlayer table) :
    ε < construction.macroOtherMassFuel excluded
          (construction.blockCount + 1) +
        construction.macroSurvivalFuel (construction.blockCount + 1) := by
  obtain ⟨negative, hnegative⟩ := construction.column_negative excluded
  let fuel := construction.blockCount + 1
  have hupper := construction.macroCorrectedValueFuel_upper
    excluded negative hnegative fuel le_rfl
  have hvalue := construction.macroCorrectedValueFuel_full negative
  rw [hvalue] at hupper
  have htarget : 0 ≤ construction.normalTarget negative :=
    (construction.buildingBlock (Fin.last construction.blockCount)).w_boundary.1.2
      negative
  have hcorrection := construction.abs_trackingCorrection_lt
    (Fin.last construction.blockCount) negative
  have hlower : -ε < construction.normalTarget negative +
      construction.trackingCorrection (Fin.last construction.blockCount) negative := by
    linarith [(abs_lt.mp hcorrection).1]
  have howner := construction.macroOwnerMassFuel_nonneg excluded fuel
  have hother := construction.macroOtherMassFuel_nonneg excluded fuel
  have hsurvival := construction.macroSurvivalFuel_nonneg fuel
  have htotal := construction.macroMassFuel_total fuel le_rfl
  rw [← construction.macroOwner_add_otherMassFuel excluded fuel] at htotal
  have hmarginOne := construction.negativeMargin_lt_one
  have hcoefficient : (5 : ℝ) ≤
      ((2 * Fintype.card (NormalPlayer table) + 1 : ℕ) : ℝ) := by
    have hcard := construction.two_le_normalPlayer_card
    exact_mod_cast (show 5 ≤ 2 * Fintype.card (NormalPlayer table) + 1 by omega)
  have hmarginFive : 5 * ε < construction.negativeMargin := by
    have hmul := mul_le_mul_of_nonneg_right hcoefficient
      construction.epsilon_pos.le
    exact lt_of_le_of_lt hmul construction.accuracy_below_margin
  have hownerCoefficient :
      (construction.negativeMargin + 1) *
          construction.macroOtherMassFuel excluded fuel ≤
        2 * construction.macroOtherMassFuel excluded fuel := by
    exact mul_le_mul_of_nonneg_right (by linarith) hother
  have hsurvivalCoefficient :
      (construction.negativeMargin - ε + 1) *
          construction.macroSurvivalFuel fuel ≤
        2 * construction.macroSurvivalFuel fuel := by
    exact mul_le_mul_of_nonneg_right (by linarith [construction.epsilon_pos])
      hsurvival
  nlinarith

/-! The operational schedule itself implies the unilateral-quitting clause:
at an active history either one selected owner uses the mesh coin or everyone
continues. -/
theorem KiloblockConstruction.atMostOneQuitter
    {table : Table ι} {ε : ℝ}
    (construction : KiloblockConstruction table ε) :
    AtMostOneQuitter construction.profile := by
  classical
  intro t history
  cases hstate : history.2 with
  | draw => trivial
  | absorbed quitters => trivial
  | active signal =>
      have hmatches := construction.mode_state t history
      rw [hstate] at hmatches
      cases hmode : construction.mode t history with
      | draw phase => simp [KiloblockMode.MatchesState, hmode] at hmatches
      | absorbed origin =>
          simp [KiloblockMode.MatchesState, hmode] at hmatches
      | finalActive =>
          simp [construction.strategy_eq, hmode]
      | active k choice remaining =>
          cases choice with
          | none =>
              simp [construction.strategy_eq, hmode]
          | some owner =>
              calc
                (Finset.filter (fun who =>
                    0 < ((construction.profile.strategy who t history)
                      true).toReal) Finset.univ).card ≤
                    ({owner.1} : Finset ι).card := by
                  apply Finset.card_le_card
                  intro who hwho
                  simp only [Finset.mem_filter, Finset.mem_univ,
                    true_and] at hwho
                  simp only [Finset.mem_singleton]
                  by_contra hne
                  have : ¬0 < ((construction.profile.strategy who t history)
                      true).toReal := by
                    simp [construction.strategy_eq, hmode, hne]
                  exact this hwho
                _ = 1 := Finset.card_singleton owner.1

/-! At a selected type-`i` history, the joint action law is exactly one
Bernoulli coin at coordinate `i`; every other coordinate is Continue. -/
theorem KiloblockConstruction.stageActionDist_active_some
    {table : Table ι} {ε : ℝ}
    (construction : KiloblockConstruction table ε)
    {t : ℕ}
    (history : (publicQuittingGame table
      construction.profile.signalLaw).Hist t)
    (k : Fin (construction.blockCount + 1))
    (owner : NormalPlayer table) (remaining : ℕ)
    (hmode : construction.mode t history =
      .active k (some owner) remaining) :
    (publicQuittingGame table construction.profile.signalLaw).stageActionDist
        construction.profile.strategy history =
      (quittingMeshHazardCoin (construction.attempt k owner).quitWeight
          (construction.mesh k)
          (construction.attempt k owner).quitWeight_pos.le
          (construction.attempt k owner).quitWeight_lt_one).bind
        (fun quits => PMF.pure
          (Function.update (fun _ : ι => false) owner.1 quits)) := by
  classical
  let coin := quittingMeshHazardCoin
    (construction.attempt k owner).quitWeight (construction.mesh k)
    (construction.attempt k owner).quitWeight_pos.le
    (construction.attempt k owner).quitWeight_lt_one
  let base : ∀ who,
      PMF ((publicQuittingGame table
        construction.profile.signalLaw).Act who) :=
    fun _ => PMF.pure false
  have hfamily :
      (fun who => construction.profile.strategy who t history) =
        Function.update base owner.1 coin := by
    funext who
    by_cases hwho : who = owner.1
    · subst who
      simp [construction.strategy_eq, hmode, coin, base]
    · rw [construction.strategy_eq]
      simp [hmode, hwho, base]
  unfold StochasticGame.stageActionDist
  rw [hfamily]
  calc
    Math.PMFProduct.pmfPi (Function.update base owner.1 coin) =
        coin.bind (fun quits => Math.PMFProduct.pmfPi
          (Function.update base owner.1 (PMF.pure quits))) :=
      Math.PMFProduct.pmfPi_update_bind base owner.1 coin
    _ = coin.bind (fun quits => PMF.pure
        (Function.update (fun _ : ι => false) owner.1 quits)) := by
      apply congrArg (PMF.bind coin)
      funext quits
      rw [show Function.update base owner.1 (PMF.pure quits) =
          fun who => PMF.pure
            (Function.update (fun _ : ι => false) owner.1 quits who) by
        funext who
        by_cases hwho : who = owner.1
        · subst who
          rw [Function.update_self, Function.update_self]
          rfl
        · rw [Function.update_of_ne hwho,
            Function.update_of_ne hwho]
          rfl]
      exact Math.PMFProduct.pmfPi_pure _

def singleQuitAction (owner : ι) (quits : Bool) : ι → Bool :=
  Function.update (fun _ => false) owner quits

omit [Fintype ι] in
@[simp]
theorem singleQuitAction_false (owner who : ι) :
    singleQuitAction owner false who = false := by
  by_cases hwho : who = owner
  · subst who
    simp [singleQuitAction]
  · rw [singleQuitAction, Function.update_of_ne hwho]

theorem singleQuitAction_true_quitters (owner : ι) :
    ({who | singleQuitAction owner true who = true} : Finset ι) =
      {owner} := by
  ext who
  by_cases hwho : who = owner
  · subst who
    simp [singleQuitAction]
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    rw [singleQuitAction, Function.update_of_ne hwho]
    simp [hwho]

theorem publicQuittingGame_transition_singleQuitAction
    {Signal : Type} [Fintype Signal]
    (table : Table ι) (signalLaw : PMF Signal) (signal : Signal)
    (owner : ι) :
    (publicQuittingGame table signalLaw).transition (.active signal)
        (singleQuitAction owner true) =
      PMF.pure (.absorbed (quittingProjectiveSingletonTerminal owner)) := by
  simp only [publicQuittingGame, singleQuitAction_true_quitters]
  split
  · congr
  · rename_i h
    exact False.elim (h (by simp))

theorem publicQuittingGame_transition_singleQuitAction_false
    {Signal : Type} [Fintype Signal]
    (table : Table ι) (signalLaw : PMF Signal) (signal : Signal)
    (owner : ι) :
    (publicQuittingGame table signalLaw).transition (.active signal)
        (singleQuitAction owner false) = PMF.pure .draw := by
  simp [publicQuittingGame, singleQuitAction_false]

def KiloblockConstruction.trackingCorrectionAtOrigin
    {table : Table ι} {ε : ℝ}
    (construction : KiloblockConstruction table ε)
    (origin : Option (Fin (construction.blockCount + 1)))
    (who : NormalPlayer table) : ℝ :=
  origin.elim 0 (fun k => construction.trackingCorrection k who)

/-! The history potential used in Lemma 3.8. It is the exact remaining block
value plus the signed (A.2'') telescope. After pre-final absorption it is the
real terminal payoff plus the same correction. The final all-Continue tail is
assigned zero, as in the accepted manuscript's proof. -/
def KiloblockConstruction.normalPotential
    {table : Table ι} {ε : ℝ}
    (construction : KiloblockConstruction table ε)
    (who : NormalPlayer table) :
    (publicQuittingGame table
      construction.profile.signalLaw).HistoryPotential :=
  fun t history =>
    match construction.mode t history with
    | .draw (.choose k) =>
        (construction.buildingBlock k).w who +
          construction.trackingCorrection k who
    | .draw (.resume k choice remaining) =>
        construction.selectedValue k choice remaining who +
          construction.trackingCorrection k who
    | .draw .final => 0
    | .active k choice remaining =>
        construction.selectedValue k choice remaining who +
          construction.trackingCorrection k who
    | .finalActive => 0
    | .absorbed origin =>
        (match history.2 with
        | .absorbed quitters => table.terminal quitters who.1
        | _ => 0) + construction.trackingCorrectionAtOrigin origin who

theorem KiloblockConstruction.normalPotential_initial
    {table : Table ι} {ε : ℝ}
    (construction : KiloblockConstruction table ε)
    (who : NormalPlayer table) :
    construction.normalPotential who 0
        ((publicQuittingGame table construction.profile.signalLaw).emptyHist
          PublicQuittingState.draw) =
      construction.normalTarget who +
        construction.trackingCorrection
          (Fin.last construction.blockCount) who := by
  simp [KiloblockConstruction.normalPotential,
    construction.mode_initial, KiloblockConstruction.normalTarget]

theorem KiloblockConstruction.normalPotential_draw_choose
    {table : Table ι} {ε : ℝ}
    (construction : KiloblockConstruction table ε)
    (who : NormalPlayer table) {t : ℕ}
    (history : (publicQuittingGame table
      construction.profile.signalLaw).Hist t)
    (k : Fin (construction.blockCount + 1))
    (hmode : construction.mode t history = .draw (.choose k)) :
    (publicQuittingGame table
      construction.profile.signalLaw).historyContinuationEU
        construction.profile.strategy (construction.normalPotential who)
        history =
      construction.normalPotential who t history := by
  classical
  have hstate : history.2 = PublicQuittingState.draw := by
    have hmatches := construction.mode_state t history
    cases hs : history.2 <;>
      simp [KiloblockMode.MatchesState, hmode, hs] at hmatches ⊢
  have hnext (action : (publicQuittingGame table
      construction.profile.signalLaw).JointAct)
      (signal : Fin (construction.profile.signalCount + 1))
      (hsignal : signal ∈ construction.profile.signalLaw.support) :
      construction.mode (t + 1)
          (Fin.snoc history.1 (history.2, action),
            PublicQuittingState.active signal) =
        .active k (construction.signalSelector k signal)
          (construction.mesh k) := by
    have hsupp : PublicQuittingState.active signal ∈
        ((publicQuittingGame table construction.profile.signalLaw).transition
          history.2 action).support := by
      rw [hstate]
      simp only [publicQuittingGame]
      exact (PMF.mem_support_map_iff _ _ _).mpr
        ⟨signal, hsignal, rfl⟩
    have hstep := construction.mode_step t history action
      (PublicQuittingState.active signal) hsupp
    simpa [KiloblockModeStep, hmode] using hstep
  rw [KiloblockConstruction.normalPotential, hmode]
  unfold StochasticGame.historyContinuationEU
  calc
    expect
        ((publicQuittingGame table
          construction.profile.signalLaw).stageActionDist
            construction.profile.strategy history)
        (fun action =>
          expect ((publicQuittingGame table
            construction.profile.signalLaw).transition history.2 action)
            (fun nextState => construction.normalPotential who (t + 1)
              (Fin.snoc history.1 (history.2, action), nextState))) =
        expect
          ((publicQuittingGame table
            construction.profile.signalLaw).stageActionDist
              construction.profile.strategy history)
          (fun _ => (construction.buildingBlock k).w who +
            construction.trackingCorrection k who) := by
      apply congrArg (expect ((publicQuittingGame table
        construction.profile.signalLaw).stageActionDist
          construction.profile.strategy history))
      funext action
      rw [hstate]
      simp only [publicQuittingGame]
      rw [Math.Probability.expect_map]
      calc
        expect construction.profile.signalLaw (fun signal =>
            construction.normalPotential who (t + 1)
              (Fin.snoc history.1 (PublicQuittingState.draw, action),
                PublicQuittingState.active signal)) =
            expect construction.profile.signalLaw (fun signal =>
              construction.selectedValue k
                  (construction.signalSelector k signal)
                  (construction.mesh k) who +
                construction.trackingCorrection k who) := by
          apply Math.ProbabilityMassFunction.expect_congr_on_support
          intro signal hsignal
          have hm := hnext action signal hsignal
          rw [hstate] at hm
          rw [KiloblockConstruction.normalPotential, hm]
        _ = (construction.buildingBlock k).w who +
            construction.trackingCorrection k who := by
          rw [Math.Probability.expect_add,
            construction.expect_selectedValue_mesh k who,
            Math.Probability.expect_const]
    _ = _ := expect_const _ _

private theorem KiloblockConstruction.normalPotential_draw_constant
    {table : Table ι} {ε : ℝ}
    (construction : KiloblockConstruction table ε)
    (who : NormalPlayer table) {t : ℕ}
    (history : (publicQuittingGame table
      construction.profile.signalLaw).Hist t)
    (value : ℝ)
    (hstate : history.2 = PublicQuittingState.draw)
    (hnext : ∀ action signal,
      signal ∈ construction.profile.signalLaw.support →
      construction.normalPotential who (t + 1)
        (Fin.snoc history.1 (history.2, action),
          PublicQuittingState.active signal) = value) :
    (publicQuittingGame table
      construction.profile.signalLaw).historyContinuationEU
        construction.profile.strategy (construction.normalPotential who)
        history = value := by
  classical
  unfold StochasticGame.historyContinuationEU
  calc
    expect
        ((publicQuittingGame table
          construction.profile.signalLaw).stageActionDist
            construction.profile.strategy history)
        (fun action =>
          expect ((publicQuittingGame table
            construction.profile.signalLaw).transition history.2 action)
            (fun nextState => construction.normalPotential who (t + 1)
              (Fin.snoc history.1 (history.2, action), nextState))) =
        expect
          ((publicQuittingGame table
            construction.profile.signalLaw).stageActionDist
              construction.profile.strategy history)
          (fun _ => value) := by
      apply congrArg (expect ((publicQuittingGame table
        construction.profile.signalLaw).stageActionDist
          construction.profile.strategy history))
      funext action
      rw [hstate]
      simp only [publicQuittingGame]
      rw [Math.Probability.expect_map]
      rw [← Math.Probability.expect_const
        construction.profile.signalLaw value]
      apply Math.ProbabilityMassFunction.expect_congr_on_support
      intro signal hsignal
      have := hnext action signal hsignal
      rw [hstate] at this
      exact this
    _ = value := expect_const _ _

theorem KiloblockConstruction.normalPotential_draw_resume
    {table : Table ι} {ε : ℝ}
    (construction : KiloblockConstruction table ε)
    (who : NormalPlayer table) {t : ℕ}
    (history : (publicQuittingGame table
      construction.profile.signalLaw).Hist t)
    (k : Fin (construction.blockCount + 1))
    (choice : Option (NormalPlayer table)) (remaining : ℕ)
    (hmode : construction.mode t history =
      .draw (.resume k choice remaining)) :
    (publicQuittingGame table
      construction.profile.signalLaw).historyContinuationEU
        construction.profile.strategy (construction.normalPotential who)
        history =
      construction.normalPotential who t history := by
  classical
  have hstate : history.2 = PublicQuittingState.draw := by
    have hmatches := construction.mode_state t history
    cases hs : history.2 <;>
      simp [KiloblockMode.MatchesState, hmode, hs] at hmatches ⊢
  rw [KiloblockConstruction.normalPotential, hmode]
  apply construction.normalPotential_draw_constant who history
    (construction.selectedValue k choice remaining who +
      construction.trackingCorrection k who) hstate
  intro action signal hsignal
  have hsupp : PublicQuittingState.active signal ∈
      ((publicQuittingGame table construction.profile.signalLaw).transition
        history.2 action).support := by
    rw [hstate]
    simp only [publicQuittingGame]
    exact (PMF.mem_support_map_iff _ _ _).mpr
      ⟨signal, hsignal, rfl⟩
  have hstep := construction.mode_step t history action
    (PublicQuittingState.active signal) hsupp
  have hm : construction.mode (t + 1)
      (Fin.snoc history.1 (history.2, action),
        PublicQuittingState.active signal) =
      .active k choice remaining := by
    simpa [KiloblockModeStep, hmode] using hstep
  rw [KiloblockConstruction.normalPotential, hm]

theorem KiloblockConstruction.normalPotential_draw_final
    {table : Table ι} {ε : ℝ}
    (construction : KiloblockConstruction table ε)
    (who : NormalPlayer table) {t : ℕ}
    (history : (publicQuittingGame table
      construction.profile.signalLaw).Hist t)
    (hmode : construction.mode t history = .draw .final) :
    (publicQuittingGame table
      construction.profile.signalLaw).historyContinuationEU
        construction.profile.strategy (construction.normalPotential who)
        history =
      construction.normalPotential who t history := by
  classical
  have hstate : history.2 = PublicQuittingState.draw := by
    have hmatches := construction.mode_state t history
    cases hs : history.2 <;>
      simp [KiloblockMode.MatchesState, hmode, hs] at hmatches ⊢
  rw [KiloblockConstruction.normalPotential, hmode]
  apply construction.normalPotential_draw_constant who history 0 hstate
  intro action signal hsignal
  have hsupp : PublicQuittingState.active signal ∈
      ((publicQuittingGame table construction.profile.signalLaw).transition
        history.2 action).support := by
    rw [hstate]
    simp only [publicQuittingGame]
    exact (PMF.mem_support_map_iff _ _ _).mpr
      ⟨signal, hsignal, rfl⟩
  have hstep := construction.mode_step t history action
    (PublicQuittingState.active signal) hsupp
  have hm : construction.mode (t + 1)
      (Fin.snoc history.1 (history.2, action),
        PublicQuittingState.active signal) = .finalActive := by
    simpa [KiloblockModeStep, hmode] using hstep
  rw [KiloblockConstruction.normalPotential, hm]

theorem KiloblockConstruction.normalPotential_absorbed
    {table : Table ι} {ε : ℝ}
    (construction : KiloblockConstruction table ε)
    (who : NormalPlayer table) {t : ℕ}
    (history : (publicQuittingGame table
      construction.profile.signalLaw).Hist t)
    (origin : Option (Fin (construction.blockCount + 1)))
    (hmode : construction.mode t history = .absorbed origin) :
    (publicQuittingGame table
      construction.profile.signalLaw).historyContinuationEU
        construction.profile.strategy (construction.normalPotential who)
        history =
      construction.normalPotential who t history := by
  classical
  rcases history with ⟨past, state⟩
  have hmatches := construction.mode_state t (past, state)
  cases state with
  | draw => simp [KiloblockMode.MatchesState, hmode] at hmatches
  | active signal =>
      simp [KiloblockMode.MatchesState, hmode] at hmatches
  | absorbed quitters =>
      let value := table.terminal quitters who.1 +
        construction.trackingCorrectionAtOrigin origin who
      have hcurrent : construction.normalPotential who t
          (past, PublicQuittingState.absorbed quitters) = value := by
        simp only [KiloblockConstruction.normalPotential, hmode]
        rfl
      rw [hcurrent]
      unfold StochasticGame.historyContinuationEU
      calc
        expect
            ((publicQuittingGame table
              construction.profile.signalLaw).stageActionDist
                construction.profile.strategy (past, .absorbed quitters))
            (fun action =>
              expect ((publicQuittingGame table
                construction.profile.signalLaw).transition
                  (.absorbed quitters) action)
                (fun nextState => construction.normalPotential who (t + 1)
                  (Fin.snoc past (.absorbed quitters, action), nextState))) =
            expect
              ((publicQuittingGame table
                construction.profile.signalLaw).stageActionDist
                  construction.profile.strategy (past, .absorbed quitters))
              (fun _ => value) := by
          apply congrArg (expect ((publicQuittingGame table
            construction.profile.signalLaw).stageActionDist
              construction.profile.strategy (past, .absorbed quitters)))
          funext action
          simp only [publicQuittingGame, Math.Probability.expect_pure]
          have hsupp : PublicQuittingState.absorbed quitters ∈
              ((publicQuittingGame table
                construction.profile.signalLaw).transition
                  (.absorbed quitters)
                  action).support := by
            change PublicQuittingState.absorbed quitters ∈
              (PMF.pure (PublicQuittingState.absorbed quitters)).support
            rw [PMF.mem_support_iff]
            simp
          have hstep := construction.mode_step t
            (past, PublicQuittingState.absorbed quitters) action
            (PublicQuittingState.absorbed quitters) hsupp
          have hm : construction.mode (t + 1)
              (Fin.snoc past (PublicQuittingState.absorbed quitters, action),
                PublicQuittingState.absorbed quitters) =
              .absorbed origin := by
            simpa [KiloblockModeStep, hmode] using hstep
          change construction.normalPotential who (t + 1)
            (Fin.snoc past
                (PublicQuittingState.absorbed quitters, action),
              PublicQuittingState.absorbed quitters) = value
          rw [KiloblockConstruction.normalPotential, hm]
        _ = _ := expect_const _ _

theorem KiloblockConstruction.normalPotential_finalActive
    {table : Table ι} {ε : ℝ}
    (construction : KiloblockConstruction table ε)
    (who : NormalPlayer table) {t : ℕ}
    (history : (publicQuittingGame table
      construction.profile.signalLaw).Hist t)
    (hmode : construction.mode t history = .finalActive) :
    (publicQuittingGame table
      construction.profile.signalLaw).historyContinuationEU
        construction.profile.strategy (construction.normalPotential who)
        history =
      construction.normalPotential who t history := by
  classical
  rcases history with ⟨past, state⟩
  have hmatches := construction.mode_state t (past, state)
  cases state with
  | draw => simp [KiloblockMode.MatchesState, hmode] at hmatches
  | absorbed quitters =>
      simp [KiloblockMode.MatchesState, hmode] at hmatches
  | active signal =>
      let continueAction : (publicQuittingGame table
        construction.profile.signalLaw).JointAct := fun _ => false
      let drawState : (publicQuittingGame table
        construction.profile.signalLaw).State := PublicQuittingState.draw
      let base : ∀ player, PMF ((publicQuittingGame table
          construction.profile.signalLaw).Act player) :=
        fun _ => PMF.pure false
      have hfamily :
          (fun player => construction.profile.strategy player t
            (past, PublicQuittingState.active signal)) =
            base := by
        funext player
        rw [construction.strategy_eq]
        simp [hmode]
        rfl
      have hproduct : Math.PMFProduct.pmfPi base =
          PMF.pure continueAction := by
        exact Math.PMFProduct.pmfPi_pure continueAction
      have htransition : (publicQuittingGame table
          construction.profile.signalLaw).transition
          (PublicQuittingState.active signal) continueAction =
          PMF.pure drawState := by
        simp [publicQuittingGame, continueAction, drawState]
      have hsupp : drawState ∈
          ((publicQuittingGame table
            construction.profile.signalLaw).transition
            (PublicQuittingState.active signal) continueAction).support := by
        rw [htransition]
        rw [PMF.mem_support_iff]
        simp
      have hstep := construction.mode_step t
        (past, PublicQuittingState.active signal) continueAction
        drawState hsupp
      have hm : construction.mode (t + 1)
          (Fin.snoc past
              (PublicQuittingState.active signal, continueAction),
            drawState) = .draw .final := by
        simpa [KiloblockModeStep, hmode, drawState] using hstep
      have hcurrent : construction.normalPotential who t
          (past, PublicQuittingState.active signal) = 0 := by
        rw [KiloblockConstruction.normalPotential, hmode]
      rw [hcurrent]
      unfold StochasticGame.historyContinuationEU
      unfold StochasticGame.stageActionDist
      rw [hfamily, hproduct, Math.Probability.expect_pure,
        htransition, Math.Probability.expect_pure]
      rw [KiloblockConstruction.normalPotential, hm]

private theorem KiloblockConstruction.normalPotential_active_some_step
    {table : Table ι} {ε : ℝ}
    (construction : KiloblockConstruction table ε)
    (who : NormalPlayer table) {t : ℕ}
    (history : (publicQuittingGame table
      construction.profile.signalLaw).Hist t)
    (k : Fin (construction.blockCount + 1))
    (owner : NormalPlayer table) (remaining : ℕ)
    (hmode : construction.mode t history =
      .active k (some owner) remaining)
    (continuation : ℝ)
    (hcontinue : ∀ signal,
      history.2 = PublicQuittingState.active signal →
      construction.normalPotential who (t + 1)
        (Fin.snoc history.1
            (history.2, singleQuitAction owner.1 false),
          PublicQuittingState.draw) = continuation) :
    (publicQuittingGame table
      construction.profile.signalLaw).historyContinuationEU
        construction.profile.strategy (construction.normalPotential who)
      history =
      quittingMeshHazard (construction.attempt k owner).quitWeight
          (construction.mesh k) *
            (NormalMatrix table who owner +
              construction.trackingCorrection k who) +
        (1 - quittingMeshHazard (construction.attempt k owner).quitWeight
          (construction.mesh k)) * continuation := by
  classical
  rcases history with ⟨past, state⟩
  have hmatches := construction.mode_state t (past, state)
  cases state with
  | draw => simp [KiloblockMode.MatchesState, hmode] at hmatches
  | absorbed quitters =>
      simp [KiloblockMode.MatchesState, hmode] at hmatches
  | active signal =>
      let quitState : (publicQuittingGame table
          construction.profile.signalLaw).State :=
        PublicQuittingState.absorbed
          (quittingProjectiveSingletonTerminal owner.1)
      let drawState : (publicQuittingGame table
          construction.profile.signalLaw).State := PublicQuittingState.draw
      have htransitionQuit : (publicQuittingGame table
          construction.profile.signalLaw).transition
          (PublicQuittingState.active signal)
            (singleQuitAction owner.1 true) = PMF.pure quitState := by
        simpa [quitState] using
          publicQuittingGame_transition_singleQuitAction table
            construction.profile.signalLaw signal owner.1
      have htransitionContinue : (publicQuittingGame table
          construction.profile.signalLaw).transition
          (PublicQuittingState.active signal)
            (singleQuitAction owner.1 false) = PMF.pure drawState := by
        simpa [drawState] using
          publicQuittingGame_transition_singleQuitAction_false table
            construction.profile.signalLaw signal owner.1
      have hquitSupport : quitState ∈
          ((publicQuittingGame table
            construction.profile.signalLaw).transition
              (PublicQuittingState.active signal)
              (singleQuitAction owner.1 true)).support := by
        rw [htransitionQuit, PMF.mem_support_iff]
        simp
      have hquitStep := construction.mode_step t
        (past, PublicQuittingState.active signal)
        (singleQuitAction owner.1 true) quitState hquitSupport
      have hquitMode : construction.mode (t + 1)
          (Fin.snoc past
            (PublicQuittingState.active signal,
                singleQuitAction owner.1 true), quitState) =
          .absorbed (some k) := by
        simp [KiloblockModeStep, hmode,
          singleQuitAction_true_quitters] at hquitStep
        exact hquitStep.2
      have hquitValue : construction.normalPotential who (t + 1)
          (Fin.snoc past
              (PublicQuittingState.active signal,
                singleQuitAction owner.1 true), quitState) =
          NormalMatrix table who owner +
            construction.trackingCorrection k who := by
        rw [KiloblockConstruction.normalPotential, hquitMode]
        simp [quitState,
          KiloblockConstruction.trackingCorrectionAtOrigin, NormalMatrix]
      have hcontinueValue : construction.normalPotential who (t + 1)
          (Fin.snoc past
              (PublicQuittingState.active signal,
                singleQuitAction owner.1 false), drawState) =
          continuation := by
        simpa [drawState] using hcontinue signal rfl
      let coin := quittingMeshHazardCoin
        (construction.attempt k owner).quitWeight (construction.mesh k)
        (construction.attempt k owner).quitWeight_pos.le
        (construction.attempt k owner).quitWeight_lt_one
      let actionLaw : PMF ((publicQuittingGame table
          construction.profile.signalLaw).JointAct) :=
        coin.bind (fun quits => PMF.pure
          (singleQuitAction owner.1 quits))
      have hactionLaw : (publicQuittingGame table
          construction.profile.signalLaw).stageActionDist
          construction.profile.strategy
          (past, PublicQuittingState.active signal) = actionLaw := by
        unfold actionLaw coin singleQuitAction
        exact construction.stageActionDist_active_some
          (past, PublicQuittingState.active signal) k owner remaining hmode
      letI : Finite ((publicQuittingGame table
          construction.profile.signalLaw).JointAct) :=
        inferInstanceAs (Finite (ι → Bool))
      unfold StochasticGame.historyContinuationEU
      rw [hactionLaw]
      unfold actionLaw
      rw [Math.Probability.expect_bind]
      simp_rw [Math.Probability.expect_pure]
      rw [Math.Probability.expect_eq_sum, Fintype.sum_bool]
      rw [htransitionContinue, Math.Probability.expect_pure,
        hcontinueValue, htransitionQuit, Math.Probability.expect_pure,
        hquitValue]
      unfold coin
      simp only [quittingMeshHazardCoin_false_toReal,
        quittingMeshHazardCoin_true_toReal]

theorem KiloblockConstruction.normalPotential_active_some_beforeFinal
    {table : Table ι} {ε : ℝ}
    (construction : KiloblockConstruction table ε)
    (who : NormalPlayer table) {t : ℕ}
    (history : (publicQuittingGame table
      construction.profile.signalLaw).Hist t)
    (k : Fin (construction.blockCount + 1))
    (owner : NormalPlayer table) (remaining : ℕ)
    (hmode : construction.mode t history =
      .active k (some owner) remaining)
    (hnotFinal : (construction.attempt k owner).continuation =
        .restart ∨ k.1 ≠ 0) :
    (publicQuittingGame table
      construction.profile.signalLaw).historyContinuationEU
        construction.profile.strategy (construction.normalPotential who)
        history =
      construction.normalPotential who t history := by
  classical
  have hremaining : 0 < remaining :=
    construction.mode_remaining_pos t history k (some owner) remaining
      (Or.inl hmode)
  rcases history with ⟨past, state⟩
  have hmatches := construction.mode_state t (past, state)
  cases state with
  | draw => simp [KiloblockMode.MatchesState, hmode] at hmatches
  | absorbed quitters =>
      simp [KiloblockMode.MatchesState, hmode] at hmatches
  | active signal =>
      obtain ⟨tail, rfl⟩ := Nat.exists_eq_succ_of_ne_zero
        (Nat.ne_of_gt hremaining)
      let drawState : (publicQuittingGame table
          construction.profile.signalLaw).State := PublicQuittingState.draw
      have htransition : (publicQuittingGame table
          construction.profile.signalLaw).transition
          (PublicQuittingState.active signal)
            (singleQuitAction owner.1 false) = PMF.pure drawState := by
        simpa [drawState] using
          publicQuittingGame_transition_singleQuitAction_false table
            construction.profile.signalLaw signal owner.1
      have hsupp : drawState ∈
          ((publicQuittingGame table
            construction.profile.signalLaw).transition
              (PublicQuittingState.active signal)
              (singleQuitAction owner.1 false)).support := by
        rw [htransition, PMF.mem_support_iff]
        simp
      have hstep := construction.mode_step t
        (past, PublicQuittingState.active signal)
        (singleQuitAction owner.1 false) drawState hsupp
      let continuation := construction.selectedValue k (some owner) tail who +
        construction.trackingCorrection k who
      have hcontinueValue : construction.normalPotential who (t + 1)
          (Fin.snoc past
              (PublicQuittingState.active signal,
                singleQuitAction owner.1 false), drawState) =
          continuation := by
        cases tail with
        | succ nextTail =>
            have hm : construction.mode (t + 1)
                (Fin.snoc past
                    (PublicQuittingState.active signal,
                      singleQuitAction owner.1 false), drawState) =
                .draw (.resume k (some owner) (nextTail + 1)) := by
              simpa [KiloblockModeStep, hmode, drawState,
                singleQuitAction_false] using hstep
            rw [KiloblockConstruction.normalPotential, hm]
        | zero =>
            have hm : construction.mode (t + 1)
                (Fin.snoc past
                    (PublicQuittingState.active signal,
                      singleQuitAction owner.1 false), drawState) =
                .draw (phaseAfterAttempt table
                  (fun k owner => (construction.attempt k owner).continuation)
                  k (some owner)) := by
              simpa [KiloblockModeStep, hmode, drawState,
                singleQuitAction_false] using hstep
            cases hbranch : (construction.attempt k owner).continuation with
            | restart =>
              have hm' : construction.mode (t + 1)
                  (Fin.snoc past
                      (PublicQuittingState.active signal,
                        singleQuitAction owner.1 false), drawState) =
                    .draw (.choose k) := by
                simpa [phaseAfterAttempt, hbranch] using hm
              rw [KiloblockConstruction.normalPotential, hm']
              simp [continuation, KiloblockConstruction.selectedValue,
                BuildingAttempt.remainingValue_zero, hbranch]
            | advance =>
              have hk : k.1 ≠ 0 := hnotFinal.resolve_left (by
                rw [hbranch]
                exact AttemptContinuation.noConfusion)
              have hkpos : 0 < k.1 := Nat.pos_of_ne_zero hk
              let previous : Fin (construction.blockCount + 1) :=
                ⟨k.1 - 1, by omega⟩
              have hprevious : previous.1 < construction.blockCount := by
                dsimp [previous]
                omega
              have hkEq : k = ⟨previous.1 + 1, by omega⟩ := by
                apply Fin.ext
                dsimp [previous]
                omega
              have hm' : construction.mode (t + 1)
                  (Fin.snoc past
                      (PublicQuittingState.active signal,
                        singleQuitAction owner.1 false), drawState) =
                    .draw (.choose previous) := by
                simpa [phaseAfterAttempt, precedingKiloblockPhase,
                  hbranch, hk, previous] using hm
              have htelescope :=
                construction.point_add_trackingCorrection_succ
                  previous.1 hprevious who
              rw [← hkEq] at htelescope
              have htelescope' : construction.point k who +
                  construction.trackingCorrection k who =
                    (construction.buildingBlock previous).w who +
                      construction.trackingCorrection previous who := by
                convert htelescope using 1
              have hpotential : construction.normalPotential who (t + 1)
                  (Fin.snoc past
                      (PublicQuittingState.active signal,
                        singleQuitAction owner.1 false), drawState) =
                    (construction.buildingBlock previous).w who +
                      construction.trackingCorrection previous who := by
                rw [KiloblockConstruction.normalPotential, hm']
              rw [hpotential, ← htelescope']
              simp [continuation, KiloblockConstruction.selectedValue,
                BuildingAttempt.remainingValue_zero, hbranch]
      have hlocal := construction.normalPotential_active_some_step who
        (past, PublicQuittingState.active signal) k owner (tail + 1) hmode
        continuation (fun selected hselected => by
          cases PublicQuittingState.active.inj hselected
          simpa [drawState] using hcontinueValue)
      have hcurrent : construction.normalPotential who t
          (past, PublicQuittingState.active signal) =
            construction.selectedValue k (some owner) (tail + 1) who +
              construction.trackingCorrection k who := by
        rw [KiloblockConstruction.normalPotential, hmode]
      rw [hlocal, hcurrent]
      rw [construction.selectedValue_some_succ k owner tail who]
      dsimp [continuation]
      ring

theorem KiloblockConstruction.normalPotential_active_none_beforeFinal
    {table : Table ι} {ε : ℝ}
    (construction : KiloblockConstruction table ε)
    (who : NormalPlayer table) {t : ℕ}
    (history : (publicQuittingGame table
      construction.profile.signalLaw).Hist t)
    (k : Fin (construction.blockCount + 1)) (remaining : ℕ)
    (hmode : construction.mode t history = .active k none remaining)
    (hnotFinal : remaining ≠ 1 ∨ k.1 ≠ 0) :
    (publicQuittingGame table
      construction.profile.signalLaw).historyContinuationEU
        construction.profile.strategy (construction.normalPotential who)
        history =
      construction.normalPotential who t history := by
  classical
  have hremaining : 0 < remaining :=
    construction.mode_remaining_pos t history k none remaining
      (Or.inl hmode)
  rcases history with ⟨past, state⟩
  have hmatches := construction.mode_state t (past, state)
  cases state with
  | draw => simp [KiloblockMode.MatchesState, hmode] at hmatches
  | absorbed quitters =>
      simp [KiloblockMode.MatchesState, hmode] at hmatches
  | active signal =>
      obtain ⟨tail, rfl⟩ := Nat.exists_eq_succ_of_ne_zero
        (Nat.ne_of_gt hremaining)
      let continueAction : (publicQuittingGame table
          construction.profile.signalLaw).JointAct := fun _ => false
      let base : ∀ player, PMF ((publicQuittingGame table
          construction.profile.signalLaw).Act player) :=
        fun _ => PMF.pure false
      let drawState : (publicQuittingGame table
          construction.profile.signalLaw).State := PublicQuittingState.draw
      have hfamily :
          (fun player => construction.profile.strategy player t
            (past, PublicQuittingState.active signal)) = base := by
        funext player
        rw [construction.strategy_eq]
        simp [hmode, base]
      have hproduct : Math.PMFProduct.pmfPi base =
          PMF.pure continueAction := by
        exact Math.PMFProduct.pmfPi_pure continueAction
      have htransition : (publicQuittingGame table
          construction.profile.signalLaw).transition
          (PublicQuittingState.active signal) continueAction =
          PMF.pure drawState := by
        simp [publicQuittingGame, continueAction, drawState]
      have hsupp : drawState ∈
          ((publicQuittingGame table
            construction.profile.signalLaw).transition
              (PublicQuittingState.active signal) continueAction).support := by
        rw [htransition, PMF.mem_support_iff]
        simp
      have hstep := construction.mode_step t
        (past, PublicQuittingState.active signal) continueAction drawState hsupp
      have hnextValue : construction.normalPotential who (t + 1)
          (Fin.snoc past
            (PublicQuittingState.active signal, continueAction), drawState) =
          construction.point k who +
            construction.trackingCorrection k who := by
        cases tail with
        | succ nextTail =>
            have hm : construction.mode (t + 1)
                (Fin.snoc past
                  (PublicQuittingState.active signal, continueAction),
                    drawState) =
                .draw (.resume k none (nextTail + 1)) := by
              simpa [KiloblockModeStep, hmode, continueAction, drawState]
                using hstep
            rw [KiloblockConstruction.normalPotential, hm]
            rfl
        | zero =>
            have hk : k.1 ≠ 0 := hnotFinal.resolve_left (by simp)
            have hkpos : 0 < k.1 := Nat.pos_of_ne_zero hk
            let previous : Fin (construction.blockCount + 1) :=
              ⟨k.1 - 1, by omega⟩
            have hprevious : previous.1 < construction.blockCount := by
              dsimp [previous]
              omega
            have hkEq : k = ⟨previous.1 + 1, by omega⟩ := by
              apply Fin.ext
              dsimp [previous]
              omega
            have hm : construction.mode (t + 1)
                (Fin.snoc past
                  (PublicQuittingState.active signal, continueAction),
                    drawState) = .draw (.choose previous) := by
              simpa [KiloblockModeStep, hmode, continueAction, drawState,
                phaseAfterAttempt, precedingKiloblockPhase, hk, previous]
                using hstep
            have htelescope :=
              construction.point_add_trackingCorrection_succ
                previous.1 hprevious who
            rw [← hkEq] at htelescope
            have htelescope' : construction.point k who +
                construction.trackingCorrection k who =
                  (construction.buildingBlock previous).w who +
                    construction.trackingCorrection previous who := by
              convert htelescope using 1
            rw [KiloblockConstruction.normalPotential, hm]
            exact htelescope'.symm
      have hcurrent : construction.normalPotential who t
          (past, PublicQuittingState.active signal) =
          construction.point k who +
            construction.trackingCorrection k who := by
        rw [KiloblockConstruction.normalPotential, hmode]
        rfl
      rw [hcurrent]
      unfold StochasticGame.historyContinuationEU
      unfold StochasticGame.stageActionDist
      rw [hfamily, hproduct, Math.Probability.expect_pure,
        htransition, Math.Probability.expect_pure]
      exact hnextValue

/-! Whether the schedule has not yet entered its final infinite tail. The
boolean stored after absorption remembers on which side of that boundary
absorption occurred. -/
def KiloblockConstruction.beforeFinal
    {table : Table ι} {ε : ℝ}
    (construction : KiloblockConstruction table ε) (t : ℕ)
    (history : (publicQuittingGame table
      construction.profile.signalLaw).Hist t) : Prop :=
  match construction.mode t history with
  | .draw .final => False
  | .finalActive => False
  | .absorbed origin => origin.isSome
  | _ => True

/-! Indicator that absorption has occurred while the construction's history
marker still lies before the final kiloblock. -/
def absorbedBeforeFinalIndicator
    {table : Table ι} {ε : ℝ}
    (construction : KiloblockConstruction table ε) (t : ℕ)
    (history : (publicQuittingGame table
      construction.profile.signalLaw).Hist t) : ℝ := by
  classical
  exact match history.2 with
    | .draw => 0
    | .active _ => 0
    | .absorbed _ => if construction.beforeFinal t history then 1 else 0

/-! Probability of absorption before the final kiloblock under a supplied
public behavior profile, represented as the supremum of its finite-horizon
event masses. -/
def absorptionBeforeFinalProbability
    {table : Table ι} {ε : ℝ}
    (construction : KiloblockConstruction table ε)
    (strategy : (publicQuittingGame table
      construction.profile.signalLaw).BehaviorProfile) : ℝ :=
  ⨆ t, expect
    ((publicQuittingGame table construction.profile.signalLaw).histDist
      strategy .draw t)
    (absorbedBeforeFinalIndicator construction t)

/-! Lemma 3.9's induced probability after player `who` is forced to Continue
at every public history. -/
def continueTerminationBeforeFinal
    {table : Table ι} {ε : ℝ}
    (construction : KiloblockConstruction table ε) (who : ι) : ℝ :=
  absorptionBeforeFinalProbability construction
    (Function.update construction.profile.strategy who
      (fun _ _ => PMF.pure false))

/-! Lemma 3.8: for normal `i`, `|γ_i(ξ*)-w_i(yᴷ)|<2ε`. -/
theorem lemma3_8
    (table : Table ι) {ε : ℝ} (hε : 0 < ε)
    (construction : KiloblockConstruction table ε) :
    ∀ i : NormalPlayer table,
      |construction.profile.payoff i.1 - construction.normalTarget i| <
        2 * ε := by
  sorry

/-! Lemma 3.9: continuing by a normal player still terminates with probability
at least `1-ε` before the last kiloblock. -/
theorem lemma3_9
    (table : Table ι) {ε : ℝ} (hε : 0 < ε)
    (construction : KiloblockConstruction table ε) :
    ∀ i : NormalPlayer table,
      continueTerminationBeforeFinal construction i.1 ≥ 1 - ε := by
  sorry

/-! Lemma 3.10: a normal player's deviation is capped by `wᵢ(yᴷ)+5ε`;
an abnormal player's gain over the prescribed profile is at most `5ε`.
The printed abnormal-player paragraph writes `wᵢ(yᴷ)`, although `w`
has only normal coordinates; its actual argument is the direct gain bound
recorded by the second branch below. -/
theorem lemma3_10
    {table : Table ι} {ε : ℝ} (hε : 0 < ε)
    (construction : KiloblockConstruction table ε) :
    ∀ i (deviation : (publicQuittingGame table
      construction.profile.signalLaw).BehaviorStrategy i),
      publicQuittingPayoff table construction.profile.signalLaw
          (Function.update construction.profile.strategy i deviation) i ≤
        if hi : i ∈ NormalPlayers table then
          construction.normalTarget ⟨i, hi⟩ + 5 * ε
        else construction.profile.payoff i + 5 * ε := by
  sorry

/-! Section 3.4 concludes from Lemmas 3.8--3.10 that the constructed profile
is a sunspot `7ε`-equilibrium. -/

/-! Section 3.4: the constructed profile is a sunspot `7ε`-equilibrium. -/
theorem section3_4
    (table : Table ι) (profile : SunspotProfile table)
    (target : NormalPlayer table → ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    (hpayoff : ∀ who : NormalPlayer table,
      |profile.payoff who.1 - target who| < 2 * ε)
    (hdeviation : ∀ who
      (deviation : (publicQuittingGame table profile.signalLaw).BehaviorStrategy who),
      publicQuittingPayoff table profile.signalLaw
        (Function.update profile.strategy who deviation) who ≤
          if hwho : who ∈ NormalPlayers table then
            target ⟨who, hwho⟩ + 5 * ε
          else profile.payoff who + 5 * ε) :
    SunspotEpsilonEquilibrium table (7 * ε) profile := by
  intro who deviation
  have hupper := hdeviation who deviation
  by_cases hwho : who ∈ NormalPlayers table
  · rw [dif_pos hwho] at hupper
    have hlower := (abs_lt.mp (hpayoff ⟨who, hwho⟩)).1
    dsimp only [SunspotProfile.payoff] at hlower
    linarith
  · rw [dif_neg hwho] at hupper
    dsimp only [SunspotProfile.payoff] at hupper
    linarith

/-! ## Section 4 — sunspot payoff characterization -/

/-! **Definition (paper, Section 4).** A vector is a sunspot equilibrium
payoff if it is the limit of payoffs of sunspot ε-equilibria as ε↓0. -/

/-! A sunspot equilibrium payoff is a limit of payoffs of sunspot
ε-equilibria as `ε↓0`. -/
def SunspotEquilibriumPayoff
    (table : Table ι) (value : Payoff ι) : Prop :=
  ∃ profiles : ℕ → SunspotProfile table,
    (∀ n : ℕ, SunspotEpsilonEquilibrium table
      ((n + 1 : ℝ)⁻¹) (profiles n)) ∧
    ∀ who, Tendsto (fun n => (profiles n).payoff who) atTop (𝓝 (value who))

/-! **M-matrix convention (paper).** Since the diagonal of `R̂` is zero, the
paper calls a Q-matrix an M-matrix when every row and every column has exactly
one positive entry. -/

/-! The v1 paper's M-matrix convention: Q, with exactly one positive entry in
each row and column. -/
def MMatrix (M : ι → ι → ℝ) : Prop :=
  QMatrix M ∧
    (∀ who, (Finset.filter (fun owner => 0 < M who owner) Finset.univ).card = 1) ∧
    (∀ owner, (Finset.filter (fun who => 0 < M who owner) Finset.univ).card = 1)

/-! `conv{rⁱ : i∈I*}` in the full payoff space of all players. -/
def NormalSingletonHull (table : Table ι) : Set (Payoff ι) :=
  convexHull ℝ (Set.range fun owner : NormalPlayer table =>
    fun who => table.terminal (quittingProjectiveSingletonTerminal owner) who)

/-! `D̃ = conv{rⁱ : i∈I*} ∩ ℝ^N_{≥0}` from Section 4. -/
def TildeD (table : Table ι) : Set (Payoff ι) :=
  NormalSingletonHull table ∩ {value | ∀ who, 0 ≤ value who}

/-! **Theorem 4.3 (paper).** If `R̂` is an M-matrix, every vector in
`D~ = conv(r¹,…,rⁿ)∩ℝⁿ_≥0` is a sunspot equilibrium payoff. -/

/-! Theorem 4.3: an M-matrix makes every `v∈D~` a sunspot equilibrium payoff. -/
theorem theorem4_3
    (table : Table ι)
    (hnormalized : SoloExitNormalized table)
    (hbounded : TablePayoffsBounded table)
    (hM : MMatrix (NormalMatrix table)) :
    ∀ value ∈ TildeD table, SunspotEquilibriumPayoff table value := by
  sorry

/-! ## Section 5 — discussion and open problems -/

/-! **Section 5.1 (paper).** The alpha players are the intersection of the
decreasing recursion
`I₀=I`,
`Iₗ₊₁={i∈Iₗ | ∃j∈Iₗ\{i}, rʲ_i≤0}`.
This is different from the min--max normal-player set in Section 2.3. Under
Assumption 2.1 it is exactly the production `normalCore` below. -/

abbrev AlphaPlayers (table : Table ι) :=
  normalCore (normalizedSoloMatrix table.zeroNeverReward)

abbrev AlphaMatrix (table : Table ι) :=
  normalizedNormalPlayerMatrix table.zeroNeverReward

def HasAlphaPlayers (table : Table ι) : Prop :=
  (AlphaPlayers table).Nonempty

/-! Every alpha player is normal, as the paper notes after equation (19). -/
theorem alphaPlayer_isNormal
    (table : Table ι) (hnormalized : SoloExitNormalized table)
    (hbounded : TablePayoffsBounded table) (who : AlphaPlayers table) :
    IsNormalPlayer table who.1 := by
  by_contra habnormal
  obtain ⟨owner, hne, hnonpositive⟩ :=
    exists_blocker_of_mem_normalCore
      (normalizedSoloMatrix table.zeroNeverReward) who.2
  have hmatrix := congr_fun
    (congr_fun
      (normalizedSoloMatrix_zeroNeverReward_eq_singletonMatrix
        table hnormalized) who.1) owner
  rw [hmatrix] at hnonpositive
  have hpositive := lemma2_6 table hnormalized hbounded habnormal hne
  exact (not_lt_of_ge hnonpositive) hpositive

/-! **Theorem 5.1(1) (paper).** If the alpha-player matrix has no
nontrivial homogeneous solution and is not Q, stationary approximate
equilibria exist. The checked production theorem proves the stronger claim
that these equilibria approach one fixed payoff. -/
theorem theorem5_1_nonQ
    (table : Table ι)
    (hnormal : HasAlphaPlayers table)
    (hzero : ¬HasNontrivialZeroProjectiveLCPSolution (AlphaMatrix table))
    (hnotQ : ¬QMatrix (AlphaMatrix table)) :
    StationaryEpsilonEquilibria table := by
  rw [hasNontrivialZeroProjectiveLCPSolution_iff_homogeneous] at hzero
  have hnotStandard : ¬IsStandardQMatrix (AlphaMatrix table) := by
    rw [← isProjectiveQMatrix_iff_standard_of_noHomogeneous
      (AlphaMatrix table) hzero]
    exact hnotQ
  let branch : OrdinaryNonQMatrixBranch table.zeroNeverReward :=
    { normal_nonempty := hnormal
      no_homogeneous := hzero
      normal_not_standardQ := hnotStandard }
  obtain ⟨value, hvalue⟩ :=
    exists_stationaryUniformEquilibriumPayoff_of_ordinaryNonQMatrixBranch
      table.zeroNeverReward branch
  change table.StationaryεEquilibriumExistence
  rw [QuittingPayoffTable.stationaryεEquilibriumExistence_iff]
  exact hvalue.hasApproximateEquilibria

/-! Theorem 5.1(2) repeats the Q-side public-signal conclusion of Theorem
2.13 with alpha players. Its semantic proof is the same kiloblock compiler
isolated in Sections 3.3--3.4 above. -/

/-! The paper discusses stopping games, absorbing games, the need for a
uniform lower bound on quitting probabilities, finite-range recursions, the
inverse-positivity question for zero-diagonal Q-matrices, and the question
whether a column with strictly negative off-diagonal entries forces Q. These
are open-problem prose, not Lean theorem declarations. -/

end
end Literature.SolanAndSolan2020
