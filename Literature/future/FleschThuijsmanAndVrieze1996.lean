import Literature.FleschThuijsmanAndVrieze1997
import MathUE.Probability.RatioProperPair

/-!
# Recursive repeated games with absorbing states

J. Flesch, F. Thuijsman and O. J. Vrieze, *Mathematics of Operations Research*
21 (1996), 1016–1022. DOI: `10.1287/moor.21.4.1016`.
Primary source: <https://dke.maastrichtuniversity.nl/f.thuijsman/recursive%20repeated.pdf>.

This is a partial paper audit. Definition 2.3 and Theorem 2.4 use the paper's
finite probability simplexes and absorption-weighted reward tables, delegating
the proper-pair construction to the generic ratio-ranking theorem. Example 3
is the same three-player game analyzed in the 1997 paper, so its table and
stationary conclusions delegate to that existing formalization. The printed
exclusion for every positive error is refuted; the corrected exclusion below
one positive threshold is retained.

## Sections 1–3: source inventory

Section 1 introduces finite stochastic games and expected pathwise limiting
average payoffs. Definition 2.1 introduces absorption probabilities, carriers,
absorbing pure actions and pure best replies. Lemma 2.2 gives the stationary
payoff ratio. Definition 2.3 introduces proper and delta-proper strategy pairs;
Theorem 2.4 proves existence of a proper pair. Theorem 3.1 proves stationary
approximate-equilibrium existence for two-player recursive repeated games with
absorbing states; Lemma 3.2 supplies its best-reply mass-ratio estimate.

Definition 2.3 and Theorem 2.4 are formalized below in their numerical-table
presentation. The other general definitions and results, Examples 1, 2 and 4,
and the three final remarks are not formalized in this file. In particular,
Lemma 2.2's expected-pathwise-liminf payoff identity and the all-behavioral
best-reply semantics used by Lemma 3.2 and Theorem 3.1 remain unformalized here.
The two-player quitting existence theorem is not asserted to cover arbitrary
action sets or probabilistic absorption, and this file does not claim complete
paper coverage or a fixed-target uniform-equilibrium payoff from Theorem 3.1.
-/

noncomputable section

namespace Literature.FleschThuijsmanAndVrieze1996

/-! ## Section 2: proper strategy pairs

The table records the absorption probability and both absorbing rewards for
each live-state action pair. The live-state stage reward is zero. Rewards at
zero-probability entries are immaterial: multiplication by the absorption
probability implements the paper's convention that those entries have value
zero. These are numerical source data, not a separately constructed stochastic
game or a new identification of expected-pathwise-liminf payoffs.

Stationary strategies are literally finite real probability vectors. Pure
stationary values below are the ratios in Lemma 2.2, with value zero when the
denominator vanishes. Their agreement with the actual stochastic-game payoff
is not proved here. Definition 2.3 uses these numerical ratios; its proper-pair
limit is along a discrete sequence, as specified by the paper's basic assumptions.
-/

/-- Canonical two-player absorption probabilities and absorbing payoff tables. -/
structure AbsorbingGameData (I J : Type*) where
  absorptionProbability : I → J → Set.Icc (0 : ℝ) 1
  reward1 : I → J → ℝ
  reward2 : I → J → ℝ

/-- The paper's simplex of stationary strategies at the live state. -/
abbrev StationaryStrategy (I : Type*) [Fintype I] :=
  {x : I → ℝ // x ∈ GameTheory.Math.Probability.simplexWeights I}

namespace AbsorbingGameData

variable {I J : Type*}

def absorptionCoefficients (G : AbsorbingGameData I J) : I → J → ℝ :=
  fun i j => G.absorptionProbability i j

/-- Actual absorption-weighted player-one rewards, not independent numerator data. -/
def payoffNumerator1 (G : AbsorbingGameData I J) : I → J → ℝ :=
  fun i j => G.absorptionCoefficients i j * G.reward1 i j

/-- Actual absorption-weighted player-two rewards. -/
def payoffNumerator2 (G : AbsorbingGameData I J) : I → J → ℝ :=
  fun i j => G.absorptionCoefficients i j * G.reward2 i j

end AbsorbingGameData

variable {I J : Type*} [Fintype I] [Fintype J]

/-- The numerical pure row payoff in Lemma 2.2's stationary ratio presentation. -/
def pureStationaryPayoff1 (G : AbsorbingGameData I J)
    (y : StationaryStrategy J) (i : I) : ℝ :=
  Math.Probability.RatioProperPair.rowRatio
    G.absorptionCoefficients G.payoffNumerator1 y.1 i

/-- The analogous numerical pure column payoff. -/
def pureStationaryPayoff2 (G : AbsorbingGameData I J)
    (x : StationaryStrategy I) (j : J) : ℝ :=
  Math.Probability.RatioProperPair.columnRatio
    G.absorptionCoefficients G.payoffNumerator2 x.1 j

/-- Definition 2.3: full mixing and both strict-payoff ranking inequalities. -/
def IsDeltaProperPair (G : AbsorbingGameData I J) (δ : ℝ)
    (x : StationaryStrategy I) (y : StationaryStrategy J) : Prop :=
  Math.Probability.RatioProperPair.IsDeltaProperPair
    G.absorptionCoefficients G.payoffNumerator1 G.payoffNumerator2 δ x.1 y.1

/-- Definition 2.3: a limit of delta-proper pairs with positive delta tending to zero. -/
def IsProperPair (G : AbsorbingGameData I J)
    (x : StationaryStrategy I) (y : StationaryStrategy J) : Prop :=
  Math.Probability.RatioProperPair.IsProperPair
    G.absorptionCoefficients G.payoffNumerator1 G.payoffNumerator2 x.1 y.1

/-- Theorem 2.4: every finite two-player absorption table has a proper strategy pair. -/
theorem theorem2_4 [Nonempty I] [Nonempty J] (G : AbsorbingGameData I J) :
    ∃ (x : StationaryStrategy I) (y : StationaryStrategy J), IsProperPair G x y := by
  obtain ⟨x, y, hxy⟩ := Math.Probability.RatioProperPair.exists_properPair
    G.absorptionCoefficients G.payoffNumerator1 G.payoffNumerator2
    (fun i j => (G.absorptionProbability i j).2.1)
  exact ⟨⟨x, hxy.1⟩, ⟨y, hxy.2.1⟩, hxy⟩

/-! ## Section 4: Example 3

The three coordinates choose Top/Bottom, Left/Right and Near/Far respectively.
The Boolean `false` denotes the first action. The all-first-action row is live
with zero stage payoff; every other row absorbs with probability one.

The definitions below use the checked terminal-payoff presentation from the
1997 formalization. They do not introduce a separate expected-pathwise-liminf
semantics or prove a new equivalence with that semantics. Unilateral deviations
in the equilibrium predicate are all behavioral strategies, not just stationary
ones. The error and stationary-profile quantifiers are preserved exactly.
-/

abbrev Example3Player := Literature.FleschThuijsmanAndVrieze1997.Player

/-- The literal table of Example 3, including its zero live row. -/
abbrev example3TerminalReward := Literature.FleschThuijsmanAndVrieze1997.terminalReward

/-- The seven absorbing rows in quitter-set form. -/
abbrev example3Reward := GameTheory.CyclicThreePlayerQuitting.AdmissibleCycle.reward

/-- The actual recursive quitting game associated with Example 3. -/
abbrev example3Game := GameTheory.quittingGame example3Reward

abbrev Example3StationaryProfile := Literature.FleschThuijsmanAndVrieze1997.StationaryProfile

/-- The literal stationary behavior profile of the actual Example 3 game. -/
abbrev example3StationaryBehaviorProfile (profile : Example3StationaryProfile) :=
  Literature.FleschThuijsmanAndVrieze1997.stationaryBehaviorProfile profile

/-- Terminal limiting-average equilibrium against all behavioral deviations. -/
abbrev Example3EpsilonEquilibrium (ε : ℝ) (profile : Example3StationaryProfile) : Prop :=
  example3Game.IsεAsymptoticNash (GameTheory.quittingTerminalPayoff example3Reward) ε
    (example3StationaryBehaviorProfile profile)

@[simp] theorem example3TerminalReward_TLN :
    example3TerminalReward ![false, false, false] = ![0, 0, 0] :=
  Literature.FleschThuijsmanAndVrieze1997.terminalReward_TLN

@[simp] theorem example3TerminalReward_BLN :
    example3TerminalReward ![true, false, false] = ![1, 3, 0] :=
  Literature.FleschThuijsmanAndVrieze1997.terminalReward_BLN

@[simp] theorem example3TerminalReward_TRN :
    example3TerminalReward ![false, true, false] = ![0, 1, 3] :=
  Literature.FleschThuijsmanAndVrieze1997.terminalReward_TRN

@[simp] theorem example3TerminalReward_TLF :
    example3TerminalReward ![false, false, true] = ![3, 0, 1] :=
  Literature.FleschThuijsmanAndVrieze1997.terminalReward_TLF

@[simp] theorem example3TerminalReward_BRN :
    example3TerminalReward ![true, true, false] = ![1, 0, 1] :=
  Literature.FleschThuijsmanAndVrieze1997.terminalReward_BRN

@[simp] theorem example3TerminalReward_BLF :
    example3TerminalReward ![true, false, true] = ![0, 1, 1] :=
  Literature.FleschThuijsmanAndVrieze1997.terminalReward_BLF

@[simp] theorem example3TerminalReward_TRF :
    example3TerminalReward ![false, true, true] = ![1, 1, 0] :=
  Literature.FleschThuijsmanAndVrieze1997.terminalReward_TRF

@[simp] theorem example3TerminalReward_BRF :
    example3TerminalReward ![true, true, true] = ![0, 0, 0] :=
  Literature.FleschThuijsmanAndVrieze1997.terminalReward_BRF

/-- Example 3 has no exact stationary terminal equilibrium. -/
theorem example3_no_stationary_equilibrium :
    ¬ ∃ profile : Example3StationaryProfile, Example3EpsilonEquilibrium 0 profile :=
  Literature.FleschThuijsmanAndVrieze1997.lemma3_1

/-- The literal printed exclusion for every positive error is false. -/
theorem example3_printed_refuted :
    ¬ (∀ ε : ℝ, 0 < ε →
      ¬ ∃ profile : Example3StationaryProfile, Example3EpsilonEquilibrium ε profile) :=
  Literature.FleschThuijsmanAndVrieze1997.theorem3_2_printed_refuted

/-- Corrected Example 3: exclusion holds below one positive error threshold. -/
theorem example3_corrected :
    ∃ threshold : ℝ, 0 < threshold ∧
      ∀ ε : ℝ, 0 < ε → ε < threshold →
        ¬ ∃ profile : Example3StationaryProfile, Example3EpsilonEquilibrium ε profile :=
  Literature.FleschThuijsmanAndVrieze1997.theorem3_2_corrected

end Literature.FleschThuijsmanAndVrieze1996
