import Literature.FleschThuijsmanAndVrieze1997

/-!
# Recursive repeated games with absorbing states

J. Flesch, F. Thuijsman and O. J. Vrieze, *Mathematics of Operations Research*
21 (1996), 1016–1022. DOI: `10.1287/moor.21.4.1016`.
Primary source: <https://dke.maastrichtuniversity.nl/f.thuijsman/recursive%20repeated.pdf>.

This is a partial paper audit. Example 3 is the same three-player game analyzed
in the 1997 paper, so its table and stationary conclusions delegate to that
existing formalization. The printed exclusion for every positive error is
refuted; the corrected exclusion below one positive threshold is retained.

## Sections 1–3: source inventory not yet formalized here

Section 1 introduces finite stochastic games and expected pathwise limiting
average payoffs. Definition 2.1 introduces absorption probabilities, carriers,
absorbing pure actions and pure best replies. Lemma 2.2 gives the stationary
payoff ratio. Definition 2.3 introduces proper and delta-proper strategy pairs;
Theorem 2.4 proves existence of a proper pair. Theorem 3.1 proves stationary
approximate-equilibrium existence for two-player recursive repeated games with
absorbing states; Lemma 3.2 supplies its best-reply mass-ratio estimate.

Those general definitions and results, Examples 1, 2 and 4, and the three final
remarks are not formalized in this file. In particular, the two-player quitting
existence theorem is not asserted to cover arbitrary action sets or probabilistic
absorption, and this file does not claim complete paper coverage.
-/

noncomputable section

namespace Literature.FleschThuijsmanAndVrieze1996

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
