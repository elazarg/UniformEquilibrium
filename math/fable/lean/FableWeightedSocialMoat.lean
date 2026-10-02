/-
Weighted (anisotropic) social moat for quitting games.

Fix a costate `theta : Payoff ι`.  A reward table is *theta-socially
nonpositive* when every terminal coalition pays a nonpositive theta-weighted
total.  Every executable behavior profile then also pays a nonpositive
theta-weighted total, because its prescribed terminal payoff is the exact
barycentric mixture of the coalition reward vectors and the zero payoff of
Never, and the mixture masses are nonnegative.  The bound survives the passage
to the compact semantic carrier, since the weighted social total is continuous
and the carrier is the closure of the attainable semantic pairs.

Against this ceiling stands the weighted singleton moat of a theta-minimal
semantic pair.  For a strictly positive costate the weighted minimum margin
puts every player's weighted best-response cap at least one weighted minimum
above the player's own weighted solo quitting reward.  Summing the moat over
all players forces the minimizer's weighted social total to be at least the
weighted solo total plus `card - 1` weighted moat widths.  With a nonnegative
weighted solo total and at least two players this is strictly positive,
contradicting the weighted social ceiling.

The moat sum, stated without the social hypothesis, is an unconditional lower
bound on the weighted social total of any theta-minimal semantic pair whenever
no uniform equilibrium payoff exists.
-/
import UniformEquilibrium.Diagnostics.Quitting.TerminalCapNashEndpointTransport
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticWeightedAuxiliaryNashBudget
import UniformEquilibrium.Quitting.Root.TerminalSemanticMoment

noncomputable section

namespace GameTheory

open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## The weighted social ceiling -/

omit [DecidableEq ι] in
/-- If every terminal coalition pays a nonpositive `theta`-weighted total, then
so does every executable behavior profile.  The prescribed terminal payoff is
the exact reward moment of the profile's terminal outcome law, whose masses are
nonnegative, and Never pays zero. -/
theorem fable_weighted_sum_terminalPayoff_nonpos
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (theta : Payoff ι) (_htheta : ∀ who, 0 ≤ theta who)
    (hsocial : ∀ terminal, (∑ who, theta who * reward terminal who) ≤ 0)
    (profile : (quittingGame reward).BehaviorProfile) :
    (∑ who, theta who * quittingTerminalPayoff reward profile who) ≤ 0 := by
  have hmoment := quittingTerminalRewardMoment_outcomeMass reward profile
  have hmass := (quittingTerminalOutcomeMass_mem_stdSimplex reward profile).1
  have hplayer : ∀ who : ι, theta who * quittingTerminalPayoff reward profile who =
      ∑ outcome, quittingTerminalOutcomeMass reward profile outcome *
        (theta who * quittingTerminalOutcomeReward reward outcome who) := by
    intro who
    rw [← congrFun hmoment who]
    simp only [quittingTerminalRewardMoment]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun outcome _ => by ring
  have hout : ∀ outcome : QuittingTerminalOutcome ι,
      (∑ who, theta who * quittingTerminalOutcomeReward reward outcome who) ≤ 0 := by
    intro outcome
    cases outcome with
    | none => simp [quittingTerminalOutcomeReward]
    | some terminal => exact hsocial terminal
  calc (∑ who, theta who * quittingTerminalPayoff reward profile who)
      = ∑ who, ∑ outcome,
          quittingTerminalOutcomeMass reward profile outcome *
            (theta who * quittingTerminalOutcomeReward reward outcome who) :=
        Finset.sum_congr rfl fun who _ => hplayer who
    _ = ∑ outcome, ∑ who,
          quittingTerminalOutcomeMass reward profile outcome *
            (theta who * quittingTerminalOutcomeReward reward outcome who) :=
        Finset.sum_comm
    _ = ∑ outcome, quittingTerminalOutcomeMass reward profile outcome *
          ∑ who, theta who * quittingTerminalOutcomeReward reward outcome who :=
        Finset.sum_congr rfl fun outcome _ => by rw [Finset.mul_sum]
    _ ≤ 0 := by
        apply Finset.sum_nonpos
        intro outcome _
        simpa using mul_le_mul_of_nonneg_left (hout outcome) (hmass outcome)

/-- The weighted social ceiling passes to the compact semantic carrier: the
weighted social total is continuous, so its nonpositivity is a closed condition
containing every attainable semantic pair, hence their closure. -/
theorem fable_weighted_sum_carrierPayoff_nonpos
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (theta : Payoff ι) (htheta : ∀ who, 0 ≤ theta who)
    (hsocial : ∀ terminal, (∑ who, theta who * reward terminal who) ≤ 0)
    (pair : QuittingTerminalSemanticPair ι)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward) :
    (∑ who, theta who * pair.1 who) ≤ 0 := by
  have hcont : Continuous
      (fun candidate : QuittingTerminalSemanticPair ι =>
        ∑ who, theta who * candidate.1 who) :=
    continuous_finsetSum Finset.univ fun who _ =>
      continuous_const.mul ((continuous_apply who).comp continuous_fst)
  have hclosed : IsClosed
      {candidate : QuittingTerminalSemanticPair ι |
        (∑ who, theta who * candidate.1 who) ≤ 0} :=
    isClosed_le hcont continuous_const
  have hsubset : quittingAttainableTerminalSemanticPairs reward ⊆
      {candidate : QuittingTerminalSemanticPair ι |
        (∑ who, theta who * candidate.1 who) ≤ 0} := by
    rintro candidate ⟨profile, rfl⟩
    exact fable_weighted_sum_terminalPayoff_nonpos reward theta htheta hsocial profile
  exact (closure_minimal hsubset hclosed) hpair

/-! ## Existence of a weighted minimum on the carrier -/

omit [DecidableEq ι] in
/-- The weighted debt objective is continuous on semantic pairs. -/
private theorem fable_continuous_weightedDebtSum (theta : Payoff ι) :
    Continuous (quittingTerminalSemanticWeightedDebtSum theta :
      QuittingTerminalSemanticPair ι → ℝ) := by
  unfold quittingTerminalSemanticWeightedDebtSum
  exact continuous_finsetSum Finset.univ fun who _ =>
    continuous_const.mul (continuous_quittingTerminalSemanticDebt who)

/-- Every costate objective attains a minimum on the compact nonempty
semantic carrier. -/
private theorem fable_exists_weightedMinimum
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (theta : Payoff ι) :
    ∃ pair ∈ quittingTerminalSemanticCarrier reward,
      ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
        quittingTerminalSemanticWeightedDebtSum theta pair ≤
          quittingTerminalSemanticWeightedDebtSum theta candidate := by
  obtain ⟨pair, hpair, hmin⟩ :=
    (quittingTerminalSemanticCarrier_isCompact reward).exists_isMinOn
      (quittingTerminalSemanticCarrier_nonempty reward)
      (fable_continuous_weightedDebtSum theta).continuousOn
  exact ⟨pair, hpair, fun candidate hcandidate => hmin hcandidate⟩

/-! ## Positivity of the weighted minimum -/

/-- A positive total-debt infimum forces every carrier pair to carry a strictly
positive weighted debt, for any strictly positive costate. -/
private theorem fable_weightedDebtSum_pos
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hinf : 0 < quittingTerminalDebtSumInf reward)
    (theta : Payoff ι) (htheta : ∀ who, 0 < theta who)
    (pair : QuittingTerminalSemanticPair ι)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward) :
    0 < quittingTerminalSemanticWeightedDebtSum theta pair := by
  have hdebtNonneg : ∀ who, 0 ≤ quittingTerminalSemanticDebt pair who :=
    quittingTerminalSemanticDebt_nonneg_of_mem_carrier reward hpair
  obtain ⟨base, hbase, hbaseMin⟩ :=
    exists_minimum_quittingTerminalSemanticDebtSum reward
  have hinfValue : quittingTerminalDebtSumInf reward =
      quittingTerminalSemanticDebtSum base :=
    quittingTerminalDebtSumInf_eq_terminalSemanticDebtSum_of_minimum
      base hbase hbaseMin
  have hsumPos : 0 < quittingTerminalSemanticDebtSum pair := by
    have hle : quittingTerminalSemanticDebtSum base ≤
        quittingTerminalSemanticDebtSum pair := hbaseMin pair hpair
    rw [hinfValue] at hinf
    linarith
  obtain ⟨owner, -, howner⟩ : ∃ who ∈ (Finset.univ : Finset ι),
      (0 : ℝ) < quittingTerminalSemanticDebt pair who := by
    refine Finset.exists_lt_of_sum_lt (f := fun _ : ι => (0 : ℝ))
      (g := fun who : ι => quittingTerminalSemanticDebt pair who) ?_
    simpa [quittingTerminalSemanticDebtSum] using hsumPos
  have hterms : ∀ who ∈ (Finset.univ : Finset ι),
      0 ≤ theta who * quittingTerminalSemanticDebt pair who :=
    fun who _ => mul_nonneg (htheta who).le (hdebtNonneg who)
  have hsingle : theta owner * quittingTerminalSemanticDebt pair owner ≤
      ∑ who, theta who * quittingTerminalSemanticDebt pair who :=
    Finset.single_le_sum hterms (Finset.mem_univ owner)
  have hpos : 0 < theta owner * quittingTerminalSemanticDebt pair owner :=
    mul_pos (htheta owner) howner
  unfold quittingTerminalSemanticWeightedDebtSum
  linarith

/-! ## The weighted singleton moat sum -/

/-- Summing the weighted singleton moat of a positive theta-minimal semantic
pair over all players: the weighted social total of the prescribed coordinate is
at least the weighted solo reward total plus `card - 1` copies of the weighted
minimum. -/
private theorem fable_weighted_moat_sum
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (theta : Payoff ι) (htheta : ∀ who, 0 < theta who)
    (pair : QuittingTerminalSemanticPair ι)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticWeightedDebtSum theta pair ≤
        quittingTerminalSemanticWeightedDebtSum theta candidate)
    (hpositive : 0 < quittingTerminalSemanticWeightedDebtSum theta pair) :
    (∑ who, theta who * reward (quittingSingletonTerminal who) who) +
        ((Fintype.card ι : ℝ) - 1) *
          quittingTerminalSemanticWeightedDebtSum theta pair ≤
      ∑ who, theta who * pair.1 who := by
  have hmoat : ∀ who : ι,
      quittingTerminalSemanticWeightedDebtSum theta pair ≤
        theta who * (pair.2 who - reward (quittingSingletonTerminal who) who) :=
    fun who => minimumTerminalSemantic_weightedSingletonMargin
      (reward := reward) theta pair hpair hminimum hpositive htheta who
  have hconstant : (Fintype.card ι : ℝ) *
      quittingTerminalSemanticWeightedDebtSum theta pair =
      ∑ _who : ι, quittingTerminalSemanticWeightedDebtSum theta pair := by
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  have hsplit : ∑ who,
      theta who * (pair.2 who - reward (quittingSingletonTerminal who) who) =
      (∑ who, theta who * pair.2 who) -
        ∑ who, theta who * reward (quittingSingletonTerminal who) who := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun who _ => by ring
  have hsum : (Fintype.card ι : ℝ) *
      quittingTerminalSemanticWeightedDebtSum theta pair ≤
      (∑ who, theta who * pair.2 who) -
        ∑ who, theta who * reward (quittingSingletonTerminal who) who := by
    rw [hconstant, ← hsplit]
    exact Finset.sum_le_sum fun who _ => hmoat who
  have hdebt : quittingTerminalSemanticWeightedDebtSum theta pair =
      (∑ who, theta who * pair.2 who) - ∑ who, theta who * pair.1 who := by
    unfold quittingTerminalSemanticWeightedDebtSum quittingTerminalSemanticDebt
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun who _ => by ring
  linarith

/-! ## The unconditional weighted necessary condition -/

/-- Without any social hypothesis: if no uniform equilibrium payoff exists, then
for every strictly positive costate the weighted minimum on the semantic carrier
is strictly positive, and the weighted social total of the prescribed coordinate
of every theta-minimal semantic pair is at least the weighted solo reward total
plus `card - 1` copies of that weighted minimum. -/
theorem fable_counterexample_weightedMinimum_socialPayoff_lowerBound
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hno : ¬∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff)
    (theta : Payoff ι) (htheta : ∀ who, 0 < theta who)
    (pair : QuittingTerminalSemanticPair ι)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticWeightedDebtSum theta pair ≤
        quittingTerminalSemanticWeightedDebtSum theta candidate) :
    0 < quittingTerminalSemanticWeightedDebtSum theta pair ∧
      (∑ who, theta who * reward (quittingSingletonTerminal who) who) +
          ((Fintype.card ι : ℝ) - 1) *
            quittingTerminalSemanticWeightedDebtSum theta pair ≤
        ∑ who, theta who * pair.1 who := by
  have hinf : 0 < quittingTerminalDebtSumInf reward :=
    quittingTerminalDebtSumInf_pos_iff_not_exists_uniformEquilibriumPayoff.mpr hno
  have hpositive : 0 < quittingTerminalSemanticWeightedDebtSum theta pair :=
    fable_weightedDebtSum_pos reward hinf theta htheta pair hpair
  exact ⟨hpositive,
    fable_weighted_moat_sum reward theta htheta pair hpair hminimum hpositive⟩

/-! ## The weighted chamber theorem -/

/-- **Weighted social moat chamber.**  A quitting game with at least two players
carrying a strictly positive costate under which every terminal coalition pays a
nonpositive weighted total and the weighted solo total is nonnegative has a
uniform equilibrium payoff. -/
theorem fable_positiveCostate_socialNonpositive_exists_uniformEquilibriumPayoff
    [Nontrivial ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (theta : Payoff ι) (htheta : ∀ who, 0 < theta who)
    (hsocial : ∀ terminal, (∑ who, theta who * reward terminal who) ≤ 0)
    (hsolo : 0 ≤ ∑ who, theta who * reward (quittingSingletonTerminal who) who) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  by_contra hno
  haveI : Nonempty ι := ⟨(exists_pair_ne ι).choose⟩
  obtain ⟨pair, hpair, hminimum⟩ := fable_exists_weightedMinimum reward theta
  obtain ⟨hpositive, hmoat⟩ :=
    fable_counterexample_weightedMinimum_socialPayoff_lowerBound
      reward hno theta htheta pair hpair hminimum
  have hceiling : (∑ who, theta who * pair.1 who) ≤ 0 :=
    fable_weighted_sum_carrierPayoff_nonpos reward theta
      (fun who => (htheta who).le) hsocial pair hpair
  have hcard : (2 : ℝ) ≤ (Fintype.card ι : ℝ) := by
    have h2 : 2 ≤ Fintype.card ι := Fintype.one_lt_card (α := ι)
    exact_mod_cast h2
  have hscale : 2 * quittingTerminalSemanticWeightedDebtSum theta pair ≤
      (Fintype.card ι : ℝ) *
        quittingTerminalSemanticWeightedDebtSum theta pair :=
    mul_le_mul_of_nonneg_right hcard hpositive.le
  linarith

end GameTheory
