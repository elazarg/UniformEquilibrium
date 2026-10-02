/-
Exact-port invocation of the minimum-floor repair.

This file formalizes the final composition of section 4 of the note
`SOCIAL_WEIGHT_REVIEW__MINIMUM_FLOOR_REPAIR_TO_EXACT_PORT_AND_STRICT_CURL_NOGO`,
in the scope confirmed by sections 3 and 4 of its `CODEX_DESCENDANT` review:
the boxed conclusion (4.1).

Nothing new is proved about the exact port here.  The production structure
`QuittingPaidRowFloorSafeSource` asks for exactly two same-profile facts, an
actual paid first-disagreement row and the all-player punishment floor, and the
production capstone
`QuittingPaidRowFloorSafeSource.exists_markedExactOrbit_alternative_of_witness`
consumes that structure together with a terminal exploitability witness.  What
is added is:

* `P1`, the single-profile packaging: a pure-time pair with a positive gap
  decodes, at any smaller positive gain, into the production paid row, and the
  supplied all-player floor completes the floor-safe source;
* `P2`, the invocation at that packaging, restating the production disjunction
  verbatim; and
* `P3`, the composition with the checked entrance of `FableFloorRepairEntrance`:
  for all late indices the softened entrance profile carries the packaging at
  gain `D_* / 4`, safely below the retained `D_* / 2` gap, hence the exact-port
  alternative.

The right arm of the production alternative names the marked orbit built from
the source, so it is genuinely profile-dependent and cannot be lifted out of
the eventually-filter as stated.  What can be lifted is the case split itself:
`P4` records that either a uniform-equilibrium payoff exists outright, or every
late entrance profile is the literal paid suffix of a summable all-Continue
semantic port with positive paid-suffix reach.

Source attachment remains external provenance: the floor-safe structure stores
no incoming minimum chronology.  No forward exact spine and no completely
absorbing sequentially-perfect family are claimed.
-/
import FableFloorRepairEntrance
import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.Endpoint.PaidRowExactPortAlternative
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPaidFirstDisagreement
import UniformEquilibrium.Quitting.Terminal.TerminalExploitabilityWitness

noncomputable section

namespace GameTheory

open Filter _root_.Math.Probability Math.ProbabilityMassFunction

open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## P1: single-profile floor-safe packaging -/

/-- The floor-safe paid-row source packaged from one actual profile carrying a
pure-time pair of gap at least `gain` for `observer`, together with the
all-player behavioral punishment floor at that same profile.  The paid row is
the one produced by the production decoder
`exists_quittingPaidFirstDisagreementRow_of_pureTimePayoff_sub`. -/
def fableFloorRepairFloorSafeSource
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (observer : ι)
    (sourceWitness targetWitness : Option ℕ) (gain : ℝ) (hgain : 0 < gain)
    (hgap : gain ≤
      quittingPureTimeDeviationPayoff reward profile observer targetWitness -
        quittingPureTimeDeviationPayoff reward profile observer sourceWitness)
    (hfloor : ∀ who, quittingPunishmentValue reward who ≤
      quittingTerminalPayoff reward profile who) :
    QuittingPaidRowFloorSafeSource reward where
  profile := profile
  observer := observer
  gain := gain
  gain_pos := hgain
  row := (exists_quittingPaidFirstDisagreementRow_of_pureTimePayoff_sub reward
    profile observer sourceWitness targetWitness gain hgain hgap).choose
  punishment_le := hfloor

@[simp] theorem fableFloorRepairFloorSafeSource_profile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (observer : ι)
    (sourceWitness targetWitness : Option ℕ) (gain : ℝ) (hgain : 0 < gain)
    (hgap : gain ≤
      quittingPureTimeDeviationPayoff reward profile observer targetWitness -
        quittingPureTimeDeviationPayoff reward profile observer sourceWitness)
    (hfloor : ∀ who, quittingPunishmentValue reward who ≤
      quittingTerminalPayoff reward profile who) :
    (fableFloorRepairFloorSafeSource reward profile observer sourceWitness
      targetWitness gain hgain hgap hfloor).profile = profile := rfl

@[simp] theorem fableFloorRepairFloorSafeSource_observer
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (observer : ι)
    (sourceWitness targetWitness : Option ℕ) (gain : ℝ) (hgain : 0 < gain)
    (hgap : gain ≤
      quittingPureTimeDeviationPayoff reward profile observer targetWitness -
        quittingPureTimeDeviationPayoff reward profile observer sourceWitness)
    (hfloor : ∀ who, quittingPunishmentValue reward who ≤
      quittingTerminalPayoff reward profile who) :
    (fableFloorRepairFloorSafeSource reward profile observer sourceWitness
      targetWitness gain hgain hgap hfloor).observer = observer := rfl

@[simp] theorem fableFloorRepairFloorSafeSource_gain
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (observer : ι)
    (sourceWitness targetWitness : Option ℕ) (gain : ℝ) (hgain : 0 < gain)
    (hgap : gain ≤
      quittingPureTimeDeviationPayoff reward profile observer targetWitness -
        quittingPureTimeDeviationPayoff reward profile observer sourceWitness)
    (hfloor : ∀ who, quittingPunishmentValue reward who ≤
      quittingTerminalPayoff reward profile who) :
    (fableFloorRepairFloorSafeSource reward profile observer sourceWitness
      targetWitness gain hgain hgap hfloor).gain = gain := rfl

/-- The packaged row keeps the supplied source witness. -/
theorem fableFloorRepairFloorSafeSource_row_sourceWitness
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (observer : ι)
    (sourceWitness targetWitness : Option ℕ) (gain : ℝ) (hgain : 0 < gain)
    (hgap : gain ≤
      quittingPureTimeDeviationPayoff reward profile observer targetWitness -
        quittingPureTimeDeviationPayoff reward profile observer sourceWitness)
    (hfloor : ∀ who, quittingPunishmentValue reward who ≤
      quittingTerminalPayoff reward profile who) :
    (fableFloorRepairFloorSafeSource reward profile observer sourceWitness
      targetWitness gain hgain hgap hfloor).row.sourceWitness = sourceWitness :=
  (exists_quittingPaidFirstDisagreementRow_of_pureTimePayoff_sub reward profile
    observer sourceWitness targetWitness gain hgain hgap).choose_spec.1

/-- The packaged row keeps the supplied receiving witness. -/
theorem fableFloorRepairFloorSafeSource_row_receivingWitness
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (observer : ι)
    (sourceWitness targetWitness : Option ℕ) (gain : ℝ) (hgain : 0 < gain)
    (hgap : gain ≤
      quittingPureTimeDeviationPayoff reward profile observer targetWitness -
        quittingPureTimeDeviationPayoff reward profile observer sourceWitness)
    (hfloor : ∀ who, quittingPunishmentValue reward who ≤
      quittingTerminalPayoff reward profile who) :
    (fableFloorRepairFloorSafeSource reward profile observer sourceWitness
        targetWitness gain hgain hgap hfloor).row.receivingWitness =
      targetWitness :=
  (exists_quittingPaidFirstDisagreementRow_of_pureTimePayoff_sub reward profile
    observer sourceWitness targetWitness gain hgain hgap).choose_spec.2

/-- **P1.**  At one profile, all-player punishment floors together with a
pure-time pair of positive gap package the production floor-safe paid-row
source at any chosen gain below that gap.  The packaged source keeps the
literal profile, observer, gain, and both pure-time witnesses. -/
theorem fableFloorRepair_exists_floorSafeSource
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (observer : ι)
    (sourceWitness targetWitness : Option ℕ) (gain gap : ℝ) (hgain : 0 < gain)
    (hgainLe : gain ≤ gap)
    (hgap : gap ≤
      quittingPureTimeDeviationPayoff reward profile observer targetWitness -
        quittingPureTimeDeviationPayoff reward profile observer sourceWitness)
    (hfloor : ∀ who, quittingPunishmentValue reward who ≤
      quittingTerminalPayoff reward profile who) :
    ∃ source : QuittingPaidRowFloorSafeSource reward,
      source.profile = profile ∧
      source.observer = observer ∧
      source.gain = gain ∧
      source.row.sourceWitness = sourceWitness ∧
      source.row.receivingWitness = targetWitness :=
  ⟨fableFloorRepairFloorSafeSource reward profile observer sourceWitness
      targetWitness gain hgain (hgainLe.trans hgap) hfloor,
    rfl, rfl, rfl,
    fableFloorRepairFloorSafeSource_row_sourceWitness reward profile observer
      sourceWitness targetWitness gain hgain (hgainLe.trans hgap) hfloor,
    fableFloorRepairFloorSafeSource_row_receivingWitness reward profile observer
      sourceWitness targetWitness gain hgain (hgainLe.trans hgap) hfloor⟩

/-! ## P2: the exact-port alternative at the packaging -/

/-- **P2.**  The production capstone applied to the `P1` packaging.  The
disjunction is exactly the one the production theorem emits: a
uniform-equilibrium payoff of the quitting game, or a summable all-Continue
charge port of the marked orbit carrying both the literal terminal-semantic
port and positive limiting reach to the unchanged paid suffix. -/
theorem fableFloorRepair_exists_exactPort_alternative_of_paidPair
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (observer : ι)
    (sourceWitness targetWitness : Option ℕ) (gain gap : ℝ) (hgain : 0 < gain)
    (hgainLe : gain ≤ gap)
    (hgap : gap ≤
      quittingPureTimeDeviationPayoff reward profile observer targetWitness -
        quittingPureTimeDeviationPayoff reward profile observer sourceWitness)
    (hfloor : ∀ who, quittingPunishmentValue reward who ≤
      quittingTerminalPayoff reward profile who)
    (witness : QuittingTerminalExploitabilityWitness reward) :
    ∃ source : QuittingPaidRowFloorSafeSource reward,
      source.profile = profile ∧
      source.observer = observer ∧
      source.gain = gain ∧
      source.row.sourceWitness = sourceWitness ∧
      source.row.receivingWitness = targetWitness ∧
      ∃ marked : QuittingPaidRowMarkedExactOrbit source,
        (∃ payoff : Payoff ι,
          (quittingGame reward).IsUniformEquilibriumPayoff none payoff) ∨
        ∃ port : QuittingPunishmentFloorInfiniteOrbit.SummableChargeAllContinuePort
            marked.orbit,
          Nonempty
              (QuittingPaidRowMarkedExactOrbit.SummableSemanticPort marked port) ∧
            Nonempty
              (QuittingPaidRowMarkedExactOrbit.PositivePaidSuffixReach marked) :=
  ⟨fableFloorRepairFloorSafeSource reward profile observer sourceWitness
      targetWitness gain hgain (hgainLe.trans hgap) hfloor,
    rfl, rfl, rfl,
    fableFloorRepairFloorSafeSource_row_sourceWitness reward profile observer
      sourceWitness targetWitness gain hgain (hgainLe.trans hgap) hfloor,
    fableFloorRepairFloorSafeSource_row_receivingWitness reward profile observer
      sourceWitness targetWitness gain hgain (hgainLe.trans hgap) hfloor,
    QuittingPaidRowFloorSafeSource.exists_markedExactOrbit_alternative_of_witness
      _ witness⟩

/-! ## P3: composition with the checked entrance -/

/-- **P3, (4.1).**  Under the entrance hypothesis surface of
`fableFloorRepair_entrance` — a positive global minimum of terminal-semantic
debt carried by `mover` alone, punishment normality of the hard residual,
coordinatewise convergence of prescribed payoffs and caps, and asymptotically
cap-optimal mover plans — together with a terminal exploitability witness, for
all late indices the softened entrance profile is the literal paid suffix of a
production floor-safe source at gain `D_* / 4`, whose paid row keeps a source
witness supported by the mover's original stopping law and the mover's own
target plan, and the checked exact-port alternative holds at that source.

The gain `D_* / 4` sits strictly below the retained `D_* / 2` pure-time gap of
the entrance.  No cap attainment is used, and the source witness is not
required to remain supported by the softened prescribed law. -/
theorem fableFloorRepair_eventually_exactPort_alternative
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (sigmas : ℕ → (quittingGame reward).BehaviorProfile)
    (mover : ι) (targets : ℕ → Option ℕ) (epsilons : ℕ → ℝ)
    (pair : QuittingTerminalSemanticPair ι)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum pair ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpositive : 0 < quittingTerminalSemanticDebtSum pair)
    (hnormal : ∀ who, quittingPunishmentValue reward who ≤
      reward (quittingSingletonTerminal who) who)
    (hmoverDebt : quittingTerminalSemanticDebt pair mover =
      quittingTerminalSemanticDebtSum pair)
    (hotherDebt : ∀ observer, observer ≠ mover →
      quittingTerminalSemanticDebt pair observer = 0)
    (hpayoff : ∀ observer, Tendsto (fun n =>
      quittingTerminalPayoff reward (sigmas n) observer) atTop
      (𝓝 (pair.1 observer)))
    (hcap : ∀ observer, Tendsto (fun n =>
      quittingContinuationBestResponseValue reward (sigmas n) observer) atTop
      (𝓝 (pair.2 observer)))
    (hepsilons : Tendsto epsilons atTop (𝓝 0))
    (htargets : ∀ n,
      quittingContinuationBestResponseValue reward (sigmas n) mover -
        epsilons n ≤
      quittingPureTimeDeviationPayoff reward (sigmas n) mover (targets n))
    (witness : QuittingTerminalExploitabilityWitness reward) :
    ∀ᶠ n in atTop,
      ∃ source : QuittingPaidRowFloorSafeSource reward,
        source.profile =
          fableFloorRepairEntranceProfile reward sigmas mover targets n ∧
        source.observer = mover ∧
        source.gain = quittingTerminalSemanticDebtSum pair / 4 ∧
        source.row.sourceWitness ∈
          (quittingBehaviorStoppingLaw reward (sigmas n mover)).support ∧
        source.row.receivingWitness = targets n ∧
        ∃ marked : QuittingPaidRowMarkedExactOrbit source,
          (∃ payoff : Payoff ι,
            (quittingGame reward).IsUniformEquilibriumPayoff none payoff) ∨
          ∃ port : QuittingPunishmentFloorInfiniteOrbit.SummableChargeAllContinuePort
              marked.orbit,
            Nonempty
                (QuittingPaidRowMarkedExactOrbit.SummableSemanticPort marked port) ∧
              Nonempty
                (QuittingPaidRowMarkedExactOrbit.PositivePaidSuffixReach marked) := by
  have hentrance := fableFloorRepair_entrance reward sigmas mover targets
    epsilons pair hpair hminimum hpositive hnormal hmoverDebt hotherDebt hpayoff
    hcap hepsilons htargets
  filter_upwards [hentrance.2.2.2.2] with n hn
  obtain ⟨hfloors, sourceWitness, hmem, -, hgap⟩ := hn
  have hgain : 0 < quittingTerminalSemanticDebtSum pair / 4 := by linarith
  have hgainLe : quittingTerminalSemanticDebtSum pair / 4 ≤
      quittingTerminalSemanticDebtSum pair / 2 := by linarith
  obtain ⟨source, hprofile, hobserver, hgainEq, hsource, hreceiving, halt⟩ :=
    fableFloorRepair_exists_exactPort_alternative_of_paidPair reward
      (fableFloorRepairEntranceProfile reward sigmas mover targets n) mover
      sourceWitness (targets n) (quittingTerminalSemanticDebtSum pair / 4)
      (quittingTerminalSemanticDebtSum pair / 2) hgain hgainLe hgap hfloors
      witness
  refine ⟨source, hprofile, hobserver, hgainEq, ?_, hreceiving, halt⟩
  rw [hsource]
  exact hmem

/-- **P4, lifted case split.**  The left arm of the production alternative is
profile-independent, so the whole case split can be made once: either the
quitting game already has a uniform-equilibrium payoff, or every late softened
entrance profile is the literal paid suffix of a marked exact orbit with a
summable all-Continue semantic port and positive paid-suffix reach.

The right arm names the marked orbit built from the profile-specific source, so
it stays inside the eventually-filter; only the disjunction itself is lifted. -/
theorem fableFloorRepair_exactPort_alternative_of_entrance
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (sigmas : ℕ → (quittingGame reward).BehaviorProfile)
    (mover : ι) (targets : ℕ → Option ℕ) (epsilons : ℕ → ℝ)
    (pair : QuittingTerminalSemanticPair ι)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum pair ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpositive : 0 < quittingTerminalSemanticDebtSum pair)
    (hnormal : ∀ who, quittingPunishmentValue reward who ≤
      reward (quittingSingletonTerminal who) who)
    (hmoverDebt : quittingTerminalSemanticDebt pair mover =
      quittingTerminalSemanticDebtSum pair)
    (hotherDebt : ∀ observer, observer ≠ mover →
      quittingTerminalSemanticDebt pair observer = 0)
    (hpayoff : ∀ observer, Tendsto (fun n =>
      quittingTerminalPayoff reward (sigmas n) observer) atTop
      (𝓝 (pair.1 observer)))
    (hcap : ∀ observer, Tendsto (fun n =>
      quittingContinuationBestResponseValue reward (sigmas n) observer) atTop
      (𝓝 (pair.2 observer)))
    (hepsilons : Tendsto epsilons atTop (𝓝 0))
    (htargets : ∀ n,
      quittingContinuationBestResponseValue reward (sigmas n) mover -
        epsilons n ≤
      quittingPureTimeDeviationPayoff reward (sigmas n) mover (targets n))
    (witness : QuittingTerminalExploitabilityWitness reward) :
    (∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) ∨
    ∀ᶠ n in atTop,
      ∃ source : QuittingPaidRowFloorSafeSource reward,
        source.profile =
          fableFloorRepairEntranceProfile reward sigmas mover targets n ∧
        source.observer = mover ∧
        source.gain = quittingTerminalSemanticDebtSum pair / 4 ∧
        source.row.sourceWitness ∈
          (quittingBehaviorStoppingLaw reward (sigmas n mover)).support ∧
        source.row.receivingWitness = targets n ∧
        ∃ marked : QuittingPaidRowMarkedExactOrbit source,
        ∃ port : QuittingPunishmentFloorInfiniteOrbit.SummableChargeAllContinuePort
            marked.orbit,
          Nonempty
              (QuittingPaidRowMarkedExactOrbit.SummableSemanticPort marked port) ∧
            Nonempty
              (QuittingPaidRowMarkedExactOrbit.PositivePaidSuffixReach marked) := by
  by_cases huniform : ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff
  · exact Or.inl huniform
  · refine Or.inr ?_
    filter_upwards [fableFloorRepair_eventually_exactPort_alternative reward
      sigmas mover targets epsilons pair hpair hminimum hpositive hnormal
      hmoverDebt hotherDebt hpayoff hcap hepsilons htargets witness] with n hn
    obtain ⟨source, hprofile, hobserver, hgainEq, hsource, hreceiving, marked,
      halt⟩ := hn
    rcases halt with hleft | hright
    · exact absurd hleft huniform
    · exact ⟨source, hprofile, hobserver, hgainEq, hsource, hreceiving, marked,
        hright⟩

end GameTheory
