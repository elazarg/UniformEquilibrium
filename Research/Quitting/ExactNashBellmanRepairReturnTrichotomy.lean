/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.ProbabilityMassFunction.Bool
import UniformEquilibrium.Quitting.Classification.AnalyticWaist
import UniformEquilibrium.Quitting.Classification.SingletonPacketEnergy
import UniformEquilibrium.Quitting.Classification.TerminalExploitabilityToggles
import UniformEquilibrium.Quitting.Root.TerminalSemanticPair
import UniformEquilibrium.Quitting.Cycles.ConditionedProductPurification

/-!
# Exact Nash--Bellman repair/return is a three-class problem

There are two different issues which are easy to conflate:

* producing an exact Nash--Bellman return; and
* forcing that return to preserve a previously marked sign or atom.

The first issue is already finite.  Apply analytic Bellman-germ existence to
the punishment-normalized auxiliary quitting table and translate the endpoint
back to the original reward.  This always gives a literal stationary
Nash--Bellman fixed point.  Its support has only the following strategic
outcomes:

1. it absorbs, in which case the auxiliary punishment normalization compiles
   it to an ordinary uniform-equilibrium payoff;
2. it is all-Continue and the cemetery branch compiles Never; or
3. it is all-Continue and exports the normalized singleton source packet.

Thus exact repair/return itself is not an unbounded chronological search.  In
a counterexample, only the third class can remain.  What is still nontrivial
is an *anchored* or sign-preserving selection of that exact return.
-/

noncomputable section

namespace GameTheory

open Filter Set Topology
open StochasticGame

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A literal period-one Nash--Bellman return for the original quitting
table.  No approximate equality and no externally supplied boundary occur in
this object. -/
structure QuittingExactStationaryNashBellmanReturn
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) where
  root : ι → PMF Bool
  value : Payoff ι
  fixed : value = quittingRootSuccessorPayoff reward value root
  nash : IsεQuittingRootNash reward value 0 root
  punishmentFloor : ∀ who, quittingPunishmentValue reward who ≤ value who

namespace QuittingExactStationaryNashBellmanReturn

variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- The return is genuinely absorbing exactly when its stationary joint
Continue mass is below one. -/
def Absorbs (repair : QuittingExactStationaryNashBellmanReturn reward) : Prop :=
  quittingStationaryContinueMass repair.root < 1

end QuittingExactStationaryNashBellmanReturn

/-- **Exact repair/return trichotomy.**  Every finite quitting table has one
exact stationary Nash--Bellman return which is either:

* absorbing and already compiled to a uniform payoff;
* the all-Continue return with Never already compiled; or
* the all-Continue return with one normalized singleton source packet.

The return and the payoff in the compiled branches are literally the same
translated analytic endpoint. -/
theorem exists_exactStationaryNashBellmanReturn_absorbing_or_never_or_packet
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    ∃ repair : QuittingExactStationaryNashBellmanReturn reward,
      (repair.Absorbs ∧
          (quittingGame reward).IsUniformEquilibriumPayoff none repair.value) ∨
        (repair.root = (quittingAllContinueRoot : ι → PMF Bool) ∧
          ((quittingGame reward).IsUniformEquilibriumPayoff none (0 : Payoff ι) ∨
            Nonempty (QuittingNormalizedSingletonSourcePacket reward))) := by
  obtain ⟨g⟩ :=
    nonempty_analyticBellmanGerm_quittingGame (quittingAuxiliaryReward reward)
  let root : ι → PMF Bool := g.endpointProfile none
  let shiftedValue := quittingGermValue g 0
  let value := quittingAuxiliaryTarget reward shiftedValue
  have hfixedShift := quittingGerm_endpoint_fixedPoint g
  have hfixed : value = quittingRootSuccessorPayoff reward value root := by
    exact quittingRootFixedPoint_unshift reward (quittingAuxiliaryLive reward)
      shiftedValue root hfixedShift
  have hnashShift := quittingGerm_endpoint_endpointNash g
  have hnashEndpoint : IsεQuittingRootEndpointNash reward value 0 root := by
    exact (isεQuittingRootEndpointNash_zero_shift_iff reward
      (quittingAuxiliaryLive reward) shiftedValue root).mp hnashShift
  have hnash : IsεQuittingRootNash reward value 0 root :=
    (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
      reward value root).mp hnashEndpoint
  let repair : QuittingExactStationaryNashBellmanReturn reward :=
    { root := root
      value := value
      fixed := hfixed
      nash := hnash
      punishmentFloor :=
        quittingPunishmentValue_le_auxiliaryEndpointTarget reward g }
  refine ⟨repair, ?_⟩
  by_cases habsorbs : quittingStationaryContinueMass root < 1
  · exact Or.inl ⟨habsorbs,
      isUniformEquilibriumPayoff_of_auxiliaryGerm_absorbingEndpoint
        reward g habsorbs⟩
  · have hcontinue : quittingStationaryContinueMass root = 1 := by
      apply le_antisymm
      · exact quittingStationaryContinueMass_le_one root
      · exact not_lt.mp habsorbs
    have hroot : root = (quittingAllContinueRoot : ι → PMF Bool) :=
      quittingRoot_eq_allContinue_of_continueMass_eq_one root hcontinue
    refine Or.inr ⟨hroot, ?_⟩
    rcases quittingAuxiliaryGerm_allContinueAlternative reward g hcontinue with
      hnever | hpacket
    · exact Or.inl hnever.2
    · exact Or.inr hpacket

/-- In a genuine counterexample the exact-return search collapses to the
single all-Continue/packet class.  In particular, neither an absorbing return
nor the cemetery/Never class can survive. -/
theorem exists_exactAllContinueReturn_and_packet_of_no_uniformPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hnot : ¬ ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) :
    ∃ repair : QuittingExactStationaryNashBellmanReturn reward,
      repair.root = (quittingAllContinueRoot : ι → PMF Bool) ∧
        Nonempty (QuittingNormalizedSingletonSourcePacket reward) := by
  obtain ⟨repair, habsorbing | hall⟩ :=
    exists_exactStationaryNashBellmanReturn_absorbing_or_never_or_packet reward
  · exact False.elim (hnot ⟨repair.value, habsorbing.2⟩)
  · rcases hall with ⟨hroot, hnever | hpacket⟩
    · exact False.elim (hnot ⟨0, hnever⟩)
    · exact ⟨repair, hroot, hpacket⟩

/-- **Packet target retained at the exact all-Continue return.**

The all-Continue auxiliary classification above exports a normalized packet,
but its existential interface forgets that the packet was built from the same
analytic endpoint as the stationary return.  Repeating that final
classification step without erasing the construction retains the exact
equality `packet.target = repair.value`.

This is a coupling theorem, not a source-return theorem for the stopping-law
frontier: neither `repair` nor `packet` is identified with a frontier base,
reset source, target profile, marked row, or retained terminal law. -/
theorem exists_exactAllContinueReturn_and_targetMatchedPacket_of_no_uniformPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hnot : ¬ ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) :
    ∃ (repair : QuittingExactStationaryNashBellmanReturn reward)
        (packet : QuittingNormalizedSingletonSourcePacket reward),
      repair.root = (quittingAllContinueRoot : ι → PMF Bool) ∧
      packet.target = repair.value := by
  obtain ⟨g⟩ :=
    nonempty_analyticBellmanGerm_quittingGame (quittingAuxiliaryReward reward)
  let root : ι → PMF Bool := g.endpointProfile none
  let shiftedValue := quittingGermValue g 0
  let value := quittingAuxiliaryTarget reward shiftedValue
  have hfixedShift := quittingGerm_endpoint_fixedPoint g
  have hfixed : value = quittingRootSuccessorPayoff reward value root := by
    exact quittingRootFixedPoint_unshift reward (quittingAuxiliaryLive reward)
      shiftedValue root hfixedShift
  have hnashShift := quittingGerm_endpoint_endpointNash g
  have hnashEndpoint : IsεQuittingRootEndpointNash reward value 0 root := by
    exact (isεQuittingRootEndpointNash_zero_shift_iff reward
      (quittingAuxiliaryLive reward) shiftedValue root).mp hnashShift
  have hnash : IsεQuittingRootNash reward value 0 root :=
    (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
      reward value root).mp hnashEndpoint
  let repair : QuittingExactStationaryNashBellmanReturn reward :=
    { root := root
      value := value
      fixed := hfixed
      nash := hnash
      punishmentFloor :=
        quittingPunishmentValue_le_auxiliaryEndpointTarget reward g }
  by_cases habsorbs : quittingStationaryContinueMass root < 1
  · exact False.elim (hnot ⟨value,
      isUniformEquilibriumPayoff_of_auxiliaryGerm_absorbingEndpoint
        reward g habsorbs⟩)
  · have hcontinue : quittingStationaryContinueMass root = 1 := by
      apply le_antisymm
      · exact quittingStationaryContinueMass_le_one root
      · exact not_lt.mp habsorbs
    have hroot : repair.root =
        (quittingAllContinueRoot : ι → PMF Bool) :=
      quittingRoot_eq_allContinue_of_continueMass_eq_one root hcontinue
    classical
    let auxiliary := quittingAuxiliaryReward reward
    by_cases hzeroAux : IsQuittingZeroSolo auxiliary
    · have hzero : IsQuittingZeroSolo reward :=
        isQuittingZeroSolo_of_auxiliaryReward_zeroSolo reward hzeroAux
      exact False.elim (hnot ⟨0,
        quittingGame_isUniformEquilibriumPayoff_zero_of_zeroSolo reward hzero⟩)
    · obtain ⟨m, leading, horder, hleadingNonneg, hleadingSumPos, hsupport,
        htotal, hshare, hsmall, hmatchingLimit, hbig⟩ :=
          quittingGermLeadingOrderNormalization_of_not_isQuittingZeroSolo
            g hzeroAux
      have hm : 1 ≤ m :=
        one_le_quittingGerm_leadingOrder_of_endpoint_allContinue
          g hcontinue horder
      have hne : ∃ owner,
          ¬∀ᶠ t in 𝓝[>] (0 : ℝ), quittingGermQuitRate g owner t = 0 :=
        exists_not_eventually_quittingGermQuitRate_eq_zero_of_not_isQuittingZeroSolo
          g hzeroAux
      rcases lt_trichotomy g.ramification m with hslow | hmatching | hfast
      · have habsorption :
            ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < quittingGermAbsorption g t :=
          eventually_quittingGermAbsorption_pos g htotal
        have hdominates : Tendsto
            (fun t : ℝ => t ^ g.ramification / quittingGermAbsorption g t)
            (𝓝[>] (0 : ℝ)) atTop :=
          tendsto_pow_div_quittingGermAbsorption_atTop
            g htotal (hbig hslow)
        have hvalueZero :=
          quittingGermValue_zero_eq_zero_of_discount_dominates
            g habsorption hdominates
        have hzero : IsQuittingZeroSolo reward := by
          intro who
          have hsolo :=
            quittingGerm_solo_le_endpointValue_of_endpoint_allContinue
              g hcontinue who
          have hvalueWho := congrFun hvalueZero who
          have hlive := quittingAuxiliaryLive_nonpos reward who
          change reward (quittingSingletonTerminal who) who -
              quittingAuxiliaryLive reward who ≤ quittingGermValue g 0 who
            at hsolo
          simp only [Pi.zero_apply] at hvalueWho
          rw [hvalueWho] at hsolo
          linarith
        exact False.elim (hnot ⟨0,
          quittingGame_isUniformEquilibriumPayoff_zero_of_zeroSolo reward hzero⟩)
      · have hmatchingOrder :
            Math.familyAnalyticOrder (quittingGermQuitRate g) =
              g.ramification := by
          rw [horder]
          exact_mod_cast hmatching.symm
        obtain ⟨matchingData⟩ :=
          exists_quittingGermMatchingLeadingData auxiliary g hne hmatchingOrder
        let projective := matchingData.toProjectiveSingletonPacket
        have hcemetery : projective.cemetery < 1 := by
          change 1 / (1 + ∑ owner, matchingData.leading owner) < 1
          rw [div_lt_iff₀ (by linarith [matchingData.leading_sum_pos])]
          linarith [matchingData.leading_sum_pos]
        let packet :=
          normalizedSingletonSourcePacket_of_auxiliaryProjectivePacket
            reward g projective rfl hcemetery
              (quittingAuxiliaryGermEndpointValue_nonneg reward g)
        exact ⟨repair, packet, hroot, rfl⟩
      · let hfastData : QuittingGermFastLeadingData auxiliary g :=
          { leading := leading
            leading_nonneg := hleadingNonneg
            leading_sum_pos := hleadingSumPos
            eventually_total_pos := htotal
            share_tendsto := hshare
            total_div_absorption_tendsto :=
              tendsto_sum_div_quittingGermAbsorption g hm horder htotal
            discount_div_absorption_tendsto :=
              tendsto_pow_div_quittingGermAbsorption_nhds_zero
                g htotal (hsmall hfast)
            quitRate_tendsto_zero := fun owner =>
              quittingGermQuitRate_tendsto_zero_of_endpoint_allContinue
                g hcontinue owner }
        let projective := hfastData.toProjectiveSingletonPacket hcontinue
        let packet :=
          normalizedSingletonSourcePacket_of_auxiliaryProjectivePacket
            reward g projective rfl (by simp [projective,
              QuittingGermFastLeadingData.toProjectiveSingletonPacket])
              (quittingAuxiliaryGermEndpointValue_nonneg reward g)
        exact ⟨repair, packet, hroot, rfl⟩

/-- A counterexample admits no nontrivial period-one exact return at a
punishment-floor-admissible value.  Any such absorbing fixed root is already
a solved exact cycle.  Consequently every exact stationary return of this
kind is literally all-Continue. -/
theorem QuittingExactStationaryNashBellmanReturn.root_eq_allContinue_of_no_uniformPayoff
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (repair : QuittingExactStationaryNashBellmanReturn reward)
    (hnot : ¬ ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) :
    repair.root = (quittingAllContinueRoot : ι → PMF Bool) := by
  by_cases habsorbs : quittingStationaryContinueMass repair.root < 1
  · have huniform : (quittingGame reward).IsUniformEquilibriumPayoff none
        repair.value := by
      let cycle : Fin 1 → ι → PMF Bool := fun _ => repair.root
      let value : Fin 1 → Payoff ι := fun _ => repair.value
      apply isUniformEquilibriumPayoff_of_punishmentAdmissibleCycle
        reward cycle value 0
      · intro phase
        simpa [cycle, value, finRotate] using repair.fixed
      · intro phase
        simpa [cycle, value, finRotate] using repair.nash
      · simpa [cycle] using habsorbs
      · intro who
        by_cases hcontract :
            quittingStationaryFixedOpponentsContinueMass repair.root who < 1
        · exact Or.inl (by simpa [cycle] using hcontract)
        · right
          have hmassLe :=
            quittingStationaryFixedOpponentsContinueMass_le_one
              repair.root who
          have hmass :
              quittingStationaryFixedOpponentsContinueMass repair.root who = 1 :=
            le_antisymm hmassLe (not_lt.mp hcontract)
          have hopponents :=
            opponents_pure_continue_of_fixedOpponentsContinueMass_eq_one
              repair.root who hmass
          have hrootQuit : 0 < ((repair.root who) true).toReal := by
            by_contra hnotQuit
            have hzero : ((repair.root who) true).toReal = 0 :=
              le_antisymm (not_lt.mp hnotQuit) ENNReal.toReal_nonneg
            have hall : repair.root =
                (quittingAllContinueRoot : ι → PMF Bool) := by
              funext player
              by_cases hp : player = who
              · subst player
                exact
                  Math.ProbabilityMassFunction.eq_pure_false_of_apply_true_toReal_eq_zero
                    _ hzero
              · exact hopponents player hp
            rw [hall, quittingStationaryContinueMass_eq_prod] at habsorbs
            simp [quittingAllContinueRoot] at habsorbs
          have hsolo : repair.value who =
              reward (quittingSingletonTerminal who) who := by
            have hquitEq :=
              quittingRootQuitPayoff_eq_stationaryFixedOpponentsQuitValue'
                reward repair.value repair.root who
            have hcontEq :=
              quittingRootContinuePayoff_eq_stationaryFixedOpponents'
                reward repair.value repair.root who
            have hH :=
              quittingStationaryFixedOpponentsContinueReward_eq_zero_of_mass_eq_one
                reward hmass
            have hS :
                quittingStationaryFixedOpponentsQuitValue reward repair.root who =
                  reward (quittingSingletonTerminal who) who :=
              quittingStationaryFixedOpponentsQuitValue_eq_solo_of_mass_eq_one
                reward repair.root who hmass
            have htargetFixed := congrFun repair.fixed who
            rw [quittingRootSuccessorPayoff_eq_endpointMix] at htargetFixed
            rw [hquitEq, hcontEq, hH, hmass, hS] at htargetFixed
            simp only [zero_add, one_mul] at htargetFixed
            have hsum :=
              quittingRoot_continueProbability_add_quitProbability
                repair.root who
            have hq : ((repair.root who) true).toReal =
                1 - ((repair.root who) false).toReal := by
              linarith
            have hproduct : ((repair.root who) true).toReal *
                (repair.value who -
                  reward (quittingSingletonTerminal who) who) = 0 := by
              calc
                ((repair.root who) true).toReal *
                      (repair.value who -
                        reward (quittingSingletonTerminal who) who) =
                    (1 - ((repair.root who) false).toReal) *
                      (repair.value who -
                        reward (quittingSingletonTerminal who) who) := by
                          rw [hq]
                _ = repair.value who -
                    ((1 - ((repair.root who) false).toReal) *
                        reward (quittingSingletonTerminal who) who +
                      ((repair.root who) false).toReal * repair.value who) := by
                        ring
                _ = repair.value who -
                    (((repair.root who) true).toReal *
                        reward (quittingSingletonTerminal who) who +
                      ((repair.root who) false).toReal * repair.value who) := by
                        rw [← hq]
                _ = 0 := by rw [← htargetFixed]; ring
            have hdiff :=
              (mul_eq_zero.mp hproduct).resolve_left hrootQuit.ne'
            linarith
          rw [← hsolo]
          exact repair.punishmentFloor who
    exact False.elim (hnot ⟨repair.value, huniform⟩)
  · have hcontinue : quittingStationaryContinueMass repair.root = 1 := by
      apply le_antisymm
      · exact quittingStationaryContinueMass_le_one repair.root
      · exact not_lt.mp habsorbs
    exact quittingRoot_eq_allContinue_of_continueMass_eq_one
      repair.root hcontinue

/-! ## The residual packet has a finite oriented sign -/

/-- In a counterexample, the normalized singleton packet has strictly
positive weighted surplus.  Equality would pin every positive-mass owner to
the delivered singleton mixture, which is exactly the input of the existing
finite face-circulation compiler. -/
theorem QuittingNormalizedSingletonSourcePacket.weightedSurplus_pos_of_no_uniformPayoff
    [Nonempty ι]
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (packet : QuittingNormalizedSingletonSourcePacket reward)
    (hnot : ¬ ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) :
    0 < quittingPacketWeightedSurplus packet := by
  have hnonneg := quittingPacketWeightedSurplus_nonneg packet
  apply lt_of_le_of_ne hnonneg
  intro hzero
  have hzero' : quittingPacketWeightedSurplus packet = 0 := hzero.symm
  have hactive : ∀ owner, 0 < packet.mass owner →
      quittingSingletonMixture reward packet.mass owner =
        reward (quittingSingletonTerminal owner) owner := by
    intro owner howner
    have hterm : packet.mass owner *
        (quittingSingletonMixture reward packet.mass owner -
          packet.target owner) = 0 := by
      apply (Finset.sum_eq_zero_iff_of_nonneg
        (fun who _ => packet.mass_mul_surplus_nonneg who)).1
      · exact hzero'
      · exact Finset.mem_univ owner
    have hmixTarget :
        quittingSingletonMixture reward packet.mass owner =
          packet.target owner := by
      rcases mul_eq_zero.mp hterm with hmassZero | hgap
      · exact (howner.ne' hmassZero).elim
      · linarith
    rw [hmixTarget, packet.positive_mass_pins_target owner howner]
  exact hnot (exists_uniformEquilibriumPayoff_of_complementarySingletonMixture
    reward packet.mass packet.target packet.mass_nonneg packet.mass_sum
      packet.mix_ge_target hactive packet.solo_le_target
      packet.punishment_le_target)

/-- **Coupling of exact return and finite packet sign.**

If a finite quitting game has no ordinary uniform-equilibrium payoff, then
one finite certificate simultaneously contains:

* a literal exact stationary Nash--Bellman return;
* proof that its root is exactly all-Continue;
* the normalized singleton packet exported at that same analytic endpoint;
* two distinct positive-mass packet owners; and
* a strictly positive reciprocal singleton-delivery effect between them.

The infinite chronological repair problem has therefore disappeared from
this interface.  The remaining obligation is precisely the finite
packet-to-same-row-strategy decoder for a supported positive reciprocal pair;
the theorem does not relabel a delivery comparison as a unilateral gain. -/
theorem exists_exactAllContinueReturn_packet_supportedPositiveReciprocalPair
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hnot : ¬ ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) :
    ∃ (repair : QuittingExactStationaryNashBellmanReturn reward)
        (packet : QuittingNormalizedSingletonSourcePacket reward)
        (who owner : ι),
      repair.root = (quittingAllContinueRoot : ι → PMF Bool) ∧
      0 < packet.mass who ∧
      0 < packet.mass owner ∧
      who ≠ owner ∧
      0 < quittingSingletonSoloEffect reward who owner +
        quittingSingletonSoloEffect reward owner who := by
  obtain ⟨repair, hroot, ⟨packet⟩⟩ :=
    exists_exactAllContinueReturn_and_packet_of_no_uniformPayoff reward hnot
  have hsurplus := packet.weightedSurplus_pos_of_no_uniformPayoff hnot
  have henergy :
      0 < quittingSingletonPacketQuadraticEnergy reward packet.mass := by
    rwa [← quittingPacketWeightedSurplus_eq_quadraticForm packet]
  obtain ⟨who, owner, hwho, howner, hne, hpair⟩ :=
    exists_supported_pair_pos_reciprocalSoloEffect_of_energy_pos
      reward packet.mass packet.mass_nonneg henergy
  exact ⟨repair, packet, who, owner, hroot, hwho, howner, hne, hpair⟩

/-- Oriented form of the coupled certificate: one of the two reciprocal
singleton *delivery* effects is itself strictly positive, and both endpoint
labels have positive mass in the exact-return packet.

This is deliberately not called a strategic source gain: at a singleton
source row, a receiver's Quit deviation creates a collision payoff, whereas
`quittingSingletonSoloEffect` compares two different singleton deliveries.
The conversion to a same-row collision sign is a separate obligation. -/
theorem exists_exactAllContinueReturn_packet_orientedSingletonEffect
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hnot : ¬ ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) :
    ∃ (repair : QuittingExactStationaryNashBellmanReturn reward)
        (packet : QuittingNormalizedSingletonSourcePacket reward)
        (receiver source : ι),
      repair.root = (quittingAllContinueRoot : ι → PMF Bool) ∧
      0 < packet.mass receiver ∧
      0 < packet.mass source ∧
      receiver ≠ source ∧
      0 < quittingSingletonSoloEffect reward receiver source := by
  obtain ⟨repair, packet, who, owner, hroot, hwho, howner, hne, hpair⟩ :=
    exists_exactAllContinueReturn_packet_supportedPositiveReciprocalPair
      reward hnot
  by_cases horiented :
      0 < quittingSingletonSoloEffect reward who owner
  · exact ⟨repair, packet, who, owner, hroot, hwho, howner, hne,
      horiented⟩
  · have hreverse :
        0 < quittingSingletonSoloEffect reward owner who := by
      linarith
    exact ⟨repair, packet, owner, who, hroot, howner, hwho, hne.symm,
      hreverse⟩

/-! ## A literal strategic sign attached to the exact return value -/

/-- **A collision-face strategic sign at the exact return tail.**

In a counterexample, take the exact all-Continue Nash--Bellman return selected
above.  Counterexample instability first selects an owner with positive solo
reward and then a distinct receiver with a positive collision-insertion
gain.  Because all-Continue is exactly Nash at the returned value, the
receiver's own singleton payoff is below that same value.  There is therefore
an explicit owner Quit rate in `[1/2,1]` for which the receiver's literal
Quit-minus-Continue endpoint difference is exactly half the collision gain.

Unlike the packet delivery effect above, this is a unilateral strategic sign:
both endpoints are evaluated at one product root and against the exact
Nash--Bellman return value.  The product root is a newly constructed
solo-owner face; it is not the all-Continue return root and is not identified
with a stopping-law frontier source or target. -/
theorem exists_exactAllContinueReturn_targetMatchedPacket_collisionFaceSign
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hnot : ¬ ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) :
    ∃ (repair : QuittingExactStationaryNashBellmanReturn reward)
        (packet : QuittingNormalizedSingletonSourcePacket reward)
        (owner receiver : ι) (rate gain : ℝ)
        (hrate0 : 0 ≤ rate) (hrate1 : rate ≤ 1),
      repair.root = (quittingAllContinueRoot : ι → PMF Bool) ∧
      packet.target = repair.value ∧
      0 < quittingPacketWeightedSurplus packet ∧
      receiver ≠ owner ∧
      1 / 2 ≤ rate ∧
      0 < gain ∧
      gain = quittingSingletonCollisionReward reward owner receiver -
        quittingSoloReward reward owner receiver ∧
      quittingRootEndpointDifference reward repair.value
          (quittingSoloStationaryRoot owner
            (quittingHazardCoin rate hrate0 hrate1)) receiver = gain / 2 := by
  let witness := quittingTerminalExploitabilityWitnessOfNoUniformPayoff reward hnot
  obtain ⟨repair, packet, hroot, htarget⟩ :=
    exists_exactAllContinueReturn_and_targetMatchedPacket_of_no_uniformPayoff
      reward hnot
  have hpacketSurplus := packet.weightedSurplus_pos_of_no_uniformPayoff hnot
  obtain ⟨owner, hownerSolo⟩ := witness.exists_terminalGap_le_soloReward
  have hownerViable : -witness.terminalGap <
      quittingSoloReward reward owner owner := by
    linarith [witness.terminalGap_pos]
  obtain ⟨receiver, hne, hinsertion⟩ :=
    witness.exists_collision_gain hownerViable
  let gain := quittingSingletonCollisionReward reward owner receiver -
    quittingSoloReward reward owner receiver
  let slack := repair.value receiver -
    quittingSoloReward reward receiver receiver
  have hnashAll : IsεQuittingRootNash reward repair.value 0
      (quittingAllContinueRoot : ι → PMF Bool) := by
    rw [← hroot]
    exact repair.nash
  have hslackNonneg : 0 ≤ slack := by
    dsimp only [slack]
    have hsingleton :=
      (isZeroQuittingRootNash_allContinue_iff_singleton_le
        reward repair.value).1 hnashAll receiver
    simpa [quittingSoloReward, quittingSingletonTerminal] using
      sub_nonneg.mpr hsingleton
  have hgainLower : witness.terminalGap ≤ gain := by
    dsimp only [gain]
    linarith
  have hgainPos : 0 < gain := witness.terminalGap_pos.trans_le hgainLower
  let rate := (slack + gain / 2) / (slack + gain)
  have hden : 0 < slack + gain :=
    add_pos_of_nonneg_of_pos hslackNonneg hgainPos
  have hrate0 : 0 ≤ rate := by
    dsimp only [rate]
    positivity
  have hrate1 : rate ≤ 1 := by
    dsimp only [rate]
    apply (div_le_one hden).2
    linarith
  have hrateHalf : 1 / 2 ≤ rate := by
    dsimp only [rate]
    apply (le_div_iff₀ hden).2
    nlinarith
  refine ⟨repair, packet, owner, receiver, rate, gain, hrate0, hrate1,
    hroot, htarget, hpacketSurplus, hne, hrateHalf, hgainPos, rfl, ?_⟩
  rw [quittingRootEndpointDifference_conditionedSolo_other reward hne]
  have hslackEq : quittingSoloReward reward receiver receiver -
      repair.value receiver = -slack := by
    dsimp only [slack]
    ring
  have hgainEq : quittingSingletonCollisionReward reward owner receiver -
      quittingSoloReward reward owner receiver = gain := rfl
  rw [hslackEq, hgainEq]
  dsimp only [rate]
  field_simp [hden.ne']
  ring

end GameTheory
