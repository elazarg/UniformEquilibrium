/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Research.Quitting.FinFourProducerAtlas.FullBindingPointwiseSupportBallistic
import Research.Quitting.FinFourProducerAtlas.StrictRayBindingCardinalityExplicit
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticResetIncidenceReturn

/-!
# A positive limiting root returns the strict Fin4 maximal ray

The compact joint-law point in this file is selected again from the actual
maximal-ray profiles.  Its cap is proved equal to the `capLimit` stored in the
same forward flow by uniqueness of limits; it is not identified with the
older retained law without proof.

A positive-absorption exact root at that cap prefixes the selected joint law.
The returned debt is exactly `L - L * absorption`, so it lies in `[D_*, L)`.
Equality with `D_*` creates a fresh minimum-law causal atom and producer for
the same hard residual.  Strict inequality retains only an off-minimum descent
object.  No branch asserts a quantitative return rate, renewable rank drop, or
uniform-equilibrium consumer.
-/

noncomputable section

namespace GameTheory

open Filter Math Math.Probability Set

variable {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
variable {bound : ℝ}
variable {source : FinFourMinimumAtomProducer reward bound}
variable {returnSource :
  FinFourOwnerCompressedMinimumReturnForcedPairSource source}
variable {lambda : ℝ}

namespace FinFourOwnerCompressedMinimumReturnForcedPairPacket

variable {packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
  returnSource lambda}
variable {flow : FinFourStrictRayForwardExactCapTail packet}

/-- The executable joint semantic/law point at one date of this exact ray. -/
def strictRayLawPoint
    (_flow : FinFourStrictRayForwardExactCapTail packet) (time : ℕ) :
    QuittingTerminalSemanticLawPoint (Fin 4) :=
  quittingMaximalCapSemanticPrefixLawPoint reward packet.raySource
    (packet.rayBaseProfile 0) time

/-- The semantic coordinate of the executable law point is the semantic point
stored by the same forward ray. -/
theorem strictRayLawPoint_pair_eq
    (flow : FinFourStrictRayForwardExactCapTail packet) (time : ℕ) :
    (strictRayLawPoint flow time).1 = flow.forward.pair time := by
  rw [flow.pair_apply]
  exact quittingTerminalSemanticPair_maximalCapSemanticPrefixProfile_eq
    reward packet.raySource (packet.rayBaseProfile 0)
      (packet.rayBaseProfile_semantic_eq 0) time

/-- A compact joint-law limit selected from the actual forward ray, with its
cap coordinate pinned literally to the forward flow's `capLimit`. -/
structure FinFourStrictRayCapLimitJointLaw
    (flow : FinFourStrictRayForwardExactCapTail packet) where
  point : QuittingTerminalSemanticLawPoint (Fin 4)
  point_mem : point ∈ quittingTerminalSemanticLawCarrier reward
  subsequence : ℕ → ℕ
  subsequence_strictMono : StrictMono subsequence
  point_tendsto : Tendsto
    (fun rank ↦ strictRayLawPoint flow (subsequence rank)) atTop (nhds point)
  cap_eq : point.1.2 = flow.forward.capLimit
  debt_eq_limit : quittingTerminalSemanticDebtSum point.1 =
    quittingMaximalCapSemanticPrefixDebtLimit reward packet.raySource
  retained_atom_pos : 0 < point.2 (some packet.rayTerminal)

namespace FinFourStrictRayCapLimitJointLaw

/-- Compactness of the joint law carrier constructs a cap-pinned limit from
the same executable profiles as `flow`. -/
theorem nonempty
    (flow : FinFourStrictRayForwardExactCapTail packet) :
    Nonempty (FinFourStrictRayCapLimitJointLaw flow) := by
  have hmem : ∀ time, strictRayLawPoint flow time ∈
      quittingTerminalSemanticLawCarrier reward := by
    intro time
    exact quittingTerminalSemanticLawPoint_mem_carrier reward
      (quittingMaximalCapSemanticPrefixProfile reward packet.raySource
        (packet.rayBaseProfile 0) time)
  obtain ⟨point, hpoint, subsequence, hsubsequence, hpointLimit⟩ :=
    (quittingTerminalSemanticLawCarrier_isCompact reward).tendsto_subseq hmem
  have hfacts := quittingMaximalCapSemanticPrefixLawPoint_cluster_facts
    reward source.point.1 packet.raySource (packet.rayBaseProfile 0)
      (packet.rayBaseProfile_semantic_eq 0) 0 packet.rayTerminal
      source.minimum source.minimumDebt_pos packet.raySource_mem (by
        rw [packet.rayBaseProfile_stageMass_eq_one]
        norm_num) point subsequence hsubsequence (by
          simpa only [strictRayLawPoint, Function.comp_def] using hpointLimit)
  have hcap : point.1.2 = flow.forward.capLimit := by
    funext who
    have hpointCap : Tendsto
        (fun rank ↦ (strictRayLawPoint flow (subsequence rank)).1.2 who)
        atTop (nhds (point.1.2 who)) :=
      (((continuous_apply who).comp continuous_snd).comp
        continuous_fst).continuousAt.tendsto.comp
          hpointLimit
    have hflowCap : Tendsto
        (fun rank ↦ (flow.forward.pair (subsequence rank)).2 who)
        atTop (nhds (flow.forward.capLimit who)) :=
      (flow.forward.cap_tendsto who).comp hsubsequence.tendsto_atTop
    have hsame : (fun rank ↦
        (strictRayLawPoint flow (subsequence rank)).1.2 who) =
        fun rank ↦ (flow.forward.pair (subsequence rank)).2 who := by
      funext rank
      rw [strictRayLawPoint_pair_eq]
    rw [hsame] at hpointCap
    exact tendsto_nhds_unique hpointCap hflowCap
  exact ⟨{
    point := point
    point_mem := hpoint
    subsequence := subsequence
    subsequence_strictMono := hsubsequence
    point_tendsto := by
      simpa only [Function.comp_def] using hpointLimit
    cap_eq := hcap
    debt_eq_limit := hfacts.2.1
    retained_atom_pos := hfacts.2.2.2.1
  }⟩

end FinFourStrictRayCapLimitJointLaw

/-- A positive exact limiting root attached to one actual cap-limit joint-law
cluster of the same strict ray. -/
structure FinFourStrictRayPositiveRootReturn
    (flow : FinFourStrictRayForwardExactCapTail packet) where
  limitLaw : FinFourStrictRayCapLimitJointLaw flow
  root : Fin 4 → PMF Bool
  exactNash : IsεQuittingRootNash reward limitLaw.point.1.2 0 root
  absorption_pos : 0 < quittingRootAbsorptionMass root

namespace FinFourStrictRayPositiveRootReturn

/-- Prefix the selected cap-limit law by the attached positive exact root. -/
def returnedPoint
    (result : FinFourStrictRayPositiveRootReturn flow) :
    QuittingTerminalSemanticLawPoint (Fin 4) :=
  (quittingTerminalSemanticPrefix reward result.root result.limitLaw.point.1,
    quittingTerminalOutcomeLawPrefix result.root result.limitLaw.point.2)

/-- The returned joint point remains in the actual joint-law carrier. -/
theorem returnedPoint_mem
    (result : FinFourStrictRayPositiveRootReturn flow) :
    result.returnedPoint ∈ quittingTerminalSemanticLawCarrier reward :=
  quittingTerminalSemanticLawPrefix_mem_carrier reward result.root
    result.limitLaw.point result.limitLaw.point_mem

/-- The positive-root return obeys the exact oriented debt account. -/
theorem returnedDebt_eq_limit_sub_charge
    (result : FinFourStrictRayPositiveRootReturn flow) :
    quittingTerminalSemanticDebtSum result.returnedPoint.1 =
      quittingMaximalCapSemanticPrefixDebtLimit reward packet.raySource -
        quittingMaximalCapSemanticPrefixDebtLimit reward packet.raySource *
          quittingRootAbsorptionMass result.root := by
  have haccount := capNashPrefix_tailEscape_exact_account
    (reward := reward) source.point.1 result.limitLaw.point.1 result.root
      source.minimum
      (terminalSemanticLawCarrier_fst_mem_carrier
        result.limitLaw.point result.limitLaw.point_mem)
      result.exactNash
  simpa only [returnedPoint, result.limitLaw.debt_eq_limit] using
    haccount.2.2.1

/-- The returned debt is still bounded below by the global minimum. -/
theorem minimumDebt_le_returnedDebt
    (result : FinFourStrictRayPositiveRootReturn flow) :
    quittingTerminalSemanticDebtSum source.point.1 ≤
      quittingTerminalSemanticDebtSum result.returnedPoint.1 := by
  exact source.minimum result.returnedPoint.1
    (terminalSemanticLawCarrier_fst_mem_carrier
      result.returnedPoint result.returnedPoint_mem)

/-- Positive absorption makes the return strictly cheaper than the retained
strict-ray law limit. -/
theorem returnedDebt_lt_limit
    (result : FinFourStrictRayPositiveRootReturn flow) :
    quittingTerminalSemanticDebtSum result.returnedPoint.1 <
      quittingMaximalCapSemanticPrefixDebtLimit reward packet.raySource := by
  rw [result.returnedDebt_eq_limit_sub_charge]
  have hlimitPos : 0 <
      quittingMaximalCapSemanticPrefixDebtLimit reward packet.raySource :=
    source.minimumDebt_pos.trans
      flow.strict.stall.strict
  nlinarith [mul_pos hlimitPos result.absorption_pos]

/-- Attach any supplied positive exact root at the literal forward cap.  The
joint-law compactification is constructed internally from the same ray. -/
theorem nonempty_of_root_at_capLimit
    (flow : FinFourStrictRayForwardExactCapTail packet)
    (root : Fin 4 → PMF Bool)
    (hnash : IsεQuittingRootNash reward flow.forward.capLimit 0 root)
    (hpositive : 0 < quittingRootAbsorptionMass root) :
    Nonempty (FinFourStrictRayPositiveRootReturn flow) := by
  obtain ⟨limitLaw⟩ := FinFourStrictRayCapLimitJointLaw.nonempty flow
  exact ⟨{
    limitLaw := limitLaw
    root := root
    exactNash := by rw [limitLaw.cap_eq]; exact hnash
    absorption_pos := hpositive
  }⟩

end FinFourStrictRayPositiveRootReturn

/-- Equality in the returned interval creates a fresh source at the returned
joint law while preserving the hard residual literally. -/
structure FinFourStrictRayMinimumLawHandoff
    (result : FinFourStrictRayPositiveRootReturn flow) where
  debt_eq_minimum : quittingTerminalSemanticDebtSum result.returnedPoint.1 =
    quittingTerminalSemanticDebtSum source.point.1
  fresh : FinFourMinimumAtomProducer reward bound
  residual_eq : fresh.residual = source.residual
  point_eq : fresh.point = result.returnedPoint

/-- The complementary branch is a strict off-minimum descent inside the same
interval.  It carries no recursive or quantitative consumer. -/
structure FinFourStrictRayOffMinimumDescent
    (result : FinFourStrictRayPositiveRootReturn flow) where
  minimum_lt : quittingTerminalSemanticDebtSum source.point.1 <
    quittingTerminalSemanticDebtSum result.returnedPoint.1
  returned_lt_limit : quittingTerminalSemanticDebtSum result.returnedPoint.1 <
    quittingMaximalCapSemanticPrefixDebtLimit reward packet.raySource

namespace FinFourStrictRayPositiveRootReturn

/-- Exact equality/strict classification of one positive limiting-root
return.  The equality branch causalizes the returned law point and packages a
fresh `FinFourMinimumAtomProducer` for the same residual. -/
theorem nonempty_minimumLawHandoff_or_offMinimumDescent
    (result : FinFourStrictRayPositiveRootReturn flow) :
    Nonempty (FinFourStrictRayMinimumLawHandoff result) ∨
      Nonempty (FinFourStrictRayOffMinimumDescent result) := by
  rcases (result.minimumDebt_le_returnedDebt).eq_or_lt with heq | hstrict
  · left
    have heq' : quittingTerminalSemanticDebtSum result.returnedPoint.1 =
        quittingTerminalSemanticDebtSum source.point.1 := heq.symm
    have hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
        quittingTerminalSemanticDebtSum result.returnedPoint.1 ≤
          quittingTerminalSemanticDebtSum candidate := by
      intro candidate hcandidate
      rw [heq']
      exact source.minimum candidate hcandidate
    obtain ⟨atom⟩ := finFourHardResidual_minimumLaw_causalSuffixAtom
      reward bound source.residual result.returnedPoint result.returnedPoint_mem
        hminimum
    let fresh : FinFourMinimumAtomProducer reward bound := {
      residual := source.residual
      point := result.returnedPoint
      point_mem := result.returnedPoint_mem
      semantic_mem := terminalSemanticLawCarrier_fst_mem_carrier
        result.returnedPoint result.returnedPoint_mem
      minimum := hminimum
      inf_pos := source.inf_pos
      debt_eq_inf := heq'.trans source.debt_eq_inf
      atom := atom
    }
    exact ⟨{
      debt_eq_minimum := heq'
      fresh := fresh
      residual_eq := rfl
      point_eq := rfl
    }⟩
  · right
    exact ⟨{
      minimum_lt := hstrict
      returned_lt_limit := result.returnedDebt_lt_limit
    }⟩

end FinFourStrictRayPositiveRootReturn

/-- Certificate-free source capstone.  The actual strict ray either exposes a
positive exact root and hence a fresh minimum/descent return, or remains
ballistic, omits a current player infinitely often, or has a cardinal-three
binding face. -/
theorem minimumLawHandoff_or_offMinimumDescent_or_ballistic_or_omitted_or_cardThree
    (flow : FinFourStrictRayForwardExactCapTail packet) :
    (∃ result : FinFourStrictRayPositiveRootReturn flow,
      Nonempty (FinFourStrictRayMinimumLawHandoff result)) ∨
      (∃ result : FinFourStrictRayPositiveRootReturn flow,
        Nonempty (FinFourStrictRayOffMinimumDescent result)) ∨
      (∃ eta, 0 < eta ∧ ∀ᶠ time in atTop,
        eta ≤ flow.forward.renewalRatio time) ∨
      (∃ who : Fin 4, ∃ᶠ time in atTop,
        flow.forward.currentHazard time who = 0) ∨
      flow.forward.bindingFinset.card = 3 := by
  rcases
      flow.positiveAbsorptionExactRoot_at_capLimit_or_bindingFinset_eq_univ_or_card_eq_three
      with ⟨root, hnash, hpositive⟩ | hbinding
  · obtain ⟨result⟩ :=
      FinFourStrictRayPositiveRootReturn.nonempty_of_root_at_capLimit
        flow root hnash hpositive
    rcases result.nonempty_minimumLawHandoff_or_offMinimumDescent with
      hminimum | hdescent
    · exact Or.inl ⟨result, hminimum⟩
    · exact Or.inr (Or.inl ⟨result, hdescent⟩)
  · rcases hbinding with hfull | hthree
    · rcases
        eventually_renewalRatio_ge_pos_or_exists_frequently_currentHazard_eq_zero
          flow hfull with hballistic | homitted
      · exact Or.inr (Or.inr (Or.inl hballistic))
      · exact Or.inr (Or.inr (Or.inr (Or.inl homitted)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr hthree)))

end FinFourOwnerCompressedMinimumReturnForcedPairPacket

end GameTheory
