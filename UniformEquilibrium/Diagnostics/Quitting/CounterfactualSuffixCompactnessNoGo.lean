/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.PMFProduct.Bool
import MathUE.PMFProduct.TotalVariation
import MathUE.Topology.UniformProbeCompactness
import UniformEquilibrium.Quitting.Paths.CounterfactualStoppingLaw

/-!
# Counterfactual suffix compactness no-go

Two four-player stopping families have the same payoff-vector response law
after every current one-player marginal replacement, but no state encoded
only by that signature can realize the stated successor values.  A separate
spike family shows that any metric state which realizes every suffix-depth
probe with one common modulus has an
infinite uniformly separated image.  It is therefore neither sequentially
compact nor covered by one finite net at the resulting resolution.

The collision forgets stopping dates and coalition labels only through an
explicit reward pushforward.  The compactness obstruction requires one
modulus common to all depths.  It does not rule out a fixed-depth state,
depth-dependent moduli, or finite-program approximations.
-/

noncomputable section

namespace GameTheory
namespace FinFourCounterfactualSuffixNoGo

open Math Math.Probability Math.ProbabilityMassFunction Math.PMFProduct

abbrev Player := Fin 4

/-- The collision reward: player zero receives one at every absorbing
outcome, while player one receives one only when players one and two quit
together. -/
def reward : {S : Finset Player // S.Nonempty} -> Payoff Player :=
  fun terminal who =>
    if who = 0 then 1
    else if who = 1 then
      if 1 ∈ terminal.1 ∧ 2 ∈ terminal.1 then 1 else 0
    else 0

/-- Payoff vector attached to a labelled terminal outcome.  This is the
explicit coalition-forgetting map used by the collision. -/
def terminalPayoffVector : QuittingTerminalOutcome Player -> Payoff Player
  | none => 0
  | some terminal => reward terminal

/-- The pushed payoff-vector law of independent stopping marginals.  The
first-stopping map forgets dates; this second map forgets coalition labels. -/
def payoffVectorLaw (laws : Player -> PMF (Option Nat)) : PMF (Payoff Player) :=
  (quittingIndependentTerminalOutcomeLaw laws).map terminalPayoffVector

/-- Fair Boolean coin used by the two source families. -/
def halfCoin : PMF Bool :=
  bernoulliBool (1 / 2) (by norm_num) (by norm_num)

/-- Stop at `time` on heads and never stop on tails. -/
def halfStopLaw (time : Nat) : PMF (Option Nat) :=
  halfCoin.bind fun stops => PMF.pure (if stops then some time else none)

/-- The source player is player zero; every other player initially never
stops. -/
def sourceLaws (time : Nat) (who : Player) : PMF (Option Nat) :=
  if who = 0 then halfStopLaw time else PMF.pure none

/-- Current one-player payoff response law. -/
def currentPayoffResponseLaw (time : Nat) (who : Player)
    (replacement : PMF (Option Nat)) : PMF (Payoff Player) :=
  payoffVectorLaw (Function.update (sourceLaws time) who replacement)

/-- The unit payoff vector supported at player zero. -/
def unitPayoff : Payoff Player := fun who => if who = 0 then 1 else 0

private theorem reward_eq_unitPayoff_of_subset_pair
    (terminal : {S : Finset Player // S.Nonempty}) (who : Player)
    (hterminal : terminal.1 ⊆ {0, who}) :
    reward terminal = unitPayoff := by
  funext observer
  fin_cases observer
  · simp [reward, unitPayoff]
  · have hnot : ¬(1 ∈ terminal.1 ∧ 2 ∈ terminal.1) := by
      rintro ⟨hone, htwo⟩
      have hone' := hterminal hone
      have htwo' := hterminal htwo
      simp only [Finset.mem_insert, Finset.mem_singleton] at hone' htwo'
      fin_cases who <;> simp_all
    simp [reward, unitPayoff, hnot]
  · simp [reward, unitPayoff]
  · simp [reward, unitPayoff]

private theorem firstStopping_payoff_of_two_active
    (times : Player -> Option Nat) (who : Player)
    (hactive : ∀ other, times other ≠ none -> other = 0 ∨ other = who) :
    terminalPayoffVector (quittingFirstStoppingOutcome times) =
      if (∃ other, times other ≠ none) then unitPayoff else 0 := by
  classical
  by_cases hexists : ∃ other, times other ≠ none
  · simp only [if_pos hexists]
    obtain ⟨active, hactiveTime⟩ := hexists
    have hearliestNe : quittingEarliestStoppingValue times ≠ ⊤ := by
      intro hearliest
      obtain ⟨time, htime⟩ : ∃ time, times active = some time := by
        cases hvalue : times active with
        | none => exact False.elim (hactiveTime hvalue)
        | some time => exact ⟨time, rfl⟩
      have hle : quittingEarliestStoppingValue times ≤
          quittingStoppingTimeValue (times active) :=
        Finset.inf_le (Finset.mem_univ active)
      rw [hearliest, htime] at hle
      simp [quittingStoppingTimeValue] at hle
    rw [quittingFirstStoppingOutcome, if_neg hearliestNe]
    change reward _ = unitPayoff
    apply reward_eq_unitPayoff_of_subset_pair
    intro other hother
    have hvalue : quittingStoppingTimeValue (times other) =
        quittingEarliestStoppingValue times :=
      (Finset.mem_filter.mp hother).2
    have hotherFinite : times other ≠ none := by
      intro hnone
      rw [hnone, quittingStoppingTimeValue] at hvalue
      exact hearliestNe hvalue.symm
    simpa [Finset.mem_insert, Finset.mem_singleton] using hactive other hotherFinite
  · simp only [if_neg hexists]
    have hnever : times = fun _ => none := by
      funext who
      by_contra hne
      exact hexists ⟨who, hne⟩
    rw [hnever, quittingFirstStoppingOutcome_all_never]
    rfl

private theorem map_firstStopping_payoff_two_active
    (law : PMF (Player -> Option Nat)) (who : Player)
    (hactive : ∀ times ∈ law.support, ∀ other,
      times other ≠ none -> other = 0 ∨ other = who) :
    law.map (terminalPayoffVector ∘ quittingFirstStoppingOutcome) =
      law.map (fun times =>
        if (∃ other, times other ≠ none) then unitPayoff else 0) := by
  rw [← PMF.bind_pure_comp, ← PMF.bind_pure_comp]
  apply Math.ProbabilityMassFunction.bind_congr_on_support
  intro times htimes
  simpa only [Function.comp_apply] using congrArg PMF.pure
    (firstStopping_payoff_of_two_active times who (hactive times htimes))

private theorem support_two_active
    (time : Nat) (who : Player) (replacement : PMF (Option Nat))
    (times : Player -> Option Nat)
    (htimes : times ∈
      (pmfPi (Function.update (sourceLaws time) who replacement)).support) :
    ∀ other, times other ≠ none -> other = 0 ∨ other = who := by
  intro other hother
  by_contra hnot
  have hotherZero : other ≠ 0 := fun heq => hnot (Or.inl heq)
  have hotherWho : other ≠ who := fun heq => hnot (Or.inr heq)
  have hmarginal :
      Function.update (sourceLaws time) who replacement other = PMF.pure none := by
    simp [sourceLaws, hotherZero, hotherWho]
  have hproduct := htimes
  simp only [PMF.mem_support_iff, pmfPi_apply] at hproduct
  have hfactor :
      Function.update (sourceLaws time) who replacement other (times other) ≠ 0 := by
    intro hzero
    rw [Finset.prod_eq_zero (Finset.mem_univ other) hzero] at hproduct
    exact hproduct rfl
  rw [hmarginal, PMF.pure_apply, if_neg hother] at hfactor
  exact hfactor rfl

private theorem halfStopLaw_map_isSome (time : Nat) :
    (halfStopLaw time).map Option.isSome = halfCoin := by
  unfold halfStopLaw
  rw [PMF.map_bind]
  have hkernel :
      (fun stops =>
        (PMF.pure (if stops then some time else none)).map Option.isSome) =
        (fun stops => PMF.pure stops) := by
    funext stops
    cases stops <;> rw [PMF.pure_map] <;> rfl
  rw [hkernel, PMF.bind_pure]

private theorem observed_product_zero_eq_one
    (who : Player) (replacement : PMF (Option Nat)) :
    (pmfPi (Function.update (sourceLaws 0) who replacement)).map
        (fun times who => (times who).isSome) =
      (pmfPi (Function.update (sourceLaws 1) who replacement)).map
        (fun times who => (times who).isSome) := by
  apply pmfPi_map_coordwise_eq_of_maps_eq
  intro other
  by_cases hother : other = who
  · subst other
    simp
  · by_cases hzero : other = 0
    · subst other
      simp [hother, sourceLaws, halfStopLaw_map_isSome]
    · simp [hother, hzero, sourceLaws]

/-- The complete current payoff-vector response laws agree after every
one-player replacement.  This equality is only after the first-stopping/date
and reward/coalition pushforwards; it does not identify either hidden datum. -/
theorem currentPayoffResponseLaw_zero_eq_one
    (who : Player) (replacement : PMF (Option Nat)) :
    currentPayoffResponseLaw 0 who replacement =
      currentPayoffResponseLaw 1 who replacement := by
  unfold currentPayoffResponseLaw payoffVectorLaw
  simp only [quittingIndependentTerminalOutcomeLaw, PMF.map_comp]
  rw [map_firstStopping_payoff_two_active _ who
      (support_two_active 0 who replacement),
    map_firstStopping_payoff_two_active _ who
      (support_two_active 1 who replacement)]
  have hmap := congrArg
    (fun law : PMF (Player -> Bool) =>
      law.map fun active => if (∃ other, active other) then unitPayoff else 0)
    (observed_product_zero_eq_one who replacement)
  have hfunction :
      (fun times : Player -> Option Nat =>
        if (∃ other, times other ≠ none) then unitPayoff else 0) =
      (fun times =>
        if (∃ other, (times other).isSome) then unitPayoff else 0) := by
    funext times
    congr 1
    simp only [Option.isSome_iff_ne_none]
  rw [hfunction]
  change
    (pmfPi (Function.update (sourceLaws 0) who replacement)).map
        ((fun active =>
          if (∃ other, active other) then unitPayoff else 0) ∘
          fun times who => (times who).isSome) =
      (pmfPi (Function.update (sourceLaws 1) who replacement)).map
        ((fun active =>
          if (∃ other, active other) then unitPayoff else 0) ∘
          fun times who => (times who).isSome)
  simpa only [PMF.map_comp] using hmap

/-- The general total variation of every corresponding payoff-vector
response law is literally zero. -/
theorem pmfGeneralTV_currentPayoffResponseLaw_zero_one_eq_zero
    (who : Player) (replacement : PMF (Option Nat)) :
    pmfGeneralTV (currentPayoffResponseLaw 0 who replacement)
      (currentPayoffResponseLaw 1 who replacement) = 0 := by
  rw [currentPayoffResponseLaw_zero_eq_one]
  unfold pmfGeneralTV
  simp only [min_self]
  rw [pmf_toReal_tsum_one]
  ring

/-- The complete family of current payoff-vector response laws. -/
def currentPayoffResponseSignature (time : Nat) :
    (who : Player) -> PMF (Option Nat) -> PMF (Payoff Player) :=
  fun who replacement => currentPayoffResponseLaw time who replacement

/-- The two source families have exactly the same current payoff response
signature. -/
theorem currentPayoffResponseSignature_zero_eq_one :
    currentPayoffResponseSignature 0 = currentPayoffResponseSignature 1 := by
  funext who replacement
  exact currentPayoffResponseLaw_zero_eq_one who replacement

/-- A state built only from the current payoff-response signature cannot both
realize the one-step suffix transition and expose the successor payoff.  The
transition and observation requirements are explicit hypotheses. -/
theorem no_currentResponseQuotient_suffixTransition_payoffObservable
    {State : Type*}
    (encode : ((who : Player) -> PMF (Option Nat) -> PMF (Payoff Player)) -> State)
    (advance : State -> State) (dead : State) (observe : State -> Real)
    (hzero : advance (encode (currentPayoffResponseSignature 0)) = dead)
    (hone : advance (encode (currentPayoffResponseSignature 1)) =
      encode (currentPayoffResponseSignature 0))
    (hdead : observe dead = 0)
    (hhalf : observe (encode (currentPayoffResponseSignature 0)) = 1 / 2) :
    False := by
  have hstate :
      encode (currentPayoffResponseSignature 0) =
        encode (currentPayoffResponseSignature 1) :=
    congrArg encode currentPayoffResponseSignature_zero_eq_one
  have hsuccessor : dead = encode (currentPayoffResponseSignature 0) := by
    calc
      dead = advance (encode (currentPayoffResponseSignature 0)) := hzero.symm
      _ = advance (encode (currentPayoffResponseSignature 1)) :=
        congrArg advance hstate
      _ = encode (currentPayoffResponseSignature 0) := hone
  have hobserve := congrArg observe hsuccessor
  rw [hdead, hhalf] at hobserve
  norm_num at hobserve

/-! ## A concrete all-depth suffix probe -/

/-- At suffix depth `label`, the root indexed by `source` has one fair Quit
coordinate exactly when the two depths agree; player two is then forced to
Quit. -/
def spikeProbeRoot (label source : Nat) (who : Player) : PMF Bool :=
  if who = 1 then
    if label = source then halfCoin else PMF.pure false
  else if who = 2 then PMF.pure true else PMF.pure false

/-- Player one's actual one-stage quitting payoff at a suffix probe. -/
def spikeProbe (label source : Nat) : Real :=
  quittingRootExpectedPayoff reward 0 (spikeProbeRoot label source) 1

/-- Exact spike identity: the depth-labelled probe is one half at its own
source and zero at every other source. -/
theorem spikeProbe_eq (label source : Nat) :
    spikeProbe label source = if label = source then 1 / 2 else 0 := by
  unfold spikeProbe quittingRootExpectedPayoff
  have hroot : spikeProbeRoot label source = fun who =>
      if who ∈ ({1} : Finset Player) then
        (if label = source then halfCoin else PMF.pure false)
      else PMF.pure (who = 2) := by
    funext who
    fin_cases who <;> simp [spikeProbeRoot]
  rw [hroot, expect_pmfPi_boolFamily_eq_sum_powerset]
  rw [show ({1} : Finset Player).powerset = {∅, {1}} by decide]
  have hpairNonempty :
      ({who : Player | who = 1 ∨ who ≠ 1 ∧ who = 2} : Finset Player).Nonempty := by
    exact ⟨2, by simp⟩
  simp [halfCoin, reward, quittingRootPayoff, quittingQuitters,
    Finset.ext_iff, hpairNonempty]
  split_ifs <;> norm_num

/-- Distinct source depths are separated by their own labelled suffix
probe. -/
theorem spikeProbe_separated {first second : Nat} (hne : first ≠ second) :
    1 / 2 ≤ dist (spikeProbe first first) (spikeProbe first second) := by
  rw [spikeProbe_eq, spikeProbe_eq]
  norm_num [hne]

/-- No sequentially compact carrier can contain an encoding of every spike
source while realizing all depth probes with one common modulus. -/
theorem not_isSeqCompact_of_commonAllDepthSpikeState
    {State : Type*} [PseudoMetricSpace State]
    (state : Nat -> State) {carrier : Set State}
    (hstate : ∀ source, state source ∈ carrier)
    (hmodulus : HasCommonProbeModulus spikeProbe state) :
    ¬IsSeqCompact carrier := by
  exact not_isSeqCompact_of_commonProbeModulus
    spikeProbe state id (by norm_num) hstate
      (fun hne => spikeProbe_separated hne) hmodulus

/-- A common-all-depth spike encoding also fails one finite global-net
property at a positive radius produced by the common modulus. -/
theorem exists_no_finite_net_of_commonAllDepthSpikeState
    {State : Type*} [PseudoMetricSpace State]
    (state : Nat -> State)
    (hmodulus : HasCommonProbeModulus spikeProbe state) :
    ∃ radius, 0 < radius ∧
      ¬∃ centers : Set State, centers.Finite ∧
        ∀ source, ∃ center ∈ centers, dist (state source) center < radius := by
  exact exists_no_finite_net_of_commonProbeModulus
    spikeProbe state id (by norm_num)
      (fun hne => spikeProbe_separated hne) hmodulus

end FinFourCounterfactualSuffixNoGo
end GameTheory
