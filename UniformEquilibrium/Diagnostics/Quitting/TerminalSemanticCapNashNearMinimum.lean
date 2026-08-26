/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Stationary.LiveMass
import MathUE.ProbabilityMassFunction.Bool
import UniformEquilibrium.Diagnostics.Quitting.TerminalCapNashEndpointTransport
import UniformEquilibrium.Quitting.AbsorptionPath.NormalizedFiniteWindowOccupation
import UniformEquilibrium.Quitting.Root.TerminalSemanticEqualityStratum
import UniformEquilibrium.Quitting.Terminal.AuxiliaryNashDebt

/-!
# Cap--Nash transport near the minimum terminal-semantic stratum

The exact auxiliary-Nash prefix estimate is not restricted to an attained
minimum.  If `reference` is a global lower bound for total semantic debt and
`pair` is within `epsilon` of that lower bound, then an exact Nash root against
the shifted cap `pair.2 - h` obeys the quantitative budget

`reference * collision + sum singleton_i * (reference - h_i) <= epsilon`.

For a constant shift `q < reference`, this charges the root's entire
absorption mass at scale `reference - q`.  Thus auxiliary Nash roots against
caps shifted by any fixed amount below the minimum debt converge to the
all-Continue face along near-minimizers.  This is the robust form of the
critical-face argument and is the input needed to recover the full singleton
margin on actual near-minimizing profiles.

The vanishing absorption is not by itself a normalized tangent packet: the
auxiliary root may already be all-Continue, and its boundary is the shifted
cap rather than the prescribed payoff used by the existing charge packet.
Likewise, no absorbing label is matched to the later maximum-debt clock.  The
endpoint-gap branch is removed before those dynamic consumers are needed;
the harmonic/defect and negative-vertex branches remain separate.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-! ## Near-minimum auxiliary budget -/

/-- The auxiliary-Nash absorption budget with an unattained lower reference
and an explicit near-minimality error. -/
theorem nearMinimumTerminalSemantic_auxiliaryNash_budget
    (pair : QuittingTerminalSemanticPair ι)
    (h : Payoff ι) (root : ι → PMF Bool)
    (reference epsilon : ℝ)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hfloor : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      reference ≤ quittingTerminalSemanticDebtSum candidate)
    (hnear : quittingTerminalSemanticDebtSum pair ≤ reference + epsilon)
    (hepsilon : 0 ≤ epsilon)
    (hh : ∀ who, 0 ≤ h who)
    (hnash : IsεQuittingRootNash reward (pair.2 - h) 0 root) :
    reference * quittingRootCollisionMass root +
        ∑ who, quittingRootCoalitionMass root {who} *
          (reference - h who) ≤ epsilon := by
  let prefixed := quittingTerminalSemanticPrefix reward root pair
  have hprefixed : prefixed ∈ quittingTerminalSemanticCarrier reward :=
    quittingTerminalSemanticPrefix_mem_carrier
      reward root pair hpair
  have hcoordinate : ∀ who,
      quittingTerminalSemanticDebt prefixed who ≤
        quittingStationaryContinueMass root *
            quittingTerminalSemanticDebt pair who +
          quittingRootCoalitionMass root {who} * h who := by
    intro who
    exact quittingTerminalSemanticDebt_prefix_le_auxiliaryNash
      (reward := reward) pair h root who (hh who) hnash
  have hsum : quittingTerminalSemanticDebtSum prefixed ≤
      quittingStationaryContinueMass root *
          quittingTerminalSemanticDebtSum pair +
        ∑ who, quittingRootCoalitionMass root {who} * h who := by
    unfold quittingTerminalSemanticDebtSum
    calc
      ∑ who, quittingTerminalSemanticDebt prefixed who ≤
          ∑ who, (quittingStationaryContinueMass root *
              quittingTerminalSemanticDebt pair who +
            quittingRootCoalitionMass root {who} * h who) :=
        Finset.sum_le_sum fun who _ => hcoordinate who
      _ = quittingStationaryContinueMass root *
            ∑ who, quittingTerminalSemanticDebt pair who +
          ∑ who, quittingRootCoalitionMass root {who} * h who := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
  have hcontinueNonneg : 0 ≤ quittingStationaryContinueMass root :=
    quittingStationaryContinueMass_nonneg root
  have hcontinueLe : quittingStationaryContinueMass root ≤ 1 :=
    quittingStationaryContinueMass_le_one root
  have hscaledNear :
      quittingStationaryContinueMass root *
          quittingTerminalSemanticDebtSum pair ≤
        quittingStationaryContinueMass root * (reference + epsilon) :=
    mul_le_mul_of_nonneg_left hnear hcontinueNonneg
  have hscaledError :
      quittingStationaryContinueMass root * epsilon ≤ epsilon :=
    mul_le_of_le_one_left hepsilon hcontinueLe
  have hraw : reference ≤
      quittingStationaryContinueMass root * (reference + epsilon) +
        ∑ who, quittingRootCoalitionMass root {who} * h who :=
    (hfloor prefixed hprefixed).trans
      (hsum.trans (add_le_add hscaledNear (le_refl _)))
  have habsorption :=
    QuittingFiniteRootWindow.quittingRootAbsorptionMass_eq_sum_singletonMass_add_collisionMass
      root
  unfold quittingRootAbsorptionMass at habsorption
  have hbudget : reference * (1 - quittingStationaryContinueMass root) -
      ∑ who, quittingRootCoalitionMass root {who} * h who ≤ epsilon := by
    nlinarith
  rw [habsorption] at hbudget
  calc
    reference * quittingRootCollisionMass root +
          ∑ who, quittingRootCoalitionMass root {who} *
            (reference - h who) =
        reference *
            ((∑ who, quittingRootCoalitionMass root {who}) +
              quittingRootCollisionMass root) -
          ∑ who, quittingRootCoalitionMass root {who} * h who := by
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
      ring
    _ ≤ epsilon := hbudget

/-! ## Constant-shift moat -/

/-- With a constant cap shift `q`, singleton and collision absorption receive
their exact distinct coefficients. -/
theorem nearMinimumTerminalSemantic_constantShiftNash_budget
    (pair : QuittingTerminalSemanticPair ι)
    (root : ι → PMF Bool) (reference epsilon q : ℝ)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hfloor : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      reference ≤ quittingTerminalSemanticDebtSum candidate)
    (hnear : quittingTerminalSemanticDebtSum pair ≤ reference + epsilon)
    (hepsilon : 0 ≤ epsilon)
    (hq : 0 ≤ q)
    (hnash : IsεQuittingRootNash reward (pair.2 - fun _ => q) 0 root) :
    reference * quittingRootCollisionMass root +
        (reference - q) *
          (∑ who, quittingRootCoalitionMass root {who}) ≤ epsilon := by
  have hbudget := nearMinimumTerminalSemantic_auxiliaryNash_budget
    (reward := reward) pair (fun _ => q) root reference epsilon
      hpair hfloor hnear hepsilon (fun _ => hq) hnash
  calc
    reference * quittingRootCollisionMass root +
          (reference - q) *
            (∑ who, quittingRootCoalitionMass root {who}) =
        reference * quittingRootCollisionMass root +
          ∑ who, quittingRootCoalitionMass root {who} *
            (reference - (fun _ => q) who) := by
      rw [Finset.mul_sum]
      apply congrArg (reference * quittingRootCollisionMass root + ·)
      apply Finset.sum_congr rfl
      intro who _
      ring
    _ ≤ epsilon := hbudget

/-- Every bit of absorption of a constant-shift auxiliary Nash root is charged
at the residual moat width `reference - q`. -/
theorem nearMinimumTerminalSemantic_constantShiftNash_absorption
    (pair : QuittingTerminalSemanticPair ι)
    (root : ι → PMF Bool) (reference epsilon q : ℝ)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hfloor : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      reference ≤ quittingTerminalSemanticDebtSum candidate)
    (hnear : quittingTerminalSemanticDebtSum pair ≤ reference + epsilon)
    (hepsilon : 0 ≤ epsilon)
    (hq : 0 ≤ q) (hqle : q ≤ reference)
    (hnash : IsεQuittingRootNash reward (pair.2 - fun _ => q) 0 root) :
    (reference - q) * quittingRootAbsorptionMass root ≤ epsilon := by
  have hbudget := nearMinimumTerminalSemantic_constantShiftNash_budget
    (reward := reward) pair root reference epsilon q hpair hfloor hnear
      hepsilon hq hnash
  have hcollisionNonneg : 0 ≤ quittingRootCollisionMass root :=
    quittingRootCollisionMass_nonneg root
  have hresidualNonneg : 0 ≤ reference - q := sub_nonneg.mpr hqle
  have hcollisionScaled :
      (reference - q) * quittingRootCollisionMass root ≤
        reference * quittingRootCollisionMass root :=
    mul_le_mul_of_nonneg_right (sub_le_self reference hq)
      hcollisionNonneg
  have habsorption :=
    QuittingFiniteRootWindow.quittingRootAbsorptionMass_eq_sum_singletonMass_add_collisionMass
      root
  calc
    (reference - q) * quittingRootAbsorptionMass root =
        (reference - q) *
          ((∑ who, quittingRootCoalitionMass root {who}) +
            quittingRootCollisionMass root) := by rw [habsorption]
    _ = (reference - q) *
          (∑ who, quittingRootCoalitionMass root {who}) +
        (reference - q) * quittingRootCollisionMass root := by ring
    _ ≤ (reference - q) *
          (∑ who, quittingRootCoalitionMass root {who}) +
        reference * quittingRootCollisionMass root :=
      add_le_add (le_refl _) hcollisionScaled
    _ ≤ epsilon := by linarith

/-- Every near-minimum pair admits a cap-shifted exact Nash root inside the
quantitative absorption moat.  The root is auxiliary, while prefixing it to
`pair` still gives an actual carrier point. -/
theorem exists_constantShiftNash_with_absorption_moat
    (pair : QuittingTerminalSemanticPair ι)
    (reference epsilon q : ℝ)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hfloor : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      reference ≤ quittingTerminalSemanticDebtSum candidate)
    (hnear : quittingTerminalSemanticDebtSum pair ≤ reference + epsilon)
    (hepsilon : 0 ≤ epsilon)
    (hq : 0 ≤ q) (hqle : q ≤ reference) :
    ∃ root : ι → PMF Bool,
      IsεQuittingRootNash reward (pair.2 - fun _ => q) 0 root ∧
        (reference - q) * quittingRootAbsorptionMass root ≤ epsilon := by
  obtain ⟨root, hnash⟩ :=
    exists_isZeroQuittingRootNash
      (reward := reward) (pair.2 - fun _ => q)
  exact ⟨root, hnash,
    nearMinimumTerminalSemantic_constantShiftNash_absorption
      (reward := reward) pair root reference epsilon q hpair hfloor hnear
        hepsilon hq hqle hnash⟩

/-! ## Endpoint moat on the same auxiliary root -/

/-- If the near-minimality error is smaller than the residual shift width,
the root in the constant-shift moat has positive survival.  The generic sharp
joining-loss estimate therefore applies to this very same root. -/
theorem exists_constantShiftNash_with_endpoint_moat
    (pair : QuittingTerminalSemanticPair ι)
    (reference epsilon q : ℝ)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hfloor : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      reference ≤ quittingTerminalSemanticDebtSum candidate)
    (hnear : quittingTerminalSemanticDebtSum pair ≤ reference + epsilon)
    (hepsilon : 0 ≤ epsilon)
    (hq : 0 ≤ q) (herror : epsilon < reference - q) :
    ∃ root : ι → PMF Bool,
      IsεQuittingRootNash reward (pair.2 - fun _ => q) 0 root ∧
        (reference - q) * quittingRootAbsorptionMass root ≤ epsilon ∧
        0 < quittingStationaryContinueMass root ∧
        (1 - quittingStationaryContinueMass root) /
            quittingStationaryContinueMass root ≤
          epsilon / (reference - q - epsilon) ∧
        ∀ who,
          q - quittingJoiningLoss reward who *
              (epsilon / (reference - q - epsilon)) ≤
            pair.2 who - reward (quittingSingletonTerminal who) who := by
  have hqle : q ≤ reference := by linarith
  obtain ⟨root, hnash, habsorption⟩ :=
    exists_constantShiftNash_with_absorption_moat
      (reward := reward) pair reference epsilon q hpair hfloor hnear
        hepsilon hq hqle
  have hcontinueNonneg : 0 ≤ quittingStationaryContinueMass root :=
    quittingStationaryContinueMass_nonneg root
  have hcontinue : 0 < quittingStationaryContinueMass root := by
    by_contra hnot
    have hcontinueZero : quittingStationaryContinueMass root = 0 :=
      le_antisymm (le_of_not_gt hnot) hcontinueNonneg
    unfold quittingRootAbsorptionMass at habsorption
    rw [hcontinueZero] at habsorption
    nlinarith
  have hdenominator : 0 < reference - q - epsilon := by linarith
  have hodds :
      (1 - quittingStationaryContinueMass root) /
          quittingStationaryContinueMass root ≤
        epsilon / (reference - q - epsilon) := by
    apply (div_le_div_iff₀ hcontinue hdenominator).2
    unfold quittingRootAbsorptionMass at habsorption
    nlinarith
  refine ⟨root, hnash, habsorption, hcontinue, hodds, ?_⟩
  intro who
  have hmargin :=
    cap_sub_singleton_ge_shift_sub_joiningLoss_mul_absorptionOdds
      (reward := reward) pair.2 (fun _ => q) root who hcontinue hnash
  have hlossNonneg : 0 ≤ quittingJoiningLoss reward who :=
    quittingJoiningLoss_nonneg (reward := reward) who
  have hscaled := mul_le_mul_of_nonneg_left hodds hlossNonneg
  linarith

/-- Root-free cap margin supplied by the shifted auxiliary Nash root.  This
is the quantitative near-minimum version of the minimum singleton margin for
the envelope coordinate. -/
theorem nearMinimumTerminalSemantic_cap_sub_singleton_ge
    (pair : QuittingTerminalSemanticPair ι) (who : ι)
    (reference epsilon q : ℝ)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hfloor : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      reference ≤ quittingTerminalSemanticDebtSum candidate)
    (hnear : quittingTerminalSemanticDebtSum pair ≤ reference + epsilon)
    (hepsilon : 0 ≤ epsilon)
    (hq : 0 ≤ q) (herror : epsilon < reference - q) :
    q - quittingJoiningLoss reward who *
        (epsilon / (reference - q - epsilon)) ≤
      pair.2 who - reward (quittingSingletonTerminal who) who := by
  obtain ⟨_root, _hnash, _habsorption, _hcontinue, _hodds, hmargin⟩ :=
    exists_constantShiftNash_with_endpoint_moat
      (reward := reward) pair reference epsilon q hpair hfloor hnear
        hepsilon hq herror
  exact hmargin who

/-- Robust singleton floor for the prescribed coordinate of a near-minimum
semantic pair.  The same auxiliary root simultaneously witnesses the
absorption moat and the displayed error on every player coordinate. -/
theorem exists_constantShiftNash_prescribed_singletonFloor
    (pair : QuittingTerminalSemanticPair ι)
    (reference epsilon q : ℝ)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hfloor : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      reference ≤ quittingTerminalSemanticDebtSum candidate)
    (hnear : quittingTerminalSemanticDebtSum pair ≤ reference + epsilon)
    (hepsilon : 0 ≤ epsilon)
    (hq : 0 ≤ q) (herror : epsilon < reference - q) :
    ∃ root : ι → PMF Bool,
      IsεQuittingRootNash reward (pair.2 - fun _ => q) 0 root ∧
        (reference - q) * quittingRootAbsorptionMass root ≤ epsilon ∧
        ∀ who,
          reward (quittingSingletonTerminal who) who - pair.1 who ≤
            reference + epsilon - q +
              quittingJoiningLoss reward who *
                (epsilon / (reference - q - epsilon)) := by
  obtain ⟨root, hnash, habsorption, _hcontinue, _hodds, hmargin⟩ :=
    exists_constantShiftNash_with_endpoint_moat
      (reward := reward) pair reference epsilon q hpair hfloor hnear
        hepsilon hq herror
  refine ⟨root, hnash, habsorption, ?_⟩
  have hdebtNonneg : ∀ who,
      0 ≤ quittingTerminalSemanticDebt pair who :=
    quittingTerminalSemanticDebt_nonneg_of_mem_carrier
      reward hpair
  intro who
  have hcoordinateLe : quittingTerminalSemanticDebt pair who ≤
      quittingTerminalSemanticDebtSum pair := by
    unfold quittingTerminalSemanticDebtSum
    exact Finset.single_le_sum
      (fun player _ => hdebtNonneg player) (Finset.mem_univ who)
  unfold quittingTerminalSemanticDebt at hcoordinateLe
  linarith [hmargin who]

/-- Comparison-vector form of the prescribed singleton floor.  A conditioned
target cannot retain a positive solo endpoint gap when its coordinate error,
the total-debt excess, and the cap-shift moat error all vanish. -/
theorem exists_constantShiftNash_comparison_endpointGap_le
    (pair : QuittingTerminalSemanticPair ι) (comparison : Payoff ι)
    (reference epsilon q : ℝ)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hfloor : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      reference ≤ quittingTerminalSemanticDebtSum candidate)
    (hnear : quittingTerminalSemanticDebtSum pair ≤ reference + epsilon)
    (hepsilon : 0 ≤ epsilon)
    (hq : 0 ≤ q) (herror : epsilon < reference - q) :
    ∃ root : ι → PMF Bool,
      IsεQuittingRootNash reward (pair.2 - fun _ => q) 0 root ∧
        (reference - q) * quittingRootAbsorptionMass root ≤ epsilon ∧
        ∀ who,
          reward (quittingSingletonTerminal who) who - comparison who ≤
            reference + epsilon - q +
              quittingJoiningLoss reward who *
                (epsilon / (reference - q - epsilon)) +
              |pair.1 who - comparison who| := by
  obtain ⟨root, hnash, habsorption, hfloorPair⟩ :=
    exists_constantShiftNash_prescribed_singletonFloor
      (reward := reward) pair reference epsilon q hpair hfloor hnear
        hepsilon hq herror
  refine ⟨root, hnash, habsorption, ?_⟩
  intro who
  have hcomparison : pair.1 who - comparison who ≤
      |pair.1 who - comparison who| := le_abs_self _
  linarith [hfloorPair who]

/-- Root-free consumer of the cap--Nash construction.  This is the direct
interface for conditioned-tail extraction: the conditioned singleton gap is
bounded by the debt excess, the chosen moat width, and the conditioning
error. -/
theorem nearMinimumTerminalSemantic_comparison_endpointGap_le
    (pair : QuittingTerminalSemanticPair ι) (comparison : Payoff ι)
    (who : ι) (reference epsilon q : ℝ)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hfloor : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      reference ≤ quittingTerminalSemanticDebtSum candidate)
    (hnear : quittingTerminalSemanticDebtSum pair ≤ reference + epsilon)
    (hepsilon : 0 ≤ epsilon)
    (hq : 0 ≤ q) (herror : epsilon < reference - q) :
    reward (quittingSingletonTerminal who) who - comparison who ≤
      reference + epsilon - q +
        quittingJoiningLoss reward who *
          (epsilon / (reference - q - epsilon)) +
        |pair.1 who - comparison who| := by
  obtain ⟨_root, _hnash, _habsorption, hgap⟩ :=
    exists_constantShiftNash_comparison_endpointGap_le
      (reward := reward) pair comparison reference epsilon q hpair hfloor
        hnear hepsilon hq herror
  exact hgap who

/-- A conditioned endpoint gap larger than the explicit cap--Nash error is
impossible.  In particular, a fixed positive endpoint gap cannot persist
along near-minimizers whose conditioning error vanishes: first fix `q` below
`reference`, let `epsilon` vanish, and then send `q` up to `reference`. -/
theorem not_nearMinimumTerminalSemantic_conditionedEndpointGap
    (pair : QuittingTerminalSemanticPair ι) (comparison : Payoff ι)
    (who : ι) (reference epsilon q gamma : ℝ)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hfloor : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      reference ≤ quittingTerminalSemanticDebtSum candidate)
    (hnear : quittingTerminalSemanticDebtSum pair ≤ reference + epsilon)
    (hepsilon : 0 ≤ epsilon)
    (hq : 0 ≤ q) (herror : epsilon < reference - q)
    (hsmall : reference + epsilon - q +
        quittingJoiningLoss reward who *
          (epsilon / (reference - q - epsilon)) +
        |pair.1 who - comparison who| < gamma) :
    ¬ gamma ≤
      reward (quittingSingletonTerminal who) who - comparison who := by
  intro hgap
  have hupper := nearMinimumTerminalSemantic_comparison_endpointGap_le
    (reward := reward) pair comparison who reference epsilon q hpair hfloor
      hnear hepsilon hq herror
  linarith

/-! ## Cap--Nash iteration freezes near the minimum -/

/-- Once the explicit cap margin dominates the absorption odds available to
an unshifted cap--Nash root, that root must be all-Continue.  Therefore the
literal iteration which repeatedly prefixes an exact Nash root against the
current cap freezes near the minimum; it does not automatically generate a
nonzero tangent chronology. -/
theorem nearMinimumTerminalSemantic_capNash_eq_allContinue
    (pair : QuittingTerminalSemanticPair ι)
    (root : ι → PMF Bool) (reference epsilon q : ℝ) {M : ℝ}
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hfloor : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      reference ≤ quittingTerminalSemanticDebtSum candidate)
    (hnear : quittingTerminalSemanticDebtSum pair ≤ reference + epsilon)
    (hepsilon : 0 ≤ epsilon)
    (hq : 0 ≤ q) (herror : epsilon < reference - q)
    (hfreeze : 2 * M * (epsilon / (reference - epsilon)) <
      q - 2 * M * (epsilon / (reference - q - epsilon)))
    (hnash : IsεQuittingRootNash reward pair.2 0 root) :
    root = (quittingAllContinueRoot : ι → PMF Bool) := by
  have hreference : 0 < reference := by linarith
  have hreferenceError : epsilon < reference := by linarith
  have hnashZero :
      IsεQuittingRootNash reward (pair.2 - fun _ => (0 : ℝ)) 0 root := by
    have htail : pair.2 - (fun _ => (0 : ℝ)) = pair.2 := by
      funext player
      simp
    rw [htail]
    exact hnash
  have habsorption :=
    nearMinimumTerminalSemantic_constantShiftNash_absorption
      (reward := reward) pair root reference epsilon 0 hpair hfloor hnear
        hepsilon le_rfl hreference.le hnashZero
  have hcontinueNonneg : 0 ≤ quittingStationaryContinueMass root :=
    quittingStationaryContinueMass_nonneg root
  have hcontinue : 0 < quittingStationaryContinueMass root := by
    by_contra hnot
    have hzero : quittingStationaryContinueMass root = 0 :=
      le_antisymm (le_of_not_gt hnot) hcontinueNonneg
    unfold quittingRootAbsorptionMass at habsorption
    rw [hzero] at habsorption
    nlinarith
  have hreferenceDenominator : 0 < reference - epsilon := by linarith
  have hodds :
      (1 - quittingStationaryContinueMass root) /
          quittingStationaryContinueMass root ≤
        epsilon / (reference - epsilon) := by
    apply (div_le_div_iff₀ hcontinue hreferenceDenominator).2
    unfold quittingRootAbsorptionMass at habsorption
    nlinarith
  have hshiftDenominator : 0 < reference - q - epsilon := by linarith
  have hshiftRatioNonneg :
      0 ≤ epsilon / (reference - q - epsilon) :=
    div_nonneg hepsilon hshiftDenominator.le
  have hrefRatioNonneg : 0 ≤ epsilon / (reference - epsilon) :=
    div_nonneg hepsilon hreferenceDenominator.le
  funext who
  have hM :=
    quittingRewardCoordinateBound_nonneg_of_player reward who hreward
  have htwoMNonneg : 0 ≤ 2 * M := by positivity
  apply Math.ProbabilityMassFunction.eq_pure_false_of_apply_true_toReal_eq_zero
  by_contra hquitZero
  have hquit : 0 < (root who true).toReal :=
    lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hquitZero)
  have hownContinue : 0 < (root who false).toReal :=
    quittingRoot_continueProbability_pos_of_continueMass_pos
      root hcontinue who
  have hendpoint :=
    (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
      reward pair.2 root).mpr hnash
  have hendpointZero :
      quittingRootEndpointDifference reward pair.2 root who = 0 :=
    quittingRootEndpointDifference_eq_zero_of_both_probabilities_pos
      reward pair.2 root who hendpoint hownContinue hquit
  have hcapRaw := nearMinimumTerminalSemantic_cap_sub_singleton_ge
    (reward := reward) pair who reference epsilon q hpair hfloor hnear
      hepsilon hq herror
  have hlossBound := quittingJoiningLoss_le_two_mul
    (reward := reward) who hreward
  have hlossScaled :=
    mul_le_mul_of_nonneg_right hlossBound hshiftRatioNonneg
  have hcapMargin :
      q - 2 * M * (epsilon / (reference - q - epsilon)) ≤
        pair.2 who - reward (quittingSingletonTerminal who) who := by
    linarith
  let eta := q - 2 * M *
    (epsilon / (reference - q - epsilon))
  let opponentContinue := quittingRootOpponentContinueMass root who
  let opponentAbsorption := quittingRootOpponentAbsorptionMass root who
  let joining := quittingOutsiderJoiningContribution reward root who
  have heta : 0 < eta := by
    dsimp [eta]
    nlinarith [mul_nonneg htwoMNonneg hrefRatioNonneg]
  have hopponentContinueNonneg : 0 ≤ opponentContinue :=
    quittingRootOpponentContinueMass_nonneg root who
  have hcontinueLeOpponent :
      quittingStationaryContinueMass root ≤ opponentContinue :=
    quittingStationaryContinueMass_le_update_pure_false root who
  have hopponentAbsorptionLe : opponentAbsorption ≤
      quittingRootAbsorptionMass root :=
    quittingRootOpponentAbsorptionMass_le_absorptionMass root who
  have hjoiningAbs : |joining| ≤ 2 * M * opponentAbsorption := by
    simpa [joining, opponentAbsorption] using
      abs_quittingOutsiderJoiningContribution_le_two_mul_absorptionMass
        reward root who hreward
  have hdecomposition :=
    quittingRootEndpointDifference_eq_outsiderNever reward pair.2 root who
  have hopponentComplement : opponentContinue = 1 - opponentAbsorption :=
    quittingRootOpponentContinueMass_eq_one_sub_absorptionMass root who
  have hjoiningEq :
      opponentContinue *
          (pair.2 who - reward (quittingSingletonTerminal who) who) =
        joining := by
    change quittingRootEndpointDifference reward pair.2 root who =
        (1 - opponentAbsorption) *
            (reward (quittingSingletonTerminal who) who - pair.2 who) +
          joining at hdecomposition
    rw [hendpointZero, ← hopponentComplement] at hdecomposition
    linarith
  have hcharged :
      quittingStationaryContinueMass root * eta ≤
        2 * M * quittingRootAbsorptionMass root := by
    have hfirst : quittingStationaryContinueMass root * eta ≤
        opponentContinue * eta :=
      mul_le_mul_of_nonneg_right hcontinueLeOpponent heta.le
    have hsecond : opponentContinue * eta ≤
        opponentContinue *
          (pair.2 who - reward (quittingSingletonTerminal who) who) :=
      mul_le_mul_of_nonneg_left (by simpa [eta] using hcapMargin)
        hopponentContinueNonneg
    have hjoiningUpper : joining ≤ 2 * M * opponentAbsorption :=
      le_of_abs_le hjoiningAbs
    have habsorptionScaled : 2 * M * opponentAbsorption ≤
        2 * M * quittingRootAbsorptionMass root :=
      mul_le_mul_of_nonneg_left hopponentAbsorptionLe htwoMNonneg
    calc
      quittingStationaryContinueMass root * eta ≤
          opponentContinue * eta := hfirst
      _ ≤ opponentContinue *
          (pair.2 who - reward (quittingSingletonTerminal who) who) := hsecond
      _ = joining := hjoiningEq
      _ ≤ 2 * M * opponentAbsorption := hjoiningUpper
      _ ≤ 2 * M * quittingRootAbsorptionMass root := habsorptionScaled
  have hetaOdds : eta ≤ 2 * M *
      ((1 - quittingStationaryContinueMass root) /
        quittingStationaryContinueMass root) := by
    rw [show 2 * M *
        ((1 - quittingStationaryContinueMass root) /
          quittingStationaryContinueMass root) =
      (2 * M * (1 - quittingStationaryContinueMass root)) /
        quittingStationaryContinueMass root by ring]
    apply (le_div_iff₀ hcontinue).2
    unfold quittingRootAbsorptionMass at hcharged
    calc
      eta * quittingStationaryContinueMass root =
          quittingStationaryContinueMass root * eta := by ring
      _ ≤ 2 * M * (1 - quittingStationaryContinueMass root) := hcharged
  have hscaledOdds := mul_le_mul_of_nonneg_left hodds htwoMNonneg
  dsimp [eta] at hetaOdds
  linarith

/-- A positive global semantic debt floor has a fixed quantitative
neighborhood in which every exact root against the displayed behavioral cap
is all-Continue.

The radius is selected directly from the explicit cap-freezing inequality:
set `q = reference / 2` and choose one positive reciprocal error small enough
that both rational loss terms sum to less than `q`.  No compactness or
punishment-normality hypothesis is used. -/
theorem exists_pos_nearMinimum_capNash_eq_allContinue_radius
    (reference : ℝ) (hreference : 0 < reference)
    (hfloor : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      reference ≤ quittingTerminalSemanticDebtSum candidate) :
    ∃ epsilon : ℝ, 0 < epsilon ∧
      ∀ pair ∈ quittingTerminalSemanticCarrier reward,
        quittingTerminalSemanticDebtSum pair ≤ reference + epsilon →
          ∀ root : ι → PMF Bool,
            IsεQuittingRootNash reward pair.2 0 root →
              root = (quittingAllContinueRoot : ι → PMF Bool) := by
  let q := reference / 2
  let error : ℕ → ℝ := fun n ↦ 1 / ((n : ℝ) + 1)
  have herrorTendsto : Tendsto error atTop (nhds 0) := by
    simpa only [error] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hreferenceSub : Tendsto (fun n ↦ reference - error n)
      atTop (nhds reference) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub herrorTendsto
  have hqSub : Tendsto (fun n ↦ reference - q - error n)
      atTop (nhds (reference - q)) := by
    simpa only [sub_zero] using
      (tendsto_const_nhds.sub herrorTendsto :
        Tendsto (fun n ↦ reference - q - error n) atTop
          (nhds (reference - q - 0)))
  have hfirstRatio : Tendsto
      (fun n ↦ error n / (reference - error n)) atTop (nhds 0) := by
    convert herrorTendsto.div hreferenceSub (ne_of_gt hreference) using 1 <;>
      try rfl
    simp
  have hqPos : 0 < reference - q := by
    dsimp only [q]
    linarith
  have hsecondRatio : Tendsto
      (fun n ↦ error n / (reference - q - error n)) atTop (nhds 0) := by
    convert herrorTendsto.div hqSub (ne_of_gt hqPos) using 1 <;>
      try rfl
    simp
  let M := quittingRewardBound reward
  have hcost : Tendsto
      (fun n ↦ 2 * M * (error n / (reference - error n)) +
        2 * M * (error n / (reference - q - error n)))
      atTop (nhds 0) := by
    simpa only [mul_zero, zero_add] using
      (hfirstRatio.const_mul (2 * M)).add
        (hsecondRatio.const_mul (2 * M))
  have herrorSmall : ∀ᶠ n in atTop, error n < reference - q :=
    (tendsto_order.1 herrorTendsto).2 (reference - q) hqPos
  have hcostSmall : ∀ᶠ n in atTop,
      2 * M * (error n / (reference - error n)) +
          2 * M * (error n / (reference - q - error n)) < q := by
    apply (tendsto_order.1 hcost).2 q
    dsimp only [q]
    linarith
  obtain ⟨n, hnError, hnCost⟩ := (herrorSmall.and hcostSmall).exists
  have hnPos : 0 < error n := by
    dsimp only [error]
    positivity
  refine ⟨error n, hnPos, ?_⟩
  intro pair hpair hnear root hnash
  have hqValuePos : 0 < q := by
    dsimp only [q]
    linarith
  exact nearMinimumTerminalSemantic_capNash_eq_allContinue
    pair root reference (error n) q
      (abs_reward_le_quittingRewardBound reward) hpair hfloor hnear hnPos.le
        hqValuePos.le hnError (by linarith) hnash

end GameTheory
