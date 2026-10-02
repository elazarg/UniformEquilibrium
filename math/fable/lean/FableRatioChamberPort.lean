/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/
import FableDebtMinimaSeparation
import UniformEquilibrium.Quitting.Terminal.TerminalDebtPrefixDescent
import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.Endpoint.ActualProfileTerminalGapPaidCap

/-!
# The ratio-chamber carrier/actual-source port

This file formalizes Theorem C of the export
`math/exports/FIN4_DEBT_RATIO_CHAMBER_CONTRACTION.md`, together with the
inf-form certificate bridge and the two-stage actual-data adapter of that
export's Lean-handoff items 4 and 5.  The per-profile content -- the chord
crossing estimate, the maximal debtor bound `a > eta` at one profile, and the
attainment-free port bound -- is consumed from `FableDebtMinimaSeparation`;
nothing about a single profile is re-derived here.

Write `d_i` for a terminal semantic debt coordinate, `D` for the total, `eta`
for the certificate scale and `M = quittingRewardBound reward`.

Results:

* **Inf-form certificate.**  `eta <= quittingTerminalExploitabilityInf reward`
  with `0 < eta` gives the hypothesis-form
  `FableCertifiedExploitabilityFloor reward eta` used throughout the scratch
  ratio-chamber development.  The production infimum is a genuine `sInf` over
  all behavior profiles, so this is the per-profile lower bound composed with
  the identification of literal and semantic exploitability at actual pairs.
* **Stabilization.**  `fableRatioChamber_exists_strictMono_maxDebt`: along one
  strictly monotone extraction a single player carries a maximal debt at every
  index.  This is the finite pigeonhole of the export's (12).
* **The limiting principal debt.**  `fableRatioChamber_lt_limit_maxDebt`: the
  stabilized player's limiting debt strictly exceeds `eta` whenever the limit
  point has total debt below `2 * eta`.  This is the export's fixed-small-mixture
  argument; the mover chord value and the `2 * M` bound on every other
  coordinate are combined at one explicit weight.
* **Theorem C.**  `fableRatioChamber_nonempty_port` produces the package
  `FableRatioChamberPort`: the fixed payer, the extraction, vanishing positive
  accuracies, literal one-player behavioral replacements, the export's (C1),
  the eventual strict form of (C2), and the eventual forms of (C3) and its
  ratio closing (21).  The export's lower chamber bound `eta < D(x)` is derived
  rather than assumed, and carrier minimality of `x` is not used.
* **(C4).**  `fableRatioChamber_exists_carrier_cluster` and
  `FableRatioChamberPort.exists_carrier_cluster` extract a carrier cluster point
  of the targets carrying the ratio floor, using compactness of the checked
  carrier and continuity of total semantic debt.
* **The two-stage adapter.**  `fableRatioChamber_composite_adapter` retains the
  incoming fixed-payer response edge together with a separately selected
  `QuittingActualProfileTerminalGapPaidCapPort` based at every target profile,
  and `fableRatioChamber_composite_adapter_of_no_uniformEquilibriumPayoff`
  enters that adapter from failure of a uniform-equilibrium payoff.

Discipline of the two binding reviews of the export is kept: no exact
best-response selection appears in any general statement -- every response is an
explicit `zeta`-approximate behavioral replacement -- and no convergence of
strategies is inferred anywhere from convergence of semantic pairs.  The
sequence hypotheses are always coordinatewise *semantic* convergence.

The (C3) conclusions are stated in eventually form: for every accuracy the
target total debt eventually exceeds the export's floor minus that accuracy.
For a real sequence this is exactly the `liminf` lower bound of (C3), stated
without the `Filter.liminf` wrapper and its boundedness side conditions.
-/

noncomputable section

namespace GameTheory

open Filter StochasticGame QuittingBoundaryHolonomy

open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## 0. The inf-form certificate bridge -/

/-- **W1.**  The checked global terminal exploitability infimum, when it is at
least a positive `eta`, supplies the hypothesis-form certificate: every actual
behavior profile has some player whose semantic debt is at least `eta`.

The production infimum `quittingTerminalExploitabilityInf` is `sInf` of the
range of literal maximum terminal exploitability, so the per-profile bound is
`quittingTerminalExploitabilityInf_le`, and literal and semantic exploitability
agree at actual pairs by `quittingTerminalSemanticExploitability_pair`. -/
theorem fableRatioChamber_certifiedFloor_of_le_exploitabilityInf [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (eta : ℝ) (heta : 0 < eta)
    (hinf : eta ≤ quittingTerminalExploitabilityInf reward) :
    FableCertifiedExploitabilityFloor reward eta := by
  intro profile
  refine fableThinSlice_exists_debt_ge_of_exploitability
    (quittingTerminalSemanticPair reward profile) eta heta ?_
  rw [quittingTerminalSemanticExploitability_pair]
  exact hinf.trans (quittingTerminalExploitabilityInf_le reward profile)

/-! ## 1. Sequence bookkeeping -/

omit [DecidableEq ι] in
/-- Total semantic debt converges whenever every debt coordinate does. -/
theorem fableRatioChamber_tendsto_debtSum
    (pairs : ℕ → QuittingTerminalSemanticPair ι) (x : QuittingTerminalSemanticPair ι)
    (hconv : ∀ observer, Tendsto (fun n => quittingTerminalSemanticDebt (pairs n) observer)
      atTop (𝓝 (quittingTerminalSemanticDebt x observer))) :
    Tendsto (fun n => quittingTerminalSemanticDebtSum (pairs n)) atTop
      (𝓝 (quittingTerminalSemanticDebtSum x)) := by
  unfold quittingTerminalSemanticDebtSum
  exact tendsto_finsetSum _ fun observer _ => hconv observer

/-- Coordinatewise semantic convergence of the prescribed payoffs and the
unrestricted behavioral caps gives coordinatewise debt convergence.  This is
the hypothesis shape used by the sequence-level scratch files. -/
theorem fableRatioChamber_tendsto_debt_of_semantic
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (sigmas : ℕ → (quittingGame reward).BehaviorProfile)
    (x : QuittingTerminalSemanticPair ι)
    (hpayoff : ∀ observer, Tendsto (fun n =>
      quittingTerminalPayoff reward (sigmas n) observer) atTop (𝓝 (x.1 observer)))
    (hcap : ∀ observer, Tendsto (fun n =>
      quittingContinuationBestResponseValue reward (sigmas n) observer) atTop
      (𝓝 (x.2 observer))) (observer : ι) :
    Tendsto (fun n => quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward (sigmas n)) observer) atTop
      (𝓝 (quittingTerminalSemanticDebt x observer)) :=
  (hcap observer).sub (hpayoff observer)

omit [Fintype ι] [DecidableEq ι] in
/-- Convergence of the whole semantic pair gives coordinatewise debt
convergence. -/
theorem fableRatioChamber_tendsto_debt_of_pair
    (pairs : ℕ → QuittingTerminalSemanticPair ι) (x : QuittingTerminalSemanticPair ι)
    (hpairs : Tendsto pairs atTop (𝓝 x)) (observer : ι) :
    Tendsto (fun n => quittingTerminalSemanticDebt (pairs n) observer) atTop
      (𝓝 (quittingTerminalSemanticDebt x observer)) :=
  ((continuous_quittingTerminalSemanticDebt observer).continuousAt.tendsto).comp hpairs

/-- Pigeonhole on a finite type: a sequence is constant along one strictly
monotone extraction. -/
theorem fableRatioChamber_exists_strictMono_comp_eq_const {α : Type*} [Finite α]
    (f : ℕ → α) :
    ∃ (value : α) (φ : ℕ → ℕ), StrictMono φ ∧ ∀ step, f (φ step) = value := by
  have hfrequent : ∃ value : α, ∃ᶠ index in atTop, f index = value := by
    by_contra hcontra
    have hall : ∀ᶠ index in atTop, ∀ value : α, f index ≠ value := by
      refine Filter.eventually_all.mpr fun value => ?_
      rw [← Filter.not_frequently]
      exact fun hfreq => hcontra ⟨value, hfreq⟩
    obtain ⟨index, hindex⟩ := hall.exists
    exact hindex (f index) rfl
  obtain ⟨value, hvalue⟩ := hfrequent
  obtain ⟨φ, hmono, hφ⟩ := extraction_of_frequently_atTop hvalue
  exact ⟨value, φ, hmono, hφ⟩

/-- **Stabilization of the principal debtor.**  Along one strictly monotone
extraction a single player carries a maximal semantic debt at every index. -/
theorem fableRatioChamber_exists_strictMono_maxDebt [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (sigmas : ℕ → (quittingGame reward).BehaviorProfile) :
    ∃ (payer : ι) (φ : ℕ → ℕ), StrictMono φ ∧ ∀ step observer,
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward (sigmas (φ step))) observer ≤
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward (sigmas (φ step))) payer := by
  classical
  choose selector hselector using fun n => Finite.exists_max
    (fun who => quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward (sigmas n)) who)
  obtain ⟨payer, φ, hmono, hφ⟩ :=
    fableRatioChamber_exists_strictMono_comp_eq_const selector
  refine ⟨payer, φ, hmono, fun step observer => ?_⟩
  have hstep := hselector (φ step) observer
  rwa [hφ step] at hstep

/-! ## 2. The limiting principal debt strictly exceeds the certificate scale -/

/-- **The export's `a > eta`.**  Let one player carry a maximal semantic debt at
every profile of a sequence whose debt coordinates converge to those of a point
`x` with total debt below `2 * eta`.  Under a certificate at scale `eta` that
player's limiting debt strictly exceeds `eta`.

The proof is the export's fixed-small-mixture argument.  If the limiting
principal debt were exactly `eta`, then every other limiting debt is at most
`D(x) - eta < eta`, and one fixed mixture weight `theta` pushes the mover chord
value below `eta` while the uniform `2 * M` debt bound keeps every other chord
value below `eta`, contradicting the certificate.  No attainment of any cap is
used, and no strategy convergence is inferred. -/
theorem fableRatioChamber_lt_limit_maxDebt [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (eta : ℝ) (heta : 0 < eta)
    (hcert : FableCertifiedExploitabilityFloor reward eta)
    (x : QuittingTerminalSemanticPair ι)
    (sigmas : ℕ → (quittingGame reward).BehaviorProfile) (payer : ι)
    (hmax : ∀ n observer, quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward (sigmas n)) observer ≤
      quittingTerminalSemanticDebt (quittingTerminalSemanticPair reward (sigmas n)) payer)
    (hconv : ∀ observer, Tendsto (fun n => quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward (sigmas n)) observer) atTop
      (𝓝 (quittingTerminalSemanticDebt x observer)))
    (hupper : quittingTerminalSemanticDebtSum x < 2 * eta) :
    eta < quittingTerminalSemanticDebt x payer := by
  classical
  have hsum := fableRatioChamber_tendsto_debtSum
    (fun n => quittingTerminalSemanticPair reward (sigmas n)) x hconv
  have hnonneg : ∀ observer, 0 ≤ quittingTerminalSemanticDebt x observer := fun observer =>
    ge_of_tendsto' (hconv observer) fun n => fableThinSlice_debt_nonneg reward (sigmas n) observer
  have hetaLe : eta ≤ quittingTerminalSemanticDebt x payer := by
    refine ge_of_tendsto' (hconv payer) fun n => ?_
    obtain ⟨witness, hwitness⟩ := hcert (sigmas n)
    exact hwitness.trans (hmax n witness)
  have hle : quittingTerminalSemanticDebt x payer ≤ quittingTerminalSemanticDebtSum x :=
    le_of_tendsto_of_tendsto' (hconv payer) hsum fun n =>
      fableThinSlice_debt_le_debtSum reward (sigmas n) payer
  by_contra hcontra
  rw [not_lt] at hcontra
  have hexact : quittingTerminalSemanticDebt x payer = eta := le_antisymm hcontra hetaLe
  have hetaD : eta ≤ quittingTerminalSemanticDebtSum x := hexact ▸ hle
  have hother : ∀ observer, observer ≠ payer →
      quittingTerminalSemanticDebt x observer ≤ quittingTerminalSemanticDebtSum x - eta := by
    intro observer hobserver
    have hpair : quittingTerminalSemanticDebt x observer +
        quittingTerminalSemanticDebt x payer ≤ quittingTerminalSemanticDebtSum x :=
      le_of_tendsto_of_tendsto' ((hconv observer).add (hconv payer)) hsum fun n =>
        fableDebtMinima_add_le_debtSum reward (sigmas n) observer payer hobserver
    rw [hexact] at hpair
    linarith
  have hMnonneg := quittingRewardBound_nonneg reward
  have hslack : 0 < 2 * eta - quittingTerminalSemanticDebtSum x := by linarith
  have hscale : (0 : ℝ) < 4 * (quittingRewardBound reward + 1) := by linarith
  obtain ⟨theta, hthetaDef⟩ : ∃ t : ℝ, t = min (1 / 2)
      ((2 * eta - quittingTerminalSemanticDebtSum x) /
        (4 * (quittingRewardBound reward + 1))) := ⟨_, rfl⟩
  have hthetaPos : 0 < theta := by
    rw [hthetaDef]
    exact lt_min (by norm_num) (div_pos hslack hscale)
  have hthetaHalf : theta ≤ 1 / 2 := by rw [hthetaDef]; exact min_le_left _ _
  have hthetaBound : 4 * (quittingRewardBound reward + 1) * theta ≤
      2 * eta - quittingTerminalSemanticDebtSum x := by
    have hstep : theta ≤ (2 * eta - quittingTerminalSemanticDebtSum x) /
        (4 * (quittingRewardBound reward + 1)) := by
      rw [hthetaDef]; exact min_le_right _ _
    rw [le_div_iff₀ hscale] at hstep
    linarith
  have hmoverEventually : ∀ᶠ n in atTop, (1 - theta) * quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward (sigmas n)) payer + theta * (eta / 2) < eta := by
    refine (((hconv payer).const_mul (1 - theta)).add_const _).eventually_lt
      tendsto_const_nhds ?_
    rw [hexact]
    nlinarith [mul_pos hthetaPos heta]
  have hotherEventually : ∀ᶠ n in atTop, ∀ observer, observer ≠ payer →
      (1 - theta) * quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward (sigmas n)) observer +
        theta * (2 * quittingRewardBound reward) < eta := by
    refine Filter.eventually_all.mpr fun observer => ?_
    by_cases hobserver : observer = payer
    · exact Filter.Eventually.of_forall fun n hcase => absurd hobserver hcase
    · have hlimit : (1 - theta) * quittingTerminalSemanticDebt x observer +
          theta * (2 * quittingRewardBound reward) < eta := by
        have htail := hother observer hobserver
        have hpos := hnonneg observer
        nlinarith [mul_nonneg hthetaPos.le hpos]
      exact ((((hconv observer).const_mul (1 - theta)).add_const _).eventually_lt
        tendsto_const_nhds hlimit).mono fun n hn _ => hn
  obtain ⟨n, hmoverN, hotherN⟩ := (hmoverEventually.and hotherEventually).exists
  obtain ⟨target, htarget⟩ := fableDebtMinima_exists_response_debt_lt reward (sigmas n) payer
    (zeta := eta / 2) (by linarith)
  refine fableDebtMinima_chord_not_all_lt reward eta hcert (sigmas n) payer target theta
    hthetaPos.le (by linarith) ?_ ?_
  · have hstep := mul_lt_mul_of_pos_left htarget hthetaPos
    linarith
  · intro observer hobserver
    have hstep := mul_le_mul_of_nonneg_left (fableDebtMinima_debt_le_two_mul_rewardBound reward
      (Function.update (sigmas n) payer target) observer) hthetaPos.le
    have hlate := hotherN observer hobserver
    linarith

/-! ## 3. Theorem C: the carrier/actual-source liminf port -/

/-- **The export's Theorem C output.**  A fixed payer, a strictly monotone
extraction of the supplied actual profiles, vanishing positive response errors,
and literal one-player behavioral replacements, together with the export's
(C1)-(C3).

The two limit conclusions are stated in eventually form: for every accuracy the
target total debt eventually exceeds the export's floor minus that accuracy.
This is exactly the `liminf` lower bound of (C3) and (21), stated without the
`Filter.liminf` wrapper.  No exact best response is selected and no convergence
of strategies is asserted. -/
structure FableRatioChamberPort {ι : Type} [Fintype ι] [DecidableEq ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (eta : ℝ)
    (x : QuittingTerminalSemanticPair ι)
    (sigmas : ℕ → (quittingGame reward).BehaviorProfile) where
  /-- The export's fixed maximal-debt player `p`. -/
  payer : ι
  /-- The stabilizing extraction. -/
  index : ℕ → ℕ
  /-- The export's response accuracies `zeta_n`. -/
  errors : ℕ → ℝ
  /-- The export's `zeta_n`-best complete behavioral responses. -/
  responses : ℕ → (quittingGame reward).BehaviorStrategy payer
  strictMono_index : StrictMono index
  errors_pos : ∀ k, 0 < errors k
  errors_tendsto : Tendsto errors atTop (𝓝 0)
  /-- `payer` carries a maximal semantic debt at every retained source. -/
  maxDebt : ∀ k observer, quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward (sigmas (index k))) observer ≤
    quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward (sigmas (index k))) payer
  /-- The export's `a > eta`. -/
  lt_limitDebt : eta < quittingTerminalSemanticDebt x payer
  /-- The export's `a <= D_*`. -/
  limitDebt_le : quittingTerminalSemanticDebt x payer ≤ quittingTerminalSemanticDebtSum x
  /-- The export's (13): the residual mover debt is below the accuracy. -/
  response_debt_lt : ∀ k, quittingTerminalSemanticDebt (quittingTerminalSemanticPair reward
      (Function.update (sigmas (index k)) payer (responses k))) payer < errors k
  /-- The export's (C1), with the literal one-player replacement. -/
  gain_lt : ∀ k, quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward (sigmas (index k))) payer - errors k <
      quittingTerminalPayoff reward
          (Function.update (sigmas (index k)) payer (responses k)) payer -
        quittingTerminalPayoff reward (sigmas (index k)) payer
  /-- The export's (C2), in the stronger eventual strict form. -/
  eventually_gain : ∀ᶠ k in atTop, eta < quittingTerminalPayoff reward
      (Function.update (sigmas (index k)) payer (responses k)) payer -
    quittingTerminalPayoff reward (sigmas (index k)) payer
  /-- The export's (C3), in eventually form. -/
  eventually_debtSum : ∀ epsilon > 0, ∀ᶠ k in atTop,
    quittingTerminalSemanticDebtSum x + quittingTerminalSemanticDebt x payer *
        (2 * eta - quittingTerminalSemanticDebtSum x) /
        (quittingTerminalSemanticDebt x payer - eta) - epsilon <
      quittingTerminalSemanticDebtSum (quittingTerminalSemanticPair reward
        (Function.update (sigmas (index k)) payer (responses k)))
  /-- The export's ratio closing (21), in eventually form. -/
  eventually_ratio : ∀ epsilon > 0, ∀ᶠ k in atTop,
    quittingTerminalSemanticDebtSum x + quittingTerminalSemanticDebtSum x *
        (2 * eta - quittingTerminalSemanticDebtSum x) /
        (quittingTerminalSemanticDebtSum x - eta) - epsilon <
      quittingTerminalSemanticDebtSum (quittingTerminalSemanticPair reward
        (Function.update (sigmas (index k)) payer (responses k)))

/-- **Theorem C.**  Under a certificate at scale `eta`, a point `x` whose debt
coordinates are limits of those of a sequence of actual profiles and whose total
debt is below `2 * eta` carries the export's whole ratio-chamber port package.

The export's lower chamber bound `eta < D(x)` is *not* assumed: it is a
consequence, since the stabilized payer's limiting debt lies strictly between
`eta` and `D(x)`.  Minimality of `D(x)` on the carrier is not used either. -/
theorem fableRatioChamber_nonempty_port [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (eta : ℝ) (heta : 0 < eta)
    (hcert : FableCertifiedExploitabilityFloor reward eta)
    (x : QuittingTerminalSemanticPair ι)
    (sigmas : ℕ → (quittingGame reward).BehaviorProfile)
    (hconv : ∀ observer, Tendsto (fun n => quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward (sigmas n)) observer) atTop
      (𝓝 (quittingTerminalSemanticDebt x observer)))
    (hupper : quittingTerminalSemanticDebtSum x < 2 * eta) :
    Nonempty (FableRatioChamberPort reward eta x sigmas) := by
  classical
  obtain ⟨payer, base, hbaseMono, hbaseMax⟩ :=
    fableRatioChamber_exists_strictMono_maxDebt reward sigmas
  have hbaseConv : ∀ observer, Tendsto (fun k => quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward (sigmas (base k))) observer) atTop
      (𝓝 (quittingTerminalSemanticDebt x observer)) := fun observer =>
    (hconv observer).comp hbaseMono.tendsto_atTop
  have hbaseSum := fableRatioChamber_tendsto_debtSum
    (fun k => quittingTerminalSemanticPair reward (sigmas (base k))) x hbaseConv
  have hlt : eta < quittingTerminalSemanticDebt x payer :=
    fableRatioChamber_lt_limit_maxDebt reward eta heta hcert x (fun k => sigmas (base k))
      payer hbaseMax hbaseConv hupper
  have hleD : quittingTerminalSemanticDebt x payer ≤ quittingTerminalSemanticDebtSum x :=
    le_of_tendsto_of_tendsto' (hbaseConv payer) hbaseSum fun k =>
      fableThinSlice_debt_le_debtSum reward (sigmas (base k)) payer
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    (hbaseSum.eventually_lt tendsto_const_nhds hupper)
  obtain ⟨index, hindexDef⟩ : ∃ f : ℕ → ℕ, f = fun k => base (k + N) := ⟨_, rfl⟩
  have hindexMono : StrictMono index := by
    rw [hindexDef]
    exact hbaseMono.comp fun a b hab => by omega
  have hindexMax : ∀ k observer, quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward (sigmas (index k))) observer ≤
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward (sigmas (index k))) payer := by
    intro k observer
    rw [hindexDef]
    exact hbaseMax (k + N) observer
  have hindexThreshold : ∀ k, quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward (sigmas (index k))) < 2 * eta := by
    intro k
    rw [hindexDef]
    exact hN (k + N) (by omega)
  have hindexConv : ∀ observer, Tendsto (fun k => quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward (sigmas (index k))) observer) atTop
      (𝓝 (quittingTerminalSemanticDebt x observer)) := fun observer =>
    (hconv observer).comp hindexMono.tendsto_atTop
  have hindexSum := fableRatioChamber_tendsto_debtSum
    (fun k => quittingTerminalSemanticPair reward (sigmas (index k))) x hindexConv
  obtain ⟨zetas, hzetasDef⟩ : ∃ z : ℕ → ℝ, z = fun k : ℕ => min eta (1 / ((k : ℝ) + 1)) := ⟨_, rfl⟩
  have hzetasPos : ∀ k, 0 < zetas k := by
    intro k
    rw [hzetasDef]
    exact lt_min heta (by positivity)
  have hzetasLe : ∀ k, zetas k ≤ eta := by
    intro k
    rw [hzetasDef]
    exact min_le_left _ _
  have hzetasTendsto : Tendsto zetas atTop (𝓝 0) := by
    rw [hzetasDef]
    refine squeeze_zero (fun k => le_of_lt (lt_min heta (by positivity)))
      (fun k => min_le_right _ _) ?_
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have hchoice : ∀ k, ∃ target : (quittingGame reward).BehaviorStrategy payer,
      quittingTerminalSemanticDebt (quittingTerminalSemanticPair reward
          (Function.update (sigmas (index k)) payer target)) payer < zetas k ∧
        quittingTerminalSemanticDebtSum
              (quittingTerminalSemanticPair reward (sigmas (index k))) +
            (quittingTerminalSemanticDebt
                (quittingTerminalSemanticPair reward (sigmas (index k))) payer - zetas k) *
              (2 * eta - quittingTerminalSemanticDebtSum
                (quittingTerminalSemanticPair reward (sigmas (index k)))) /
              (quittingTerminalSemanticDebt
                (quittingTerminalSemanticPair reward (sigmas (index k))) payer - eta) ≤
          quittingTerminalSemanticDebtSum (quittingTerminalSemanticPair reward
            (Function.update (sigmas (index k)) payer target)) := fun k =>
    fableDebtPort_exists_response_debtSum_le reward eta heta hcert (sigmas (index k)) payer
      (hindexMax k) (hindexThreshold k) (zetas k) (hzetasPos k) (hzetasLe k)
  choose responses hresponseLt hresponsePort using hchoice
  have hport : Tendsto (fun k =>
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward (sigmas (index k))) +
        (quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward (sigmas (index k))) payer - zetas k) *
          (2 * eta - quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPair reward (sigmas (index k)))) /
          (quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward (sigmas (index k))) payer - eta)) atTop
      (𝓝 (quittingTerminalSemanticDebtSum x + quittingTerminalSemanticDebt x payer *
        (2 * eta - quittingTerminalSemanticDebtSum x) /
        (quittingTerminalSemanticDebt x payer - eta))) := by
    have hconst : Tendsto (fun _ : ℕ => 2 * eta) atTop (𝓝 (2 * eta)) := tendsto_const_nhds
    have hnum := ((hindexConv payer).sub hzetasTendsto).mul (hconst.sub hindexSum)
    have hden := (hindexConv payer).sub_const eta
    have hstep := hindexSum.add (hnum.div hden (ne_of_gt (sub_pos.mpr hlt)))
    rwa [sub_zero] at hstep
  have heventually : ∀ epsilon > 0, ∀ᶠ k in atTop,
      quittingTerminalSemanticDebtSum x + quittingTerminalSemanticDebt x payer *
          (2 * eta - quittingTerminalSemanticDebtSum x) /
          (quittingTerminalSemanticDebt x payer - eta) - epsilon <
        quittingTerminalSemanticDebtSum (quittingTerminalSemanticPair reward
          (Function.update (sigmas (index k)) payer (responses k))) := by
    intro epsilon hepsilon
    filter_upwards [tendsto_const_nhds.eventually_lt hport (sub_lt_self _ hepsilon)] with k hk
    exact hk.trans_le (hresponsePort k)
  have hratio := fableDebtPort_ratio_mono heta hlt hleD hupper
  have hgain : ∀ k, quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward (sigmas (index k))) payer - zetas k <
      quittingTerminalPayoff reward
          (Function.update (sigmas (index k)) payer (responses k)) payer -
        quittingTerminalPayoff reward (sigmas (index k)) payer := by
    intro k
    have hcap := fableThinSlice_replacement_cap_eq reward (sigmas (index k)) payer (responses k)
    have hsmall := hresponseLt k
    unfold quittingTerminalSemanticDebt quittingTerminalSemanticPair at hsmall ⊢
    simp only at hsmall ⊢
    linarith
  refine ⟨{ payer := payer, index := index, errors := zetas, responses := responses
            strictMono_index := hindexMono, errors_pos := hzetasPos
            errors_tendsto := hzetasTendsto, maxDebt := hindexMax
            lt_limitDebt := hlt, limitDebt_le := hleD
            response_debt_lt := hresponseLt, gain_lt := hgain
            eventually_gain := ?_, eventually_debtSum := heventually
            eventually_ratio := ?_ }⟩
  · have hstep : Tendsto (fun k => quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward (sigmas (index k))) payer - zetas k) atTop
        (𝓝 (quittingTerminalSemanticDebt x payer - 0)) := (hindexConv payer).sub hzetasTendsto
    filter_upwards [tendsto_const_nhds.eventually_lt hstep (by simpa using hlt)] with k hk
    exact hk.trans (hgain k)
  · intro epsilon hepsilon
    filter_upwards [heventually epsilon hepsilon] with k hk
    linarith

/-! ## 4. (C4): a carrier cluster point of the targets -/

/-- **(C4).**  A sequence of actual profiles whose total semantic debt
eventually exceeds every strict lower approximation of `floor` has a
subsequence whose semantic pairs converge to a carrier point of total debt at
least `floor`.  Only compactness of the checked carrier and continuity of total
semantic debt are used; nothing is claimed about the strategies. -/
theorem fableRatioChamber_exists_carrier_cluster
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (rhos : ℕ → (quittingGame reward).BehaviorProfile) (floor : ℝ)
    (hfloor : ∀ epsilon > 0, ∀ᶠ k in atTop, floor - epsilon <
      quittingTerminalSemanticDebtSum (quittingTerminalSemanticPair reward (rhos k))) :
    ∃ (y : QuittingTerminalSemanticPair ι) (psi : ℕ → ℕ), StrictMono psi ∧
      y ∈ quittingTerminalSemanticCarrier reward ∧
      Tendsto (fun j => quittingTerminalSemanticPair reward (rhos (psi j))) atTop (𝓝 y) ∧
      floor ≤ quittingTerminalSemanticDebtSum y := by
  have hmem : ∀ k, quittingTerminalSemanticPair reward (rhos k) ∈
      quittingTerminalSemanticCarrier reward := fun k => subset_closure ⟨rhos k, rfl⟩
  obtain ⟨y, hy, psi, hpsi, htendsto⟩ :=
    (quittingTerminalSemanticCarrier_isCompact reward).tendsto_subseq hmem
  refine ⟨y, psi, hpsi, hy, htendsto, ?_⟩
  have hsum : Tendsto (fun j => quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward (rhos (psi j)))) atTop
      (𝓝 (quittingTerminalSemanticDebtSum y)) :=
    continuous_quittingTerminalSemanticDebtSum.continuousAt.tendsto.comp htendsto
  refine le_of_forall_pos_le_add fun epsilon hepsilon => ?_
  have hlate := hpsi.tendsto_atTop.eventually (hfloor epsilon hepsilon)
  have hbound := ge_of_tendsto hsum (hlate.mono fun j hj => hj.le)
  linarith

/-- The port's own targets have a carrier cluster point carrying the export's
`D_* + Delta_port` floor. -/
theorem FableRatioChamberPort.exists_carrier_cluster
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {eta : ℝ}
    {x : QuittingTerminalSemanticPair ι}
    {sigmas : ℕ → (quittingGame reward).BehaviorProfile}
    (port : FableRatioChamberPort reward eta x sigmas) :
    ∃ (y : QuittingTerminalSemanticPair ι) (psi : ℕ → ℕ), StrictMono psi ∧
      y ∈ quittingTerminalSemanticCarrier reward ∧
      Tendsto (fun j => quittingTerminalSemanticPair reward (Function.update
        (sigmas (port.index (psi j))) port.payer (port.responses (psi j)))) atTop (𝓝 y) ∧
      quittingTerminalSemanticDebtSum x + quittingTerminalSemanticDebtSum x *
          (2 * eta - quittingTerminalSemanticDebtSum x) /
          (quittingTerminalSemanticDebtSum x - eta) ≤
        quittingTerminalSemanticDebtSum y :=
  fableRatioChamber_exists_carrier_cluster reward
    (fun k => Function.update (sigmas (port.index k)) port.payer (port.responses k)) _
    port.eventually_ratio

/-! ## 5. The two-stage actual-data adapter -/

/-- Every carrier point below the two-debtor threshold carries the port package
along an executable realizing sequence, under an inf-form certificate. -/
theorem fableRatioChamber_exists_port_of_mem_carrier [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (eta : ℝ) (heta : 0 < eta)
    (hinf : eta ≤ quittingTerminalExploitabilityInf reward)
    (x : QuittingTerminalSemanticPair ι)
    (hx : x ∈ quittingTerminalSemanticCarrier reward)
    (hupper : quittingTerminalSemanticDebtSum x < 2 * eta) :
    ∃ sigmas : ℕ → (quittingGame reward).BehaviorProfile,
      Tendsto (fun n => quittingTerminalSemanticPair reward (sigmas n)) atTop (𝓝 x) ∧
        Nonempty (FableRatioChamberPort reward eta x sigmas) := by
  obtain ⟨sigmas, hsigmas⟩ := exists_terminalProfile_sequence_tendsto_semanticPair reward x hx
  refine ⟨sigmas, hsigmas, fableRatioChamber_nonempty_port reward eta heta
    (fableRatioChamber_certifiedFloor_of_le_exploitabilityInf reward eta heta hinf) x sigmas
    (fun observer => fableRatioChamber_tendsto_debt_of_pair _ x hsigmas observer) hupper⟩

/-- **The export's two-stage adapter, item 5.**  In the ratio chamber the
incoming literal fixed-payer response edge `sigma_n -> rho_n` is retained with
all of its (C1)-(C3) data, and, separately, the checked terminal-gap
first-disagreement construction is invoked at every target `rho_n`.

The two stages are kept apart exactly as the export requires: the port's stored
gain is the chosen `gamma`, and its selected observer and paid row are not
identified with the incoming payer `port.payer`. -/
theorem fableRatioChamber_composite_adapter [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (eta gamma : ℝ) (heta : 0 < eta)
    (hgamma : 0 < gamma) (hgammaEta : gamma < eta)
    (hinf : eta ≤ quittingTerminalExploitabilityInf reward)
    (x : QuittingTerminalSemanticPair ι)
    (hx : x ∈ quittingTerminalSemanticCarrier reward)
    (hmin : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum x ≤ quittingTerminalSemanticDebtSum candidate)
    (hupper : quittingTerminalSemanticDebtSum x < 2 * eta) :
    ∃ (sigmas : ℕ → (quittingGame reward).BehaviorProfile)
        (port : FableRatioChamberPort reward eta x sigmas),
      Tendsto (fun n => quittingTerminalSemanticPair reward (sigmas n)) atTop (𝓝 x) ∧
        ∀ k, Nonempty (QuittingActualProfileTerminalGapPaidCapPort reward x
          (Function.update (sigmas (port.index k)) port.payer (port.responses k)) gamma) := by
  obtain ⟨sigmas, hsigmas, ⟨port⟩⟩ :=
    fableRatioChamber_exists_port_of_mem_carrier reward eta heta hinf x hx hupper
  have hpositive : 0 < quittingTerminalSemanticDebtSum x :=
    heta.trans (port.lt_limitDebt.trans_le port.limitDebt_le)
  have hgap : HasTerminalExploitabilityGap reward gamma :=
    hasTerminalExploitabilityGap_of_lt_quittingTerminalExploitabilityInf reward
      (hgammaEta.trans_le hinf)
  exact ⟨sigmas, port, hsigmas, fun k => hgap.nonempty_actualProfilePaidCapPort hgamma x
    hmin hpositive _⟩

/-- The composite adapter entered from failure of a uniform-equilibrium payoff.
The certificate scale is the checked terminal exploitability infimum itself, and
the ratio-chamber hypothesis is the export's `D_* < 2 * eta` stated over the
carrier minimizers. -/
theorem fableRatioChamber_composite_adapter_of_no_uniformEquilibriumPayoff [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (gamma : ℝ) (hgamma : 0 < gamma)
    (hno : ¬ ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff)
    (hgammaInf : gamma < quittingTerminalExploitabilityInf reward)
    (hchamber : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      (∀ other ∈ quittingTerminalSemanticCarrier reward,
        quittingTerminalSemanticDebtSum candidate ≤ quittingTerminalSemanticDebtSum other) →
      quittingTerminalSemanticDebtSum candidate <
        2 * quittingTerminalExploitabilityInf reward) :
    ∃ (minimum : QuittingTerminalSemanticPair ι)
        (sigmas : ℕ → (quittingGame reward).BehaviorProfile)
        (port : FableRatioChamberPort reward
          (quittingTerminalExploitabilityInf reward) minimum sigmas),
      minimum ∈ quittingTerminalSemanticCarrier reward ∧
        (∀ candidate ∈ quittingTerminalSemanticCarrier reward,
          quittingTerminalSemanticDebtSum minimum ≤
            quittingTerminalSemanticDebtSum candidate) ∧
        ∀ k, Nonempty (QuittingActualProfileTerminalGapPaidCapPort reward minimum
          (Function.update (sigmas (port.index k)) port.payer (port.responses k)) gamma) := by
  have heta : 0 < quittingTerminalExploitabilityInf reward :=
    quittingTerminalExploitabilityInf_pos_of_no_uniformEquilibriumPayoff reward hno
  obtain ⟨minimum, hminimum, hmin⟩ := exists_minimum_quittingTerminalSemanticDebtSum reward
  obtain ⟨sigmas, port, -, hports⟩ := fableRatioChamber_composite_adapter reward
    (quittingTerminalExploitabilityInf reward) gamma heta hgamma hgammaInf le_rfl minimum
    hminimum hmin (hchamber minimum hminimum hmin)
  exact ⟨minimum, sigmas, port, hminimum, hmin, hports⟩

end GameTheory
