/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/
import UniformEquilibrium.Quitting.Root.TerminalDebtPrefix
import UniformEquilibrium.Quitting.Root.TerminalSemanticEqualityStratum
import UniformEquilibrium.Quitting.Paths.StoppingLawMixture
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauTightness
import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.TerminalSemanticStoppingLawDebtConvexity

/-!
# Certified thin slices and the golden-ratio debtor-token obstruction

This file formalizes sections 1-3 of the note
`math/notes/SOCIAL_WEIGHT_REVIEW__CERTIFIED_THIN_SLICE_DEBT_TOKEN_ROTATION.md`.

The global input is a *hypothesis-form* exploitability certificate: some fixed
`gamma > 0` such that every actual behavior profile has at least one player
whose semantic debt is at least `gamma`.  Nothing here proves that any reward
table has such a certificate; the certificate is carried as a hypothesis.

Under that certificate the results are:

* **Thin-slice token.**  If the total debt of an actual profile is at most
  `gamma + epsilon` with `epsilon < gamma`, exactly one player carries a
  `gamma`-scale debt, and all remaining debts sum to at most `epsilon`.
* **Replacement facts.**  Replacing one player's complete strategy leaves that
  player's behavioral cap untouched, so an exact best-response replacement
  collects exactly that player's debt as prescribed-payoff gain.
* **Chord control.**  Along the complete stopping-law mixture chord between a
  source profile and its principal-debtor response, the mover's debt is exactly
  affine and every other coordinate is bounded by the chord.  Both facts are
  consumed from the production file `TerminalSemanticStoppingLawDebtConvexity`
  under `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/`; they are not
  reproved here.
* **Golden-ratio obstruction.**  If additionally
  `epsilon ^ 2 + gamma * epsilon - gamma ^ 2 < 0`, equivalently
  `epsilon / gamma < (Real.sqrt 5 - 1) / 2`, then a principal-debtor exact
  best-response target cannot stay inside the same thin slice: its total debt
  strictly exceeds `gamma + epsilon`.

The obstruction argument is a chord argument, not a rank or chronological
argument: the midpoint-like profile `sigma^theta` at
`theta = gamma / (2 * gamma + epsilon)` would have every coordinate strictly
below `gamma`, which the certificate forbids.
-/

noncomputable section

namespace GameTheory

open StochasticGame QuittingBoundaryHolonomy

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## 1. The global certificate -/

/-- Hypothesis-form global exploitability certificate at scale `gamma`: every
actual behavior profile has some player whose semantic debt is at least
`gamma`.  This is equation (2) of the note.  It is an assumption about
`reward`, never established here. -/
def FableCertifiedExploitabilityFloor
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (gamma : ℝ) : Prop :=
  ∀ profile : (quittingGame reward).BehaviorProfile,
    ∃ who, gamma ≤ quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward profile) who

omit [DecidableEq ι] in
/-- A positive lower bound on the checked maximum-coordinate exploitability
functional supplies the certificate's per-profile existential form. -/
theorem fableThinSlice_exists_debt_ge_of_exploitability [Nonempty ι]
    (pair : QuittingTerminalSemanticPair ι) (gamma : ℝ) (hgamma : 0 < gamma)
    (hexploit : gamma ≤ quittingTerminalSemanticExploitability pair) :
    ∃ who, gamma ≤ quittingTerminalSemanticDebt pair who := by
  obtain ⟨who, -, hwho⟩ :=
    Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := ι))
      (fun who => max 0 (quittingTerminalSemanticDebt pair who))
  have hmax : gamma ≤ max 0 (quittingTerminalSemanticDebt pair who) :=
    le_trans hexploit hwho.le
  refine ⟨who, ?_⟩
  rcases le_or_gt gamma (quittingTerminalSemanticDebt pair who) with hle | hlt
  · exact hle
  · exfalso
    rcases max_cases 0 (quittingTerminalSemanticDebt pair who) with
      ⟨heq, -⟩ | ⟨heq, -⟩
    · rw [heq] at hmax
      linarith
    · rw [heq] at hmax
      linarith

/-- Every coordinate of the semantic debt of an *actual* profile is
nonnegative: the player's own prescribed strategy is one of the deviations the
behavioral cap ranges over. -/
theorem fableThinSlice_debt_nonneg
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι) :
    0 ≤ quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward profile) who :=
  quittingTerminalDeviationDebt_nonneg reward profile who

/-- One nonnegative debt coordinate is bounded by the total debt. -/
theorem fableThinSlice_debt_le_debtSum
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward profile) who ≤
      quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward profile) := by
  unfold quittingTerminalSemanticDebtSum
  exact Finset.single_le_sum
    (fun i _ => fableThinSlice_debt_nonneg reward profile i) (Finset.mem_univ who)

/-! ## 2. The thin-slice debtor token -/

/-- Equation (7).  Subtracting a `gamma`-scale coordinate from a
`gamma + epsilon` slice bound leaves at most `epsilon` for all other
players. -/
theorem fableThinSlice_sum_erase_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (gamma epsilon : ℝ) (principal : ι)
    (hslice : quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward profile) ≤ gamma + epsilon)
    (hprincipal : gamma ≤ quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward profile) principal) :
    ∑ who ∈ Finset.univ.erase principal,
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward profile) who ≤ epsilon := by
  have hsplit := Finset.add_sum_erase Finset.univ
    (fun who => quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward profile) who)
    (Finset.mem_univ principal)
  unfold quittingTerminalSemanticDebtSum at hslice
  linarith

/-- Coordinatewise form of (7): away from a `gamma`-scale debtor every debt in
the thin slice is at most `epsilon`. -/
theorem fableThinSlice_debt_le_of_ne_principal
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (gamma epsilon : ℝ) (principal : ι)
    (hslice : quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward profile) ≤ gamma + epsilon)
    (hprincipal : gamma ≤ quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward profile) principal)
    (who : ι) (hwho : who ≠ principal) :
    quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward profile) who ≤ epsilon := by
  have hmem : who ∈ Finset.univ.erase principal :=
    Finset.mem_erase.mpr ⟨hwho, Finset.mem_univ who⟩
  have hsingle := Finset.single_le_sum
    (f := fun i => quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward profile) i)
    (fun i _ => fableThinSlice_debt_nonneg reward profile i) hmem
  have htail := fableThinSlice_sum_erase_le reward profile gamma epsilon principal
    hslice hprincipal
  linarith

/-- **Thin-slice debtor token**, equation (6).  Under the certificate, an
actual profile in a slice of width `epsilon < gamma` above `gamma` has exactly
one `gamma`-scale debtor. -/
theorem fableThinSlice_existsUnique_principalDebtor
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (gamma epsilon : ℝ) (hthin : epsilon < gamma)
    (hcert : FableCertifiedExploitabilityFloor reward gamma)
    (profile : (quittingGame reward).BehaviorProfile)
    (hslice : quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward profile) ≤ gamma + epsilon) :
    ∃! principal, gamma ≤ quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward profile) principal := by
  obtain ⟨principal, hprincipal⟩ := hcert profile
  refine ⟨principal, hprincipal, ?_⟩
  intro other hother
  by_contra hne
  have hsmall := fableThinSlice_debt_le_of_ne_principal reward profile gamma epsilon
    principal hslice hprincipal other hne
  linarith

/-! ## 2b. Exact best-response replacement -/

/-- Own-update cap invariance, restated for readability.  This is the
production theorem `quittingContinuationBestResponseValue_update_self`. -/
theorem fableThinSlice_replacement_cap_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (mover : ι)
    (target : (quittingGame reward).BehaviorStrategy mover) :
    quittingContinuationBestResponseValue reward
        (Function.update profile mover target) mover =
      quittingContinuationBestResponseValue reward profile mover :=
  quittingContinuationBestResponseValue_update_self reward profile mover target

/-- Equation (8).  An exact behavioral best-response replacement by one player
gains exactly that player's semantic debt at the source profile, because the
replacement does not move that player's cap. -/
theorem fableThinSlice_replacement_payoff_gain
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (mover : ι)
    (target : (quittingGame reward).BehaviorStrategy mover)
    (hbest : quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward
        (Function.update profile mover target)) mover = 0) :
    quittingTerminalPayoff reward (Function.update profile mover target) mover -
        quittingTerminalPayoff reward profile mover =
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward profile) mover := by
  have hcap := fableThinSlice_replacement_cap_eq reward profile mover target
  unfold quittingTerminalSemanticDebt quittingTerminalSemanticPair at hbest ⊢
  simp only at hbest ⊢
  linarith

/-- Equation (9).  In a thin slice, every exact best-response replacement made
by a player other than the principal debtor gains at most `epsilon`. -/
theorem fableThinSlice_nonPrincipal_replacement_gain_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (gamma epsilon : ℝ) (principal : ι)
    (hslice : quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward profile) ≤ gamma + epsilon)
    (hprincipal : gamma ≤ quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward profile) principal)
    (mover : ι) (hmover : mover ≠ principal)
    (target : (quittingGame reward).BehaviorStrategy mover)
    (hbest : quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward
        (Function.update profile mover target)) mover = 0) :
    quittingTerminalPayoff reward (Function.update profile mover target) mover -
        quittingTerminalPayoff reward profile mover ≤ epsilon := by
  rw [fableThinSlice_replacement_payoff_gain reward profile mover target hbest]
  exact fableThinSlice_debt_le_of_ne_principal reward profile gamma epsilon
    principal hslice hprincipal mover hmover

/-- Equation (12).  A principal-debtor exact response either leaves the
certified thin slice quantitatively, or moves the whole `gamma`-scale debtor
token to a different player. -/
theorem fableThinSlice_response_exits_or_rotates
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (gamma epsilon : ℝ) (hgamma : 0 < gamma)
    (hcert : FableCertifiedExploitabilityFloor reward gamma)
    (profile : (quittingGame reward).BehaviorProfile) (principal : ι)
    (target : (quittingGame reward).BehaviorStrategy principal)
    (hbest : quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward
        (Function.update profile principal target)) principal = 0) :
    gamma + epsilon < quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward
          (Function.update profile principal target)) ∨
      ∃ rotated, rotated ≠ principal ∧
        gamma ≤ quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (Function.update profile principal target)) rotated ∧
        ∑ who ∈ Finset.univ.erase rotated,
            quittingTerminalSemanticDebt
              (quittingTerminalSemanticPair reward
                (Function.update profile principal target)) who ≤ epsilon := by
  by_cases hexit : gamma + epsilon < quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward
        (Function.update profile principal target))
  · exact Or.inl hexit
  · rw [not_lt] at hexit
    obtain ⟨rotated, hrotated⟩ := hcert (Function.update profile principal target)
    refine Or.inr ⟨rotated, ?_, hrotated, ?_⟩
    · rintro rfl
      rw [hbest] at hrotated
      linarith
    · exact fableThinSlice_sum_erase_le reward
        (Function.update profile principal target) gamma epsilon rotated hexit hrotated

/-! ## 3. The stopping-law chord and the golden-ratio obstruction -/

/-- The chord profile `sigma^theta`: only `mover`'s coordinate changes, and it
is replaced by the behavioral realization of the convex mixture of its own
*complete* stopping law with the complete stopping law of `target`. -/
def fableThinSliceChordProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (mover : ι)
    (target : (quittingGame reward).BehaviorStrategy mover)
    (theta : ℝ) (htheta0 : 0 ≤ theta) (htheta1 : theta ≤ 1) :
    (quittingGame reward).BehaviorProfile :=
  Function.update profile mover
    (quittingStoppingLawMixtureBehaviorStrategy reward mover (profile mover) target
      theta htheta0 htheta1)

@[simp] theorem fableThinSliceChordProfile_apply_of_ne
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (mover : ι)
    (target : (quittingGame reward).BehaviorStrategy mover)
    (theta : ℝ) (htheta0 : 0 ≤ theta) (htheta1 : theta ≤ 1)
    (who : ι) (hwho : who ≠ mover) :
    fableThinSliceChordProfile reward profile mover target theta htheta0 htheta1 who =
      profile who := by
  unfold fableThinSliceChordProfile
  exact Function.update_of_ne hwho _ _

/-- **Chord, mover coordinate.**  The moved player's debt is exactly affine
along the chord.  Consumed from
`quittingTerminalSemanticDebt_stoppingLawMixture_eq_self`. -/
theorem fableThinSliceChord_debt_mover_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (mover : ι)
    (target : (quittingGame reward).BehaviorStrategy mover)
    (theta : ℝ) (htheta0 : 0 ≤ theta) (htheta1 : theta ≤ 1) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (fableThinSliceChordProfile reward profile mover target theta htheta0
            htheta1)) mover =
      (1 - theta) * quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward profile) mover +
        theta * quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (Function.update profile mover target)) mover := by
  have haffine := quittingTerminalSemanticDebt_stoppingLawMixture_eq_self
    reward profile mover (profile mover) target theta htheta0 htheta1
  rw [Function.update_eq_self] at haffine
  exact haffine

/-- **Chord, every coordinate.**  No coordinate of the debt rises above the
chord between the two endpoint profiles.  Consumed from
`quittingTerminalSemanticDebt_stoppingLawMixture_le`. -/
theorem fableThinSliceChord_debt_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (mover : ι)
    (target : (quittingGame reward).BehaviorStrategy mover)
    (theta : ℝ) (htheta0 : 0 ≤ theta) (htheta1 : theta ≤ 1) (observer : ι) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (fableThinSliceChordProfile reward profile mover target theta htheta0
            htheta1)) observer ≤
      (1 - theta) * quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward profile) observer +
        theta * quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (Function.update profile mover target)) observer := by
  have hconvex := quittingTerminalSemanticDebt_stoppingLawMixture_le
    reward profile mover observer (profile mover) target theta htheta0 htheta1
  rw [Function.update_eq_self] at hconvex
  exact hconvex

/-- Equation (15).  Against an exact best-response target the mover's debt
decays exactly linearly along the chord. -/
theorem fableThinSliceChord_debt_mover_eq_of_bestResponse
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (mover : ι)
    (target : (quittingGame reward).BehaviorStrategy mover)
    (theta : ℝ) (htheta0 : 0 ≤ theta) (htheta1 : theta ≤ 1)
    (hbest : quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward
        (Function.update profile mover target)) mover = 0) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (fableThinSliceChordProfile reward profile mover target theta htheta0
            htheta1)) mover =
      (1 - theta) * quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward profile) mover := by
  rw [fableThinSliceChord_debt_mover_eq reward profile mover target theta htheta0
    htheta1, hbest]
  ring

/-- **Golden-ratio debtor-token obstruction**, equation (22).

Under a `gamma`-scale exploitability certificate, if an actual profile lies in
the thin slice `D <= gamma + epsilon`, if `principal` is a `gamma`-scale
debtor there, and if `target` is an exact behavioral best response for
`principal` against the unchanged opponents, then the resulting profile leaves
the slice.

The width hypothesis `epsilon ^ 2 + gamma * epsilon - gamma ^ 2 < 0` is
equation (21), that is `epsilon / gamma < (Real.sqrt 5 - 1) / 2`, the
reciprocal golden ratio.  In particular the exact token rotation (13) is
impossible. -/
theorem fableThinSlice_principalDebtor_response_exits_slice
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (gamma epsilon : ℝ) (hgamma : 0 < gamma) (hepsilon : 0 ≤ epsilon)
    (hgolden : epsilon ^ 2 + gamma * epsilon - gamma ^ 2 < 0)
    (hcert : FableCertifiedExploitabilityFloor reward gamma)
    (profile : (quittingGame reward).BehaviorProfile)
    (hslice : quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward profile) ≤ gamma + epsilon)
    (principal : ι)
    (hprincipal : gamma ≤ quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward profile) principal)
    (target : (quittingGame reward).BehaviorStrategy principal)
    (hbest : quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward
        (Function.update profile principal target)) principal = 0) :
    gamma + epsilon < quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward
        (Function.update profile principal target)) := by
  by_contra hcontra
  rw [not_lt] at hcontra
  -- The golden-ratio width hypothesis already forces a thin slice.
  have hthin : epsilon < gamma := by nlinarith
  -- The response also lies in the slice, so it too has a principal debtor,
  -- and that debtor is not `principal`, whose debt there is zero.
  obtain ⟨rotated, hrotated⟩ := hcert (Function.update profile principal target)
  have hrotatedNe : rotated ≠ principal := by
    rintro rfl
    rw [hbest] at hrotated
    linarith
  have hsourceOther : ∀ who, who ≠ principal →
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward profile) who ≤ epsilon :=
    fun who hwho => fableThinSlice_debt_le_of_ne_principal reward profile gamma
      epsilon principal hslice hprincipal who hwho
  have hresponseOther : ∀ who, who ≠ rotated →
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (Function.update profile principal target)) who ≤ epsilon :=
    fun who hwho => fableThinSlice_debt_le_of_ne_principal reward
      (Function.update profile principal target) gamma epsilon rotated hcontra
      hrotated who hwho
  have hsourcePrincipal :
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward profile) principal ≤ gamma + epsilon :=
    le_trans (fableThinSlice_debt_le_debtSum reward profile principal) hslice
  have hresponseRotated :
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (Function.update profile principal target)) rotated ≤ gamma + epsilon :=
    le_trans (fableThinSlice_debt_le_debtSum reward
      (Function.update profile principal target) rotated) hcontra
  -- The balancing chord parameter, equation (19).
  have hden : 0 < 2 * gamma + epsilon := by linarith
  obtain ⟨theta, htheta⟩ :
      ∃ t : ℝ, t = gamma / (2 * gamma + epsilon) := ⟨_, rfl⟩
  have htheta0 : 0 ≤ theta := by
    rw [htheta]
    exact div_nonneg hgamma.le hden.le
  have htheta1 : theta ≤ 1 := by
    rw [htheta, div_le_one hden]
    linarith
  have hthetaMul : theta * (2 * gamma + epsilon) = gamma := by
    rw [htheta]
    field_simp
  -- Equation (20): the two endpoint bounds coincide at this `theta`.
  have hcommon : (1 - theta) * (gamma + epsilon) = epsilon + theta * gamma := by
    linear_combination (-1 : ℝ) * hthetaMul
  -- Equation (21): the common value is strictly below the certificate scale.
  have hpositive : 0 < gamma ^ 2 - gamma * epsilon - epsilon ^ 2 := by linarith
  have hfactored :
      (gamma - epsilon - theta * gamma) * (2 * gamma + epsilon) =
        gamma ^ 2 - gamma * epsilon - epsilon ^ 2 := by
    linear_combination (-gamma) * hthetaMul
  have hstrict : epsilon + theta * gamma < gamma := by
    nlinarith [hfactored, hpositive, hden]
  have honeSub : 0 ≤ 1 - theta := by linarith
  -- Every coordinate of the chord profile is strictly below `gamma`.
  have hmover :
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (fableThinSliceChordProfile reward profile principal target theta htheta0
            htheta1)) principal < gamma := by
    rw [fableThinSliceChord_debt_mover_eq_of_bestResponse reward profile principal
      target theta htheta0 htheta1 hbest]
    nlinarith [hsourcePrincipal, honeSub, hcommon, hstrict]
  have hrotatedBound :
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (fableThinSliceChordProfile reward profile principal target theta htheta0
            htheta1)) rotated < gamma := by
    have hchord := fableThinSliceChord_debt_le reward profile principal target theta
      htheta0 htheta1 rotated
    have hsource := hsourceOther rotated hrotatedNe
    nlinarith [hchord, hsource, hresponseRotated, honeSub, htheta0, hcommon, hstrict]
  have hother : ∀ who, who ≠ principal → who ≠ rotated →
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (fableThinSliceChordProfile reward profile principal target theta htheta0
            htheta1)) who < gamma := by
    intro who hwhoPrincipal hwhoRotated
    have hchord := fableThinSliceChord_debt_le reward profile principal target theta
      htheta0 htheta1 who
    have hsource := hsourceOther who hwhoPrincipal
    have hresponse := hresponseOther who hwhoRotated
    have hthetaGamma : 0 ≤ theta * gamma := mul_nonneg htheta0 hgamma.le
    nlinarith [hchord, hsource, hresponse, honeSub, htheta0, hstrict, hthetaGamma]
  -- The certificate at the chord profile is contradicted.
  obtain ⟨witness, hwitness⟩ := hcert
    (fableThinSliceChordProfile reward profile principal target theta htheta0 htheta1)
  by_cases hwitnessPrincipal : witness = principal
  · subst hwitnessPrincipal
    linarith
  · by_cases hwitnessRotated : witness = rotated
    · subst hwitnessRotated
      linarith
    · linarith [hother witness hwitnessPrincipal hwitnessRotated]

end GameTheory
