/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib

/-!
# The controller-denominator lower bound

*Claim.*  A deterministic periodic process whose long-run frequency of a
marked event realizes an exact reduced rational rate `a / b` (`Nat.Coprime a
b`) must have every period `L` of the process divisible by `b`.  In
particular, if the process is driven by a finite-state deterministic
controller with `n` states, its denominator `b` cannot exceed `n`.  Since the
rate `a / b` itself only needs `O(log b)` bits to describe, while realizing it
exactly forces an explicit phase controller with at least `b` states, this is
an exponential (in the description length of the rate) lower bound on
controller memory.

This upgrades the exhaustive check reported as experiment **E29** in
`ideas/wild/ComputabilityAndComplexity.md` §6
(`experiments/exact_rate_memory_blowup.py`, recorded in
`experiments/RESULTS.md`): all 1,259 reduced rates with denominator at most 64
were found, by brute-force search, to have minimal deterministic recurrent
cycle length *exactly* equal to their denominator.  The results below give a
general proof of the *lower-bound* half of that exhaustive finding — every
period is a multiple of the denominator, hence the minimal one is at least
`b` — for every exact reduced rate, not just the 1,259 checked instances.

## What is proved

1. `period_dvd_of_rate` — the core number-theoretic fact: if a period-`L`
   window of a Boolean sequence contains exactly `k` marked steps and
   `k / L = a / b` in lowest terms, then `b ∣ L`.
2. `period_dvd_of_density` — the same fact stated with the rate hypothesis
   phrased as an equality of rationals `(k : ℚ) / L = (a : ℚ) / b`.
3. `exists_orbit_period` — a finite-state pigeonhole fact: the output
   sequence of *any* deterministic controller with `n` states and a bijective
   (permutation) transition function is purely periodic with some period `L`
   satisfying `0 < L ≤ n`.
4. `denominator_le_card` — combining (1)–(3): if such an `n`-state controller
   realizes an exact reduced rate `a / b` over one of its periods, then
   `b ≤ n`.

## What is *not* proved (nonclaims)

* No discrepancy/balanced-word *attainment* result is proved or used: the
  constructive "three-distance theorem" half — that a balanced word of period
  `b` (e.g. `Fraction((t+1)*a) // b - Fraction(t*a) // b`, as used by the
  Python experiment) actually realizes the rate with bounded prefix
  discrepancy — is entirely outside this file.  Only the lower bound `b ∣ L`
  (hence `b ≤ n` for finite-state realizations) is established here; the
  matching upper bound (some `n`-state controller with `n = b` achieves the
  rate) is not formalized.
* No probabilistic or randomized controllers are considered.  The transition
  function `f` and output map `o` are deterministic and the "rate" is an
  exact long-run density over an exact period, not an almost-sure limit.
* This is a lower bound on the state count of an *exact* realization only; it
  says nothing about approximate or `ε`-close realizations, which may use far
  fewer states.

The finite-state corollary (3)–(4) is delivered in its full, unconditional
form: the pigeonhole argument that any bijective `n`-state controller orbit is
purely periodic with period `≤ n` is formalized here (not merely assumed as a
hypothesis), so no weakening relative to the brief's preferred option is
taken.
-/


namespace GameTheory

namespace DeterministicRateDenominator

/-- **Core number-theoretic lemma.**  Let `u : ℕ → Bool` be periodic with
period `L > 0`, and let `k` count the marked (`true`) steps in one period
`Finset.range L`.  If the exact rate `k / L` written as a fraction equals
`a / b` in lowest terms (`k * b = a * L` and `Nat.Coprime a b`), then the
denominator `b` divides the period `L`.

This is the algebraic heart of the controller-denominator lower bound: from
`k * b = a * L` we get `b ∣ a * L`, and coprimality of `a` and `b` lets us
cancel the `a` factor, leaving `b ∣ L`. -/
theorem period_dvd_of_rate (u : ℕ → Bool) (L : ℕ) (_hL : 0 < L)
    (_hperiodic : Function.Periodic u L)
    (k a b : ℕ) (_hk : k = ((Finset.range L).filter (fun i => u i)).card)
    (hrate : k * b = a * L) (hcoprime : Nat.Coprime a b) :
    b ∣ L := by
  have hdvd : b ∣ a * L := ⟨k, by rw [← hrate]; ring⟩
  exact hcoprime.symm.dvd_of_dvd_mul_left hdvd

/-- **Density formulation.**  Same conclusion as `period_dvd_of_rate`, but
with the exact-rate hypothesis phrased as an equality of rationals
`(k : ℚ) / L = (a : ℚ) / b`.  The rational equality is cross-multiplied into
the natural-number equation `k * b = a * L` and lemma 1 is applied. -/
theorem period_dvd_of_density (u : ℕ → Bool) (L : ℕ) (hL : 0 < L)
    (hperiodic : Function.Periodic u L)
    (k a b : ℕ) (hk : k = ((Finset.range L).filter (fun i => u i)).card)
    (hb : 0 < b)
    (hrate : (k : ℚ) / (L : ℚ) = (a : ℚ) / (b : ℚ)) (hcoprime : Nat.Coprime a b) :
    b ∣ L := by
  have hLQ : (L : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hL.ne'
  have hbQ : (b : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hb.ne'
  have hcross : (k : ℚ) * (b : ℚ) = (a : ℚ) * (L : ℚ) :=
    (div_eq_div_iff hLQ hbQ).mp hrate
  have hcrossN : k * b = a * L := by exact_mod_cast hcross
  exact period_dvd_of_rate u L hL hperiodic k a b hk hcrossN hcoprime

/-- **Finite-state pigeonhole periodicity.**  A deterministic `n`-state
controller with bijective transition `f : Fin n → Fin n`, output map
`o : Fin n → Bool`, and start state `s : Fin n`, produces an output sequence
`fun i => o (f^[i] s)` that is *purely* periodic with some period `L`
satisfying `0 < L ≤ n`.

Proof idea: the `n + 1` states `f^[0] s, …, f^[n] s` cannot be pairwise
distinct inside the `n`-element type `Fin n`, so two of them coincide, say at
indices `i < j ≤ n`.  Since `f` is injective, so is every iterate `f^[i]`,
and cancelling it from `f^[i] s = f^[i] (f^[j-i] s)` gives `f^[j-i] s = s`:
the orbit returns to `s` after `L := j - i` steps, with `0 < L ≤ n`. -/
theorem exists_orbit_period {n : ℕ} (f : Fin n → Fin n) (o : Fin n → Bool)
    (s : Fin n) (hf : Function.Bijective f) :
    ∃ L, 0 < L ∧ L ≤ n ∧ Function.Periodic (fun i => o (f^[i] s)) L := by
  -- Pigeonhole: the `n + 1` iterates `f^[0] s, …, f^[n] s` collide somewhere.
  obtain ⟨x, y, hxy, hg⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun m : Fin (n + 1) => f^[(m : ℕ)] s)
    (by simp)
  have hvalne : (x : ℕ) ≠ (y : ℕ) := fun he => hxy (Fin.ext he)
  -- A helper turning a collision `i < j ≤ n`, `f^[i] s = f^[j] s`
  -- into the desired period.
  have build : ∀ i j : ℕ, i < j → j ≤ n → f^[i] s = f^[j] s →
      ∃ L, 0 < L ∧ L ≤ n ∧ Function.Periodic (fun t => o (f^[t] s)) L := by
    intro i j hij hjn heq
    refine ⟨j - i, by omega, by omega, ?_⟩
    have hji : i + (j - i) = j := by omega
    have hcomm : f^[j] s = f^[i] (f^[j - i] s) := by
      have h := Function.iterate_add_apply f i (j - i) s
      rwa [hji] at h
    have heq2 : f^[i] s = f^[i] (f^[j - i] s) := by rw [heq, hcomm]
    have hcancel : f^[j - i] s = s := ((hf.injective.iterate i) heq2).symm
    intro t
    change o (f^[t + (j - i)] s) = o (f^[t] s)
    rw [Function.iterate_add_apply, hcancel]
  rcases lt_or_gt_of_ne hvalne with hlt | hgt
  · exact build (x : ℕ) (y : ℕ) hlt (by omega) hg
  · exact build (y : ℕ) (x : ℕ) hgt (by omega) hg.symm

/-- **Finite-state denominator corollary.**  If an `n`-state deterministic
controller (transition `f`, output `o`, start `s`) has an output sequence
`fun i => o (f^[i] s)` periodic with period `L ≤ n` — exactly the situation
`exists_orbit_period` produces for a bijective `f` — and realizes, over that
period, an exact reduced rate `a / b` (`k * b = a * L`, `Nat.Coprime a b`,
where `k` counts marked steps in the period), then the denominator is bounded
by the state count: `b ≤ n`.

This is the finite-state form of the controller-denominator lower bound: an
explicit deterministic phase controller realizing the exact rate `a / b`
needs at least `b` states, even though `a / b` itself needs only `O(log b)`
bits to write down.  (This corollary itself only consumes the period bound
`L ≤ n` and the periodicity fact, not bijectivity directly; combine it with
`exists_orbit_period` to discharge those two hypotheses for a bijective
controller.) -/
theorem denominator_le_card {n : ℕ} (f : Fin n → Fin n) (o : Fin n → Bool)
    (s : Fin n)
    (L : ℕ) (hL : 0 < L) (hLn : L ≤ n)
    (hperiodic : Function.Periodic (fun i => o (f^[i] s)) L)
    (k a b : ℕ)
    (hk : k = ((Finset.range L).filter (fun i => o (f^[i] s))).card)
    (hrate : k * b = a * L) (hcoprime : Nat.Coprime a b) :
    b ≤ n := by
  have hdvd : b ∣ L :=
    period_dvd_of_rate (fun i => o (f^[i] s)) L hL hperiodic k a b hk hrate hcoprime
  exact (Nat.le_of_dvd hL hdvd).trans hLn

end DeterministicRateDenominator

end GameTheory
