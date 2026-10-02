# Export gate: Fin4 minimum joint law has a finite atom

**Reviewer:** `CODEX_MINER`  
**Current head audited:** `41051dd`  
**Verdict:** **REVISE.**  The mathematical contraction is correct, new at the
current head, independently reviewed twice with unrestricted-deviation
falsification, and significant enough for a narrow export.  The draft is not
yet a complete export packet because its Fin4 corollary is not stated with
exact quantifiers, its causal-consumer paragraph skips the checked
minimum-to-infimum adapter, and two mandatory packet audits are only implicit.
All defects are local proof-writing/packaging repairs; I found no counterexample
to the theorem.

## Claim gated

The packet proposes two results.

1. For a finite-player joint terminal semantic/law carrier point
   `point=(z,mu)`, if `z` is a positive global minimizer of ordinary semantic
   debt and every player is punishment-normal, then `mu none=1` implies
   `z.1=0`, strictly negative own-singleton rewards, exact unrestricted
   terminal Nash of the literal all-Continue profile, and the zero uniform
   payoff.
2. For a `Fin 4` quantitative full-support hard residual, every joint-law
   lift over a global semantic minimum has a positive finite coalition
   coordinate, and that coordinate feeds the checked deep causal suffix-atom
   theorem.

Both results are correct.  The following repairs are mandatory before moving
the packet to `exports/`.

## 1. Exact statement: mandatory quantifier repair

The generic opening

```text
Let I be a finite player type ... let (z,mu) in K_r^law ...
```

is understandable but falls short of the packet gate's exact statement.  It
must spell out the data and assumptions in the same form as the declarations:

```text
I : Type, [Fintype I], [DecidableEq I]
reward : {S : Finset I // S.Nonempty} -> Payoff I
point : QuittingTerminalSemanticLawPoint I
hpoint : point ∈ quittingTerminalSemanticLawCarrier reward
z := point.1, mu := point.2
hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
  quittingTerminalSemanticDebtSum z ≤
    quittingTerminalSemanticDebtSum candidate
hpositive : 0 < quittingTerminalSemanticDebtSum z
hnormal : ∀ who,
  quittingPunishmentValue reward who ≤
    reward (quittingSingletonTerminal who) who
hpure : mu none = 1.
```

The conclusion should explicitly quantify `who` and identify the exact Nash
predicate and uniform payoff.  The theorem is valid for an empty finite player
type only vacuously because positive total debt is impossible; either retain
that genericity or assume `[Nonempty I]`, but state the choice.

The Fin4 corollary is currently only prose: “for a
`FinFourQuantitativeFullSupportHardResidual`, every joint-law lift of a
positive global minimum.”  Replace it by an exact statement quantifying

```text
reward : {S : Finset (Fin 4) // S.Nonempty} -> Payoff (Fin 4)
bound : Real
residual : FinFourQuantitativeFullSupportHardResidual reward bound
point : QuittingTerminalSemanticLawPoint (Fin 4)
hpoint : point ∈ quittingTerminalSemanticLawCarrier reward
hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
  quittingTerminalSemanticDebtSum point.1 ≤
    quittingTerminalSemanticDebtSum candidate.
```

Its conclusion is

```text
∃ terminal : {S : Finset (Fin 4) // S.Nonempty},
  0 < point.2 (some terminal).
```

Positivity of the minimum need not be an extra Fin4 assumption: derive it
from `residual.witness.not_exists_uniformEquilibriumPayoff` using the checked
infimum equivalence and minimum-value identity named in Section 4 below.  If
the author prefers to retain positivity as an explicit corollary premise,
the packet must stop saying the result applies to *every* hard-residual
minimum law without explaining this derivation.

There is also a Markdown proof typo after equation `(5)`: add the missing
closing `\]` before “Use
`terminalSemanticLawCarrier_fst_mem_carrier`.”

## 2. Generic proof and joint-law nonrealization: PASS

The law argument uses only closed carrier identities and never assumes that
`mu` is the law of one actual profile.  At the current head:

* `terminalSemanticLawCarrier_mass_mem_stdSimplex` gives coordinatewise
  nonnegativity and total mass one;
* `mu none=1`, `Fintype.sum_option`, and nonnegativity force every
  `mu (some terminal)=0`;
* `terminalSemanticLawCarrier_rewardMoment` has the exact orientation

  ```text
  quittingTerminalRewardMoment reward point.2 = point.1.1;
  ```

* the Never outcome reward is zero, hence `point.1.1=0`; and
* `terminalSemanticLawCarrier_fst_mem_carrier point hpoint` supplies the
  ordinary-carrier premise needed by the strict-singleton theorem.

Thus
`minimumTerminalSemantic_strictSingleton_of_punishmentNormal` gives

```text
reward (quittingSingletonTerminal who) who < point.1.1 who = 0
```

for every player.  The draft correctly distinguishes the possibly
nonrealized carrier law from the separate literal all-Continue profile used
after these same-table reward signs are proved.

The relevant declaration paths in the draft are current and exact:

* `TerminalSemanticResetIncidenceCapReturn.lean` for the simplex theorem;
* `TerminalSemanticResetIncidenceReturn.lean` for the reward moment;
* `TerminalSemanticResetIncidenceRatio.lean` for semantic projection; and
* `TerminalSemanticFinFourMinimumFiberIsolation.lean` for the generic strict
  singleton theorem, despite that file's FinFour name.

## 3. Unrestricted behavioral-deviation audit: PASS, one wording addition

At error zero,

```text
isεAsymptoticNash_quittingAlwaysContinue_iff reward le_rfl
```

is an equivalence with nonpositive own-singleton rewards.  Its reverse proof
uses
`quittingTerminalPayoff_update_quittingAlwaysContinue_le_max` for an
arbitrary complete behavioral replacement.  It therefore covers randomized,
history-dependent, delayed finite-time, and Never deviations.  The terminal
payoff is zero by `quittingTerminalPayoff_quittingAlwaysContinue`, and
`quittingGame_isUniformEquilibriumPayoff_of_terminalNash_exact` supplies the
uniform-payoff consumer.

To satisfy export item 3 literally, add one sentence specifying the
observation/agency model: strategies are the project's behavioral strategies
on finite public histories; a unilateral deviator replaces one player's
entire behavioral strategy, while all opponents retain literal all-Continue.
There is no controller, stationary restriction, or external correlation.
Stopping includes every finite quitting time and the infinite Never outcome.

## 4. Fin4 hard-residual and causal-consumer adapter: mandatory repair

The hard-residual step is mathematically valid:

* `residual.all_punishmentNormal` unfolds through
  `IsQuittingNormalPlayer` and `quittingSoloSelfPayoff` to exactly the generic
  same-table normality premise; and
* `residual.witness.not_exists_uniformEquilibriumPayoff` contradicts the zero
  uniform payoff in the pure-Never case.

Hence `mu none != 1`.  Simplex normalization and nonnegativity give
`mu none<1` and a positive sum of finite coordinates, so finiteness produces
the displayed terminal.  This conclusion is about the joint carrier law and
does not assert behavioral realization.

The paragraph saying the positive coordinate “directly satisfies every
hypothesis” of
`exists_deep_nearMinimum_capNashChronologies_with_causalSuffixAtom` is
incomplete.  That theorem requires, in addition to carrier membership and
positive mass,

```text
0 < quittingTerminalDebtSumInf reward
quittingTerminalSemanticDebtSum point.1 =
  quittingTerminalDebtSumInf reward.
```

Insert the exact checked bridge:

1. obtain nonexistence from
   `residual.witness.not_exists_uniformEquilibriumPayoff`;
2. obtain positive literal infimum from
   `quittingTerminalDebtSumInf_pos_iff_not_exists_uniformEquilibriumPayoff`;
3. obtain the equality (in the orientation needed by causalization) from

   ```text
   (quittingTerminalDebtSumInf_eq_terminalSemanticDebtSum_of_minimum
     point.1
     (terminalSemanticLawCarrier_fst_mem_carrier point hpoint)
     hminimum).symm;
   ```

4. then invoke
   `exists_deep_nearMinimum_capNashChronologies_with_causalSuffixAtom`.

If the packet also claims an **existential arbitrary-data adapter** producing
a minimum joint-law point, name
`exists_minimum_terminalSemanticLawCarrier_of_not_uniformPayoff` (or its
positive-infimum version
`exists_minimum_terminalSemanticLawCarrier_of_debtSumInf_pos`) instead of the
current vague phrase “compactness supplies minimum joint-law lifts.”  Those
theorems return carrier membership, global minimality, and debt equality to
the literal infimum in exactly the needed form.

With these additions, the downstream claim is exact: the atom is realized in
the literal suffix of arbitrarily deep actual source-matched cap--Nash stacks.
It is not a cap--Nash prefix row, Bellman edge, paid row, incidence
coordinate, reset, or final consumer.  The packet's existing nonclaims on
these points are correct.

## 5. Boundary tests: mandatory concrete examples

The bullet list correctly identifies logical boundaries, but export item 5
asks for exact positive and negative tests.  Add at least the following
fully explicit tests.

1. **Zero-debt boundary.**  On `Fin 4`, set every terminal reward coordinate
   to zero.  The literal all-Continue profile gives the joint carrier point
   `z=(0,0)`, `mu=delta_Never`; its semantic debt is the global minimum zero,
   every player is punishment-normal, and every singleton reward is zero,
   not strictly negative.  This shows why `D(z)>0` is essential and why pure
   Never is not excluded outside the hard residual.
2. **Mixed-Never boundary.**  On the same zero table, let one player Quit at
   date zero with probability `1/2` and otherwise Continue forever, with all
   opponents always Continue.  The actual terminal law has Never mass `1/2`
   and singleton mass `1/2`; thus the finite-atom conclusion follows from
   normalization as soon as Never mass is strictly below one, independently
   of the singleton-separation theorem.

These examples are exact and test precisely the two law boundaries used in
the proof.  If punishment normality is advertised as essential beyond its use
in the checked theorem, either give an exact counterexample after dropping it
or soften the wording to “required by the present strict-singleton adapter.”

## 6. Novelty and source correspondence: PASS after two additions

A narrow declaration search at head `41051dd` found all ingredients but no
theorem composing pure-Never law mass, reward moment, minimum-fiber singleton
separation, and the unrestricted all-Continue compiler.  The checked
`QuittingMinimumLawNeverOrCausalAtomDispatch` returns

```text
0 < point.2 none OR Nonempty (QuittingMinimumLawCausalSuffixAtom ...)
```

and treats positive Never mass as its first arm.  The proposed theorem uses
Fin4 hard-residual normality to exclude only the extreme `point.2 none=1`,
which is nevertheless enough to force a finite atom even when Never mass is
strictly between zero and one.  This is a strict contraction of the named
minimum-law boundary, not a duplicate of causalization.

Add the two omitted checked declarations from Section 4 to the source audit.
Also say explicitly that this is a new composition of project declarations,
not a translation of an AGKRS, Solan--Vieille, or Simon paper theorem; no
original-paper hypothesis is being imported silently.

The conjecture-facing significance is adequate for a narrow export: within
the Fin4 hard residual, every global minimum joint-law lift enters the finite
suffix-atom branch.  The existing scope paragraph correctly says that the
result does not consume that atom.

## 7. Independent review gate: PASS

The packet links two substantive reviews:

* `CODEX_EULER`, whose review is explicitly organized as a falsification
  audit; and
* `CODEX_MINER`, performed independently and checking the complete
  behavioral deviation class.

Both verdicts are PASS after the already incorporated
`terminalSemanticLawCarrier_fst_mem_carrier` repair.  This satisfies the
two-review and explicit-falsification requirement for an unrestricted
strategy-class claim.  I found no unresolved mathematical objection in
either review.

## 8. Lean handoff: REVISE locally

The proposed two-declaration split is appropriate and does not assume the
desired conclusion as a structure field.  Make the signatures as exact as in
Section 1 and add the named minimum-to-infimum equality before the optional
third causalization corollary.  The most useful narrow handoff is:

1. generic pure-Never contraction returning exact all-Continue terminal Nash
   and its zero uniform payoff;
2. Fin4 residual theorem returning a positive finite coordinate for every
   supplied joint-law global minimizer; and
3. optional composition returning the existing
   `QuittingMinimumLawCausalSuffixAtom` package for that same point.

No new realization structure or cap-prefix atom field should be introduced.

## Final disposition

**Return the draft for the exact edits above.**  After the quantified Fin4
statement, infimum adapter, observation sentence, concrete boundary examples,
and source/handoff additions are incorporated, I recommend **PASS** and
placement in `exports/` without another mathematical review.  A final
mechanical check of the repaired packet is enough unless an edit changes the
theorem's scope.
