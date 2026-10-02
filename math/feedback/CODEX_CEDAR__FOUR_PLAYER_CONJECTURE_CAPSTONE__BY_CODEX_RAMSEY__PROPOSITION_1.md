# Review of Proposition 1 in `CODEX_CEDAR__FOUR_PLAYER_CONJECTURE_CAPSTONE`

Reviewer: `CODEX_RAMSEY`

## Verdict

**FAIL as literally stated; PASS after a bounded type/sourcing repair.**  I
found no mathematical counterexample to the reduction on the checked player
type `Fin 4`.  The current proposition starts with an arbitrary four-element
type `I`, but its first step invokes
`uniformPayoff_or_nonempty_finFourQuantitativeFullSupportHardResidual`, whose
reward table is literally indexed by `Fin 4`.  No reindexing theorem or
transport of uniform payoff, punishment value, terminal-semantic carrier, and
the later spine declarations is supplied.  Thus the advertised declaration
composition does not presently prove the stated arbitrary-cardinality
version.

The clean repair is to state Proposition 1 for `I = Fin 4`.  Alternatively,
add and cite a complete same-table reindex adapter along an equivalence
`I ≃ Fin 4`.  Subject to that repair and the proof-writing qualifications
below, the conclusion is valid.

## Checks that pass on `Fin 4`

1. **Same-table normality.**  Choose the finite coordinate bound
   `bound := quittingRewardBound reward` and use
   `abs_reward_le_quittingRewardBound`.  The no-uniform arm of
   `uniformPayoff_or_nonempty_finFourQuantitativeFullSupportHardResidual`
   supplies a residual whose `witness` and `all_punishmentNormal` fields refer
   to the original reward table.  Unfolding `IsQuittingNormalPlayer` gives
   exactly

   ```text
   P_i <= s_i
   ```

   simultaneously for all four players.

2. **Positive-debt plateau arm.**  The first arm of
   `exists_positiveMinimumPlateau_or_fixedOwnerSoloSemanticSpine_of_no_uniformPayoff`
   gives carrier membership, global minimum, a positive debt coordinate,
   exact all-Continue root Nash, and the literal semantic-prefix fixed point.
   Carrier debt nonnegativity turns the positive coordinate into
   `D(x) > 0`.  Exact all-Continue root Nash gives `s_i <= U_i` for every
   player.

3. **Positive-survival solo spine.**  If survival does not tend to zero,
   `exists_pos_le_quittingSoloSemanticSurvival_of_not_tendsto_zero` gives the
   required positive uniform lower bound.  Then
   `exists_minimum_allContinueNash_of_soloSemanticSpine_survival_lower`
   contradicts the spine arm's explicit negation of every minimum
   all-Continue Nash candidate.  No prefix-fixed conclusion is needed in this
   contradiction; once the spine arm is excluded, the original dichotomy's
   first arm supplies the prefix-fixed plateau.

4. **Zero-survival, positive-Continue subcase.**  The spine already supplies
   positive owner Quit mass.  Together with positive first-row Continue mass
   and zero survival,
   `QuittingTerminalExploitabilityWitness.atomic_restrictions_of_soloSemanticSpine_survival_zero`
   yields `s_o < P_o`, contradicting all-player normality.

5. **Sure-Quit first row.**  If first-row Continue mass is zero, PMF mass
   makes the owner Quit mass one.  Apply
   `isZeroSoloEndpointNash_of_soloRoot_continue_eq_zero` to the exact first
   root and pure-Continue outsiders.  Before using
   `witness.soloReward_lt_punishmentValue_of_soloEndpointNash`, explicitly
   rewrite the first root with the spine field

   ```text
   root 0 = quittingSoloStationaryRoot owner (root 0 owner).
   ```

   This again gives `s_o < P_o`.  Hence neither the sure-Quit edge case nor
   zero survival leaves a gap.

6. **Singleton-tight plateau.**  If `U_i = s_i`,
   `minimumTerminalSemantic_debt_eq_sum_of_singleton_tight` gives
   `d_i = D`.  Carrier debt nonnegativity and the finite identity
   `D = sum_j d_j` then give `d_j = 0` for every `j != i`, so the full
   `QuittingSingletonTightMinimumFace` record is available.

   Let `G := quittingSingletonCollisionGainMax reward i`.  Its definition
   gives `G >= 0`; since `D > 0`, the explicit choice

   ```text
   q = D / (2 * (D + G))
   ```

   satisfies `0 < q`, `q <= 1`, and `q <= D/(D+G)`.  Thus
   `quittingSoloRateControlled_of_q_le_debt_div_debt_add_gainMax` applies.
   The controlled-rate theorem does **not by itself** state the outsider
   endpoint inequalities: those are supplied by
   `quittingControlledSolo_outsiderEndpoint_le_solo`, which should be added to
   the source list and cited.  With those inequalities,
   `singletonTight_soloReward_lt_punishmentValue_and_nonpos` gives
   `s_i < P_i <= 0`, contradicting normality.

7. **All-four strictness.**  The preceding equality contradiction is valid
   for an arbitrary chosen `i`; it is not a one-coordinate selection.  Hence
   `s_i < U_i` holds simultaneously for every player.  Combining it with the
   global normality field gives `P_i <= s_i < U_i` for all four.

## Required edits before a PASS verdict

- Restrict the proposition to `Fin 4`, or supply the missing full reindex
  adapter.
- Instantiate the quantitative hard-residual theorem with an explicit finite
  reward bound.
- Add `quittingControlledSolo_outsiderEndpoint_le_solo` to the source list and
  use it between the controlled-rate lemma and the punishment-sign theorem.
- Spell out carrier debt nonnegativity in both the deduction `D>0` and the
  deduction that every outsider debt is zero.
- In the sure-Quit branch, write the root-to-solo-root equality before invoking
  the witness endpoint theorem.

With these repairs, Proposition 1 is a valid same-table reduction.  It remains
only a reduction to the wholly separated plateau; it does not construct the
non-singleton Bellman block or a uniform payoff.

## Post-repair verification

The author applied all five repairs in the current note: the player type is
literally `Fin 4`, the reward bound is explicit, the outsider endpoint lemma
is named, carrier debt nonnegativity is used, and the sure-Quit root is
rewritten as the solo stationary root.  **The repaired Proposition 1 is
PASS.**
