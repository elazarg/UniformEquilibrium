# Feedback on Finite-deadline Nash projective boundary

Target:
[`CODEX_KOLMOGOROV__FINITE_DEADLINE_PROJECTIVE_BOUNDARY.md`](../notes/CODEX_KOLMOGOROV__FINITE_DEADLINE_PROJECTIVE_BOUNDARY.md)

Reviewer: `PROJECTIVE_BOUNDARY_REVIEW`

Verdict: `MATH_ACCEPTED`

Final requested disposition: **PASS**.

The first-round debt-limit, notation, attribution, and finite-depth
clarifications have all been incorporated correctly.  The strengthened paid
edge/paid rectangle hybrid and the exact retained-tail seam also survive a
focused second audit.  The second-round `D_*=0` justification and equation
cross-references have now also been repaired.  I found no remaining objection
to the reviewed ordinary mathematics.

The detailed material through the first Export assessment records the initial
audit, and **Round 2 focused rereview** records the second audit.  The final
section gives the disposition of the current note.

## Claim checked

For a nonempty finite player set `I`, rewards in `[-R,R]` with `R > 0`, and
the hard-tail timing games with actions `A_N = {0,...,N-1} union {infinity}`,
the note claims:

1. every consecutive pair `p in NE_N`, `q in NE_(N+1)` satisfies the
   all-behavior terminal-debt bound

   \[
   d_i(\sigma_p)\le 4R\sum_j \operatorname{TV}(L_Np_j,q_j);
   \]

2. a global terminal gap `gamma` forces adjacent separation, which splits
   into new-date mass or censored-law reshuffling;
3. the new-date arm gives the Fin4 response-pair atom floor
   `gamma^3/(32 R^3)`, and the reshuffling arm gives either a paid law edge or
   a common-date-`N` response square of charge at least `gamma/(2n)`;
4. the adjacent minimum `Delta_N(r)` is attained, is a finite semialgebraic
   optimization, and satisfies `eta(r) <= 4 R Delta_N(r)`;
5. an exactly compatible family of finite timing Nash laws induces an exact
   behavioral terminal Nash profile; and
6. the two-player retained-tail table in Section 7 has pure all-`infinity` as
   its unique mixed timing Nash equilibrium at every finite prefix length,
   despite a charged retained tail.

I also checked the Section 6 hard-deadline boundary test against the exact
formulas in the integrated declarations.

## Independent check

### 1. Timing semantics and the all-behavior debt identity

The timing convention matches
`QuittingFiniteDeadlineTimingAction` and
`quittingFiniteDeadlineTimingActionTime`
(`UniformEquilibrium/Diagnostics/Quitting/FiniteDeadlineTimingGame.lean`):
`none` is Never, finite actions are dates strictly below the deadline, and the
all-Never terminal payoff is zero.  The product of marginal timing laws is the
mixed-extension convention, and
`quittingTerminalPayoff_finiteDeadlineTimingProfile_eq_mixedEU` plus
`quittingFiniteDeadlineTimingProfile_update_pureTime_eq_mixedEU` identify the
literal behavioral realization and its pure-time deviations with the normal
form.  I found no truncation-payoff or mixed/behavioral-realization mismatch.

The coupling calculation is correct.  A disagreement of product samples has
probability at most the sum of marginal total variations.  Since both the
prescribed payoff and a fixed pure-response payoff lie in `[-R,R]`, this gives

\[
 |G_i(a;P)-G_i(a;Q)|
 \le 2R\bigl(\operatorname{TV}(P_i,Q_i)
       +2\sum_{j\ne i}\operatorname{TV}(P_j,Q_j)\bigr)
 \le 4R\sum_j\operatorname{TV}(P_j,Q_j).
\]

For `sigma_p`, Nash optimality caps every date below `N` and Never.  Every
date at least `N` has the date-`N` payoff because all opponents Continue from
date `N` onward.  The exact `sSup` equality in
`sSup_range_quittingTerminalPayoff_update_eq_pureTime`
(`UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean`) then
gives

\[
 d_i(\sigma_p)=[G_i(N;L_Np)]_+.
\]

This step does cover arbitrary unilateral behavioral strategies.  It neither
assumes that a general infinite-time cap is attained nor restricts deviations
to a bounded controller: the hard suffix reduces the pure-time range itself
to the old finite actions, Never, and one common late value.  Since date `N`
is legal for `q`, `G_i(N;q) <= 0`, and the displayed `4R` debt bound follows.

Consequently a sequence of adjacent pairs with vanishing total variation
does give terminal approximate Nash profiles at every positive error.
`quittingGame_exists_uniformEquilibriumPayoff_of_terminalNash_all_errors`
(`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`)
then selects a fixed uniform payoff.  This quantifier order is correct.

### 2. Positive gap, censoring split, and response atom

`HasTerminalExploitabilityGap`
(`UniformEquilibrium/Quitting/Terminal/ExploitabilityGap.lean`) applied to
`sigma_p` gives some coordinate debt at least `gamma`.  Combining this with
the preceding coordinatewise bound yields

\[
 \sum_j\operatorname{TV}(L_Np_j,q_j)\ge \gamma/(4R).
\]

For each marginal, moving `q_j(N)=b_j` to Never has total variation exactly
`b_j`, lift preserves the censored total variation, and the triangle inequality
gives

\[
 \operatorname{TV}(L_Np_j,q_j)\le e_j+b_j.
\]

Thus the two `gamma/(8R)` arms are exhaustive with the stated weak
inequalities.

For the boundary arm, apply the gap to the deadline-`N+1` realization of
`q`.  If `h` is its gap-selected player, then
`QuittingFiniteDeadlineNashProfile.semanticDebt_le_escapeCharge`
(`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFiniteDeadlineNashEscalation.lean`)
gives

\[
 \gamma\le
 \left(\prod_{k\ne h}q_k(\infty)\right)
       \max(0,r_h(\{h\}))
 \le R\prod_{k\ne h}q_k(\infty).
\]

Hence `r_h({h}) > 0` and every opponent factor is at least `gamma/R`.  Choose
`j` with `b_j >= gamma/(8Rn)` and a distinct responder `i` exactly as in the
note.  Independence then gives

\[
 \Pr_q(T_j=N,\ T_k=\infty\text{ for }k\notin\{i,j\}
        \mid i\text{ is replaced by }N)
 \ge {\gamma\over 8Rn}\left({\gamma\over R}\right)^{n-2}.
\]

At `n=4` this is exactly `gamma^3/(32R^3)`.  It is a response atom attached
to the actual source law `q`, not a prescribed-play atom; the note states this
distinction correctly.

### 3. Reshuffling hybrid and common response square

Under `sum_j b_j < gamma/(8R)`, the `4R` gain Lipschitz bound between `q` and
`L_N(C_Nq)` costs less than `gamma/2`.  From
`G_i(N;L_Np) >= gamma` and `G_i(N;q) <= 0` one obtains

\[
 G_i(N;L_Np)-G_i(N;L_N(C_Nq))\ge \gamma/2.
\]

Telescoping over any enumeration of the `n` player marginals yields one
coordinate change `A -> B` with gain drop at least `gamma/(2n)`.  If that
coordinate is `i`, the pure-date-`N` response term is unchanged, so
`U_i(B)-U_i(A) >= gamma/(2n)`.  If it is `j != i`, expansion gives exactly the
common-response square in (4.11).  All four corners have literal finite-clock
behavioral realizations.  No strategy-class or cap-attainment assumption is
hidden here.

The notation `Q_N` first appears in (4.11) without definition.  Define it as
the deterministic timing law/pure-time behavior that quits at date `N`.
Also say the common hard suffix starts strictly after `N`; a response corner
itself quits at `N`.

### 4. The `Delta_N` hierarchy

For each fixed deadline the mixed-strategy domain is a finite product of
simplices.  Its Nash subset is nonempty, compact, and semialgebraic: Nash can
be written using the finitely many pure-deviation polynomial inequalities.
The total-variation objective is continuous and semialgebraic (absolute values
may be split into finitely many sign cells).  Thus the minimum defining
`Delta_N(r)` is attained.

Taking a minimizing adjacent pair in the coordinatewise debt estimate gives

\[
 \max_i d_i(\sigma_p)\le 4R\Delta_N(r),
 \qquad
 \eta(r):=\inf_\sigma\max_i d_i(\sigma)\le4R\Delta_N(r).
\]

The inequality orientation in (3.7) is correct.  Therefore
`inf_N Delta_N(r)=0` is a sufficient, not necessary, zero-gap criterion.  The
hard-deadline table is a valid incompleteness test: uniqueness fixes the
adjacent pair, and the deadline-`N+1` law has a marginal atom

\[
 b_N={2^N\over 2^{N+2}-1}\longrightarrow {1\over4}
\]

at the new date.  Since the lifted deadline-`N` marginal assigns that event
zero mass, its marginal total variation is at least `b_N`; hence `Delta_N`
does stay away from zero while the table has a uniform-equilibrium payoff.

Calling this a "finite exact semialgebraic query" is sound as a structural
statement.  It should not be read as a supplied algorithm over an arbitrary
encoding of real reward entries; the note does not make that stronger claim.

### 5. Exact compatible family

The compatible-family proof is valid ordinary mathematics.  Define
`mu_i(t)=p_i^{t+1}(t)`.  Compatibility makes every already exposed finite atom
permanent; the decreasing Never masses have a limit, which is `mu_i(infinity)`.
Then `p_i^N` is exactly the censoring of `mu_i` at `N`, and
`mu_i(N) -> 0`.

The payoff mismatch between `p^N` and `mu` is supported on the event that the
first finite stopping time is at least `N`.  These events decrease to the empty
event after excluding all-infinity, so their probabilities tend to zero and
bounded rewards give payoff convergence.  For each fixed finite pure time,
the Nash inequality passes to the limit (indeed the relevant early opponent
atoms are eventually unchanged); the Never inequality passes by the same
bounded convergence.  Exact pure-time extremality then caps every behavioral
deviation.  There is no mixed/behavioral or nonattained-supremum gap.

The final compactness sentence is also correct if "maximum compatibility
error at depth `D`" means the minimum, over the compact product
`NE_1 x ... x NE_D`, of the maximum of all adjacent compatibility errors.
It is not the single-edge quantity `Delta_N`; spelling out this distinction
would prevent a false reading.

### 6. Retained-tail regression

For the Section 7 table, the retained tail that makes both players quit at its
first date has payoff `(1,1)`.  Both own singleton rewards are `-1`; player 1
can Continue at that tail row and receive `r_1({2})=2`, so its tail debt is
exactly `1`.

The finite timing-game uniqueness argument is correct after making its mixed
deviation explicit.  If a profile has finite mass, choose the earliest finite
date `t` used by either player and move the selected player's positive mass at
`t` to infinity:

- if only player 1 uses `t`, every affected outcome improves from `-1` to
  either `2` or the retained value `1`;
- if only player 2 uses `t`, every affected outcome improves from `-1` to
  either `0` or `1`; and
- if both use `t`, player 1 strictly improves at least on the positive-probability
  matching event, from `1` to `2`, and does not lose on the remaining affected
  events.

Thus no finite action can have positive equilibrium mass.  Against a passing
opponent, infinity pays `1` while each finite action pays `-1`, so pure
all-infinity is strict and unique.  This argument uses legal complete mixed
timing-law deviations and the retained payoff, not the hard-tail zero payoff.
The regression therefore survives.

## Source audit

The following declarations were checked in place:

- `quittingTerminalPayoff_finiteDeadlineTimingProfile_eq_mixedEU`,
  `quittingFiniteDeadlineTimingProfile_update_pureTime_eq_mixedEU`, and
  `quittingFiniteDeadlineTimingProfile_isFiniteDeadline`
  (`UniformEquilibrium/Diagnostics/Quitting/FiniteDeadlineTimingGame.lean`);
- `sSup_range_quittingTerminalPayoff_update_eq_pureTime` and
  `quittingTerminalPayoff_update_le_sSup_pureTimeBehaviorStrategy`
  (`UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean`);
- `QuittingFiniteDeadlineNashProfile.semanticDebt_le_escapeCharge`
  (`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFiniteDeadlineNashEscalation.lean`);
- `quittingGame_exists_uniformEquilibriumPayoff_of_terminalNash_all_errors`
  (`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`);
- `HasTerminalExploitabilityGap` and
  `not_exists_uniformEquilibriumPayoff_iff_exists_terminalExploitabilityGap`
  (`UniformEquilibrium/Quitting/Terminal/ExploitabilityGap.lean`);
- `existsUnique_finiteDeadlineTimingNash`,
  `finiteDeadlineTimingNash_exploitability_eq_hardDeadlineDebt`
  (`UniformEquilibrium/Diagnostics/Quitting/FinFourHardDeadlineTimingNashUniqueness.lean`);
- `hardDeadlineDebt_eq_normalizedGeometric`,
  `tendsto_hardDeadlineDebt_succ_quarter`, and
  `comparisonTarget_isUniformEquilibriumPayoff`
  (`UniformEquilibrium/Diagnostics/Quitting/FinFourHardDeadlineTimingNashBarrier.lean`);
- `IsQuittingRetainedTailFiniteTimingNash.debt_le_deletedReturn_mul_tailDebt`
  (`UniformEquilibrium/Diagnostics/Quitting/RetainedTailFiniteTimingNash.lean`);
  and
- `terminalGap_retainedTailFiniteTimingNash_jointReturn_ge`
  (`UniformEquilibrium/Diagnostics/Quitting/RetainedTailFiniteTimingReturnFloor.lean`).

The definite mismatch is Section 6's statement that the unique timing Nash
law has unrestricted debt tending to `1/2`.  The checked formulas give

\[
 D_N={1/4\over 1-(1/2)^{N+1}}\longrightarrow {1\over4}.
\]

The quantity tending to `1/2` is `oneNeverMass(N)`, while the debt is half of
that mass.  The displayed new-boundary atom `b_N` in (6.1) is correct and tends
to `1/4`.  Replace only the erroneous `1/2` debt claim; the boundary-response
interpretation and the new Section 3.1 countertest then remain valid.

Section 7's reference to "the nonidentity absorption-floor lemma" should cite
[`CODEX_ROOT__NONIDENTITY_RETAINED_TAIL_TIMING_NASH_TWO_SIDED_CHARGE.md`](../notes/CODEX_ROOT__NONIDENTITY_RETAINED_TAIL_TIMING_NASH_TWO_SIDED_CHARGE.md)
and mark it as unreviewed ordinary mathematics.  The checked retained-tail
modules supply debt transport and a return floor under additional global-gap
and punishment hypotheses; they do not state that nonidentity absorption
floor.  This is a source-status attachment repair, not a failure of the
Section 7 counterexample.

## Findings

1. **Pass:** equations (2.1)--(3.5), including the `4R` constant and coverage
   of all unilateral behavioral deviations.
2. **Pass:** the `gamma/(8R)` participation/reshuffling split.
3. **Pass:** the general response-pair floor and the Fin4 constant
   `gamma^3/(32R^3)`.
4. **Pass with notation repair:** the `gamma/(2n)` paid edge/common-response
   square; define `Q_N` and locate the suffix after date `N`.
5. **Pass:** compactness, semialgebraicity, and the orientation
   `eta(r) <= 4R Delta_N(r)`; the hard table correctly shows non-completeness
   at zero gap.
6. **Pass:** compatible timing-law families produce an exact behavioral
   terminal Nash profile.  The finite-depth compatibility error should be
   distinguished from the one-edge `Delta_N`.
7. **Repair required:** change the hard-deadline debt limit from `1/2` to
   `1/4` and cite the exact declarations above.
8. **Pass with source-status repair:** the retained-tail table and uniqueness
   proof are correct; explicitly cite the unreviewed absorption-floor note.

## Suggested next move

Make three local changes to the author note:

1. in Section 6 replace "unrestricted debt tending to `1/2`" by
   "unrestricted debt tending to `1/4`" and distinguish it from the opponent
   Never mass tending to `1/2`;
2. define `Q_N` before (4.11) and say the common all-Continue suffix is after
   the response date; and
3. attach the Section 7 absorption-floor comparison to the named conference
   note with its ordinary-mathematics/unreviewed status.

After those changes, the mathematical disposition of the reviewed claims
would be **PASS**.

## Export assessment (round 1)

No export should have been made from the first-round version.  Its false `1/2`
checked-source statement first required correction.  Even after that repair,
Sections 3--5 were ordinary mathematics not checked in Lean, and the note
itself correctly stated that its boundary packets lacked positive-minimum
source provenance and did not close the current Fin4 consumer.  This review
therefore supported retention as a valid internal result after revision, not
self-export.

## Round 2 focused rereview

Current disposition: **REVISE**.

### Prior repairs

All first-round requested repairs are present:

1. Section 6 now gives the checked hard-deadline debt limit `1/4`, separately
   identifies the opponent Never-mass limit `1/2`, and cites
   `hardDeadlineDebt_eq_normalizedGeometric`,
   `tendsto_hardDeadlineDebt_succ_quarter`, and
   `comparisonTarget_isUniformEquilibriumPayoff`
   (`UniformEquilibrium/Diagnostics/Quitting/FinFourHardDeadlineTimingNashBarrier.lean`).
2. Section 4.2 defines `Q_N` as the deterministic date-`N` timing law and
   correctly places the common all-Continue suffix strictly after date `N`.
3. Section 7 names
   `notes/CODEX_ROOT__NONIDENTITY_RETAINED_TAIL_TIMING_NASH_TWO_SIDED_CHARGE.md`
   and explicitly labels its absorption-floor comparison unreviewed ordinary
   mathematics rather than a checked retained-tail declaration.
4. Section 5 now distinguishes the depth-`D` maximum adjacent-error minimum
   over `NE_1 x ... x NE_D` from the single-edge quantity `Delta_N`.

These repairs discharge every first-round mathematical objection.

### Strengthened paid-edge or genuinely paid-rectangle hybrid

The new Section 4.2 is correct.  Let

\[
 H_0=L_Np,\qquad H_n=q,
\]

replace all `n-1` opponent marginals first, and replace observer `i`'s own
marginal last.  Put `g_k=G_i(N;H_k)`.  The gap and Nash inequalities give
`g_0 >= gamma` and `g_n <= 0`.

If `g_k > 3 gamma/4` for every `k<n`, then the final edge changes only `i`'s
law.  Its opponents, hence its pure-`Q_N` response payoff, are fixed.  Thus

\[
 g_{n-1}-g_n=U_i(H_n)-U_i(H_{n-1})>3\gamma/4.
\]

This is a legal unilateral whole-behavior-law deviation from `H_(n-1)` to
`H_n=q`, not merely a prescribed-payoff comparison.

Otherwise take the first `k<n` with `g_k <= 3 gamma/4`.  Necessarily `k>=1`,
and

\[
 \sum_{ell=1}^k(g_{ell-1}-g_ell)=g_0-g_k\ge\gamma/4.
\]

Although individual signed drops may be negative, at least one is at least
`gamma/(4k) >= gamma/(4(n-1))`.  Its source index is below the first crossing,
so its source response gain is strictly above `3 gamma/4`.  Expanding that
drop gives exactly (4.12).  Therefore the rectangle is genuinely paid at its
actual source `A`; the proof does not infer profitability merely from a
positive cross-difference.  The constants and strict/weak inequalities are
all oriented correctly, including the `n=2` case.

This strengthened statement is unconditional with respect to the earlier
`b/e` split.  It remains conditional on the stated global gap and `n>=2`, as
the section correctly records through the gap witness (4.7).

### Exact retained-tail seam

Equations (4.13)--(4.15) are exact.  A hard timing product law reaches a
retained tail only on the all-pass event, whose probability is

\[
 M(P)=\prod_jP_j(\infty).
\]

Thus replacing terminal value zero by a tail payoff `u` adds exactly
`M(P)u_i` to the prescribed coordinate.  A pure response at the final date
`N` either loses to an earlier opponent stop or absorbs at `N`; it never
reaches the tail, including on simultaneous date-`N` quits.  Its payoff is
therefore tail-independent, and

\[
 G_i^u(N;P)=G_i^0(N;P)-M(P)u_i.
\]

Subtracting the gains at `A` and `B` yields the seam
`-(M(A)-M(B))u_i` with the sign shown in (4.15).  The stated sufficient bound
`|M(A)-M(B)| |u_i|` smaller than the hard cross floor is valid.  The note also
correctly refrains from claiming that adjacent timing Nash comparison controls
this seam.

### Joint-pass equalization regression

The payoff and cube calculations in Section 4.4 are correct.  With observer
reward

\[
 r_1(S)=\mathbf 1_{S=\{1\}},
\]

the hard-zero-tail source `A` has prescribed payoff `0` and pure-`Q_N`
response payoff `1`, while `B` and its response both pay observer `1` zero.
The hard response-square charge is exactly `1`.  After grafting the displayed
tail `tau`, the four observer payoffs are exactly those in (4.17), and

\[
 M(A)=1,\quad M(B)=0,\quad u_1=1
\]

makes the seam `-1`, cancelling the charge.  Forcing observer `1` or either
zero-reward spare to `Q_N` in both columns equalizes joint pass at zero,
leaves both response gains zero, and gives the correcting player no own-payoff
gain.  The observer payoff lost under a spare correction is indeed not a
unilateral gain of that spare.  Hence the intended local equalization
principle is refuted.

One sentence is false: "the table has `D_*=0` (indeed all-Never is exact)."
At all-Never, observer `1` receives zero and can Quit alone for
`r_1({1})=1`, so its debt is at least `1`; all-Never is not exact.  The
preceding conclusion `D_*=0` is nevertheless correct because `tau` itself is
an exact behavioral profile:

- observer `1` already receives its maximum possible payoff `1` by quitting
  alone; and
- every other player's reward is identically zero.

The repair is therefore simply:

> The table has `D_*=0` because the retained tail `tau` is exact.

Delete the all-Never parenthetical.  No reward, profile, seam, or correction
calculation needs to change.

### Remaining editorial cross-references

The strengthened square is equation (4.12), not (4.11).  Section 6 may cite
the qualifying paid-source inequalities (4.11) or the square (4.12), but the
logical-level bullet in Section 8 should extend through (4.12), and the next
question should refer to (4.10)--(4.12) or name the paid edge and paid square
without a range.  These are editorial repairs, not additional mathematical
objections.

### Round 2 findings

1. **Pass:** all first-round debt-limit, notation, source-attribution, and
   compactness clarifications.
2. **Pass:** the strengthened `3 gamma/4` paid own-law edge versus
   `gamma/(4(n-1))` genuinely paid response rectangle.
3. **Pass:** the exact retained-tail payoff/gain seam and its sign.
4. **Pass:** the joint-pass equalization cancellation and no-paid-correction
   calculations.
5. **Repair required:** replace the false claim that all-Never is exact by the
   correct reason for `D_*=0`, namely exactness of `tau`.
6. **Editorial repair:** update the strengthened response-square equation
   cross-references from (4.11) to (4.12) where appropriate.

After these local changes, the reviewed current note merits **PASS** as
ordinary mathematics.  It still should not be exported: the note deliberately
lacks positive-minimum source provenance and does not close a maintained Fin4
consumer.

## Final focused rereview

Final disposition: **PASS**.

The two Round-2 repairs are complete:

1. Section 4.4 now states that `D_*=0` because the retained-tail profile is
   exact.  This is correct: observer `1` receives the maximal possible payoff
   `1`, and every other player's rewards vanish.  The false all-Never
   parenthetical is gone.
2. The response square is consistently cited as (4.12) in the Section 6
   boundary comment, the Section 8 logical-level summary, and the Section 9
   next question.  Equation (4.11) remains correctly reserved for the paid
   source and signed-drop inequalities.

No mathematical objection remains in the scope of either review.  This is
acceptance as ordinary mathematics only; no export was made or recommended.
