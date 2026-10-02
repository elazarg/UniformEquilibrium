# Whole-packet export gate: single-anchor induced-Nash arbitrary-completion escape

Reviewer: **CODEX_RAMSEY**  
Packet audited:
[`SINGLE_ANCHOR_INDUCED_NASH_ARBITRARY_COMPLETION_ESCAPE_EXPORT_DRAFT.md`](../notes/SINGLE_ANCHOR_INDUCED_NASH_ARBITRARY_COMPLETION_ESCAPE_EXPORT_DRAFT.md)  
Current head audited: `41051dd`  
Verdict: **REVISE**; the mathematics passes, but the current-head source and
novelty audit needs bounded repairs before promotion.

## Required repairs

No theorem statement or proof repair is required.  Before export, make these
source-facing edits.

1. Replace the phrase “formalized two-player persistent-base escape” in the
   conjecture-facing section by the exact comparison: the checked prior result
   is the **cardinality-at-least-two persistent-base arbitrary-completion
   escape**.  The new result strictly extends its literal-membership
   architecture exclusion from two protected coordinates to one protected
   coordinate; it does not subsume every general pointwise leave-safe theorem
   for a larger base.
2. Add the current checked comparison modules to the source audit:
   `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/`
   `PersistentBaseArbitraryCompletionEscape.lean`, especially
   `exists_exactTerminalNash_and_uniformPayoff_of_persistentBaseMembershipReward`,
   and `PersistentBaseArbitraryCompletionSixPlayer.lean`, especially
   `exists_targetA_exactTerminalNash_uniformPayoff_and_secondPairMass_zero`.
   State explicitly that both retain the premise `2 <= base.card`; the present
   ordinary-mathematics theorem supplies the missing singleton-base stopping
   calculation.
3. Name the exact cap identities used by the proof and handoff:
   `quittingStationaryUnilateralCap_eq_max_div` in
   `UniformEquilibrium/Quitting/Stationary/MinMax.lean` and
   `quittingStationaryFullRateUnilateralCap_of_eq_one` in
   `UniformEquilibrium/Quitting/Stationary/FullRateStationaryVerifier.lean`.
   The packet already names the unrestricted deviation bound and the exact
   stationary verifier correctly.
4. Add the exact six-player source
   `UniformEquilibrium/Quitting/Paths/SixPlayerOnePairMassTargetLock.lean`,
   with `SixPlayerOnePair.targetA`, `SixPlayerOnePair.targetB`, and
   `SixPlayerOnePair.secondPairMass`.  In the handoff, use the named labels
   `player1`, ..., `player6`; do not encode the prose labels as raw `Fin 6`
   numerals.
5. In the boundary bullet for `O<1`, replace “`Q_a(x)` may be negative” by
   wording that distinguishes the branch calculation from the stated global
   hypotheses, for example: “Equation (5) remains valid without using the
   sign of `Q_a(x)`; the theorem retains `Q_a(x)>=0` to cover `O=1`.”  As
   currently written, the bullet literally conflicts with assumption (2),
   even though the intended stronger branch observation is correct.

These are exact source/scope and proof-writing repairs.  After they are
applied literally, the packet is mathematically in **PASS** scope; a new
mathematical review is unnecessary, but the repaired draft should be checked
for the source additions before it moves to `exports/`.

## Independent theorem audit

### Induced game and free players

Let `F=I\{a}` and let `x` be a mixed Nash equilibrium of the induced binary
game in which `a` Quits surely.  The orientation agrees with
`quittingPersistentBaseUtility`: a free quitter set `Q` realizes
`{a} union Q`.

After replacing one free player's complete behavioral strategy, the anchor
still Quits at date zero with probability one.  The deviator's payoff depends
only on its randomized date-zero action.  Conditional on its two pure actions,
the values are precisely the two induced-game pure deviations; arbitrary
private randomization is their convex combination.  Thus mixed-Nash
optimality controls every behavioral replacement, not merely stationary
ones.  This is also the semantic content exposed by
`quittingPersistentBaseRoot_free_purePayoff_le`.

The argument includes `F=empty`: the induced zero-player game has its unique
mixed point and there is no free-player obligation.

### Anchor, contracting branch

Write

\[
 O=\Pr_x(Q=\varnothing),\qquad
 C=\sum_{\varnothing\ne T\subseteq F}\Pr_x(Q=T)r_a(T).
\]

Immediate Quit has value

\[
 Q_a(x)=O r_a(\{a\})+C.
\]

If `O<1`, the free stationary row eventually absorbs almost surely when the
anchor continues forever, and the Never endpoint is `C/(1-O)`.  The
pointwise excluded-face bounds give

\[
 C\le(1-O)Q_a(x),\qquad C/(1-O)\le Q_a(x).
\]

Hence `quittingStationaryUnilateralCap_eq_max_div` makes the exact cap
`max(Q_a(x),C/(1-O))=Q_a(x)`.  This calculation indeed does not use the sign
of `Q_a(x)`; the packet's theorem nevertheless assumes the sign globally for
the saturated branch.

### Anchor, saturated branch

If `O=1`, every free marginal is pure Continue.  Then

\[
 Q_a(x)=r_a(\{a\}),\qquad
 \operatorname{FullCap}_a=\max(0,r_a(\{a\})).
\]

The hypothesis `Q_a(x)>=0` makes this cap equal the prescribed payoff.  This
is exactly the branch of
`quittingStationaryFullRateUnilateralCap_of_eq_one`, and it includes every
finite delay, Never, and the one-player boundary.

The declaration
`quittingTerminalPayoff_update_stationary_le_fullRateUnilateralCap` bounds an
arbitrary history-dependent randomized anchor deviation in both branches.
Combining all coordinate bounds through
`isεAsymptoticNash_stationary_iff_fullRateUnilateralCap_le` at error zero
proves unrestricted terminal Nash.  The invocation of
`quittingGame_isUniformEquilibriumPayoff_of_terminalNash_exact` is therefore
valid.

### Literal membership and the Fin6 zero-`B` conclusion

If `r_a(S)=1_{a in S}`, every anchor-Quit coalition pays the anchor one, so
every induced Nash point has `Q_a(x)=1`; every nonempty excluded coalition
pays zero.  All other players' complete reward coordinates are genuinely
unrestricted.

In the checked six-player notation,
`targetA={player1,player2}` and `targetB={player3,player4}`.  If either member
of `targetA` is the protected anchor, the constructed root makes that member
Quit surely at date zero.  Every realized terminal coalition contains the
anchor, while `targetB` does not.  The Never outcome also has mass zero.
Consequently the exact `targetB` atom, hence `secondPairMass`, is zero.  This
is stronger than merely producing some uniform payoff and directly defeats
the desired positive second-pair-mass guarantee.

The logical quantifier in the necessary architecture screen is also correct.
Because one induced Nash point satisfying both dominance conditions already
produces the escape, avoidance requires that every induced Nash point have
either negative `Q_a(x)` or some excluded-face reward strictly above it.  The
converse is not claimed.

## Current-head novelty comparison

The closest checked result is no longer just an abstract persistent-base
compiler.  The current tree contains the complete arbitrary-completion
adapter in `PersistentBaseArbitraryCompletionEscape.lean` and its Fin6
zero-second-pair specialization in
`PersistentBaseArbitraryCompletionSixPlayer.lean`.  Those theorems cover
every base with `2 <= base.card`; another sure quitter prevents a deviating
base member from exposing a continuation.

The present result is genuinely new at the stated scope.  With a singleton
base, a deviating anchor can expose an indefinitely repeated free row, so the
cardinality-at-least-two proof does not apply.  The new step is exactly the
full Snell-cap calculation above, including the `O=1` boundary.  In the
literal-membership specialization it eliminates a strictly larger completion
class: retaining only one first-pair coordinate suffices, while the other five
coordinates may all change arbitrarily.

A narrow current-head search found no checked theorem with this singleton
anchor, induced complement Nash, unconditional Quit value, and excluded-face
dominance interface.  The draft should therefore claim novelty only for this
cardinality-one extension and its five-coordinate Fin6 completion corollary.

## `exports/README.md` gate

1. **Exact statement — PASS.**  The nonempty finite player type, anchor,
   complement game, selected induced Nash point, dominance inequalities, and
   unrestricted conclusions are quantified.  The empty complement remains
   covered.
2. **Definitions and complete proof — PASS.**  The product expectation,
   opponent empty mass, continuation contribution, contracting and saturated
   cap branches, induced-game Nash argument, and terminal consumer form a
   complete proof.
3. **Probability and unilateral agency — PASS.**  The packet specifies public
   histories, independent behavioral randomization, first-coalition
   absorption, the Never payoff, and arbitrary late/history-dependent
   deviations.  The full-rate theorem supplies exactly the claimed power of
   the deviator.
4. **Adapter and consumer — PASS.**  Finite mixed-Nash existence constructs
   the source root.  Literal membership makes the screen automatic, and the
   exact terminal Nash feeds the checked uniform-payoff compiler.  The Fin6
   zero-`B` atom removes a universal architecture explicitly accepted by
   `questions/INCENTIVE_GADGET.md`.
5. **Boundary tests — PASS after repair 5.**  Contracting, saturated,
   genuinely mixed, empty-complement, negative-reward, late, Never, and
   failure boundaries are all mathematically correct; only the stated-versus-
   branch sign wording needs correction.
6. **Source and novelty audit — REVISE.**  The present draft omits the newly
   checked cardinality-at-least-two arbitrary-completion modules, the exact
   max/div declaration, and the Fin6 label/mass source.  Repairs 1--4 resolve
   this without changing the theorem.
7. **Independent review — PASS.**  The packet links substantive independent
   falsification reviews by CODEX_MINER and CODEX_RAMSEY.  Both explicitly
   test arbitrary behavioral deviations and report no unresolved objection,
   satisfying the enhanced requirement for unrestricted strategy-class
   coverage.
8. **Lean handoff — PASS after repairs 2--4.**  Its theorem shape and proof
   split are appropriate and do not assume the singleton theorem as a
   structure field.  The added declarations make the reuse boundary and
   cardinality-one novelty exact.

## Final disposition

**REVISE.**  The mathematical packet survives adversarial review, including
the zero-`B` specialization.  Apply the five bounded source/scope repairs
above, retain both independent review links, and promote under the stable
filename
`SINGLE_ANCHOR_INDUCED_NASH_ARBITRARY_COMPLETION_ESCAPE.md` only after a
literal source-audit check.  No proof rereview is required.
