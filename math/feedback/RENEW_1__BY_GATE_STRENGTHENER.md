# Independent strengthening review of RENEW_1

## Verdict

**FAIL as an export answering the terminal-exit question.**  The document does
not consume any of the three exits in
`questions/FIN4_RENEWAL_TERMINAL_EXIT_CONSUMERS.md`.  Its global paid-cap
reduction and its maximal-reset trichotomy are already checked in the
repository, and both still end in the named open paid/reset residuals.

There is one correct and potentially useful local addition: a finite prefix
with zero return both under prescribed play and after deletion of any one
player screens an arbitrary behavioral tail exactly.  The sharp concrete
adapter is not “two deterministic deadlines” but **two distinct players with
zero own survival through the prefix**.  This preserves the complete outcome
law of every unilateral behavioral response, hence prescribed payoff and the
unrestricted cap.  The existing finite-stopper reset proof can be strengthened
to produce such a prefix.

That component removes a tail-substitution seam.  It does not produce the
simultaneous Nash--Bellman inequalities required for a punishment-floor
admissible edge.  Therefore it is a formalizable utility lemma, not a completed
consumer or a strict answer to the named question.

## Claims audited

### 1. The refusal ledger is correct but not new here

The fixed-root-sequence identity and its finite-set and summability
consequences are already the content of
`UniformEquilibrium/Quitting/Paths/GlobalRefusalLedger.lean`.  Their scope is
exactly one root sequence.  They cannot telescope gains belonging to a list of
different complete profiles obtained by successive unilateral replacements.
The warning in `RENEW_1.md` about this mismatch is correct.

### 2. The full-gap paid row at every actual profile is correct and already checked

`HasTerminalExploitabilityGap.exists_supported_pureTimePayoff_sub_at` and
`HasTerminalExploitabilityGap.exists_paidFirstDisagreementRow_at` in
`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/ActualProfileTerminalGapPaidCap.lean`
retain the full gap `gamma`; there is no loss to `gamma / 2`.  The support-pair
argument compares two stopping-law averages, so it does not require attainment
of the unrestricted cap by a pure time.

The same file already constructs
`QuittingActualProfileTerminalGapPaidCapPort` at every actual profile and proves
the exact trichotomy.  Under the terminal-gap witness its charged-return arm is
excluded by the uniform-payoff consumer, leaving
`QuantitativeDebtDescent ∨ InertStall`.

Thus the displayed implication from a renewable terminal exit to a paid-cap
open residual is mathematically harmless after choosing any literal profile,
but it does not use or consume the exit geometry.  It simply re-applies an
existing arbitrary-profile theorem.  It is not a rank decrease, a return, or a
terminal approximation.

### 3. The maximal paid/reset trichotomy is also already checked

The source-side regeneration, repaired-side regeneration, or double unique
all-Continue alternative is the theorem
`sourceMaximalRegeneration_or_repairedMaximalRegeneration_or_doubleUnique` in
`Research/Quitting/FinFourPaidCapMaximalDoubleRegeneration.lean`.  That file
explicitly records that strict real-valued debt decrease is not well founded
and that the double-unique arm remains open.  Restating the trichotomy does not
narrow either residual.

## Sharp tail-screening theorem

Let `A = (q_0,...,q_{H-1})` be a finite word of independent quitting roots.
Write

\[
c(A)=\Pr_A(\hbox{all players Continue through }A),
\]

and, for player `i`,

\[
H_i(A)=\Pr_A(\hbox{all opponents of }i\hbox{ Continue through }A).
\]

For arbitrary behavioral tails `T` and `T'`, assume

\[
c(A)=0,
\qquad H_i(A)=0\quad\hbox{for every }i.
\tag{S}
\]

Then the following stronger statement holds.

### Complete response-law screening

For every player `i` and every complete behavioral replacement `tau_i`, the
terminal outcome laws of

\[
(A\star T)[i\leftarrow\tau_i]
\quad\hbox{and}\quad
(A\star T')[i\leftarrow\tau_i]
\]

are identical.  The prescribed terminal outcome laws of `A star T` and
`A star T'` are also identical.  Consequently

\[
U(A\star T)=U(A\star T'),
\qquad
B(A\star T)=B(A\star T'),
\]

and hence their full terminal semantic pairs and every coordinate debt agree.

### Proof

Under prescribed play, the probability of reaching the tail is `c(A)=0`.
After replacing player `i`'s complete strategy, all opponents still use the
same prefix word; the probability that they all survive it is `H_i(A)=0`.
Thus neither prescribed play nor any unilateral response reaches the portion
where the two profiles differ.  Coupling the common prefix actions gives
equality of the complete terminal outcome laws, not merely equality of their
reward moments.  Taking expected rewards and then the supremum over all
behavioral replacements gives the semantic equality.

No reward bound and no approximation constant are needed.  The error is
exactly zero.

### Equivalent finite-word proof from existing identities

The prescribed-payoff identity is already
`quittingRetainedTailFiniteTimingGraft_payoff_sub_eq_jointReturn_mul`.
For deviations before the end of the word, the payoff is tail-independent by
`quittingPureTimeDeviationPayoff_retainedTail_eq_of_lt`.  For deviations at or
after the word, including Never,
`quittingPureTimeDeviationPayoff_absolute_sub_absolute_eq` multiplies the tail
difference by `H_i(A)`.  Therefore every pure-time deviation value is equal on
the two grafts.  Applying
`quittingContinuationBestResponseValue_eq_sSup_pureTimeDeviationPayoff` gives
exact cap equality.  This route proves the semantic statement even before the
stronger response-law equality is added.

## Sharp actual-data adapter: two zero-survival players

Let

\[
S_j(A)=\Pr_A(j\hbox{ Continues throughout }A)
\]

be player `j`'s own prefix survival.  If `a != b` and

\[
S_a(A)=S_b(A)=0,
\tag{T}
\]

then (S) follows.  For a given deviator `i`, at least one of `a,b` is a
distinct opponent `j`.  The checked comparison

\[
H_i(A)\le S_j(A)
\]

is
`quittingLiteralRootStackOpponentSurvival_le_ownSurvival_of_ne`, so
`H_i(A)=0`.  Joint survival is then zero by
`quittingLiteralRootStackJointSurvival_eq_opponent_mul_own`.

Two distinct deterministic finite stoppers are the literal special case of
(T).  If their deadlines are `T_a,T_b` and a graft replaces all actions from
date `H` onward, the necessary cutoff is

\[
H>\max(T_a,T_b).
\]

The two deadlines may coincide; only the player labels must be distinct.

## Strengthening the finite-stopper reset finish

The existing theorem `nonempty_finiteStopperExactFinish` can be strengthened
without weakening its constants.  Starting from a finite stopper `s` at
deadline `d`, its chosen exact best responder `i` is distinct from `s`.

* If the selected best pure time for `i` is finite, the endpoint already has
  two distinct finite stoppers.
* If it is Never, replace it by deadline `d+1`.  By
  `quittingTerminalPayoff_update_pureTime_eq_none_of_opponent_stops_before`,
  this has exactly the Never payoff, so exact cap attainment and zero owner
  debt are preserved.  Since `s` stops first, the prescribed terminal law and
  the positive-incidence certificate are unchanged.
* In the two-step no-incidence branch, the first responder is forced to Quit at
  date zero.  If the second exact responder is Never, replace it by date one.
  The same argument gives two distinct finite stoppers and preserves the unit
  incidence used in the current proof.

Therefore the exact finish can retain:

\[
\text{path length at most }2,
\quad\text{each finish-edge gain at least `gap`},
\quad\text{two distinct finite stoppers}.
\]

The larger reset-arrival composition still has the constants already exposed
by its public API: length at most `card(I)+3` and path threshold
`3*gap/4`.  Tail screening introduces no additional loss.

This strengthening is not literally present in the current structure:
`QuittingFiniteStopperExactFinish` stores the reset owner and incidence witness
but does not store two finite-stopper labels and deadlines.  It therefore needs
a new theorem or an extended result type; it must not be claimed as checked
merely because the late-time payoff equality is checked.

## Boundary tests

### One stopper is insufficient

Take two players `a,b`.  In the prefix, `a` Quits surely and `b` Continues.
Set player `a`'s reward at `{a}` to zero and at `{b}` to one.  Compare a first
tail in which `b` Quits surely and a second tail in which `b` Never quits, with
all relevant singleton rewards in the second tail equal to zero.  Prescribed
play is absorbed by `a` in both profiles, but after `a` deviates to Continue,
the first tail pays one and the second pays zero.  Thus prescribed laws can be
tail-independent while `a`'s unrestricted cap is tail-dependent.  Zero joint
return alone is not enough; player-deleted return is essential.

### The strict cutoff is necessary

If the graft begins at a stopper's deadline rather than strictly after it, it
may replace the sure-Quit action itself.  The tail can then be reached.  Hence
`H > max(T_a,T_b)` is sharp for the stated “replace from H onward” convention.

### A horizontal best reply is not a simultaneous root Nash point

Take two players with a zero continuation.  Give player one reward one for
quitting alone and zero for continuing.  Give player two reward one when only
player one quits and reward two when both quit.  Updating player one from
Continue to its exact best response Quit is a cap-attaining horizontal update
and makes player one's debt zero.  At the resulting root player two strictly
prefers Quit to its prescribed Continue action.  Thus exact cap attainment for
the mover supplies none of the other player's Nash inequalities.  Tail
screening cannot repair this prefix-local failure.

## What the tail theorem does and does not consume

The strengthened finite-stopper result is an actual-data producer for a
zero-return screening word.  The screening theorem then consumes that word by
allowing an arbitrary literal behavioral tail to be inserted without changing
the endpoint's semantic pair or any unilateral-response law.

It does **not** identify the inserted tail's semantic pair with the endpoint's
semantic pair.  In particular, the `returned` field of
`QuittingActualProfileFixedLawResetHandoff` is a point of the joint carrier,
not necessarily the semantic pair of one attained behavioral profile.  Even
when an actual realizing tail is chosen and hidden behind the screen, the
visible semantic pair remains the reset endpoint's pair, not the returned
tail's pair.

Most importantly, the reset path is a list of horizontal whole-strategy
updates.  A `QuittingPunishmentFloorAdmissibleEdge` requires simultaneous
Nash--Bellman and punishment-floor data for one chronological root and its
tail.  The screening word controls what happens after the prefix; it does not
make the prefix roots exact for the nonmoving players.  The missing implication

\[
\text{fixed-law reset handoff}
\Longrightarrow
\text{positive punishment-floor-admissible path}
\]

therefore remains completely unproved.

## Lean handoff for the useful local theorem

The narrowest reusable declarations would be:

```text
quittingTerminalOutcomeMass_retainedTail_eq_of_jointSurvival_eq_zero

quittingPureTimeDeviationPayoff_retainedTail_eq_of_opponentSurvival_eq_zero

quittingContinuationBestResponseValue_retainedTail_eq_of_opponentSurvival_eq_zero

quittingTerminalSemanticPair_retainedTail_eq_of_zeroReturns
  (joint_zero : quittingLiteralRootStackJointSurvival roots = 0)
  (deleted_zero : forall i,
    quittingLiteralRootStackOpponentSurvival roots i = 0)

quittingTerminalSemanticPair_retainedTail_eq_of_two_ownSurvival_zero
  (a_ne_b : a != b)
  (a_zero : quittingLiteralRootStackOwnSurvival roots a = 0)
  (b_zero : quittingLiteralRootStackOwnSurvival roots b = 0)

QuittingTwoFiniteStopperExactFinish

nonempty_twoFiniteStopperExactFinish
```

If deleted outcome laws are part of the intended chronology packet, also add
the stronger theorem asserting outcome-law equality after every fixed
behavioral replacement.  The proof should use the literal graft and not only
equality of reward moments.

The likely dependencies are
`RetainedTailFiniteTimingNash.lean`,
`LiteralRootStackSurvival.lean`, and
`TerminalSemanticFinitePureTimeResetArrival.lean`.  No Fin4 specialization is
needed for the screening theorem; Fin4 only supplies distinct labels and the
hard-residual reset source upstream.

Do not create a theorem named schematically
`QuittingPunishmentFloorAdmissiblePath` from these data.  The concrete target
would have to build a path in
`quittingPunishmentFloorAdmissibleChargedRelation` from actual
`QuittingPunishmentFloorAdmissibleEdge` values, and the simultaneous root
conditions needed for that construction are exactly what is missing.

## Export gate

### PASS conditions

`RENEW_1.md` could pass only after one of the following is added and reviewed:

1. a proof deriving a positive punishment-floor-admissible path from the
   actual reset handoff, including simultaneous root inequalities for every
   player and an actual returned-tail realization; or
2. a separate named question is introduced whose accepted answer is exactly
   the zero-return tail-screening theorem, and the packet is rewritten to
   contain only that complete theorem, its reset adapter, boundary tests, and
   exact source correspondence.

For route 1, the proof must retain positive charge and prove the required
punishment floors; merely grafting a tail or listing horizontal cap-attaining
updates is not sufficient.

### Current FAIL conditions

The present document fails the export gate because:

* it explicitly leaves the simultaneous-root producer open;
* its common paid-cap reduction and maximal-reset trichotomy duplicate checked
  declarations and terminate in existing open residuals;
* the two-stopper strengthening is not yet stated or proved at the sharp
  zero-return level and is not represented by the current Lean structure;
* it has no downstream terminal consumer or well-founded rank; and
* it treats hiding a returned-source tail as if it were a semantic return,
  although the fixed-law returned point need not be attained and the visible
  semantics remain those of the screening endpoint.

The correct disposition is to retain the sharp tail-screening lemma as an
internal formalization candidate and reject the combined document as an
answer to the terminal-exit question.
