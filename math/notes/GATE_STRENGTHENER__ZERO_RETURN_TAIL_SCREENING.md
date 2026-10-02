# Zero-return tail screening

## Status

The theorem below is proved in ordinary mathematics and is closely supported
by existing checked finite-word transport identities.  The response-law
formulation and the two-zero-survival reset wrapper are not claimed to be Lean
checked.

This is an exact tail-substitution theorem.  It does not construct a
Nash--Bellman chronology, a punishment-floor-admissible edge, a return to a
minimum semantic point, or a uniform-equilibrium payoff.

## Setting

Let `I` be a finite nonempty player set and let `r` be an arbitrary quitting
reward table.  No reward normalization or sign condition is assumed.

Let

\[
A=(q_0,\ldots,q_{H-1})
\]

be a finite word of product quitting roots.  For each player `i`, define

\[
S_i(A)
 :=\prod_{t<H}q_t^i(\mathsf C),
\]

the probability that `i` Continues throughout the word, and define

\[
H_i(A)
 :=\prod_{t<H}\prod_{j\ne i}q_t^j(\mathsf C),
\]

the one-player-deleted, or opponent, survival probability.  The joint return
probability is

\[
c(A)
 :=\prod_{t<H}\prod_{j\in I}q_t^j(\mathsf C).
\]

For a complete behavioral tail `T`, write `A star T` for the literal profile
which plays the roots in `A` on the first `H` live histories and, after `H`
all-Continue outcomes, resumes `T` literally.

The terminal outcome law includes every nonempty quitting coalition and the
all-Never outcome.  A unilateral response means replacement of one player's
complete behavioral strategy, including arbitrary private randomization,
calendar dependence, Never, and arbitrarily late stopping.

## Theorem 1: complete zero-return screening

Assume

\[
H_i(A)=0\qquad\text{for every }i\in I.
\tag{1}
\]

Then, for any two complete behavioral tails `T,T'`, all of the following
hold.

1. The prescribed terminal outcome laws of `A star T` and `A star T'` are
   equal.

2. For every player `i` and every complete behavioral response `tau_i`, the
   terminal outcome laws of

   \[
   (A\star T)[i\leftarrow\tau_i]
   \quad\text{and}\quad
   (A\star T')[i\leftarrow\tau_i]
   \]

   are equal.

3. Consequently the entire unilateral response-payoff functions agree:

   \[
   U_i((A\star T)[i\leftarrow\tau_i])
   =
   U_i((A\star T')[i\leftarrow\tau_i])
   \]

   for every `i,tau_i`.

4. Prescribed payoffs, unrestricted behavioral caps, coordinate debts, and
   the complete terminal semantic pair agree:

   \[
   U(A\star T)=U(A\star T'),
   \qquad
   B(A\star T)=B(A\star T'),
   \qquad
   \operatorname{Sem}(A\star T)=\operatorname{Sem}(A\star T').
   \tag{2}
   \]

5. In particular, every one-player-deleted terminal law agrees across the two
   grafts.  This is obtained from item 2 by taking `tau_i` to be literal
   Never, equivalently forcing `i` to Continue forever.

### Proof

Fix a player `i` and a behavioral response `tau_i`.  In both updated profiles,
all opponents of `i` play the same prefix roots.  The probability that every
one of those opponents survives the word is exactly `H_i(A)=0`.  Therefore,
even after the arbitrary response by `i`, absorption occurs within the prefix
with probability one.  The two plays can be coupled using the same prefix
randomness; their terminal time and coalition then agree almost surely.  This
proves equality of the complete response outcome laws.

Since `I` is nonempty, choose any player `i`.  Joint survival factors as

\[
c(A)=H_i(A)S_i(A)=0.
\]

Thus prescribed play also absorbs within the prefix almost surely, proving
item 1.  Equality of outcome laws gives equality of expected rewards.  Taking
the supremum of the identical response-payoff functions over the complete
behavioral strategy class gives cap equality and hence (2).

The error is exactly zero.  The argument uses neither bounded rewards nor
attainment of a best response.

## Theorem 2: the sharp two-player clock adapter

Suppose there are distinct players `a,b` such that

\[
S_a(A)=0,
\qquad
S_b(A)=0.
\tag{3}
\]

Then condition (1) holds, and hence every conclusion of Theorem 1 holds.

### Proof

Fix `i`.  At least one of `a,b`, call it `j`, is distinct from `i`.  Opponent
survival after deleting `i` includes `j`'s own survival as a factor, so

\[
0\le H_i(A)\le S_j(A)=0.
\]

Thus `H_i(A)=0` for every `i`.

This is the correct abstraction of a two-stopper barrier.  The two players
need not stop at the same date, and their clocks need not be deterministic;
each only needs zero probability of surviving the finite prefix.

## Corollary: two literal finite stoppers

Suppose `a != b` and, in a behavioral profile `P`, player `a` uses the pure
stopping time `T_a` while player `b` uses the pure stopping time `T_b`, both
finite.  Let

\[
H>\max(T_a,T_b),
\]

and retain the live roots of `P` at dates `0,...,H-1`.  Replacing everything
strictly after that prefix by any behavioral tail leaves unchanged:

* the prescribed terminal law and payoff;
* every unilateral behavioral response law and payoff;
* every player-deleted law;
* every unrestricted cap; and
* the complete semantic pair and debt vector.

Indeed, both `a` and `b` have zero own survival through this prefix.  The
deadlines may coincide; the labels must be distinct.

The strict cutoff is necessary for the stated convention.  If the graft begins
at a stopper's deadline, it may replace the sure-Quit action itself and expose
the new tail.

## Reset-arrival adapter

The checked finite reset finish can be strengthened to retain a literal
two-stopper barrier without weakening its quantitative constants.

Assume a profile already contains a finite stopper `s` at deadline `d`, and
the checked uniform terminal-debt floor selects a distinct exact best
responder `i`.

* If `i`'s selected cap-attaining pure time is finite, `s` and `i` are already
  two distinct finite stoppers.
* If the selected action is Never, replace it by the pure deadline `d+1`.
  Against the unchanged stopper `s`, that deadline has exactly the Never
  payoff.  Hence exact cap attainment, the responder's zero debt, the
  prescribed law, and the stored positive incidence are unchanged.
* In the existing two-step no-incidence branch, the first responder is forced
  to Quit at date zero.  If the next exact responder selects Never, use date
  one instead.  The same argument applies.

Thus the exact finish can be strengthened to store two distinct finite
stoppers while retaining:

\[
\text{finish length}\le2
\]

and the full `gap` gain on each exact finish edge.  The larger public reset
arrival retains its existing length bound `card(I)+3` and its public path
threshold `3*gap/4`; the tail-screening step loses nothing further.

The necessary checked payoff equality is
`quittingTerminalPayoff_update_pureTime_eq_none_of_opponent_stops_before`.
The current structure `QuittingFiniteStopperExactFinish` does not store the
second stopper and its deadline, so this strengthened output requires a new
wrapper or result structure.

## Sharp negative boundary: one stopper does not screen caps

Let `I={a,b}`.  Use the one-root prefix at date zero in which `a` Quits surely
and `b` Continues surely.  Give player `a` rewards

\[
r_a(\{a\})=0,
\qquad
r_a(\{b\})=1,
\qquad
r_a(\{a,b\})=0,
\]

and let player `b`'s rewards be arbitrary, say all zero.

Compare two tails beginning at date one:

* in `T`, player `b` Quits surely at date one;
* in `T'`, player `b` Never quits.

Under prescribed play, `a` quits at date zero, so both grafts have the same
outcome `{a}` and the same payoff.  If `a` deviates to Never, however, the
first graft terminates at `{b}` and pays `a` one, while the second never
absorbs and pays zero.  In the second graft every finite pure quit by `a` also
pays `r_a({a})=0`.  Hence

\[
B_a(A\star T)=1,
\qquad
B_a(A\star T')=0.
\]

Here joint return is zero, but the return after deleting the sole stopper `a`
is one.  Therefore joint absorption, prescribed-law invariance, or one finite
stopper alone cannot imply cap or response-law invariance.  The deleted-return
hypothesis in Theorem 1 is essential.

## Source correspondence

The finite-word quantities are the checked definitions

* `quittingLiteralRootStackJointSurvival`,
* `quittingLiteralRootStackOpponentSurvival`, and
* `quittingLiteralRootStackOwnSurvival`

in
`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/LiteralRootStackSurvival.lean`.
The comparison used in Theorem 2 is
`quittingLiteralRootStackOpponentSurvival_le_ownSurvival_of_ne`, and joint
survival factors through
`quittingLiteralRootStackJointSurvival_eq_opponent_mul_own`.

The existing payoff and pure-time transport identities are in
`UniformEquilibrium/Diagnostics/Quitting/RetainedTailFiniteTimingNash.lean`:

* `quittingRetainedTailFiniteTimingGraft_payoff_sub_eq_jointReturn_mul`;
* `quittingPureTimeDeviationPayoff_retainedTail_eq_of_lt`; and
* `quittingPureTimeDeviationPayoff_absolute_sub_absolute_eq`.

Together with
`quittingContinuationBestResponseValue_eq_sSup_pureTimeDeviationPayoff`, they
already imply the semantic equality in Theorem 1.  The stronger formulation as
equality of every unilateral response outcome law is the clean theorem surface
that should be added if deleted-law provenance is needed.

The finite-stopper source is
`nonempty_finiteStopperExactFinish` in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinitePureTimeResetArrival.lean`.
That theorem already supplies exact cap attainment and the two-step bound, but
its public structure does not retain two finite stoppers.

The same-stage theorem
`quittingTerminalSemanticPair_literalRootStack_pureSet_screen` in
`UniformEquilibrium/Quitting/Paths/PureNonsingletonCommonPrefixScreening.lean`
is related but not identical: it screens with two simultaneous sure quitters
at one root.  The present theorem allows the two zero-survival clocks to occur
at different dates of an arbitrary finite word.

## Suggested Lean declarations

```text
quittingTerminalOutcomeMass_retainedTail_eq_of_jointSurvival_eq_zero

quittingTerminalOutcomeMass_update_retainedTail_eq_of_opponentSurvival_eq_zero

quittingPureTimeDeviationPayoff_retainedTail_eq_of_opponentSurvival_eq_zero

quittingContinuationBestResponseValue_retainedTail_eq_of_opponentSurvival_eq_zero

quittingTerminalSemanticPair_retainedTail_eq_of_zero_deleted_returns

quittingTerminalSemanticPair_retainedTail_eq_of_two_ownSurvival_zero

QuittingTwoFiniteStopperExactFinish

nonempty_twoFiniteStopperExactFinish
```

The most reusable top theorem should assume all deleted returns vanish.  The
two-own-survival and literal-two-deadline statements should be adapters to it,
not competing proofs.

## Exact nonclaim

The reset construction is horizontal: consecutive points are complete
profiles differing in one player's whole strategy.  Exact cap attainment
controls that mover only.  A chronological Nash--Bellman root must satisfy the
simultaneous endpoint inequalities for every player at one root against one
tail.  Zero-return screening makes the tail invisible but supplies none of the
other players' root inequalities.

For example, with two players and zero continuation, let player one gain one
by quitting alone.  Let player two receive one when only player one quits and
two when both quit.  Replacing player one's Continue strategy by Quit is an
exact cap-attaining horizontal update and makes player one's debt zero, but at
the resulting root player two strictly prefers Quit to its prescribed
Continue action.  The updated root is not Nash.

Therefore this theorem does not convert
`QuittingActualProfileFixedLawResetHandoff` into a path in
`quittingPunishmentFloorAdmissibleChargedRelation`.  It closes tail
substitution behind a supplied screening word and nothing more.
