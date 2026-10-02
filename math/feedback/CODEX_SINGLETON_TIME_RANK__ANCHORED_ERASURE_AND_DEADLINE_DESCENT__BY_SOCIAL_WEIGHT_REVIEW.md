# Adversarial review of anchored erasure and deadline descent

Reviewer: `SOCIAL_WEIGHT_REVIEW`  
Date: 2026-08-31  
Verdict: **PASS, with two local wording repairs.**

## Claim checked

The note claims that an actual canonical pure-time/Never global minimum of
positive debt cannot remain forever in the pure singleton/reset lane.
Anchored erasure either exposes an off-minimum sibling, or reaches a singleton
minimum.  An exact response of that singleton owner either exits the minimum
fibre or strictly removes the current earliest finite deadline.  The number
of distinct prescribed finite deadlines is therefore a renewable finite
rank, and the construction must eventually reach an actual off-minimum paid
port.

I checked the reduction against unrestricted behavioral responses, the exact
three-value response menu, date-zero and all-Never boundary cases, the
canonical choice of the equality response, literal strategy changes, strict
rank descent, and composition with the separately reviewed finite-clock
purification result.  I also tried two-player deadline chains and simultaneous
earliest coalitions as counterexamples.  The argument survives.

## 1. Unrestricted cap reduction is valid

Fix deterministic opponent stopping times and let their earliest finite date
be `u`, with coalition `A`.  Before absorption the only public history is the
all-Continue word.  Any behavioral response of the selected player induces a
probability law on pure stopping times and Never.  Its payoff is the
corresponding convex combination of

\[
 r_i(\{i\}),\qquad r_i(A\cup\{i\}),\qquad r_i(A),
\]

according as it stops before, at, or after `u`.  Hence the complete
unrestricted cap is the maximum of these finitely many values, not merely a
stationary or finite-horizon cap.

At a singleton minimum at date `t<u`, the first value is the prescribed
singleton payoff and lies strictly below the cap by

\[
 B_i-r_i(\{i\})\ge D_*>0.
\]

Therefore an exact cap attainer may be chosen canonically as QuitAt `u` or
Never.  Calendar-dependent randomization, late stopping and Never add no
fourth value.

The same screening argument validates the anchored-erasure formula.  With a
second sure quitter retained at the marked date, every response of the erased
player has value in the displayed three-element set, and the singleton moat
removes the singleton option whenever it is attainable.

One wording repair is needed here: if the earliest date is `t=0`, there is no
strictly earlier pure stopping time, so the singleton value need not be
attainable in Section 3.  The response-value set is then a subset of the
three displayed values.  The cap formula (3.1) is still exact—indeed more
directly so—but “every response is a convex combination of only three payoff
values” should not suggest that all three are always attained.  Also repair
the typographical `s_p,qquad`.

## 2. Canonicality and literal strategy identity

For the repository's canonical strategy
`quittingPureTimeBehaviorStrategy`, QuitAt `t` Quits only at `t` and
Continues at every other live date.  Replacing it by Never therefore changes
exactly the date-`t` live action.  Replacing the singleton owner by QuitAt
`u` is a legal whole-strategy change at exactly the two clock dates `t` and
`u`; replacing it by Never changes only `t`.

If the collision and refusal endpoint values tie, either QuitAt `u` or Never
is cap-attaining.  Both are canonical and both introduce no new finite date.
Thus no nonconstructive selection can defeat the rank comparison.

The target laws are also exactly as stated: QuitAt `u` gives the pure
coalition `A ∪ {b}`, while Never gives `A`; if every opponent is Never, the
Never target is all Never.  No unchanged post-date semantic tail is claimed
across the owner response, only literal profile ancestry, which is correct.

## 3. Strict finite-rank descent

After anchored erasure the singleton owner is the only player at the current
earliest finite date `t`.  If there is a next opponent date `u`, then `u`
already belongs to the old deadline support.  The exact equality response is
QuitAt `u` or Never, so

\[
 H(\text{target})\subseteq H(\text{source})\setminus\{t\}.
\]

The inclusion is strict and no new deadline is added.  If the target remains
at total debt `D_*`, it is another actual canonical pure-time global minimum,
so the same construction applies again.  The rank `|H|` is at most the number
of players and decreases at every recursive equality step.

At rank one, anchored erasure leaves one singleton owner with all opponents
Never.  Its exact profitable response is Never and the target is all Never.
That target cannot have positive globally minimum debt: if some singleton
reward is nonnegative, its singleton cap margin is zero; if all singleton
rewards are negative, all Never has zero debt.  Thus the recursion must exit
off minimum before or at rank one.

This is a genuine renewable natural-valued rank on the literal pure profiles,
not a real-valued descent and not a serialization of the horizontal erasure
face.

## 4. Payments and source attachment

At a first strict erasure sibling, every actual profile has debt at least
`D_*`, the preceding sibling is a literal minimum, and a maximum-debt player
at the strict sibling has complete response gain

\[
 d_h>D_*/|I|.
\]

Against deterministic pure-time opponents this cap is attained at one pure
time or Never.  Since the prescribed strategy is also pure, positive gain
gives a literal first disagreement.  If instead the singleton owner's exact
response is the first strict exit, that minimum-to-off-minimum edge itself
has gain exactly `D_*`.  All profiles arise by explicit unilateral strategy
updates from the supplied source; no carrier realizer is substituted.

The statement correctly does not claim that the erasure list is a directed
best-response chronology.  Only the selected adjacent comparison is
oriented, while the recursive temporal transition is the singleton owner's
actual response.

## 5. Composition with finite-clock purification

Proposition 9.3 of
`CODEX_SINGLETON_SOURCE__ONE_SURE_OWNER_EXACT_RESPONSE_HANDOFF.md` has a
separate PASS review.  Its equality arm returns an actual profile in which
every coordinate is a pure time or Never, not merely a semantic or law limit.
It therefore supplies exactly the input required here.  If purification exits
off minimum, it already supplies the same paid-port conclusion; otherwise
the deadline-rank theorem applies literally.

This composition is an ordinary-mathematics theorem pending Lean
formalization.  It does not consume the resulting off-minimum port and hence
does not by itself prove Fin4 uniform equilibrium.

## 6. Hard-residual toggle check

The repaired singleton discussion is correct.  At a singleton minimum all
outsider debts are zero, so the collision arm of
`singleton_refusal_or_exists_collision_gain` is impossible: the outsider can
join at the literal singleton date.  Thus the owner-refusal inequality must
hold.  It is only extra table information, not an executable refusal on a
tail containing later opponent deadlines.  The deadline menu, rather than a
false unconditional collision claim, provides the actual response and the
rank drop.

## Disposition

After changing the Section 3 response menu to “a subset of these three
values” at date zero and fixing the typo, I find no mathematical blocker.
This is a genuine finite-rank contraction of the fully pure finite-clock lane
to the existing off-minimum paid port.  Export would still need the usual
delta review after those small edits; it should not be described as a
consumer of the off-minimum port or as a proof of the full conjecture.

