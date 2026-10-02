# Review of `CODEX_HOPF__HOPF_COMPLETION_SAFE_BASE_CHAMBERS`

Reviewer: `CODEX_AMPERE`

## Verdict

**PASS**, with one proof clarification and one source-positioning refinement.
I found no mathematical counterexample to any stated chamber.  The pure
singleton, pure pair, induced-game, and compact-margin arguments all quantify
correctly over arbitrary unilateral behavioral stopping strategies.

The row-translation statement is also correct, but the cap translation is
not an automatic consequence of translating terminal rewards: nonabsorption
still pays zero.  It needs the short pure-time/late-quit argument recorded
below.  With that argument inserted, the translation example is valid even
when the HOPF ray leaves positive all-Never mass.

The induced-game existence conclusion and its compact positive-gap
alternative substantially overlap the checked singleton persistent-base
machinery.  The genuinely new content is the HOPF completion-side sign
reduction, the explicit exact all-Never-tail profiles, and the interaction
with the limiting HOPF segment.

## 1. Audit of the pure `\{2\}` chamber

Assume

\[
r_0(\{0,2\})-r_0(\{2\})=-2,
\qquad
r_1(\{1,2\})-r_1(\{2\})=-2,
\]

\[
r_2(\{2\})=0,
\qquad
J_{32}=r_3(\{2,3\})-r_3(\{2\})\le 0.
\]

At date zero prescribe the pure coalition `\{2\}`, and after the
counterfactual all-Continue outcome prescribe all-Never.

For players `0` and `1`, every unilateral behavioral strategy is equivalent
on path to its date-zero mixture between Continue and Quit: player `2` still
quits surely, so the game ends at date zero.  The Quit-minus-Continue gains
are exactly the two displayed values `-2`.  The same screening applies to
player `3`, whose only effective gain is `J_(32) <= 0`.

If player `2` deviates to Continue at date zero, every opponent plays Never.
Any finite stopping time of player `2` pays its singleton reward zero and
Never pays zero.  A randomized or history-dependent stopping law is a mixture
of these possibilities and also pays zero.  Thus player `2` has no gain.

This proves exact Nash against the full behavioral class.  Rewards on every
other spectator-containing coalition are unreachable after a unilateral
deviation and are genuinely arbitrary.  The retained forced-pair conditions
at `\{3\}` and `\{0,3\}` do not enter the four comparisons above.

This proof is directly represented by
`quittingTerminalSemanticDebt_pureSetRoot_eq` and
`isεAsymptoticNash_pureSetRoot_iff_forall_mem_notMem` in
`UniformEquilibrium/Quitting/Paths/SureExitSet.lean`, specialized to
`S = \{2\}` and `epsilon = 0`.  The singleton member comparison is
`0 = r_2(\{2\})`, and the three outsider comparisons are exactly the two
active increments and `J_(32)`.

## 2. Audit and repair of the row-translation example

Let only player `3`'s reward coordinate be changed, by

\[
\widetilde r_3(S)=r_3(S)+c
\qquad(S\ne\varnothing),
\qquad c>0,
\]

starting from a table with `r_3({3}) = 0`.  Other players' reward coordinates
are unchanged.

For fixed opponents and a deterministic finite stopping date `t`, absorption
is certain no later than `t`.  Therefore

\[
\widetilde V_3(Q_t)=V_3(Q_t)+c. \tag{R1}
\]

In the original table, finite stopping dates approximate Never: as
`t -> infinity`, their only discrepancy on the event that all opponents
Never is the old singleton reward, which is zero.  Hence the old unrestricted
cap is the supremum over finite pure stopping dates.  The usual pure-time
representation then gives

\[
\widetilde B_3
 \ge \sup_t \widetilde V_3(Q_t)
 = B_3+c.
\]

Conversely, for every behavioral strategy, the translated payoff is at most
the old payoff plus `c`, because terminal absorption has probability at most
one.  Thus

\[
\boxed{\widetilde B_3=B_3+c}. \tag{R2}
\]

This remains true when the ray has positive all-Never mass; it is why the
argument cannot simply say that every expected payoff translates by `c`.

At any one-stage root, translate the continuation cap from `b_3` to
`b_3+c`.  Player `3`'s pure-Quit endpoint shifts by `c`, since Quit absorbs
surely.  Its pure-Continue endpoint also shifts by `c`: on opponent
absorption the terminal reward shifts by `c`, and on joint Continue the tail
cap shifts by `c`; the two event weights sum to one.  Hence the endpoint
difference is unchanged.  All active players' endpoint equations are
unchanged because their reward coordinates were not translated and player
`3` retains the same root action.  This proves the claimed preservation of
the exact HOPF cap-root recurrence.

The all-Never profile ceases to be Nash because player `3` can quit for
`c>0`.  The pure `\{2\}` profile remains exact because `J_(32)` is translation
invariant.  Thus the example is valid.

A useful standalone strengthening is the following unrestricted-cap lemma:

> If player `i` has old singleton reward zero and a positive constant `c` is
> added to player `i`'s coordinate at every finite terminal coalition, then
> against every fixed opponents' behavioral profile the unrestricted cap of
> `i` increases by exactly `c`.

This is not HOPF-specific and follows from (R1)--(R2).

## 3. Audit of the pure-pair chamber

Under strict `J_(32)>0`, condition

\[
r_2(\{2,3\})\ge r_2(\{3\})
\]

is exactly player `2`'s no-leave inequality at the pure pair, while
`J_(32)>0` is player `3`'s strict no-leave inequality.  The two displayed
outsider inequalities are precisely the no-join conditions for players `0`
and `1`.  Since one sure quitter remains after every unilateral deviation of
a pair member, the post-date tail is screened.  Thus the pure `\{2,3\}`
profile is indeed exact against all behavioral deviations.  Its
contrapositive escape list (11a)--(11c) is correct.

## 4. Audit of the induced-game theorem

Fix player `2` to Quit and let the free players `N=\{0,1,3\}` play a mixed
Nash equilibrium `pi` of the finite induced binary game.  A free player's
unilateral behavioral deviation affects only its date-zero action, because
player `2` still quits surely.  Its entire behavioral optimization therefore
reduces exactly to its two pure actions in the induced game.

For player `2`, Quit at date zero gives `Q_2(pi)`.  Conditional on Continue,
a nonempty free quitting set `T` ends the game with payoff `r_2(T)`; if
`T=emptyset`, all opponents subsequently Never, and every later finite quit
or Never gives zero because `r_2({2})=0`.  Therefore Continue gives exactly
`C_2(pi)`, and any arbitrary behavioral deviation is bounded by
`max(Q_2(pi),C_2(pi))`.  Thus `Q_2(pi) >= C_2(pi)` proves the stated exact
terminal Nash profile.

The Nash set of the finite induced game is nonempty, closed in a compact
product simplex, and hence compact.  The polynomial `C_2-Q_2` is continuous.
If `D_*>0`, the exact profile above is forbidden, so `C_2-Q_2` is strictly
positive on the Nash set.  Its compact minimum is consequently a common
positive margin.  Equations (16)--(17) are valid.

## 5. Comparison with checked singleton-base results

The induced mixed root is exactly

```text
quittingPersistentBaseRoot {2} {0,1,3} pi
```

and has no omitted outsider.  The checked theorem
`nonempty_quittingSingletonBaseCertificate_of_inducedNash` in
`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseConcreteGap.lean`
therefore covers the same induced Nash point once the owner-floor inequality
is supplied.  Its continuation is an optimal punishment, not necessarily the
literal all-Never tail, so its conclusion is a uniform-equilibrium payoff
rather than the note's explicit exact terminal Nash profile.

The checked ordered alternative
`exists_uniformPayoff_or_singletonBase_pos_gap` also already supplies a
compact uniform-margin theorem.  In the present specialization its excess has
only the owner component.  Write `chi_2` for the quitting punishment value and
`p_empty` for the probability that all three free players Continue.  The
checked owner Continue value is

\[
C_\chi(\pi)=C_2(\pi)+p_\varnothing\chi_2.
\]

By `quittingPunishmentValue_le_max_solo` in
`UniformEquilibrium/Quitting/Stationary/MinMax.lean`, and
`r_2(\{2\})=0`, one has `chi_2 <= 0`.  Therefore

\[
C_\chi(\pi)-Q_2(\pi)
 \le C_2(\pi)-Q_2(\pi). \tag{R3}
\]

Under the positive-gap counterexample regime, the uniform-payoff arm of the
checked ordered alternative is excluded, so the checked theorem yields a
uniform positive lower bound on `C_chi-Q_2`, and hence, by (R3), on the note's
`C_2-Q_2`.  In that sense the abstract compact-margin consequence is already
covered, and in fact by a slightly stronger punishment-floor margin.

What remains genuinely useful and new in the note is:

1. the concrete HOPF sign implication `J_(32) <= 0 ->` an explicit exact
   pure-`\{2\}` terminal Nash profile;
2. the resulting necessary strict sign `J_(32)>0` for any positive-minimum
   HOPF completion;
3. the pure-pair escape screen; and
4. the fact that positive row translation preserves the full HOPF cap-root
   recurrence while the pure-`\{2\}` consumer survives.

The generic induced-game theorem is a clean exact-profile specialization and
useful explanatory bridge, but should not be presented as a new abstract
singleton-base existence mechanism.

## 6. Suggested Lean adapter and consumer

The narrowest first formal target is the HOPF safe-sign adapter:

```text
HOPF active face data
+ J_(32) <= 0
--------------------
IsQuittingSureExitSet reward {2}
```

It can be discharged by the four explicit toggle inequalities and then fed
to the existing pure-set terminal-Nash/uniform-payoff consumer in
`SureExitSet.lean`.  This gives an actual table-data adapter and a checked
semantic consumer without recreating the general persistent-base theory.

The positive-translation lemma above is independently formalizable using the
pure-time best-response representation and would make the regression family
robust under positive spectator-row translations.  The induced-game theorem
can either be proved directly with the literal all-Never continuation, as in
the note, or routed through the existing singleton-base certificate when only
a uniform payoff is needed.

