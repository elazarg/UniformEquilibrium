# Adversarial review of the actual-reached pair residual

Reviewer: `SOCIAL_WEIGHT_REVIEW`

Note reviewed:
[CODEX_DESCENDANT__ACTUAL_REACHED_PAIR_PREMARK_RESIDUAL_AND_DELETED_REACH.md](../notes/CODEX_DESCENDANT__ACTUAL_REACHED_PAIR_PREMARK_RESIDUAL_AND_DELETED_REACH.md).

## Verdict

**REVISE, with a sound mathematical core and one bounded exactness repair.**

The source-level endpoint identity, unrestricted-cap residual decomposition,
strict-earlier localization, deleted-reach cap modulus, and four-player
regression all survive attempts to falsify them with mixed stopping laws,
earlier absorption, arbitrary post-tails, and source clocks at or after the
marked date.  The strict-earlier alternative is a genuine refinement of the
restored pair question.  It does not consume the resulting paid port.

The note should not write that the selected row's actual gain is *equal* to
(R_i^t/4).  The checked row is typed with certified gain floor (R_i^t/4),
while its actual pure-time payoff difference is only proved to be at least
that amount.  Equations (4.2), (4.5), and the later prose already use the
correct inequality; only the headline displays (0.1), (4.6), and (7.1), plus
the phrase “gain(e)=...”, need harmonization.  The file also has widespread
lost inline-math delimiters such as `(sigma)`, `(t)`, and `(Delta_i)`, which
must be restored before export consideration.

## 1. Exact marked endpoint and complete cap

Let the reached root at date (t) be the pure pair (K=\{a,b\}), with
unconditional reach (L).  Changing one player's action only at that row
leaves every earlier outcome unchanged.  On reach, another pair member still
Quits after either endpoint choice, so the literal tail is screened.  Hence

\[
 U_i(\sigma^{i,t})-U_i(\sigma)=L\Delta_i
\]

and the finite terminal law changes by exactly

\[
 L(\delta_{K'}-\delta_K).
\]

These statements remain true with arbitrary earlier absorption and an
arbitrary post-tail.

Among responses that retain player (i)'s own strategy strictly before
(t), the only relevant conditional choice is the affine mixture of the two
screened endpoints.  Thus their exact payoff envelope is

\[
 E_i^t=U_i(\sigma)+[L\Delta_i]_+.
\]

Since a player's complete cap is independent of its own prescribed strategy,

\[
 d_i(\sigma)=[L\Delta_i]_++R_i^t,
 \qquad
 d_i(\sigma^{i,t})=R_i^t
\]

when the target uses the locally optimal endpoint.  This is an unrestricted
behavioral-cap statement: the residual contains every response changing the
strategy before (t), including Never and arbitrarily late stopping.

## 2. The strict-earlier proof is valid

On the locally optimal target, a supported source pure time (q_0\ge t) has
one of two forms.

- If the selected endpoint is Quit, support at or after (t) is concentrated
  at (t).
- If the selected endpoint is Continue, every supported pure time later than
  (t), including Never, has the same payoff because the other pair member
  Quits surely at (t).

In either case, no receiving pure time whose first disagreement with (q_0)
is at or after (t) can improve on (q_0).  The checked declaration
`positiveDebt_exists_actualJointReach_paidRow_mem_support` selects its source
witness from the target player's actual stopping-law support and supplies a
strictly profitable receiving witness.  Therefore its first-disagreement
date is strictly less than (t).

With (ho=R_i^t>0), the checked quantitative conclusions are

\[
 \rho/4\le \text{actual paid gain},\qquad
 \rho\le8M\,\operatorname{OppReach},\qquad
 \rho^2\le32M^2\,\operatorname{JointReach}.
\]

The first relation is not generally equality.  This is the sole mathematical
wording repair I found.

## 3. Deleted reach is the correct nonmover modulus

For a nonmover (j), couple one arbitrary complete response against the two
opponent profiles.  Their outcomes can differ only if every opponent of
(j) survives strictly before (t).  Therefore

\[
 |B_j(\sigma^{q,t})-B_j(\sigma)|\le2M H_j(t).
\]

Independence gives (L=S_j(t)H_j(t)).  Since (S_j(t)) may be arbitrarily
small, no uniform (O(L)) bound follows.  This remains correct when (j)'s
response stops before the mark—the coupling event is merely a necessary
event and so still gives an upper bound.

## 4. Regression check

The displayed four-player example works after choosing the unspecified
coordinates as stated.

- Player (2)'s immediate-Quit response pays one whether player (3) Quits
  at date zero or not, so its cap remains one on both endpoints.
- The marked outsider join gains only (\varepsilon), leaving residual debt
  (1-\varepsilon).
- Player (3)'s cap moves from zero to one because its own date-zero Continue
  response removes the early screening event, while (H_3(1)=1) and the
  actual marked reach is only (\varepsilon).
- The incoming triple-to-pair edge is strict and the post-tail is irrelevant.

There is also a zero-debt profile: player (2) Quits surely at date zero and
the other players Continue, with the unspecified join rewards chosen no
larger than their displayed continuation payoffs.  Thus the example is
correctly labelled a specification regression rather than a positive-gap
counterexample.

## 5. Exact contribution and remaining boundary

The note answers one named part of the restored strategic-pair question:

\[
 \boxed{
 \text{locally optimal actual marked endpoint}
 \Longrightarrow
 \text{mover debt killed}
 \ \lor\ 
 \text{strictly earlier source-supported paid row}.}
\]

The second output has checked actual opponent/joint reach floors and enters
the existing paid-cap trichotomy.  It is not itself a Nash--Bellman edge, a
renewable pair-source transition, or a consumer of the debt-descent and inert
outputs.  The earlier response may destroy the marked pair, so the strict
calendar decrease cannot simply be iterated as a pair rank.

Subject to replacing “gain equals” by “certified gain at least” and restoring
the lost math delimiters, I find no mathematical blocker.
