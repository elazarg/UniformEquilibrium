# Adversarial review of the remote-bubble response-value cocycle

Reviewer: `CODEX_NOETHER`

Claim reviewed:
[`CODEX_RESPONSE_SWITCH__REMOTE_BUBBLE_RESPONSE_VALUE_COCYCLE.md`](../notes/CODEX_RESPONSE_SWITCH__REMOTE_BUBBLE_RESPONSE_VALUE_COCYCLE.md)

## Verdict

**REVISE.**

The central cocycle theorem is exact, including its signs, telescope, bounded
endpoint term, and limsup conclusion.  The four-player rational regression
also checks completely: the full behavioral caps, debts, outcome laws,
escaping marginals, social bubble moment, cap jump, and zero global minimum
are all as displayed.

One local statement overreaches.  A bounded regeneration path localizes a
drop in the value of one fixed response, but that is not by itself a
four-corner common-response or response-externality square.  The prescribed
baseline payoff needed for a square is absent.  This should be renamed a
fixed-response externality edge/drop, with the exact path hypothesis made
explicit.  Nothing else in the cocycle or regression depends on the
overstatement.

Even after that repair, the packet is not export-ready conjecture-facing
progress.  It is a correct supplied-coherence consumer plus a `D_*=0`
regression showing why semantic/law equality is insufficient.  It neither
produces sublinear reentry loss from positive-minimum data nor rules out a
positive-minimum theorem.

## 1. Cocycle algebra and signs

With

\[
 x_k=U_o(P_k[o\leftarrow Q_{q_k}]),\qquad
 y_k=U_o(P_k[o\leftarrow Q_{q_{k+1}}]),
\]

the definitions

\[
 G_k=y_k-x_k,\qquad \ell_k=y_k-x_{k+1}
\]

give

\[
 G_k-\ell_k=x_{k+1}-x_k.
\]

Therefore

\[
 \sum_{k<N}\ell_k
 =\sum_{k<N}G_k-(x_N-x_0).
\]

The sign is correct: `\ell_k>0` means the outgoing response loses value
when re-evaluated in the successor environment, and exactly offsets the
installed gain in the telescope.

If all rewards lie in `[-R,R]`, every `x_k` lies in that interval, so

\[
 \sum_{k<N}\ell_k\ge Ng-2R.
\]

Each `\ell_k` is bounded in `[-2R,2R]`.  The average lower bound
therefore implies

\[
 \limsup_k\ell_k\ge g.
\]

Indeed, an eventual upper bound `\ell_k\le g-\varepsilon` would make the
Cesaro averages eventually less than `g-\varepsilon/2`.  Thus each
condition in (2.8) is sufficient:

- `\ell_k\to0` contradicts the limsup;
- `\sum_k(\ell_k)_+<\infty` bounds every signed partial sum above; and
- `\sum_{k<N}\ell_k=o(N)` contradicts the linear lower bound.

This is a valid conditional consumer of an infinite fixed-gain chain.

## 2. Label and source assumptions

The theorem needs more than equality of two displayed natural numbers.  It
needs `Q_{q_{k+1}}` to denote the same complete behavioral pure-time
strategy in `y_k` and `x_{k+1}`.  The note states this correctly as
literal label closure.  If the successor chart inserts a prefix or takes a
reindexed spine, the equality must include the corresponding clock
shift/offset; raw `Option Nat` equality is generally false.

The regression uses one common absolute calendar and hence satisfies the
strong requirement literally:

\[
 q_{k+1}=2k+2
\]

is the same deterministic stopping strategy in the outgoing and successor
evaluations.

The cocycle itself requires no semantic convergence, cap continuity, or
minimum-fibre hypothesis.  Those fields enter only when one asks for a
source adapter proving small reentry loss.

## 3. The bounded-path localization needs narrower language

Suppose there is a literal path

\[
 Z_{k,0}=D_k,\ Z_{k,1},\ldots,Z_{k,m}=P_{k+1}
\]

of length `m\le L`, every step changes one nonobserver strategy, and
observer `o` prescribes the same response `Q_{q_{k+1}}` throughout.
Then

\[
 \ell_k=U_o(Z_{k,0})-U_o(Z_{k,m})
\]

telescopes, so for `\ell_k>0` some step satisfies

\[
 U_o(Z_{k,r})-U_o(Z_{k,r+1})\ge \ell_k/L.
\]

That conclusion is a literal source-matched **fixed-response value drop**
caused by one other player's strategy change.  It is not yet the
four-corner common-response square

\[
 [V_o(A,q)-U_o(A)]-[V_o(B,q)-U_o(B)],
\]

because no second prescribed-baseline column, and no sign or equality for its
change, is supplied.  Nor is it an own-payoff gain for the player whose
strategy changed.

If `P_{k+1}` does not itself prescribe `Q_{q_{k+1}}`, a path changing
only nonobserver strategies cannot literally end there; the endpoint should
instead be `P_{k+1}[o\leftarrow Q_{q_{k+1}}]`.  The note should state this
endpoint explicitly.

Required repair: replace “response-externality square” by
“fixed-response externality edge/drop,” use the response-overridden successor
as the path endpoint, and leave construction of a genuine square as a
separate optional strengthening.

## 4. Rational Fin4 regression audit

Let `A=\{0,1\}`.  The displayed table has reward bound `R=6`.  At
every `P_k` and `D_k`, the prescribed terminal coalition is `A`, so

\[
 u=(-1,-1,5,6),\qquad \operatorname{Law}=\delta_A.
\]

The unrestricted caps are exactly

\[
 b=(0,0,6,6).
\]

The pure-time checks are:

- Player `0`: quitting before `t_k` gives `-3`, joining player
  `1` at `t_k` gives `-1`, and waiting past `t_k` gives
  reward `0` on `\{1\}`.  Thus its cap is `0`.
- Player `1` is symmetric.
- Player `2`: quitting before the pair gives `3`, joining `A`
  gives `6`, and waiting gives `5`.  Thus its cap is `6`.
- Player `3`: quitting before the pair gives `3`, joining gives
  `-1`, and waiting or `Never` gives `6`.  Thus its cap is
  `6`.

Changing player `3`'s own prescribed time between `Never` and the
late `q_{k+1}` does not change its cap, and the base pair has already
absorbed before that time.  Hence `P_k` and `D_k` have the same full
semantic/law point

\[
 (u,b,\delta_A),\qquad d=(1,1,1,0),\qquad D=3.
\]

The clock identities are exact:

\[
 q_k=2k<t_k=2k+1<q_{k+1}=2k+2.
\]

The incoming response gives player `3` its singleton reward `3`; the
outgoing response waits beyond the pair and gives `6`.  Thus

\[
 G_k=3,\qquad d_3(D_k)=0.
\]

At `P_{k+1}`, the same response `q_{k+1}` now occurs before
`t_{k+1}=2k+3`, so its value returns to `3`.  Therefore

\[
 \ell_k=6-3=3=G_k.
\]

Every marginal clock in `D_k` escapes to `Never`, while the full
outcome law remains `\delta_A`.  The actual marginal-limit profile is
all-`Never`, with cap/debt vector

\[
 B(\bar\sigma)=(0,0,3,3),\qquad d(\bar\sigma)=(0,0,3,3),
 \qquad D(\bar\sigma)=6.
\]

The escaped social moment and cap jump are

\[
 E_{\rm soc}=\sum_i r_i(A)=9,
\qquad
 \Delta_B=\sum_i(b_i-B_i(\bar\sigma))=6.
\]

Therefore

\[
 E_{\rm soc}-\Delta_B=3=D(\bar\sigma)-D(u,b),
\]

and the desired reverse bubble inequality fails strictly.

Finally, the pure singleton `\{2\}` is an exact all-behavior terminal Nash
profile.  Player `2` gets `3` and cannot improve by exposing the
zero tail; players `0,1,3` weakly prefer Continue to joining
`\{2\}`.  Hence `D_*=0`.  The example is not a positive-gap table.

## 5. Cap-jump conclusion and positive-minimum scope

The identity

\[
 D(\bar\sigma)-D_*=E_{\rm soc}-\Delta_B
\]

is correct when the remote semantic point has debt `D_*` and the compact
marginal limit is all-`Never`.  Global minimality gives

\[
 D(\bar\sigma)\ge D_*,
\]

hence only

\[
 E_{\rm soc}\ge\Delta_B.
\]

That is the opposite weak direction from the desired
`E_{\rm soc}\le\Delta_B`.  The cocycle accounts repeated installed
response gains in one coordinate; it does not compare the other cap
coordinates or the escaped social reward.

No stronger positive-minimum consequence follows from the note's current
data.  Positive minimum does not bound the same named response's payoff
across two different opponent profiles.  To use the cocycle positively one
still needs one of:

1. a source-faithful proof that cumulative reentry loss is sublinear;
2. a literal regeneration path and a consumer for its localized
   fixed-response externality; or
3. a global deformation comparing the bubble point to the all-`Never`
   profile with a controlled total debt.

The `D_*=0` regression proves that ordered clocks, fixed response labels,
zero target-observer debt, a unit nonsingleton bubble, unrestricted caps, and
even exact semantic/full-law equality do not supply those missing facts.  It
does not show that positive-minimum provenance also fails.

## 6. Export-gate verdict

After the terminology/path-endpoint repair, the cocycle and regression are
mathematically complete and worth retaining in `notes/`.  They do not pass
the export gate:

- the cocycle is a supplied-condition consumer, not a producer of sublinear
  reentry loss from arbitrary Fin4 data;
- the regression has `D_*=0` and therefore does not refute the live
  positive-minimum implication; and
- no terminal approximation, charged return, renewable rank decrease, or
  positive-gap counterexample is produced.

A future packet would become exportable if it constructed the literal
reentry path from the maintained Fin4 source and either made its cumulative
loss sublinear or consumed a localized fixed-response externality into an
existing terminal/rank endpoint.

