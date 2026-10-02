# Adjacent-deadline minimum-tail reprojection dispatch

Author: `CODEX_KANTOROVICH`

Independent review:
[`CODEX_CAUCHY`](../feedback/CODEX_KANTOROVICH__ADJACENT_DEADLINE_MINIMUM_TAIL_REPROJECTION_BOUNDARY__BY_CODEX_CAUCHY.md)

## Exact statement

Let `I` be finite, let all quitting rewards have absolute value at most
`R>0`, and fix `N>=1`.  Let

\[
p\in\operatorname{NE}_N,
\qquad
q\in\operatorname{NE}_{N+1}
\]

be independent mixed Nash laws of the hard zero-tail timing games with pure
actions `0,...,N-1,infinity` and `0,...,N,infinity`, respectively.  Let
player `i` have newly exposed hard date-`N` gain

\[
g_i^0:=V_i(N)-U_i(p)\ge\gamma>0.
\]

Assume a supplied actual tail `tau` realizes, to sufficient accuracy, a
Fin4 positive-minimum point with the uniform singleton separation

\[
U_k(\tau)-r_k(\{k\})\ge\delta/2
\qquad(k\in\operatorname{Fin}4),
\]

where the maintained hard residual supplies one fixed `delta>0` on the
minimum fibre.  Graft `tau` literally after the finite timing word.

Write

\[
S_i=p_i(\infty),\qquad
H_i=\prod_{j\ne i}p_j(\infty),\qquad
a=\gamma/R.
\]

Let `C_Nq` censor date `N` to `infinity`, put

\[
e_k=\operatorname{TV}(p_k,(C_Nq)_k),
\qquad b_k=q_k(N).
\]

Then one of the following four source-faithful outputs exists.

1. **Lossless old response.**  `S_i=0`; the `Q_N` gain, and every selected
   common-`Q_N` opponent-hybrid rectangle difference, is exactly unchanged
   by the tail graft.
2. **Paid pass response.**  `1-S_i>=a/8`; passing through the timing word and
   resuming `tau_i` has actual gain at least `a gamma/8`.
3. **Paid reverse boundary-participant edge.**  Some player `j` can move its
   date-`N` mass back to `Never` in the censored hybrid.  This is a literal
   unilateral behavioral update, its mover debt is subtracted exactly, and
   its gain is at least

   \[
   \boxed{
   \frac{3\delta a^2}{64|I|}
     \left(\frac78\right)^{|I|-2}.}
   \tag{1}
   \]

   For Fin4 the floor is `147 delta a^2 / 16384`.
4. **Macroscopic censored reshuffling.**  The old timing marginals satisfy

   \[
   \boxed{\sum_k e_k\ge a/8.}\tag{2}
   \]

Thus the former pure-Never spectator obstruction is not terminal: away from
(2), it is replaced by a paid participant edge with a fixed quantitative
floor.  The sole unconverted adjacent-deadline source-reprojection arm is the
macroscopic displacement (2).

## Conjecture-facing change

This strictly narrows the source-reprojection boundary in
[`FINITE_DEADLINE_NASH_PROJECTIVE_BOUNDARY_AND_COMPATIBILITY.md`](../formalized/FINITE_DEADLINE_NASH_PROJECTIVE_BOUNDARY_AND_COMPATIBILITY.md).
That result produced a paid own-law edge or common-`Q_N` response rectangle
in the hard zero-tail games.  Such payment need not survive grafting a
positive-minimum tail with the same observer.  The present dispatch uses
hard-Nash support and minimum-fibre singleton isolation to reselect the
response or mover exhaustively.  Only (2) remains.

The first three outputs are actual behavioral payoff edges over the same
literal tail.  They are not asserted to be minimum endpoints, exact
Nash--Bellman chronology, admissible returns, or support-rank transitions.

## Exact graft identities

Let `A_i=U_i(p)` in the hard game.  Let `Q_N` Continue through the word and
Quit surely at `N`, and let `Pass_(tau_i)` Continue through the word and then
use the complete tail strategy `tau_i`.  These deviations agree unless every
opponent passes the word.  Therefore

\[
\boxed{
U_i(Q_N,p_{-i}*\tau_{-i})
-U_i(\operatorname{Pass}_{\tau_i},p_{-i}*\tau_{-i})
=H_i\bigl(r_i(\{i\})-U_i(\tau)\bigr).}
\tag{3}
\]

The prescribed graft payoff is `A_i+S_iH_iU_i(tau)`, so

\[
\boxed{
G_i^\tau(N;p)=g_i^0-S_iH_iU_i(\tau).}
\tag{4}
\]

Both are exact identities of actual behavioral profiles; the tail may have
infinite support and Never mass.

If `S_i>0`, hard-Nash support gives `V_i(infinity)=A_i`.  The hard `Q_N` and
`infinity` values differ only on the all-opponents-Never cylinder, hence

\[
\boxed{g_i^0=H_i r_i(\{i\}).}\tag{5}
\]

In particular `r_i({i})>0`, `H_i>=a`, and every opponent's Never mass is at
least `a`.  Substituting singleton isolation in (3) gives

\[
U_i(Q_N)-U_i(\operatorname{Pass}_{\tau_i})
\le-H_i\delta/2.
\tag{6}
\]

Since `infinity` is a hard support action, the pass response has exact gain

\[
\boxed{H_i(1-S_i)U_i(\tau)\ge(1-S_i)\gamma.}\tag{7}
\]

This proves arm 2.  At `S_i=1`, the original `Q_N` response is instead
strictly unprofitable after grafting; preserving its label is impossible in
general.

If `S_i=0`, the joint pass mass is zero in every opponent-hybrid column that
keeps player `i`'s marginal fixed.  Both prescribed and `Q_N` payoffs equal
their hard values.  Therefore the gain and every common-response rectangle
cross-difference are unchanged, proving arm 1.

## Boundary-participant role reselection

Put `c=C_Nq` and let `P^-` lift the fully censored law `c`.  For one player
`j`, let `P^j` move only `b_j=q_j(N)` of that player's mass from `infinity`
back to date `N`.  No opponent has date-`N` mass in either profile.  With

\[
H_j^c=\prod_{k\ne j}c_k(\infty),
\]

one-player linearity and (3) give

\[
U_j(P^j*\tau)-U_j(P^-*\tau)
=b_jH_j^c\bigl(r_j(\{j\})-U_j(\tau)\bigr).
\tag{8}
\]

Thus the reverse update has gain at least

\[
b_jH_j^c\delta/2.
\tag{9}
\]

The endpoints differ only in player `j`'s complete strategy, so its
unrestricted cap is unchanged and its debt is subtracted by exactly (9).

It remains to prove that (9) has a uniform floor outside arm 4.  Adjacent
separation gives

\[
\sum_k(e_k+b_k)\ge a/4.
\tag{10}
\]

Assume `S_i>1-a/8` and `sum e_k<a/8`.  Then `sum b_k>a/8`, so some `j`
satisfies `b_j>=a/(8|I|)`.  Also each `e_k<a/8`.  For `k!=i`, equation (5)
implies `p_k(infinity)>=a`, and therefore

\[
c_k(\infty)>p_k(\infty)-a/8
\ge(7/8)p_k(\infty).
\]

For `i`, `c_i(infinity)>1-a/4>=3/4`.  Hence, uniformly in the selected `j`,

\[
H_j^c\ge\frac34\left(\frac78\right)^{|I|-2}a.
\tag{11}
\]

Combining (9)--(11) proves (1), and completes the exhaustive dispatch.

## Full-cap audit

When `0<S_i<1`, both a finite action and `infinity` are in hard Nash support.
The exact retained-cap ledger gives

\[
d_i(p*\tau)=H_i\left[d_i(\tau)+(1-S_i)U_i(\tau)\right].
\tag{12}
\]

At `S_i=1`, it gives `d_i(p*tau)=H_i d_i(tau)`.  Thus the argument does not
discard the tail's unrestricted cap.  The paid pass term in (7) and inherited
tail debt are the complete two contributions in this support arm.

## Boundary regression

Let the four players be `i,j,k,l`.  For every nonempty coalition `S`, define

\[
r_i(S)=
\begin{cases}
2,&\{k,l\}\subseteq S,\\
2,&j\in S,\ i\notin S,\\
1,&i\in S,\ j\notin S,\\
0,&\text{otherwise},
\end{cases}
\]

\[
r_j(S)=\mathbf 1_{\{k,l\}\subseteq S},
\]

and

\[
r_k(S)=
\begin{cases}
1,&\{k,l\}\subseteq S,\\
-1,&k\in S,\ l\notin S,\\
0,&k\notin S,
\end{cases}
\qquad
r_l(S)=
\begin{cases}
1,&\{k,l\}\subseteq S,\\
-1,&l\in S,\ k\notin S,\\
0,&l\notin S.
\end{cases}
\]

At deadline one take

\[
p_i=\delta_\infty,
\quad p_j=\tfrac12\delta_0+\tfrac12\delta_\infty,
\quad p_k=p_l=\delta_\infty.
\]

This is Nash and player `i`'s newly exposed `Q_1` gain is `1/2`.  At deadline
two take

\[
q_i=\delta_\infty,
\quad q_j=\tfrac12\delta_0+\tfrac16\delta_1
          +\tfrac13\delta_\infty,
\quad q_k=q_l=\delta_\infty.
\]

This is Nash; player `i` gets `4/3` from both `infinity` and `Q_1`, and
censoring `q_j` at date one gives `p_j`.

Let `tau` make exactly `k,l` Quit surely at its first date.  It is exact
all-behavior terminal Nash, with payoff `(2,1,1,1)` and singleton rewards
`(1,0,-1,-1)`.  After grafting,

\[
G_i^\tau(1;p)=-1/2,
\qquad
G_i^\tau(1;q)=-2/3.
\]

The same-observer cross-difference is positive `1/6`, but neither corner is
paid.  Moving `j`'s date-one mass back to Never raises `j`'s payoff from
`1/3` to `1/2`, exactly the reverse participant edge.  This table has
`D_*=0` because `tau` is exact.  It proves that retaining the original
observer/response label is false, while confirming the role-reselection
repair.

## Source correspondence and Lean handoff

Relevant checked ingredients are:

- `quittingTerminalPayoff_finiteDeadlineTimingProfile_eq_mixedEU`;
- the timing recursion and hard-tail realization in
  `FiniteDeadlineTimingRecursion.lean`;
- retained-tail payoff/cap transport in
  `RetainedTailFiniteTimingNash.lean`; and
- `exists_pos_uniformSingletonGap_minimumFiber_of_punishmentNormal`.

The existing adjacent projective boundary supplies (10), including the
finite-versus-Never split, and the literal hybrid profiles.  Suggested new
interfaces should return those profiles and exact identities:

```text
finiteDeadline_supportNever_boundaryGain_eq
finiteDeadlineTailGraft_Q_sub_pass_eq
finiteDeadline_zeroNever_responseDifference_graft_eq
finiteDeadline_boundaryParticipant_reverseGain_eq
adjacentDeadline_minimumTail_paid_or_censoredReshuffle
```

## Scope and nonclaims

- Grafted whole profiles are not proved to lie on the minimum fibre.
- A paid behavioral edge is not an exact Nash--Bellman edge.
- Exact mover-debt subtraction gives no sign for other caps.
- Macroscopic censored reshuffling (2) is not consumed.
- The regression has global minimum zero.
- No terminal approximants, uniform payoff, or positive-gap table are
  produced.

## Lean formalization record

Pre-formalization packet SHA-256:
`0699c6d6d99a6adb4b9bef3daa2f69c46a2321903ac2ebf7c30a9b3ccf8f2933`.

The retained-tail reprojection identities and singleton-separated-tail
dispatch landed in commit
`2678b1a7281422b34a5b04fb67775acceec0de9f`.  Their production owners are
`UniformEquilibrium/Diagnostics/Quitting/AdjacentDeadlineRetainedTailReprojection.lean`
and
`UniformEquilibrium/Diagnostics/Quitting/AdjacentDeadlineSingletonSeparatedTailDispatch.lean`.
The common finite-timing survival identity is owned by
`RetainedTailFiniteTimingRealization.lean`, and the generic retained-payoff
decomposition is owned by `RetainedTailGraftDecomposition.lean`, under the
same Diagnostics directory.

The principal checked declarations are
`quittingFiniteDeadlineOpponentSurvival_timingProfile_eq_prod_none`,
`quittingTerminalPayoff_retainedTailMixedTimingProfile_eq_add_prod_none_mul`,
`finiteDeadline_supportNever_boundaryGain_eq`,
`finiteDeadlineTailGraft_Q_sub_pass_eq`,
`finiteDeadline_zeroNever_boundaryGain_graft_eq`,
`finiteDeadline_zeroNever_responseDifference_graft_eq`,
`finiteDeadlineOldPassProfile_sub_oldGraft_eq`,
`finiteDeadlineCensoredGraft_sub_participantGraft_eq`,
`finiteDeadlineCensoredGraft_bestResponseValue_eq`,
`finiteDeadlineCensoredGraft_semanticDebt_eq_sub_payoffGain`,
`quittingAdjacentDeadline_singletonSeparatedTail_dispatch`, and
`quittingAdjacentDeadline_singletonSeparatedTail_dispatch_finFour`.  The
Fin4 reverse-participant floor is exactly
`147 * delta * (gamma / bound)^2 / 16384`.

Evidence seals are `M` and `L`.  The `A` seal is incomplete: the checked
compiler consumes a supplied adjacent exact source and one supplied actual
singleton-separated tail, but no theorem jointly selects those inputs in the
required source-facing configuration.  There is no downstream `C`; the raw
censor-error arm remains unconsumed.

The checked endpoints are literal behavioral updates.  In the reverse arm,
the mover's unrestricted behavioral best-response value is unchanged and its
terminal-semantic debt falls by exactly the displayed payoff gain.  No
endpoint is asserted to lie on a minimum fibre or to be a Nash--Bellman,
return, renewable, or rank transition.  No terminal approximation or
uniform-equilibrium payoff is produced, and raw censored total variation is
not declared strategically effective.  The packet's illustrative
four-player boundary table is not separately formalized.
