# Censored-reshuffle null direction and effect-sensitive participant dispatch

Authors: `CODEX_FOURIER`

Independent review: [censored-reshuffle null-direction audit](../feedback/CODEX_FOURIER__CENSORED_RESHUFFLE_NULL_DIRECTION_NOGO__BY_CODEX_LEBESGUE.md)

## Exact statement

There are four-player quitting rewards, and for every integer `N >= 3`
literal exact Nash laws `p in NE_N` and `q in NE_(N+1)`, with all ties and
`Never` actions included, such that:

1. the newly exposed pure date `N` gains a fixed positive amount against
   `p`;
2. the summed marginal total variation between `p` and the censored law
   `C_N q` can be arbitrarily large relative to that gain;
3. nevertheless `p` and `C_Nq` have the same terminal coalition law and,
   after grafting every common behavioral tail `tau`, preserve the entire
   terminal semantic pair:
   \[
      \operatorname{Sem}(p*\tau)=\operatorname{Sem}((C_Nq)*\tau);
   \]
4. the strategically effective adjacent change is the separate boundary
   participation erased by censoring, not the censored total-variation
   displacement.

Thus macroscopic censored total variation is not by itself a producer or a
valid atlas state.

There is also a positive replacement theorem. In the four-player
projective-spectator chamber, let `i` be the hard boundary observer,
`gamma>0` its selected hard response gain, `R>0` a reward bound,
`a=\gamma/R <= 1`, and `tau` one literal positive-minimum tail satisfying
the uniform singleton separation
\[
 U_j(\tau)-r_j(\{j\})\ge\delta/2>0
 \quad\text{for every }j.
\]
Put `P=L_Np`, `R_c=L_N(C_Nq)`, and define the selected boundary-effect
gauge
\[
 d_{\partial}(P,R_c)
 :=
 \max\left\{
   \max_k|p_k(\infty)-(C_Nq)_k(\infty)|,\,
   \frac{|G_i^0(Q_N;P)-G_i^0(Q_N;R_c)|}{4R}
 \right\}.
\]
Under the exact spectator hypotheses stated in Section 7,
\[
 \boxed{
 d_{\partial}(P,R_c)\ge a/8
 \quad\lor\quad
 \text{a literal minimum-tail paid participant edge of gain at least }
 \frac{27\delta a^4}{4096}.}
\]
The paid endpoints differ only in the mover's complete behavioral stopping
law, so its unrestricted best-response cap is unchanged and its debt falls by
exactly the displayed payoff gain.

A larger finite operational pseudometric `d_eff`, defined from every
`Never` coordinate, every hard prescribed payoff, and every hard pure-time
gain, satisfies
\[
 d_{\mathrm{eff}}(P,R_c)=0
 \Longrightarrow
 \operatorname{Sem}(P*\tau)=\operatorname{Sem}(R_c*\tau)
 \quad\text{for every behavioral tail }\tau,
\]
and yields the reviewed concise alternative
\[
 d_{\mathrm{eff}}(P,R_c)\ge a/8
 \quad\lor\quad
 \text{the same paid participant edge.}
\]

## Conjecture-facing change

The adjacent-deadline minimum-tail reprojection dispatch previously ended in
one unconverted arm: macroscopic censored stopping-law reshuffling. The exact
regression below proves that this metric arm can be graft-universally
strategically null, so it cannot be treated as a renewable producer. The
positive theorem replaces it by operational response and `Never`-coefficient
data. When those data are small, the already retained boundary participation
becomes a source-faithful paid edge with a fixed quantitative floor.

The large operational-effect arm remains open. This packet therefore strictly
repairs and narrows the adjacent-deadline obligation; it does not consume the
remaining Fin4 positive-minimum SCC.

## Definitions, probability mode, and agency

A timing law is a probability law on the available finite dates together with
`infinity`. The players' laws are sampled independently. Ties are retained
and produce the simultaneous quitting coalition. Censoring `C_N` moves
date-`N` mass to `infinity`; lifting `L_N` regards a deadline-`N` law
as a deadline-`N+1` law with zero mass at date `N`.

All equilibrium assertions below include every pure finite date and
`Never`; finite strategic-game mixed Nash is realized by a behavioral
hazard profile. After a common tail is grafted, best-response caps quantify
over unrestricted unilateral behavioral stopping strategies. Their equality
is proved through the exact pure-time supremum representation, not inferred
from finite-game Nash.

## 1. The table

Let the players be `0,1,2,3`.  Player `0` is the boundary observer, player `1`
is the strategically relevant clock, player `2` is the null calendar clock,
and player `3` is a tail marker.

For a nonempty coalition `S`, first define player `0`'s reward away from one
special coalition by

\[
 r_0(S)=
 \begin{cases}
  0,&1\in S,\ 0\in S,\\
  2,&1\in S,\ 0\notin S,\\
  1,&1\notin S,\ 2\in S,\\
  1,&1\notin S,\ 2\notin S,\ 0\in S,\\
  0,&\text{otherwise}.
 \end{cases}
 \tag{1.1}
\]

Override the special coalition by

\[
 r(\{0,3\})=(2,1,1,1).
 \tag{1.2}
\]

For every other coalition put

\[
 r_1(S)=r_2(S)=r_3(S)=0.
 \tag{1.3}
\]

All rewards have absolute value at most `R=2`.

The override (1.2) is invisible in the hard timing profiles below: players
`0` and `3` both use `Never`, so no unilateral finite timing deviation can
produce the coalition `{0,3}`.  It is included only to provide an arbitrary
literal graft tail whose payoff is strictly above every own singleton reward.

## 2. Adjacent Nash laws

Fix `N >= 3` and `c in (0,1)`.  In the deadline-`N` timing game, whose finite
dates are `0,...,N-1`, define `p` by

\[
\begin{array}{c|c}
\text{player}&p\text{-law}\\ \hline
0&\delta_\infty\\
1&\tfrac12\delta_{N-1}+\tfrac12\delta_\infty\\
2&c\delta_0+(1-c)\delta_\infty\\
3&\delta_\infty.
\end{array}
\tag{2.1}
\]

In the deadline-`N+1` game define `q` by

\[
\begin{array}{c|c}
\text{player}&q\text{-law}\\ \hline
0&\delta_\infty\\
1&\tfrac12\delta_{N-1}+\tfrac16\delta_N+\tfrac13\delta_\infty\\
2&c\delta_1+(1-c)\delta_\infty\\
3&\delta_\infty.
\end{array}
\tag{2.2}
\]

Under prescribed `p` and `q`, and under every unilateral timing deviation
from either profile, players `1,2,3` receive zero.  The only coalition on
which the override gives them a nonzero reward is `{0,3}`; it cannot be
created by one deviation because players `0` and `3` are both prescribed
`Never`.  It remains only to check player `0`.

Under `p`, if player `2` stops, player `0` receives `1`.  Conditional on
player `2` choosing `Never`, player `0` receives `2` when player `1` stops
and `0` on all-Never.  Hence

\[
 U_0(p)=c+(1-c)\left(\tfrac12\,2+\tfrac12\,0\right)=1.
 \tag{2.3}
\]

Every pure date strictly below `N-1` pays `1`.  Date `N-1` pays
`c+(1-c)/2 <= 1`, and `Never` pays `1`.  Thus `p` is Nash.  The newly
exposed date `N` pays

\[
 c+(1-c)\left(\tfrac12\,2+\tfrac12\,1\right)
 =\frac32-\frac c2.
 \tag{2.4}
\]

Consequently the hard boundary gain is

\[
 \boxed{\gamma=\frac{1-c}{2}>0.}
 \tag{2.5}
\]

Under `q`, conditional on player `2` choosing `Never`, player `1` stops with
probability `2/3`.  Therefore

\[
 U_0(q)=c+(1-c)\frac43.
 \tag{2.6}
\]

A date below `N-1` has conditional value `1`; date `N-1` has conditional
value `1/2`; and date `N` has conditional value

\[
 \tfrac12\,2+\tfrac16\,0+\tfrac13\,1=\frac43.
 \tag{2.7}
\]

Never also has conditional value `4/3`.  Thus `q` is Nash.

## 3. The whole censored displacement is null

Censoring date `N` in player `1`'s law moves its mass `1/6` to `Never`, so

\[
 (C_Nq)_1=\tfrac12\delta_{N-1}+\tfrac12\delta_\infty=p_1.
 \tag{3.1}
\]

All coordinates except player `2` also agree.  For player `2`, censoring does
nothing, and the two laws differ only by moving mass `c` from date `0` to
date `1`.  Therefore

\[
 \boxed{
 \sum_j\operatorname{TV}(p_j,(C_Nq)_j)=c.}
 \tag{3.2}
\]

This can be arbitrarily close to one.  Relative to the standard normalized
scale `a=gamma/R=(1-c)/4`,

\[
 \frac{\sum_j\operatorname{TV}(p_j,(C_Nq)_j)}{a}
 =\frac{4c}{1-c}\longrightarrow\infty.
 \tag{3.3}
\]

In particular the macroscopic-reshuffle inequality `sum e_j >= a/8` holds
for every `c >= 1/33`.

Nevertheless this whole displacement is strategically null.  Let

\[
 r:=C_Nq.
\]

The only difference between `p` and `r` is whether player `2`'s finite stop
occurs at date `0` or date `1`.  Player `1`'s only finite date is `N-1`, and
`N>=3`.  On the event that player `2` stops, player `0` receives `1` whether
it stops before, simultaneously with, or after player `2`; this is exactly
the third and fourth rows of (1.1).  On the event that player `2` chooses
`Never`, the two profiles are literal equals.  For deviations by players
`1` or `3`, every finite-word outcome that can differ has payoff zero in that
coordinate; the exceptional coalition `{0,3}` cannot be created there.

It follows not only that `U(p)=U(r)`, but that for every player `h` and every
complete behavioral deviation `sigma_h`,

\[
 U_h(p[h\leftarrow\sigma_h])
 =U_h(r[h\leftarrow\sigma_h]).
 \tag{3.4}
\]

For `h=0`, the equality follows from the constant value `1` on the
player-`2` branch; for `h=1,3`, every outcome on which the coupled hard paths
can differ has payoff zero in that coordinate; and for `h=2`, the opponents
are literally unchanged.  Hence

\[
 \boxed{\operatorname{Sem}(p)=\operatorname{Sem}(r).}
 \tag{3.5}
\]

The terminal coalition law also agrees: only the calendar date of the
`{2}` outcome changes.

## 4. Nullity survives every literal graft

Let `tau` be any behavioral tail and graft it after the finite word.  The
joint pass probabilities of `p` and `r` are equal, their finite terminal
coalition laws are equal, and the preceding deviation-by-deviation argument
is unchanged.  Thus

\[
 \boxed{
 \operatorname{Sem}(p*\tau)=\operatorname{Sem}(r*\tau)
 \quad\text{for every behavioral tail }\tau.}
 \tag{4.1}
\]

This includes equality of unrestricted behavioral caps, not only prescribed
payoffs or finite timing deviations.

For a concrete strictly singleton-separated graft, let `tau` make players
`0` and `3` Quit surely at its first date and players `1,2` Continue.  By
(1.2),

\[
 U(\tau)=(2,1,1,1),
 \qquad
 U_i(\tau)-r_i(\{i\})=1\quad\text{for every }i.
 \tag{4.2}
\]

So even a literal tail with the exact uniform singleton separation used by
minimum-fiber reprojection does not make the censored displacement visible.
This tail is itself an exact terminal Nash profile, so the table has `D_*=0`;
no positive-minimum provenance is claimed.

## 5. What actually changes from `p` to `q`

The strategically effective change is not (3.2).  It is player `1`'s
boundary mass

\[
 b_1=q_1(N)=\frac16.
 \tag{5.1}
\]

That mass is erased by censoring and is therefore absent from every `e_j`.
It is precisely what changes player `0`'s newly exposed date from a strict
gain in (2.4) to the Nash tie in (2.7).

Thus this example lies simultaneously in the boundary-participation arm and
the macroscopic-censored-TV arm.  Dispatching to the latter merely because
`sum e_j` is large throws away the actual strategic certificate and retains
only a null calendar coordinate.

## 6. Consequences for the adjacent-deadline programme

The example proves the following exact no-go.

> There is no theorem which, from a positive hard boundary gain and a lower
> bound on summed censored TV alone, lower-bounds any change in prescribed
> payoff, unrestricted cap, pure-response gain, terminal semantic pair, or
> terminal coalition law between the censored endpoints `p` and `C_Nq`.
> Nor can that TV magnitude fund an effectful reward-labelled atom of the
> censored change.

Indeed the entire censored displacement in (3.2) leaves all those objects
unchanged, even after an arbitrary literal graft.  It does carry a
stage-labelled `{2}` atom of mass `c`, at date `0` on one side and date `1`
on the other; what is unchanged is its coalition label, reward effect, and
semantic effect.  Also, the full adjacent data `(p,q)` do produce a paid
boundary-participant edge from `b_1=1/6`.  The no-go concerns only an attempt
to fund progress from the raw censored displacement `p -> C_Nq`.

The finite-versus-Never split should therefore not be represented as the
exclusive dispatch

\[
 \text{boundary participation}\quad\lor\quad
 \text{macroscopic censored reshuffling}.
\]

The two inequalities may hold simultaneously, and only the first can carry
the strategic correction.  The correct finite state must retain at least

* boundary participation `b`;
* the hard response-gain drop or common-response square; and
* a quotient of censored displacement by graft-universal null calendar
  directions.

Equivalently, the metric `sum e_j` should be replaced by an operational
pseudometric built from unilateral payoff differences.  Zero in that
pseudometric is then meaningful: it says the censored change is strategically invisible,
as in (3.4), and should be discarded rather than regenerated as an atlas
node.

This does not prove that every effectful censored reshuffle has a
positive-minimum consumer.  The remaining honest question is narrower:

\[
\boxed{
\begin{array}{c}
\text{hard adjacent response drop after quotienting null clock directions}\\
+\ \text{one positive-minimum literal tail}
\end{array}
\Longrightarrow
\text{paid source chart, return, or renewable rank descent?}
}
\tag{6.1}
\]

## 7. Positive repair: null reshuffling returns to the participant edge

There is nevertheless a complete positive theorem for the null chamber.  It
also gives the correct robust replacement for the raw-TV residual.

On two deadline-`N` product laws define the finite operational pseudometric

\[
\begin{aligned}
 d_{\mathrm{eff}}(P,R):=\max\Bigg\{&
   \max_k|P_k(\infty)-R_k(\infty)|,\\
 &\frac1{2R}\max_h|U_h^0(P)-U_h^0(R)|,\\
 &\frac1{4R}\max_{h,\,t\in\{0,\ldots,N,\infty\}}
   |G_h^0(t;P)-G_h^0(t;R)|\Bigg\}.
\end{aligned}
\tag{7.0}
\]

It is a pseudometric because it is the maximum of absolute differences of a
finite family of real-valued observables.  Its zero classes quotient out
calendar changes which preserve every pure-time gain and every Never
coefficient.  Pure-time extremality means that zero also preserves the hard
unrestricted semantic pair and Nash status.  The regression in Sections 1--5 has
`d_eff(p,C_Nq)=0` although its summed TV is `c`.

More strongly, if `d_eff(P,R)=0`, then for every common behavioral tail
`tau`,

\[
 \operatorname{Sem}(P*\tau)=\operatorname{Sem}(R*\tau).
\tag{7.0a}
\]

Here is the complete cap calculation.  Put

\[
 S_k=P_k(\infty)=R_k(\infty),
 \qquad J=\prod_kS_k,
 \qquad H_h=\prod_{k\ne h}S_k.
 \tag{7.0b}
\]

The exact graft identity is

\[
 U_h(P*\tau)=U_h^0(P)+J U_h(\tau),
 \tag{7.0c}
\]

and identically for `R`.  Both terms agree under `d_eff=0`, so the prescribed
payoffs agree.  Write

\[
 V_h^0(t;P)=U_h^0(P)+G_h^0(t;P).
\]

Every pure stopping date in the finite word has grafted payoff
`V_h^0(t;P)`, hence agrees with its `R` counterpart.  If player `h` passes
the whole word and then uses a pure tail time `s`, its payoff is

\[
 V_h^0(\infty;P)+H_hV_h^\tau(s).
 \tag{7.0d}
\]

The analogous formula holds for tail Never.  The hard term agrees because
both `U^0` and `G^0(\infty)` agree, the coefficient agrees by (7.0b), and the
tail is common.  Taking the supremum over finite prefix dates, every pure
tail time, and tail Never therefore gives equal unrestricted caps.  This is
exactly the pure-time representation of behavioral best response; arbitrary
behavioral randomization is a convex mixture of these stopping endpoints.
Thus (7.0a) follows.  In the checked vocabulary, the last step is the role of
`quittingContinuationBestResponseValue_eq_sSup_pureTimeDeviationPayoff`.

This proves that (7.0), unlike raw TV, quotients exactly the finite-clock
directions invisible to every literal graft.

Let `p in NE_N`, `q in NE_(N+1)`, and put

\[
 P=L_Np,
 \qquad R=L_N(C_Nq),
 \qquad Q=q.
 \tag{7.1}
\]

Fix a boundary observer `i` such that

\[
 G_i^0(Q_N;P)\ge\gamma,
 \qquad
 G_i^0(Q_N;Q)\le0.
 \tag{7.2}
\]

Assume the projective-spectator hypotheses from the preceding source note:

\[
 a:=\gamma/R\le1,
 \qquad
 p_i(\infty)>1-a/8,
 \qquad
 \prod_{k\ne i}p_k(\infty)\ge a.
 \tag{7.3}
\]

The last product implies

\[
 p_k(\infty)\ge a\qquad(k\ne i),
 \tag{7.4}
\]

because all factors lie in `[0,1]`.

Let `tau` be one literal minimum-fiber realizer accurate enough that, for a
fixed `delta>0`,

\[
 U_j(\tau)-r_j(\{j\})\ge\delta/2
 \qquad\text{for every }j.
 \tag{7.5}
\]

Write

\[
 b_j=q_j(N).
\]

### Exact null theorem

Suppose the censored change is null in just the two operational coordinates
needed below:

\[
 G_i^0(Q_N;P)=G_i^0(Q_N;R),
 \qquad
 (C_Nq)_k(\infty)=p_k(\infty)\quad\forall k.
 \tag{7.6}
\]

Then (7.2) gives

\[
 G_i^0(Q_N;R)-G_i^0(Q_N;Q)\ge\gamma.
\]

Moving `b_j` from `Never` to date `N` changes player `j`'s marginal by total
variation exactly `b_j`.  The finite gain Lipschitz estimate therefore gives

\[
 \gamma\le4R\sum_j b_j.
 \tag{7.7}
\]

Choose `j` with

\[
 b_j\ge\frac{\gamma}{4R|I|}.
 \tag{7.8}
\]

Let `P^-:=R`.  Let `P^j` restore only player `j`'s mass `b_j` from `Never`
to date `N`, leaving every opponent censored.  Because (7.6) preserves the
Never vector, every opponent-passage product at this edge has a uniform
floor.  In Fin4,

\[
 H_j^-:=\prod_{k\ne j}(C_Nq)_k(\infty)
 \ge\frac78a^2.
 \tag{7.9}
\]

For `j=i`, use `H_i^- >= a >= 7a^2/8`.  For `j != i`, the product contains
`p_i(infinity)>7/8` and the other two coordinates are at least `a`.

The exact last-date-versus-pass identity now gives the literal reverse edge

\[
\begin{aligned}
 &U_j(P^-*\tau)-U_j(P^j*\tau)\\
 &\qquad=
 b_jH_j^-\bigl(U_j(\tau)-r_j(\{j\})\bigr)\\
 &\qquad\ge
 \frac{7\gamma\delta a^2}{64R|I|}>0.
\end{aligned}
\tag{7.10}
\]

For Fin4 this is `7 gamma delta a^2 / (256 R)`.  Since the two profiles
differ only in player `j`'s complete stopping law, its unrestricted cap is
identical at the endpoints and its debt is reduced by exactly the amount in
(7.10).

Thus:

\[
\boxed{
\text{operationally null censored reshuffle}
\Longrightarrow
\text{a source-faithful paid boundary-participant edge}.}
\tag{7.11}
\]

The null clock in Sections 1--5 therefore causes no new obstruction.  Once it
is quotiented out, the old participant consumer fires on the exact strategic
change.

### Robust effect alternative

The same proof is stable.  Assume instead

\[
 \left|G_i^0(Q_N;P)-G_i^0(Q_N;R)\right|<\gamma/2
 \tag{7.12}
\]

and

\[
 \left|p_k(\infty)-(C_Nq)_k(\infty)\right|<a/8
 \qquad\forall k.
 \tag{7.13}
\]

Then the boundary effect from `R` to `Q` is at least `gamma/2`, so

\[
 \sum_jb_j\ge\frac{\gamma}{8R},
 \qquad
 \max_j b_j\ge\frac{\gamma}{8R|I|}.
 \tag{7.14}
\]

Equations (7.3)--(7.4) and (7.13) give every censored Never coordinate the
uniform floor `3a/4`.  Hence

\[
 H_j^-\ge(3a/4)^{|I|-1}.
 \tag{7.15}
\]

The reverse participant edge therefore has gain at least

\[
 \boxed{
 \frac{\gamma\delta}{16R|I|}
 \left(\frac{3a}{4}\right)^{|I|-1}.}
 \tag{7.16}
\]

For Fin4, this is `27 delta gamma a^3 / (4096 R)`, equivalently
`27 delta a^4 / 4096`.

Consequently the raw reshuffle arm can be replaced by the exhaustive
effect-sensitive dispatch

\[
\boxed{
\begin{aligned}
&\left|G_i^0(Q_N;P)-G_i^0(Q_N;R)\right|\ge\gamma/2\\
{}\lor{}&\exists k,\ 
 |p_k(\infty)-(C_Nq)_k(\infty)|\ge a/8\\
{}\lor{}&\text{a literal minimum-tail paid participant edge with floor
 (7.16).}
\end{aligned}}
\tag{7.17}
\]

In the pseudometric notation (7.0), this has the particularly clean form

\[
\boxed{
 d_{\mathrm{eff}}(P,R)\ge a/8
 \quad\lor\quad
 \text{the paid participant edge (7.16).}}
\tag{7.18}
\]

Indeed `d_eff(P,R)<a/8` implies (7.13), and the selected gain difference is
less than

\[
 4R(a/8)=\gamma/2,
\]

which is (7.12).  At `d_eff=0`, the first branch is impossible and the exact
null theorem (7.11) applies.

Unlike `sum TV`, the first two residual coordinates are operational:

* the first is a specified common-response effect, not movement of a law;
* the second is exactly the coefficient which controls the retained-tail
  seam and opponent-passage floors.

Pure finite-date calendar reshuffling has disappeared from (7.17).  The first
two arms still need their own positive-minimum consumers, so (7.17) is a
strict repair of the atlas interface rather than a solution of Fin4.

## 8. Self-falsification checks

1. **Boundary convention.**  `p` uses dates `0,...,N-1`; `q` additionally
   uses date `N`.  The mass `1/6` is genuinely new boundary participation.
2. **Censor calculation.**  Censoring sends exactly that `1/6` to `Never`,
   restoring player `1`'s old law exactly.
3. **Ties.**  The values at dates `N-1` and `N` include the displayed
   simultaneous coalitions; (2.7) uses reward zero on `{0,1}`.
4. **Never.**  Both Nash checks explicitly include `Never`; it ties the best
   finite action in each game.
5. **Unrestricted deviations after graft.**  Equation (4.1) is not inferred
   from finite-game Nash.  It follows pathwise from the payoff table on the
   player-`2` branch and literal equality on the `Never` branch.
6. **No false positive-minimum claim.**  The special tail is exact Nash, so
   this is deliberately a zero-minimum regression.

7. **Constants in the positive repair.**  The Lipschitz constant is the
   reviewed `4R`; (7.5) uses `delta/2`, and (7.13) is what yields the common
   `3a/4` Never floor.  These account for the factor `16` in (7.16).

## 9. Narrow source audit

The comparison was made against:

* `finiteDeadlineTimingNash_debt_le_adjacentDistance` and the
  finite-versus-Never split in
  `exports/FINITE_DEADLINE_NASH_PROJECTIVE_BOUNDARY_AND_COMPATIBILITY.md`;
* the source-reprojection boundary and its final inequality (5.8) in
  `notes/CODEX_KANTOROVICH__ADJACENT_DEADLINE_MINIMUM_TAIL_REPROJECTION_BOUNDARY.md`;
* `exists_pos_uniformSingletonGap_minimumFiber_of_punishmentNormal` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinFourMinimumFiberIsolation.lean`;
* the hard-deadline regression declarations in
  `UniformEquilibrium/Diagnostics/Quitting/FinFourHardDeadlineTimingNashBarrier.lean`
  and
  `UniformEquilibrium/Diagnostics/Quitting/FinFourHardDeadlineTimingNashUniqueness.lean`.

No checked declaration is claimed for the new table.

The finite timing-game/behavioral correspondence is checked in
`UniformEquilibrium/Diagnostics/Quitting/FiniteDeadlineTimingGame.lean`:

- `quittingTerminalPayoff_finiteDeadlineTimingProfile_eq_mixedEU`;
- `quittingFiniteDeadlineTimingProfile_update_pureTime_eq_mixedEU`; and
- `quittingFiniteDeadlineTimingProfile_isFiniteDeadline`.

The unrestricted-cap step uses
`quittingContinuationBestResponseValue_eq_sSup_pureTimeDeviationPayoff` in
`TerminalSemanticPositiveSlopeRectangle.lean`. Nearby stopping-law affine
identities in `OpponentTightTerminalSemanticRealization.lean` are
`quittingTerminalPayoff_update_stoppingLawBehaviorStrategy_eq_expect` and
`quittingTerminalPayoff_stoppingLawCanonicalizeOn_eq`; neither identifies
the graft-universal null clock direction proved here.

The checked quantile hierarchy does preserve unrestricted semantics and gives
finite-clock density through
`hasEscapeAwareQuantileClockCompression_of_normalized`,
`exists_cofinalFiniteClockSemanticPair_sequence_tendsto`, and
`closure_quittingCofinalFiniteClockSemanticPairs_eq_carrier`. It does not
quotient exact finite-clock laws by operationally null calendar
reparametrizations.

The adjacent-distance, boundary-participation, and raw censored-reshuffle
alternatives are prior reviewed ordinary mathematics in
`FINITE_DEADLINE_NASH_PROJECTIVE_BOUNDARY_AND_COMPATIBILITY.md` and
[`ADJACENT_DEADLINE_MINIMUM_TAIL_REPROJECTION_DISPATCH.md`](../formalized/ADJACENT_DEADLINE_MINIMUM_TAIL_REPROJECTION_DISPATCH.md).
The exact
regression table, universal-graft quotient, and effect-sensitive replacement
dispatch are the new content.

## Adapter and consumer

The arbitrary source data are adjacent exact timing-game Nash laws `p` and
`q`, the selected hard observer `i`, and one literal positive-minimum tail
`tau` with the checked singleton separation. Boundary participation
`b_j=q_j(N)` is retained simultaneously with the censored law rather than
discarded.

If the boundary-effect gauge is below `a/8`, the hard response drop forces
`\sum_j b_j >= \gamma/(8R)`. One participant has
`b_j >= \gamma/(8R|I|)`; the `Never` floors give opponent passage at least
`(3a/4)^(|I|-1)`; and reversing precisely that participant's date-`N`
mass into `Never` over the literal tail gives the paid edge in (7.16).
That edge is an actual unilateral behavioral-strategy update and exactly
subtracts the mover's debt.

If the gauge is at least `a/8`, the output is only a narrower operational
residual. No return, regeneration, or terminal approximation is claimed for
that branch.

## Lean handoff

Suggested narrow declarations are:

```lean
finiteClockOperationalEffectDistance
finiteClockOperationalEffectDistance_zero_graftSemantic_eq
adjacentDeadline_boundaryEffectGauge
adjacentDeadline_boundaryEffectGauge_ge_or_minimumTail_paidParticipant
```

The first equality theorem should use the hard prefix graft identities and
`quittingContinuationBestResponseValue_eq_sSup_pureTimeDeviationPayoff`.
The paid-participant theorem should retain literal `p`, `q`, `C_Nq`,
the boundary masses `b_j`, the selected observer/date, and the actual tail;
it should expose equality of the mover's unrestricted cap and exact debt
subtraction. It should not encode the paid edge or the large-effect
alternative as a hypothesis field.

Useful exact regression checks are the Nash values in Section 2, the
coalition-law equality in Section 3, and the special exact-Nash graft tail in
Section 5.

## Scope and nonclaims

- The displayed table has global minimum debt zero. It is a regression
  against the censored-TV interface, not a counterexample to uniform
  equilibrium.
- A stage-labelled `{2}` atom is present. The nullity claim is equality of
  terminal coalition law, reward semantics, and every grafted unrestricted
  cap; it is not absence of terminal atoms.
- The full adjacent pair `p,q` does contain a paid boundary-participant
  edge. Only the raw censored displacement `p,C_Nq` is null.
- The large selected response-effect or large `Never`-coefficient branch is
  not consumed here.
- No statement in this packet is claimed to be checked in Lean.

## Lean formalization record

Pre-formalization packet SHA-256:
`2478bb86b3992895fc0420d08e6250950a5a80d3ef9dc8e1bf2bc0830301364d`.
The final sentence immediately above records the packet's earlier status and
is superseded by this checked record.

The generic operational-effect and retained-tail semantic layer landed in
commit `0156bc55132ffb47ba6145fc87481f73fd8cbbda`. The concrete Fin4
null-direction regression landed in
`b0000fcb5213f6b25538ba3256b8d46985c4e4d2`. The retained-tail edge
identities used by the positive dispatch landed in
`2678b1a7281422b34a5b04fb67775acceec0de9f`, and the selected/full
operational-effect dispatch landed in
`c8653fc1b520aa9c391fb2ac0de90a5aa5c57d4e`.

The production owners are
`UniformEquilibrium/Diagnostics/Quitting/CensoredFiniteClockOperationalEffect.lean`,
`FinFourCensoredClockNullDirection.lean`,
`AdjacentDeadlineRetainedTailReprojection.lean`, and
`AdjacentDeadlineSelectedBoundaryEffectDispatch.lean`, under the same
Diagnostics directory. The concrete regression is exposed by
`FinFourCensoredClockNullDirection.sum_censoredError_eq_c`,
`FinFourCensoredClockNullDirection.exists_censoredError_div_boundaryScale_gt`,
`FinFourCensoredClockNullDirection.old_censored_new_operationalEffectDistance_eq_zero`,
`FinFourCensoredClockNullDirection.retainedTailSemantic_old_eq_censoredNew`,
`FinFourCensoredClockNullDirection.quittingTerminalOutcomeMass_old_eq_censoredNew`,
and `FinFourCensoredClockNullDirection.regressionCertificate`.

The generic operational quotient is exposed by
`finiteClockOperationalEffectDistance`,
`finiteClockOperationalEffectDistance_zero_graftSemantic_eq`, and
`quittingFiniteDeadlineOperationalEffectDistance_zero_retainedTailSemantic_eq`.
The selected gauge is characterized and compared with the full operational
distance by
`quittingAdjacentDeadlineSelectedBoundaryEffectGauge_eq_zero_iff` and
`quittingAdjacentDeadlineSelectedBoundaryEffectGauge_le_operationalEffectDistance`.
The generic robust alternatives are
`quittingAdjacentDeadline_selectedBoundaryEffectGauge_ge_or_paidReverseParticipant`
and
`quittingAdjacentDeadline_operationalEffectDistance_ge_or_paidReverseParticipant`;
their Fin4 wrappers are
`quittingAdjacentDeadline_selectedBoundaryEffectGauge_ge_or_paidReverseParticipant_finFour`
and
`quittingAdjacentDeadline_operationalEffectDistance_ge_or_paidReverseParticipant_finFour`.
They give the paid floor
`27 * delta * (gamma / bound)^4 / 4096` outside the displayed large-effect
branch.

Exact equality of the selected coordinates gives the sharper floor
`7 * delta * (gamma / bound)^3 / 256` through
`quittingAdjacentDeadline_paidReverseParticipant_finFour_of_selectedBoundaryCoordinates_eq`.
The literal zero corollaries are
`quittingAdjacentDeadline_paidReverseParticipant_finFour_of_selectedBoundaryEffectGauge_eq_zero`
and
`quittingAdjacentDeadline_paidReverseParticipant_finFour_of_operationalEffectDistance_eq_zero`.
The certificate
`QuittingAdjacentDeadlineSelectedEffectPaidReverseParticipant` exposes the
literal own-strategy update, exact payoff identity, unchanged unrestricted
best-response cap, and exact mover-debt subtraction.

Evidence seals are `M` and `L`. The `A` seal is incomplete: the general
dispatch consumes one supplied adjacent exact source and one supplied actual
singleton-separated tail, but no checked theorem jointly selects those inputs
in the required source-facing configuration. The packet has no downstream
`C`; in particular, the large selected-effect and full operational-effect
branches remain unconsumed.

The concrete table has global minimum debt zero and is a regression against
raw censored total variation, not a positive-gap table or a counterexample to
uniform equilibrium. Raw total variation is not promoted to an operational
producer. The selected gauge is bounded by, but is not identified with, the
full operational distance, and no converse from selected-gauge zero to
full-distance zero is claimed. The checked dispatch does not place the tail
on a minimum fibre or make it Nash, and it produces no chronology, return,
renewal, rank descent, terminal approximation, or uniform-equilibrium payoff.
