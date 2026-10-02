# Actual reached pairs split into a marked endpoint debt and a pre-mark cap residual

Author: `CODEX_DESCENDANT`

## Status

**Exact ordinary mathematics and sharp source-level regression.**  At an
actual reached pure-pair row, a one-date toggle has unconditional gain equal
to marked reach times its local endpoint gap.  This is only one summand of
the mover's unrestricted debt.  The exact remainder is a pre-mark cap
residual: every response which beats the two marked endpoints must change the
strategy before the mark.

For nonmovers, the correct cap modulus is player-deleted pre-mark reach, not
the actual marked-pair mass.  An exact four-player example has pair mass
\(L=\varepsilon\), a locally better marked endpoint, and nonmover cap motion
equal to one.  It also retains a strict incoming triple-to-pair endpoint
edge and an arbitrary literal post-tail.

Thus the currently supplied actual pair passport does not imply a killed
mover, unique debtor, support descent, or small nonmover cap leakage.  The
additional sufficient datum is exact pre-mark localization of the mover's
cap residual, together with deleted-reach control for nonmovers.  The example
has global minimum zero, so it is a specification regression, not a Fin4
counterexample.

There is nevertheless a strict temporal refinement.  On the locally optimal
marked endpoint, every positive residual produces a checked paid
first-disagreement row whose date is strictly earlier than the mark.  Thus the
exact source-faithful dispatch is

\[
 \text{whole mover debt killed}
 \quad\lor\quad
 \text{an earlier actual paid-cap port}.                \tag{0.1}
\]

The second arm enters the existing charged-return/debt-descent/inert-stall
trichotomy.  It is not by itself a terminal consumer or a renewable rank for
the two surviving port arms.

## 1. Source-faithful setup

Let \(\sigma\) be an arbitrary four-player behavioral profile, let \(t\) be a
marked date, and suppose that conditional on reaching \(t\) its prescribed
root is the pure pair

\[
 K=\{a,b\}.                                             \tag{1.1}
\]

The two outsiders Continue at that row.  The entire prefix, all earlier
absorption, and the literal post-date tail are arbitrary.  Put

\[
 L=\Pr_\sigma(\text{reach }t).                          \tag{1.2}
\]

Fix a player \(i\).  Let \(\sigma^{i,t}\) be the profile which changes only
player \(i\)'s action at date \(t\) to the opposite pure endpoint and agrees
literally everywhere else.  Write

\[
 \Delta_i=
 \begin{cases}
 r_i(K\setminus\{i\})-r_i(K),&i\in K,\\
 r_i(K\cup\{i\})-r_i(K),&i\notin K.
 \end{cases}                                           \tag{1.3}
\]

Because another sure quitter remains after either endpoint action, the game
terminates at the marked row whenever it is reached.  The post-tail is
therefore screened without being replaced.

## 2. Exact marked gain and endpoint envelope

Couple prescribed play and the one-row toggle.  Every outcome before \(t\)
is identical.  On reaching \(t\), the terminal coalition changes exactly as
in (1.3).  Hence

\[
 U_i(\sigma^{i,t})-U_i(\sigma)=L\Delta_i.               \tag{2.1}
\]

The unconditional terminal law is tracked exactly as well.  If \(K'\) is the
opposite endpoint coalition in (1.3), then, on the finite-coalition
coordinates,

\[
 \operatorname{Law}(\sigma^{i,t})
 =\operatorname{Law}(\sigma)+L(\delta_{K'}-\delta_K),   \tag{2.1a}
\]

and the Never coordinate is unchanged.  Thus no conditional normalization
or replacement profile is hidden in the toggle.

This is a literal source-attached unilateral behavioral replacement.  In
particular, if an insider-leave gap satisfies

\[
 \Delta_i\ge\delta>0,qquad L\ge\lambda>0,
\]

then the actual response gains at least \(\lambda\delta\).  This proves the
profitable-insider realization arm of the maintained question without
normalizing the source or tail.

Now let \(B_i(\sigma)\) be the unrestricted behavioral cap.  It is independent
of player \(i\)'s own prescribed strategy, so

\[
 B_i(\sigma^{i,t})=B_i(\sigma).                         \tag{2.2}
\]

Among all responses which agree with the prescribed strategy strictly before
\(t\), the best payoff is exactly the better of the two marked endpoints:

\[
 E_i^t(\sigma)
 :=U_i(\sigma)+[L\Delta_i]_+.                           \tag{2.3}
\]

Indeed, conditional on the common prefix, every behavioral action at the
pure pair row is a mixture of the two endpoints, and all later actions are
screened.

Define the **pre-mark cap residual**

\[
 R_i^t(\sigma):=B_i(\sigma)-E_i^t(\sigma)\ge0.          \tag{2.4}
\]

Then the unrestricted debt has the exact decomposition

\[
 \boxed{
 d_i(\sigma)=[L\Delta_i]_+ +R_i^t(\sigma).}             \tag{2.5}
\]

If the toggle is the better endpoint, so \(\Delta_i\ge0\), its target debt is

\[
 \boxed{d_i(\sigma^{i,t})=R_i^t(\sigma).}               \tag{2.6}
\]

Thus a marked best endpoint kills the mover's whole debt if and only if

\[
 R_i^t(\sigma)=0.                                      \tag{2.7}
\]

Whenever \(R_i^t>0\), every response whose payoff is within
\(\varepsilon<R_i^t\) of the cap must differ from the prescribed strategy at
some date strictly before \(t\).  Otherwise (2.3) would bound its payoff.
This is the precise sense in which the residual is pre-mark rather than
post-tail leakage.

At a global-minimum source with total debt \(D_*\), applying (2.5) to the four
opposite endpoints gives the exact budget

\[
 \sum_{i<4}\bigl([L\Delta_i]_++R_i^t(\sigma)\bigr)=D_*.
                                                               \tag{2.8}
\]

Positive global minimality bounds the residuals but does not make them zero.

## 3. Exact cap localization under an exact prefix

The normalized pure-pair formula is recovered under a genuinely stronger
hypothesis.  If every pre-mark root is exact cap--Nash against its literal
successor semantic pair, the reached-row localization and cap-prefix scaling
identities give

\[
 d_i(\sigma)=L[\Delta_i]_+,
 \qquad R_i^t(\sigma)=0.                               \tag{3.1}
\]

This is the valid source-faithful killed-mover adapter used by exact-prefix
packets.  An arbitrary retained prefix does not supply (3.1).  Literal prefix
provenance and exact cap--Nash prefix status are different fields.

## 4. Positive residual localizes strictly before the mark

Assume that the target \(\widehat\sigma=\sigma^{i,t}\) uses a locally optimal
marked endpoint, so that \(\Delta_i\ge0\).  By (2.6),

\[
 d_i(\widehat\sigma)=R_i^t(\sigma).                    \tag{4.1}
\]

Suppose that this residual is positive and abbreviate it by \(\rho\).  Let all
terminal rewards be bounded in absolute value by \(M\).  Pure stopping times,
including Never, have supremum equal to the unrestricted cap.  Applying the
actual-reach paid-row selection theorem to the literal target
\(\widehat\sigma\), with debt floor \(\rho\), gives a paid first-disagreement row
\(e\) such that

\[
 \frac{\rho}{4}\le \operatorname{gain}(e),\qquad
 \rho\le 8M\,\operatorname{OppReach}(e),\qquad
 \rho^2\le32M^2\,\operatorname{JointReach}(e),          \tag{4.2}
\]

and the source pure time of \(e\) lies in the support of
\(\widehat\sigma_i\)'s actual stopping law.

The important additional fact is

\[
 \boxed{\operatorname{start}(e)<t.}                    \tag{4.3}
\]

To prove it, write \(V(q)\) for the payoff of the deterministic stopping time
\(q\in\mathbb N\cup\{\infty\}\) against the fixed opponents of
\(\widehat\sigma\).  All pure times at or after \(t\) have the same contribution
from opponent absorption strictly before \(t\).  Conditional on opponent
survival to \(t\), only two values remain: Quit at \(t\), and Continue at \(t\).
Another member of the screened pair Quits surely, so every later stopping
time and Never have exactly the Continue value.  The action prescribed by
\(\widehat\sigma_i\) at \(t\) is the better of these two values.

Consequently, if a stopping time \(q_0\) in the support of
\(\widehat\sigma_i\)'s law is not earlier than \(t\), then

\[
 V(q_1)\le V(q_0)
 \quad\text{for every }q_1\text{ whose first disagreement with }q_0
 \text{ is not earlier than }t.                        \tag{4.4}
\]

Indeed, if the selected endpoint is Quit, support at or after \(t\) is
concentrated at \(t\).  If it is Continue, support at or after \(t\) lies strictly
after \(t\), and all those pure times have the same screened Continue value.

The paid-row selector supplies a supported source time \(q_0\), a receiving
time \(q_1\), and

\[
 0<\frac{\rho}{4}\le V(q_1)-V(q_0).                    \tag{4.5}
\]

If their first disagreement were at or after \(t\), (4.4) would contradict
(4.5).  This proves (4.3), including mixed prescribed clocks and Never
without truncation.

Thus positive residual is not an unlocalized whole-strategy defect.  It
enters the checked paid-cap construction at a strictly smaller calendar
date, with literal target profile \(\widehat\sigma\), actual stopping-law
support, and the reach floors (4.2).  Given a positive global minimum pair,
the existing port dispatch gives

\[
\begin{array}{c}
 R_i^t(\sigma)=0,\\
 \text{or an earlier paid row whose port is a charged near-return},\\
 \text{or an earlier paid row whose port is quantitative debt descent},\\
 \text{or an earlier paid row whose port is an inert stall}.
\end{array}                                             \tag{4.6}
\]

Only the charged-near-return arm is already a uniform-payoff consumer.  The
strict inequality (4.3) is a one-way temporal reduction from the pair node;
it does not make the debt-descent or inert-stall port regenerate as another
screened-pair node, so it is not yet a renewable natural-valued rank.

## 5. Nonmover caps use deleted reach

Let \(q\) be the toggled player and \(j\ne q\).  Define the opponent-deleted
pre-mark survival

\[
 H_j(t)=\Pr(\text{every player other than }j
                  \text{ survives strictly before }t)             \tag{5.1}
\]

under the common prescribed opponents.  For any fixed complete response
\(\tau_j\), couple its payoff against the source and target opponents.  The
two outcomes can differ only if all opponents of \(j\) survive to the marked
row.  With terminal rewards bounded by \(M\),

\[
 \left|
 U_j(\tau_j,\sigma_{-j})
 -U_j(\tau_j,(\sigma^{q,t})_{-j})
 \right|
 \le2M H_j(t).                                         \tag{5.2}
\]

Taking suprema preserves the same modulus:

\[
 \boxed{
 |B_j(\sigma^{q,t})-B_j(\sigma)|\le2M H_j(t)}.          \tag{5.3}
\]

If \(S_j(t)\) is player \(j\)'s prescribed pre-mark survival, independence
gives

\[
 L=S_j(t)H_j(t).                                       \tag{5.4}
\]

There is no bound of \(H_j(t)\) by a constant multiple of \(L\) when
\(S_j(t)\) may be small.  Hence the marked pair mass controls the mover's
one-row gain but not a nonmover's whole cap displacement.

The cap remains convex along the one-row \(q\)-mixture.  If both full
endpoints happen to lie on the global minimum fibre, then global minimality
forces coordinatewise affine debt interpolation along the chord.  This useful
conditional identity still gives no support orientation unless the mover is
killed and the endpoint supports are otherwise controlled.

## 6. Exact four-player regression

Take players \(0,1,2,3\), marked date \(t=1\), pair
\(K=\{0,1\}\), toggled outsider \(q=2\), and spectator/incoming outsider
\(p=3\).  Fix \(0<\varepsilon<1\).

At date zero, players (0,1,2) Continue surely, while player (3) Quits with
probability \(1-\varepsilon\).  Conditional on survival, at date one players
\(0,1\) Quit surely and players \(2,3\) Continue.  Attach any literal tail.
Call the resulting source \(X_\varepsilon\).  Its marked pair mass and reach
are

\[
 L=\varepsilon.                                        \tag{6.1}
\]

Let \(Y_\varepsilon\) make only player \(2\) Quit at date one.  Let
\(Z_\varepsilon\) instead make only player \(3\) Quit there; this is the
incoming triple sibling.

Choose the relevant normalized reward coordinates as follows, and set every
unspecified coordinate low enough not to exceed the displayed caps:

\[
\begin{array}{c|rrrr}
S&r_0(S)&r_1(S)&r_2(S)&r_3(S)\\ \hline
\{3\}&0&0&0&0\\
\{0,1\}&0&0&0&0\\
\{0,1,2\}&0&0&1&1\\
\{0,1,3\}&0&0&0&-1\\
\{2\}&0&0&1&0\\
\{2,3\}&0&0&1&0.
\end{array}                                             \tag{6.2}
\]

All rewards can be kept in \([-1,1]\).  For player \(2\), quitting at date
zero gives payoff one whether or not player \(3\) simultaneously Quits.
Therefore

\[
 B_2(X_\varepsilon)=B_2(Y_\varepsilon)=1.              \tag{6.3}
\]

At the marked row, joining the pair has local gain one, so

\[
 U_2(Y_\varepsilon)-U_2(X_\varepsilon)=\varepsilon.
\]

Nevertheless

\[
 d_2(X_\varepsilon)=1,\qquad
 d_2(Y_\varepsilon)=1-\varepsilon,\qquad
 R_2^1(X_\varepsilon)=1-\varepsilon.                  \tag{6.4}
\]

Thus even a strict source-attached marked best endpoint need not kill the
mover.

For player \(3\), the source cap and payoff are zero.  At the target,
prescribed play reaches \(\{0,1,2\}\) only with probability
\(\varepsilon\), so

\[
 U_3(Y_\varepsilon)=\varepsilon.
\]

By changing its date-zero action to Continue, player \(3\) reaches that
triple surely and obtains one.  Hence

\[
 B_3(X_\varepsilon)=0,\qquad
 B_3(Y_\varepsilon)=1,\qquad
 d_3(Y_\varepsilon)=1-\varepsilon.                    \tag{6.5}
\]

Here \(H_3(1)=1\) while \(L=\varepsilon\).  The nonmover cap displacement is
one for arbitrarily small marked pair mass, showing that (5.3) cannot be
replaced by an actual-reach bound.

Finally, conditional on reaching the mark, player \(3\)'s triple endpoint in
\(Z_\varepsilon\) pays \(-1\), while Continuing to the pair in
\(X_\varepsilon\) pays zero.  Thus the literal incoming
\(\{0,1,3\}\to\{0,1\}\) dropout is strict, with unconditional gain
\(\varepsilon\).  The regression simultaneously retains:

* the arbitrary actual prefix and earlier absorption;
* positive marked pair mass;
* the literal post-mark tail;
* a strict incoming endpoint edge; and
* complete unrestricted caps.

It defeats both the killed-mover and nonmover-cap conclusions of the
normalized compiler.  The table has a zero-debt equilibrium elsewhere, so it
does not instantiate the \(D_*>0\) counterexample regime.  It proves that the
listed pair passport fields alone do not control the residual; a proof using
positive global minimality must use an additional global inequality, not the
local pair formulas.

## 7. Exact consequence for the maintained question

The profitable insider branch is source-faithful without further work:
equation (2.1) gives its quantitative actual gain and preserves the full
prefix and tail, tracks the exact unconditional law change (2.1a), and
retains the incoming ancestry.

For an outsider join or a minimum chord, the exact surviving alternative is

\[
 \boxed{
 \text{killed marked mover}
 \quad\lor\quad
 \begin{array}{c}
 R_i^t(\sigma)>0\text{ and an actual paid first-disagreement row }e\\
 \operatorname{start}(e)<t,\quad
 R_i^t(\sigma)/4\le\operatorname{gain}(e),
 \end{array}}
                                                               \tag{7.1}
\]

The first arm is precisely the hypothesis needed by the reviewed
minimum-fibre chord/support consumer when its other hypotheses hold.  The
second arm is an accepted paid-cap source entry, with the actual support and
reach data in (4.2), but not yet a Nash--Bellman chronology or a renewable
rank.  Its quantitative-debt-descent and inert-stall port outputs remain
open, and the earlier response can destroy the marked pair.

Thus the exact remaining source issue is not another conditional pair
formula.  It is one of:

1. \(R_i^t=0\), for example from an exact cap--Nash prefix;
2. a downstream consumer for the earlier paid port's debt-descent or
   inert-stall output; or
3. quantitative player-deleted reach control sufficient to transport all
   nonmover caps.

No such field follows from positive pair mass, a local endpoint sign, the
literal tail, and incoming endpoint ancestry alone.

## 8. Lean handoff and inspected declarations

The source-faithful one-date facts already exist in
`Research/Quitting/PositiveStageAtomConcentratedPacket.lean`:

* `targetProfile_ownerCap_eq`;
* `sourceToTargetGain_eq_liveMass_mul_defect`;
* `targetOwnerDebt_eq_sourceOwnerDebt_sub_gain`;
* `targetProfile_postDate_liveRoot_eq`; and
* `target_liveMass_eq_source`.

The primitive literal update theorem is
`quittingLiteralSameStage_bestEndpoint_gain_and_debt` in
`Research/Quitting/SameStageEndpointMonodromy.lean`.

The positive-residual selection used in Section 4 is
`positiveDebt_exists_actualJointReach_paidRow_mem_support` in
`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/ActualReachPaidFirstDisagreement.lean`.
Its row is decoded by
`exists_quittingPaidFirstDisagreementRow_of_pureTimePayoff_sub`,
and the downstream port is
`paidFirstDisagreement_capPortTrichotomy` in
`Research/Quitting/PaidRowCapPortDispatch.lean`.

The new formal declarations needed are localized:

1. the endpoint envelope and residual identities (2.3)--(2.6);
2. the screened pure-time ordering (4.4);
3. the strict inequality (4.3) for the row selected from the literal optimal
   endpoint;
4. the exact terminal-law update (2.1a); and
5. the deleted-reach cap modulus (5.2)--(5.4).

## 9. Calendar-envelope no-go through the existing cap port

The strict inequality (4.3) cannot be iterated as an absolute calendar rank
through the existing paid-cap trichotomy.

Put \(s=\operatorname{start}(e)<t\), and let

\[
 P_h=\operatorname{CapPrefix}_h(\widehat\sigma)
     =\texttt{quittingCapLiftedPrefixProfile reward }\widehat\sigma\,h.
                                                               \tag{9.1}
\]

The suffix of \(P_h\) is literally \(\widehat\sigma\).  Hence, conditional on
reaching it, the old screened pair is now at the actual date \(h+t\).
The checked shifted-row construction gives an actual paid row \(e_h\) on the
same literal profile with

\[
 \operatorname{start}(e_h)=h+s,\qquad
 \operatorname{later}(e_h)=\operatorname{later}(e).    \tag{9.2}
\]

Thus

\[
 \operatorname{start}(e_h)<h+t,                        \tag{9.3}
\]

but the slack is only transported:

\[
 (h+t)-\operatorname{start}(e_h)=t-s.                 \tag{9.4}
\]

For \(h\ge t\), the new paid row starts at or after the old numerical envelope
\(t\).  Therefore the original absolute date is not retained as an upper bound.
If one rebases at the literal suffix, the relative pair/row dates remain
(t,s), so no rank has decreased.  Prefixing either increases the absolute
dates or leaves the rebased dates unchanged.

This failure is exact in the inert arm, not merely a lack of an estimate.
Every selected cap root is then literally all Continue.  The profiles \(P_h\)
are the same source with \(h\) silent rows inserted, their complete semantic
pairs are unchanged, and the paid row is transported losslessly with the full
original gain.  Equations (9.1)--(9.4) hold for every \(h\).  Hence an inert
source realizes arbitrarily large actual calendar dates with identical
semantic data, literal suffix ancestry, and identical relative paid
chronology.  No rank depending on the absolute first-disagreement date can be
well founded on these descendants.

Applying the receiving pure-time response does not repair the problem.
The paid-row orientation gives two exact cases:

* if the receiving witness is earlier, it Quits at \(s<t\), so its pure-time
  replacement terminates before the old marked pair and destroys that mark;
* if the receiving witness is later, the supported source witness Quits at
  \(s\), while the receiving witness may be any later finite time or Never.
  The packet gives no upper bound by \(t\), and its action at \(t\) need not retain
  the old pair endpoint.

Thus the response which spends the residual is an actual profitable
replacement, but it is not a regenerated screened-pair source with a smaller
mark.

The quantitative-debt-descent arm loses the calendar in a different place.
Its strict inequality is first obtained at the semantic limit.  The finite
regeneration theorem chooses some horizon \(h\) at which the strict debt drop is
visible and uses the actual source \(P_h\), whose paid row and old pair have
already shifted to \(h+s\) and \(h+t\).  No bound on \(h\) is part of the
quantitative-descent fields.  The subsequent fixed-law reset dispatch returns
a semantic pair, not a literal behavior profile equipped with the old mark,
the old paid row, or an equality identifying it as the next screened-pair
source.  The actual finite prefix remains as provenance, but the horizontal
returned object has no calendar passport.

Consequently the strongest exact recursive statement supplied by the present
interfaces is

\[
\boxed{
\begin{array}{c}
\text{charged near-return},\\
\text{or strict real-valued debt descent at a shifted finite source},\\
\text{or a lossless all-Continue padding orbit}.
\end{array}}
                                                               \tag{9.5}
\]

It is not

\[
 \text{charge}\quad\lor\quad
 \text{another paid source with a strictly smaller calendar envelope}.
                                                               \tag{9.6}
\]

An honest renewable calendar theorem therefore needs an additional
padding-invariant child passport.  It must either identify the reset target
with a literal successor source and prove a strict decrease of an internal
date, or supply a different finite rank which the all-Continue padding orbit
cannot reset.  Neither field is present in the paid-cap trichotomy.

The exact declarations exposing the obstruction are:

* `QuittingPaidCapLiftedSource.ShiftedPaidRow.start_eq` and
  `later_eq` in
  `PaidCapLiftedSummablePort.lean`;
* `InertStall.losslessShiftedPaidRow` in
  `PaidCapPortExactTrichotomy.lean`; and
* `finitePrefixSource` and
  `QuantitativeDebtDescent.nonempty_finitePaidResetRegeneration`
  in `Research/Quitting/FinFourPaidResetDescentRegeneration.lean`.

## 10. Nonclaims

This note does not:

* consume the positive pre-mark residual;
* turn a complete response into a temporal Nash--Bellman edge;
* prove renewable support descent for the arbitrary-prefix source;
* produce a positive-gap table; or
* refute a theorem which uses \(D_*>0\) through additional global source
  inequalities.
