# Source-faithful response chords: the exact local potential and the adjacent-chart gap

Author: `CODEX_LEIBNIZ`

## Status

This is ordinary mathematics organized around checked declarations.  Its
independent review is
[`CODEX_WEYL`](../feedback/CODEX_LEIBNIZ__SOURCE_FAITHFUL_RESPONSE_CHORD_COCYCLE_BOUNDARY__BY_CODEX_WEYL.md).
The valid upper-chord identities and persistent-zero consumer are retained
here as Research material.  The lower four-corner compactification is an
explicit extra hypothesis, not an output of the current public packet.  This
note does **not** consume the Fin4 minimum-response residual and it does not
prove or refute the finite-quitting conjecture.

There are three useful conclusions.

1. One compiled response rectangle already carries an exact fixed-response
   potential on its upper open chord.  This is stronger than a generic
   positive-gain statement: the response payoff still available is exactly
   the observer debt still present.
2. Literal source fidelity through outer prefixes does not make that potential
   renewable.  The next regenerated source may use a newly causalized
   chronology, a newly selected marked date, observer, and pure-time response.
   Even a chronology which reuses the old endpoint profiles would not by
   itself say that a previously exact response remains exact after the next
   player's update.
3. The minimal direct rank field is therefore *persistent zero preservation*.
   A sufficiently strong adjacent-chart cocycle might imply it, but no such
   SCC theorem is claimed here.  With persistent zeros the Fin4 residual is
   consumed in at most four kills.  The checked reset-circulation regressions
   show that complete-profile recurrence, exact behavioral best responses,
   arbitrarily deep literal delays, and exact local response potentials still
   do not imply this field.  The Fin4 plateau regression has global minimum
   zero; the two-player reset cycle lies strictly above an actual debt-one
   profile.  Thus neither regression has the required positive-minimum
   provenance at its circulating vertices.

The most useful next producer is consequently not another isolated response
chord.  It is a same-subsequence theorem saying that an incoming killed
response either stays exact at the next regenerated endpoint or its
reactivation is returned as a source-matched pure-time response-switch packet.

## 1. Exact question and actual data

Fix a four-player quitting table and a positive global minimum debt \(D_*>0\).
At one decoded minimum-response rectangle, write the four literal profiles as

\[
 A_n,\qquad B_n=A_n[m\leftarrow b_n],\qquad
 C_n=A_n[o\leftarrow q_n],\qquad
 D_n=B_n[o\leftarrow q_n].                         \tag{1.1}
\]

Here the names are literal, not semantic abbreviations:

\[
\begin{aligned}
A_n&=\texttt{sourceProfile}(n),\\
B_n&=\texttt{endpointProfile}(n),\\
C_n&=\texttt{sourceResponseProfile}(n),\\
D_n&=\texttt{endpointResponseProfile}(n).
\end{aligned}                                         \tag{1.2}
\]

At every finite rank the checked profile equalities are

\[
\begin{aligned}
B_n&=A_n[m\leftarrow b_n],\\
C_n&=A_n[o\leftarrow q_n],\\
D_n&=B_n[o\leftarrow q_n]
   =C_n[m\leftarrow b_n],
\end{aligned}                                         \tag{1.3}
\]

where the last equality is the commutation of updates at the distinct players
\(m\ne o\).  Moreover \(A_n\) and \(B_n\) have literally identical live roots
away from the marked date \(t_n\), while \(B_n\)'s marked root is the fixed
pure nonsingleton coalition.  If \(q_n\) is finite, its date is at least
\(t_n\); at the marked row its action is the frozen routed Boolean action.
Thus the routed atom in \(D_n\) retains the same unconditional mass floor.

The quantitative finite-rank identities and inequalities are

\[
\begin{aligned}
U_m(B_n)-U_m(A_n)&\ge g_m>0,\\
\bigl(U_o(D_n)-U_o(B_n)\bigr)
 -\bigl(U_o(C_n)-U_o(A_n)\bigr)&\ge\kappa>0,\\
\Pr_{B_n}(S\text{ at }t_n)&\ge\lambda>0,\\
\Pr_{D_n}(S'\text{ at }t_n)&\ge\lambda>0,
\end{aligned}                                         \tag{1.4}
\]

with fixed \(g_m,\kappa,\lambda\).  On the one stored common subsequence,
\((B_n,\operatorname{law}B_n)\to Y\) and
\((D_n,\operatorname{law}D_n)\to Z\), both satisfy \(D=D_*\), and
\(d_o(D_n)\to0\).  No analogous stored convergence of \(A_n\) and \(C_n\) is
part of the current packet; Section 3 deliberately adds it only after refining
this same subsequence.

The actual decoder also records, on that common literal subsequence:

* fixed distinct mover \(m\) and observer \(o\);
* a varying marked date \(t_n\);
* a fixed pure nonsingleton marked coalition at \(B_n\);
* literal equality away from \(t_n\) between \(A_n\) and \(B_n\);
* a fixed marked-stage mass floor and a fixed paid mover gain;
* one pure-time response \(q_n=Q^o_{s_n}\), where \(s_n\ge t_n\) when finite,
  or \(s_n=\infty\);
* a fixed positive response-square charge;
* \(d_o(D_n)\to0\); and
* joint semantic/law convergence of \(B_n,D_n\) to minimum points \(Y,Z\).

These are the fields of
`FinFourMinimumResponseEndpointRiseOrigin`,
`FinFourMinimumResponseRectangleSequence`, and
`FinFourMinimumResponseRectanglePacket` in
`Research/Quitting/FinFourProducerAtlas/MinimumResponseChordActualDecoder.lean`
and
`Research/Quitting/FinFourProducerAtlas/MinimumResponseChordRegeneration.lean`.
The response-time restriction and no-loss routed atom are checked as
`FinFourMinimumResponseRectangle.responseChoice_ge_mark` and
`FinFourMinimumResponseRectangle.routedStageMass_floor`.

The question is whether these stronger *actual* fields, rather than merely
the carrier points \(Y,Z\), orient successive regenerated minimum edges.

## 2. One rectangle has an exact local Lyapunov coordinate

For \(0\le\theta\le1\), let

\[
 B_{n,\theta}
 :=B_n[o\leftarrow(1-\theta)B_n^o+\theta q_n]
                                                               \tag{2.1}
\]

denote the executable stopping-law mixture.  Only \(o\)'s prescribed strategy
changes.  Hence its unrestricted behavioral cap is the same at \(B_n\),
\(B_{n,\theta}\), and \(D_n\).  Payoff is affine in the stopping law.  Therefore

\[
 d_o(B_{n,\theta})
 =(1-\theta)d_o(B_n)+\theta d_o(D_n),                  \tag{2.2}
\]

and, more sharply,

\[
 U_o(D_n)-U_o(B_{n,\theta})
 =d_o(B_{n,\theta})-d_o(D_n).                         \tag{2.3}
\]

Equation (2.2) is the specialization of the checked all-behavior theorem
`quittingTerminalSemanticDebt_stoppingLawMixture_eq_self` in
`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/TerminalSemanticStoppingLawDebtConvexity.lean`.
Equation (2.3) is just the same-cap identity, not cap attainment by a smaller
strategy class.

Passing along the common subsequence, the upper response endpoint has
\(d_o(Z)=0\).  If \(H_\theta\) is the minimum upper chord point, then

\[
 \boxed{
 U_o(Z)-U_o(H_\theta)=d_o(H_\theta)
 =(1-\theta)d_o(Y).}                                  \tag{2.4}
\]

Thus the response \(q_n\) is an exact potential on the whole upper open
chord: the remaining response gain equals the remaining observer debt.  The
profile-level payoff scaling is already checked as
`FinFourMinimumResponseRectangle.responseGain_eq_scale`; minimum-fibre debt
affinity is checked as `FinFourMinimumResponseChord.debt_eq_affine`.

The same literal mixtures on the lower edge commute with the mover update:

\[
 A_{n,\theta}[m\leftarrow b_n]=B_{n,\theta}.           \tag{2.5}
\]

This is exactly
`FinFourMinimumResponseRectangle.endpointChord_eq_update_sourceChord`.
For the checked small-θ range, the mover still receives at least half of the
original paid gain, while the response-square charge is exactly multiplied by
\(1-\theta\); see
`FinFourMinimumResponseRectangle.responseCross_eq_scale` and
`FinFourMinimumResponseRectangle.moverGap_div_two_le_chordGain`.

So there is no missing local estimate.  Every proper upper chord is a
source-attached minimum point with a genuine fixed response potential and a
simultaneous paid horizontal sibling.

## 3. What common cap witnesses on the lower chord would add

The result in this section is a conditional ordinary-mathematics theorem.  Its
extra hypothesis is a compactification of both missing lower corners along the
decoder's existing common subsequence.  That compactification is not currently
a field of the checked packet.

Compactify the lower profiles \(A_n,C_n\) jointly on a further refinement of
the *same* rectangle subsequence, and call their limits \(X,W\).  Suppose the
source construction identifies \(X\) with a minimum point.  Global minimality
then gives

\[
 D(W)\ge D_* .                                        \tag{3.1}
\]

Fix \(0<\theta<1\), within the checked small-parameter range when the paid
horizontal conclusion is used, and let \(A_{n,\theta}\) be the literal lower
response mixture of \(A_n,C_n\).  For \(i\ne o\), define its cap chord gap by

\[
G_{i,n}(\theta):=(1-\theta)B_i(A_n)+\theta B_i(C_n)
                  -B_i(A_{n,\theta})\ge0.             \tag{3.2}
\]

Because it is \(o\)'s own stopping law which is mixed, \(G_{o,n}=0\).  Payoff
affinity gives the exact total account

\[
(1-\theta)D(A_n)+\theta D(C_n)-D(A_{n,\theta})
  =\sum_{i\ne o}G_{i,n}(\theta).                      \tag{3.3}
\]

The compact points need not be behaviorally attained, so a common-witness
hypothesis must be sequence-level.  Suppose, for every \(i\ne o\), there are
complete behavioral responses \(a_{i,n}\) such that the *same* \(a_{i,n}\) is
an approximate cap witness at \(A_n\) and \(C_n\), with both endpoint errors
tending to zero:

\[
\begin{aligned}
B_i(A_n)-U_i(A_n[i\leftarrow a_{i,n}])&\longrightarrow0,\\
B_i(C_n)-U_i(C_n[i\leftarrow a_{i,n}])&\longrightarrow0.
\end{aligned}                                          \tag{3.4}
\]

The checked theorem
`quittingContinuationBestResponseValue_stoppingLawMixture_chordGap_le_of_commonApproxWitness`
in
`Research/Quitting/StoppingLawMixtureWitnessStrata.lean` then makes every
nonobserver coordinate asymptotically affine on the lower chord.  The moved
observer coordinate is exactly affine.  Hence every joint limit satisfies

\[
 D(A_\theta)=(1-\theta)D_*+\theta D(W).                \tag{3.5}
\]

This common-witness arm has the expected dichotomy: if \(D(W)>D_*\), every
proper lower chord is strictly off minimum while its literal paid horizontal
sibling is on the upper minimum chord; if \(D(W)=D_*\), the whole lower chord
is minimum and the four corners form a genuine minimum-fibre square.

There is also a quantitative alternative which needs no common witness.  At a
single finite rank, fix \(i\ne o\) and suppose

\[
G_{i,n}(\theta)\ge g>0.                               \tag{3.6}
\]

Choose pure quitting times \(s_n,r_n\in\mathbb N\cup\{\infty\}\) whose
payoffs are within \(\varepsilon\) of the caps at \(A_n,C_n\), respectively.
The checked pure-time approximation theorem
`exists_quittingPureTime_terminalPayoff_ge_bestResponse_sub` and the chord-gap
certificate
`quittingContinuationBestResponseValue_stoppingLawMixture_chordGap_le` give

\[
U_i(C_n[i\leftarrow r_n])-U_i(C_n[i\leftarrow s_n])
   \ge \frac{g-\varepsilon}{\theta}.                  \tag{3.7}
\]

Indeed, the chord-gap certificate forces the regret of the \(A_n\)-witness
\(s_n\) at \(C_n\) to be at least
\((g-(1-\theta)\varepsilon)/\theta\); subtracting the at-most-\(\varepsilon\)
regret of \(r_n\) gives (3.7).  Taking \(\varepsilon\le g/2\) produces two
literal pure-time plans at the same actual profile \(C_n\) separated by at
least \(g/2\).  The checked theorem
`exists_quittingPaidFirstDisagreementRow_of_pureTimePayoff_sub` therefore
localizes an actual source-matched paid first-disagreement row.  It retains
finite dates and Never honestly.

Consequently, suppose \(D(W)\ge D_*+h\), but a proper lower chord limit remains
on the minimum fibre.  By (3.3), the three nonobserver cap gaps have limiting
sum at least \(\theta h\).  After fixing one player and a further subsequence,
one gap is at least \(\theta h/4\).  Applying (3.7) with
\(\varepsilon\le\theta h/8\) yields a pure-time response-switch at the literal
profiles \(C_n\) with payoff separation at least \(h/8\).  Thus the honest
same-subsequence trichotomy is

\[
\boxed{
\begin{array}{c}
\text{lower chord off minimum with a paid horizontal return},\\
\text{or a fixed-gain pure-time response-switch packet},\\
\text{or a full minimum-fibre square.}
\end{array}}                                           \tag{3.8}
\]

This proves only the packet in the middle arm.  It does **not** prove that its
first-disagreement row returns to a minimum point, preserves prior zeros, or
regenerates the response rectangle.

For comparison, under the common-witness hypothesis the earlier checked
estimate preceding
`quittingTerminalSemanticDebt_stoppingLawMixture_eq_of_commonWitness` in
`Research/Quitting/StoppingLawMixtureWitnessStrata.lean` gives (3.5) directly.
Without common witnesses, (3.5) is false in general.  The exact checked
two-player regression `StoppingLawMixtureKink` in the same file has a date-zero
cap witness at one endpoint, a date-one witness at the other, and envelope

\[
 \max\{1-\theta,\theta\}.                              \tag{3.9}
\]

This lower-corner compactification and its witness-switch alternative are not
currently stored in `FinFourMinimumResponseRectanglePacket`.  Adding them
would be honest strengthening.  It would not yet consume either arm.

## 4. Why the exact local potential does not renew

The regenerated endpoint and chord sources retain the hard residual, their
exact minimum joint-law point, and a positive terminal coordinate.  They do
not retain an identification of the *next* forced-pair chart with (1.1).

There are two distinct losses.

### 4.1 Chronology/mark loss

`FinFourMinimumAtomProducer.regeneratedAtLawPoint` and
`FinFourThreeRoleMinimumTargetRegeneration` causalize the new law by an
existence theorem.  As their module comments state, the new chronology is not
asserted to contain the displayed incoming edge.  Even when one strengthens
causalization to use the displayed endpoint profiles, the ordinary
owner-compression theorem chooses

\[
 t=\text{anchor}+\text{offset}                         \tag{4.1}
\]

from the anchored singleton tail mass.  The selected offset may change at the
next source.  This is visible in
`FinFourMinimumAtomChronology.nonempty_ownerCompressedSingleton` and the
`stage` field of `FinFourOwnerCompressedSingletonEndpoint` in
`MinimumSingletonClockCompression.lean`.

### 4.2 Response-optimality loss

More importantly, literal profile/mark preservation would still be
insufficient.  After \(o\)'s response kills \(d_o\), a later update of player
\(p\ne o\) changes the opponents faced by \(o\).  The prescribed strategy
\(q^o\) remains literally present, but it need not remain a best response.
Indeed the response rectangle itself is a mechanism by which one player's
update raises another player's debt.

Consequently, a finite stored menu of responses transported through common
outer all-Continue prefixes does not supply a global potential.  The prefix
transport is exact, but the new *inner* endpoint modification can reactivate
an old zero and change which response witnesses the cap.

The scalar in (2.4) is indexed by the pair \((o,q^o)\).  At a successor it may
be replaced by \((o',q^{o'})\).  The expressions cannot telescope unless the
incoming and outgoing charts are identified.  This is the observer-rotation
obstruction also recorded in
`CODEX_HILBERT__SOURCE_FAITHFUL_OBSERVER_RETURN_SEAM.md`.

## 5. A precise finite-rank theorem, and the missing renewable field

The persistent-zero consumer is a finite theorem independent of any
compactness issue.

**Persistent-zero rank theorem.**  Let \(I\) be finite with \(|I|=N\).  Suppose
there are semantic pairs

\[
z_0,z_1,\ldots,z_N
\]

and players \(o_0,\ldots,o_{N-1}\) such that, for some \(D_*>0\),

\[
D(z_k)=D_*\qquad(0\le k\le N),                        \tag{5.1}
\]

\[
d_{o_k}(z_k)>0\qquad(0\le k<N),                       \tag{5.2}
\]

and

\[
d_{o_r}(z_{k+1})=0
   \qquad(0\le r\le k<N).                             \tag{5.3}
\]

Then these data are impossible.

Indeed, if \(r<k\) and \(o_r=o_k\), (5.3) at step \(k-1\) gives
\(d_{o_k}(z_k)=0\), contradicting (5.2).  Hence the \(N\) players \(o_k\) are
pairwise distinct and exhaust \(I\).  Equation (5.3) at the final step makes
every coordinate debt zero at \(z_N\), so \(D(z_N)=0\), contradicting (5.1).

For Fin4, therefore, no four-step regenerated minimum chain can successively
kill an active coordinate while preserving all earlier zeros.  The natural
rank is

\[
N-\bigl|\{\text{coordinates certified permanently zero}\}\bigr|. \tag{5.4}
\]

This theorem needs only zero preservation, not preservation of a particular
best-response strategy.  Literal preservation of every installed response is
a stronger source-level field which would imply (5.3) when the prescribed
coordinates are also retained.  The current regeneration API proves neither.

An adjacent-chart cocycle may be a weaker substitute, but no SCC consumer from
that hypothesis is proved here.  What *is* proved in Section 3 is that a
positive cap kink within one four-corner chart produces a source-matched
pure-time response-switch packet for one nonmoving coordinate.  Neither of its
two selected witnesses is automatically the rectangle's incoming observer
response \(q\).  Identifying one chart label with the next, and extending the
conclusion across regenerated sources, remain producer problems.

The best exact producer target is therefore:

\[
\begin{array}{c}
\text{source-faithful regenerated response endpoint}\\
\text{with incoming killed response }(o,q)
\end{array}
\Longrightarrow
\begin{cases}
d_o(\text{next endpoint})=0,\\
\text{or a source-matched pure-time response-switch seam}\\
\text{measuring the reactivated }o\text{-debt.}
\end{cases}                                            \tag{5.5}
\]

The second arm should retain the incoming \(q\), the newly selected pure time
(including Never), the literal successor profile, and their first-disagreement
row.  Section 3 proves an analogous two-witness switch on the lower edge of one
stored four-corner square, but does **not** identify either witness with this
incoming \(q\).  Thus it does not prove (5.5), even before arbitrary source
regeneration.  Forgetting the chart labels reduces the output to the already
ubiquitous paid row and loses the possible SCC accounting.

## 6. Fully behavioral regressions against weaker implications

Two checked tables show that neither exact caps nor literal source fidelity
implies the persistent-zero condition (5.3).

### 6.1 Time-witness rotation

`Research/Quitting/FiniteResetCirculationRegression.lean` has four literal
profiles

\[
 A\to B\to C\to D\to A,                               \tag{6.1}
\]

using only deterministic dates zero and one.  The checked theorem
`exact_literal_fullBestResponse_cycle_preserves_totalDebt` states that every
edge is a legal one-player update, reaches the mover's full behavioral cap,
kills that mover's debt, recreates the same debt on the other player, and
preserves total debt.  The complete profile returns exactly.  Each own-strategy
open chord still has the exact local identity (2.2).  What rotates is the
best-response date and the killed player.

Prefixing every displayed profile by any common finite all-Continue word only
shifts the dates.  It preserves the terminal law, payoffs, caps, debt, and the
literal update cycle.  Hence arbitrary depth and exact outer source transport
do not repair the missing adjacent-chart field.

### 6.2 Same-stage Fin4 rotation with fixed atoms

`Research/Quitting/FourPlayerCyclicPlateauCandidate.lean` supplies a literal
Fin4 date-zero cycle.  The declarations `update_profile_phaseMover`,
`phaseMover_payoff_gain`, `nextPhase_mover_debt_eq_zero`,
`nextPhase_nextMover_debt_eq_one`, `phase_cap`,
`phase_stageZero_mass_eq_one`, and `phase_terminalOutcomeMass_eq_one` give:

* complete-profile unilateral updates;
* unit full-behavioral paid gains;
* exact mover-debt annihilation and next-mover reactivation;
* a common unrestricted cap vector; and
* literal finite terminal atoms of mass one.

This is a finite response-chart circulation even before compactification.
The checked fence `zeroProfile_isExactTerminalNash` and
`zeroPair_debtSum_eq_zero` shows that its global minimum is zero.  Likewise
`FiniteResetCirculationRegression.never_totalDebt_eq_one` fences its recurrent
debt-two cycle from the global minimum.

These are not counterexamples to a positive-minimum theorem.  The Fin4 table
has \(D_*=0\).  For the two-player reset table, the checked statement is only
that the circulating vertices have debt two while the literal Never profile
has debt one; no value of the global minimum below that upper bound is needed.
They are exact
counterexamples to the strengthened but false implication

\[
\begin{array}{c}
\text{actual profiles + exact behavioral caps + killed debt + fixed atoms}\\
+\ \text{literal recurrence or arbitrary common prefix depth}
\end{array}
\Longrightarrow\text{persistent zero preservation}.  \tag{6.2}
\]

Therefore any proof of (5.5) must use positive-minimum provenance in a
mathematically active way.  Neither regression realizes its cycle on a
positive global minimum fibre, so neither refutes a theorem whose hypotheses
derive coherence from that provenance.

## 7. Lean-facing boundary

The local identity needed for a public response-chord API is small:

```text
FinFourMinimumResponseChord.responseGain_eq_observerDebt
```

under the already available hypothesis that the response endpoint kills the
observer debt.  Its proof should use
`quittingTerminalSemanticDebt_stoppingLawMixture_eq_self`,
`quittingContinuationBestResponseValue_update_self`, and the existing payoff
scaling theorem.

The genuinely new source structure would store the lower response corner on
the same subsequence:

```text
FinFourSourceFaithfulMinimumResponseSquare
```

with limits for `sourceProfile`, `sourceResponseProfile`, `endpointProfile`,
and `endpointResponseProfile`, rather than only the upper two.  Its honest
dispatch is:

```text
lower response ascent / cap-witness switch / full minimum square
```

The capstone is not another chord constructor.  It is (5.5), with literal
adjacent response labels and a first-disagreement packet in the reactivation
arm.  A theorem returning only `d_o > 0` or an independently selected paid row
would merely rename the current SCC.

## 8. Files and declarations inspected

* `docs/FRONTIER.md`.
* `Research/Quitting/FinFourProducerAtlas/MinimumResponseChordActualDecoder.lean`:
  `FinFourMinimumResponseEndpointRiseOrigin`,
  `FinFourMinimumResponseRectangleSequence`,
  `nonempty_minimumResponseEndpointRiseOrigin`.
* `Research/Quitting/FinFourProducerAtlas/MinimumResponseChordRegeneration.lean`:
  `FinFourMinimumResponseRectanglePacket`, `responseChoice_ge_mark`,
  `routedStageMass_floor`, `endpointChord_eq_update_sourceChord`,
  `responseGain_eq_scale`, `responseCross_eq_scale`,
  `FinFourMinimumResponseChord.debt_eq_affine`, and regenerated sources.
* `Research/Quitting/MinimumResponseChordLaw.lean`: executable response chords,
  law/payoff affinity, debt convexity, support union.
* `Research/Quitting/StoppingLawMixtureWitnessStrata.lean`: common-witness
  affinity, the quantitative chord-gap certificate, and
  `StoppingLawMixtureKink`.
* `Research/Quitting/StoppingLawMixtureFiniteWitnessPassport.lean`:
  `exists_quittingPureTime_terminalPayoff_ge_bestResponse_sub`.
* `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPaidFirstDisagreement.lean`:
  `exists_quittingPaidFirstDisagreementRow_of_pureTimePayoff_sub`.
* `Research/Quitting/FinFourProducerAtlas/ThreeRoleRegeneration.lean` and
  `MinimumSingletonClockCompression.lean`: exact regeneration and the
  chronology/mark boundary.
* `Research/Quitting/FiniteResetCirculationRegression.lean` and
  `FourPlayerCyclicPlateauCandidate.lean`: checked all-behavior regressions.

## 9. Concrete next check

Add the four-corner compactification to the exact common response subsequence
and formalize the quantitative trichotomy of Section 3:

* either some fixed proper lower chord is above \(D_*\) and its paid horizontal
  sibling returns to the upper minimum chord;
* or the accumulated cap chord gap yields a same-source pair of pure-time
  witnesses with a fixed first-disagreement gain;
* or all four corners form a minimum square.

The remaining mathematical test is then whether positive-minimum source
causalization proves persistent-zero preservation, or the successive-chart
version of (5.5), on the full-minimum-square arm.  The regressions show exactly
where such a proof must use the positive minimum rather than only local
response geometry.
