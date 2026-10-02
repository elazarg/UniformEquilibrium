# Source-faithful response menus do not by themselves close observer rotation

Author: `CODEX_HILBERT`

## Status

Ordinary mathematics, not checked in Lean. This note records one exact
positive transport lemma and one correction/no-go.

* A response shifted through a positive-survival exact cap--Nash prefix keeps
  its **cap regret** with the exact opponent-survival factor. Thus the
  source-faithful causalization of
  `CODEX_AMPERE__SOURCE_FAITHFUL_CAUSALIZATION_AND_RESPONSE_SEAM.md` really
  can retain a finite near-cap response menu, not merely its pairwise payoff
  contrasts.
* Merely remembering a response until the same observer occurs again does
  **not** decode observer rotation into a new chronological consumer. The
  resulting same-source seam is dominated by the paid first-disagreement row
  already available from the later response alone. The historical label
  carries no signed comparison between the two literal sources.

Consequently this note proves neither observer balance nor any of the desired
positive-minimum outputs: renewable zero-preserving support elimination, an
adjacent-chart seam surviving the paid-cap lift, or an induced-owner HOPF
chamber. The cyclic-plateau table remains an exact zero-minimum regression
for the stronger historical-menu interface. This note is internal and is
not an export proposal.

## 1. Exact question

Suppose the minimum-response construction is regenerated using the literal
endpoint realizers, so every old complete response plan is still available as
a counterfactual at every later source. If the observer labels rotate and
eventually return, does the historical response produce more than the generic
paid row already present at every actual source in a counterexample?

The distinction is:

1. **menu retention:** an old plan is still a legal plan and its payoff can be
   evaluated at the later literal source;
2. **chart retention:** the same plan has a signed response-gain increment
   across two specified literal sources; and
3. **chronological retention:** that signed two-source comparison remains
   attached to the exact entrance and successor used by the paid-cap lift.

The supplied-realizer construction proves the first item and transports all
pairwise contrasts through its new exact prefixes. It does not, through
intervening horizontal endpoint replacements, prove the second or third.

## 2. Positive-survival cap prefixes preserve cap regret exactly

Fix a tail profile \(\sigma\), a player \(i\), and one complete behavioral
response \(a\) of \(i\). Write

\[
 B=B_i(\sigma),\qquad
 V=U_i(\sigma[i\leftarrow a]),\qquad
 R=B-V\ge0.                                             \tag{2.1}
\]

Let \(q\) be an exact root Nash point against the tail cap vector and assume
its joint Continue mass is positive. Put

\[
 m_i(q)=\Pr_q(\text{all opponents of }i\text{ Continue})>0.             \tag{2.2}
\]

Let `shift_q(a)` prescribe Continue at the new root and then use \(a\) in the
suffix. The exact endpoint formulas are

\[
 V_i(\operatorname{shift}_q a;q*\sigma)=A_i(q)+m_i(q)V                 \tag{2.3}
\]

and

\[
 B_i(q*\sigma)=\max\{Q_i(q),A_i(q)+m_i(q)B\}.                          \tag{2.4}
\]

Positive joint Continue mass implies that player \(i\) assigns positive
probability to Continue. Exact root Nash optimality therefore gives

\[
 Q_i(q)\le A_i(q)+m_i(q)B.                                             \tag{2.5}
\]

Combining (2.3)--(2.5),

\[
 \boxed{
 B_i(q*\sigma)-
 V_i(\operatorname{shift}_q a;q*\sigma)
 =m_i(q)R.}
                                                                        \tag{2.6}
\]

For a finite exact cap--Nash word \(W\) with positive joint survival at
every stage, iteration gives

\[
 \boxed{
 \operatorname{Regret}_i(\operatorname{shift}_W a;W*\sigma)
 =m_i(W)\operatorname{Regret}_i(a;\sigma),}
                                                                        \tag{2.7}
\]

where \(m_i(W)\) is the product of the opponent-survival factors. Pairwise
response payoff differences scale by the same factor.

For the positive-minimum causal stacks, the checked positivity theorem for
the stack Continue product makes (2.7) applicable rankwise. In the
near-minimum supplied-realizer construction, joint survival tends to one, so
every opponent-survival product also tends to one. Thus a finite near-cap
menu survives causalization asymptotically without loss.

This is strictly a **vertical prefix** fact. A later horizontal replacement
of another player changes an opponent strategy for \(i\) and can change both
the value and cap regret of the old plan by order one.

## 3. The historical-return calculation collapses to the generic paid row

Fix one later actual profile \(P\) and one player \(i\). For pure times,
including literal `Never`, put

\[
 W(q)=U_i(P[i\leftarrow Q_q]),
 \qquad q\in\mathbb N\cup\{\infty\}.                                  \tag{3.1}
\]

Let \(q_{\rm old}\) be any historical pure-time label and let
\(q_{\rm new}\) be a current paid response satisfying

\[
 W(q_{\rm new})-U_i(P)\ge g>0.                                        \tag{3.2}
\]

There is a valid historical-label dichotomy:

\[
 \boxed{
 W(q_{\rm new})-W(q_{\rm old})\ge g/2
 \quad\text{or}\quad
 W(q_{\rm old})-U_i(P)\ge g/2.}                                      \tag{3.3}
\]

It is just the identity obtained by inserting \(W(q_{\rm old})\) into
(3.2). The first arm is a same-source switch involving the old label; the
second says that the old response itself is still paid at the later source.

But (3.3) gives no new quantitative first-disagreement theorem. If \(\mu\)
is the stopping law of the prescribed strategy \(P_i\), then

\[
 U_i(P)=\mathbb E_{q\sim\mu}W(q).                                     \tag{3.4}
\]

The bounded-support averaging lemma directly selects
\(q_-\in\operatorname{supp}\mu\) with

\[
 W(q_-)\le \mathbb E_\mu W.
\]

Therefore (3.2) alone already gives the stronger same-source seam

\[
 \boxed{W(q_{\rm new})-W(q_-)\ge g.}                                  \tag{3.5}
\]

Equation (3.5), with no recurrence assumption, feeds
`exists_quittingPaidFirstDisagreementRow_of_pureTimePayoff_sub`. In (3.3),
the only extra datum is the name `q_old`. Forgetting the name yields an
object no stronger than the ubiquitous paid row. Retaining the name still
does not give a sign for the cross-source quantity

\[
 \bigl[W_{P_{\rm new}}(q_{\rm old})-U_i(P_{\rm new})\bigr]
 -
 \bigl[W_{P_{\rm old}}(q_{\rm old})-U_i(P_{\rm old})\bigr].            \tag{3.6}
\]

That signed increment, not legal availability of \(q_{\rm old}\), is what a
common response chart requires.

## 4. Why source-faithful menus do not balance observer flow

For an edge-local response chart, write

\[
 G_{i,q}(P)=U_i(P[i\leftarrow Q_q])-U_i(P).                            \tag{4.1}
\]

Ampere's supplied-realizer construction retains every historical \(q\) and
Section 2 transports it through the newly added exact prefix. An intervening
horizontal endpoint operation can nevertheless change
\(G_{i,q}\) with either sign. Hence a later occurrence of observer \(i\)
does not imply

\[
 G_{i,q_{\rm old}}(P_{\rm later})
 -G_{i,q_{\rm old}}(P_{\rm earlier})>0,                               \tag{4.2}
\]

nor does it imply the adjacent-source version of (4.2) on any edge between
the two occurrences.

Finite pigeonhole only returns an observer label. It does not turn a
rotating edge circulation into the observer-by-observer balance condition
used in Maxwell's holonomy lemma. In particular, if

\[
 b(v,i)=
 \sum_{t(e)=v,o_e=i}\lambda_e-
 \sum_{s(e)=v,o_e=i}\lambda_e                                      \tag{4.3}
\]

is nonzero, carrying all response menus leaves \(b\) unchanged. The scalar
terms which fail to telescope are still comparisons of different players'
payoffs. No unilateral strategy switch implements such an interpersonal
difference.

A genuinely stronger packet would have to retain at least one of:

1. an observer-balanced circulation, so the finite coupling argument pairs
   incoming and outgoing charts of the same player;
2. a signed adjacent-source inequality of the form (4.2), with both literal
   sources and response labels attached to the paid-cap entrance;
3. a zero-preserving support transition which converts an observer's later
   re-entry into a strict finite-rank loss; or
4. the separate induced-Nash-law sign needed by the owner HOPF chamber.

Literal menu retention alone supplies none of these four signs.

### 4.1 The exact adjacent chart at a first debt re-entry

There is one useful vector calculation, but it reproduces the reviewed
minimum-response rectangle rather than consuming it. For any complete
response \(a\), set

\[
 G_{i,a}(P)=U_i(P[i\leftarrow a])-U_i(P).
\]

Since the behavioral cap dominates every response,

\[
 G_{i,a}(P)\le d_i(P).                                      \tag{4.4}
\]

If \(a\) is an \(\varepsilon\)-best response at \(Y\), then

\[
 G_{i,a}(Y)\ge d_i(Y)-\varepsilon.                         \tag{4.5}
\]

Hence two literal sources satisfy the exact chart inequality

\[
 \boxed{
 G_{i,a}(Y)-G_{i,a}(X)
 \ge d_i(Y)-d_i(X)-\varepsilon.}                           \tag{4.6}
\]

In particular, at a first re-entry of a previously killed coordinate,

\[
 d_i(X)=0,qquad d_i(Y)\ge\delta>0,
\]

the target near-cap response supplies an adjacent same-observer chart rise
at least \(\delta-\varepsilon\). If its full response endpoint is
\(Z=Y[i\leftarrow a]\), then own-cap invariance gives

\[
 d_i(Z)=B_i(Y)-U_i(Y[i\leftarrow a])\le\varepsilon.       \tag{4.7}
\]

Thus an exact response gives the source-faithful excursion

\[
 d_i(X)=0\longrightarrow d_i(Y)>0\longrightarrow d_i(Z)=0.             \tag{4.8}
\]

When \(X,Y,Z\) all lie on the minimum fibre and the endpoint law is retained,
(4.6)--(4.8) are precisely the extra adjacent-chart provenance stored by the
minimum-response rectangle and its source-faithful regeneration. Section 2
shows that this decoration survives the new cap prefix. Passing (4.8) to the
paid-cap lift therefore is legitimate.

It still reaches the known residual: the response which restores coordinate
\(i\) to zero can create debt in a different inactive coordinate. Repeating
the construction merely moves the first-re-entry label. Thus nonzero
observer rotation can be localized into source-faithful zero--positive--zero
excursions, but no current consumer turns those excursions into a renewable
decrease. This is exact overlap with the reviewed producer, not a new atlas
exit.

## 5. The maximal-support handoff remains one-time

At a minimum response edge \(X\to Y\) killing observer \(i\), the checked
minimum-fibre chord has interior positive-debt support

\[
 \operatorname{supp}^+d(X)\cup\operatorname{supp}^+d(Y).              \tag{5.1}
\]

Choosing an inclusion- or cardinality-maximal support on the minimum fibre
therefore excludes support entry on that one attached full replacement and
gives strict support loss. This is the valid canonical handoff.

It is not renewable at the current interface. The next canonical pure-pair
ray starts from its tail-independent sure-pair semantic point, not from the
regenerated endpoint \(Y\). Its source support is not constrained to lie in
\(\operatorname{supp}^+d(Y)\). Source-faithful causalization preserves the
endpoint as the suffix chronology, but it does not identify the next whole
ray source with that suffix point. Thus the next entrance can restore a
previously killed coordinate.

This is exactly the source-typing obstruction recorded in
`CODEX_RIEMANN__MINIMUM_REGENERATION_ORIENTATION_AUDIT.md`, Section 11; the
historical-menu lemma does not repair it.

## 6. Positive-minimum-compatible vector obstruction

There is a finite synthetic minimum-fibre model showing that positivity of
the minimum, coordinatewise cap convexity, own-cap invariance, exact debt
affinity, and support-union geometry still do not force observer balance.
It is not asserted to be the complete semantic carrier of a quitting table.

Use two active labels \(0,1\) (and add two inert coordinates to obtain four
labels). Let four formal source vertices be \(A,B,C,D\), with observer word

\[
 1,0,1,0                                                     \tag{6.1}
\]

on the edges \(A\to B\to C\to D\to A\). Put

\[
 d(A)=d(C)=e_1,
 \qquad
 d(B)=d(D)=e_0,                                           \tag{6.2}
\]

and, in every coordinate,

\[
 B_i(v)=1,
 \qquad
 U_i(v)=1-d_i(v).                                        \tag{6.3}
\]

Thus every vertex has

\[
 D(v)=1>0.                                                \tag{6.4}
\]

On an edge whose observer is \(i\), the unilateral full replacement raises
\(U_i\) from \(0\) to \(1\), leaves \(B_i=1\), and hence kills exactly one
unit of its own debt. Simultaneously the other active coordinate's payoff
drops from \(1\) to \(0\), its cap stays \(1\), and the unit debt enters
there. The total debt remains one.

Fill every edge by affine interpolation:

\[
 d((1-\theta)v+\theta w)
  =(1-\theta)d(v)+\theta d(w),
 \qquad
 U=\mathbf 1-d,
 \qquad B=\mathbf 1.                                    \tag{6.5}
\]

Then all of the following hold exactly:

* the compact edge complex has positive constant minimum \(D_*=1\);
* every prescribed-payoff coordinate is affine on each executable
  one-coordinate chord;
* every cap coordinate is constant, hence convex and cyclically monotone;
* the moved observer's cap is invariant;
* every debt coordinate is affine on each minimum chord;
* every proper chord has support equal to the union of its endpoint supports;
* every edge is a unit paid response which annihilates its observer debt; and
* the observer flow is maximally unbalanced at every vertex.

The maximal-support points are the proper chord interiors, with support
\(\{0,1\}\). They have no supplied outgoing response operation. The decorated
vertices have outgoing operations but support only one coordinate. This is
the abstract form of the source-typing failure behind the one-time maximal
support handoff.

This model proves a precise logical limitation: no argument using only the
listed vector identities, convexity/cyclic monotonicity, and the scalar fact
\(D_*>0\) can establish observer balance or renewable support descent. A
successful positive-minimum proof must use a property of the **complete
quitting semantic carrier** or one of the hard-residual/source-law fields not
encoded above.

The model is deliberately not presented as a quitting-game counterexample.
In the ordinary matching-pennies realization of the same four pure reset
vertices, the missing jointly mixed profiles lower the global debt. Declaring
the edge complex to be the whole carrier would therefore be illegitimate.
The point is exactly that edgewise minimum geometry alone cannot see this
global completion.

## 7. Exact zero-minimum quitting regression

The checked cyclic-plateau table in
`Research/Quitting/FourPlayerCyclicPlateauCandidate.lean` has the literal
cycle

\[
 \{2\}\to\{0,2\}\to\{0,1,2\}\to\{1,2\}\to\{2\},                    \tag{7.1}
\]

with paid mover gain one on every edge. Its observer word alternates
\(1,0,1,0\). The complete pure-time menu at every phase reduces to the two
relevant actions `QuitAt 0` and `Never`. When observer \(1\) returns, the
preferred orientation of this pair has reversed; the same is true for
observer \(0\).

Therefore the table has all of the local features used by the proposed
historical-return argument:

* literal source profiles forming a closed cycle;
* exact behavioral caps and paid endpoint updates;
* complete response menus available at every source;
* repeated observers; and
* large same-source response switches when an observer returns.

Yet no fixed observer/ordered-response chart or observer-balanced edge
circulation follows. The returned switch is exactly another generic paid
row and does not orient the cycle. The table's all-Continue profile is an
exact terminal Nash profile, so its global minimum debt is zero.

This is not a counterexample to a theorem that uses \(D_*>0\) through an
additional global inequality. It is a precise regression showing that
source sequences, complete menus, recurrence, and local paid gains alone do
not supply that inequality.

## 8. HOPF does not follow from response rotation

For a candidate owner \(h\) with the other three players free, the remaining
HOPF sign is

\[
 Q_h(\pi)-C_h(\pi)
 =\sum_{T\subseteq I\setminus\{h\}}
   \mu_\pi(T)\bigl(r_h(T\cup\{h\})-r_h(T)\bigr)\ge0                  \tag{8.1}
\]

at one induced Nash law \(\mu_\pi\), together with the appropriate solo
sign. Historical response recurrence controls neither the induced Nash law
nor the other summands in (8.1). The forced-pair and positive response-square
regression in
`CODEX_RIEMANN__FORCED_PAIR_TO_INDUCED_OWNER_HOPF_ADAPTER.md` shows this
independence exactly at global minimum zero. Positive-minimum provenance
would have to provide a new law-incidence inequality; menu retention does not.

## 9. Verdict and next exact target

The attempted conclusion

\[
 \text{observer returns}
 \Longrightarrow
 \text{new source-faithful paid-cap seam consumer}
\]

is unsupported. The valid conclusion is only

\[
 \boxed{
 \text{observer returns}
 \Longrightarrow
 \text{historically labelled generic paid row,}}
                                                                        \tag{9.1}
\]

and the word "historically" has no current consumer.

The exact remaining positive-minimum theorem is therefore still Maxwell's
question, strengthened by the source-faithful data:

> Given a literal returned minimum-response chain carrying the complete
> historical response menu, prove either observer-by-observer balance, a
> signed adjacent-source same-observer chart increment which survives the
> paid-cap lift, renewable zero-preserving support elimination, or the exact
> induced-owner HOPF sign.

A result which ends only in `QuittingPaidFirstDisagreementRow` or
`QuittingPaidCapLiftedSource` without one of these extra fields has not moved
the frontier.

## 10. Lean-facing boundary

The only standalone positive lemma here which may merit formalization is

```text
shiftedResponseRegret_capNashRootStack_eq_opponentSurvival_mul
```

It strengthens pairwise contrast transport to cap-regret transport along a
positive-survival exact cap stack. It should be treated as an adapter, not a
consumer.

The historical dichotomy (3.3) is elementary but should not be promoted as
progress: (3.5) already follows from the current response without historical
data.

## 11. Source audit

The bounded sources inspected were:

* `notes/CODEX_MAXWELL__RESPONSE_CHART_HOLONOMY_AND_OBSERVER_SWITCH_NOGO.md`;
* `notes/CODEX_AMPERE__SOURCE_FAITHFUL_CAUSALIZATION_AND_RESPONSE_SEAM.md`;
* `exports/SOURCE_FAITHFUL_MINIMUM_ENDPOINT_CAUSALIZATION_AND_RESPONSE_MENU_TRANSPORT.md`;
* `notes/CODEX_RIEMANN__MINIMUM_REGENERATION_ORIENTATION_AUDIT.md`;
* `notes/CODEX_RIEMANN__FORCED_PAIR_TO_INDUCED_OWNER_HOPF_ADAPTER.md`;
* `exports/FIN4_MINIMUM_RESPONSE_CHORD_ATOM_AND_SOURCE_REGENERATION.md`;
* `Research/Quitting/FinFourProducerAtlas/MinimumResponseChordRegeneration.lean`;
* `Research/Quitting/FourPlayerCyclicPlateauCandidate.lean`;
* `MathUE/ProbabilityMassFunction/BoundedSupportAverage.lean`;
* `UniformEquilibrium/Quitting/Paths/BehaviorStoppingPayoff.lean`;
* `UniformEquilibrium/Quitting/Root/SuccessorCertificate.lean`;
* `UniformEquilibrium/Diagnostics/Quitting/TerminalCapNashChronology.lean`;
* `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/TerminalSemanticStoppingLawDebtConvexity.lean`;
* `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPaidFirstDisagreement.lean`;
* `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/PaidCapLiftedSummablePort.lean`; and
* `Research/Quitting/ConcentratedCollisionThreeRoleEndpointLaw.lean`.

The checked declarations used as interfaces are:

* `quittingTerminalDebtSum_capNashRootStack_eq` and
  `capNashRootStack_continueMass_pos_of_debtSumInf_pos`;
* `quittingTerminalSemanticPrefix_envelope_eq_rootSuccessorPayoff_of_capNash`;
* `quittingTerminalPayoff_update_eq_expect_stoppingLaw_pureTime`;
* `exists_mem_support_le_expect`;
* `exists_quittingPaidFirstDisagreementRow_of_pureTimePayoff_sub`; and
* the exact phase-profile declarations in
  `FourPlayerCyclicPlateauCandidate.lean`.

Equation (2.7) is new ordinary mathematics and is not claimed checked. The
remaining sections are exact overlap and interface-no-go analysis, not a new
producer.
