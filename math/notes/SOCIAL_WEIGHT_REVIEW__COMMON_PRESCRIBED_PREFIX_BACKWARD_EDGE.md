# Common prescribed prefixes give a literal backward response edge

**Identity:** SOCIAL_WEIGHT_REVIEW  
**Status:** ordinary mathematics; two independent audits PASS after the bounded repairs incorporated below; not Lean-checked

## Question

Suppose two supplied profile families \(H_n,Y_n\) converge to positive-debt
global-minimum semantic/law points \(h,y\), differ only in one player's
suffix strategy, and have a fixed positive suffix payoff gain.  Source-faithful
causalization of \(H_n\) selects a finite exact cap--Nash word \(W_n\) whose
joint survival tends to one.

Can the same **prescribed** word be copied onto \(Y_n\) so that

\[
 A_n:=W_n\star H_n \longrightarrow
 P_n:=W_n\star Y_n
\]

is a literal one-player response edge between actual profiles, while
\(A_n\to h\) and \(P_n\to y\) in the complete semantic/law packet?

This is distinct from the invalid shifted-response construction.  A shifted
response forces the responder to Continue through \(W_n\), and therefore
does not start at the prescribed profile \(A_n\).  Here both endpoints retain
the responder's prescribed actions in \(W_n\) and differ only after the word.

## Result

Yes, provided the limiting tail caps strictly dominate singleton cash-out in
every coordinate.  Positive global minimum debt supplies precisely that
moat.  The key elementary statement is complete-cap stability under an
arbitrary common prefix whose player-deleted survival tends to one.

Applied to the moving pair chord of
`PAIRED_HULL_REVIEW__ORIENTED_PAIR_TO_SINGLETON_OR_RENEWABLE_CHORD.md`, this
gives the prefixed backward edge left open in Section 17, when returned in
the explicit paired-edge wrapper of Section 4.  It does
not consume the positive-residual or off-minimum outputs.

## 1. Vanishing-prefix complete-cap lemma

Let \(I\) be finite and suppose all terminal rewards lie in \([-M,M]\).
For each \(n\), let

* \(T_n\) be an arbitrary behavioral tail;
* \(W_n\) be a nonempty finite product-root word;
* \(P_n=W_n\star T_n\);
* \(c_n\) be the joint all-Continue probability through \(W_n\); and
* \(h_{i,n}\) be the probability that every opponent of player \(i\)
  Continues through \(W_n\).

Assume

\[
 c_n\to1,\qquad
 (U(T_n),B(T_n),\mu(T_n))\to(U,b,\mu),
\]

and, writing \(s_i=r_i(\{i\})\), assume

\[
 b_i>s_i\qquad(i\in I).
\tag{1.1}
\]

Then

\[
 (U(P_n),B(P_n),\mu(P_n))\to(U,b,\mu).
\tag{1.2}
\]

Moreover, for every player \(i\), the one-player-deleted law of \(P_n\) is
within total variation \(1-h_{i,n}\) of the corresponding deleted tail law.
Thus any deleted-law coordinates included in the supplied tail convergence
have the same limits after prefixing.

### Proof

Joint survival is at most every player-deleted survival, hence

\[
 c_n\le h_{i,n}\le1.
\]

Thus \(h_{i,n}\to1\) for every \(i\).

Couple the prefixed prescribed play with the tail play after the word.  They
disagree only if the word absorbs, an event of probability \(1-c_n\).
Therefore prescribed payoffs and ordinary terminal laws converge to their
tail counterparts.  After deleting any fixed player \(i\), the analogous
coupling error is at most \(1-h_{i,n}\), so every deleted law converges too.

It remains to control the unrestricted cap.  Behavioral pure-time
extremality lets us consider deterministic Quit dates and Never.

Fix player \(i\).  A pure response which Quits inside \(W_n\) receives the
singleton payoff \(s_i\) whenever every opponent survives the whole word.
Only the complementary event, of probability \(1-h_{i,n}\), can alter that
payoff.  Hence its value lies within

\[
 2M(1-h_{i,n})
\]

of \(s_i\).

A pure response which Continues through the word and then uses a tail pure
time can be coupled with that tail response.  Again the two outcomes differ
only if some opponent absorbs inside the word, so their values differ by at
most \(2M(1-h_{i,n})\).  Taking suprema gives

\[
 \left|
 B_i(P_n)-\max\{s_i,B_i(T_n)\}
 \right|
 \le 2M(1-h_{i,n}).
\tag{1.3}
\]

For the lower bound in (1.3), use either immediate Quit or an
\(\varepsilon\)-optimal tail pure time shifted behind the word, then let
\(\varepsilon\downarrow0\).  For the upper bound, split every pure time into
the two cases just considered and use pure-time extremality.

By (1.1), eventually

\[
 \max\{s_i,B_i(T_n)\}=B_i(T_n).
\]

Consequently \(B_i(P_n)\to b_i\) for every \(i\), proving (1.2).

The estimate (1.3) does not require \(W_n\) to be Nash.  Only survival is
used.  Nonemptiness is necessary for this standalone formula: if \(W_n\)
is empty and \(B_i(T_n)<s_i\), the left side of (1.3) need not vanish while
its right side is zero.  In the application, source-faithful causalization
gives \(|W_n|=n+1\), so the condition holds at every rank.

## 2. Positive minimum supplies the singleton moat

At a global minimum terminal-semantic pair with minimum debt \(D_*>0\), the
checked singleton-margin theorem gives

\[
 B_i-r_i(\{i\})\ge D_*>0
 \qquad(i\in I).
\tag{2.1}
\]

Therefore every positive global-minimum limit satisfies hypothesis (1.1),
uniformly with moat \(D_*\).

This is the only global-minimum input in the cap-stability argument.  Without
strict singleton separation the conclusion is false in this form: an
arbitrarily small prefix can make an early singleton response tie or replace
the tail cap maximizer.

## 3. Literal common-prefix response transport

Assume now that \(H_n\) and \(Y_n\) differ only in player \(q\)'s suffix
strategy, with

\[
 U_q(Y_n)-U_q(H_n)=g_n.
\]

Let \(W_n\) be the exact cap--Nash words chosen by source-faithful
causalization of \(H_n\), and put

\[
 A_n=W_n\star H_n,\qquad P_n=W_n\star Y_n.
\tag{3.1}
\]

The endpoints in (3.1) have literally identical prescribed prefix actions
for every player, including \(q\).  They differ only in \(q\)'s suffix
strategy.  Thus (3.1) is an actual one-player complete-strategy replacement
from the prescribed prefixed source \(A_n\).

The common-word payoff identity gives exactly

\[
 U_q(P_n)-U_q(A_n)=c_n g_n.
\tag{3.2}
\]

Since the opponents are identical at the two endpoints,

\[
 B_q(P_n)=B_q(A_n).
\tag{3.3}
\]

If the suffix mover debt satisfies

\[
 d_q(Y_n)=d_q(H_n)-g_n,
\]

then exact cap--Nash debt scaling at the source and (3.2)--(3.3) give

\[
 d_q(P_n)=c_n d_q(Y_n).
\tag{3.4}
\]

In particular an asymptotically debt-killing suffix response remains
asymptotically debt-killing after the copied prescribed prefix.

By source-faithful causalization, \(c_n\to1\).  Applying Section 1 first to
\((W_n,H_n)\) and then to \((W_n,Y_n)\) yields

\[
 \operatorname{SemLaw}(A_n)\to h,\qquad
 \operatorname{SemLaw}(P_n)\to y.
\tag{3.5}
\]

Any jointly compactified player-deleted laws have the same tail limits by
the quantitative coupling in Section 1.  Thus the prefixed literal edge has
the intended source and target limits.

## 4. Marked atom and child regeneration

Suppose the suffix family \(Y_n\) has a marked coalition \(K'\) at date
\(t_n\) with mass at least \(\lambda>0\).  At the shifted date
\(|W_n|+t_n\), the copied-prefix target has exact mass

\[
 c_n\,\Pr_{Y_n}(K'\text{ at }t_n).
\tag{4.1}
\]

Hence it is at least \(\lambda/2\) eventually.  After discarding finitely
many indices, source-faithful minimum causalization may be applied directly
to the supplied target family \(P_n\) and these shifted literal marks.  This
regenerates the minimum child at \(y\).

The standard `FinFourMinimumAtomProducer` does **not** itself contain an
incoming-edge field.  Exact ancestry is therefore represented by a thin
paired-edge wrapper, not attributed to the child producer alone.  The wrapper
stores:

1. the source causalization of \(H_n\), including its words \(W_n\);
2. the target causalization of \(P_n\) at the shifted marks;
3. the actual families \(A_n=W_n\star H_n\) and
   \(P_n=W_n\star Y_n\);
4. a player-\(q\) strategy family \(\tau_n\) with the literal equality

   \[
   P_n=\operatorname{update}(A_n,q,\tau_n);
   \tag{4.2}
   \]

5. the exact payoff, cap, debt, and marked-mass identities
   (3.2)--(3.4) and (4.1); and
6. the complete limits (3.5).

Every field is constructed from the two supplied suffix families and the
same selected word; no additional game-theoretic hypothesis, realizer, mark,
or source is chosen.  A downstream consumer can inspect the incoming edge
through this wrapper, while the ordinary child producer continues to expose
only its own causal chronology.

For the Section 17 moving pair chord, take \(H_n=H_n^s\).  On its
minimum-fibre arm,

\[
 g_n=(1-s)L_n\Delta,\qquad
 d_q(Y_n)=R_n\to0,\qquad
 L_n\ge\lambda.
\]

Equations (3.2)--(4.2) therefore retain a uniform paid gain, asymptotically
kill \(q\)'s debt, preserve the marked \(K'\)-atom, and converge to the
strict-support child \(y\).  The paired-edge wrapper is precisely the
backward compiler that the shifted-response construction failed to type.

## 5. What is and is not claimed

The proof establishes a literal **behavioral response edge**, not a
Nash--Bellman temporal row.  It does not make the copied word exact cap--Nash
against \(Y_n\), and does not need that property.  The word is exact only at
the source tail \(H_n\).

It also does not consume:

* the positive residual branch;
* the quantitative off-minimum branch; or
* any later nonrecursive tangent-trace exit.

Its role is narrower: together with the paired-edge wrapper, it removes the
prefixed source/target typing gap in the minimum-fibre support descent.

## 6. Source and novelty audit

Named declarations inspected:

* `quittingTerminalPayoff_literalRootStack_sub_eq_continueProduct_mul` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalCapNashChronology.lean`;
* `quittingTerminalPayoff_shiftedBehavioralResponse_sub_eq` and
  `tendsto_quittingLiteralRootStackOpponentSurvival_one` in
  `Research/Quitting/SourceFaithfulMinimumLawCausalization.lean`;
* `QuittingSourceFaithfulMinimumCausalization.continueProduct_tendsto_one`,
  `.opponentSurvival_tendsto_one`, and
  `nonempty_sourceFaithfulMinimumCausalization` in the same file; and
* behavioral pure-time extremality in
  `UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean`;
* the exact all-Continue special case
  `quittingRootSequenceTerminalSemanticPairAt_silentPrefix_zero` in
  `UniformEquilibrium/Diagnostics/Quitting/SilentPrefixTerminalSemantics.lean`.

The exact common-word prescribed-payoff identity, survival limits, and
zero-absorption special case are checked already.  I did not find a named
declaration for the almost-silent cap estimate (1.3), nor for the resulting
common-prescribed-prefix backward edge.  Those are the new
ordinary-mathematics adapters proposed here.

The construction does not contradict the correction to the shifted-response
claim.  It uses a different response: retain the prescribed prefix action and
change only the suffix strategy.

## 7. Review disposition and Lean handoff

Two independent audits tried to falsify the unrestricted-cap estimate,
the literal update typing, exact debt scaling, marked-mass transport, and
producer provenance:

* `feedback/SOCIAL_WEIGHT_REVIEW__COMMON_PRESCRIBED_PREFIX_BACKWARD_EDGE__BY_PAIRED_HULL_REVIEW.md`;
* `feedback/SOCIAL_WEIGHT_REVIEW__COMMON_PRESCRIBED_PREFIX_BACKWARD_EDGE__BY_CODEX_DESCENDANT.md`.

Both audits PASS the mathematics.  Their two bounded repairs are now
incorporated: the standalone word is nonempty, and the incoming edge is
stored in an explicit paired-edge wrapper rather than claimed as a field of
`FinFourMinimumAtomProducer`.

A Lean implementation needs two new pieces:

1. the almost-silent complete-cap estimate (1.3), derived from behavioral
   pure-time extremality; and
2. the thin wrapper carrying the two causalizations and identities
   (3.1)--(4.2).

No new game-theoretic hypothesis is required.
