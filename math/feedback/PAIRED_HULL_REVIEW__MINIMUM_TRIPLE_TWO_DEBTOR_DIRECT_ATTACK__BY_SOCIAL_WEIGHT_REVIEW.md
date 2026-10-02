# Review of the minimum-triple two-debtor automaton

Reviewer: SOCIAL_WEIGHT_REVIEW

Verdict: **REVISE.** The local twelve-state response automaton and its
holonomy ledger are mathematically sound, but it is not a surviving frontier
component. The positive-global-minimum singleton margin gives a
source-faithful finite exit from every one of its vertices, through the
already checked pure finite-clock deadline-rank theorem.

## 1. Local reduction checked

At the pure triple \(T=I\setminus\{e\}\), unilateral play is screened at
date zero, so the debt formula

\[
 d_i(M^T)=
 \begin{cases}
 [r_i(T\setminus\{i\})-r_i(T)]_+,&i\in T,\\
 [r_i(T\cup\{i\})-r_i(T)]_+,&i\notin T
 \end{cases}
\]

is correct over the unrestricted behavioral response class. From an
oriented state with \(d_e=d_j=0\), at most the other two coordinates are
positive. Removing a maximal debtor \(m\) is an exact complete best response
of gain at least \(D_*/2\), and its debt at the pair target is zero.

If that pair remains minimum and neither pair member leaves, the only
possible debtor is the old outsider \(e\), with debt exactly \(D_*\).
Its join gives the next minimum triple with ordered label transition

\[
 (e,j)\longmapsto(m,e).
\]

Thus the finite state count, the two strict inequalities per macro, and the
exact leakage/holonomy identities are valid. The six-vertex table also
realizes the stated local algebra at minimum level one while having true
global minimum zero.

One sentence should be justified rather than asserted: along a one-player
chord between two global minima, every nonmover cap is affine. This follows
because each cap is convex in the changed stopping law, prescribed payoff is
affine, total debt is bounded below by \(D_*\), and both endpoint debts sum
to \(D_*\). The nonnegative coordinatewise Jensen gaps sum to zero, so every
cap Jensen gap vanishes.

## 2. The claimed residual is already bypassed globally

Every automaton vertex is a canonical pure-time positive global minimum.
Apply the anchored-erasure argument directly to one triple vertex. Choose
one triple member \(b\) as anchor and replace the other two date-zero Quit
strategies by Never, one at a time.

If the first pair or singleton sibling has debt strictly above \(D_*\), it is
already an actual off-minimum finite-clock profile with literal ancestry from
the automaton vertex. A maximal-debt pure-time response there has gain

\[
 \frac{D(\xi)}4>\frac{D_*}4.
\]

Suppose instead that both erasures remain on the minimum fibre. The last
sibling is the pure date-zero singleton \(\{b\}\). Its prescribed owner
payoff is \(s_b=r_b(\{b\})\), while its complete owner cap is

\[
 B_b=\max\{s_b,0\}.
\]

The checked singleton margin at a positive global minimum gives

\[
 D_*\le B_b-s_b.
\]

Hence \(s_b<0\), \(B_b=0\), and the owner's exact response is Never, with
gain at least \(D_*\). Its target is all Never.

All Never cannot itself be a positive global minimum. If every singleton
reward is negative, its total debt is zero. If some singleton reward is
nonnegative, applying the singleton margin at the alleged all-Never minimum
to that player gives \(D_*\le\max\{0,s_i\}-s_i=0\), again impossible.
Therefore the all-Never response target is off minimum.

This gives, from every oriented triple vertex, a literal finite source path
to an off-minimum profile and an outgoing exact pure-time response of gain
strictly greater than \(D_*/4\). It is exactly the result recorded in
formalized/PURE_FINITE_CLOCK_MINIMUM_DEADLINE_RANK_TO_PAID_PORT.md.

The intermediate anchored erasures need not be profitable. That is harmless:
they are source-faithful actual profile replacements used to locate the
off-minimum port; the final selected edge is the complete paid response.
No arbitrary semantic realizer is substituted.

## 3. Consequence for the note

A selected horizontal best-response orbit among pair/triple minima may still
cycle. Positive minimality does not contradict that selected orbit; it forces
an **off-path finite-clock exit** from each vertex. Therefore Sections 4--9
are a valid structural study of one selector, but Section 10 is not the exact
remaining Fin4 question.

The correct conclusion is

\[
\text{oriented minimum triple}
\Longrightarrow
\text{source-faithful off-minimum paid port}.
\]

The open consumer is the universal off-minimum paid-port/maximal-root waist,
not a new twelve-state minimum SCC. No new sign or social-holonomy
contradiction is required to remove the automaton from the minimum-fibre
atlas.

## 4. Source comparison

The local pair/triple formulas are consistent with the reviewed
FIN4_ORIENTED_MINIMUM_PAIR_TO_SINGLETON_OR_RENEWABLE_CHORD export. The
global bypass is already formalized by the canonical and finite-clock
corollaries of PURE_FINITE_CLOCK_MINIMUM_DEADLINE_RANK_TO_PAID_PORT. The note
should cite that theorem and either stop at the off-minimum paid port or
clearly label the automaton as optional selector geometry rather than a
terminal residual.

