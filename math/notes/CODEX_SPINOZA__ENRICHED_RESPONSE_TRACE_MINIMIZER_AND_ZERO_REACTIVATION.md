# Enriched response-trace minimization stops at macroscopic zero reactivation

Author: `CODEX_SPINOZA`

## Status

The compact minimizer lemma and the four-state regression below are exact
ordinary mathematics, not checked in Lean.  The regression itself is the
law-enriched reading of a reward table whose unrestricted pure-time response
cycle is already checked in production Lean.

The positive result is conditional on a compact state space on which the debt
coordinates are continuous and the displayed response replacement is an
actual edge.  It proves a sharp alternative: a response leaves the global
minimum fibre, or a formerly zero debt reappears at a uniform positive scale.
It does **not** turn either alternative into a temporal Nash--Bellman block.

The negative result is exact and early: even after retaining the terminal law,
all four player-deleted laws, and all four selected best-response laws, a
finite exact-response cycle returns to the identical enriched state.  Hence
no scalar or finite lexicographic functional of those data can strictly
decrease under every best-response replacement.

## Question

Let \(I=\operatorname{Fin}4\), and for an actual behavioral profile
\(\sigma\) write

\[
 U_i(\sigma),\qquad
 B_i(\sigma)=\sup_{\tau_i}U_i(\tau_i,\sigma_{-i}),\qquad
 d_i(\sigma)=B_i(\sigma)-U_i(\sigma),\qquad
 D(\sigma)=\sum_i d_i(\sigma).
\]

Can one compactify the source together with its counterfactual laws, minimize
a scalar or lexicographic functional there, and use a best-response
replacement as a well-founded descent?

The finite outcome space is

\[
 \Omega=\{\mathsf{Never}\}\cup
 \{S\subseteq I:S\ne\varnothing\}.
\]

The depth-one enriched law record of an actual source and selected responses
\(q_i\) is

\[
 \mathcal T(\sigma,q)=
 \left(
   U(\sigma),B(\sigma),
   \nu(\sigma),
   \bigl(\nu(\sigma[i\leftarrow\mathsf{Never}])\bigr)_{i\in I},
   \bigl(\nu(\sigma[i\leftarrow q_i])\bigr)_{i\in I}
 \right),                                                     \tag{1}
\]

where \(\nu\) is the complete terminal-outcome law, including Never.  Thus
(1) retains one source law, four player-deleted laws, and four selected
response laws.  Each \(q_i\) may be exact or \(\varepsilon\)-optimal against
the source's actual opponents.

## Sources inspected

The complete behavioral cap and pure-time extremality are in
`BehaviorPureTimeExtremality.lean`.  Exact pure-clock cap attainment in one
inherited finite alphabet is
`exists_quittingPureTime_capAttainer_mem_inheritedResponseAlphabet` in
`PureTimeInheritedResponseAlphabet.lean`.

The checked literal response operation, zero target debt, and exact mover
gain are respectively
`QuittingPureTimeMaxDebtExactResponseStep`,
`QuittingPureTimeMaxDebtExactResponseStep.target_mover_debt_eq_zero`, and
`QuittingPureTimeMaxDebtExactResponseStep.mover_payoff_gain_eq_source_debt`
in `PureTimeSelectedExactResponseOrbit.lean`.  The finite-orbit output is
`exists_minimumDebtEntrance_xor_offMinimumExactResponseCycle` in
`PureTimeExactResponseMinimumAlternative.lean`.

The exact reward-table regression is recorded in
`formalized/FIN4_FINITE_PURE_CLOCK_EXACT_RESPONSE_CYCLE.md`; its response
orbit is checked by the preceding declarations.  The older local debt-transfer
screen is `notes/CODEX_RIEMANN__FULL_SCREEN_CLEARING_DEBT_ROTATION_NOGO.md`.

The topological boundary of finite response-law records is in
`arch/SUFFIX_INFORMATION_OBSTRUCTION.md` and the checked
`CounterfactualSuffixCompactnessNoGo.lean`: present payoff-response data do
not determine literal suffixes.  The split Late/Never compactification and
its actuality caveat are in `arch/EXECUTABLE_COMPACT_STATE.md`.

## 1. Abstract compact enriched trace

The minimizer calculation needs much less than a proposed universal
compactification.  Let \(K\) be a compact space of enriched trace nodes, let

\[
 d_i:K\to[0,\infty)
\]

be continuous, and put \(D=\sum_i d_i\).  A directed edge
\(x\stackrel{p,\varepsilon}{\longrightarrow}y\) means that it is backed by
an actual one-player replacement at the source represented by \(x\), with
the following two exact fields:

1. the opponents of \(p\) are unchanged; and
2. the new strategy of \(p\) is within \(\varepsilon\) of its unrestricted
   cap.

Consequently

\[
 d_p(y)\le\varepsilon.                                      \tag{2}
\]

For an exact best response, \(\varepsilon=0\).  Terminal, deleted, and
response laws may be coordinates of \(K\), but the edge must retain literal
replacement ancestry; equality of the finite law record alone does not define
the operation.

Write

\[
 D_*^K=\min_{x\in K}D(x),\qquad
 F=\{x\in K:D(x)=D_*^K\}.                                  \tag{3}
\]

Assume \(D_*^K>0\).  For \(x\in F\), let

\[
 A(x)=\{i:d_i(x)>0\},\qquad
 m=\min_{x\in F}|A(x)|.                                    \tag{4}
\]

Then \(1\le m\le4\).  Let \(a_m(x)\) be the \(m\)-th largest of the four
numbers \(d_i(x)\), and define

\[
 \alpha=\min_{x\in F}a_m(x).                               \tag{5}
\]

### Lemma 1.1 (uniform active-coordinate moat)

\[
 \boxed{\alpha>0.}                                          \tag{6}
\]

#### Proof

Every point of \(F\) has at least \(m\) positive coordinates, so
\(a_m(x)>0\) pointwise on \(F\).  The order statistic \(a_m\) is continuous,
and \(F\) is compact.  If its minimum were zero, a minimizing point would
have at most \(m-1\) positive coordinates, contrary to (4).  \(\square\)

The compactness in this proof is substantive.  Without it, the newly active
coordinate may tend to zero along a moving sequence.

## 2. Minimum response dichotomy

### Theorem 2.1 (off-fibre response or macroscopic zero reactivation)

Choose \(x\in F\) with \(|A(x)|=m\), choose \(p\in A(x)\), and suppose

\[
 x\stackrel{p,\varepsilon}{\longrightarrow}y,
 \qquad 0\le\varepsilon<\alpha.                            \tag{7}
\]

Then exactly one of the following broad alternatives holds:

1. **off the minimum fibre:** \(D(y)>D_*^K\); or
2. **macroscopic zero reactivation:** \(y\in F\), and there is
   \(j\notin A(x)\) such that

   \[
   d_j(x)=0,\qquad d_j(y)\ge\alpha.                         \tag{8}
   \]

In particular, if a class of response edges preserves every old zero debt,
then every sufficiently accurate response by an active player leaves the
minimum fibre.

#### Proof

Global minimality gives \(D(y)\ge D_*^K\).  Suppose equality holds.  By
Lemma 1.1, at least \(m\) coordinates of \(y\) have debt at least \(\alpha\).
Equation (2) and \(\varepsilon<\alpha\) exclude \(p\) from these coordinates.
Only \(m-1\) players remain in \(A(x)\setminus\{p\}\).  Therefore one of the
\(m\) coordinates is a player \(j\notin A(x)\), and (8) follows.  \(\square\)

### Corollary 2.2 (full-debt ejection)

If \(m=4\), every response in (7) is off the minimum fibre.  There is no old
zero coordinate available to satisfy (8).

This is the abstract core of the already formalized full-debt contraction
packet; it is not a new consumer of that packet.

### Corollary 2.3 (exact transfer account on the minimum fibre)

If the response in Theorem 2.1 is exact and \(y\in F\), then

\[
 d_p(y)=0,
 \qquad
 \sum_{j\ne p}\bigl(d_j(y)-d_j(x)\bigr)=d_p(x).             \tag{9}
\]

Hence some spectator debt rises by at least \(d_p(x)/3\).  The spectator in
this averaging conclusion need not be the newly activated player in (8).

#### Proof

Exact cap attainment and unchanged opponents give \(d_p(y)=0\).  Subtract
the equalities \(D(x)=D(y)=D_*^K\) and isolate the \(p\)-coordinate.  The
Fin4 average gives the last assertion.  \(\square\)

### Compact target-fibre refinement

For fixed \(x,p,\varepsilon\), suppose the target set

\[
 R_{p,\varepsilon}(x)=
 \{y:x\stackrel{p,\varepsilon}{\longrightarrow}y\}
\]

is nonempty and compact.  If it does not meet \(F\), then continuity gives a
literal separation

\[
 \eta_{p,\varepsilon}(x)
 :=\min_{y\in R_{p,\varepsilon}(x)}(D(y)-D_*^K)>0.           \tag{10}
\]

Thus a compact executable response fibre gives either a uniformly separated
off-minimum port or a minimum-fibre zero reactivation of size (\alpha).
The theorem does not identify either response edge with a Nash--Bellman root
or with chronological absorption charge.

## 3. What lexicographic minimization actually adds

One may refine the choice of \(x\) by minimizing, in order,

\[
 \left(D(x),\ |A(x)|,\ \Phi(\mathcal T(x))\right),          \tag{11}
\]

where \(\Phi\) is any continuous scalarization of the nine terminal-law
coordinates in (1).  On an equal-\(D\) response target, the second coordinate
cannot decrease, by the definition of \(m\).  If it remains equal, the last
coordinate cannot be smaller than at the selected minimizer.

This is not response descent.  It merely says that a same-fibre response is
forced to move weakly upward in the chosen tie-breaker after it rotates debt
to an old zero.  Reversing the tie-breaker reverses which edge is favorable;
no choice makes all response edges descend, as the next exact regression
shows.

## 4. Exact Fin4 law-enriched cycle regression

Use players \(0,1,2,3\).  For coalitions contained in \(\{0,1\}\), set

\[
\begin{array}{c|ccc}
S&\{0\}&\{1\}&\{0,1\}\\ \hline
r_0(S)&1&1&0\\
r_1(S)&0&-1&1,
\end{array}                                                 \tag{12}
\]

and set the coordinates of players \(2,3\) to zero.  For every coalition
containing player \(2\) or \(3\), set the entire reward vector to zero.

Let \(0\) denote Quit surely at date zero and \(\infty\) denote Never.  Put

\[
 x_0=(\infty,\infty,\infty,\infty),\quad
 x_1=(0,\infty,\infty,\infty),\quad
 x_2=(0,0,\infty,\infty),\quad
 x_3=(\infty,0,\infty,\infty).                             \tag{13}
\]

The literal response orbit is

\[
 x_0\xrightarrow{0}x_1\xrightarrow{1}x_2
 \xrightarrow{0}x_3\xrightarrow{1}x_0.                    \tag{14}
\]

Every displayed mover gains exactly one and attains its unrestricted
behavioral cap.  The payoff, cap, and debt vectors are

\[
\begin{array}{c|c|c|c}
 &U&B&d\\ \hline
x_0&(0,0,0,0)&(1,0,0,0)&(1,0,0,0)\\
x_1&(1,0,0,0)&(1,1,0,0)&(0,1,0,0)\\
x_2&(0,1,0,0)&(1,1,0,0)&(1,0,0,0)\\
x_3&(1,-1,0,0)&(1,0,0,0)&(0,1,0,0).
\end{array}                                                 \tag{15}
\]

Thus \(D=1\) and \(|A|=1\) at all four states.  Every edge kills the mover's
only debt and reactivates the other active player's old zero debt at size one.

For completeness, choose for each zero-debt player its prescribed clock as
the selected cap response.  The source terminal laws along (13) are

\[
 \mathsf N,\quad \delta_{\{0\}},\quad
 \delta_{\{0,1\}},\quad\delta_{\{1\}},                     \tag{16}
\]

where \(\mathsf N\) is the point mass on Never.  The four player-deleted law
tuples are

\[
\begin{array}{c|cccc}
 &-0&-1&-2&-3\\ \hline
x_0&\mathsf N&\mathsf N&\mathsf N&\mathsf N\\
x_1&\mathsf N&\delta_{\{0\}}&\delta_{\{0\}}&\delta_{\{0\}}\\
x_2&\delta_{\{1\}}&\delta_{\{0\}}&\delta_{\{0,1\}}&\delta_{\{0,1\}}\\
x_3&\delta_{\{1\}}&\mathsf N&\delta_{\{1\}}&\delta_{\{1\}}.
\end{array}                                                 \tag{17}
\]

The four selected-response law tuples are

\[
\begin{array}{c|cccc}
 &+0&+1&+2&+3\\ \hline
x_0&\delta_{\{0\}}&\mathsf N&\mathsf N&\mathsf N\\
x_1&\delta_{\{0\}}&\delta_{\{0,1\}}&\delta_{\{0\}}&\delta_{\{0\}}\\
x_2&\delta_{\{1\}}&\delta_{\{0,1\}}&\delta_{\{0,1\}}&\delta_{\{0,1\}}\\
x_3&\delta_{\{1\}}&\mathsf N&\delta_{\{1\}}&\delta_{\{1\}}.
\end{array}                                                 \tag{18}
\]

After the fourth edge, not only the prescribed profile but the entire tuple
(1) is literally the original tuple.  Therefore, for **every** function
\(\Psi\) of the enriched record,

\[
 \Psi(\mathcal T(x_0))>\Psi(\mathcal T(x_1))>
 \Psi(\mathcal T(x_2))>\Psi(\mathcal T(x_3))>
 \Psi(\mathcal T(x_0))                                    \tag{19}
\]

is impossible.  The same applies to a finite lexicographic tuple or a
natural-valued rank.

The finite set \(K_0=\{\mathcal T(x_k):0\le k<4\}\) is compact, its selected
response graph is closed and serial, and its restricted minimum debt is one.
So positivity of a **restricted** compact trace minimum is not enough.  The
table is not a counterexample to the quitting-game conjecture: player \(2\)
quitting surely at date zero while everyone else Never stops is an exact
terminal Nash profile with zero debt.  The missing hypothesis in any global
application is genuinely that the compact response-closed object represents
the global positive minimum rather than a selected positive subcycle.

## 5. Compactification boundary

The nine law coordinates in (1) lie in a finite product of simplices, so
their closure is compact.  Two further assertions do **not** follow from that
formal compactness.

1. A boundary tuple need not be generated by one actual source and four
   actual response laws.  Finite stopping mass can escape to Late, which is
   strategically distinct from Never.
2. A depth-one record does not determine the next literal response diagram.
   After replacing player \(p\), the four new caps and response laws depend on
   the child's actual opponents.  Iterating requires response data at every
   descendant.  Finite-depth records are compact, but an infinite-depth law
   tree has no automatic common actualization or suffix congruence.

Accordingly Theorem 2.1 applies without qualification to a supplied compact
**executable** response relation (for example, a fixed finite pure-clock
alphabet).  Applying it to the closure of (1) requires a separate actuality,
tightness, or finite-diagram fusion theorem.  Merely adding more terminal-law
coordinates does not provide that theorem.

## 6. Positive-minimum restrictions on a returned response cycle

The previous regression does not use a genuine positive global minimum.
There are two exact consequences of that missing hypothesis.

### Proposition 6.1 (a best-response target cannot be its pure singleton)

Assume the game is punishment-normal, \(D_*>0\), and \(y\) is a global
minimum semantic/law point.  If \(d_p(y)=0\), then the terminal law of \(y\)
is not the point mass on \(\{p\}\).

#### Proof

The checked theorem
minimumTerminalSemantic_strictSingleton_of_punishmentNormal gives

\[
 r_p(\{p\})<U_p(y).
\]

If the terminal law were \(\delta_{\{p\}}\), the checked reward-moment
identity would instead give \(U_p(y)=r_p(\{p\})\).  \(\square\)

Thus the singleton vertices in (13)--(14) cannot occur as zero-debt targets
on a punishment-normal positive global-minimum fibre.  A surviving cycle has
to use nonsingleton or genuinely mixed terminal laws.  This is a real use of
the positive-minimum source, but it does not exclude pair/triple cycles.

The quantitative form used below is the checked singleton-margin inequality:
at any positive global minimum,

\[
 D_*-d_i(y)\le U_i(y)-r_i(\{i\}).                         \tag{20}
\]

In particular a zero-debt target earns at least \(D_*\) above its solo
reward.

## 7. Finite response-complete cycles force zero global debt

Let \(A_i\) be a nonempty finite set of actual complete strategies for player
\(i\), and let

\[
 P=\prod_i\Delta(A_i)                                     \tag{21}
\]

be their independently mixed product hull.  Ex ante mixing of finitely many
stopping laws is again one stopping law, so every point of \(P\) has an
ordinary behavioral realization.

Call the menu \(A=(A_i)_i\) **response-complete on its hull** if, for every
\(\lambda\in P\) and player \(i\),

\[
 B_i(\lambda)
 =
 \max_{a_i\in A_i}U_i(a_i,\lambda_{-i}).                  \tag{22}
\]

### Theorem 7.1 (finite hull completion)

If one finite menu is response-complete on its hull, the quitting game has an
actual terminal Nash profile.  Consequently \(D_*=0\).

#### Proof

The finite normal-form game with pure strategy sets \(A_i\) has a mixed Nash
equilibrium \(\lambda^*\).  At that point,

\[
 U_i(\lambda^*)=
 \max_{a_i\in A_i}U_i(a_i,\lambda^*_{-i}).
\]

Equation (22) identifies the right side with the unrestricted behavioral cap.
Thus every \(d_i(\lambda^*)=0\).  The independent finite mixtures compile to
one actual behavioral profile, so this is a terminal Nash profile against
every behavioral deviation.  \(\square\)

### Corollary 7.2 (global-gap interior escape)

Assume instead that every actual profile has total debt at least
\(D_*>0\).  For every finite menu \(A\), let \(\lambda^*\) be a Nash
equilibrium of its finite normal form.  Then some player \(i\) has an
unrestricted response outside the menu inequality with gain at least
\(D_*/4\): for every \(\zeta>0\), some complete response \(\tau_i\) satisfies

\[
 U_i(\tau_i,\lambda^*_{-i})-U_i(\lambda^*)
 \ge D_*/4-\zeta.                                         \tag{23}
\]

No member of \(A_i\) can realize a positive right side, by finite-menu Nash
optimality.

#### Proof

The behavioral realization of \(\lambda^*\) has total debt at least \(D_*\),
so one of four coordinates is at least \(D_*/4\).  Approximate its
unrestricted cap within \(\zeta\).  \(\square\)

Now start from any finite exact response cycle and let \(A_i\) contain every
complete strategy of player \(i\) appearing at a cycle vertex, together with
every selected response stored in the enriched record.  Literal return of
the source, terminal laws, player-deleted laws, and selected response laws
does not close the argument.  Under a positive global gap, Corollary 7.2
forces a new response at a generally interior mixed profile of the hull.
The vertex records do not assert (22).

This identifies the exact global obstruction:

\[
 \boxed{
 \text{a positive-minimum finite response cycle must fail response
 completeness away from its visited vertices}.}           \tag{24}
\]

It is stronger than saying that the cycle is merely horizontal.  It produces
a literal finite-menu Nash source and a fresh all-behavior gain of scale
\(D_*/4\).  It still does not attach that new source to the original
minimum-fibre chronology.

## 8. The smallest pair/triple rectangle is impossible

There is one quitting-specific case in which vertexwise data *does* imply the
missing hull completion.

Fix distinct players \(p,q\).  At date zero let a fixed nonempty set
\(C\subseteq I\setminus\{p,q\}\) Quit surely.  Let every remaining spectator
Continue at date zero (its later strategy is irrelevant), and allow \(p,q\)
only the two date-zero actions Quit and Continue.  The resulting four
profiles have terminal coalitions

\[
 C,\qquad C\cup\{p\},\qquad C\cup\{p,q\},\qquad C\cup\{q\}.
                                                               \tag{25}
\]

Suppose every spectator has zero unrestricted debt at all four corners.

### Theorem 8.1 (anchored rectangular cycle closure)

The convex product square generated by the two actions of \(p,q\) contains
an actual unrestricted terminal Nash profile.  Hence the four corners cannot
all lie on a genuine positive global-minimum fibre.

#### Proof

Because \(C\ne\varnothing\) Quits surely at date zero, play terminates at that
date under every unilateral deviation by \(p\) or \(q\).  Such a deviation
therefore reduces exactly to the deviator's date-zero Quit probability.
Their binary menus are response-complete on the whole square.

Fix a spectator \(k\).  Its unrestricted debt is nonnegative and convex
along a one-player stopping-law chord.  On each of the two boundary edges it
is bounded above by the interpolation of its zero corner values, hence is
zero.  Applying the same argument in the other coordinate shows

\[
 d_k=0
\]

throughout the product square.

Choose a mixed Nash equilibrium of the \(2\times2\) game of \(p,q\).
Binary response completeness gives zero unrestricted debt to \(p,q\), while
the preceding paragraph gives zero debt to every spectator.  Its behavioral
realization is the required terminal Nash profile.  \(\square\)

This theorem rules out the most economical nonsingleton repair of the
four-state regression: a square

\[
 \{2,3\}\to\{0,2,3\}\to I\to\{1,2,3\}\to\{2,3\}
                                                               \tag{26}
\]

with zero spectator debts necessarily has an equilibrium in its mixed
rectangle.  All terminal and player-deleted laws in (26) return exactly, but
that return supports rather than obstructs the finite-menu compiler.

A genuine positive-minimum response cycle must therefore violate at least one
of the following small-cycle fields:

1. two-player rectangularity;
2. a fixed sure-quitting nonempty core;
3. zero spectator debt at every corner; or
4. hull-wide response completeness.

The general finite enriched cycle is not excluded: its forced new response
from Corollary 7.2 can live only at an unvisited mixed hull point and may use
a clock absent from the cycle.

## 9. Verdict and precise next question

The strongest unconditional minimizer output is

\[
 \boxed{
 \text{uniform off-minimum separation}
 \quad\text{or}\quad
 \text{macroscopic reactivation of an old zero debt}.}
\]

The second arm is not a defect of coarse state: it persists after the full
depth-one terminal/deleted/response law record is retained, and (12)--(18)
show an exact finite rotation.  Thus this lane does not yield a well-founded
rank or a terminal approximate Nash profile.

The global hypothesis does eliminate pure-singleton targets and
response-complete finite cycles.  For any surviving finite enriched cycle it
produces a new all-behavior response at a mixed hull point, with gain
\(D_*/4-o(1)\).  What it does not provide is ancestry from that newly solved
finite-menu Nash source back to a visited minimum source.

The remaining precise question is whether the source law, all four
player-deleted laws, and the finite cycle's literal replacement edges can
attach the Corollary 7.2 interior escape to one visited source with a
summable seam.  Without such an attachment, iteratively enlarging the menu
returns to the already known moving-deadline/Late--Never boundary.  Another
scalarization of the vertex law record cannot suffice.
