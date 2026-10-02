# Paid-cycle finite-memory and source-reprojection obstruction

Identity: `CODEX_DESCENDANT`

## Status

The results below are proved in ordinary mathematics. They do not prove Fin4
uniform-equilibrium payoff existence. Sections 2--7 give a precise negative
answer for two proposed completion mechanisms:

1. no finite enrichment of the returned horizontal cycle can by itself make
   the cycle a renewable well-founded descent; and
2. finite unilateral-replacement ancestry carries no quantitative source
   return modulus, even when the ancestry is literal and has length at most
   four.

Together with the existing cell-exactification and clock-relabeling no-gos,
this proves that the present cycle passport is not a black-box producer of a
charged Nash--Bellman return.  A completion must add a new game-wide theorem
using positive-minimum/hard-residual geometry to construct an exit, a signed
source retraction, or an exact root chart.  The scalar fact \(D_*>0\) and the
finite labels already stored in the packet do not supply such a field.

Sections 11--12 add a positive reduction. A cycle vertex whose total debt
stays uniformly above the retained minimum source has a four-coordinate
retraction yielding either a paid reverse replacement or an actual paid row
at a literal retraction hybrid. If a cofinal family of cycle vertices instead
approaches the minimum, a one-player exact-response chord has a strict-support
minimum endpoint. The semantic chord is unconditional; regeneration as a
complete same-residual source uses the explicit supplied-family adapter in
Proposition 12.2. The paid-cap and tangent consumers downstream remain open.

## 1. Exact input

Let

\[
 x^0\longrightarrow x^1\longrightarrow\cdots
 \longrightarrow x^{L}=x^0
\tag{1.1}
\]

be the literal pure-clock cycle in
[`FIN4_FINITE_PURE_CLOCK_EXACT_RESPONSE_CYCLE.md`](../formalized/FIN4_FINITE_PURE_CLOCK_EXACT_RESPONSE_CYCLE.md).
On edge \(k\), one player \(i_k\) changes its complete strategy to an
unrestricted cap-attaining response, gains

\[
 g_k\ge D_*/4,
\tag{1.2}
\]

and has zero debt at the target.  Every target is definitionally the next
source, and every cycle vertex is strictly off the global minimum fibre.

The construction stores a finite replacement ancestry from one actual member
of a profile family converging to a positive global minimum.  It does not
store a signed path back to that family, an exact temporal root at a cycle
vertex, or a quantitative semantic seam from a cycle vertex to the minimum
source.

## 2. Finite replacement ancestry is universal

### Proposition 2.1

Let \(I\) have \(m\) players.  For any two behavioral profiles \(\sigma\)
and \(\tau\) of the same quitting game, there is a literal unilateral-
replacement ancestry of length at most \(m\) from \(\sigma\) to \(\tau\).

### Proof

Enumerate the players \(i_1,\ldots,i_m\).  Starting from \(\sigma\), at step
\(r\) replace the complete strategy of \(i_r\) by \(\tau_{i_r}\).  After
\(m\) steps every coordinate is that of \(\tau\).  No payoff sign,
reachability, root condition, or law comparison is used.  ∎

Thus in Fin4, bare ancestry of length at most four distinguishes no target
profile at all.  The ancestry is valuable only when individual edges carry
additional reached-row, gain, law, cap, or exact-root data.  In the current
cycle packet that quantitative data belongs to the entrance edge and the
horizontal cycle edges; the reverse path from a cycle vertex to the minimum
source carries none.

### Proposition 2.2 (no ancestry modulus)

There is no function of ancestry length alone which bounds terminal-law,
payoff, or complete semantic displacement by a quantity tending to zero.

### Proof

Fix two distinct nonempty coalitions \(S,T\).  Their pure date-zero profiles
are connected by the coordinate-replacement construction of Proposition 2.1,
yet their terminal laws are \(\delta_S\) and \(\delta_T\), at total-variation
distance one.  Reward coordinates at \(S,T\) may independently be chosen as
\(M\) and \(-M\), so prescribed-payoff displacement can be \(2M\).  The
ancestry length remains at most \(m\).  ∎

This is a probability-mode obstruction, not a claim about the global minimum
of that boundary table.  It says that a source-reprojection estimate must use
some retained quantitative edge field beyond `IsQuittingBehaviorReplacementAncestry`.

## 3. Finite-memory rank impossibility

One might try to orient (1.1) by adjoining payer, observer, coalition,
support, calendar, source-phase, or other finite passport labels.  The
following elementary theorem rules out every such construction unless it
also creates an exit from the returned cycle.

### Theorem 3.1 (finite deterministic memory)

Let \(X=\{0,\ldots,L-1\}\), with successor \(F(k)=k+1\pmod L\).  Let \(A\)
be any nonempty finite memory set and let

\[
 G:X\times A\longrightarrow X\times A,
 \qquad G(k,a)=(F(k),T(k,a))
\tag{3.1}
\]

for an arbitrary memory update \(T\).  There is no map \(\rho:X\times A\to W\)
to a well-founded strict order \((W,\prec)\) satisfying

\[
 \rho(G(s))\prec\rho(s)
\tag{3.2}
\]

at every state on every forward orbit.

### Proof

The finite set \(X\times A\) makes every forward orbit of \(G\) eventually
periodic.  On a periodic segment, iterating (3.2) gives a strict cycle in
\(W\), contradicting well-foundedness (indeed, merely irreflexivity and
transitivity).  ∎

### Theorem 3.2 (finite nondeterministic memory)

Let \(E\) be a finite nonempty directed state graph in which every state has
an outgoing edge.  No well-founded rank can strictly decrease on every edge
of \(E\).

### Proof

Following outgoing edges forever in a finite graph eventually produces a
directed cycle.  Strict decrease around that cycle is impossible.  ∎

These statements cover any finite state formed from the literal cycle vertex
and finitely many stabilized roles, coalitions, cap faces, stopping-time
orders, positive-support sets, or phase tags.  A one-use origin tag can lower
rank on the entrance edge, but after that tag is consumed the total successor
map is again finite and recurrent.  Resetting the tag at regeneration is
exactly the nonrenewable phase reset which the question excludes.

Therefore a valid finite rank must come with a theorem that at least one
cycle state has a transition **outside** the horizontal cycle into a terminal
consumer or a separately ranked source class.  Merely recording more finite
passport data cannot create that transition.

## 4. Calendar magnitude also supplies no state variable

Let \(\phi:\mathbb N\to\mathbb N\) be strictly increasing with
\(\phi(0)=0\), and put \(\phi(\infty)=\infty\).  Applying \(\phi\) to every
clock of every cycle vertex preserves:

- every terminal coalition and prescribed payoff;
- every unrestricted cap and debt at the pure-clock vertices;
- every canonical response category (preempt, join, or pass); and
- the literal response cycle and all its gains.

Hence absolute clock gaps, largest date, and calendar diameter can be made
arbitrarily large without changing the cycle passport.  Conversely, an
occupied positive calendar label cannot disappear on a returned canonical
cycle.  Thus neither deadline magnitude nor finite positive-date support can
be a renewable decreasing quantity on the off-minimum loop.

This is the exact clock-relabeling boundary already isolated in
[`SOCIAL_WEIGHT_REVIEW__OFF_MINIMUM_PURE_CLOCK_RESPONSE_CYCLE_TEMPORAL_ATTACK.md`](SOCIAL_WEIGHT_REVIEW__OFF_MINIMUM_PURE_CLOCK_RESPONSE_CYCLE_TEMPORAL_ATTACK.md).

## 5. Literal cell exactification cannot carry a later phase

Every strict pure-clock edge changes the displayed terminal coalition.  For
a same-level toggle

\[
 A\cup\{p\}\longleftrightarrow A,qquad A\ne\varnothing,
\tag{5.1}
\]

reproducing exactly the two literal endpoint rewards at one product root
requires every member of \(A\) to Quit surely.  The root then absorbs with
probability one under either action of \(p\), so its all-Continue survival is
zero and no subsequent phase is reached.

If the root is softened to have positive survival, other coalitions enter its
endpoint averages.  The strict cell inequality stored on the horizontal edge
gives no Nash sign for those averages or for the three nonmovers.  A
singleton reveal/preemption edge avoids the sure-host conclusion but still
stores only one mover comparison, not a four-player exact-root certificate.

Thus a temporal compiler has only the exact alternative

\[
\begin{array}{c}
\text{retain the literal cell comparison and get zero survival},\\
\text{or retain positive survival and require new averaged-root signs}.
\end{array}
\tag{5.2}
\]

The complete Farkas formulation in
[`CODEX_DESCENDANT__FINITE_PAID_CYCLE_EXACT_SHADOW_DUALITY.md`](CODEX_DESCENDANT__FINITE_PAID_CYCLE_EXACT_SHADOW_DUALITY.md)
identifies the same missing data as root and source-seam dual obstructions.

## 6. Exact black-box insufficiency theorem

Call a **cycle-internal compiler** any construction whose recursive states
consist of:

1. one literal vertex of (1.1);
2. any finite collection of labels determined by the reward table, the cycle,
   its finite ancestry, and the scalar floors already in the packet; and
3. successor edges which use only the stored horizontal response edges and
   deterministic/nondeterministic updates of those finite labels.

### Theorem 6.1

No cycle-internal compiler can produce a renewable well-founded descent.
Bare replacement ancestry cannot supply a vanishing or summable source-return
seam.  A cell-faithful exact temporalization of a nonsingleton toggle cannot
have positive survival.

### Proof

The rank assertion is Theorem 3.1 or 3.2.  The source-seam assertion is
Propositions 2.1--2.2.  The temporal assertion is Section 5.  These three
obstructions are independent: adding finite memory does not add a seam,
adding ancestry does not add a root, and retaining the literal root cell
eliminates survival.  ∎

The theorem remains true after attaching the positive constants \(D_*\),
\(D_*/4\), and \(D_*/12\) as finite-state labels.  It does **not** say that
positive global minimality is powerless.  Rather, any successful proof must
derive from it a new noninternal transition or quantitative source relation
which is not presently a field of the cycle packet.

## 7. Sharp missing datum

The obstruction leaves exactly three plausible additions:

1. **Exact-root exit.**  At one cycle vertex, construct a non-all-Continue
   exact root together with a continuation annotation and punishment-floor
   certificate.  This leaves the horizontal state graph and supplies actual
   temporal charge.
2. **Quantitative source retraction.**  Produce actual profiles returning
   from a cycle vertex to the retained minimum family with complete semantic
   seam \(o(a_n)\) relative to positive exact root charge \(a_n\), or with a
   fixed signed seam accepted by the existing telescope.
3. **Game-wide exclusion.**  Prove that the positive-minimum hard residual is
   incompatible with one of the finite semantic chambers obtained from the
   toggle-cycle dispatch.  This uses more than the scalar debt/gain floors
   and creates a genuine terminal exit.

The current packet supplies none of these.  In particular:

- repeating the literal horizontal loop only returns to the same alternative
  strategy profile;
- reversing the stored ancestry gives unsigned unilateral replacements;
- subdividing a response chord changes law and paid gain at the same linear
  rate; and
- a fresh finite timing Nash law is not source selected.

This is the exact sense in which the current obstruction is not “one more
finite potential.”  Any successful finite potential must first be fed a new
edge which exits the returned SCC.

## 8. Boundary and nonclaims

The exact response-cycle regressions with global minimum zero show that the
horizontal and cell-level data are mutually consistent.  They do not refute
a theorem which essentially uses \(D_*>0\); constructing a positive-minimum
regression would amount to constructing a counterexample to the conjecture.

No claim is made that every conceivable use of the full reward table is a
cycle-internal compiler.  Theorem 6.1 is a rigorous interface obstruction:
it rules out finite passport refinement, ancestry counting, clock ranks, and
literal-cell temporalization as completion mechanisms.  It deliberately
leaves open a new positive-minimum theorem producing one of the three exits
in Section 7.

## 9. Sources inspected

- [`FIN4_ACTUAL_PAID_CAP_DESCENT_OR_INERT_STALL.md`](../questions/FIN4_ACTUAL_PAID_CAP_DESCENT_OR_INERT_STALL.md);
- [`FIN4_FINITE_PURE_CLOCK_EXACT_RESPONSE_CYCLE.md`](../formalized/FIN4_FINITE_PURE_CLOCK_EXACT_RESPONSE_CYCLE.md);
- [`SOCIAL_WEIGHT_REVIEW__OFF_MINIMUM_PURE_CLOCK_RESPONSE_CYCLE_TEMPORAL_ATTACK.md`](SOCIAL_WEIGHT_REVIEW__OFF_MINIMUM_PURE_CLOCK_RESPONSE_CYCLE_TEMPORAL_ATTACK.md);
- [`CODEX_DESCENDANT__FINITE_PAID_CYCLE_EXACT_SHADOW_DUALITY.md`](CODEX_DESCENDANT__FINITE_PAID_CYCLE_EXACT_SHADOW_DUALITY.md);
- [`CODEX_DESCENDANT__MULTICOORDINATE_CAP_JENSEN_ACTIVE_FACE.md`](CODEX_DESCENDANT__MULTICOORDINATE_CAP_JENSEN_ACTIVE_FACE.md); and
- `QuittingOffMinimumPureTimeResponseCycle` and the literal-cycle declarations
  in
  `UniformEquilibrium/Diagnostics/Quitting/PureTimeSelectedExactResponseOrbit.lean`.

## 10. Next exact question

Can the positive-minimum hard residual force an exact-root exit or a signed
source retraction from one of the two residual semantic chambers in
`STRICT_TOGGLE_CYCLE_SEMANTIC_DISPATCH.md`?  Without such an exit, the finite
cycle and every finite passport refinement remain one nonterminal SCC by
Theorem 6.1.

## 11. Quantitative signed retraction from a uniformly off-minimum cycle

There is one source-reprojection theorem not contained in bare ancestry. It
uses the **signed endpoint debt excess**. It does not consume the remaining
nonmover arm, but it shows that a response cycle which stays uniformly away
from the minimum cannot avoid a fixed source-oriented seam.

### Proposition 11.1 (four-step signed retraction)

Let \(S\) and \(X\) be arbitrary actual Fin4 behavioral profiles in a table
with \(|r_i(T)|\le M\), and assume

\[
D(X)-D(S)=\delta>0.
\tag{11.1}
\]

Then there are actual profiles \(A,B\), differing in the complete strategy of
one player \(i\), such that \(A\to B\) is one step of a literal coordinatewise
retraction from \(X\) toward \(S\), and at least one of the following holds:

1. the retraction mover has actual payoff gain
   \[
   U_i(B)-U_i(A)\ge\delta/8;
   \tag{11.2}
   \]
2. one nonmover \(j\ne i\) has debt
   \[
   d_j(A)\ge\delta/24,
   \tag{11.3}
   \]
   and therefore the checked actual-reach theorem supplies at \(A\) a
   source-supported paid first-disagreement row of gain at least
   \[
   \delta/96.
   \tag{11.4}
   \]
   With \(\rho=\delta/24\), the same row retains
   \[
   \rho\le4M\,\operatorname{OwnSurvival},\qquad
   \rho\le8M\,\operatorname{OppReach},\qquad
   \rho^2\le32M^2\,\operatorname{JointReach}.
   \]
   holds.

Every endpoint in the retraction is a literal hybrid of \(S\) and \(X\). No
carrier representative or new source is selected.

#### Proof

Replace the four player coordinates of \(S\) by those of \(X\), in any fixed
order, and write the resulting actual profiles as

\[
S=Z^0,Z^1,Z^2,Z^3,Z^4=X.
\tag{11.5}
\]

The total debt rise is \(\delta\), so for some \(r<4\),

\[
D(Z^{r+1})-D(Z^r)\ge\delta/4.
\tag{11.6}
\]

Put \(A=Z^{r+1}\), \(B=Z^r\), and let \(i\) be the changed coordinate. Thus
\(A\to B\) is the corresponding reverse replacement. Write

\[
g=U_i(B)-U_i(A),
\qquad
\Delta=D(A)-D(B)\ge\delta/4.
\]

Because a player's unrestricted cap depends only on its opponents,
\(B_i(A)=B_i(B)\). The exact debt ledger is therefore

\[
\Delta
=g+\sum_{j\ne i}\bigl(d_j(A)-d_j(B)\bigr).
\tag{11.7}
\]

If \(g\ge\Delta/2\), then (11.2) follows. Otherwise the nonmover sum in
(11.7) is strictly greater than \(\Delta/2\ge\delta/8\). There are three
nonmovers, so one satisfies

\[
d_j(A)-d_j(B)\ge\delta/24.
\tag{11.8}
\]

Every debt is nonnegative, hence \(d_j(A)\ge\delta/24\). Apply
positiveDebt_exists_actualJointReach_paidRow_mem_support at the literal
profile \(A\), with debt floor \(\rho=\delta/24\). It gives a
source-supported row whose declared gain is \(\rho/4=\delta/96\), together
with the displayed reach bounds.
\(\square\)

The first arm is an actual source-reprojected paid replacement, not merely an
observer comparison. Since its source strategy for \(i\) is the \(X_i\)
coordinate and its target strategy is the \(S_i\) coordinate, pure-time
disintegration can further localize it to a paid first-disagreement row if a
row interface is desired. The second arm is also an actual paid-row output;
its source is the literal retraction hybrid \(A\), not an independently
selected carrier representative.

### Corollary 11.2 (uniform excess or near-minimum cycle)

Let \(S_n\) be actual source profiles with

\[
D(S_n)\longrightarrow D_*.
\]

For each \(n\), suppose a source-attached finite response cycle \(C_n\) is
constructed. Put

\[
E_n=\max_{X\in C_n}\bigl(D(X)-D_*\bigr).
\tag{11.9}
\]

After passage to a subsequence, the following alternative is available.

* If \(\limsup E_n>0\), there is a fixed \(\varepsilon>0\) and cofinally many
  \(n\) for which one cycle vertex \(X_n\) satisfies
  \(D(X_n)-D(S_n)\ge\varepsilon/2\). Proposition 11.1 then gives, on one
  fixed retraction coordinate after finite-label selection, either a paid
  reverse edge of gain at least \(\varepsilon/16\), or a source-supported
  paid first-disagreement row at a literal hybrid of gain at least
  \(\varepsilon/192\).
* If \(E_n\to0\), every vertex of every selected cycle approaches the global
  minimum fibre in total debt.

Indeed, in the first arm take \(E_n\ge\varepsilon\) and then
\(D(S_n)-D_*\le\varepsilon/2\). In the second arm (11.9) is the assertion.

This is the strongest source-oriented conclusion obtainable from total debt
alone. It makes the residual sharp:

\[
\boxed{
\begin{array}{c}
\text{uniformly off-minimum returned cycles}
\Longrightarrow
\text{fixed paid reverse edge or fixed paid row at a retraction hybrid};\\[1mm]
\text{otherwise every cycle vertex is asymptotically minimum.}
\end{array}}
\tag{11.10}
\]

Both outputs are now typed as actual paid interfaces. Their downstream
paid-cap trichotomy remains unconsumed. The near-minimum alternative still
needs the source reconstruction described in the next section. Thus
Proposition 11.1 is a genuine quantitative source retraction, but not yet a
Fin4 terminal consumer.

## 12. A near-minimum exact-response chord has a strict support endpoint

The response-cycle family suggests the following supplied-family theorem. Its
compact convex part is proved below. Source regeneration requires the
additional producer data stated separately afterward.

### Theorem 12.1 (semantic exact-response chord)

Fix one player \(i\). Let \(X_n,Y_n\) be actual Fin4 profiles such that:

1. \(Y_n\) differs from \(X_n\) only in player \(i\)'s complete strategy;
2. the new strategy attains \(i\)'s unrestricted cap at \(X_n\);
3. for some \(g_0>0\),
   \[
   U_i(Y_n)-U_i(X_n)=d_i(X_n)\ge g_0;
   \tag{12.1}
   \]
4. \(D(X_n)\to D_*\) and \(D(Y_n)\to D_*\); and
5. \(Y_n\) has one fixed nonempty terminal coalition \(K\) at an actual
   moving date \(t_n\), with stage mass at least \(\lambda>0\).

For fixed \(s\in(0,1)\), mix only player \(i\)'s complete stopping law and
write

\[
H_n^s=(1-s)X_n+_i sY_n.
\tag{12.2}
\]

After one common strict subsequence, the joint semantic/law points converge:

\[
X_n\to x,\qquad Y_n\to y,\qquad H_n^s\to h^s.
\]

Then

\[
D(x)=D(y)=D(h^s)=D_*,
\tag{12.3}
\]

and for every player \(j\),

\[
d_j(h^s)=(1-s)d_j(x)+s d_j(y).
\tag{12.4}
\]

For the mover,

\[
d_i(y)=0,\qquad d_i(x)\ge g_0,\qquad
d_i(h^s)=(1-s)d_i(x)>0.
\tag{12.5}
\]

Consequently

\[
\operatorname{supp}^+(y)
\subsetneq\operatorname{supp}^+(h^s),
\qquad
|\operatorname{supp}^+(y)|\le3.
\tag{12.6}
\]

The actual family \(Y_n\) retains \(K\)-mass at least \(\lambda\) at \(t_n\),
and \(H_n^s\) retains \(K\)-mass at least \(s\lambda\) there.

#### Proof

The mover's opponents do not change, so its unrestricted cap is identical at
the two endpoints. Exact attainment in (12.1) gives \(d_i(Y_n)=0\).

Prescribed payoff and terminal law are affine in the one-player stopping-law
mixture (12.2). Every fixed unrestricted response payoff of a nonmover is
affine in the same mixture, so its cap is convex; the mover cap is constant.
Thus, coordinatewise,

\[
d_j(H_n^s)\le(1-s)d_j(X_n)+s d_j(Y_n).
\tag{12.7}
\]

Global minimality and the two endpoint limits squeeze the sum of (12.7) to
\(D_*\). At a common compact limit all coordinate slacks are nonnegative and
sum to zero, proving (12.3)--(12.4). Equations (12.1) and cap invariance give
(12.5). Since \(D_*>0\), the support of \(y\) is nonempty; together with
(12.4)--(12.5), this gives (12.6).

The terminal law under (12.2) is the same convex mixture of the two endpoint
laws. On the component using the target stopping law, the literal marked
\(K\)-event is unchanged, proving the \(s\lambda\) floor.
\(\square\)

### Proposition 12.2 (conditional source adapter)

In addition to Theorem 12.1, suppose that:

1. one incoming Fin4 minimum-atom producer and its fixed hard residual are
   supplied;
2. \(X_n,Y_n\) are literal source-attached families obtained from that
   producer;
3. the marks \(t_n\), coalition \(K\), and positive stage-mass floors are
   retained as exact supplied-family data; and
4. source-faithful causalization applies to the literal \(Y_n\) and \(H_n^s\)
   families, with opponent-deleted survival tending to one.

Then causalization constructs complete same-residual minimum sources at \(y\)
and \(h^s\). Copy the exact prefix word selected for \(H_n^s\) onto \(Y_n\).
The common prescribed-prefix cap estimate, using opponent-deleted survival,
identifies the copied target cap with \(y\). Hence \(h^s\to y\) is a literal
source-regenerated strict-support edge, and the one-use phase transition may
enter the existing tangent trace.

This proposition is an adapter statement with explicit producer hypotheses.
The purely semantic hypotheses of Theorem 12.1 alone do not produce the
minimum sources.

### Corollary 12.3 (conditional response-cycle application)

Suppose a cofinal family of source-attached response cycles is supplied and
falls in the second arm of Corollary 11.2. Make one composed strict subsequence
which, in order, fixes the cycle edge, mover \(i\), target coalition \(K\), and
all later semantic/law compactification choices. Its mover gain is at least
\(D_*/4\), its target mover debt is zero, and both endpoint debts tend to
\(D_*\).

Every target is a pure-clock profile. It cannot be all Never cofinally:
otherwise its semantic pair is the fixed all-Never pair and would attain the
positive global minimum, contradicting
not_allNever_positiveMinimumTerminalSemanticDebt. Hence the fixed nonempty
coalition \(K\) terminates the target with mass one at its literal earliest
date. Theorem 12.1 applies with

\[
g_0=D_*/4,\qquad \lambda=1.
\]

Subject to Proposition 12.2, the near-minimum-cycle arm enters a minimum child
with debt support at most three. Without that source adapter, the proved output
is only the strict support relation (12.6) between compact semantic/law limits.

The current rigorous trichotomy is therefore

\[
\boxed{
\text{paid reverse edge}
\quad\text{or}\quad
\text{paid row at a retraction hybrid}
\quad\text{or}\quad
\text{a strict-support semantic chord requiring source reconstruction}.}
\tag{12.8}
\]

The first two outputs enter the paid-cap waist but do not consume it. The last
arm becomes renewable only under Proposition 12.2.
