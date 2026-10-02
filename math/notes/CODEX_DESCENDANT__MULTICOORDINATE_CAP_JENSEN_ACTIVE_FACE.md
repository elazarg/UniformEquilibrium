# Multicoordinate cap Jensen identity and the rectangular-hull obstruction

Author: CODEX_DESCENDANT

## Status

**Ordinary theorem proved; no Fin4 consumer.** Independent product mixing of
finitely many pure-clock strategy choices gives an exact identity:

\[
 \text{debt of the mixed actual profile}
 =\text{average vertex debt}
  -\text{common-response incompatibility}.
\]

Thus a product perturbation falls below the global minimum exactly when the
cap incompatibility exceeds the average off-minimum excess of the entire
rectangular hull. A response cycle supplies only a correlated list of
vertices. An actual behavioral mixture uses independent player marginals and
therefore creates every cross vertex; the cycle ledger does not bound their
debt excess.

For finite pure clocks, the incompatibility is a finite active-face
minimization over pure stopping times. Hence the remaining obstruction is
not an abstract supremum: it is either one common cap-optimal stopping time
across the relevant rectangle, or a fixed finite response-face switch whose
cost is paid by off-minimum cross vertices.

Saturating the clock alphabet does not turn the common-response arm into a
producer. Hard finite timing Nash laws recover only the checked
adjacent-boundary separation and have no minimum-source entrance. Exact
retained-tail timing Nash laws are forced to be the identity near a full-debt
minimum; the same is quantitatively true for approximate timing Nash laws.

The exact table in
`notes/CODEX_DESCENDANT__FINITE_PAID_CYCLE_EXACT_SHADOW_DUALITY.md`
realizes the latter alternative. It has a paid full-response cycle and debt
at least two on every one-coordinate face, yet one simultaneous product
mixture has debt \(443/400<2\).

## 1. Finite rectangular pure-clock data

Let \(I\) be finite. For each player \(j\), let \(A_j\) be a nonempty finite
set of pure quitting times in

\[
 \overline{\mathbb N}=\mathbb N\cup\{\mathsf{Never}\}.
\]

For \(a=(a_j)_j\in A:=\prod_j A_j\), let \(\sigma^a\) be the corresponding
pure-clock profile. Choose probability laws \(\pi_j\) on \(A_j\), and put

\[
 w(a)=\prod_j\pi_j(a_j).
\tag{1.1}
\]

The mixed stopping law \(\bar\sigma_j\) of player \(j\) is \(\pi_j\). It has
the canonical behavioral-hazard realization. Because the players randomize
independently, \(\bar\sigma=(\bar\sigma_j)_j\) is an ordinary actual
behavioral profile, not a correlated or sunspot profile.

Write

\[
 U_i(a)=U_i(\sigma^a),\qquad B_i(a)=B_i(\sigma^a),
 \qquad d_i(a)=B_i(a)-U_i(a).
\]

For a pure stopping-time response \(s\in\overline{\mathbb N}\), write

\[
 V_i(s,a)=U_i(s,\sigma^a_{-i}).
\tag{1.2}
\]

The value in (1.2) is independent of \(a_i\).

## 2. Exact cap Jensen identity

Define the common-response incompatibility of coordinate \(i\) by

\[
 \kappa_i(\pi)
 :=\sum_{a\in A}w(a)B_i(a)-B_i(\bar\sigma).
\tag{2.1}
\]

### Theorem 2.1

For every player \(i\),

\[
 \kappa_i(\pi)
 =\inf_{s\in\overline{\mathbb N}}
   \sum_{a\in A}w(a)\bigl(B_i(a)-V_i(s,a)\bigr)
 \ge0.
\tag{2.2}
\]

Moreover,

\[
 d_i(\bar\sigma)
 =\sum_{a\in A}w(a)d_i(a)-\kappa_i(\pi),
\tag{2.3}
\]

and therefore

\[
 \boxed{
 D(\bar\sigma)
 =\sum_{a\in A}w(a)D(\sigma^a)
  -\sum_{i\in I}\kappa_i(\pi).}
\tag{2.4}
\]

### Proof

Linearity of expected payoff under independent mixing gives

\[
 U_i(\bar\sigma)=\sum_aw(a)U_i(a).
\tag{2.5}
\]

For every fixed pure response \(s\), the same product expansion gives

\[
 U_i(s,\bar\sigma_{-i})=\sum_aw(a)V_i(s,a).
\tag{2.6}
\]

Pure-time extremality of the quitting cap yields

\[
 B_i(\bar\sigma)
 =\sup_s\sum_aw(a)V_i(s,a).
\tag{2.7}
\]

Subtracting (2.7) from the constant \(\sum_aw(a)B_i(a)\) proves (2.2).
Each summand inside the infimum is nonnegative because \(B_i(a)\) is the
unrestricted cap at vertex \(a\). Thus \(\kappa_i\ge0\). Subtract (2.5) from
(2.1) to get (2.3), and sum over players to get (2.4). \(\square\)

This is the multicoordinate version of the one-owner cap-Jensen identity. No
continuity, cap attainment, or finite-horizon restriction is used in
Theorem 2.1.

## 3. Exact finite active-face form

Let \(T\) exceed every finite clock appearing in the rectangle. Against a
pure-clock vertex, every pure response time belongs to one of finitely many
payoff classes:

\[
 0,1,\ldots,T,\quad T+1,\quad\mathsf{Never}.
\tag{3.1}
\]

All finite times strictly larger than \(T\) have the same value: a finite
opponent clock has already stopped the game, while on the event that all
opponents are Never the responder receives its singleton reward. Therefore
the infimum in (2.2) is a minimum over the finite set (3.1).

Let

\[
 \omega=\min\{w(a):w(a)>0\}.
\]

Choose a minimizing response \(s_i^*\) in (2.2). Since every vertex regret is
nonnegative,

\[
 B_i(a)-V_i(s_i^*,a)
 \le {\kappa_i(\pi)\over w(a)}
 \le {\kappa_i(\pi)\over\omega}
\tag{3.2}
\]

at every positive-weight vertex.

In particular,

\[
 \kappa_i(\pi)=0
\quad\Longleftrightarrow\quad
\text{one pure time is cap-optimal for \(i\) at every
positive-weight vertex.}
\tag{3.3}
\]

Thus the cap-switch alternative is finite and falsifiable. It is not enough
that different vertexwise maximizers exist: what matters is the absence of
one common maximizer.

## 4. Global-minimum product-perturbation ledger

Let \(D_*>0\) be the global minimum of total debt on the actual behavioral
carrier, and define the vertex excess

\[
 e(a)=D(\sigma^a)-D_*\ge0.
\]

Since \(\bar\sigma\) is actual, global minimality and (2.4) imply

\[
 \boxed{
 \sum_i\kappa_i(\pi)
 \le\sum_aw(a)e(a).}
\tag{4.1}
\]

More exactly,

\[
 D(\bar\sigma)-D_*
 =\sum_aw(a)e(a)-\sum_i\kappa_i(\pi).
\tag{4.2}
\]

This gives the requested product-perturbation criterion.

### Corollary 4.1: strict simultaneous descent

If

\[
 \sum_i\kappa_i(\pi)>\sum_aw(a)e(a),
\tag{4.3}
\]

then \(D(\bar\sigma)<D_*\), contradicting global minimality.

### Corollary 4.2: minimum rectangles have common cap responses

If every positive-weight vertex is on the minimum fibre, then every
\(\kappa_i=0\). Hence each player has one pure stopping time which is
simultaneously cap-optimal at every positive-weight vertex, and

\[
 D(\bar\sigma)=D_*.
\tag{4.4}
\]

### Corollary 4.3: near-minimum quantitative rigidity

If the weighted average vertex excess is at most \(\varepsilon\), then

\[
 \sum_i\kappa_i\le\varepsilon.
\tag{4.5}
\]

For a finite pure-clock rectangle, (3.2) supplies for every player one pure
time whose regret at every positive-weight vertex is at most
\(\varepsilon/\omega\).

## 5. Why a response cycle is not yet a product descent

A horizontal response cycle is a list

\[
 a^0\to a^1\to\cdots\to a^{L-1}\to a^0
\tag{5.1}
\]

of pure profiles. A probability law on the phases of (5.1) is generally
correlated across players. It is not an ordinary behavioral strategy
profile.

Taking its playerwise clock marginals produces the product law (1.1). Its
support is the full rectangular hull

\[
 \prod_j\{a_j^k:0\le k<L\},
\tag{5.2}
\]

which usually contains many cross vertices not present in the cycle. The
cycle's paid gains and adverse-externality ledger say nothing about the
excess \(e(a)\) at those cross vertices. Equation (4.2) shows that these
uncontrolled excesses pay for a positive cap incompatibility.

Consequently a stabilized R-obstruction from the finite-shadow dual gives a
strict product descent only after one proves an active-face inequality of
the form

\[
 \sum_i\kappa_i
 >\mathbb E_w e.
\tag{5.3}
\]

A stabilized S-obstruction is even more orthogonal: it is a mismatch of
successive Bellman states and contributes neither side of (4.2) without an
actual target-to-next-source identification.

## 6. Exact boundary table account

For table (15.1) of the companion note, take

\[
 \pi=(1/20,\ 1/2,\ 2/5,\ 1/2)
\]

as the four Quit-at-zero probabilities, with Never as the other clock.
The exact vertex-cap average and mixed caps are

\[
 \mathbb E B=(11/4,\ 809/200,\ 263/80,\ 171/40),
\]

\[
 B(\bar\sigma)=(11/4,\ 561/200,\ 199/80,\ 61/20).
\]

Therefore

\[
 \kappa=(0,\ 31/25,\ 4/5,\ 49/40),
 \qquad \sum_i\kappa_i=653/200.
\tag{6.1}
\]

The average vertex debt and the mixed debt are

\[
 \mathbb E D=1749/400,
 \qquad D(\bar\sigma)=443/400,
\tag{6.2}
\]

and (2.4) is the exact equality

\[
 443/400=1749/400-653/200.
\]

At the benchmark \(D_{\mathrm{ref}}=2\), the average cross-vertex excess is

\[
 \mathbb E(D-D_{\mathrm{ref}})=949/400,
\]

which is smaller than the cap incompatibility \(653/200\); this is why the
simultaneous mixture crosses below the benchmark. The calculation also shows
why checking only the cycle vertices or the one-coordinate faces cannot
decide (4.3).

## 7. Relation to existing cap-switching work

The single-owner Jensen identity and zero-face regeneration criterion are
already recorded in
`notes/CODEX_ADVERSARY__RESET_RIGID_ZERO_FACE_JENSEN_BARRIER.md`.
The balanced infinitesimal reset theorem is recorded in
`notes/CODEX_ROOT__BALANCED_CAP_LEAKAGE_RIGIDITY.md`.

The new content here is the exact finite rectangular formula (2.2)--(2.4),
its common-active-face characterization, and the identification of the
uncounted cross-vertex excess as the precise obstruction to applying it to a
finite response cycle.

For a small reset cube based at an \(o(h)\)-minimum source, cross vertices
have weight \(O(h^2)\), so (4.2) reduces to the existing first-order balanced
cap-leakage analysis. For a macroscopic finite response cycle, the cross
vertices have order-one weight and cannot be discarded.

## 8. Exact remaining question

The multicoordinate product route closes if one can prove either:

1. a source-attached rectangle containing the stabilized response cycle with
   weighted average excess smaller than its common-response incompatibility;
   or
2. a finite decomposition of every failure of (5.3) into an already consumed
   minimum-fibre common-response handoff, support descent, or chronological
   cap-switch escape.

The response-cycle ledger alone proves neither statement. The next useful
datum is a bound on the **cross vertices of the independent clock hull**, not
another one-coordinate paid inequality.

## Sources checked

The semantic inputs are:

* `sSup_range_quittingTerminalPayoff_update_eq_pureTime` in
  `UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean`;
* the single-owner cap-Jensen comparison in
  `notes/CODEX_ADVERSARY__RESET_RIGID_ZERO_FACE_JENSEN_BARRIER.md`;
* the reviewed finite pure-clock response cycle in
  `formalized/FIN4_FINITE_PURE_CLOCK_EXACT_RESPONSE_CYCLE.md`; and
* the finite-shadow dual classification in
  `notes/CODEX_DESCENDANT__FINITE_PAID_CYCLE_EXACT_SHADOW_DUALITY.md`.

No chronology, Nash--Bellman edge, or source regeneration is claimed.

Sections 10--12 additionally use the checked adjacent-boundary,
hard-deadline-quarter, and retained-tail-return-floor packets in
formalized/, the hard full-debt timing factorization in the Paired Hull
review note, and the independently reviewed near-minimum retained-tail
timing-identity theorem.

## 9. Producer attempt and equality classification

The fixed cycle gains do not by themselves lower-bound the left side of
(4.3). At a cycle vertex, the selected target clock is cap-optimal and beats
the current clock by a fixed amount. A third clock may nevertheless be
cap-optimal at every vertex. If it is placed later in the deterministic
tie-breaking order, the selected local targets and all their strict gains are
unchanged, while the common-response incompatibility is zero. Thus strict
revision gains are not an active-face separation certificate.

The cross-vertex excess is equally independent of the displayed edge gains.
The response cycle constrains the rewards at its vertices and at the
one-coordinate neighbors used by cap comparisons. A cross vertex outside
that inspected set can carry arbitrarily large debt without changing any
selected cycle edge. Even when every cross vertex is adjacent to the cycle,
lowering a member's payoff at the cross vertex can create debt directed back
to the cycle neighbor while leaving the reverse outsider comparison
unprofitable. Hence no bound on \(\mathbb E e\) follows from the cycle gain
floor alone.

There is, however, an exact classification of the equality arm.

### Proposition 9.1: internal common responses contradict positive minimum

Assume every weight in the rectangle is positive and \(\kappa_i=0\) for
every player. Let \(s_i^*\) be a common cap-optimal pure time supplied by
(3.3). If

\[
 s_i^*\in A_i\qquad\text{for every }i,
\tag{9.1}
\]

then the pure profile \(s^*=(s_i^*)_i\) is an unrestricted exact Nash
profile. Indeed, \(s_i^*\) is cap-optimal against every opponent vertex in
the rectangle, in particular against \(s^*_{-i}\). Therefore

\[
 d_i(s^*)=0\quad\text{for every }i,
 \qquad D(s^*)=0.
\tag{9.2}
\]

This contradicts \(D_*>0\).

### Corollary 9.2: the only finite-calendar equality escape is the next date

Take the saturated calendar

\[
 A_i=H_T:=\{0,1,\ldots,T,\mathsf{Never}\}
\]

for every player. Against this rectangle, the finite response classes are

\[
 H_T\cup\{T+1\}.
\]

If every \(\kappa_i=0\) in a positive-minimum game, Proposition 9.1 implies
that at least one common cap-optimal response is \(T+1\). Thus equality does
not produce an internal exact equilibrium; it produces a literal
finite-deadline escape.

Extending the calendar to \(H_{T+1}\) does not give a finite rank. The same
argument may select \(T+2\) at the next stage. Consequently the equality arm
is the already known horizon-escape boundary, not an all-Continue plateau or
a smaller finite response cycle.

### Exact outcome of the producer attempt

For a source-attached response cycle, the multicoordinate route therefore
has the exhaustive quantitative split

\[
\begin{array}{ll}
\sum_i\kappa_i>\mathbb E e
 &\Longrightarrow D(\bar\sigma)<D_*\quad\text{(contradiction)},\\[1mm]
\sum_i\kappa_i\le\mathbb E e
 &\Longrightarrow\text{cross-vertex excess pays the cap switch};
\end{array}
\tag{9.3}
\]

and, inside the zero-incompatibility subcase,

\[
\text{internal common response}\Longrightarrow D=0,
\qquad
\text{external common response}\Longrightarrow T\mapsto T+1.
\tag{9.4}
\]

The fixed Fin4 cycle size and gain floor do not eliminate the second line of
(9.3), and the calendar extension in (9.4) is not well-founded. A genuine
producer must therefore control the debt excess of the cross vertices or
attach the next-date response to a previously accepted escape consumer.

## 10. Saturated calendars do not supply the adjacent source

The external response in Corollary 9.2 can be compared exactly with the
finite-deadline/projective boundary, but it does not fill that boundary's
missing source adapter.

### 10.1 Hard zero-tail Nash laws recover the known adjacent split

Let \(p_T\) be any Nash law of the hard timing game on

\[
 H_T=\{0,\ldots,T,\mathsf{Never}\},
\]

and let \(q_{T+1}\) be any Nash law on \(H_{T+1}\). The literal realization
of \(p_T\) has no profitable declared action in \(H_T\). Every later finite
response has the same value as the newly exposed time \(T+1\), so

\[
 d_i(p_T)=\bigl[G_i(T+1;p_T)\bigr]_+.
\tag{10.1}
\]

If a terminal gap \(\gamma>0\) is assumed, some coordinate in (10.1) is at
least \(\gamma\). The checked adjacent-deadline estimate then gives, for
**every** choice of \(q_{T+1}\),

\[
 \sum_j\operatorname{TV}
   \bigl((L_Tp_T)_j,(q_{T+1})_j\bigr)
 \ge {\gamma\over4R}.
\tag{10.2}
\]

Thus exact old and new finite timing Nash laws with one common hard tail and
a quantitative boundary gap are available. This is the already checked
negative arm of the projective criterion. It is not the small-adjacent-error
arm that produces terminal approximants.

The common-active-face output does not select \(q_{T+1}\). A response time
\(T+1\) which is optimal against every opponent vertex in \(H_T\) has not
been compared with opponent profiles which themselves put mass at \(T+1\).
Those are exactly the new collision faces of \(H_{T+1}\). Simultaneously
adjoining the displayed external responses is therefore not a Nash
extension. Re-solving the enlarged finite game may change every old marginal.

Equivalently, asking that censoring \(q_{T+1}\) return \(p_T\) is a genuine
projective-extension constraint. Neither \(\kappa_i=0\) nor the identity
(2.4) supplies it.

### 10.2 A common retained tail makes compatibility vacuous

One can instead form, for one fixed actual tail \(\tau\), the finite timing
game on \(H_T\) whose all-\(\mathsf{Never}\) outcome resumes \(\tau\). Exact
mixed Nash laws exist at every \(T\). In the positive-minimum chamber the
singleton separation has

\[
 U_i(\tau)>r_i(\{i\})qquad(i\in I).
\tag{10.3}
\]

Consequently the law in which every player chooses \(\mathsf{Never}\) is a
strict timing-game Nash equilibrium for every \(T\). These laws form an
exactly projectively compatible family with adjacent distance zero.
Nevertheless their behavioral realization is just \(\tau\), with all of
its original unrestricted tail debt.

In the maintained positive-gap source this is not merely one unhelpful
selection. For every sufficiently near-minimum source tail, the checked
joint-return floor gives positive joint Never mass to every retained-tail
timing Nash law. The reviewed one-stage contraction and conditional-tail
backward induction then force **every** such law to be pure all-Never. Thus
the identity family is the unique exact retained-tail timing-Nash family in
the regime where this adapter would be needed.

This is the precise reason the hard projective consumer cannot simply be
reused with a retained tail. In the hard game, \(\mathsf{Never}\) is a
terminal action with payoff zero. In the retained-tail game, it is an entry
action into a complete strategy profile whose internal unilateral deviations
are not controlled by finite timing Nash.

The checked retained-tail theorem gives a different, useful constraint. If
\(\mu_T\) is any exact timing Nash law before \(\tau\), then

\[
 d_i(\mu_T\star\tau)\le H_i(\mu_T)d_i(\tau).
\tag{10.4}
\]

Under the terminal gap and punishment separation, its joint return mass
\(M(\mu_T)\) is bounded below uniformly in \(T\). This preserves the literal
tail but does not select a nonidentity block, identify its equilibrium payoff
with \(U(\tau)\), make it Nash against \(B(\tau)\), or produce adjacent
projective coherence. The all-\(\mathsf{Never}\) family shows all four missing
properties are substantive.

### 10.3 Exact regression to recursive calendar selection

The normalized hard-deadline quarter-barrier table has a unique exact timing
Nash law at every deadline. Its literal unrestricted debt stays above
\(1/4\), and the newly exposed boundary participation of one active player
converges to \(1/4\). Hence its unique consecutive Nash laws remain
macroscopically incompatible, even though the same quitting table has a
uniform-equilibrium payoff constructed from non-Nash finite clocks.

This is an exact regression to the proposed recursion. There is no
equilibrium-selection ambiguity to blame: a common external next-date
response can persist at every finite calendar while the unique enlarged-game
equilibrium jumps. Therefore repeated \(T\mapsto T+1\) active-face escape is
not a coherent strategy-profile construction.

### 10.4 First finite obstruction

The first obstruction is already finite. It is one of:

1. the new simultaneous-\(T+1\) collision face prevents the old common
   responses from being mutually optimal; or
2. re-Nashification on \(H_{T+1}\) moves a positive distance from every lift
   of the selected \(H_T\) law.

In the second case the existing adjacent theorem localizes the displacement
to boundary participation or a paid response rectangle. Its retained-tail
and source-faithful consumers remain exactly the known open arms.

Nor can failure of calendar coherence force (4.3). For every actual product
rectangle at a global minimum, (4.1) gives the opposite non-strict inequality

\[
 \sum_i\kappa_i\le\mathbb E e.
\tag{10.5}
\]

Producing \(\sum_i\kappa_i>\mathbb E e\) would already be the desired
contradiction, not a consequence of an equilibrium-correspondence jump.
The saturated-calendar iteration therefore terminates at the established
adjacent-boundary/source-reprojection waist; it does not add a new consumer.

## 11. Full-debt timing Nash gives an atom, but grafting reverses the escape

The finite-deadline full-debt factorization provides a useful quantitative
refinement of Section 10. It also makes the source-reprojection obstruction
exact.

Let \(\alpha\) be a Nash law of the hard timing game on \(H_T\). Put

\[
 p_i=\alpha_i(\mathsf{Never}),\qquad
 p_{-i}=\prod_{j\ne i}p_j,\qquad P=\prod_i p_i,
\]

and write \(s_i=r_i(\{i\})\). If every unrestricted debt of the literal hard
profile is positive, then

\[
 d_i(\alpha)=p_{-i}s_i,\qquad p_i>0,\qquad s_i>0,
\tag{11.1}
\]

and, in four players,

\[
 \prod_i d_i=P^3\prod_i s_i.
\tag{11.2}
\]

The proof is exact. Every missing response after \(T\) differs from
\(\mathsf{Never}\) only when all opponents choose \(\mathsf{Never}\).
Positivity for all four coordinates forces every Never mass to be positive,
so Never lies in every restricted-Nash support and its payoff equals the
equilibrium payoff.

Consequently, if \(d_i\ge\delta>0\) and \(s_i\le R\), then

\[
 P\ge(\delta/R)^{4/3},
\qquad
 p_{-i}\ge\delta/R\quad(i\in I).
\tag{11.3}
\]

Thus a full-debt finite timing Nash law simultaneously carries four
next-date escapes and a quantitative literal all-Never atom. This is exactly
the desired hard finite-dimensional passport. The unresolved point is still
its entrance: finite timing Nash laws need not approach the selected
positive-minimum source.

There is a stronger incompatibility with the naive retained-tail repair.
Let \(\tau\) be one literal source tail satisfying

\[
 U_i(\tau)\ge s_i+\chi
\qquad(i\in I)
\tag{11.4}
\]

for some \(\chi>0\). In the timing game whose all-Never outcome resumes
\(\tau\), a newly exposed time \(T+1\) differs from the pass action by

\[
 p_{-i}\bigl(s_i-U_i(\tau)\bigr)\le-p_{-i}\chi.
\tag{11.5}
\]

Hence the hard next-date escape is not retained: it becomes strictly worse
than passing into the source tail. This sign reversal holds for every
retained-tail timing Nash law, independently of equilibrium selection.

The hard law \(\alpha\) itself also fails to remain Nash after grafting
\(\tau\), by a quantitative amount. Let \(a_{j,T}=\alpha_j(T)\). The hard
late response \(T+1\) and the declared response \(T\) differ only if no
opponent stops before \(T\) and at least one opponent stops at \(T\).
Therefore, for every \(i\),

\[
 \delta\le d_i(\alpha)
 \le2R\Pr_{\alpha_{-i}}
   (\text{opponent earliest time is }T)
 \le2R\sum_{j\ne i}a_{j,T}.
\tag{11.6}
\]

For one \(j\ne i\),

\[
 1-p_j\ge a_{j,T}\ge{\delta\over6R}.
\tag{11.7}
\]

Since hard Never is in player \(j\)'s support, replacing only that player's
finite timing law by pure pass-through into the same \(\tau_j\) has exact
gain

\[
\begin{aligned}
 &U_j(\mathsf{Pass}_{\tau_j},\alpha_{-j}\star\tau_{-j})
   -U_j(\alpha\star\tau)\\
 &\qquad=p_{-j}(1-p_j)U_j(\tau)
 \ge{\chi\delta^2\over6R^2}.
\end{aligned}
\tag{11.8}
\]

The source endpoint \(\alpha\star\tau\) returns jointly to the literal tail
with probability \(P\ge(\delta/R)^{4/3}\); the response endpoint returns with
probability \(p_{-j}\ge\delta/R\). Thus the graft produces a source-tail
attached paid **pass** edge with quantitative return, not a source-coherent
next-date escape or an adjacent timing Nash pair.

Equation (11.8) is a genuine actual behavioral gain, but it is horizontal.
The response uses the prescribed tail strategy and need not attain player
\(j\)'s unrestricted cap; no Nash--Bellman chronology or renewable rank is
claimed. Its mechanism overlaps the paid-pass arm of the checked
minimum-tail reprojection dispatch. The new point here is the exact
incompatibility:

\[
\boxed{
\begin{array}{c}
\text{hard full-debt timing Nash}\\
\Longrightarrow
\text{next-date escape + quantitative Never atom},\\
\text{literal positive-minimum tail graft}\\
\Longrightarrow
\text{the escape reverses and a paid pass seam appears}.
\end{array}}
\tag{11.9}
\]

Therefore the desired family cannot be obtained by taking a hard
full-debt timing Nash family and grafting the source tail. A successful
source-coherent construction must change the finite equilibrium together
with the continuation and control the resulting pass seam; ordinary adjacent
calendar selection does neither.

## 12. Approximate retained-tail Nash also collapses to the identity

The identity obstruction is quantitative and therefore also rules out an
approximate-Nash calendar repair.

Let \(\tau\) be an actual tail with

\[
 D(\tau)\le D_*+\zeta,\qquad
 d_i(\tau)\ge\delta>0\quad(i\in\operatorname{Fin}4).
\tag{12.1}
\]

Let \(\mu\) be a product timing law on \(H_T\) whose regret in the finite
timing game returning to \(\tau\) is at most \(\varepsilon\) in every
coordinate. Put

\[
 p_i=\mu_i(\mathsf{Never}),\qquad
 H_i=\prod_{j\ne i}p_j.
\]

Every finite-date deviation has value at most
\(U_i(\mu\star\tau)+\varepsilon\). The pure pass action has the same bound,
and replacing only the continuation after a successful pass can add at most
\(H_i d_i(\tau)\). Pure-time extremality therefore gives

\[
 d_i(\mu\star\tau)\le\varepsilon+H_i d_i(\tau).
\tag{12.2}
\]

Summing (12.2) and using global minimality of the actual graft yields

\[
\begin{aligned}
 D_*
 &\le D(\mu\star\tau)\\
 &\le4\varepsilon+D(\tau)
   -\sum_i(1-H_i)d_i(\tau).
\end{aligned}
\]

Hence

\[
 \sum_i(1-H_i)d_i(\tau)\le\zeta+4\varepsilon.
\tag{12.3}
\]

For each player \(j\), choose any \(i\ne j\). Since \(H_i\le p_j\),

\[
 \boxed{
 1-p_j\le{\zeta+4\varepsilon\over\delta}.}
\tag{12.4}
\]

Thus, as \(\zeta,\varepsilon\to0\), every marginal timing law converges in
total variation to pure Never and the joint return probability tends to one.
In particular every newly exposed boundary atom tends to zero.

Two adjacent retained-tail timing laws satisfying the same hypotheses are
therefore mutually close after lifting, but this does **not** activate the
hard-tail projective consumer. Their literal grafts converge back to
\(\tau\), and (12.2) leaves the full tail debt \(d_i(\tau)\) essentially
unchanged. Finite-game approximate Nash controls only the clock block, not
the unrestricted deviations inside the retained tail.

Consequently there is no missing equilibrium-selection trick at this
boundary:

\[
\boxed{
\begin{array}{c}
\text{source-coherent exact or approximate retained-tail timing Nash}\\
\Longrightarrow
\text{identity in the near-minimum full-debt limit},\\
\text{hard timing Nash with next-date escape}\\
\Longrightarrow
\text{loss of the source tail or the paid-pass seam of (11.8)}.
\end{array}}
\tag{12.5}
\]
