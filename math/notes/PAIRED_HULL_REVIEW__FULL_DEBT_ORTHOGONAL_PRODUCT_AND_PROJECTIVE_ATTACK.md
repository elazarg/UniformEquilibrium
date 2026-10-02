# Full-debt chamber: orthogonal product and projective attack

Identity: `PAIRED_HULL_REVIEW`

Status: **Section 13 contains a new ordinary-mathematics source-row
contraction which passed one independent review and awaits the second
unrestricted-strategy export review; the downstream full-debt exits are not
consumed.**  The cap-near common-prefix construction sends the full-debt
source either to a reached redistribution edge followed by a separately
selected off-minimum paid port, or to a regenerated minimum child with strict
support drop.  The multicoordinate cap--Jensen theorem
survives independent audit.  Its application identifies an uncontrolled
rectangular-hull excess, not a contradiction.  A separate finite-deadline
calculation gives an exact four-player boundary formula and a strong
conditional projective entrance, but the supplied full-debt minimum is not
known to arise as a limit of the required finite-deadline Nash profiles.  In
fact, retaining the literal minimum tail makes every vanishing-regret finite
timing block asymptotically all Continue, uniformly in its deadline.  The
ordinary finite-horizon and discounted-equilibrium routes are already known
loops: the former loses the terminal/source condition at the exposed
deadline, while the latter lands in the hard projective analytic packet and
can retain a fixed terminal refusal price.

This route deliberately does not use response-cycle temporalization,
pure-clock deadline descent, or an assumed horizontal-to-temporal adapter.

## 1. Question and exact production comparison

Let \(I=\operatorname{Fin}4\), let \(D_*>0\) be the global minimum of total
unrestricted terminal debt, and let

\[
 z=(U,B,\mu)
\]

be the source-attached joint semantic/law point supplied in
`questions/FIN4_FULL_DEBT_CHAMBER_CONSUMER.md`, with

\[
 D(z)=D_*,\qquad d_i(z)=B_i-U_i>0\quad(i\in I),
\]

and a positive finite terminal atom.

The question's bare conditions (F1)--(F3) are a projection of the current
production theorem
`finFour_noUniformPayoff_exists_lawTightGlobalMinimumMoatTwoChamber` in
`UniformEquilibrium/Diagnostics/Quitting/FinFourLawTightCapNashStrictMinimum.lean`.
The production theorem is stronger at the carrier level: it retains the
global-minimum origin, the law-tight saturation-minimum relation, equality of
origin and selected minimum debts, the positive finite atom, and the exact
alternative

\[
 \text{full debt}\quad\lor\quad\text{reset rigid}.
\]

It is weaker only in a presentational sense concerning chronology: the theorem
itself explicitly claims no single behavioral realization or source
chronology.  Joint-carrier membership does supply a common realizing sequence,
and the question additionally grants the already developed paid-fork and
target-side reductions.  Thus the operational question has strictly more
usable inputs than the bare production theorem, but it does not impose a
stronger local full-debt geometry.

## 2. Exact-root geometry is already exhausted

At any positive global minimum, every exact product root against \(B\) is all
Continue.

Indeed, prefixing an exact root \(q\) scales every debt coordinate by its
joint Continue probability \(c(q)\):

\[
 D(T_qz)=c(q)D_*.
\]

The prefixed point remains in the terminal semantic carrier, so global
minimality gives \(D_*\leq c(q)D_*\).  Since \(D_*>0\) and
\(c(q)\leq1\), one has \(c(q)=1\), hence \(q\) is all Continue.

This is not new relative to production: it is the content of
`quittingLawTightCapNashSaturationMinimumFace_rootNash_iff_allContinue` on the
selected saturation face.  The singleton moat gives the stronger strict
one-coordinate inequalities

\[
B_i-r_i(\{i\})\geq D_*>0.
\]

There is a second, more relevant frozen-root theorem at the **prescribed**
coordinate \(U\), not merely at the cap \(B\).  The checked declaration
`minimumTerminalSemantic_exactNash_criticalFace` says that every exact product
root against \(U\) is collision free, and any player with positive singleton
root mass must carry the entire total debt:

\[
 q(\{i\})>0\quad\Longrightarrow\quad d_i=D_*.
\tag{2.1}
\]

In the full-debt chamber, every other coordinate has positive debt, so
\(d_i<D_*\) for every \(i\).  Hence no singleton root mass is possible.
Collision mass is already zero, and therefore

\[
 \boxed{
 \text{every exact product root against }U\text{ is all Continue}.}
\tag{2.2}
\]

Equivalently, this is
`minimumTerminalSemantic_exactNash_eq_allContinue_of_no_debtGate` together
with the observation that full debt excludes every debt gate.  Thus a
stationary or one-root complementarity construction cannot leave the
full-debt minimum at either displayed continuation coordinate.  Any positive
construction must genuinely vary continuation values over time.

The checked homotopy theorem
`minimumTerminalSemantic_debtHomotopy_eq_allContinue` fills the interval
between these endpoints.  For

\[
 v_t=B-t(B-U),\qquad 0\leq t<1,
\]

every exact root against \(v_t\) is all Continue; (2.2) supplies the endpoint
\(t=1\).  Hence the entire closed debt segment from cap to prescribed payoff
is a frozen complementarity corridor.  A degree continuation restricted to
this natural segment cannot generate an absorbing branch.

There is also an exact finite-block corollary.  Take any finite
Nash--Bellman word whose terminal continuation payoff is \(U\).  At its last
row, (2.2) forces all Continue, so the preceding continuation payoff is again
\(U\).  Backward induction forces every row to be all Continue.  Therefore

\[
 \boxed{
 \text{every finite exact Nash--Bellman stack over the full-debt minimum}
 \text{ is the identity stack}.}
\tag{2.3}
\]

The same statement holds for exact cap--Nash stacks over \(B\).  Consequently
an exact finite return based at the displayed minimum cannot carry charge;
one must leave the minimum continuation corridor, use approximate seams, or
pass to an infinite moving-continuation construction.

The statement is stable on an open neighborhood, uniformly in calendar
depth.  Exact-root correspondence is upper hemicontinuous in the continuation
vector because it is defined by finitely many continuous product-root
inequalities.  Since the only exact root at \(U\) is all Continue, all exact
roots at sufficiently close continuations lie in a small root neighborhood
of all Continue.  The strict inequalities

\[
 U_i-r_i(\{i\})\geq\sum_{k\ne i}d_k>0
\]

persist on a possibly smaller continuation/root neighborhood.  There every
player strictly prefers Continue, so the only exact root is literally all
Continue.  Hence there is an open neighborhood \(\mathcal O_U\) such that

\[
 v\in\mathcal O_U
 \quad\Longrightarrow\quad
 \text{the unique exact root against }v\text{ is all Continue}.
\tag{2.4}
\]

Let \(U_n\to U\).  For all sufficiently large \(n\), consider an exact finite
Nash--Bellman timing stack of **arbitrary finite length** whose terminal
continuation is \(U_n\).  Its last root is all Continue by (2.4), so its
predecessor payoff is again exactly \(U_n\).  Backward induction applies for
the entire word, regardless of its length.  Thus

\[
 \boxed{
 \text{every finite exact timing stack over a sufficiently source-near}
 \text{ prescribed tail is the identity stack}.}
\tag{2.5}
\]

Accordingly, even unbounded finite calendar length does not help while the
literal source tail is retained.  A nontrivial projective family must change
the terminal continuation away from the source-near prescribed payoff, hence
pay exactly the continuation/source seam that the hard finite-deadline route
does not control.

Therefore the all-Continue root is an isolated strict equilibrium of the
finite root game.  Ordinary equilibrium index or mod-two parity gives no
contradiction: an isolated strict pure equilibrium has the full admissible
local index, and a finite game can have it as its unique equilibrium.  The
exact rational regression in
`notes/SOCIAL_WEIGHT_REVIEW__JENSEN_FULL_DEBT_LOCAL_CLOSURE_BOUNDARY.md`
realizes unique all-Continue root geometry, all four positive debts, the
singleton moat at the displayed debt level, punishment normality, and four
actually reached best-response forks.  Its true global minimum is zero.  This
confirms that the missing pressure is global carrier comparison, not a local
root-index calculation.

## 3. Audited multicoordinate cap--Jensen identity

For each player \(j\), choose a finite alphabet \(A_j\) of pure clocks and a
law \(\pi_j\) on it.  Let \(a\in\prod_jA_j\) index the pure vertex
\(\sigma^a\), put \(w(a)=\prod_j\pi_j(a_j)\), and let \(\bar\sigma\) be the
ordinary independently mixed behavioral profile.  For player \(i\), define

\[
 \kappa_i
 =\sum_a w(a)B_i(\sigma^a)-B_i(\bar\sigma).
\]

The independently audited theorem in
`notes/CODEX_DESCENDANT__MULTICOORDINATE_CAP_JENSEN_ACTIVE_FACE.md` gives

\[
 \kappa_i
 =\inf_{s\in\overline{\mathbb N}}
   \sum_a w(a)\bigl(B_i(\sigma^a)-V_i(s,a)\bigr)\geq0,
\tag{3.1}
\]

and the exact debt identity

\[
 \boxed{
 D(\bar\sigma)=\sum_a w(a)D(\sigma^a)-\sum_i\kappa_i.}
\tag{3.2}
\]

If \(T\) exceeds every finite clock in the rectangle, every response time is
payoff-equivalent on the rectangle to one of

\[
 0,1,\ldots,T,T+1,\mathsf{Never}.
\]

Thus (3.1) is a finite minimum.  Moreover,

\[
 \kappa_i=0
\]

if and only if player \(i\) has one pure time cap-optimal at every
positive-weight vertex.

The audit is recorded in
`feedback/CODEX_DESCENDANT__MULTICOORDINATE_CAP_JENSEN_ACTIVE_FACE__BY_PAIRED_HULL_REVIEW.md`.
The displayed rational calculation was independently re-enumerated and all
fractions agree.

## 4. What global minimality says about a source rectangle

Write

\[
 e(a)=D(\sigma^a)-D_*\geq0.
\]

Because \(\bar\sigma\) is an actual product profile, (3.2) and global
minimality give exactly

\[
 \boxed{
 \sum_i\kappa_i\leq\sum_a w(a)e(a).}
\tag{4.1}
\]

This has two useful but nonclosing consequences.

### 4.1 A genuine strict-descent criterion

Any source-attached rectangle for which

\[
 \sum_i\kappa_i>\mathbb E_w e
\]

would contradict \(D_*>0\) immediately.  This is an actual behavioral product
perturbation, not a correlated phase mixture.

### 4.2 Rigidity of minimum rectangles

If every positive-weight vertex is on the minimum fibre, then every
\(\kappa_i=0\).  Hence every player has one common pure cap-optimal response
on the entire rectangle, and the independently mixed profile remains on the
minimum fibre.

This is stronger than one-coordinate cap convexity.  It still does not give a
root or terminal contradiction.  The common response can lie at the successor
of the largest finite clock.  Enlarging the clock alphabet then creates a new
largest clock.  If every alphabet contains Never, no finite pure-clock
alphabet is closed under this successor operation.  The equality arm is
therefore the projective clock boundary, not a finite active-face rank.

## 5. Why the natural full-debt rectangle is uncontrolled

At a sufficiently late actual source approximation, every debt coordinate
has a fixed positive floor.  Choose for each player a legal nearly cap-optimal
pure clock, and form the \(2^4\) meta-rectangle whose coordinate choices are
the prescribed strategy and that player's selected response.  This rectangle
is source attached and ordinary product mixing is legal.

The full-debt data control the four one-coordinate gains.  They do not control
the debts of vertices where two or more selected responses are applied.  Those
cross vertices have changed opponents for every cap problem.  Neither the
positive law atom nor the first-disagreement reach floor bounds their total
debt excess.

For a small independent response probability \(h\), one-response vertices
have weight \(O(h)\) and multiple-response vertices have weight \(O(h^2)\).
But the one-response endpoint excess may itself be order one, producing an
\(O(h)\) right side in (4.1).  Full debt supplies no \(o(h)\) estimate.  If a
one-response target lies on the minimum fibre, the problem leaves the
full-debt chamber and enters the reset-rigid/minimum-handoff side; if it is
off minimum, its excess is precisely the open paid-port quantity.

Thus the cap--Jensen theorem does not close the current waist without one new
source theorem of either form:

\[
 \mathbb E_w e=o(\textstyle\sum_i\kappa_i),
\]

or an equality-case theorem turning the common active response into a
finite, extension-compatible terminal construction.  Conditions (F1)--(F3)
imply neither statement.

### 5.1 Retaining the source tail forces every timing equilibrium to vanish

There is a tempting attempt to repair the source problem: keep one late actual
source tail \(\tau_n\), solve a finite normal-form timing game in front of that
same tail for every calendar size, and select the equilibria coherently.  In
the full-debt chamber every such retained-tail equilibrium has vanishing
absorption, uniformly over the calendar size and the equilibrium selection.

The singleton margin implies

\[
 U_i-s_i\geq D_*-d_i=\sum_{k\ne i}d_k>0.
\tag{5.1}
\]

Hence, for all sufficiently late realizing tails,

\[
 U_i(\tau_n)>s_i\qquad(i\in I).
\tag{5.2}
\]

Let \(m=\min_i d_i(z)>0\), and discard a finite prefix so that
\(d_i(\tau_n)\geq m/2\) for every \(i\).  Write

\[
 e_n=D(\tau_n)-D_*\longrightarrow0.
\]

More generally, let \(\pi_n\) be any mixed law of any finite timing game
placed before \(\tau_n\), where the timing action Never enters the literal
tail and receives its prescribed payoff.  Let \(r_{i,n}\geq0\) be player
\(i\)'s unrestricted regret **within that finite timing game**.  Put
\(S_{p,n}\) for player \(p\)'s probability of surviving the entire block, and

\[
 H_{i,n}=\prod_{p\ne i}S_{p,n}.
\]

The retained-tail cap comparison gives

\[
 d_i(\pi_n\star\tau_n)
 \leq r_{i,n}+H_{i,n}d_i(\tau_n).
\tag{5.3}
\]

Indeed, replace player \(i\) arbitrarily in the complete graft.  Use the
same within-block behavior as a timing-game deviation, but replace the
post-block best-response tail by the prescribed tail.  The two payoffs differ
only when every opponent survives the block, and conditional improvement is
at most the tail debt.  The finite timing regret bounds the prescribed-tail
version over the prescribed graft payoff, proving (5.3).  This argument uses
normal-form timing regret and does not assume sequential perfection.

The graft is an actual profile, so global minimality and (5.3) imply

\[
 D_*
 \leq D(\pi_n\star\tau_n)
 \leq D(\tau_n)-
   \sum_i(1-H_{i,n})d_i(\tau_n)+\sum_i r_{i,n}.
\]

Therefore

\[
 \sum_i(1-H_{i,n})
 \leq\frac{2(e_n+\sum_i r_{i,n})}{m}.
\tag{5.4}
\]

Let \(a_{p,n}=1-S_{p,n}\) be player \(p\)'s probability of stopping inside
the timing block.  For every \(i\ne p\),

\[
 H_{i,n}\leq S_{p,n},
 \qquad 1-H_{i,n}\geq a_{p,n}.
\]

In Fin4, summing over the three choices \(i\ne p\) and using (5.4) gives

\[
 a_{p,n}\leq\frac{2(e_n+\sum_i r_{i,n})}{3m}.
\tag{5.5}
\]

Hence the block's joint absorption satisfies

\[
 \boxed{
 1-\prod_pS_{p,n}
 \leq\sum_pa_{p,n}
 \leq\frac{8(e_n+\sum_i r_{i,n})}{3m}.
 \tag{5.6}
\]

In particular, if \(\sum_i r_{i,n}\to0\), then

\[
 \boxed{
 1-\prod_pS_{p,n}
 \longrightarrow0.}
\tag{5.7}
\]

At an attained full-debt minimum, \(e_n=0\), so every exact retained-tail
timing Nash law is literally all Never.  For the carrier source, (5.7) is the
exact approximate version: equilibrium selection and calendar length are
both irrelevant; every retained-tail approximate-Nash selection with
vanishing timing error collapses to the identity.

The all-Never laws are exactly projectively compatible across all deadlines,
and their literal behavioral graft is just \(\tau_n\), so the original
unrestricted tail debt is unchanged.  The backward induction in (2.5)
separately says that all-Never is the only sequentially exact Nash--Bellman
stack once \(n\) is sufficiently large.

Thus existence or failure of a coherent finite-calendar equilibrium selection
with one retained tail cannot force a cap--Jensen descent: every selection is
already asymptotically identity.  A useful projective theorem must change the
terminal continuation by an amount not controlled by the source excess, and
must then pay that continuation seam.  Replacing the continuation payoff by
the cap \(B(\tau_n)\) makes the all-Continue block even more stable, but
\(B(\tau_n)\) is not a jointly realizable continuation payoff.

## 6. Exact finite-deadline boundary formula

There is a second, independent calculation which isolates the projective
boundary sharply.

Fix \(H\in\mathbb N\) and consider the finite normal-form timing game in which
each player's pure clock lies in

\[
 K_H=\{0,1,\ldots,H,\mathsf{Never}\}.
\]

Let \(\alpha=\prod_i\alpha_i\) be a mixed Nash equilibrium of this finite
game.  It is an ordinary behavioral profile.  Write

\[
 p_i=\alpha_i(\mathsf{Never}),
 \qquad p_{-i}=\prod_{j\ne i}p_j,
\]

and let \(N_i\) be player \(i\)'s payoff from playing Never against
\(\alpha_{-i}\).  Let \(U_i\) be the equilibrium payoff.

### Theorem 6.1

The unrestricted terminal debt of \(\alpha\) is exactly

\[
 \boxed{
 d_i(\alpha)=
 \bigl(N_i+p_{-i}r_i(\{i\})-U_i\bigr)_+.}
\tag{6.1}
\]

If every coordinate debt is positive, then every \(p_i>0\), every singleton
reward is positive, Never belongs to every player's equilibrium support, and

\[
 \boxed{
 N_i=U_i,
 \qquad
 d_i(\alpha)=p_{-i}r_i(\{i\}).}
\tag{6.2}
\]

For four players, with \(P=\prod_ip_i\),

\[
 \prod_i d_i
 =P^3\prod_i r_i(\{i\}).
\tag{6.3}
\]

Consequently, if \(d_i\geq\delta>0\) and
\(0<r_i(\{i\})\leq M\) for every player, then the literal all-Never atom has
the uniform floor

\[
 \boxed{P\geq(\delta/M)^{4/3}.}
\tag{6.4}
\]

### Proof

Against opponents supported on \(K_H\), all finite pure response times
strictly greater than \(H\) have the same payoff.  On the event that some
opponent uses a finite clock, that opponent stops before the responder, so the
payoff equals the Never-response payoff.  On the event that every opponent
uses Never, a finite late response terminates alone and adds the singleton
reward.  Therefore

\[
 V_i(t)=N_i+p_{-i}r_i(\{i\})\qquad(t>H).
\]

Pure-time extremality says that the unrestricted cap is the maximum of the
restricted cap and this one missing response class.  Since \(\alpha\) is a
restricted mixed Nash equilibrium, its prescribed payoff equals its
restricted cap.  This proves (6.1).

If \(d_i>0\), then \(p_{-i}>0\) and \(r_i(\{i\})>0\).  If this holds for all
four players, then for every \(j\) one may choose \(i\ne j\); positivity of
\(p_{-i}\) implies \(p_j>0\).  Hence Never is in every player's equilibrium
support, so \(N_i=U_i\), proving (6.2).  Multiplying (6.2) over four players
gives (6.3), because each \(p_j\) appears in exactly three opponent products.
The quantitative bound (6.4) follows immediately.

## 7. What Theorem 6.1 would buy, and the missing entrance

Suppose one had a sequence of finite timing equilibria \(\alpha^{H_n}\) whose
full terminal semantic pairs converged to the supplied full-debt global
minimum.  Then the positive debt-support moat would make all four debts
uniformly positive.  Theorem 6.1 would give:

1. positive singleton rewards for every player;
2. a uniform positive all-Never atom;
3. exact boundary indifference \(N_i=U_i\); and
4. the exact factorization \(d_i=p_{-i}r_i(\{i\})\).

This is substantially stronger than an arbitrary paid fork.  Conditional on
the all-Never event, moving some boundary clocks to \(H_n+1\) realizes a
literal one-row product law on the selected quitting coalition.  It is the
right finite-dimensional input for a projective or complementarity attack.

However, no such entrance follows from the supplied chamber.  A global
minimum is approached by arbitrary actual profiles, not by Nash equilibria of
the finite clock games \(K_H\).  Conversely, finite-clock Nash equilibria
exist for every \(H\), but their unrestricted total debts need not approach
\(D_*\), and their semantic clusters need not equal the selected law-tight
minimum.  Selecting an unrelated finite-horizon equilibrium would lose the
source and the positive atom.

This is the exact producer gap for the projective route.

## 8. Why a finite-alphabet fixed point does not finish the argument

For fixed \(H\), the finite timing game has a mixed Nash equilibrium.  It need
not be an unrestricted terminal Nash equilibrium because the missing clock
\(H+1\) differs from Never precisely on the all-opponents-Never event.  Adding
\(H+1\) merely creates a new missing successor \(H+2\).

One can graft a product root after the all-Never outcome of a finite block.
This is an actual behavioral construction.  But the graft changes the
continuation payoff assigned to the old Never action, so the earlier finite
block need not remain Nash.  A fixed point of the finite-block Nash-payoff
correspondence would solve this, but that correspondence need not have convex
values.  Convexifying it introduces public correlation and proves at most a
sunspot-type statement, not the ordinary product-behavioral target.

Thus neither finite Nash existence nor root-game parity supplies the missing
projective compatibility.

## 9. Exact small boundary regression

The boundary mechanism already occurs in a two-player rational table.  Let

\[
 r(\{0\})=(1,2),\qquad
 r(\{1\})=(2,1),\qquad
 r(\{0,1\})=(0,0).
\]

In the restricted clock game \(K_0=\{0,\mathsf{Never}\}\), the symmetric
mixed equilibrium Quits at zero with probability (1/3) and plays Never with
probability (2/3).  Each prescribed payoff is (2/3).  The missing clock
one pays (4/3), so each unrestricted debt is (2/3), exactly as (6.2)
predicts:

\[
 (2/3)\,r_i(\{i\})=2/3.
\]

Yet the unrestricted terminal game has a pure equilibrium in which one player
Quits at zero and the other plays Never.  Thus the boundary full-debt profile
does not define a positive global minimum.  This regression confirms both the
formula and the necessity of the global/source entrance; it is not a Fin4
counterexample.

## 10. Actual finite-horizon and discounted equilibria do not restore the source

The preceding retained-tail no-go might suggest abandoning the source tail
and using equilibria of the ordinary finite-horizon or discounted games.  The
two constructions exist, but neither produces the missing full-debt entrance.

### 10.1 Hard finite horizons

For every deadline \(H\), the finite clock game with the hard all-Continue
tail has a mixed Nash equilibrium.  Its literal infinite-game realization
can fail terminal Nash only through a pure clock strictly beyond the exposed
deadline.  This is not just a qualitative observation.  The reviewed packet
`formalized/FINITE_DEADLINE_NASH_PROJECTIVE_BOUNDARY_AND_COMPATIBILITY.md`
proves that, under a positive terminal gap, **every** Nash law at deadline
\(H\) is separated by a fixed total-variation amount from **every** Nash law
at deadline \(H+1\).  That separation localizes to either a paid unilateral
edge or a paid common-response rectangle on the hard-tail profiles.

The same packet also computes the exact reprojection seam.  Grafting a tail
of payoff \(u\) behind a finite law \(P\) changes the prescribed payoff by

\[
 M(P)u,
\]

where \(M(P)\) is the joint Never mass.  A response square therefore acquires
the signed defect

\[
 -(M(A)-M(B))u_i.
\]

Finite-horizon Nash existence supplies no bound on this defect and no
identification with the supplied minimum source.  Thus the actual
finite-horizon route reaches the already formalized adjacent-deadline
incompatibility loop; full debt adds no missing source correspondence.

There is an elementary playerwise version of the same boundary.  If a hard
deadline equilibrium has terminal debt at least \(\gamma\), select \(i\) with
\(d_i\geq\gamma/4\).  Formula (6.1) and the fact that Never is an available
finite-game action imply

\[
 d_i
 \leq p_{-i}r_i(\{i\})
 \leq Mp_{-i}.
\]

Consequently

\[
 r_i(\{i\})>0,
 \qquad
 p_{-i}\geq\frac{\gamma}{4M}.
\tag{10.1}
\]

This gives a fixed three-opponent Never base and a profitable missing late
clock.  It still does not give a reached Nash--Bellman row: the deviator can
force its own survival to the missing clock, whereas the equilibrium profile
may reach that date with vanishing or zero probability.  Nor does restricted
optimality of the opponents' Never actions make them best replies to the
counterfactual sure late quitter.  These are exactly the reach and row-typing
fields needed by the AGKRS S.2/S.3 consumers.

### 10.2 Discounted stationary equilibria

The discounted route has been computed independently in
`notes/CODEX_CEDAR__DISCOUNTED_RADIAL_DEBIASING.md`.  A discounted stationary
Bellman root can be converted to its literal undiscounted stationary terminal
payoff, but the conversion changes the continuation endpoint.  The exact
unrestricted cap then acquires a pure-Never or pure-Quit refusal term.  In the
matching analytic regime this term can converge to a fixed positive number;
the four-player boundary table in that note has refusal limit \(1/12\) in
every coordinate even though the table is solved by a nonstationary
period-two profile.

Equivalently, if stationary absorption remains large relative to the discount
rate, debiasing can yield a terminal stationary consumer.  In the remaining
case hazards live on the discount scale and their normalized limit is the
projective/LCP packet.  The projective-Q-bar packet already has a checked
uniform-payoff decoder; the residual hard principal case is precisely the
case not consumed by that method.  The supplied full-debt terminal minimum is
not a discounted value and gives no equation identifying it with this
analytic packet.

Thus finite-game Nash existence leaves one exact producer gap:

\[
 \boxed{
 \begin{array}{c}
 \text{either attach the exposed boundary row to a uniformly reached}\\
 \text{literal minimum source, or control the hard-tail reprojection seam.}
 \end{array}}
\tag{10.2}
\]

Without (10.2), the now-checked AGKRS S.2/S.3 compilers have no supplied
branch object.  This is not a missing compactness theorem: hard finite laws
are compact at each deadline, and discounted analytic germs exist.  It is a
failure of undiscounted source and unrestricted-response compatibility.

## 11. Exact boundary-row reach theorem, and its sharp missing hypothesis

The finite-horizon producer can be sharpened to an exact reach statement.
Let \(p\) be a Nash law of the hard deadline-\(H\) timing game, and realize it
as the literal infinite profile with all Continue after the deadline.  Write

\[
 p_i^\infty=p_i(\mathsf{Never}),
 \qquad
 P=\prod_i p_i^\infty.
\]

Assume every unrestricted terminal debt has the common floor

\[
 d_i(p)\geq m>0.
\tag{11.1}
\]

Then the exact boundary formula (6.2) applies and gives

\[
 d_i(p)=p_{-i}^\infty r_i(\{i\}),
 \qquad
 P^3\prod_i r_i(\{i\})=\prod_i d_i(p).
\]

If \(\lvert r_i(S)\rvert\leq M\), then

\[
 \boxed{P\geq(m/M)^{4/3}.}
\tag{11.2}
\]

On the event that all four timing actions are Never, the hard profile is
literally still live at date \(H\), its displayed root there is all Continue,
and its literal continuation is the hard all-Continue tail.  Hence (11.2) is
a uniform **prescribed-source** reach floor for the first excluded boundary
row.  For each player \(i\), changing that row to sure Quit is the pure clock
\(H\), and its gain is exactly \(d_i(p)\geq m\).  Thus (11.1) co-realizes, on
one actual source profile,

* a uniformly reached boundary row;
* its literal continuation payoff;
* a fixed pure-boundary refusal gain for every player; and
* ordinary independent behavioral randomization only.

This is exactly the source object sought by the projective route.  Its proof
is elementary; the missing fact is (11.1), not any further occupation
compactness.

The supplied full-debt minimum has a floor \(m=\min_i d_i(z)>0\), but an
arbitrarily selected hard finite-horizon equilibrium is a different carrier
point.  Global minimality gives only

\[
 \sum_i d_i(p)\geq D_*,
\]

so at most one debt coordinate is forced positive.  It does not transfer the
minimum point's coordinatewise floor to \(p\).  With only one gap witness
\(i\), one still gets

\[
 p_{-i}^\infty\geq\frac{D_*}{4M},
\]

and therefore the **response** profile in which \(i\) forces the missing
clock reaches the boundary with a fixed floor.  The prescribed source reach
also contains \(p_i^\infty\), which may vanish.

This loss is exact, not a weakness of the estimate.  The checked Fin4 hard-
deadline regression in
`FinFourHardDeadlineTimingNashUniqueness.lean` has a fixed positive boundary
debt and a fixed opponent-Never base, while the prescribed probability of
reaching the last exposed date tends to zero.  Only the response profile
creates the fixed boundary collision.  That table has three zero-debt dummy
coordinates and global minimum zero, so it does not refute the desired
positive-minimum theorem.  It proves, however, that total debt, a boundary
gain, and opponent reach cannot replace the all-coordinate hypothesis
(11.1).

There is also a literal adjacent-clock causalization that does not repair the
source reach.  If \(H>0\), Nash optimality gives

\[
 V_i(H-1)\leq U_i(p),
 \qquad
 V_i(H)-U_i(p)=d_i(p),
\]

for every positive-debt coordinate.  Therefore

\[
 V_i(H)-V_i(H-1)\geq d_i(p).
\tag{11.3}
\]

The pure clocks \(H-1\) and \(H\) agree before date \(H-1\).  Their payoff
difference is supported only on the event that no opponent stops earlier and
at least one opponent stops exactly at \(H-1\); the all-opponents-Never event
pays the same solo reward at both clocks.  Thus

\[
 \Pr_{p_{-i}}
   (\min_{j\ne i}T_j=H-1)
 \geq\frac{d_i(p)}{2M}.
\tag{11.4}
\]

Equations (11.3)--(11.4) give an actual, uniformly reached first-disagreement
edge between two pure response profiles, with the literal one-row successor.
They still do not make the original equilibrium use or reach that row:
player \(i\)'s prescribed clock may stop earlier with probability tending to
one.  This is precisely the distinction between a response attachment and a
prescribed-source attachment.

Consequently the exact remaining producer is now:

\[
 \boxed{
 \begin{array}{c}
 \text{from the source-attached full-debt global minimum, select hard}\\
 \text{finite-horizon equilibria with a uniform four-coordinate debt floor,}\\
 \text{or otherwise transfer the minimum source to the response-reached row.}
 \end{array}}
\tag{11.5}
\]

The first alternative would feed (11.2) directly.  The second must add real
source ancestry; equality of payoff/law clusters or the response reach in
(11.4) is insufficient.

## 12. Current conclusion

The orthogonal attacks leave a sharper but still open fork.

* **Product geometry:** construct from the actual source a finite response
  rectangle whose common-response incompatibility exceeds its complete
  cross-vertex excess, or consume the common-active-face equality arm.
* **Projective geometry:** produce finite-clock Nash blocks converging to the
  source-attached full-debt minimum, or prove an equivalent source-faithful
  boundary-indifference packet without reselecting an unrelated equilibrium.

The full-debt chamber itself supplies neither missing producer.  The first
route is blocked by uncontrolled multi-response vertices; the second is
blocked by lack of source/minimum attachment.  These are different
manifestations of the same structural issue: individual unrestricted caps
are optimized against different opponent profiles, while ordinary behavioral
play must use one product profile.

## 13. Cap-near common-prefix responses give the missing source-row contraction

The preceding conclusion understated the strength of the stopping-law
selection argument.  The checked scratch common-prefix fork redirects the
choices losing at least one fixed fraction of the debt.  If instead one
redirects **every** stopping choice outside an arbitrarily thin cap band, one
simultaneously obtains:

* a target whose mover debt tends to zero;
* a fixed whole-profile payoff gain;
* an exact live-path common prefix with the actual source; and
* a fixed lower bound on the actual joint probability of reaching the first
  changed date.

This is an ordinary-mathematics strengthening of the selection argument.  It
is not yet a Lean declaration.

### 13.1 One-profile theorem

Let \(\sigma\) be an actual behavioral profile, fix player \(i\), and write

\[
 v(q)=U_i(\sigma[i\leftarrow q]),\qquad
 B=\sup_{q\in\mathbb N\cup\{\infty\}}v(q),\qquad
 d=B-U_i(\sigma)>0.
\tag{13.1}
\]

Here \(q\) denotes the deterministic pure stopping time, including Never.
Let \(M>0\) bound the absolute rewards.  Fix \(0<\varepsilon<d\), and choose
one receiver \(r\) with

\[
 v(r)>B-\varepsilon/2.
\tag{13.2}
\]

Let \(\nu\) be player \(i\)'s actual complete stopping law and put

\[
 A_\varepsilon=\{q:B-v(q)>\varepsilon\}.
\tag{13.3}
\]

Push \(\nu\) forward by the map which sends every member of
\(A_\varepsilon\) to \(r\) and fixes every other stopping time.  Realize the
resulting law as an ordinary behavioral strategy by copying the source's
live-path hazards strictly before the finite cut constructed below and using
the canonical hazards of the pushed residual thereafter.  Call the updated
profile \(\tau^\varepsilon\).  This splicing realizes exactly the pushed
complete stopping law.

Then

\[
 d_i(\tau^\varepsilon)\le\varepsilon,
 \qquad
 U_i(\tau^\varepsilon)-U_i(\sigma)\ge d-\varepsilon.
\tag{13.4}
\]

Indeed, every stopping time retained in the target has value at least
\(B-\varepsilon\), while the receiver has strictly larger value.  The
unrestricted cap of player \(i\) is unchanged because the opponents are
unchanged.  This proves both assertions in (13.4).

There is also a finite cut \(c_\varepsilon\) before which the source and
target have exactly the same action on the unique live all-Continue history.
This is the operational common-prefix statement relevant to a quitting game;
it does **not** assert equality of the two behavioral strategies on arbitrary
off-path histories.  To see it, first note that

\[
 d=\mathbb E_\nu(B-v)
 \le \varepsilon+2M\nu(A_\varepsilon).
\tag{13.5}
\]

Thus \(\nu(A_\varepsilon)>0\).  If a finite member of
\(A_\varepsilon\) has positive \(\nu\)-mass, let \(b\) be the earliest such
date; otherwise put \(b=\infty\).  In the latter case Never is bad with
positive mass, so the good receiver \(r\) is finite.  Hence

\[
 c_\varepsilon=\min\{b,r\}<\infty.
\tag{13.6}
\]

No positive-mass bad choice lies strictly before \(b\), and the receiver is
not strictly before \(c_\varepsilon\).  Therefore the source and pushed laws
have equal finite masses and equal survival probabilities below the cut.  The
target construction copies the source hazards there literally and realizes
the canonical pushed residual afterwards.  Hence their live actions agree at every date strictly
before \(c_\varepsilon\).  The target is still the literal one-player update
of the original profile \(\sigma\); no unrelated source profile is selected.

The distinction from full strategy equality matters only on histories after
someone has already Quit, which cannot affect a terminal outcome.  Thus the
source and target outcome laws agree up to the cut and any payoff difference
is supported on joint reach of the cut.

Their payoff difference is supported on the event that the source reaches
the cut.  Conditional payoff differences are bounded by \(2M\), so (13.4)
gives the genuine prescribed-source reach floor

\[
 d-\varepsilon
 \le 2M\Pr_\sigma(\text{all players reach }c_\varepsilon).
\tag{13.7}
\]

This includes all problematic cases: the earliest bad choice or the receiver
may be Never, but not both; unbounded and randomized source clocks are treated
through their complete stopping law; and the cap in (13.4) remains the full
behavioral cap because pure-time extremality is exact for quitting games.

### 13.2 Application to a full-debt minimum source

Return to the source sequence \(\sigma_n\to x\) in the full-debt chamber.
Fix one player \(i\) and put \(a=d_i(x)>0\).  Apply the theorem above with
\(\varepsilon_n\downarrow0\).  After discarding finitely many indices, the
literal targets \(\tau_n\) satisfy

\[
\begin{aligned}
 d_i(\tau_n)&\longrightarrow0,\\
 U_i(\tau_n)-U_i(\sigma_n)&\ge a/2,\\
 \Pr_{\sigma_n}(\text{reach the common-prefix cut }c_n)
   &\ge a/(4M).
\end{aligned}
\tag{13.8}
\]

Every \(\tau_n\) is a literal update of only player \(i\)'s complete strategy
and agrees with \(\sigma_n\) on every live history before \(c_n\).  Compactness
and global minimality now give an exhaustive strict/minimum split after one
common subsequence.

* If \(D(\tau_n)\) stays a fixed amount above \(D_*\), the literal
  redistribution edge \(\sigma_n\to\tau_n\) retains its fixed gain and fixed
  actual reach.  Separately, applying the standard actual-reach paid-row
  selector at the off-minimum target \(\tau_n\) gives the ordinary
  off-minimum paid port with ancestry from \(\sigma_n\).  The redistribution
  mover/cut and the target-side paid-row observer/date need not coincide.
* Otherwise \(D(\tau_n)\to D_*\), and every target cluster \(y\) is a global
  minimum with \(d_i(y)=0\).

In the second arm, mix only player \(i\)'s source and target stopping laws by
one fixed \(s\in(0,1)\), producing actual profiles \(H_n^s\).  Prescribed
payoffs are affine and unrestricted caps are convex along this one-player
chord.  Since both endpoints converge to the global minimum fibre,

\[
 D_*\le D(H_n^s)
 \le(1-s)D(\sigma_n)+sD(\tau_n)\longrightarrow D_*.
\tag{13.9}
\]

The coordinatewise convexity inequalities must all be equalities in the
limit.  Hence, writing \(h^s\) for the chord cluster,

\[
 d_k(h^s)=(1-s)d_k(x)+s d_k(y)\quad(k\in I).
\tag{13.10}
\]

Because \(x\) has full positive-debt support, \(h^s\) also has full support,
whereas

\[
 \varnothing\ne\operatorname{supp}^+(y)
 \subsetneq I,
 \qquad |\operatorname{supp}^+(y)|\le3.
\tag{13.11}
\]

The support is nonempty because \(D_*>0\).  The actual families
\(H_n^s,\tau_n\), their live-prefix cuts, and their literal one-player
update are all retained.  For every \(n\), choose an exact cap--Nash word of
length \(n+1\) against \(H_n^s\).  Its Continue product tends to one: exact
debt scaling and global minimality squeeze that product between
\(D_*/D(H_n^s)\) and one.  Copying the same word onto \(\tau_n\) preserves the
literal suffix response edge, and the vanishing-prefix cap estimate gives the
complete limits \(h^s\) and \(y\).

The positive finite-atom theorem at each Fin4 global minimum and the weaker
`nonempty_sourceFaithfulMinimumCausalChronology` now regenerate complete
same-residual sources at the **same exact joint-law points** \(h^s\) and
\(y\), while retaining the supplied chord family and the copied-prefix target
family.  This adapter reselects a positive date from a finite mass window; it
does not require a uniform supplied stage-mass floor.  In particular it may
be applied to the literal target profiles after the copied prefix.  A paired
ancestry wrapper therefore retains the actual edge and the complete child
source without substituting an unrelated profile family.

Thus the full-debt chamber has the source-attached contraction

\[
\boxed{
 \text{full-debt minimum source}
 \Longrightarrow
 \begin{cases}
  \text{reached redistribution edge plus an off-minimum paid port},\\
  \text{or a regenerated minimum child with strict support drop }4\to\le3.
 \end{cases}}
\tag{13.12}
\]

This does not consume the off-minimum port or the generic tangent exits after
the support child.  It does remove the source-row producer named in (11.5):
finite-horizon Nash selection is unnecessary for that purpose.  What remains
of the priority question is the downstream paid/reset waist, not attachment
of a reached response to the full-debt source.

### 13.3 Novelty and implementation boundary

`positiveDebt_exists_commonPrefix_profitableStoppingLawFork` already proves
the common-prefix/reach mechanism for a fixed badness threshold.  The new
point is to let the target tolerance tend to zero while retaining a reach
floor controlled by the **source debt**, as in (13.4)--(13.7).  The standard
approximate-response target gives vanishing mover debt but no common-prefix
cut; the fixed-threshold fork gives the cut but leaves a fixed fraction of
the mover debt.  The construction above supplies both on the same literal
target.

A Lean implementation should first generalize the bad-set map in
`FableCommonPrefixFork.lean` from the fixed threshold \(\Delta/2\) to an
arbitrary \(\varepsilon\)-cap band and export (13.4), the finite-cut equality,
and (13.7).  Its prefix field should state equality of the source and target
hazards on the unique live history; the existing theorem's stronger equality
between two *canonical reconstructions* must not be misread as equality with
an arbitrary source strategy on off-path histories.  The carrier chord and
coordinatewise equality should reuse the existing minimum-response-chord
geometry.  The implementation should select exact cap--Nash words directly
on the supplied chord profiles and prove their Continue products tend to one
by the minimum squeeze.  It must not invoke the stronger marked-atom
`nonempty_sourceFaithfulMinimumCausalization` without a uniform stage-mass
hypothesis.  Instead it should use
`nonempty_sourceFaithfulMinimumCausalChronology`, which selects its own finite
window and mark while keeping the supplied profiles, and package that object
into the regenerated atom as in
`CanonicalPairFullReplacementSourceRegeneration.lean`.  No finite-horizon
Nash law, stationary restriction, or bounded response class enters.

In the strict arm the implementation must expose the private mathematical
constructor currently used inside
`offMinimumAncestry_exists_actualReachPaidPort`, or restate its elementary
average-debt/actual-reach proof for the supplied target.  It must not identify
that selected target-side row with the source redistribution edge.

## Sources inspected

* `questions/FIN4_FULL_DEBT_CHAMBER_CONSUMER.md`;
* `finFour_noUniformPayoff_exists_lawTightGlobalMinimumMoatTwoChamber` in
  `UniformEquilibrium/Diagnostics/Quitting/FinFourLawTightCapNashStrictMinimum.lean`;
* `quittingLawTightCapNashSaturationMinimumFace_rootNash_iff_allContinue` in
  `UniformEquilibrium/Diagnostics/Quitting/LawTightCapNashMinimumFace.lean`;
* `minimumTerminalSemantic_singletonMargin` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticAuxiliaryNashBudget.lean`;
* `minimumTerminalSemantic_exactNash_criticalFace` in the same file, and
  `minimumTerminalSemantic_debtHomotopy_eq_allContinue` plus
  `minimumTerminalSemantic_exactNash_eq_allContinue_of_no_debtGate` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticMinimumDebtSimplex.lean`;
* `sSup_range_quittingTerminalPayoff_update_eq_pureTime` in
  `UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean`;
* `notes/CODEX_DESCENDANT__MULTICOORDINATE_CAP_JENSEN_ACTIVE_FACE.md` and its
  independent review; and
* the exact local regression in
  `notes/SOCIAL_WEIGHT_REVIEW__JENSEN_FULL_DEBT_LOCAL_CLOSURE_BOUNDARY.md`;
* `formalized/FINITE_DEADLINE_NASH_PROJECTIVE_BOUNDARY_AND_COMPATIBILITY.md`;
* `FiniteDeadlineAdjacentTotalVariation.lean`,
  `AdjacentDeadlineGapSource.lean`, and the exact regression in
  `FinFourHardDeadlineTimingNashUniqueness.lean` under
  `UniformEquilibrium/Diagnostics/Quitting/`;
* `formalized/AGKRS_FORWARD_TRICHOTOMY_BY_REFUSAL_COMPACTIFICATION.md` and
  `formalized/NORMAL_S3_DELAYED_SWITCH_UNIFORM_PAYOFF.md`; and
* `notes/CODEX_CEDAR__DISCOUNTED_RADIAL_DEBIASING.md`;
* `positiveDebt_exists_commonPrefix_profitableStoppingLawFork` in
  `fable/lean/FableCommonPrefixFork.lean`;
* `minimumRealizingSequence_exists_offMinimumActualReachPaidPort` in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/ArbitraryClockMinimumActualReachPaidPort.lean`;
* the minimum-response chord and source-regeneration declarations summarized
  in `docs/TOOLKIT.md`; and
* the common prescribed-prefix response edge in
  `notes/SOCIAL_WEIGHT_REVIEW__COMMON_PRESCRIBED_PREFIX_BACKWARD_EDGE.md`.
