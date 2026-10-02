# Off-minimum pure-clock response cycles: temporal attack and exact boundary

Identity: SOCIAL_WEIGHT_REVIEW

Status: **ordinary mathematics; exact structural reduction and no-go; no
Fin4 consumer.** The input is the reviewed finite literal pure-clock
best-response cycle. The new conclusions below show exactly what calendar
information survives periodicity and why finite-alphabet Nashification leaves
the cycle through the all-Never boundary. They do not construct a
Nash--Bellman chronology.

## 1. Question

Let \(I=\operatorname{Fin}4\), and suppose every actual behavioral profile has
total terminal semantic debt at least \(D_*>0\). The finite pure-clock cycle
theorem supplies actual pure-clock profiles

\[
x^0\longrightarrow x^1\longrightarrow\cdots
\longrightarrow x^L=x^0,
\tag{1.1}
\]

where every arrow changes one player's entire clock to an exact unrestricted
best reply and gives that mover gain at least \(D_*/4\).

Can the retained clock calendar, positive-minimum ancestry, and exact response
closure be turned into an exact charged Nash--Bellman cycle, a payoff
near-return, or a source-reprojected block whose seam is little-oh of its
charge?

The answer obtained here is negative for every construction using only the
finite clock alphabet or the bare replacement ancestry. A genuine consumer
must use additional source-aligned continuation information.

## 2. Every strict pure-clock response changes the terminal outcome

For a pure-clock profile \(t:I\to\mathbb N\cup\{\infty\}\), let
\(\Omega(t)\) be its terminal outcome: Never if every clock is infinite, and
otherwise the coalition at the least finite clock.

Fix a player \(p\). If the opponents have no finite clock, the only response
values are

\[
r_p(\{p\})\quad\hbox{and}\quad 0.
\tag{2.1}
\]

Otherwise let \(m\) be their first finite deadline and let \(A\ne\varnothing\)
be the opponent coalition at \(m\). Every pure response has one of the three
values

\[
\begin{array}{c|c|c}
q<m & r_p(\{p\}) & \Omega=\{p\},\\
q=m & r_p(A\cup\{p\}) & \Omega=A\cup\{p\},\\
q>m\text{ or }q=\infty & r_p(A) & \Omega=A.
\end{array}
\tag{2.2}
\]

Clocks within one row of this table have identical payoff. Hence a strict
best-response change must move between different rows and therefore changes
the terminal outcome. Its whole-profile gain is exactly

\[
r_p(\Omega(t'))-r_p(\Omega(t))>0.
\tag{2.3}
\]

Consequently (1.1) projects to a finite closed walk of terminal outcomes,
with every projected edge carrying the literal strict payoff improvement of
its mover. The complete clock profile retains at most the information needed
to say which opponent coalition is revealed when a sole earliest quitter
moves later.

## 3. Positive calendar labels are irreversible

Let

\[
P(t)=\{d>0:\exists i,\ t_i=d\}
\tag{3.1}
\]

be the set of occupied positive finite deadlines. A canonical pure-clock best
reply is one of \(0\), the first finite opponent deadline, or Never.
Therefore

\[
P(F(t))\subseteq P(t).
\tag{3.2}
\]

Indeed, the only positive date inserted by a response is already occupied by
an opponent. Once a positive label disappears it can never reappear.

On a literal cycle, (3.2) around the loop forces equality at every edge:

\[
P(x^0)=P(x^1)=\cdots=P(x^{L-1}).
\tag{3.3}
\]

Thus every positive calendar level appearing on the cycle remains occupied
throughout the whole cycle. This is stronger than finiteness of the inherited
alphabet: periodicity removes all positive-label creation and deletion.

## 4. Exact calendar classification of the cycle

Assume first that no cycle vertex has a player at date zero. The positive
support cannot be empty: the all-Never profile has no strict response except
to a date-zero singleton. Let \(d\) be the least occupied positive deadline.
By (3.3), \(d\) remains occupied forever.
At every vertex its occupants are precisely the terminal coalition \(C\).

An outsider cannot gain strictly by changing one later clock to another later
clock or to Never: all such clocks have the same value \(r_p(C)\). Since date
zero is absent from the cycle, its only possible strict response is to join at
\(d\). A member of \(C\) can strictly respond only by leaving \(d\). The
sole member of \(C\) cannot leave, because that would erase the occupied label
\(d\), contrary to (3.3). Hence the entire cycle projects to

\[
C_0\mathbin\triangle\{p_0\}=C_1,
\quad\ldots,\quad
C_{L-1}\mathbin\triangle\{p_{L-1}\}=C_0,
\tag{4.1}
\]

with every \(C_k\ne\varnothing\), every edge a strict mover improvement, and
all changes occurring at one fixed earliest calendar level.

If the projected closed walk repeats a coalition before its endpoint, cut at
the first repetition. This gives a simple strict-toggle cycle. A two-edge
cycle is impossible because it would toggle the same player across one
unordered cube edge and require both opposite strict inequalities. Thus the
cycle has even length between \(4\) and \(16\) and enters the existing Fin4
strict-toggle semantic dispatch. Its accepted branches give a uniform payoff;
under a counterexample hypothesis the only remaining outputs are the
persistent-base positive-excess chamber or the empty-base polynomial
no-interior-root chamber. This is a genuine finite classification, but those
two chambers have no general consumer.

Now suppose date zero occurs on the cycle. While its quitting coalition has
at least two members, every strict edge again adds or removes exactly one
date-zero member. Date zero can disappear only when its sole owner moves to
the least positive opponent deadline or to Never, revealing the next occupied
coalition. It can reappear only when a player moves strictly before the
current positive earliest coalition, producing that player as a singleton.
Between disappearance and reappearance, the least occupied positive date is
fixed and all strict edges are same-level membership toggles as in (4.1).

Thus every pure-clock response cycle is a concatenation of:

1. strict one-member toggle walks at one fixed currently earliest date;
2. a sole-owner reveal edge from a date-zero singleton to the next positive
   coalition (or Never); and
3. a preemption edge from a positive coalition (or Never) to a date-zero
   singleton.

This classification is literal. It neither serializes the projected walk in
game time nor turns a reveal/preemption edge into a product-root Bellman edge.

## 5. The clock magnitudes carry no charge

Let \(\phi:\mathbb N\to\mathbb N\) be strictly increasing with
\(\phi(0)=0\), extended by \(\phi(\infty)=\infty\). Applying \(\phi\)
coordinatewise to every clock in a response cycle preserves:

* the terminal outcome at every vertex;
* all prescribed payoffs;
* every unrestricted pure-clock cap and debt coordinate;
* the three response categories in (2.2); and
* the literal best-response cycle after transporting the deterministic
  calendar tie-break.

Therefore all positive dates may be spaced arbitrarily far apart without
changing any displayed semantic or response-cycle datum. Absolute deadlines
in the returned cycle cannot by themselves supply root absorption charge,
source reach, or a small Bellman seam.

## 6. Bare source ancestry is nonrestrictive

For arbitrary behavioral profiles \(\sigma\) and \(\tau\) on \(m\) players,
enumerate the players and replace their complete strategies one at a time by
the corresponding strategies of \(\tau\). After at most \(m\) unilateral
replacements the profile is literally \(\tau\).

Hence the fact that the cycle has a finite unilateral-replacement ancestry
from the source imposes no semantic or chronological relation unless the
intermediate edges also retain quantitative signs, laws, reached suffixes, or
cap comparisons. The reviewed entrance does retain useful information on its
initial paid edge, but that information is historical by the time the fresh
canonical cycle is selected. The cycle vertices are not suffixes of one source
play.

This rules out using target-to-next-source equality of the horizontal cycle
as a substitute for source reprojection.

## 7. Lossless toggle exactification has zero survival

Consider one projected same-level toggle

\[
C=A\cup\{p\}\longleftrightarrow A,
\qquad A\ne\varnothing.
\tag{7.1}
\]

To reproduce the two literal endpoint rewards
\(r_p(A\cup\{p\})\) and \(r_p(A)\) at one product root without averaging
other coalition rows, every member of \(A\) must Quit surely and every player
outside \(A\cup\{p\}\) must Continue surely. The root then absorbs with
probability one regardless of \(p\)'s action. Its Bellman successor is
independent of the tail and no later cycle phase is reached.

Conversely, a product root with positive all-Continue probability cannot have
a nonempty sure host \(A\). Its Quit/Continue endpoint values average several
coalition rewards and are not the literal payoff cells which certify the
response-cycle edge. The strict inequality of the pure edge supplies no sign
for this softened comparison.

Thus a nonsingleton toggle edge has the exact dichotomy

\[
\text{literal endpoint comparison}
\Longrightarrow \text{zero survival},
\qquad
\text{positive survival}
\Longrightarrow \text{uncontrolled averaged endpoints}.
\tag{7.2}
\]

The same fact has a source-law reading. Every pure-clock vertex absorbs surely
at its first deadline. Any later layer used when a sole earliest owner is
deleted has zero prescribed joint reach; it lives in a player-deleted
counterfactual law. Full-response caps see that layer, but an actual
chronology does not. Hence the cycle's later-clock data are exactly the wrong
probability mode for a positive-survival Nash--Bellman return.

Singleton reveal/preemption edges avoid the sure-host part of (7.2), but then
only the displayed mover comparison is controlled. The three nonmover root
inequalities and the punishment-floor annotation remain absent. This proves a
literal incompatibility, not merely a missing construction detail.

## 8. Exact finite-alphabet Nashification exits at the late boundary

Let \(T\) exceed every finite deadline used by the cycle. Consider the finite
timing game whose pure actions are

\[
\{0,1,\ldots,T,\infty\}.
\tag{8.1}
\]

It has a mixed Nash law \(\mu^T\), and the standard independent stopping-law
realization is an actual behavioral profile \(\sigma^T\). Nash controls every
declared date and Never. Against opponents supported in (8.1), all finite
dates later than \(T\) have one common value, represented by \(T+1\).
Pure-time extremality therefore gives the exact identity

\[
d_i(\sigma^T)=
\left(
U_i(\sigma^T[i\leftarrow T+1])-U_i(\sigma^T)
\right)_+.
\tag{8.2}
\]

Under the positive global debt hypothesis, some right-hand side is positive.
Under a terminal exploitability witness with gap \(\gamma>0\), one is at
least \(\gamma\). Thus finite-alphabet Nashification cannot close the
pure-clock cycle: it necessarily creates a profitable first omitted late
date.

There is an exact anchor boundary. If two distinct players have zero Never
mass under \(\mu^T\), then for every deviator at least one opponent never
survives past the horizon. Every later finite action is then equivalent to
Never, so (7.2) vanishes for all players and \(\sigma^T\) is already an exact
unrestricted terminal Nash profile. Therefore, in a counterexample, every
finite timing Nash law has at most one zero Never marginal and hence at least
three positive Never marginals.

This is precisely the existing finite-deadline/projective-boundary chamber.
The response cycle supplies no compatible selection of the laws \(\mu^T\) as
\(T\) grows, so adjacent total-variation or projective consumers do not apply
automatically.

## 9. Whole-cycle leakage does not repair the typing

The exact cycle ledger gives, for each player \(j\),

\[
\sum_{k:i_k\ne j}\Delta B_j(k)=0,
\qquad
\sum_{k:i_k\ne j}\Delta U_j(k)=-G_j,
\qquad
\sum_{k:i_k\ne j}\Delta d_j(k)=G_j,
\tag{9.1}
\]

where \(G_j\) is the sum of \(j\)'s mover gains. Thus some actual horizontal
edge carries a nonmover payoff loss and some edge a nonmover debt rise of at
least \(D_*/12\). The role-swapped actual-reach theorem localizes such a
payoff externality at a reached first-disagreement row.

But the total cap holonomy is exactly zero. The payoff-table cell changes
needed to concatenate the strict mover inequalities pay the whole gain, just
as in the checked observer-switch transport no-go. Neither (9.1) nor its
actual-reach localization makes the changed row exact Nash for the three
nonmovers.

## 10. Routes tested and exact failures

The following constructions do not consume the cycle.

* **Deterministic serialization.** A sure terminal coalition at the first
  phase prevents every later phase from being reached.
* **Independent phase mixing.** Independent marginal mixtures do not realize
  a correlated mixture of cycle vertices and instead enter the finite-timing
  boundary of Section 8.
* **Small-hazard dilution of nonsingleton vertices.** Product roots generate
  singleton mass at first order and collision mass only at second order; a
  rare public activation of a sure nonsingleton coalition is unavailable.
* **Local root Nashification.** The paid mover's action can be made locally
  optimal, but the other three endpoint inequalities are uncontrolled. An
  arbitrary exact root may be all Continue and carry zero charge.
* **Cycle contraction.** Softening each edge around its own source preserves
  its mover gain to first order, but the softened endpoint is not the source
  of the next softened edge. Contracting every vertex toward one common base
  destroys the best-response inequalities and leaves precisely the known cap-
  switching curvature obstruction.
* **Finite-alphabet equilibrium.** Section 8 proves that its sole unresolved
  defect is the first omitted late date, not an internal cycle edge.

## 11. Positive-support purification does not transport reached rows

The source entrance retains two facts which must not be conflated:

* the original off-minimum profile has one paid first-disagreement row with a
  fixed positive actual-reach floor; and
* every later clock purification chooses a pure time from the positive
  marginal support of the player being purified.

The second fact does not transport the first.  Positive marginal support at a
date gives no lower bound, or even positivity, for joint reach of that date
after another player is purified.

Here is an exact four-player regression.  Fix a date \(a>0\) and
\(0<\alpha<1\).  Player \(k\)'s stopping law assigns mass \(\alpha\) to date
zero and mass \(1-\alpha\) to Never.  Player \(h\) uses the pure clock \(a\),
and the other two players use Never.  Give player \(k\) payoff zero at every
terminal coalition.  Give player \(h\) payoff \(-1\) at the singleton
\(\{h\}\), payoff zero at every coalition containing \(k\), and arbitrary
bounded values elsewhere.

Against the displayed opponents, replacing \(h\)'s clock \(a\) by Never has
gain

\[
 1-\alpha,
\tag{11.1}
\]

and its first-disagreement row at \(a\) has joint reach \(1-\alpha\).  On the
other hand, both positive-support pure components of player \(k\)'s prescribed
law have payoff zero, equal to \(k\)'s prescribed payoff.  Hence the supported
non-worse purification rule is permitted to replace \(k\)'s mixed clock by
the date-zero component.  After that one allowed replacement, joint reach of
date \(a\) and the gain in (11.1) are both exactly zero.  The clock \(a\) is
still literally present in \(h\)'s pure strategy, but only as an off-path
counterfactual.

The same example works for arbitrarily large \(a\).  Thus neither support of
a selected pure clock nor finite replacement ancestry controls the absolute
location or reached mass of the response-cycle calendar.  In particular, the
fixed reached row attached to the initial off-minimum port may be destroyed
before the canonical pure-clock response orbit is selected.  This is exactly
why the response-cycle export records that row only as historical provenance.

This regression has zero global minimum debt and therefore is not a
counterexample to Fin4 uniform-equilibrium payoff existence.  Its role is to
falsify the probability-transport implication used by the proposed splice.
A positive-minimum proof could still exploit an additional global theorem,
but no such theorem follows from positive support, the stored ancestry, or
the literal response cycle.

There is a second, independent typing break at the projective boundary.  The
finite timing Nash law \(\mu^T\) in Section 8 is selected afresh in a different
normal-form game.  It is not a vertex of the response cycle, a suffix of the
minimum source, or a member of the replacement ancestry.  Its first omitted
action \(T+1\) is deliberately outside its support.  Consequently the cycle
packet contains no quantity whose convergence can bound the seam between the
minimum source and \(\mu^T\), let alone make that seam little-oh of the omitted
late gain.  The exact hard-deadline quarter-barrier regression shows that even
unique finite timing Nash laws may retain a fixed unrestricted late gain at
every horizon while unrelated finite-clock profiles of the same game have
vanishing debt.

Therefore combining the finite response cycle with an arbitrary finite-game
Nash existence theorem does not improve the projective boundary.  A valid
improvement needs a new producer choosing the finite timing laws from the
retained source with quantitative adjacent-law or suffix control.  Support
membership and ancestry alone cannot provide it.

## 12. The fresh cycle edges already give the maximal adjacent-law loop

The newly produced cycle edges themselves do retain more than the historical
row of Section 11, but the retained datum stops exactly one type short of the
projective consumer.

Choose one horizon \(H\) strictly larger than every finite clock in the
literal cycle.  Represent each vertex \(x^k\) by its deterministic product
timing law

\[
 \nu_i^k=\delta_{x_i^k}
\]

on \(\{0,\ldots,H-1,\mathsf{Never}\}\).  Consecutive laws differ in exactly
one marginal, their behavioral realizations are literally the original
profiles, and

\[
 \nu^L=\nu^0.
\tag{12.1}
\]

If \(p=i_k\) is the mover on \(x^k\to x^{k+1}\), put
\(g_k=U_p(x^{k+1})-U_p(x^k)\).  Then \(g_k\ge D_*/4\), and the target pure
action is an exact unrestricted best response to the unchanged opponents.
For \(0\le s\le1\), interpolate only that marginal:

\[
 \nu_p^{k,s}=(1-s)\delta_{x_p^k}+s\delta_{x_p^{k+1}},
 \qquad
 \nu_j^{k,s}=\nu_j^k\quad(j\ne p).
\tag{12.2}
\]

These are actual behavioral timing laws on the same retained hard tail.  For
\(0\le s<t\le1\),

\[
 U_p(\nu^{k,t})-U_p(\nu^{k,s})=(t-s)g_k,
\qquad
 \operatorname{TV}(\nu_p^{k,s},\nu_p^{k,t})=t-s.
\tag{12.3}
\]

The exact best-response gain remaining at \(\nu^{k,s}\) is
\((1-s)g_k\).  Thus arbitrary subdivision produces a coordinate-adjacent
closed timing-law loop with literal target-to-next-source identity and zero
outer seam.  It also shows the sharp rate boundary:

\[
 \frac{\operatorname{TV}(\nu_p^{k,s},\nu_p^{k,t})}
      {U_p(\nu^{k,t})-U_p(\nu^{k,s})}
 =\frac1{g_k}\le\frac4{D_*}.
\tag{12.4}
\]

Subdivision makes both the local law displacement and local payment small at
the same linear rate; it does not make the former little-oh of the latter.

This construction is not an adjacent-*deadline Nash* source.  Every vertex
has positive debt, and the selected profitable reply belongs to the same
finite action alphabet, so no \(\nu^k\) is Nash even in this finite timing
game.  The old-Nash and new-Nash hypotheses of the checked adjacent-deadline
source are therefore absent.  Equally, (12.2) is not a Nash--Bellman edge:
only its displayed mover is optimized.

Consequently the fresh cycle solves literal law matching completely but does
not solve edge typing.  An arbitrary-accuracy exact floor-admissible payoff
shadow of this closed loop would already be enough: the off-diagonal payoff
ledger forces a fixed aggregate absorption denominator for any such shadow,
and the existing aggregate near-return compiler would yield a uniform payoff.
What is missing is precisely the producer of that exact shadow.  Replacing it
by the coordinate-adjacent loop (12.2) is invalid, while further subdivision
cannot improve the linear ratio (12.4).

## 13. Common-base contraction loses every first-order payment

There is a stronger exact obstruction to repairing the loop by contracting
all of its vertices toward one source profile.  It does not depend on which
source is chosen.

Let \(\beta_i\) be an arbitrary stopping-time law for each player and, for
\(0\leq\theta\leq1\), define

\[
 \zeta_i^{k,\theta}
  =(1-\theta)\beta_i+\theta\delta_{x_i^k}.
\tag{13.1}
\]

Every such law is behaviorally realizable by its discrete hazard sequence.
Because consecutive cycle vertices differ only in the mover \(i_k\), the
contracted vertices \(\zeta^{k,\theta}\) and
\(\zeta^{k+1,\theta}\) also differ only in that player.  Put

\[
 G_k(\theta)
 =U_{i_k}(\zeta^{k+1,\theta})
  -U_{i_k}(\zeta^{k,\theta}).
\tag{13.2}
\]

For a player \(i\), let \(L_i^\beta(s)\) be the payoff from pure stopping
time \(s\) against \(\beta_{-i}\), and define the first-order coefficient

\[
 a_k=L_{i_k}^\beta(x_{i_k}^{k+1})
       -L_{i_k}^\beta(x_{i_k}^{k}).
\tag{13.3}
\]

Payoff is multilinear in the four stopping-time laws, so

\[
 \frac{G_k(\theta)}{\theta}\longrightarrow a_k.
\tag{13.4}
\]

More quantitatively, if every terminal reward lies in \([-R,R]\), coupling
the three opponent laws with \(\beta_{-i_k}\) gives

\[
 |G_k(\theta)-\theta a_k|\leq12R\theta^2.
\tag{13.5}
\]

Indeed, each opponent marginal is within total variation \(\theta\) of its
base law.  The opponent product law is therefore within total variation at
most \(3\theta\).  The payoff of either of the mover's two pure clocks changes
by at most \(6R\theta\), and taking their difference and multiplying by the
outer mixture weight \(\theta\) proves (13.5).

The crucial cancellation is playerwise.  Since the literal cycle returns to
its initial complete clock vector and only mover edges change a coordinate,

\[
 \sum_{k:i_k=i}
   (\delta_{x_i^{k+1}}-\delta_{x_i^k})=0.
\]

Applying the one linear functional \(L_i^\beta\) gives

\[
 \boxed{\sum_{k:i_k=i}a_k=0\qquad(i\in I).}
\tag{13.6}
\]

Consequently, suppose there is a sequence \(\theta_n\downarrow0\) on which
every contracted edge remains strictly profitable.  Equation (13.4) gives
\(a_k\geq0\) for every edge.  Equation (13.6) then forces

\[
 a_k=0\qquad\text{for every }k.
\tag{13.7}
\]

All surviving payments are therefore second order:

\[
 0<G_k(\theta_n)\leq12R\theta_n^2.
\tag{13.8}
\]

On the other hand, strictness of the original edge implies that its two pure
clocks are distinct, and hence

\[
 \operatorname{TV}
   (\zeta_{i_k}^{k,\theta_n},
    \zeta_{i_k}^{k+1,\theta_n})=\theta_n.
\tag{13.9}
\]

Thus every sign-preserving common-base contraction obeys

\[
 \boxed{
 \frac{\operatorname{TV}
   (\zeta_{i_k}^{k,\theta_n},
    \zeta_{i_k}^{k+1,\theta_n})}
      {G_k(\theta_n)}
 \geq\frac1{12R\theta_n}\longrightarrow\infty .}
\tag{13.10}
\]

If some \(a_k<0\), that edge instead becomes unprofitable for every
sufficiently small \(\theta\).  These are exhaustive alternatives.

This proves more than the linear boundary (12.4).  A common-base contraction
cannot produce a replayable seam which is little-oh of its paid charge.  If
all edge signs survive, their first-order parts cancel exactly and the law
seam is asymptotically much larger than the payment.  Equivalently, a
sign-preserving contracted loop is necessarily a two-or-more-player response
curvature object.  Any positive result from this construction must consume
that curvature; it cannot obtain a chronological return merely by choosing a
better common base.

## 14. Every rowwise exact shadow pays a macroscopic seam

The fresh strict edges also exclude an exact Nash--Bellman shadow which is
rowwise close to the source clocks.  This obstruction is order one, rather
than the second-order rate obstruction of Section 13.

Fix an edge \(x^k\to x^{k+1}\), with mover \(p=i_k\) and gain

\[
 g_k\geq D_*/4.
\]

Let \(t_k\) be the first date at which the mover's two pure clocks disagree.
The two profiles agree before \(t_k\).  Strict gain implies that no opponent
stops before \(t_k\); otherwise the mover's change would not affect the
outcome.  Thus the common prefix reaches \(t_k\) with probability one, and
the whole-profile gain is exactly the mover's one-root endpoint gap at that
date.  Denote the deterministic source root by \(r^k\), its prescribed
all-Continue continuation payoff by \(w^k\), and the source and target mover
actions by \(a_k\ne a_k'\).  Then

\[
 Q_p(r^k_{-p};w^k)-C_p(r^k_{-p};w^k)
\]

has the sign selecting \(a_k'\) over \(a_k\), with absolute value \(g_k\).

Let \(y\) be another product root and \(w\) another continuation vector.  If
all rewards and continuation coordinates lie in \([-R,R]\), elementary
coupling of the three opponent Bernoulli laws gives

\[
 |\operatorname{Gap}_p(y_{-p};w)
   -\operatorname{Gap}_p(r^k_{-p};w^k)|
 \leq
 4R\sum_{j\ne p}\operatorname{TV}(y_j,r_j^k)
 +\|w-w^k\|_\infty.
\tag{14.1}
\]

The constant is intentionally nonsharp.  The Quit endpoint is an expectation
of a bounded terminal reward, and the Continue endpoint is an expectation of
bounded terminal rewards plus the all-Continue continuation coordinate.

It follows that if

\[
 4R\sum_{j\ne p}\operatorname{TV}(y_j,r_j^k)
 +\|w-w^k\|_\infty<g_k/2,
\tag{14.2}
\]

then the source action \(a_k\) is still worse than \(a_k'\) by more than
\(g_k/2\).  Hence:

* a support-\(\varepsilon\) Nash root with \(\varepsilon<g_k/2\) cannot put
  positive mass on \(a_k\); and
* an exact root satisfying (14.2) must put probability one on \(a_k'\), so

  \[
  \operatorname{TV}(y_p,r_p^k)=1.
  \tag{14.3}
  \]

Using \(g_k\ge D_*/4\), every exact shadow of the source row therefore obeys
the explicit alternative

\[
 \boxed{
 \operatorname{TV}(y_p,r_p^k)=1
 \quad\text{or}\quad
 4R\sum_{j\ne p}\operatorname{TV}(y_j,r_j^k)
 +\|w-w^k\|_\infty\ge D_*/8.}
\tag{14.4}
\]

Thus a rowwise exact shadow cannot converge to the literal source roots and
their actual continuations.  It must perform the complete horizontal mover
flip, or pay a fixed opponent/continuation seam.  Performing the mover flip
does not finish the construction: its target is the next cycle source, which
has its own fixed profitable response.  Iterating the argument pushes the
shadow away from successive deterministic vertices and into a genuinely
mixed simultaneous root.  Producing compatible Bellman values for that mixed
root is exactly the finite-timing/projective boundary, not a serialization of
the response cycle.

Equation (14.4) is an exact incompatibility theorem for any proposed shadow
that retains the cycle's source rows.  It does not exclude a nonlocal shadow
which abandons those rows and constructs a new mixed exact root; such a
construction still requires the missing source-selected continuation
adapter.

## 15. The signed semantic-seam telescope does not consume the moat

The alternative (14.4) cannot be inserted directly into the checked signed
terminal-semantic seam telescope.

There are two typing failures.

1. The full mover flip in (14.3) is a distance between product roots.  Root
   distance is not a seam between the expected semantic child of one root and
   the decoded semantic point at the next stage.
2. The second arm of (14.4) controls opponent-root distance plus one
   prescribed continuation-payoff displacement.  The signed telescope sees
   instead

   \[
    D(\text{expected child})-D(\text{decoded child}),
   \]

   so an equal cap displacement cancels the payoff displacement exactly.
   The sign of the resulting debt seam is not controlled.

The following literal Fin4 regression makes the second failure exact.  Let
all unlisted reward coordinates be zero and put

\[
 r_0(\{0\})=1,\qquad
 r_0(\{2,3\})=2,\qquad
 r_0(\{0,2,3\})=3.
\tag{15.1}
\]

All rewards of players \(1,2,3\) are zero.  Let \(P\) be the all-Never
profile.  Its semantic pair is

\[
 U(P)=(0,0,0,0),\qquad B(P)=(1,0,0,0),
\qquad d(P)=(1,0,0,0).
\tag{15.2}
\]

Let \(Q\) be the pure date-zero profile at which exactly players \(2,3\)
Quit.  Screening at date zero gives

\[
 U(Q)=(2,0,0,0),\qquad B(Q)=(3,0,0,0),
\qquad d(Q)=(1,0,0,0).
\tag{15.3}
\]

Indeed, player \(0\) obtains three by joining the pair; every other
coordinate is identically zero.  Thus the two actual semantic points are
separated by two in both the prescribed-payoff and cap coordinates of player
zero, but have exactly the same positive debt vector.

Take a length-one semantic seam chain whose expected child is the semantic
pair of \(Q\), whose decoded child is the semantic pair of \(P\), and whose
root is all Continue.  The all-Continue root is exact against \(B(Q)\), since
the singleton rewards are coordinatewise at most that cap.  It leaves the
semantic pair of \(Q\) unchanged.  Hence the stage Nash charge is zero,
survival is one, and

\[
 \operatorname{signedDebtSeam}
   =D(Q)-D(P)=0.
\tag{15.4}
\]

The telescope reads simply

\[
 1=0+1\cdot1+0.
\tag{15.5}
\]

The complete two-coordinate seam is macroscopic, but neither the signed debt
seam nor its absolute value carries any charge.  This is not a positive-gap
counterexample; its global minimum is zero.  It is an exact regression for
the proposed compiler interface.  Positive global minimality can forbid
particular endpoint pairs, but the moat (14.4) itself supplies no relation
between the missing cap coordinate and the displaced payoff coordinate.

The coercive seam theorem consequently gives only the familiar alternative

\[
 \text{exact Nash charge}
 \quad\text{or}\quad
 \text{absolute total-debt seam}
 \quad\text{or}\quad
 \text{endpoint excess}.
\]

The coordinatewise semantic seam gives only an upper bound on the absolute
total-debt seam, not a lower bound.  A large complete mismatch may therefore
contribute zero, as (15.4) does; it is not an accepted chronological charge.
To turn (14.4) into a consumer one still needs a source theorem giving the
seam a debt sign, bounding the accompanying cap displacement, or returning
the displaced semantic coordinate on one executable chain.

## 16. The genuine quadratic branch feeds the checked cap-switch chord

The response curvature in Section 13 has a precise interface with the
checked full-chord cap-switch theorem, but only when it appears at the first
possible nonlinear order.

Fix one cycle edge \(k\), write \(i=i_k\), and let \(s,t\) be its source and
target pure clocks. Against the contracted opponent profile put

\[
 H_k(\theta)
 =U_i(t,\zeta_{-i}^{k,\theta})
  -U_i(s,\zeta_{-i}^{k,\theta}).
\tag{16.1}
\]

The exact affine dependence on player \(i\)'s stopping law gives

\[
 G_k(\theta)=\theta H_k(\theta).
\tag{16.2}
\]

In the sign-preserving branch, Section 13 gives \(H_k(0)=a_k=0\). Suppose
that for a sequence \(\theta_n\downarrow0\),

\[
 \liminf_n\frac{G_k(\theta_n)}{\theta_n^2}=c>0.
\tag{16.3}
\]

For all large \(n\), \(H_k(\theta_n)\geq c\theta_n/2\). Order the three
opponents of \(i\), and move their laws one at a time from \(\beta_j\) to

\[
 (1-\theta_n)\beta_j+\theta_n\delta_{x_j^k}.
\]

The three increments of the pure-time gap telescope from \(H_k(0)=0\) to
\(H_k(\theta_n)\). Hence one fixed opponent \(j\ne i\) and one fixed
intermediate cube context, after passing to a subsequence, have a gap
increment at least

\[
 \frac{c\theta_n}{6}.
\tag{16.4}
\]

This is exactly a stopping-law mixture edge of scale \(\theta_n\) in the
input format of exists_quittingCapSwitchFullChordPaidRow. If rewards are
bounded by \(R>0\), use

\[
 \operatorname{edgeCharge}=\frac{c\theta_n}{6},
 \qquad
 \operatorname{gain}=\frac{c}{12},
 \qquad
 \operatorname{deletedFloor}=\frac{c}{24R}.
\tag{16.5}
\]

The two division-free budgets are identities:

\[
 2\theta_n\frac{c}{12}=\frac{c\theta_n}{6},
 \qquad
 4R\theta_n\frac{c}{24R}=\frac{c\theta_n}{6}.
\tag{16.6}
\]

Therefore one literal full endpoint of the selected opponent chord carries
an actual paid first-disagreement row for observer \(i\), with fixed gain at
least \(c/12\), fixed pair-deleted survival at least \(c/(24R)\), and the
checked full-opponent-survival factorization. This is not merely an analogy
with cap switching: it supplies the exact hypotheses and constants of the
checked declaration.

It still does not consume the response cycle. The intermediate cube
contexts are synthetic contractions toward \(\beta\), not suffixes of the
retained positive-minimum source. The full-chord theorem itself is static:
it explicitly does not produce a Nash--Bellman edge, minimum-fibre return, or
source reprojection. Thus (16.3) reduces the cycle to the already known
full-chord paid-row waist, rather than closing it.

There is also an exact obstruction to asserting (16.3). Fix an observer
\(i\), let all three opponents mix independently from Never toward Quit at
date zero with probability \(\theta\), and define the observer's endpoint
difference by

\[
 r_i(S\cup\{i\})-r_i(S)
 =\begin{cases}
 1,&S=I\setminus\{i\},\\
 0,&S\subsetneq I\setminus\{i\},
 \end{cases}
\tag{16.7}
\]

including value zero at the empty opponent coalition. This is realized, for
example, by taking all observer rewards without \(i\) equal to zero and only
\(r_i(I)=1\) among rewards containing \(i\). The Quit-zero versus Never gap
is then exactly

\[
 H(\theta)=\theta^3.
\tag{16.8}
\]

If the observer's own law is also moved by scale \(\theta\), the actual
horizontal gain is

\[
 G(\theta)=\theta^4.
\tag{16.9}
\]

At the full endpoint the gap is one, but every first- and second-order
opponent incidence at the Never base vanishes. Descaling any one opponent
edge at the common scale yields only a vanishing full-chord gain. This exact
payoff-table example does not by itself realize the whole positive-minimum
response cycle; it falsifies the local implication from a strict full
endpoint response to the quadratic lower bound (16.3).

The checked reset-cube orientation theorem has the same boundary. It turns
a supplied debt square above a stated threshold into a static witness switch,
but the fresh response cycle supplies no first-order debt-square lower bound.
The pure-time polynomial may begin with the three-opponent monomial (16.8).

The missing incidence theorem is therefore exact:

> From the retained positive-minimum source provenance, prove that some
> sign-preserving contracted response edge has a nonzero quadratic payment
> coefficient as in (16.3), or consume the higher-order two-/three-opponent
> incidence directly by an all-player escape, chronological return, or
> finite rank.

Without the source clause this statement is false by (16.7)--(16.9). With
the clause it remains unproved. Thus the existing cap-switch machinery
consumes the genuine quadratic geometry conditionally, while the exact
remaining obstruction is higher-order opponent incidence plus source
attachment, not unidentified "curvature."

## 17. Finite-degree exhaustion and the operational-effect boundary

There is no infinite analytic hierarchy in Fin4. For one fixed edge,
\(H_k(\theta)\) is multiaffine in the three opponent laws, hence

\[
 H_k(\theta)=c_1\theta+c_2\theta^2+c_3\theta^3
\tag{17.1}
\]

once \(H_k(0)=0\). Since \(H_k(1)=g_k\geq D_*/4\),

\[
 \max\{|c_1|,|c_2|,|c_3|\}\geq g_k/3\geq D_*/12.
\tag{17.2}
\]

If the contracted edge stays profitable cofinally as \(\theta\downarrow0\),
its first nonzero coefficient is positive. There are exactly three cases:

\[
\begin{array}{c|c|c}
\text{first nonzero term of }H_k
  &H_k(\theta)&G_k(\theta)\\ \hline
c_1&\Theta(\theta)&\Theta(\theta^2)\\
c_2&\Theta(\theta^2)&\Theta(\theta^3)\\
c_3&\Theta(\theta^3)&\Theta(\theta^4).
\end{array}
\tag{17.3}
\]

A negative first nonzero coefficient is exactly the alternative in which the
edge loses profitability under every sufficiently small common-base
contraction. Thus (17.3), together with sign loss, is exhaustive.

The quadratic-payment case is Section 16. The cubic and quartic payment
cases do **not** instantiate the checked adjacent-deadline selected-effect
dispatch. That declaration requires a
QuittingAdjacentDeadlineGapSource: two adjacent finite timing Nash laws, a
new boundary date, the old-observer passage floor, and one common
singleton-separated graft tail. The contracted response-cycle profiles are
actual stopping-law profiles, but they are not finite timing Nash laws, are
not an adjacent censor pair, and carry no selected boundary date. A large
pure-time response effect is only one coordinate of that interface; it does
not manufacture the interface.

At the generic stopping-law level, however, every degree is already captured
by the full-chord cap-switch packet. Telescope the three opponents at the
full scale \(\theta=1\), from \(\beta_{-i}\) to \(x^k_{-i}\). Since the total
gap change is \(g_k\), one fixed opponent chord has absolute gap change at
least \(g_k/3\). Apply
exists_quittingCapSwitchFullChordPaidRow at scale one with

\[
 \operatorname{edgeCharge}=g_k/3,\qquad
 \operatorname{gain}=g_k/6,\qquad
 \operatorname{deletedFloor}=g_k/(12R).
\tag{17.4}
\]

The checked budgets again hold with equality. In particular the selected
literal full endpoint carries a pure-time paid row with

\[
 \operatorname{gain}\geq D_*/24,\qquad
 \operatorname{pairDeletedFloor}\geq D_*/(48R).
\tag{17.5}
\]

This applies equally to the cubic observer gap \(H(\theta)=\theta^3\). Thus
the top-degree case does not fall outside the generic operational geometry;
it falls into its already known **large response-effect** output. What fails
is the adjacent-Nash/source adapter and the downstream consumer.

The paid row can be converted into a literal fixed-gain horizontal response.
At the selected endpoint opponents, prescribe the observer's worse row
witness, obtaining \(A\), and then replace it by the better witness,
obtaining \(B\). The cap is unchanged and

\[
 U_i(B)-U_i(A)\geq D_*/24,\qquad
 d_i(B)=d_i(A)-\bigl(U_i(B)-U_i(A)\bigr).
\tag{17.6}
\]

Replacing the observer instead by an \(\varepsilon_n\)-best response gives
\(C_n\) with

\[
 U_i(C_n)-U_i(A_n)\geq D_*/24-\varepsilon_n,
\qquad d_i(C_n)\leq\varepsilon_n.
\tag{17.7}
\]

For a source-indexed family, compactness now gives the exact familiar split.
Either \(D(A_n)-D_*\) stays uniformly positive on a subsequence, producing a
quantitative off-minimum paid port, or \(D(A_n)\to D_*\), and (17.7) supplies
the hypotheses of the generic paid-response maximal-root/reset reduction.
If the response target also returns to the minimum fibre, it enters the
existing reset/support machinery; otherwise it is again an off-minimum paid
port.

This is a complete finite-degree reduction, but not a new consumer. The
selected chord endpoint depends on the edge, the opponent order, and the
chosen intermediate hybrid context. Neither \(B_k\) nor \(C_k\) is the
source selected for edge \(k+1\). Literal closure of the original pure-clock
cycle therefore gives no closure of the extracted paid-row profiles. The
unsigned hybrid replacements from the minimum source to \(A_k\) also carry no
Nash--Bellman annotation. The large-effect output consequently reaches the
same off-minimum/reset-rigid waist, with fixed constants, but supplies no
charged return, renewable rank, or contradiction.

The exact outstanding question is not a fourth analytic degree. It is
whether positive-minimum source provenance can align one extracted hybrid
paid row with a later source, or orient the intervening cap/payoff motion
into an accepted signed semantic seam. The finite response cycle alone
does neither.

## 18. Exact remaining waist

The entirely off-minimum pure-clock response cycle contributes only a finite
static improvement walk plus one historical source port. A real consumer
must add one of the following data not present in the cycle packet:

1. one common continuation annotation making a positive subset of the
   projected edges exact Nash--Bellman roots;
2. a source retraction from a cycle vertex to the retained paid suffix with
   seam little-oh of an exact root charge; or
3. a signed theorem using the positive-minimum source law to bound the
   observer-switch/externality bill strictly below the mover gains.

Without one of these, the response cycle is a finite normal-form obstruction,
not an executable quitting chronology. The present result therefore gives a
rigorous incompatibility theorem for the two obvious exactifications but not
a proof of Fin4 uniform-equilibrium payoff existence.

## 19. Sources inspected

The response-cycle input is
formalized/FIN4_FINITE_PURE_CLOCK_EXACT_RESPONSE_CYCLE.md, based on the checked
pure-time cap-attainment and minimum-descent declarations named there.

The exact late-boundary formula and unrestricted finite-deadline consumer are
in
UniformEquilibrium/Diagnostics/Quitting/FiniteDeadlineAdjacentTotalVariation.lean
and
UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFiniteDeadlineNashEscalation.lean.

The payoff-cell observer-switch no-go is in
UniformEquilibrium/Quitting/Classification/PreemptionTransport.lean and its
terminal-gap adapter in
UniformEquilibrium/Diagnostics/Quitting/Collision/PreemptionTransport.lean.
The no-date-zero simple-cycle output is consumed or reduced by
formalized/STRICT_TOGGLE_CYCLE_SEMANTIC_DISPATCH.md.

The exact finite-timing regression used in Section 11 is
formalized/FIN4_HARD_DEADLINE_TIMING_NASH_QUARTER_BARRIER.md.

The exact-shadow denominator comparison used in Section 12 is Proposition 69
of notes/CODEX_CEDAR__PAID_ROW_REENTRY.md.  It is conditional on supplied
exact floor-admissible payoff shadows and does not construct them.

The full-chord cap-switch consumer used in Section 16 is
`exists_quittingCapSwitchFullChordPaidRow` in
UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/
TerminalSemanticCapSwitchFullChord.lean.  The reset-cube comparison is
`terminalSemanticDebt_resetCube_nearReturn_or_curvatureWithOrientation` in
UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/
TerminalSemanticStoppingLawResetCubeOrientation.lean.  Both declarations
are static and explicitly stop before a chronological consumer.

The selected operational-effect comparison in Section 17 is
quittingAdjacentDeadline_selectedBoundaryEffectGauge_ge_or_paidReverseParticipant_finFour
in UniformEquilibrium/Diagnostics/Quitting/
AdjacentDeadlineSelectedBoundaryEffectDispatch.lean. Its input includes an
adjacent finite timing Nash source and therefore is not supplied by the
pure-clock response cycle.

No external paper theorem is used.

## 20. A universal cyclic seam toll rules out aggregate response cancellation

There is a short global obstruction to the remaining idea of cancelling
several response seams while retaining exact-root charge.  It does not use
the special pure-clock geometry.

Let

\[
 z^0,\ldots,z^{L-1}
\]

be terminal-semantic carrier points, indexed cyclically, and assume

\[
 D(z^k)\ge D_*>0
 \qquad(0\le k<L).
\tag{20.1}
\]

For every phase choose a product root \(q_k\) against the actual cap
coordinate of \(z^k\).  Put

\[
 c_k=\Pr_{q_k}(\text{all Continue}),
 \qquad a_k=1-c_k,
 \qquad
 w^k=\operatorname{Prefix}(q_k,z^k).
\tag{20.2}
\]

Let \(N_k\) be the total one-row Nash defect of \(q_k\) against that cap.
The checked prefix identity gives

\[
 D(w^k)=N_k+c_kD(z^k).
\tag{20.3}
\]

Measure the proposed cyclic rebase from the prefixed phase to the next
source by

\[
 s_k=D(z^{k+1})-D(w^k),
 \qquad z^L=z^0.
\tag{20.4}
\]

Then there is an exact unweighted identity

\[
 \boxed{
 \sum_{k<L}s_k
 =\sum_{k<L}\bigl(a_kD(z^k)-N_k\bigr).}
\tag{20.5}
\]

Indeed, sum (20.4), use cyclicity to replace
\(\sum_kD(z^{k+1})\) by \(\sum_kD(z^k)\), and substitute (20.3).

In particular, if every root is exact Nash, then

\[
 \boxed{
 \sum_{k<L}s_k
 =\sum_{k<L}a_kD(z^k)
 \ge D_*\sum_{k<L}a_k.}
\tag{20.6}
\]

Thus exact vector cancellation of all payoff/cap rebase seams is impossible
as soon as one phase has positive absorption.  The obstruction is already
visible in the total-debt projection; opposite coordinate seams cannot hide
it.

There is also a metric form.  Write

\[
 e^k_U=U(z^{k+1})-U(w^k),
 \qquad
 e^k_B=B(z^{k+1})-B(w^k),
\]

and

\[
 E_k=\sum_i\bigl(|e^k_{U,i}|+|e^k_{B,i}|\bigr).
\tag{20.7}
\]

Since

\[
 s_k=\sum_i(e^k_{B,i}-e^k_{U,i}),
\]

the triangle inequality and (20.6) give

\[
 \boxed{
 \sum_{k<L}E_k\ge D_*\sum_{k<L}a_k.}
\tag{20.8}
\]

For \(I=\operatorname{Fin}4\), if the pair norm is the maximum of the eight
payoff/cap coordinate errors, then

\[
 \boxed{
 \sum_{k<L}\|z^{k+1}-w^k\|_\infty
 \ge {D_*\over8}\sum_{k<L}a_k.}
\tag{20.9}
\]

The same obstruction is stable under approximate roots.  If \(q_k\) is an
ordinary \(\eta_k\)-Nash root, then the checked coordinate-defect theorem
gives \(N_k\le |I|\eta_k\), so

\[
 \sum_{k<L}E_k
 \ge
 D_*\sum_{k<L}a_k-|I|\sum_{k<L}\eta_k.
\tag{20.10}
\]

Consequently a family with total Nash defect little-oh of total absorption
still cannot have cyclic semantic rebase error little-oh of that absorption.
This applies equally after repeating phases with arbitrary multiplicities.

The noncyclic form makes the source budget explicit.  For a chain
\(z^0,\ldots,z^L\), with \(w^k\) defined from \(z^k\) for \(k<L\), the same
calculation gives

\[
 \boxed{
 \sum_{k<L}\bigl(D(z^{k+1})-D(w^k)\bigr)
 =D(z^L)-D(z^0)
  +\sum_{k<L}\bigl(a_kD(z^k)-N_k\bigr).}
\tag{20.11}
\]

For exact roots, a chain starting at a global minimum and ending anywhere in
the carrier therefore pays at least

\[
 D_*\sum_{k<L}a_k
\tag{20.12}
\]

in signed total-debt rebase seam.  More generally, if the initial source has
excess

\[
 E_0=D(z^0)-D_*,
\]

and the final source lies in the carrier, then the lower bound is

\[
 D_*\sum_{k<L}a_k-E_0.
\tag{20.13}
\]

Thus an off-minimum source may spend its initial excess once on exact-root
absorption.  After that debt battery is exhausted, renewing further exact
charge requires a positive signed rebase seam.  This is exactly why one
finite cap-lift orbit is compatible with positive minimality while a
source-returning repetition still needs a new paid response/seam consumer.

This closes one proposed use of the finite response cycle: several
horizontal best-response seams cannot be combined around actual positive-
minimum carrier points so that their full payoff/cap error cancels while
exact-root charge survives.  To evade (20.6), a construction must do at
least one of the following:

1. replace an actual carrier cap by a new Bellman annotation;
2. pay root Nash defect at the same first order as absorption;
3. leave the positive-minimum carrier during the phase chart; or
4. avoid cyclic source rebasing altogether and terminate in a genuine
   consumer or rank drop.

The normalized-motion periodic construction follows the first route: its
periodic Bellman values are constructed afresh and need not be the semantic
pairs of the response-cycle sources.  Therefore (20.6) does not contradict
that compiler.  Conversely, it shows that source attachment cannot be added
to that compiler merely by cancelling more horizontal response edges.

Equation (20.3) is
`quittingTerminalSemanticDebtSum_prefix_eq_continueMass_mul_add_capDefect`
from
`UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/CapDebtBellmanReduction.lean`.
The estimate \(N_k\le |I|\eta_k\) is
`quittingRootTotalNashDefect_le_card_mul_of_isεQuittingRootNash` from
`UniformEquilibrium/Quitting/Root/NashDefect.lean`.  The finite-chain signed
version is organized in
`UniformEquilibrium/Quitting/Debt/Dynamic/TerminalSemanticSignedSeamTelescope.lean`;
the new point here is the cyclic source-rebase specialization (20.5) and its
direct exclusion of multi-response seam cancellation.
