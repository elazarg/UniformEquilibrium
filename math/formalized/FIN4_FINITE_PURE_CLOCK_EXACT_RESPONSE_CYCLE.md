# Fin4 positive debt forces a finite literal pure-clock best-response cycle

Authors: `PAIRED_HULL_REVIEW`

Independent reviews:
[Social Weight Review](../feedback/PAIRED_HULL_REVIEW__FINITE_PURE_CLOCK_EXACT_RESPONSE_CYCLE__BY_SOCIAL_WEIGHT_REVIEW.md),
[Codex Descendant](../feedback/PAIRED_HULL_REVIEW__FINITE_PURE_CLOCK_EXACT_RESPONSE_CYCLE__BY_CODEX_DESCENDANT.md)

## Exact statement

Let \(I=\operatorname{Fin}4\), and let

\[
r:\{S\subseteq I:S\ne\varnothing\}\longrightarrow\mathbb R^I
\]

be a finite quitting-game reward table. For an actual behavioral profile
\(\sigma\), let

\[
U_i(\sigma)
\]

be its terminal payoff, and let

\[
B_i(\sigma)=\sup_{\tau_i}U_i(\tau_i,\sigma_{-i})
\]

be its cap, where the supremum is over every complete unilateral behavioral
strategy of player \(i\), including randomized unbounded stopping and Never.
Put

\[
d_i(\sigma)=B_i(\sigma)-U_i(\sigma),
\qquad
D(\sigma)=\sum_{i\in I}d_i(\sigma).
\]

Assume that

\[
D(\sigma)\ge D_*>0
\tag{1}
\]

for every actual behavioral profile. Equivalently for the intended adapter,
\(D_*\) is the positive global minimum of the closed terminal-semantic
carrier.

A pure-clock profile is a vector

\[
t:I\longrightarrow\overline{\mathbb N}
:=\mathbb N\cup\{\infty\}.
\]

At every live date before \(t_i<\infty\), player \(i\) Continues; at date
\(t_i\), it Quits surely. The value \(t_i=\infty\) means Never.

### Theorem A: finite inherited response alphabet

For every pure-clock profile \(t\) and player \(i\), the unrestricted
behavioral cap is attained by a pure clock belonging to the following menu.

1. If no opponent has a finite deadline, the menu is

   \[
   \{0,\infty\}.
   \]

2. If the earliest finite opponent deadline is \(m_i=0\), the menu is

   \[
   \{0,\infty\}.
   \]

3. If the earliest finite opponent deadline is \(m_i>0\), the menu is

   \[
   \{0,m_i,\infty\}.
   \]

Fix an initial pure-clock profile \(t^0\), and define

\[
\Lambda(t^0)
=\{0,\infty\}\cup
\{t_i^0:i\in I, t_i^0<\infty\}.
\tag{2}
\]

If every coordinate of \(t\) belongs to \(\Lambda(t^0)\), one can choose an
exact unrestricted best reply to \(t\) which also belongs to
\(\Lambda(t^0)\). In Fin4,

\[
|\Lambda(t^0)|\le6.
\tag{3}
\]

### Theorem B: deterministic exact-response orbit and literal cycle

Choose fixed total orders on the four players and on the finite alphabet
\(\Lambda(t^0)\). For \(t\in\Lambda(t^0)^I\), let \(i(t)\) be the least
player maximizing \(d_i(t)\). Among the exact cap-attaining clocks in Theorem
A, let \(q(t)\) be the least, and define

\[
F(t)=t[i(t)\leftarrow q(t)].
\tag{4}
\]

Then

\[
U_{i(t)}(F(t))-U_{i(t)}(t)
=d_{i(t)}(t)
\ge \frac{D_*}{4},
\tag{5}
\]

and

\[
d_{i(t)}(F(t))=0.
\tag{6}
\]

In particular \(F(t)\ne t\). The orbit \(t^{n+1}=F(t^n)\) remains in the
finite set \(\Lambda(t^0)^I\). Therefore among

\[
t^0,t^1,\ldots,t^{1296}
\]

two states agree. There are integers

\[
0\le a<b\le1296
\]

such that

\[
t^a=t^b
\tag{7}
\]

literally as vectors of stopping times, and the segment

\[
t^a\longrightarrow t^{a+1}\longrightarrow\cdots
\longrightarrow t^{b}=t^a
\tag{8}
\]

is a nontrivial cycle. Every edge is a literal one-player replacement by an
exact best response over the full behavioral strategy class, every mover
gains at least \(D_*/4\), and every target has zero debt in its mover
coordinate. Since \(|\Lambda(t^0)|\le 6\), both the first repetition and the
cycle length are bounded by \(6^4=1296\); the cycle length is at least two.

More generally, for a nonempty finite player set of cardinality \(m\), the
same argument gives gain \(D_*/m\), alphabet size at most \(m+2\), and orbit
bound \((m+2)^m\).

### Theorem C: minimum hit or entirely off-minimum cycle

Suppose \(D(t^0)>D_*\). Before the first repeated state, exactly one of the
following occurs.

1. There is a least \(n>0\), necessarily \(n\le1296\), such that

   \[
   D(t^n)=D_*.
   \tag{9}
   \]

   Then

   \[
   t^0\longrightarrow t^1\longrightarrow\cdots\longrightarrow t^n
   \tag{10}
   \]

   is a literal finite exact-best-response path to an actual pure-clock
   global minimum. Its last mover has debt zero at that minimum. By the
   minimality of \(n\), the last edge is an off-minimum-to-minimum exact
   response.

2. No orbit state before the first repetition lies on the minimum fibre. The
   cycle (8) then consists entirely of profiles satisfying

   \[
   D(t^k)>D_*.
   \tag{11}
   \]

In both alternatives every response edge has a literal pure-time
first-disagreement row with whole-profile payoff gain at least \(D_*/4\).

### Theorem D: exact externality ledger on the literal cycle

Write the cycle as

\[
x^0,x^1,\ldots,x^L=x^0,
\]

let \(i_k\) be the mover on \(x^k\to x^{k+1}\), and put

\[
g_k=U_{i_k}(x^{k+1})-U_{i_k}(x^k)
=d_{i_k}(x^k)\ge \frac{D_*}{4}.
\tag{12}
\]

For each player \(j\), define

\[
G_j=\sum_{k:i_k=j}g_k.
\]

Then the literal return gives the three exact identities

\[
\sum_{k:i_k\ne j}
 \bigl(B_j(x^{k+1})-B_j(x^k)\bigr)=0,
\tag{13}
\]

\[
\sum_{k:i_k\ne j}
 \bigl(U_j(x^{k+1})-U_j(x^k)\bigr)=-G_j,
\tag{14}
\]

and

\[
\sum_{k:i_k\ne j}
 \bigl(d_j(x^{k+1})-d_j(x^k)\bigr)=G_j.
\tag{15}
\]

Consequently, among the \(3L\) nonmover edge-coordinates there is an edge
and a nonmover whose prescribed payoff falls by at least \(D_*/12\), and
there is, possibly on another edge and for another nonmover, a debt increase
of at least \(D_*/12\). Aggregate nonmover cap displacement cancels exactly.

### Theorem E: source-faithful entrance from arbitrary minimum clocks

Let \(z_*\) be a positive global-minimum terminal-semantic point, and let
\((\sigma_n)\) be any retained sequence of actual behavioral profiles with

\[
\operatorname{Sem}(\sigma_n)\longrightarrow z_*.
\tag{16}
\]

The reviewed arbitrary-clock purification theorem supplies one retained
\(\sigma_N\), an actual off-minimum descendant \(\tau\), and a finite literal
unilateral replacement ancestry

\[
\sigma_N\leadsto\tau,
\qquad
D(\tau)>D_*.
\tag{17}
\]

The strict branch of that theorem need not make every strategy in \(\tau\)
pure. Purify each still-mixed player once by selecting a positive-support pure
clock whose payoff is at least that player's current prescribed payoff. After
at most four further literal replacements, obtain a pure-clock profile
\(\xi\).

- If \(D(\xi)>D_*\), set \(t^0=\xi\).
- If \(D(\xi)=D_*\), apply the checked pure-time minimum descent theorem to
  obtain a pure-clock descendant \(t^0\) satisfying \(D(t^0)>D_*\).

Applying Theorem C to this \(t^0\) gives a literal minimum hit or a literal
off-minimum exact-response cycle. Every displayed profile has finite
replacement ancestry from the same retained source profile \(\sigma_N\).
No carrier realizer, minimum point, or unrelated chronology is reselected.

The paid first-disagreement row originally attached to \(\tau\) remains
historical provenance. The cycle itself uses fresh canonical exact pure-clock
best replies and has the stronger per-edge gain floor \(D_*/4\).

## Conjecture-facing change

The maintained obligation
[`FIN4_ACTUAL_PAID_CAP_DESCENT_OR_INERT_STALL`](../questions/FIN4_ACTUAL_PAID_CAP_DESCENT_OR_INERT_STALL.md)
starts from a source-attached actual off-minimum paid port. Before this result,
that waist had no finite literal returned object with target-to-next-source
identity.

Theorems A--E give the strict source-faithful reduction

\[
\text{positive minimum source}
\longrightarrow
\text{actual off-minimum descendant}
\longrightarrow
\begin{cases}
\text{literal exact-response path to a pure minimum},\\
\text{literal entirely off-minimum exact-response cycle}.
\end{cases}
\tag{18}
\]

The clock alphabet, response selector, gain, target zero, source ancestry,
and return equality are all literal finite data. Thus arbitrary off-minimum
clock behavior is no longer needed as a separate strategy-revision residual.
Moreover, an off-minimum cycle cannot be semantically featureless: Theorem D
extracts a fixed nonmover payoff fall and a fixed nonmover debt rise of size
\(D_*/12\), while proving exact cancellation of aggregate cross-cap motion.
The open waist is therefore reduced to a bounded literal response cycle with
an explicit fixed-size prescribed-payoff externality, rather than an
unstructured off-minimum port.

This does not by itself close the obligation. The finite cycle is horizontal
best-response dynamics, not an in-game Nash--Bellman chronology. The remaining
bridge is exactly one of:

1. convert the cycle to an exact punishment-floor Nash--Bellman return;
2. give the minimum-hit branch a renewable finite rank; or
3. consume an entirely off-minimum literal pure-clock response cycle.

## Definitions and assumptions

Before absorption, the only public history at date \(n\) is that every player
Continued at all earlier dates. A behavioral strategy may use independent
private randomization at every such history. It induces a probability law on
\(\mathbb N\cup\{\infty\}\), its first Quit time; conversely every such law
is represented by behavioral hazards.

Against fixed opponents, terminal payoff is affine in this stopping-time law.
Therefore the unrestricted behavioral cap is the supremum over deterministic
pure stopping times. Theorem A proves more: against pure-clock opponents the
supremum is a maximum of at most three displayed values. No finite-horizon,
stationary-deviation, bounded-memory, or bounded-clock restriction is made.

Players' randomizations in the quitting game remain independent. The theorem
does not introduce public correlation. The response orbit is an external
sequence of actual profiles obtained by literal unilateral replacements; it
is not asserted to be a sequence of dates within one play of the game.

The assumption \(D_*>0\) is used at every orbit state, not only at the source:
global minimality gives \(D(t)\ge D_*\), and nonnegativity of the four debt
coordinates gives \(\max_i d_i(t)\ge D_*/4\).

## Source correspondence

The existing checked and reviewed inputs are:

- `quittingContinuationBestResponseValue_pureTimeProfile_eq_max_two_at_zero`
  and `exists_quittingPureTime_capAttainer` in
  `UniformEquilibrium/Diagnostics/Quitting/PureTimeCapAttainment.lean`, and
  `quittingContinuationBestResponseValue_pureTimeProfile_eq_max_three` in
  `UniformEquilibrium/Diagnostics/Quitting/PureTimeScreenedMenu.lean`;
- `pureTimeMinimum_exists_offMinimum` and its deadline-rank proof in
  `UniformEquilibrium/Diagnostics/Quitting/PureTimeMinimumDescent.lean`;
- `pureTimeMinimum_exists_offMinimumPaidPort` in
  `UniformEquilibrium/Diagnostics/Quitting/PureTimeMinimumPaidPort.lean`; and
- the arbitrary-clock source adapter in
  [`ARBITRARY_CLOCK_MINIMUM_PURIFICATION_TO_OFF_MINIMUM_PAID_PORT.md`](../formalized/ARBITRARY_CLOCK_MINIMUM_PURIFICATION_TO_OFF_MINIMUM_PAID_PORT.md).

The exact downstream types audited are:

- `QuittingPunishmentFloorAdmissibleEdge` and
  `quittingPunishmentFloorAdmissibleChargedRelation` in
  `UniformEquilibrium/Quitting/Bellman/Finite/PunishmentFloorAdmissibleChargedRelation.lean`;
- `QuittingPositiveAdmissibleReturn` in
  `UniformEquilibrium/Diagnostics/Quitting/UniformExistenceBoundary.lean`; and
- `QuittingPositiveAdmissiblePayoffClosure` in
  `UniformEquilibrium/Diagnostics/Quitting/PaidFirstDisagreementPayoffNearReturn.lean`.

The new mathematics is the finite inherited-alphabet closure, deterministic
full-best-response orbit, explicit Fin4 repeat bound, literal cycle, exact
gain/zero and externality-ledger identities, minimum-hit split, and
source-faithful composition with arbitrary-clock purification.

A narrow search found finite pure-time cap attainment and finite reset-arrival
paths, but no declaration or reviewed packet constructing this literal closed
full-best-response orbit. The same-stage static toggle-cycle modules do not
contain the complete clock profiles, exact unrestricted cap attainment at
every vertex, or target-to-next-source equality established here.

No external paper theorem is used.

## Proof

### 1. Pure-clock cap calculation

Fix a pure-clock profile \(t\) and a player \(i\).

If every opponent uses Never, a finite pure response by \(i\) terminates alone
and gives \(r_i(\{i\})\), while Never gives zero. Hence

\[
B_i(t)=\max\{r_i(\{i\}),0\}.
\tag{19}
\]

Otherwise let \(m_i\) be the first finite opponent deadline and let

\[
A_i=\{j\ne i:t_j=m_i\}.
\]

This coalition is nonempty. A pure response \(q\) has exactly one of three
payoffs:

\[
\begin{array}{c|c}
q<m_i&r_i(\{i\}),\\
q=m_i&r_i(A_i\cup\{i\}),\\
q>m_i\text{ or }q=\infty&r_i(A_i).
\end{array}
\tag{20}
\]

The first case exists precisely when \(m_i>0\), and \(q=0\) represents it.
The second is represented by \(q=m_i\), and Never represents the third.
Every randomized behavioral response averages these deterministic values, so
its payoff is at most their finite maximum. A displayed pure response attains
that maximum. This proves Theorem A.

If all current deadlines belong to \(\Lambda(t^0)\), the only possibly new
finite menu entry is \(m_i\), which is itself one of the current opponents'
deadlines. Thus it already lies in \(\Lambda(t^0)\). The entries \(0\) and
\(\infty\) were inserted by definition. This proves closure.

There are at most four distinct finite values among the four initial clocks.
Adding \(0\) and \(\infty\) gives (3); duplicates only improve the bound.

### 2. Gain, target debt, and finite recurrence

Every debt coordinate is nonnegative because the prescribed strategy is an
available unilateral response. From (1),

\[
\max_i d_i(t)\ge\frac14\sum_i d_i(t)
=\frac{D(t)}4\ge\frac{D_*}{4}.
\tag{21}
\]

Let \(i=i(t)\) and \(q=q(t)\). Theorem A says

\[
U_i(t[i\leftarrow q])=B_i(t).
\tag{22}
\]

Changing only player \(i\)'s own strategy leaves its opponent profile, and
hence its unrestricted cap, exactly unchanged:

\[
B_i(t[i\leftarrow q])=B_i(t).
\tag{23}
\]

Subtracting the source payoff from (22) proves (5); combining (22)--(23)
proves (6). The gain is positive, so the successor is not the source.

The deterministic tie-breaking makes \(F\) a function on a set of at most

\[
6^4=1296
\]

states. Pigeonhole applied to its first \(1297\) orbit states gives
\(a<b\le1296\) with (7). Choose the earliest repeated state. Determinism makes
the segment close, and absence of fixed points makes its length at least two.
This proves Theorem B and the stated bounds.

### 3. Minimum hit versus off-minimum cycle

Start with \(D(t^0)>D_*\). If an orbit state on the finite transient and first
cycle lies on the minimum fibre, choose its least positive index \(n\). Every
preceding arrow has the exact properties from Theorem B, and the last mover
has zero target debt by (6), proving alternative 1 of Theorem C.

If no such state exists before the first repetition, none exists later:
determinism repeats the same cycle forever. Every cycle state is an actual
profile, so its debt is at least \(D_*\); failure of equality makes it strictly
larger. This proves alternative 2.

For one response edge, the source and target clocks of its mover are distinct.
The exact pure-time payoff difference is at least \(D_*/4\). The checked
first-disagreement localization, or its elementary stopping-time proof,
selects their first differing date and retains the same actual opponents and
the full gain. This supplies the claimed paid row.

### 4. Exact cycle ledger

Fix a player \(j\). On every edge moved by \(j\), its opponents are
unchanged. Hence its cap is unchanged, while its prescribed payoff rises by
the mover gain \(g_k\). Since the initial and final profiles of the cycle are
literally equal, both \(B_j\) and \(U_j\) telescope to zero around the whole
cycle. Removing the \(j\)-moved edges gives (13) and (14). Subtracting (14)
from (13) gives (15).

Now sum (14) and (15) over \(j\). Every edge has exactly three nonmovers, so
there are \(3L\) signed nonmover coordinate changes. Moreover,

\[
\sum_jG_j=\sum_{k=0}^{L-1}g_k\ge \frac{LD_*}{4}.
\tag{24}
\]

Thus the average nonmover debt change is at least \(D_*/12\), while the
average nonmover payoff change is at most \(-D_*/12\). One term realizes each
corresponding one-sided bound. They need not be the same term. Equation (13)
also shows that the cycle has no aggregate cap holonomy: the positive debt
leakage is paid by negative prescribed-payoff externality.

### 5. Source-faithful arbitrary-clock adapter

Apply the reviewed arbitrary-clock purification theorem to (16). It chooses
one actual source rank and only literal unilateral replacements, producing
(17). At a current profile and for one still-mixed player, disintegrate that
player's stopping law into pure clocks. Its prescribed payoff is the average
of the pure-clock response payoffs. Some positive-support pure clock has value
at least the average. Replacing the player by that clock is literal and leaves
that player's cap unchanged. Repeating for the four players yields \(\xi\).
No assertion about nonmover caps or about preservation of \(D(\tau)>D_*\) is
used.

Global minimality gives \(D(\xi)\ge D_*\). In the strict case, take \(t^0=\xi\).
In the equality case, the checked theorem
`pureTimeMinimum_exists_offMinimum` starts from the literal pure-clock vector
\(\xi\), performs a finite pure-time replacement ancestry, and returns a
literal pure-clock descendant \(t^0\) with \(D(t^0)>D_*\). Concatenating the
three finite ancestries proves Theorem E.

### 6. Exact audit of the near-return mismatch

A cycle edge proved here has type

\[
\text{actual profile}
\xrightarrow{\text{one complete-strategy best response}}
\text{actual profile}.
\tag{25}
\]

A `QuittingPunishmentFloorAdmissibleEdge` has different data. It stores a
product root \(x\), a tail payoff \(u\), and a current payoff \(v\) satisfying

\[
v=F_x(u),
\tag{26}
\]

with \(x\) exact root Nash against \(u\). Its charge is the root's one-stage
absorption probability, and both boxed states obey the behavioral punishment
floor. A relation path is a finite exact temporal Nash--Bellman block.

Equation (25) supplies none of (26), exact root Nash, absorption charge, or
punishment-floor annotations. A complete-response payoff gain is not an
absorption probability. A paid first-disagreement row is not automatically an
exact root. Finally, consecutive external strategy revisions are not
consecutive live dates in one play of the quitting game.

Therefore the literal equality \(t^a=t^b\) cannot be passed to
`QuittingPositiveAdmissibleReturn`. The payoff-closure consumer weakens only
the endpoint return condition; it still requires a path in
`quittingPunishmentFloorAdmissibleChargedRelation`. This proves the exact
noncomposition asserted in the conjecture-facing section.

## Boundary tests

### Date zero and all Never

When the first opponent deadline is zero, an earlier singleton response is
unavailable. Formula (20) correctly leaves only joining at zero and passing
by Never. When every opponent uses Never, every finite response is the same
singleton outcome, and (19) correctly includes Never's zero payoff. These are
the two boundaries at which an informal relative-order argument most often
adds a nonexistent action or omits Never.

### Positivity is essential

If \(D_*=0\), the selected maximal debt may be zero, the chosen cap attainer
may be the prescribed clock, and \(F\) may have a fixed point. The nontrivial
cycle and positive gain conclusions correctly require \(D_*>0\).

### A literal exact-response cycle can coexist with an exact equilibrium

The following Fin4 reward table falsifies any attempt to feed a horizontal
response cycle directly into the uniform-payoff consumer.

For coalitions contained in \(\{0,1\}\), set

\[
\begin{array}{c|ccc}
S&\{0\}&\{1\}&\{0,1\}\\ \hline
r_0(S)&1&1&0\\
r_1(S)&0&-1&1,
\end{array}
\tag{27}
\]

and set the coordinates of players \(2,3\) to zero. For every coalition
containing player \(2\) or player \(3\), set the entire reward vector to zero.

With players \(2,3\) always using Never, the pure-clock profiles

\[
(\infty,\infty,\infty,\infty)
\to(0,\infty,\infty,\infty)
\to(0,0,\infty,\infty)
\to(\infty,0,\infty,\infty)
\to(\infty,\infty,\infty,\infty)
\tag{28}
\]

form a literal exact unrestricted-best-response cycle. The movers are
\(0,1,0,1\), and every gain is exactly one. At each source the displayed
response attains the full behavioral cap by (19)--(20).

Nevertheless the profile in which player \(2\) Quits surely at date zero and
everyone else uses Never is an exact terminal Nash profile against every
behavioral deviation. Every realized or deviating outcome has payoff zero:
joining player \(2\), passing player \(2\)'s date-zero Quit, changing player
\(2\)'s own stopping time, and any randomized mixture all yield zero. Hence
the global debt minimum is zero and the game has a uniform-equilibrium payoff.

This regression does not satisfy the theorem's positive-minimum hypothesis.
It tests the downstream inference only: literal state return plus exact full
best-response gains is not an admissible Nash--Bellman return.

### Pure-minimum hit is not a rank conclusion

At a minimum hit, the last mover has zero debt, but another previously zero
coordinate may reactivate. The theorem neither asserts zero-set inclusion nor
a smaller positive-debt support. This is why Theorem C keeps the minimum-hit
branch separate rather than labeling it a descent.

## Adapter and consumer

The actual-data adapter is Theorem E. A positive global minimum and any of its
retained actual realizing sequences enter the already reviewed arbitrary-clock
purification theorem. Bounded additional purification and, only if needed,
the checked pure-time minimum descent produce the literal pure off-minimum
source \(t^0\). No compactness is used after that point.

The output strictly narrows the actual paid-port obligation to two finite
objects: a bounded exact-response path to a pure minimum or an entirely
off-minimum literal exact-response cycle. This is a reduction, not a terminal
consumer. The audited existing positive-return consumer does not accept either
object without temporal exactification or a renewable rank.

## Lean handoff

A narrow implementation can reuse the existing pure-time APIs and add:

1. a finite response-menu definition containing Never, zero, and the first
   opponent deadline;
2. a theorem that this menu attains
   `quittingContinuationBestResponseValue` and is contained in the inherited
   finite alphabet;
3. a deterministic Fin4 successor choosing a maximum-debt player and a
   canonical maximizing menu entry;
4. exact gain and target-debt-zero identities;
5. a finite-orbit repetition theorem with the \(6^4\) bound;
6. the minimum-hit/off-minimum-cycle split;
7. a bounded adapter that purifies the arbitrary-clock port target and invokes
   `pureTimeMinimum_exists_offMinimum` only in the equality case; and
8. the exact cycle ledger and its \(D_*/12\) externality consequences; and
9. the four-state regression (27)--(28), including its exact terminal-Nash
   witness.

Likely dependencies are
`PureTimeCapAttainment.lean`, `PureTimeMinimumDescent.lean`, stopping-law
disintegration, finite-function cardinality, and the existing pure-time paid
first-disagreement localization. The implementation should not define a
`QuittingPunishmentFloorAdmissibleEdge` from a response edge; the theorem
explicitly proves no such adapter.

Useful checks are:

- all-Never source;
- first opponent deadline zero;
- four distinct positive initial deadlines, where the alphabet bound is six;
- a response which deletes the only occurrence of one inherited deadline;
- a minimum hit followed by reactivation of an old zero coordinate; and
- the solved-game cycle regression.

## Scope and nonclaims

- Theorems A--E are checked in production Lean as recorded below.
- It does not prove a uniform-equilibrium payoff or refute the conjecture.
- It does not turn strategy-revision time into game time.
- It does not assign root absorption charge to a best-response gain.
- It does not turn the \(D_*/12\) nonmover payoff fall or debt rise into a
  Nash--Bellman edge or punishment-floor charge.
- It does not prove punishment-floor admissibility of cycle vertices.
- It does not show that the original paid row survives the bounded extra
  purification; only its literal ancestry remains recorded.
- It does not give zero-set inclusion, support descent, or any other renewable
  rank in the minimum-hit branch.
- It does not consume the entirely off-minimum response cycle.
- It does not claim the cycle's (1296) bound is sharp.

## Lean formalization record

Pre-formalization packet SHA-256:
`84c45dc6f1ed93eb0b350f73d04c0f970e993946804d30e60652fe419a11dfb0`.

The finite horizontal response alternative was integrated in production Lean
by commit `a848b051d2d1406f7526eb650e41cbfa16d36b54`.

The inherited alphabet and exact cap-attainment statements are owned by
`UniformEquilibrium/Diagnostics/Quitting/PureTimeInheritedResponseAlphabet.lean`.
`card_quittingPureTimeInheritedResponseAlphabet_le` gives the generic
`card ι + 2` bound, while
`exists_quittingPureTime_capAttainer_mem_inheritedResponseAlphabet` retains
exact unrestricted cap attainment inside that alphabet.

`UniformEquilibrium/Diagnostics/Quitting/PureTimeSelectedExactResponseOrbit.lean`
owns the deterministic maximal-debt response orbit, the exact mover-gain and
zero-target-debt identities, literal replacement ancestry, and the Fin4
recurrence bound `1296`.
`exists_minimumDebtEntrance_xor_offMinimumExactResponseCycle`
(`UniformEquilibrium/Diagnostics/Quitting/PureTimeExactResponseMinimumAlternative.lean`)
states the exclusive alternatives literally.  Its entrance records strict
off-minimality at every earlier orbit state.  Its cycle records strict
off-minimality through the complete finite-state bound; every response edge
has a fresh paid first-disagreement row with gain at least `D*/card ι`.

The exact closed-cycle accounting is factored through
`closed_mover_externality_ledger`
(`MathUE/FiniteResponseCycleLedger.lean`).  In Fin4,
`exists_nonmover_payoffFall_and_debtRise_ge_twelfth_finFour`
(`UniformEquilibrium/Diagnostics/Quitting/FinFourPureTimeExactResponseCycleExternality.lean`)
gives a prescribed-payoff fall and a possibly different debt-rise witness,
each at least `D*/12`, together with exact aggregate nonmover cap cancellation.

`nonempty_quittingBehaviorSupportedPureTimePurification`
(`UniformEquilibrium/Quitting/Paths/BoundedSupportedPureTimePurification.lean`)
purifies by at most `card ι` support-selected non-worsening replacements.
`exists_finFourActualSourcePureTimeResponseAlternative_of_debtSumInf_pos`
(`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/FinFourActualSourcePureTimeResponseAlternative.lean`)
starts from positive terminal-debt infimum, selects the actual compact minimum
source, retains the normalized paid port, and records ancestry from one fixed
retained source to the initial pure profile and every displayed response-orbit
profile.  Its exclusive Fin4 alternative exposes the entrance time or cycle
endpoint and period with literal bound `1296`, and its purification count is at
most four.

Theorems A--E have `M` and `L`.  The direct compact-minimum/realizing-sequence
wrapper provides actual-source `A`.  Attaching the retained paid row and
source port to the exclusive finite response alternative is branch-local `C`.
There is no consumer of the resulting minimum entrance or off-minimum cycle,
and no chronology, renewal, Nash or Nash--Bellman path, punishment-floor
return, uniform-equilibrium payoff, or conjecture conclusion is claimed.
