# Finite pure-clock max-debt response cycles

## Status

The finite-alphabet and literal-cycle statements below are proved in ordinary
mathematics.  They have not been checked as new Lean declarations.

They do **not** give a punishment-floor admissible return.  The cycle edges are
whole-strategy response replacements, whereas the checked admissible-return
consumer requires temporal exact Nash--Bellman predecessor edges.  The result
is therefore a sharp horizontal normal form, not a consumer for the
off-minimum paid port.  A strict preemption edge does yield either one fixed
punishment-floor charged predecessor or a fixed below-punishment actual
payoff, but the former is not renewable and the latter is only the original
behavioral debt in a sharper form.

## Question

Suppose a four-player quitting game has positive global minimum terminal debt

\[
D_*>0,
\]

and an actual pure-clock profile has been reached through literal replacements
from a source-attached off-minimum paid port.  If one repeatedly lets a
maximum-debt player install a complete cap-attaining best response, can the
iteration be kept in a finite state space, and does its recurrence give a
checked admissible return?

## 1. Pure-clock caps have three canonical representatives

Write a pure clock as an element of

\[
\overline{\mathbb N}=\mathbb N\cup\{\infty\}.
\]

Fix a pure-clock opponent profile for player \(i\).

If every opponent uses Never, then every finite stopping time gives the
singleton payoff \(r_i(\{i\})\), while Never gives the nontermination payoff
zero.  Thus a cap-attaining response may be chosen from \(\{0,\infty\}\).

Otherwise, let \(m\) be the earliest finite opponent deadline and let \(A\)
be the nonempty coalition of opponents stopping at \(m\).  A deterministic
stopping time \(q\) has value

\[
\begin{array}{c|c}
q<m&r_i(\{i\}),\\
q=m&r_i(A\cup\{i\}),\\
q>m\text{ or }q=\infty&r_i(A).
\end{array}
\tag{1.1}
\]

The first option is available exactly when \(m>0\), and then it is represented
by \(q=0\).  Hence a cap-attaining response can always be chosen from

\[
\{0,m,\infty\}.
\tag{1.2}
\]

This covers arbitrary behavioral responses.  Before absorption the only
public history is repeated all-Continue, so one player's behavioral strategy
induces a probability distribution on pure stopping times.  Against fixed
pure-clock opponents its payoff is the corresponding average of the values
in (1.1); an extreme pure time attains the maximum.

This is the same elementary cap calculation used in the calendar lemma of
[`ARBITRARY_CLOCK_MINIMUM_PURIFICATION_TO_OFF_MINIMUM_PAID_PORT.md`](../formalized/ARBITRARY_CLOCK_MINIMUM_PURIFICATION_TO_OFF_MINIMUM_PAID_PORT.md).

## 2. The clock alphabet is closed under canonical best responses

Let \(t^0\) be the initial pure-clock profile and define

\[
\mathcal A=
\{0,\infty\}\cup
\{t_i^0:t_i^0<\infty\}.
\tag{2.1}
\]

Assume the current profile belongs to \(\mathcal A^4\).  Its earliest finite
opponent deadline for any selected player, when it exists, is itself a
coordinate of the current profile and therefore belongs to \(\mathcal A\).
By (1.2), that player has a cap-attaining response in \(\mathcal A\).
Consequently canonical cap-attaining pure responses preserve
\(\mathcal A^4\).

Fix once and for all:

1. a deterministic tie-break among maximum-debt players; and
2. a deterministic tie-break among the canonical cap-attaining clocks in
   \(\{0,m,\infty\}\).

These choices define a self-map

\[
F:\mathcal A^4\longrightarrow\mathcal A^4.
\tag{2.2}
\]

No compactness or calendar-type quotient is used: this is a literal finite set
of absolute clock profiles.

## 3. Every selected edge has a fixed actual gain

For a current actual profile \(x\), let

\[
d_i(x)=B_i(x)-U_i(x),
\qquad
D(x)=\sum_i d_i(x).
\]

Every actual semantic pair belongs to the carrier, so

\[
D(x)\ge D_*.
\tag{3.1}
\]

For the selected maximum-debt player \(i\),

\[
d_i(x)\ge \frac{D(x)}4\ge\frac{D_*}4.
\tag{3.2}
\]

Let \(y=F(x)\).  Only player \(i\)'s strategy changes, and its new pure clock
attains \(B_i(x)\).  Since the opponents are unchanged,

\[
B_i(y)=B_i(x),
\qquad
U_i(y)=B_i(x).
\]

Therefore

\[
U_i(y)-U_i(x)=d_i(x)\ge\frac{D_*}4,
\qquad
d_i(y)=0.
\tag{3.3}
\]

These are complete behavioral best-response edges, not merely stationary or
one-date comparisons.

The target need not remain on the minimum fibre.  Exactly,

\[
D(y)-D(x)
=-d_i(x)+\sum_{j\ne i}\bigl(d_j(y)-d_j(x)\bigr).
\tag{3.4}
\]

At a minimum source, global minimality only forces the cross-coordinate
leakage in (3.4) to be at least \(d_i(x)\).  It does not force equality.  Thus
minimum-fibre preservation is not part of this construction.

## 4. Literal periodic response orbit

Because \(\mathcal A^4\) is finite, the deterministic orbit

\[
x^{k+1}=F(x^k)
\]

is eventually periodic.  There exist \(a<b\) such that

\[
x^a=x^b
\tag{4.1}
\]

as literal pure-clock profiles.  Every edge on this closed segment is an
actual one-player cap-attaining response with gain at least \(D_*/4\), and it
annihilates the mover's debt at its target.

The period cannot be one, because every selected source has positive debt and
(3.3) gives a strict payoff gain.  Earlier zero coordinates may be reactivated
by later players' replacements, so periods of length greater than one are not
excluded.

All source ancestry is literal: the target of one response is definitionally
the source of the next.  If the initial pure-clock profile descended from the
original paid port, the whole finite response orbit retains that replacement
list as provenance.  What need not survive operationally is the original
paid row or its cap comparison at every later profile.

## 5. Exact regression: horizontal response recurrence is possible

Already with two players, restrict clocks to \(\{0,\infty\}\) and set

\[
\begin{array}{c|ccc}
&\{1\}&\{2\}&\{1,2\}\\ \hline
r_1&-1&0&1\\
r_2&1&1&0.
\end{array}
\tag{5.1}
\]

Then the literal best-response cycle is

\[
(0,0)\to(0,\infty)\to(\infty,\infty)
\to(\infty,0)\to(0,0),
\tag{5.2}
\]

where each moving player gains exactly one.  Every state on the cycle has
total debt one.  This game nevertheless has an exact terminal stationary
equilibrium: player (1) always Continues and player (2) Quits at any fixed
stationary rate (q\in(0,1/2]).  Player (2)'s terminal payoff and cap are
both one; player (1)'s prescribed payoff and cap are both zero.  Thus the
game does not model the positive-minimum counterexample regime.  Its role is narrower: a
closed loop of literal full best responses and fixed positive gains is
compatible with quitting-game payoff geometry.  A contradiction must use the
positive-minimum source structure or a genuinely temporal compiler, not the
existence of the horizontal cycle alone.

## 6. Why the checked admissible-return consumer does not apply

The checked structure `QuittingPunishmentFloorAdmissibleEdge` in
`PunishmentFloorAdmissibleChargedRelation.lean` consists of two boxed payoff
states together with

\[
\texttt{IsQuittingNashBellmanEdge reward current tail}.
\]

It is an exact **temporal predecessor edge**.  Its charge is the literal
one-stage absorption mass of the exact Nash root.  Paths in the relation
decode to finite exact punishment-floor Nash--Bellman prefixes.

A pure-clock response edge \(x\to y\) above has different data:

* it replaces one player's complete strategy against fixed opponents;
* its positive quantity is the mover's whole-profile payoff gain;
* its source and target are alternative strategy profiles, not consecutive
  continuation states of one play; and
* it supplies neither a root exact-Nash certificate for all players nor the
  Bellman factorization of the source payoff through the target payoff.

The first-disagreement of the two pure clocks can localize the mover's gain to
an actual row, but this remains a horizontal counterfactual comparison.  It
does not turn that row into an `IsQuittingNashBellmanEdge`, and the payoff gain
is not the absorption charge used by the admissible relation.

Accordingly neither
`quittingGame_exists_uniformPayoff_of_positive_admissible_cycle` nor
`QuittingPositiveAdmissiblePayoffNearReturnFamily` accepts the cycle (4.1).
Both require a path made of exact punishment-floor admissible predecessor
edges.  Exact recurrence of the strategy profile does not fill that missing
field.

## 7. Strongest valid conclusion and remaining question

Conditionally on reaching one actual pure-clock profile in the positive-
minimum branch, canonical maximum-debt responses produce

\[
\boxed{
\text{a literal finite closed cycle of complete behavioral best responses,}
\quad
\text{each with gain at least }D_*/4.}
\tag{7.1}
\]

This is stronger than recurrence only up to calendar type and stronger than a
sequence of unrelated paid rows.  It supplies perfect target-to-next-source
typing in response-update time.

It does not consume the off-minimum port.  The remaining bridge is precisely
one of the following:

1. serialize a positive-gain horizontal response cycle into a finite exact
   Nash--Bellman/punishment-floor chronology with positive absorption charge;
2. prove that such a response cycle is incompatible with positive global
   minimum debt plus the retained hard-residual source passport; or
3. extract a renewable finite rank from the cross-coordinate debt
   reactivations around the cycle.

Without one of these, summing the edge gains is invalid: different players
move, and later externalities can undo earlier payoff gains.

## 8. Exact aggregate leakage ledger around the cycle

The literal cycle permits a complete accounting, but the accounting supplies
no missing sign.

Index a period by (k\in\mathbb Z/L\mathbb Z).  Let (i_k) be the mover on
the edge (x^k\to x^{k+1}), and put

\[
g_k=d_{i_k}(x^k)\ge D_*/4.
\]

For a nonmover (j\ne i_k), write

\[
\ell_{k,j}=d_j(x^{k+1})-d_j(x^k).
\]

The mover identity is

\[
d_{i_k}(x^{k+1})-d_{i_k}(x^k)=-g_k.
\tag{8.1}
\]

Summing the debt change of one fixed player (j) around the literal cycle
gives the exact coordinate account

\[
\sum_{k:i_k\ne j}\ell_{k,j}
=
\sum_{k:i_k=j}g_k.
\tag{8.2}
\]

Thus every unit of debt annihilated when (j) moves is recreated, in the
aggregate, by the other players' moves.  Summing again over (j) gives

\[
\sum_k\sum_{j\ne i_k}\ell_{k,j}
=\sum_k g_k>0.
\tag{8.3}
\]

The payoff and cap ledgers make the cancellation even more explicit.  Since
the mover's opponents are unchanged,

\[
B_{i_k}(x^{k+1})-B_{i_k}(x^k)=0,
\qquad
U_{i_k}(x^{k+1})-U_{i_k}(x^k)=g_k.
\tag{8.4}
\]

Literal recurrence then gives, for each player (j),

\[
\sum_{k:i_k\ne j}
  \bigl(B_j(x^{k+1})-B_j(x^k)\bigr)=0,
\tag{8.5}
\]

and

\[
\sum_{k:i_k\ne j}
  \bigl(U_j(x^{k+1})-U_j(x^k)\bigr)
=-\sum_{k:i_k=j}g_k.
\tag{8.6}
\]

Equation (8.2) is exactly (8.5) minus (8.6).  Hence the cycle does not hide a
positive cap telescope: cap motion caused by the other players has zero signed
sum, while adverse prescribed-payoff externalities exactly finance all of the
own-response gains.

Positive global minimum debt supplies the lower bounds on (g_k), but no
sign on any individual term in (8.5) or (8.6).  At a minimum-fibre state it
only says that the outgoing aggregate nonmover debt leakage is at least the
mover payment; at a maximum-debt state on the cycle the reverse inequality
holds for total-debt motion.  Neither statement is strict, renewable, or
temporal.

Therefore the exact aggregate identities alone yield none of the three
accepted outputs: no executable Nash--Bellman edge, no finite rank, and no
contradiction to (D_*>0).  Any use of the retained purification ancestry
must add a sign or a chronological realization not present in this ledger.

## 9. A punishment-floor split for strict preemption edges

The only calendar-changing edge that can introduce a new earliest date is a
strict preemption to date zero.  Suppose player $i$ makes such an edge from
$x$ and gains

\[
 g=s_i-U_i(x)\ge D_*/4,
 \qquad s_i=r_i(\{i\}).
 \tag{9.1}
\]

Let $P_i$ be player $i$'s behavioral punishment value.  The Fin4 hard
residual makes every player punishment-normal, so $P_i\le s_i$.  The exact
identity

\[
 g=(s_i-P_i)+(P_i-U_i(x))
 \tag{9.2}
\]

therefore gives the exhaustive alternative

\[
 s_i-P_i\ge g/2
 \quad\hbox{or}\quad
 U_i(x)\le P_i-g/2.
 \tag{9.3}
\]

The first arm creates a genuine punishment-floor charged edge, although only
one edge.  Let $P=(P_j)_j$, and let $q$ be any exact product Nash root
against the tail vector $P$.  Write $a_i(q)$ for the probability that at
least one opponent of $i$ Quits at $q$, and $A(q)$ for total root
absorption.  If rewards are bounded by $M>0$, forcing $i$ to Quit changes
its singleton payoff by at most $2Ma_i(q)$, while forcing it to Continue
changes its tail payoff $P_i$ by at most $2Ma_i(q)$.  Hence its
Quit-minus-Continue endpoint difference is at least

\[
 (s_i-P_i)-4M a_i(q).
 \tag{9.4}
\]

If $a_i(q)<(s_i-P_i)/(4M)$, exact Nash forces $i$ to Quit surely, and
then $A(q)=1$.  Otherwise $A(q)\ge a_i(q)$.  Since
$0\le s_i-P_i\le2M$, both cases give

\[
 A(q)\ge \frac{s_i-P_i}{4M}
 \ge \frac{D_*}{32M}.
 \tag{9.5}
\]

Exact Nash--Bellman prefixing of the punishment vector by $q$ is therefore
a floor-admissible predecessor edge with the fixed absorption charge (9.5).
The floor certificate is automatic from
`quittingPunishmentValue_le_rootSuccessorPayoff_of_tail_ge`, and the edge is
packaged by `QuittingPunishmentFloorAdmissibleEdge.ofExactEdge`.

This does **not** consume the response cycle.  The edge runs once from the
punishment anchor to its Bellman predecessor.  Nothing in the horizontal
clock cycle returns that predecessor to the punishment vector, or makes the
same root exact against the predecessor.  A hypothetical counterexample is
already allowed a finite total punishment-floor charge budget, so one fixed
positive edge merely spends part of that budget.

In the second arm of (9.3), the actual pure-clock payoff is separated below
the punishment value by at least $D_*/8$.  Consequently its behavioral cap
debt is at least $D_*/8$, but this is only a refinement of the debt already
used to select the response.  It supplies no temporal predecessor edge.

Thus preemption yields the sharper but still nonterminal split

\[
 \boxed{
 \text{one positive punishment-floor edge}
 \quad\lor\quad
 \text{one actual payoff below its punishment value}.}
 \tag{9.6}
\]

The split confirms the remaining typing obstruction: repeating the
horizontal preemption in response-update time does not repeat the
punishment-floor edge in game time.

## Sources inspected

* [`ARBITRARY_CLOCK_MINIMUM_PURIFICATION_TO_OFF_MINIMUM_PAID_PORT.md`](../formalized/ARBITRARY_CLOCK_MINIMUM_PURIFICATION_TO_OFF_MINIMUM_PAID_PORT.md),
  calendar cap calculation and pure-clock off-minimum entrance.
* `UniformEquilibrium/Quitting/Bellman/Finite/
  PunishmentFloorAdmissibleChargedRelation.lean`, exact admissible edge and
  path types.
* `UniformEquilibrium/Quitting/Bellman/Finite/PunishmentFloorForward.lean`,
  punishment-floor invariance under exact Nash predecessors.
* `UniformEquilibrium/Quitting/Paths/QuitEndpointOpponentBound.lean` and the
  corresponding elementary forced-Continue coupling, the two $2M a_i(q)$
  endpoint bounds used in (9.4).
* `UniformEquilibrium/Quitting/Projective/PunishmentFloorNearReturn.lean`,
  positive admissible cycle and payoff-near-return consumers.
* `UniformEquilibrium/Diagnostics/Quitting/
  PaidFirstDisagreementPayoffNearReturn.lean`, explicit statement that the
  paid-row interface does not itself construct an admissible return.
