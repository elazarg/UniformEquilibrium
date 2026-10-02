# Finite pure-clock exact-response cycles and the admissible-edge mismatch

Author: `PAIRED_HULL_REVIEW`

## Status

The finite-cycle theorem below is proved ordinary mathematics. It uses
unrestricted behavioral caps, not a bounded-clock substitute. It constructs a
literal cycle of actual pure-clock profiles whose successive profiles differ
by one exact complete best response. The cycle retains any finite ancestry
leading to its initial profile.

It does **not** prove a uniform-equilibrium payoff. The exact-response edges
are horizontal changes of complete strategies. The checked positive-return
consumer instead requires temporal Nash--Bellman predecessor edges carrying
root absorption charge and punishment-floor states. Section 5 records this
typing mismatch precisely.

## 1. Setting

Let the player set be \(I=\operatorname{Fin}4\), and let \(r\) be a bounded
quitting reward table. For an actual behavioral profile \(\sigma\), write

\[
 U_i(\sigma),\qquad
 B_i(\sigma)=\sup_{\tau_i}U_i(\tau_i,\sigma_{-i}),\qquad
 d_i(\sigma)=B_i(\sigma)-U_i(\sigma),
\]

where the supremum is over every complete behavioral strategy of player
\(i\). Put \(D(\sigma)=\sum_i d_i(\sigma)\), and suppose

\[
 D(\sigma)\ge D_*>0
 \tag{1.1}
\]

for every actual profile. This follows when \(D_*\) is the positive global
minimum of terminal semantic debt.

A pure-clock profile is a vector

\[
 t:I\longrightarrow \overline{\mathbb N}:=\mathbb N\cup\{\infty\}.
\]

Player \(i\) Continues before \(t_i\), Quits surely at \(t_i<\infty\), and
plays Never when \(t_i=\infty\).

## 2. Canonical full best replies use a finite inherited alphabet

Fix a pure-clock profile \(t\) and player \(i\).

If every opponent uses Never, every finite pure response by \(i\) terminates
alone, while Never gives the declared nonabsorption payoff zero. Hence

\[
 B_i(t)=\max\{r_i(\{i\}),0\}.
 \tag{2.1}
\]

Otherwise let \(m_i\) be the earliest finite opponent deadline and let
\(A_i\) be the nonempty coalition of opponents whose deadline is \(m_i\).
Every pure response has one of the following values:

\[
 \begin{array}{c|c}
 q<m_i&r_i(\{i\}),\\
 q=m_i&r_i(A_i\cup\{i\}),\\
 q>m_i\text{ or }q=\infty&r_i(A_i).
 \end{array}
 \tag{2.2}
\]

The first line is available exactly when \(m_i>0\), and is represented by
\(q=0\). The second is represented by \(q=m_i\), and the third by Never.
Since a complete behavioral response is a probability distribution on pure
stopping times and payoff is affine in that distribution, (2.1)--(2.2) give
the unrestricted behavioral cap. Thus an exact cap attainer may always be
chosen from

\[
 \{0,m_i,\infty\}
 \tag{2.3}
\]

after deleting unavailable or duplicate entries.

Now fix an initial pure-clock profile \(t^0\) and define its inherited clock
alphabet

\[
 \Lambda(t^0)=
 \{0,\infty\}\cup\{t_i^0:i\in I, t_i^0<\infty\}.
 \tag{2.4}
\]

If every coordinate of a current profile belongs to \(\Lambda(t^0)\), then
its earliest opponent deadline \(m_i\), when finite, also belongs to
\(\Lambda(t^0)\). Therefore the canonical exact response (2.3) belongs to
the same alphabet. No new finite date is ever created.

## 3. Literal finite exact-response cycle

Choose fixed total orders on the four players and on the finite set
\(\Lambda(t^0)\). Define a deterministic successor map \(F\) on
\(\Lambda(t^0)^I\) as follows.

1. At \(t\), choose the least player \(i(t)\) among those maximizing
   \(d_i(t)\).
2. Among the canonical cap-attaining responses in (2.3), choose the least
   one, denoted \(q(t)\).
3. Put

   \[
   F(t)=t[i(t)\leftarrow q(t)].
   \tag{3.1}
   \]

Because there are four players, (1.1) gives

\[
 d_{i(t)}(t)=\max_i d_i(t)\ge D(t)/4\ge D_*/4.
 \tag{3.2}
\]

The selected response attains the unrestricted cap. Changing only player
\(i(t)\)'s strategy leaves that player's cap unchanged. Consequently

\[
 U_{i(t)}(F(t))-U_{i(t)}(t)=d_{i(t)}(t)\ge D_*/4,
 \tag{3.3}
\]

and

\[
 d_{i(t)}(F(t))=0.
 \tag{3.4}
\]

In particular \(F(t)\ne t\).

Iterate \(t^{n+1}=F(t^n)\). The state space
\(\Lambda(t^0)^I\) is finite. Hence there are \(a<b\) such that

\[
 t^a=t^b
 \tag{3.5}
\]

literally as pure-clock vectors. Choosing the first repeated state makes
\(t^a,\ldots,t^{b-1}\) a nontrivial directed cycle. Every edge of the cycle
is an actual one-player replacement by an exact unrestricted behavioral best
response, has gain at least \(D_*/4\), and kills the mover's debt exactly.

This proves:

> **Finite pure-clock exact-response cycle theorem.** If a four-player
> quitting game has positive global terminal semantic debt \(D_*>0\), then
> from every pure-clock profile there is a finite literal path into a
> nontrivial literal cycle of pure-clock profiles. Every edge is an exact
> complete behavioral best response with mover gain at least \(D_*/4\), and
> the target has zero mover debt.

The same proof for a finite player set of cardinality \(m>0\) gives the floor
\(D_*/m\).

## 4. Minimum-return split and source ancestry

First suppose the initial profile \(t^0\) is pure-clock and off minimum, so

\[
 D(t^0)>D_*.
 \tag{4.1}
\]

Exactly one of the following happens before the first repeated state.

1. There is a least \(n>0\) with \(D(t^n)=D_*\). Then

   \[
   t^0\longrightarrow t^1\longrightarrow\cdots
   \longrightarrow t^n
   \tag{4.2}
   \]

   is a literal finite chain of exact full best responses returning to an
   actual pure-clock global minimum. The last mover has debt zero at the
   returned minimum. If already \(D(t^{n-1})=D_*\), the last edge is a
   genuine minimum-to-minimum response chord; otherwise it is an
   off-minimum-to-minimum paid return.

2. No such \(n\) occurs. Then the eventual literal response cycle consists
   entirely of profiles with total debt strictly above \(D_*\).

This pure off-minimum entrance can be obtained source-faithfully from the
arbitrary-clock purification output, but one extra step is necessary. That
theorem's strict branch may stop before all four strategies are pure. Starting
from its actual off-minimum target \(\tau\), apply the elementary supported
pure-clock selection successively to every still-mixed player. After at most
four literal replacements one obtains a pure-clock profile \(\xi\). No claim
is made that these extra replacements preserve the off-minimum inequality.

- If \(D(\xi)>D_*\), take \(t^0=\xi\).
- If \(D(\xi)=D_*\), apply the checked
  `pureTimeMinimum_exists_offMinimum` theorem to \(\xi\). Its output is a
  pure-clock profile \(t^0\), connected to \(\xi\) by a finite literal
  pure-time replacement ancestry, with \(D(t^0)>D_*\).

Thus every profile in either output is connected by a literal finite
unilateral replacement ancestry to \(\tau\), and hence, by composition, to
the original minimum-approximating source profile retained by the arbitrary-
clock purification theorem. No new carrier realizer or unrelated source is
selected. The original paid row at \(\tau\) remains historical provenance;
the cycle uses freshly selected exact pure-clock best replies.

For every edge, the two distinct pure stopping times also give a literal paid
first-disagreement row with gain at least \(D_*/4\). This is a localization
of the horizontal response gain; it does not change the edge type discussed
next.

## 5. Why the checked admissible-return consumer does not apply

The cycle in Section 3 lives in the graph

\[
 \text{actual profile}
 \xrightarrow{\text{replace one complete strategy by a best response}}
 \text{actual profile}.
 \tag{5.1}
\]

The checked positive admissible-return relation is different. A
`QuittingPunishmentFloorAdmissibleEdge` stores two bounded payoff/root states
and asserts an exact temporal Bellman predecessor identity

\[
 u_{\mathrm{current}}
 =F_x(u_{\mathrm{tail}}),
 \tag{5.2}
\]

where \(x\) is an exact product root against the displayed tail continuation.
Its charge is the one-stage absorption probability of \(x\), and both states
must satisfy the punishment floor. Relation paths are finite exact
Nash--Bellman root blocks, read in reverse to form an in-game chronology.

None of these fields follows from (5.1):

- a complete-strategy best-response gain is not root absorption charge;
- the target profile is not a Bellman predecessor of the source profile;
- the paid first-disagreement row need not be exact root Nash against its
  literal continuation;
- no punishment-floor state annotations are supplied; and
- serializing strategy revisions is not the same as playing the revised
  profiles at consecutive dates of one quitting game.

Therefore neither
`QuittingPositiveAdmissibleReturn.exists_uniformEquilibriumPayoff` nor the
weaker payoff-near-return consumer accepts the cycle. The latter still needs
a path in
`quittingPunishmentFloorAdmissibleChargedRelation`; it weakens only endpoint
return to payoff closure.

The precise mismatch is thus:

\[
 \boxed{
 \text{literal finite full-best-response return}
 \not\Rightarrow
 \text{finite punishment-floor Nash--Bellman return}.}
 \tag{5.3}
\]

This is not merely a source-reconstruction failure. Section 3 supplies exact
target-to-next-source identity. The remaining problem is temporal
exactification of at least one positive edge while retaining closure of the
rest of the cycle.

## 6. Consequence for the off-minimum waist

The arbitrary-clock purification result, the bounded extra purification in
Section 4, and Section 3 give the unconditional source-faithful reduction

\[
 \text{positive minimum source}
 \longrightarrow
 \text{actual off-minimum target}
 \longrightarrow
 \text{pure-clock off-minimum descendant}
 \longrightarrow
 \begin{cases}
 \text{literal exact-response return to a pure minimum},\\
 \text{literal off-minimum exact-response cycle}.
 \end{cases}
 \tag{6.1}
\]

Thus the off-minimum paid-port waist does not lack a finite returned object in
the strategy-revision graph. What it lacks is a theorem converting this
returned object into one of:

1. an exact punishment-floor Nash--Bellman return;
2. a renewable minimum-fibre rank decrease in the minimum-return arm; or
3. a terminal consumer for the entirely off-minimum response cycle.

Static coalition-toggle cycles warn that forgetting the complete clock and
source data is insufficient. Conversely, any future exactification theorem
may use the stronger facts retained here: finite inherited clock alphabet,
literal profile equality at return, exact unrestricted cap attainment, a
uniform response gain on every edge, and exact killed-mover debt.

## 7. Named source interfaces inspected

- `exists_quittingPureTime_capAttainer` in
  `UniformEquilibrium/Diagnostics/Quitting/PureTimeCapAttainment.lean`;
- `pureTimeMinimum_exists_offMinimumPaidPort` in
  `UniformEquilibrium/Diagnostics/Quitting/PureTimeMinimumPaidPort.lean`;
- the complete pure-clock cap calculation in
  [`ARBITRARY_CLOCK_MINIMUM_PURIFICATION_TO_OFF_MINIMUM_PAID_PORT.md`](../formalized/ARBITRARY_CLOCK_MINIMUM_PURIFICATION_TO_OFF_MINIMUM_PAID_PORT.md);
- `QuittingPunishmentFloorAdmissibleEdge` and
  `quittingPunishmentFloorAdmissibleChargedRelation` in
  `UniformEquilibrium/Quitting/Bellman/Finite/PunishmentFloorAdmissibleChargedRelation.lean`;
- `QuittingPositiveAdmissibleReturn` in
  `UniformEquilibrium/Diagnostics/Quitting/UniformExistenceBoundary.lean`;
- `QuittingPositiveAdmissiblePayoffClosure` in
  `UniformEquilibrium/Diagnostics/Quitting/PaidFirstDisagreementPayoffNearReturn.lean`.

No external paper claim is used.
