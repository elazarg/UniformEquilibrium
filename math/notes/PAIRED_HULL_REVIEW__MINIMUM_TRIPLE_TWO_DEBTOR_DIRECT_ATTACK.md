# Minimum pure triple with two possible debtors: direct attack

Identity: `PAIRED_HULL_REVIEW`

## Status

The source-attached pure-triple output of the oriented-pair chord admits a
more concrete dispatch than a generic tangent-family exit.  Its literal
complete best responses generate a finite oriented-triple automaton with
twelve states.  Every nonterminal transition is a two-edge
triple-to-pair-to-triple swap; every intermediate and terminal profile is an
actual pure-clock profile with Never tail and can be regenerated as a
complete minimum source whenever it stays on the global minimum fibre.

This finite automaton is valid selector geometry, but it is **not a live
minimum-fibre SCC**. Every vertex is a canonical pure-time positive global
minimum, so the checked pure-time deadline-rank theorem applies directly and
gives a source-faithful finite replacement ancestry to an off-minimum paid
port of gain \(>D_*/4\). The horizontal automaton may cycle if one insists on
its selected responses, but an off-path finite-clock exit exists from every
vertex. The remaining obstruction is therefore the universal off-minimum
paid-port waist, not the twelve-state minimum automaton.

## 1. Input state

Let \(I=\operatorname{Fin}4\), and suppose terminal-semantic total debt has
positive global minimum \(D_*>0\). For a nonempty coalition \(S\subseteq I\),
write \(M^S\) for the profile in which exactly \(S\) Quits surely at date zero
and everyone else plays Never.

An oriented triple state is determined by distinct labels \(e,j\in I\). Put

\[
 T=I\setminus\{e\},
 \qquad C=I\setminus\{e,j\}.
\]

The state \(O(e,j)\) consists of:

1. the actual global-minimum profile \(Y=M^T\);
2. a retained strict outsider-join edge from the pair \(T\setminus\{j\}\)
   to \(Y\), whose mover is \(j\);
3. the exact zero-debt identities
   \(d_e(Y)=d_j(Y)=0\); and
4. the nonempty support bound
   \[
     \varnothing\ne\operatorname{supp}^+(Y)\subseteq C.
   \]

The oriented-pair minimum-chord theorem supplies exactly such a state, with
\(e=p\) and \(j=q\). Every cap here is the unrestricted behavioral cap.

## 2. Complete debt formula at the triple

Because \(T\) contains three sure date-zero quitters, every unilateral
response is screened at date zero.  Hence

\[
 d_i(M^T)=
 \begin{cases}
 [r_i(T\setminus\{i\})-r_i(T)]_+,&i\in T,\\[1mm]
 [r_i(T\cup\{i\})-r_i(T)]_+,&i\notin T.
 \end{cases}
\tag{2.1}
\]

In particular, every debtor in \(C\) has a literal pure Continue best
response which removes it from the terminal triple.  If the support has two
members, selecting a maximum-debt member gives gain at least \(D_*/2\); if it
has one member, the gain is \(D_*\).

The profile \(Y\) is also literally a deterministic pair-base induced-Nash
point: take the sure-Quit base \(C\), and the two free players \(e,j\).
Player \(j\) strictly chooses Quit by the incoming edge, and \(e\) weakly
chooses Continue because its debt is zero.  Thus the existing pair-base
two-debtor geometry applies at this exact point without selecting a different
stationary source.  Its paid row is one of the core-member leaves described
above.  This identification does not turn that row into a temporal return.

## 3. One literal response and the pair dispatch

Choose \(m\in C\) with maximal positive debt and set

\[
 P=T\setminus\{m\}=I\setminus\{e,m\}.
\]

The exact full response

\[
 M^T\longrightarrow M^P
\tag{3.1}
\]

is made by \(m\), has gain \(d_m(M^T)\ge D_*/2\), and kills \(m\)'s debt.

If \(D(M^P)>D_*\), (3.1) is an actual off-minimum paid port. Suppose instead
\(D(M^P)=D_*\). At the pair \(P\), the incoming mover \(m\) has zero debt,
because reversing (3.1) is strictly worse.  There are then three cases.

### 3.1 A pair member leaves

If a member of \(P\) has positive debt, its exact best response is a literal
pair-to-singleton response.  This is strategically oriented, not the
unsigned same-stage singleton route.

### 3.2 No pair member leaves and no outsider joins

This is impossible because total debt at \(M^P\) is \(D_*>0\).

### 3.3 The other outsider joins

If no pair member leaves, the only player who can carry positive debt is the
old excluded player \(e\): the incoming mover \(m\) is already solved. Thus

\[
 d_e(M^P)=D_*,
\]

and \(e\)'s exact response is the strict join

\[
 M^P\longrightarrow M^{I\setminus\{m\}}.
\tag{3.2}
\]

If the target is off minimum, this is the off-minimum paid port.  If it is
minimum, the oriented-pair chord theorem, now with incoming dropout \(m\),
gives the next oriented triple state

\[
 O(e,j)\longrightarrow O(m,e).
\tag{3.3}
\]

The new state has zero debt on \(m,e\), and its nonempty debt support is
contained in \(I\setminus\{m,e\}=P\). Its exact pure profile and ancestry
regenerate as a complete same-residual source using the neutral
all-Continue plateau construction.

Thus the generic support-entry output at the pure triple has become a finite
literal alternative: pair-to-singleton, off minimum, strict support descent,
or another oriented triple.

## 4. The finite oriented-triple automaton

There are exactly \(4\cdot3=12\) ordered states \(O(e,j)\). A nonterminal
successor has the form

\[
 (e,j)\longmapsto(m,e),
 \qquad m\notin\{e,j\}.
\tag{4.1}
\]

Choose \(m\) deterministically from the positive support, for example by
maximum debt followed by a fixed label order.  If no singleton or off-minimum
output occurs, iteration therefore enters a periodic orbit after at most
twelve distinct oriented states.

Writing the successive excluded labels as \(e_k\), the period obeys

\[
 e_{k+1}\ne e_k,
 \qquad e_{k+1}\ne e_{k-1}.
\tag{4.2}
\]

The two strict reward inequalities in one macro are

\[
\begin{aligned}
r_{e_{k+1}}(I\setminus\{e_k,e_{k+1}\})
  &>r_{e_{k+1}}(I\setminus\{e_k\}),\\
r_{e_k}(I\setminus\{e_{k+1}\})
  &>r_{e_k}(I\setminus\{e_k,e_{k+1}\}).
\end{aligned}
\tag{4.3}
\]

The first is the triple-to-pair leave; the second is the pair-to-triple join.
The join has exact gain \(D_*\), while the selected leave has gain at least
\(D_*/2\).

At the new triple, the excluded old mover \(e_{k+1}\) has zero join debt and
the new joiner \(e_k\) has zero leave debt. This is the exact state matching
needed to iterate (4.1); no independently selected pair-base point appears.

## 5. Background reversal is forced, not contradictory

Each macro carries a strict second difference.  The old excluded player
\(e=e_k\) strictly joins the pair
\(P=I\setminus\{e,m\}\), but it had zero debt at the previous triple
\(I\setminus\{e\}\), so

\[
 r_e(P\cup\{e\})-r_e(P)>0,
 \qquad
 r_e(I)-r_e(I\setminus\{e\})\le0.
\tag{5.1}
\]

Adding the omitted mover \(m\) to the background reverses the sign of \(e\)'s
join.  This is precisely the strict-background-reversal geometry already
forced in a hypothetical no-UE table.  It does not produce a robust-join
edge or a contradiction.  The robust-predecessor-base consumer requires a
join that stays weakly favorable on every disjoint background; (5.1) says
the opposite.

The hard-principal declarations concern normalized singleton rewards.  The
inequalities (4.3)--(5.1) live on complementary pair/triple/full-coalition
faces.  No checked implication aligns their labels or signs with a selected
hard principal.

## 6. Why the periodic orbit is not yet a consumer

Every edge in the orbit is an actual unilateral full-profile best response,
and every vertex is an actual global-minimum pure-clock profile.  Yet every
vertex absorbs at date zero.  The target terminal coalition of one edge is an
alternative profile, not the all-Continue successor reached after a stage of
the source profile.

Consequently the orbit is a horizontal response cycle.  It does not inhabit
`QuittingPunishmentFloorAdmissibleEdge`, whose edge is an exact
Nash--Bellman predecessor relation between continuation values.  The positive
payoff gains in (4.3) cannot be summed as chronological absorption charge.

Delaying every pure coalition behind an exact all-Continue plateau preserves
the semantic pairs and makes each response occur at a later literal deadline,
but it does not repair the typing: at the marked deadline the response target
is still a terminal sibling rather than the next all-Continue continuation.

This is the same obstruction exposed abstractly by the finite pure-clock
exact-response-cycle theorem, now with a much smaller source-attached state
space and exact alternating leave--join form.

## 7. One-debtor and two-debtor consequences

If an oriented triple has one debtor, its first leave gain is exactly \(D_*\).
If its minimum pair target has no positive pair member, the old excluded
player joins with gain \(D_*\), producing the next oriented triple. Thus a
nonterminal one-debtor run carries two full-gap horizontal responses per
macro.

If it has two debtors, the selected leave has gain at least \(D_*/2\). A
minimum target with no inactive-coordinate entry gives a literal support-one
child.  Entry by a current pair member is a positive singleton response;
entry by the old excluded outsider is exactly the swap (3.3). There is no
other support-entry label in Fin4.

This sharpens the direct geometry but does not orient the swap cycle by a
natural rank: the newly activated core coordinate may be one which was zero
at the preceding triple.

## 8. Relation to the reset-rigid chamber

This is not a new chamber disjoint from the checked reset-rigid node. It is a
strict specialization of that node. At \(O(e,j)\):

* the complete terminal law is the point mass at \(I\setminus\{e\}\);
* the reset owner may be taken to be either displayed zero-debt coordinate;
* every opponent-incidence atom selected by the fixed-law dispatcher is the
  same literal triple;
* the supported static toggle is therefore an actual member-leave or
  outsider-join comparison at that triple; and
* the sure base has cardinality three and its sole complementary coordinate
  is solved.

The sure-base fixed-law cap-rigidity theorem consequently identifies the
returned semantic pair with the literal pure-triple pair itself. At a global
minimum the dispatcher's strict absorbing child is impossible, so its dynamic
output is exactly the all-Continue fixed face. Thus the generic fixed-law
dispatcher adds no further vertex or edge here.

The specialization is nevertheless stronger than the generic chamber: it
retains a mass-one law, two named zero coordinates, an incoming strict join,
and literal pure-coalition best responses. Sections 3--4 use precisely these
extra fields to reduce every nonterminal move to the alternating
triple--pair swap. What remains after that use is the finite horizontal
holonomy below.

## 9. Global bypass through pure-time deadline rank

Every \(O(e,j)\) vertex is an actual canonical pure-time profile: three
players Quit at date zero and the excluded player plays Never. It therefore
instantiates `pureTimeMinimum_exists_offMinimumPaidPort` with minimum debt
\(D_*\).

Concretely, fix one triple member as anchor and replace the other two
date-zero Quit strategies by Never, one at a time. If an intermediate pair
or singleton sibling has total debt above \(D_*\), it is already an actual
off-minimum pure-clock target with literal ancestry from \(O(e,j)\).

If both erasures stay at the minimum, the last sibling is a singleton
profile. Its owner \(b\) has

\[
 U_b=s_b,\qquad B_b=\max\{s_b,0\}.
\]

The singleton margin \(D_*\le B_b-s_b\) forces \(s_b<0\), so Never is an
exact response of gain at least \(D_*\) and its target is all-Never.
All-Never cannot be a positive global minimum: if every \(s_i<0\), its total
debt is zero; if some \(s_i\ge0\), the singleton margin at all-Never would
read \(D_*\le\max\{0,s_i\}-s_i=0\).

Thus every oriented triple has a finite literal pure-time replacement
ancestry to an off-minimum target. At that target a maximum-debt coordinate
has an exact pure-time or Never cap response of gain

\[
 \frac{D(\text{target})}{4}>\frac{D_*}{4},
\]

with the checked paid first-disagreement row. Intermediate erasures need not
be profitable; they retain source provenance but are not claimed to be a
Nash--Bellman chronology.

This is a genuine chamber contraction:

\[
 \boxed{\text{oriented minimum triple}
   \Longrightarrow \text{source-faithful off-minimum paid port}.}
\tag{9.1}
\]

The following automaton and holonomy remain correct descriptions of one
possible horizontal selector. They are not needed to exit the minimum fibre
and should not be treated as frontier nodes.

## 10. Exact holonomy around a closed swap orbit

Let \(\sigma_0,\ldots,\sigma_L=\sigma_0\) be the alternating sequence of
triple and pair profiles in one periodic orbit. Write \(i_t\) for the mover
on \(\sigma_t\to\sigma_{t+1}\), and

\[
 g_t=U_{i_t}(\sigma_{t+1})-U_{i_t}(\sigma_t)
     =d_{i_t}(\sigma_t)>0.
\]

Every target kills its mover's debt and every displayed state has total debt
\(D_*\). Therefore each edge has the exact leakage identity

\[
 \sum_{k\ne i_t}
   \bigl(d_k(\sigma_{t+1})-d_k(\sigma_t)\bigr)=g_t.
\tag{10.1}
\]

Fix a player \(j\), and let

\[
 G_j=\sum_{t:i_t=j}g_t.
\]

On a move by \(j\), its opponents are unchanged, so its cap is unchanged and
its payoff rises by \(g_t\). Since both payoff and cap return after one full
period, summing only the non-\(j\) moves gives

\[
\begin{aligned}
\sum_{t:i_t\ne j}\Delta U_j(t)&=-G_j,\\
\sum_{t:i_t\ne j}\Delta B_j(t)&=0,\\
\sum_{t:i_t\ne j}\Delta d_j(t)&=G_j.
\end{aligned}
\tag{10.2}
\]

Thus every player's own positive gains are paid exactly by payoff losses and
debt reactivation while other players move. This is stronger than a bare
support cycle, but it is conservative holonomy: all signed changes close.
Global-minimum equality makes every one-player chord between consecutive
vertices a minimum chord and makes the nonmover cap coordinates affine along
that chord. Indeed, prescribed payoffs are affine in the changed player's
stopping-law mixture, while every nonmover cap is convex. Each coordinate
debt is therefore bounded above by its endpoint interpolation. Global
minimality and equality of the two endpoint debt sums force the total Jensen
gap to vanish; the coordinatewise nonnegative gaps must then all vanish.
It supplies no strict slack in (10.1)--(10.2), so neither an old
zero nor an old cap face is preserved around the period.

In particular, the holonomy does not yield a zero-preserving response. The
coordinate killed when its owner moves must recover exactly its total loss
before that player moves again.

## 11. Positive-minimum singleton pressure and its limit

Global minimality does add information missing from a generic response
cycle. At every displayed minimum vertex \(M^S\), the checked singleton
margin gives

\[
 B_i(M^S)-s_i\ge D_*,
 \qquad s_i:=r_i(\{i\}).
\tag{11.1}
\]

Since every player is punishment-normal in the hard residual, the strict
minimum-fibre separation also gives

\[
 r_i(S)=U_i(M^S)>s_i
 \qquad(i\in I).
\tag{11.2}
\]

For an edge \(S\to S'\) moved by \(i\), put
\(g_i=r_i(S')-r_i(S)=d_i(M^S)\). The target has zero \(i\)-debt, so

\[
 r_i(S')=B_i(M^S)=B_i(M^{S'}),
 \qquad
 r_i(S)\ge s_i+D_*-g_i,
 \qquad
 r_i(S')\ge s_i+D_*.
\tag{11.3}
\]

These inequalities do not acquire a sign after summing around the orbit.
For each player, its own moves raise its payoff by \(G_i\), while the moves
of the other players lower it by exactly \(G_i\), as in (10.2). All visited
payoffs can remain strictly above \(s_i\) throughout that oscillation. The
minimum margin therefore supplies a floor, not a monotone quantity.

Punishment normality also does not change the orientation: (11.2) implies
that every visited payoff is strictly individually rational relative to the
punishment vector, but the profitable response at the vertex remains. An
average of the visited terminal laws would be a correlated individually
rational object; ordinary independent behavioral play supplies no public
randomizer which realizes that average while preserving its incentive
comparisons.

The exact regression below satisfies (11.1), with the displayed fibre value
read as one, and satisfies (11.2) and punishment normality at every displayed
vertex. Its true global minimum is nevertheless zero. Hence the finite
inequalities (11.1)--(11.3), punishment normality, and equal displayed debt
do not by themselves express the missing global-minimum pressure. Any
successful use of \(D_*>0\) must exclude a lower semantic point elsewhere in
the carrier or construct a source-compatible temporal edge; it cannot be a
sum of the displayed reward inequalities alone.

## 12. Exact six-vertex regression for the finite holonomy

The algebraic obstruction in Section 10 is realizable by a four-player reward
table, although the example has global minimum zero and therefore is not a
counterexample to UE.

Let players be \(0,1,2,3\). Start with every reward coordinate equal to zero.
Give the response cycle the six values

\[
 r_0(\{1,3\})=r_0(\{0,2,3\})=1,
\quad
 r_1(\{2,3\})=r_1(\{0,1,3\})=1,
\quad
 r_2(\{0,3\})=r_2(\{1,2,3\})=1.
\tag{12.1}
\]

To impose the positive-minimum singleton inequalities at the displayed
vertices, additionally set

\[
\begin{aligned}
r_0(\{0\})=r_0(\{1\})=r_0(\{0,1\})&=-2,\\
r_1(\{1\})=r_1(\{2\})=r_1(\{1,2\})&=-2,\\
r_2(\{2\})=r_2(\{0\})=r_2(\{0,2\})&=-2,\\
r_3(\{3\})=r_3(\{0,1,2\})=r_3(I)&=-4.
\end{aligned}
\tag{12.2}
\]

The six pure profiles

\[
\begin{aligned}
\{1,2,3\}&\to\{2,3\}\to\{0,2,3\}\to\{0,3\}\\
&\to\{0,1,3\}\to\{1,3\}\to\{1,2,3\}
\end{aligned}
\tag{12.3}
\]

form an alternating strict response cycle. The movers are respectively
\(1,0,2,1,0,2\), and every gain equals one. Direct use of the pure-coalition
debt formula gives the debt vectors

\[
\begin{array}{c|c}
\text{coalition}&(d_0,d_1,d_2,d_3)\\ \hline
\{1,2,3\}&(0,1,0,0)\\
\{2,3\}&(1,0,0,0)\\
\{0,2,3\}&(0,0,1,0)\\
\{0,3\}&(0,1,0,0)\\
\{0,1,3\}&(1,0,0,0)\\
\{1,3\}&(0,0,1,0).
\end{array}
\tag{12.4}
\]

Thus every displayed vertex has total debt one, every triple has the two
oriented zero coordinates, and (10.1)--(10.2) hold exactly. Player \(3\) is a
persistent passive background.

At every displayed vertex, every prescribed payoff is \(0\) or \(1\), while
the own singleton rewards are \((-2,-2,-2,-4)\). Hence strict singleton
separation holds. Every displayed cap is at least one above the corresponding
own singleton reward, so (11.1) holds with the nominal value \(D_*=1\).

The table is also punishment-normal. To punish player \(0\), let player
\(1\) Quit surely: both \(r_0(\{1\})\) and \(r_0(\{0,1\})\) equal \(s_0\).
Use player \(2\) analogously for player \(1\), and player \(0\) for player
\(2\). To punish player \(3\), let players \(0,1,2\) Quit surely; both
\(r_3(\{0,1,2\})\) and \(r_3(I)\) equal \(s_3\). These stationary opponent
plans show that each punishment value is at most the own singleton reward.

Nevertheless all-Never has payoff and unrestricted caps equal to zero,
because every own singleton reward is negative and Never pays zero. The true
global minimum is therefore zero. This regression shows that finite
coalition geometry, exact equal-fibre holonomy, both checked singleton
inequalities, punishment normality, and the two-zero triple pattern are
mutually consistent. A contradiction must use positive global minimum in a
way stronger than merely declaring the six displayed debts equal and applying
the vertexwise singleton theorems.

## 13. Consequence for the Fin4 frontier

The alternating horizontal orbit needs no separate consumer. Section 9 exits
from any one of its vertices before following that selector. The retained
output is exactly the already universal object:

> an actual off-minimum pure-clock profile, a literal finite ancestry from
> the supplied minimum source, and an outgoing unrestricted cap-attaining
> pure-time/Never response with gain \(>D_*/4\) and a paid
> first-disagreement row.

What remains open is to consume that off-minimum paid port by a charged
Nash--Bellman return, a renewable source rank, or a contradiction. Nothing in
the horizontal holonomy itself supplies that consumer.

## 14. Checked sources inspected

- `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/PairBaseStationaryTwoDebtorHandoff.lean`;
- `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/PairBasePaidResetAlignment.lean`;
- `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/PairBasePaidResetCapRigidity.lean`;
- `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/StationaryPaidCarrierLinearDebtMoat.lean`;
- `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/RobustJoinPredecessorBase.lean`;
- `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/RobustJoinStrictBackgroundReversal.lean`;
- `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPositiveMinimumUnitResetCycle.lean`;
- `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticAuxiliaryNashBudget.lean`;
- `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticMinimumLawFiniteAtom.lean`;
- `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFixedLawCapRigidity.lean`;
- `UniformEquilibrium/Diagnostics/Quitting/PureTimeMinimumPaidPort.lean`;
- `Research/Quitting/SameStageEndpointMonodromyImpossible.lean`; and
- `UniformEquilibrium/Quitting/Bellman/Finite/PunishmentFloorAdmissibleChargedRelation.lean`.

## 15. The obvious induced-base descent fails immediately

For completeness, the most obvious attempt to consume the *selected*
horizontal orbit internally does fail, even though Section 9 bypasses the
orbit globally.

One might try to select an induced Nash point over a visited pair base \(P\)
and prove that its total debt is below \(D_*\). The orbit itself blocks that
argument. In the macro \(O(e,j)\to O(m,e)\), use \(P\) as the sure-Quit base
and \(e,m\) as the two free players. The successor triple

\[
 M^{I\setminus\{m\}}=M^{P\cup\{e\}}
\]

is already an exact induced Nash point:

* \(e\) strictly prefers Quit, by the pair-to-triple gain \(D_*\); and
* \(m\) weakly prefers Continue, because the successor state's excluded
  coordinate has zero debt.

The second comparison can be made strict by choosing
\(r_m(I)<r_m(I\setminus\{m\})\). Hence the binary induced game may simply
return the literal minimum triple, with total debt still \(D_*\). Existence
or fresh selection of an induced pair-base Nash point cannot consume the
orbit.

Thus pair-base compactness alone only renames the same triple. No further
internal selector analysis is needed for the minimum-fibre atlas, because the
checked pure-time deadline rank already supplies the source-matched
deformation to the off-minimum paid port.
