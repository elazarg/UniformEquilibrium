# Concentrated singleton to a source-matched full-gap toggle cycle

Author: ATLAS_FALSIFIER

Status: **proved finite source-preserving horizontal adapter and a
full-gap transition from every exceptional directed class to one literal
same-source response rectangle; the required all-behavior rectangle consumer
is still open.** This note does not answer
questions/FIN4_ATLAS_CONCENTRATED_SINGLETON.md: its output is a horizontal
same-stage cycle, not a terminal approximant, uniform payoff, or well-founded
atlas descent.

## Question

Let \(r\) be a quitting reward table on Fin 4 carrying a
FinFourQuantitativeFullSupportHardResidual, with terminal gap
\(\gamma>0\). Suppose one actual behavioral profile \(\sigma\), one date
\(t\), and one player \(o\) satisfy

\[
 \lambda\le
 \Pr_\sigma(\text{the terminal coalition at date }t\text{ is }\{o\}),
 \qquad \lambda>0.
\tag{1}
\]

Assume the complete live-root tail strictly after \(t\) is retained as source
provenance. Can the singleton be consumed without first producing a recurrent
packet or aligning an independently selected stationary source?

The finite result below gives a literal, uniformly paid endpoint cycle on the
same row. It is not temporal recurrence: the missing step is chronological
consumption of that horizontal cycle.

## Sources inspected

- FinFourAtlasConcentratedSingletonEndpoint and its stage-mass and
  post-date-tail fields in
  Research/Quitting/FinFourProducerAtlas/SemanticConnections.lean;
- literal one-date and pure-root routing in
  Research/Quitting/SameStageEndpointMonodromy.lean;
- FinFourQuantitativeFullSupportHardResidual.exists_terminalGap_collision_at_singleton
  in
  UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/PunishmentNormalAtomicCollisionHandoff.lean;
- QuittingTerminalExploitabilityWitness.exists_leave_or_join_gain and
  QuittingTerminalExploitabilityWitness.not_isQuittingSureExitSet in
  UniformEquilibrium/Quitting/Classification/TerminalExploitabilityToggles.lean;
- quittingContinuationBestResponseValue_pureSetRoot_eq and
  quittingTerminalSemanticDebt_pureSetRoot_eq in
  UniformEquilibrium/Quitting/Paths/SureExitSet.lean;
- pure-set payoff and endpoint identities in
  UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/StaticCycleChronologyBarrier.lean;
- the reviewed same-stage finite regeneration in
  formalized/SAME_STAGE_ENDPOINT_MONODROMY_REDUCTION.md.

## 1. Purifying the displayed singleton costs no marked mass

Write \(x\) for the live product root of \(\sigma\) at \(t\), and \(L\) for
the probability of reaching \(t\). Equation (1) says

\[
 L\,x_o(Q)\prod_{j\ne o}x_j(C)\ge\lambda.
\tag{2}
\]

Change, only at date \(t\), \(o\)'s action to pure Quit and every other
player's action to pure Continue. Call the resulting actual profile
\(\rho_{\{o\}}\). Its complete past and complete post-\(t\) behavior are
literally those of \(\sigma\), while

\[
 \Pr_{\rho_{\{o\}}}(\{o\}\text{ at }t)=L\ge\lambda.
\tag{3}
\]

This is just repeated Boolean-cylinder routing in the direction of the
already positive singleton cylinder: dividing by each old coordinate
probability cannot decrease its mass. No endpoint sign and no Nash assertion
is used during this preliminary purification.

More generally, for every nonempty coalition \(A\subseteq\operatorname{Fin}4\),
let \(\rho_A\) be the actual profile with the same behavior as \(\sigma\) at
every date other than \(t\), and pure quitting coalition \(A\) at \(t\).
Every \(\rho_A\) has the same literal past, reach \(L\), and post-date tail,
and its marked stage mass is exactly \(L\).

## 2. Every nonempty pure coalition has a full-gap nonempty toggle

Define the finite membership payoff at \(A\ne\varnothing\) by

\[
 u_i(A)=r_i(A).
\]

For \(i\in\operatorname{Fin}4\), its toggle gain at \(A\) is

\[
 g_i(A)=r_i(A\mathbin\triangle\{i\})-r_i(A),
\tag{4}
\]

provided \(A\mathbin\triangle\{i\}\ne\varnothing\).

### Nonsingleton vertices

If \(|A|\ge2\), prescribe \(A\) as the pure quitting coalition at date zero.
After any unilateral behavioral deviation, at least one prescribed member of
\(A\) still Quits at date zero. Thus absorption remains immediate and every
arbitrary behavioral deviation collapses to the deviator's binary date-zero
choice. The terminal exploitability witness therefore supplies \(i\) with

\[
 g_i(A)\ge\gamma.
\tag{5}
\]

The toggled coalition remains nonempty because \(|A|\ge2\).

This is already checked for unrestricted behavioral deviations. In
`UniformEquilibrium/Quitting/Paths/SureExitSet.lean`,
`quittingContinuationBestResponseValue_pureSetRoot_eq` identifies the full
behavioral cap at a pure-set profile with the maximum of the two membership
endpoints, and `quittingTerminalSemanticDebt_pureSetRoot_eq` records the debt
formula. Applying the witness is packaged by
`QuittingTerminalExploitabilityWitness.exists_leave_or_join_gain` in
`UniformEquilibrium/Quitting/Classification/TerminalExploitabilityToggles.lean`.
Its companion theorem
`QuittingTerminalExploitabilityWitness.not_isQuittingSureExitSet` is the
qualitative no-sink form. Thus "deviations collapse" here refers to a checked
all-behavior cap identity, not to a restriction of the deviation class.

### Singleton vertices

If \(A=\{o\}\), punishment normality and the terminal witness give a distinct
collider \(c(o)\ne o\) satisfying

\[
 r_{c(o)}(\{o,c(o)\})-r_{c(o)}(\{o\})\ge\gamma.
\tag{6}
\]

Thus the prescribed toggle at a singleton is always the join
\(\{o\}\to\{o,c(o)\}\), never the empty-coalition leave.

The exact checked declaration is
`FinFourQuantitativeFullSupportHardResidual.exists_terminalGap_collision_at_singleton`
in
`UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/PunishmentNormalAtomicCollisionHandoff.lean`.
It uses the hard residual's punishment normality to rule out the singleton
owner's empty toggle. This extra input is why the generic
`exists_leave_or_join_gain` theorem alone does not keep the orbit inside the
nonempty cube.

Combining (5) and (6), every nonempty Boolean vertex has a nonempty outgoing
toggle of gain at least \(\gamma\).

## 3. Literal same-stage realization and finite closure

Choose one such outgoing toggle \(F(A)\) for every nonempty \(A\). Starting
from \(A_0=\{o\}\), define \(A_{k+1}=F(A_k)\). Since there are only fifteen
nonempty coalitions, a repeated vertex occurs after at most sixteen visits.
The minimal repeated segment gives

\[
 A_s,A_{s+1},\ldots,A_{s+K}=A_s,
 \qquad K\in\{4,6,8,10,12,14\}.
\tag{7}
\]

Indeed, the nonempty four-cube is bipartite with eight odd-cardinality and
seven even-cardinality vertices, so a simple cycle has even length at most
fourteen. Length two would traverse the same player's membership comparison
strictly in both directions, contradicting positivity of the two gains.

Realize every vertex by \(\rho_{A_k}\) and every edge by the corresponding
literal one-date pure endpoint update at date \(t\). The actual terminal
payoff gain of its mover is exactly the common reach times the table gain:

\[
 U_{i_k}(\rho_{A_{k+1}})-U_{i_k}(\rho_{A_k})
 =L\,g_{i_k}(A_k)
 \ge \lambda\gamma.
\tag{8}
\]

All profiles have the same complete past and same complete post-\(t\) tail.
Every displayed stage atom has mass \(L\ge\lambda\). Repetition of the
coalition is therefore equality of complete behavioral profiles, not merely
of their semantic pairs.

Because an own-strategy replacement leaves that player's unrestricted
behavioral cap unchanged, every edge also satisfies the exact debt identity

\[
 d_{i_k}(\rho_{A_{k+1}})
 =
 d_{i_k}(\rho_{A_k})-
 \bigl[U_{i_k}(\rho_{A_{k+1}})
       -U_{i_k}(\rho_{A_k})\bigr].
\tag{9}
\]

Consequently each debt coordinate telescopes around the literal cycle, and
the mover losses are exactly replenished by externalities from other moves.

### Proposed declaration shape

    theorem FinFourAtlasConcentratedSingletonEndpoint.nonempty_fullGapToggleCycle
        (endpoint : FinFourAtlasConcentratedSingletonEndpoint source) :
        Nonempty
          (QuittingSameStageNonemptyFullGapToggleCycle
            reward endpoint.profile endpoint.stage
            endpoint.low.lambda source.residual.witness.terminalGap)

For the minimum-singleton clock-compression origin, the same statement uses
its actual reference profile, marked date, and positive stage floor instead
of endpoint.low. No low-tail inequality is needed.

## 4. Why this is not yet the requested consumer

The cycle is horizontal. Every vertex is a sibling obtained by changing the
root at one common date above one common tail. It is not an ordered
Nash--Bellman chronology:

\[
 z^+\xrightarrow{A_k}\operatorname{Sem}(\rho_{A_k}),
 \qquad
 z^+\xrightarrow{A_{k+1}}\operatorname{Sem}(\rho_{A_{k+1}}).
\]

A pure nonempty root absorbs at its date. Conditional play therefore cannot
visit two vertices of (7). The checked static-cycle chronology barrier
applies literally. Diluting a nonsingleton root destroys its first-order
coalition content under product independence; it does not turn (7) into a
small-error vertical cycle.

Nor does (9) give a well-founded rank. Total debt may rise on some edges and
fall on others, and returns exactly after one turn. Selecting a minimum-debt
vertex of the finite cycle merely makes its outgoing total-debt change
nonnegative. Positive mover-debt loss can be exactly offset by new debt in
other coordinates. No support containment follows.

Thus this theorem removes the singleton as a *finite source-provenance* dead
end, but it does not meet any accepted output of
FIN4_ATLAS_CONCENTRATED_SINGLETON. The remaining question is whether the
extra fact that the cycle is attached to the original concentrated source
and has the uniform full-gap scale \(\lambda\gamma\) can yield:

1. a punishment-floor chronology with positive cumulative charge;
2. a minimum-fiber endpoint with strict no-new-support descent; or
3. a scale-free obstruction contradicting the positive terminal gap.

No such implication is proved here.

## 5. Geometry audit: not an existing atlas monodromy leaf

The checked common-host/complementary-pair classifier in
`Research/Quitting/FinFourProducerAtlas/Leaves.lean` is reached only after
partial purification stays inside `QuittingNonsingletonCoalition (Fin 4)`.
Its simple closed trace therefore contains no singleton. The orbit constructed
here is on the larger set of **all nonempty** coalitions. The singleton
collider prevents an empty vertex, but it does not prevent later singleton
vertices.

Consequently the present cycle need have neither checked geometry. At the
Boolean level, for example,

\[
 \{0\}\to\{0,1\}\to\{1\}\to\{1,2\}\to
 \{2\}\to\{0,2\}\to\{0\}
\tag{10}
\]

is a simple nonempty toggle cycle. Its total intersection is empty, so it has
no common host. Its only pair vertices are
\(\{0,1\},\{1,2\},\{0,2\}\), and no two are complements in `Fin 4`.
Nothing in the full-gap choice above rules out this geometry.

Therefore the theorem does **not** map the concentrated-singleton node into
either `FinFourCommonHostMonodromyProducer` or
`FinFourComplementaryPairMonodromyProducer`. Its fresh content relative to
the previously known table-level strict-toggle cycle is the actual-data
adapter: fixed reach, fixed full-gap stage gain, literal common past and tail,
and applicability to the clock-compressed origin. It should be represented,
if desired, as an enlarged generic horizontal nonempty-toggle node.

Counting it as a genuine atlas contraction requires one further result:

1. prove that hard-residual reward inequalities forbid singleton-containing
   geometries such as (10); or
2. consume arbitrary source-matched nonempty toggle cycles.

Absent one of these, it remains a horizontal producer lemma, not a reduction
to the existing monodromy leaves.

### Exact finite geometry beyond the existing leaves

There is nevertheless a small exhaustive enlargement. Let (C) be a simple
cycle in the nonempty four-cube and suppose (C) contains a singleton. Then
one of the following holds:

1. (C) has a common host;
2. (C) contains two complementary two-element coalitions; or
3. after forgetting direction, and up to relabeling and cyclic rotation, the
   support of (C) is one of the following five unoriented patterns

\[
\begin{array}{ll}
G_6^0:&a-ab-b-bc-c-ac-a,\\
G_6^1:&a-ab-b-bc-abc-ac-a,\\
G_8^0:&a-ab-b-bc-abc-abcd-acd-ac-a,\\
G_8^1:&a-ab-b-bc-bcd-abcd-acd-ac-a,\\
G_8^2:&a-ab-abc-bc-bcd-abcd-acd-ac-a.
\end{array}
\tag{11}
\]

Here juxtaposition denotes a coalition. A short proof uses only the parity
bipartition. If a four-cycle contains a singleton, its square has a fixed
singleton coordinate and hence a common host. If neither of the first two
outcomes holds, at most one pair may be used from each of the three
complementary pair classes. Thus there are at most three pair vertices. If
the grand coalition is absent, a non-common-host cycle must have length six;
the three pair vertices must form a triangle rather than a star, and the odd
intermediate vertices give exactly (G_6^0,G_6^1). If the grand coalition is
present, a length-six singleton cycle again has a common host. A remaining
cycle has length eight; its three pairs must again form a triangle, and the
four odd intermediates give exactly the three (G_8) patterns. This is a
finite Boolean classification, not a semantic consumer.

Direction cannot simply be forgotten in the payoff problem. Restoring the
orientation gives **seven** directed classes up to relabeling and cyclic
rotation: (G_6^0,G_6^1,G_8^1) are equivalent to their reversals after a
relabeling, while each of (G_8^0) and (G_8^2) has two chiral directed
forms. Thus (11) is a five-support mnemonic, not a five-class directed
classification.

### The first exceptional geometry is not automatically balanced or robust

The hard-residual collision signs and the impossibility of traversing one
cube edge strictly in both directions do not collapse (G_6^0) to the
currently compiled balanced chamber. Here is an exact sign regression.
Take labels (a,b,c,d), choose (K>1), and give every active player
(i\in\{a,b,c\}) payoff zero on every coalition containing (i). Write

\[
 \delta_i(R)=q_i-r_i(R)
\]

for the membership gain in opponent context (R). Set

\[
\begin{array}{lll}
\delta_a(\{c\})=1,&\delta_a(\{b\})=-K,&
  \delta_a(\{b,c\})=-K,\\
\delta_b(\{a\})=1,&\delta_b(\{c\})=-K,&
  \delta_b(\{a,c\})=-K,\\
\delta_c(\{b\})=1,&\delta_c(\{a\})=-K,&
  \delta_c(\{a,b\})=-K.
\end{array}
\tag{12}
\]

These signs orient exactly

\[
a\to ab\to b\to bc\to c\to ac\to a.
\]

For an interior stationary root with active quit rates (p_a,p_b,p_c), the
three membership equations are

\[
\begin{aligned}
H_a&=p_c(1-p_b)-Kp_b=0,\\
H_b&=p_a(1-p_c)-Kp_c=0,\\
H_c&=p_b(1-p_a)-Kp_a=0.
\end{aligned}
\tag{13}
\]

They would imply (p_c>Kp_b>K^2p_a>K^3p_c), impossible. Moreover every
positive singleton join in the directed player triangle has a strict
background reversal: the corresponding two-opponent value in (12) is
(-K). Hence the supplied cycle is not a `QuittingRobustJoin` cycle either.

For completeness this is a full Fin4 reward table, not merely a partially
specified three-player sign system. For active (i), if (i\notin S) and
(d\notin S), put (r_i(S)=-\delta_i(S)) using (12) (with the unused empty
case set to zero). If (i\notin S) and (d\in S), put (r_i(S)=K), so every
such membership gain is (-K). Put (r_d(S)=0) for every nonempty (S).
Together with the already specified zero payoffs on coalitions containing the
recipient, this defines all nonempty-coalition reward coordinates. Setting
(p_d=0) recovers exactly (13). The passive fourth player also makes clear why
this is only a local sign regression: the table has obvious equilibrating
features and is not a positive-gap candidate.

This regression does not satisfy, and does not purport to satisfy, the full
positive-gap hard-residual premises. Its role is narrower: neither Boolean
geometry, strict opposite-edge impossibility, nor the local collision signs
alone force the balanced stationary or robust-join consumer. Any such
contraction must use additional hard-residual/source information.

## 6. A source-matched response rectangle is forced

Although the seven exceptional directed classes are not automatically
balanced or robust, they are not seven unrelated strategic residuals.  Their
strict edge gains have positive discrete curl, and the curl can be localized
on one literal two-coordinate face without changing the marked source row.

For an oriented add-edge (A\to A\cup\{i\}), put

\[
 \omega(A,i)=r_i(A\cup\{i\})-r_i(A).
\tag{14}
\]

Use antisymmetry for the reverse edge.  The integral of this one-cochain
around the directed cycle is the sum of its mover gains, hence at least
(K\gamma).

For nonempty (A) and distinct (i,j\notin A), orient the Boolean square

\[
 Q(A;i,j):
 A\to Ai\to Aij\to Aj\to A.
\]

Its circulation splits into two common-response cross-differences:

\[
 \begin{aligned}
 \int_{Q(A;i,j)}\omega
 ={}&[\omega(A,i)-\omega(Aj,i)]\\
   &+[\omega(Ai,j)-\omega(A,j)].
 \end{aligned}
\tag{15}
\]

Thus if an oriented square has circulation at least (2c), one of the two
players has a fixed endpoint response whose gain changes by at least (c)
when the other player's endpoint is changed.

For the five unoriented supports in (11), the following signed fillings use
only squares whose four vertices are nonempty:

\[
\begin{array}{ll}
G_6^0:& Q(a;b,c)-Q(b;a,c)+Q(c;a,b),\\
G_6^1:& Q(a;b,c)-Q(b;a,c),\\
G_8^0:& Q(a;b,c)-Q(b;a,c)+Q(ac;b,d),\\
G_8^1:& Q(a;b,c)-Q(b;a,c)+Q(ac;b,d)-Q(bc;a,d),\\
G_8^2:& Q(a;b,c)+Q(ac;b,d)-Q(bc;a,d).
\end{array}
\tag{16}
\]

The boundary check is literal.  For example,

\[
\begin{aligned}
\partial Q(a;b,c)
  &=a-ab-abc-ac-a,\\
\partial[-Q(b;a,c)]
  &=b-bc-abc-ab-b,\\
\partial Q(c;a,b)
  &=c-ac-abc-bc-c.
\end{aligned}
\]

Adding these three rows cancels every edge incident with \(abc\) and leaves
\(G_6^0\).  For \(G_6^1\), the first two rows already leave its displayed
hexagon.  The additional boundaries are

\[
\begin{aligned}
\partial Q(ac;b,d)&=ac-abc-abcd-acd-ac,\\
\partial[-Q(bc;a,d)]&=bc-bcd-abcd-abc-bc.
\end{aligned}
\]

Adding them with the signs shown in (16) gives \(G_8^0,G_8^1,G_8^2\)
respectively; all internal edges occur twice with opposite signs.  Thus the
fillings do not rely on an unlisted diagonal or on the empty coalition.

Their boundaries are therefore respectively the displayed cycles in (11).  Reversing
a directed class negates the whole filling and changes nothing below.  The
numbers of signed squares are (3,2,3,4,3), while the cycle lengths are
(6,6,8,8,8).  Hence some signed square has circulation at least
((K/N)\gamma\ge2\gamma).  By (15), one of its two common-response
cross-differences is at least (gamma).

Now realize all four corners by the profiles (\rho_A) from Section 1.  The
square base is nonempty, so all four pure roots absorb at the marked date.
The selected observer uses one fixed one-date endpoint action on both source
corners; the other square coordinate uses one fixed endpoint action as well.
Consequently the actual payoff cross-difference is exactly (L) times the
table cross-difference and is at least

\[
 \boxed{\lambda\gamma}.
\tag{17}
\]

Every corner has the same literal past, marked-date reach (L), and complete
post-date tail.  This is therefore a genuine actual-data response rectangle,
not an independently selected reward-table square.

There is also a geometry-free weaker version.  Cone every edge of an arbitrary
nonempty Fin (n) cube cycle to `univ` by adding the missing coordinates in
one fixed order.  Commuting the toggled coordinate through that word fills
each edge loop with at most (n-1) nonempty squares.  Cancellation of the
cone paths gives a filling of the whole cycle with ℓ1 norm at most
(K(n-1)).  Thus a cycle with every gain at least (gamma) has a
source-matched response rectangle of cross-difference at least
(gamma/(2(n-1))); for Fin4 this is (gamma/6).  Formula (16) gives the
sharper full-gap scale for the seven exceptional directed classes.

This is a real source-preserving transition, but not yet a consumer accepted
by the concentrated-singleton question.  Existing vanishing-debt rectangle
interfaces require near-minimum and tangent provenance that the purified
corners do not possess.  Positive common-response curvature at one literal
square therefore cannot presently be promoted to a cumulative exact path or
minimum-fiber rank drop.  The new finite target is:

\[
 \boxed{
 \text{exceptional singleton toggle cycle}
 \Longrightarrow
 \text{same-source full-gap response rectangle}.}
\]

The remaining theorem is to consume this actual rectangle without importing
the absent near-minimum recipient-transfer hypothesis.

## 7. Retaining an incentive-aware paid pair through the finite dispatch

The owner-debt estimate from incentive-aware singleton clock compression is
not stable under the purification in Section 1.  The paid pure-time pair can,
however, be retained in a weaker but exact way.  It produces a finite
dichotomy in which the paid observer is attached either to the terminal
toggle class or to the response rectangle itself.

Assume this endpoint comes from the minimum-singleton clock-compression
origin.  Let (j) be the forced singleton owner, let (o\ne j) be the fixed
observer supplied by the terminal-gap wrapper, and let (s,r) be its two pure
times.  For the compressed profile (\tau),

\[
 F(x_{-o}):=
 U_o(\tau[o\leftarrow Q_r])-
 U_o(\tau[o\leftarrow Q_s])\ge\gamma .
\tag{18}
\]

Here only the opponents' product root at the marked date is displayed.  With
the complete past and tail fixed, each pure-time payoff is multi-affine in
that root, so (F) is multi-affine as well.  Round the opponents' coordinates
one at a time, at every step choosing an endpoint which does not decrease
(F).  The owner coordinate is already pure Quit and is not changed.  Finally
set the observer's own prescribed marked action to pure Quit.  This last
change does not change either deviation payoff, because both deviations
replace the observer's entire strategy.

The result is a pure sibling (\rho_{A_0}) with

\[
 \{j,o\}\subseteq A_0,
 \qquad |A_0|\ge2,
 \qquad F(A_0)\ge\gamma .
\tag{19}

It retains the common past, reach, and post-date tail.  Reapplying the paid-row
constructor to the same two pure times gives a paid row at the literal
(\rho_{A_0}); no continuity of the cap is used.

Now form the directed graph containing only the nonempty toggle edges whose
table gain is at least (\gamma).  Sections 2--3 show that every vertex has an
outgoing edge.  Choose a shortest directed path

\[
 A_0,A_1,\ldots,A_N
\]

from (A_0) into a terminal strongly connected component of this graph.  It is
simple, so (N\le14).  Evaluate the same fixed response pair at every pure
sibling and write its payoff difference as (F(A_k)).

There are two cases.

### Paid terminal class

If

\[
 F(A_N)\ge\gamma/2,
\tag{20}
\]

then the terminal class contains a literal profile carrying the same paid
pair with gain (\gamma/2).  Every vertex of this terminal class lies on a
directed cycle, so the output is a source-matched full-gap toggle cycle with
a paid vertex.  The marked root of that vertex is pure nonempty and has mass
(L\ge\lambda).

### Paid-observer response square

Otherwise let (k) be the first index with (F(A_k)<\gamma/2).  The total drop
before that first crossing is larger than (\gamma/2), and (k\le14).
Consequently some edge (A_q\to A_{q+1}) on this prefix satisfies

\[
 F(A_q)-F(A_{q+1})\ge {\gamma\over 2k}
 \ge {\gamma\over28},
 \qquad F(A_q)\ge\gamma/2.
\tag{21}
\]

Let (p) be the mover of this edge.  Necessarily (p\ne o), since changing the
observer's prescribed marked action does not change the payoff of either
pure-time deviation.  The four profiles obtained by combining

* the two pure marked actions of (p) from (A_q,A_{q+1}); and
* the two fixed complete pure-time responses (Q_s,Q_r) of (o)

form a literal commuting response square.  In the appropriate orientation
its observer-payoff cross-difference is at least (\gamma/28), exactly by
(21).  Its source base profile (\rho_{A_q}) simultaneously carries:

\[
 \text{a paid row for }o\text{ of gain }\gamma/2,
 \qquad
 \text{an endpoint edge for }p\text{ of actual gain }L\gamma,
 \qquad
 \text{marked mass }L\ge\lambda.
\tag{22}

The first-disagreement date of the paid row is still no later than the old
forced singleton deadline.  This uses only the unchanged witnesses: at the
compressed endpoint the forced owner showed that the two selected pure times
could not both lie after the deadline, and the paid-row constructor defines
`start` from the earlier of those same two times.  Later removal of the owner
can change their payoff values, but not their dates; positivity at the new
base is supplied separately by (21).

This finite dichotomy is stronger than merely saying that some square in the
cycle has nonzero curl: it fixes the square observer to the original paid
observer, uses the original response pair, and puts a paid row at the square's
source base.  It also explains exactly what multi-affinity can and cannot
retain.  The complete response-square corners replace (o)'s whole strategy,
so they need not retain the marked atom themselves; the atom and paid row are
co-realized at the base profile (\rho_{A_q}).

Neither output is yet a chronological consumer.  Existing normalized
curvature decoders require one response to be quantitatively near the cap at
the relevant square endpoint.  A paid difference (V_r-V_s\ge\gamma/2) gives
no upper bound on (B-V_r), and endpoint rounding can change the maximizing
witness.  The two-player support-leak regression in
`CODEX_ROOT__INCENTIVE_AWARE_SINGLETON_CLOCK_COMPRESSION__BY_STRENGTHENER`
shows that this witness switch can be order one.  Hence the valid contraction
is

\[
 \boxed{
 \text{incentive-aware singleton endpoint}
 \Longrightarrow
 \text{paid terminal toggle class}
 \ \lor\
 \text{paid-source response square}.}
\tag{23}
\]

The remaining consumer must use the paid difference without silently
promoting it to a near-best response at the rounded endpoint.

### Exact regression against automatic near-cap promotion

The missing near-best premise is not a technical artifact.  It fails on a
literal Fin4 response square with all the local data in (22).  Use players
(o,j,p,d), let every player Continue at date zero, and at date one prescribe
(j,o) to Quit surely while (d) Never Quits.  Compare the two pure marked
actions of (p).  Take a constant (H>1), and set the relevant observer rewards
to

\[
 r_o(\{o\})=H,
 \quad r_o(\{j,o\})=1,
 \quad r_o(\{j\})=0,
 \quad r_o(\{j,o,p\})=r_o(\{j,p\})=0.
\tag{24}
\]

Set also

\[
 r_p(\{j,o,p\})=1,
 \qquad r_p(\{j,o\})=0,
\tag{25}
\]

and set unspecified coordinates to zero.  At the base marked root
(A=\{j,o\}), observer plans (Q_1) and Never differ by one.  After toggling
(p) to Quit, the same difference is zero.  Thus the literal response square
has cross-difference one, its base carries a paid row of gain one and a sure
nonsingleton atom, and the mover's marked endpoint gain is one.

Nevertheless (o)'s unrestricted cap is at least (H), attained by (Q_0), at
both endpoints.  The receiving response (Q_1) is therefore (H-1) below the
cap at the paid base.  This deficit can be arbitrarily large relative to the
square gain.  The example is not a positive-gap counterexample; it is an
exact interface separation showing that paid source plus response square plus
marked atom does not imply the approximation fields of
`QuittingStoppingLawCurvaturePaidWitness`.

## 8. Falsification requested

Please test the finite theorem, rather than the absent consumer:

1. whether pure singleton purification really retains unconditional mass
   \(L\ge\lambda\) when the source has earlier absorption and Never mass;
2. whether the nonsingleton use of the terminal gap legitimately collapses
   **all** behavioral deviations to one binary action;
3. whether the same table-level toggle gain transports to the marked date
   with exact factor \(L\), independently of the preserved tail; and
4. whether any edge can accidentally route to the empty coalition.

The conjecture-facing consumer should not be accepted unless it additionally
solves the horizontal-to-vertical or well-founded-rank problem above.
