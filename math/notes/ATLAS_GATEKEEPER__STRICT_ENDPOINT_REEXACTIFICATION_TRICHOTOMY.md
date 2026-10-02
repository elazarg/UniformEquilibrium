# Strict killed-mover endpoint re-exactification: rank, packet, or inertness

Author: `ATLAS_GATEKEEPER`

## Status

Fresh exactification of the strict off-minimum endpoint does **not** reduce
unconditionally to the already named unique-all-Continue passport point.
There is an exact source-sibling account, and the larger normalized carrier
adds one further honest branch.

Starting from the canonical forced-pair minimum source and its literal
killed-mover endpoint, normalized-passport minimization first gives either:

1. the endpoint's normalized exact-prefix orbit has a strictly off-minimum
   minimizer, and every exact root there is all Continue (the maintained
   inert normalized-passport node);
2. the closed all-prefix slice reaches the minimum fibre, producing an actual
   minimum-return concentrated packet at the routed coalition.

The second branch already enters the existing concentrated-packet consumer.
If it is obtained by an exact cap-prefix repair word, copying that word back
to the source additionally gives exactly one of:

3. exactification returns the endpoint and its copied source sibling to the
   minimum fibre, and the half stopping-law chord gives the already proved
   strict support-rank drop; or
4. exactification returns the endpoint to the minimum fibre but leaves the
   copied source sibling strictly off it.  In that case the copied repair word
   carries a fixed positive **reached cap-defect charge**.  Its amount is
   exactly the absorption payment forced by the positive minimum plus the
   sibling's strict excess.

The fourth item is not a new atlas leaf.  The minimum endpoint in both items
3--4 already supplies the packet in item 2.  The sibling charge is extra
source-matched structure inside that packet branch.  It cannot itself be
spent by an exact-path compiler, because the common word is cap--Nash on the
endpoint branch, not on the source sibling.

There is a further gate qualification.  The checked concentrated-packet
consumer returns another maintained residual, not a terminal or descent
conclusion.  Moreover, the original minimum-return forced-pair source already
has a checked concentrated collision packet.  Thus the adapter below is a
type-correct reduction of the *fresh strict endpoint exactification* to an
existing named node, but it is not by itself a well-founded atlas contraction.
Its additional value is the co-realized killed coordinate and copied-sibling
charge.  Independent review must decide whether that stronger provenance is
strictly usable downstream or merely returns to the existing node.

An exact four-player regression already shows that source-side exactness need
not survive the horizontal endpoint update.  Its global minimum is zero, so
it is a boundary no-go rather than a counterexample to the positive-minimum
conjecture.  Thus no theorem from the presently supplied local fields can
force item 3 rather than item 4, but item 4 no longer blocks the atlas
contraction to the existing packet consumer.

This is ordinary mathematics.  The one-step debt account and exact cap-stack
scaling are checked; the source-facing trichotomy is not one Lean declaration.

## 1. Input and notation

Let (D_*>0) be the global minimum total terminal-semantic debt.  Let

\[
  X_n
\]

be the canonical exact-prefix pure-pair sources from the equality arm of the
forced-pair ray.  Fix the paid mover (p), and let (E_n) be the literal
best-endpoint sibling at the shifted pure-pair row.  The canonical localization
proved in
`ATLAS_GATEKEEPER__CANONICAL_PAIR_ENDPOINT_MINIMUM_FIBER_RANK_DROP.md`
gives

\[
 D(X_n)\longrightarrow D_*,
 \qquad d_p(X_n)=g_n\ge g_0>0,
 \qquad d_p(E_n)=0.
\tag{1}
\]

The two profiles have the same strategies for every player other than (p),
the same literal prefix before the marked row, and the same literal tail after
it.  Their marked root coalitions differ by toggling (p).  After finite-label
subselection that routed coalition is fixed and nonempty, and its reached mass
has the same positive floor as the original pair atom.

Assume the strict endpoint arm

\[
 D(E_n)\longrightarrow L>D_*.
\tag{2}
\]

For each (n), let

\[
 W_n=(q_{n,0},\ldots,q_{n,h_n-1})
\]

be a finite root word which is an exact cap--Nash stack over (E_n).  Put

\[
 V_n:=W_n\triangleright E_n,
 \qquad
 U_n:=W_n\triangleright X_n,
\tag{3}
\]

and let

\[
 c_n:=\prod_{t<h_n}\operatorname{Cont}(q_{n,t}).
\tag{4}
\]

Thus (V_n) is the freshly exactified endpoint, while (U_n) is the literal
source sibling formed by copying exactly the same root word.  No root in
(W_n) is asserted cap--Nash on the (U_n) branch.

The exactification-return case is

\[
 D(V_n)\longrightarrow D_*.
\tag{5}
\]

Exact cap-stack scaling on the endpoint branch gives

\[
 D(V_n)=c_nD(E_n),
 \qquad
 d_p(V_n)=c_nd_p(E_n)=0.
\tag{6}
\]

Equations (2), (5), and (6) imply

\[
 c_n\longrightarrow c:=\frac{D_*}{L}\in(0,1).
\tag{7}
\]

The copied marked atom and the copied (p)-gain are multiplied by (c_n),
so both retain fixed positive floors.

## 2. Exact sibling-prefix defect account

View the literal word (W_n) over the source sibling as a finite prefix
chain.  At row (t), let

\[
 \Delta_{n,t}:=
   \sum_i
   \operatorname{Def}_i
      (q_{n,t};\text{the actual }U_n\text{-branch successor at }t)
\]

be its total root Nash defect, and let

\[
 s_{n,t}:=\prod_{r<t}\operatorname{Cont}(q_{n,r})
\]

be its reached weight.  Define the reached sibling charge

\[
 R_n:=\sum_{t<h_n}s_{n,t}\Delta_{n,t}\ge0.
\tag{8}
\]

The checked coordinate identity

```text
quittingTerminalSemanticDebt_prefix_eq_capDefect_add_continueMass_mul
```

and its finite telescope

```text
QuittingTerminalSemanticPrefixChain.debt_zero_eq_sum_reached_defect_add_tail
```

give, after summing the four coordinates,

\[
 \boxed{D(U_n)=R_n+c_nD(X_n).}
\tag{9}
\]

Every (U_n) is an actual profile, so global minimality gives

\[
 D(U_n)\ge D_*.
\]

Consequently

\[
 R_n\ge D_*-c_nD(X_n),
\]

and (1), (7) imply the fixed floor

\[
 \boxed{
 \liminf_n R_n
 \ge (1-c)D_*
 =\frac{D_*(L-D_*)}{L}>0.}
\tag{10}
\]

More precisely, rearranging (9) gives

\[
 R_n-(1-c_n)D_*
 = D(U_n)-D_*+c_n(D_*-D(X_n)).
\tag{11}
\]

Since (D(X_n)\to D_*), every cluster subsequence satisfies

\[
 \boxed{
 \lim R_n-(1-c)D_*
 =\lim D(U_n)-D_*}
\tag{12}

whenever either limit is taken along that subsequence.  Thus the copied
prefix charge splits canonically into:

* the unavoidable minimum-debt absorption payment ((1-c)D_*); and
* exactly the residual whole-debt excess of the copied source sibling.

This is the quantitative content lost by saying only that the old roots may
cease to be exact.

## 3. Minimum copied sibling gives strict support rank drop

Suppose, after a subsequence,

\[
 D(U_n)\longrightarrow D_*.
\tag{13}
\]

Take semantic clusters (U_n\to U) and (V_n\to V).  Then

\[
 D(U)=D(V)=D_*.
\tag{14}
\]

The profiles (U_n,V_n) differ only in (p)'s action at their common deep
marked row.  Their opponents' complete strategies are identical, so their
(p)-caps are identical.  Equation (6) gives (d_p(V_n)=0); hence the
literal payoff difference from (U_n) to (V_n) is the entire debt
(d_p(U_n)).  By (1), (7), and exact marked-row transport,

\[
 d_p(U)>0,
 \qquad d_p(V)=0.
\tag{15}
\]

Mix the two complete (p)-stopping laws with weight one half at every (n),
and take a semantic cluster (H).  Coordinatewise stopping-law debt
convexity gives

\[
 d_i(H)\le\frac12d_i(U)+\frac12d_i(V).
\]

Both endpoint sums equal (D_*), while (H) is an actual carrier point and
therefore has total debt at least (D_*).  Every coordinate inequality is
an equality.  Hence

\[
 \operatorname{supp}_+d(H)
 =\operatorname{supp}_+d(U)\cup\operatorname{supp}_+d(V),
\]

and (15) gives

\[
 \boxed{
 \operatorname{supp}_+d(V)
 \subsetneq\operatorname{supp}_+d(H).}
\tag{16}
\]

The checked positive-minimum tangent-family constructor and re-extraction
theorem turn (16) into a regenerated tangent family with strictly smaller
support cardinality.  This is exactly the rank consumer proved in
`ATLAS_GATEKEEPER__CANONICAL_PAIR_ENDPOINT_MINIMUM_FIBER_RANK_DROP.md`;
fresh exactification does not disturb it when the copied source sibling also
returns to the minimum fibre.

In this arm, (12) says the sibling charge tends to the **exact** absorption
payment ((1-c)D_*).  The nonzero charge is compatible with rank descent; it
does not by itself constitute a contradiction.

## 4. Minimum exactification directly supplies a concentrated packet

Before distinguishing the copied sibling, observe that the exactified
endpoint sequence \(V_n\) has every field of
`QuittingReprojectionConcentratedPacket` after one finite-index shift.

Let \(T\) be the fixed routed coalition at the marked row and let \(t_n\) be
its shifted date after \(W_n\).  Exact marked-mass transport and (7) give a
constant \(\rho>0\) such that, eventually,

\[
\rho\le
\operatorname{StageMass}(V_n,t_n,T).
\tag{17}
\]

The marked root is the literal best endpoint of \(p\), so its local
coordinate Nash defect is exactly zero against the literal post-mark tail:

\[
\operatorname{Def}_p(V_n,t_n)=0.
\tag{18}
\]

Choose \(N\) and \(\rho>0\) so that (17) holds for every \(n\ge N\).  Define

\[
\begin{aligned}
\mathrm{profiles}(n)&:=V_{N+n},\\
\mathrm{subseq}(n)&:=n,\\
\mathrm{mark}(n)&:=t_{N+n},\\
\mathrm{cutoff}(n)&:=t_{N+n}+1,\\
\mathrm{scale}(n)&:={1\over n+1}.
\end{aligned}
\tag{19}
\]

Equation (17) supplies packet resolution \(\rho\); identity is strictly
monotone; mark is below cutoff; the literal spine decomposition supplies
`semanticPrefix`; and (18) makes `defect_tendsto` identically zero.  The scale
is positive and tends to zero.  The generic packet has no whole-profile
near-minimum field.  Equation (5) is therefore external retained provenance.
The post-mark tail is literally the original retained minimum-return tail;
this later forces every selected tail cluster back onto the minimum fibre.

The routed coalition is nonempty and contains a player other than \(p\):

* in leave mode it is the singleton consisting of the other original pair
  member, so \(p\notin T\);
* in join mode it is the triple containing both original pair members, so
  either one may be selected.

Therefore the checked theorem
`QuittingTerminalExploitabilityWitness.concentratedPacket_singletonStrategic_or_collisionMinimumResidual`
applies with owner \(p\), the fixed selected \(other\in T\), and the original
global minimum point.  Its exact output is

\[
\boxed{
\text{HasQuittingConcentratedSingletonStrategicDispatch}
\quad\lor\quad
\text{Nonempty(QuittingConcentratedCollisionMinimumResidual)}.}
\tag{20}
\]

This is an actual-data adapter into the maintained packet consumer, but not a
terminal-equilibrium or support-descent theorem.  In Fin4 the strategic side
contains the maintained static atomic-toggle handoff (positive-gap exact
deletion has separately been excluded); the collision side is the maintained
source-attached collision-minimum residual.  No claim is made that either
remaining output is already consumed, nor that this re-entry is a strict
well-founded atlas edge.

The packet construction uses only the endpoint branch.  It does not require
the copied source sibling \(U_n\) to return to the minimum fibre.  Thus the
sibling-charge alternative below is extra retained structure, not a new
unconsumed predecessor node.

The equality-arm actualizer also keeps the commonly prefixed historical
comparison profiles.  Its checked theorem
`gainFloor_le_actualPayoffGain` gives the literal whole-profile floor

\[
0<\frac{\psi D_*}{2}
\le U_a(V_n)-U_a(S_n)
\tag{20b}
\]

for one fixed gain mover $a$.  This is the active-passport strengthening
suggested by the serial audit.  It is producer data, not a terminal result.
For a nonsingleton routed coalition, the checked minimum-return compiler uses
the packet and returns a `ThreeRoleLimitChord`; for a singleton it enters the
strategic-singleton output.  Neither output is consumed here.

### 4.1 Exact declaration-level field map

The construction above is not just a resemblance of interfaces.  Its exact
map to the checked packet fields is as follows.

* The target structure is
  `QuittingReprojectionConcentratedPacket` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticResetReprojectionTemporalSplit.lean`.
  Its parameters are instantiated by

  \[
  \begin{aligned}
  \texttt{profiles}(k)&=V_{N+k},\\
  \texttt{owner}&=p,\\
  \texttt{terminal}&=T,\\
  \texttt{cutoff}(k)&=t_{N+k}+1,\\
  \texttt{scale}(k)&=1/(k+1).
  \end{aligned}
  \]

* `resolution` is the fixed \(\rho>0\) chosen after the finite shift \(N\),
  and `resolution_pos` is its strict positivity.  If the unprefixed routed
  endpoint has stage mass at least \(\lambda>0\), then

  \[
  \operatorname{StageMass}(V_n,t_n,T)
  =c_n\operatorname{StageMass}(E_n,s_n,T).
  \tag{20a}
  \]

  This is exactly
  `quittingStageCoalitionMass_literalRootStack_add_length` in
  `TerminalSemanticLawCarrierCausalization.lean`, with
  \(t_n=|W_n|+s_n\).  Since \(c_n\to D_*/L>0\), one may take, for example,
  \(\rho=(D_*/(2L))\lambda\) after increasing \(N\).  The unprefixed no-loss
  routing estimate is
  `quittingStageCoalitionMass_le_stagePureEndpointRouted` in
  `TerminalSemanticLiveWeightedCollisionTransfer.lean`.

* `subseq := id` and `subseq_strictMono := strictMono_id`; all prior
  subselections and the finite shift are absorbed into the definition of
  `profiles`.  `mark k := t_{N+k}` and `mark_lt` is the tautology
  \(t_{N+k}<t_{N+k}+1\).

* `semanticPrefix` is the literal spine identity at the displayed row.  It
  is discharged by
  `positive_stageCoalitionMass_has_semanticPrefixIncidence`, exactly as in
  the checked definition
  `FinFourOwnerCompressedMinimumReturnForcedPairPacket.movingPacket` in
  `Research/Quitting/FinFourProducerAtlas/MinimumReturnForcedPair.lean`.
  This records actual current and tail carrier points, exact prefix equality,
  and positive root mass for \(T\); it is not semantic reselection.

* `defect_tendsto` has numerator identically zero.  The local endpoint fact is
  the checked theorem
  `QuittingStageAtomConcentratedPacketAdapter.ownerMarkedDefect_eq_zero` in
  `Research/Quitting/PositiveStageAtomConcentratedPacket.lean`; after
  prefixing, the marked root and its literal post-mark tail are unchanged,
  only their date is shifted.  Thus

  \[
  \operatorname{LiveMass}(V_{N+k},t_{N+k})
  \operatorname{Def}_p(V_{N+k},t_{N+k})=0,
  \]

  and division by the positive scale \(1/(k+1)\) remains zero.

* The low-tail/minimum information is **not** a packet field.  It is retained
  externally through the literal post-date identity
  `payerTarget_postDateSpine_eq_reference` and the convergence theorem
  `referenceDebt_tendsto` in `MinimumReturnForcedPair.lean`; prefixing by
  \(W_n\) before the marked row preserves that post-mark spine verbatim.
  Hence any tail subsequence selected by the downstream compactness consumer
  has debt \(D_*\).  A formal wrapper should state this convergence beside
  the generic packet rather than falsely add it to the packet API.

The exact checked consumer is
`QuittingTerminalExploitabilityWitness.concentratedPacket_singletonStrategic_or_collisionMinimumResidual`
in `Research/Quitting/ConcentratedSingleton/StrategicDispatch.lean`.  Besides
the packet it takes a distinct member `other ∈ terminal`, the supplied global
minimum and its positivity, and positivity/convergence of `scale`.  Its
literal result type is

```text
HasQuittingConcentratedSingletonStrategicDispatch witness packet other
  ∨
Nonempty (QuittingConcentratedCollisionMinimumResidual
  reward minimum owner terminal packet)
```

The collision residual contains `cluster`, `subseq`, `cluster_mem`,
`subseq_strictMono`, `tail_tendsto`, `ownerDefect_tendsto`, and
`escape_or_otherDefect`.  It is a residual.  It does not assert terminal
approximants, a cumulative admissible return, or support descent.  In the
present source-attached construction the external post-mark tail convergence
rules out its strict tail-escape alternative and leaves the minimum-tail
other-defect arm, by the same argument formalized as
`movingCollisionResidual_clusterDebt_eq_minimum` and
`movingCollisionResidual_minimumTail` for the repository's original moving
forced-pair packet.

Finally, `FinFourOwnerCompressedMinimumReturnForcedPairPacket.movingPacket`
already constructs a minimum-tail concentrated pair packet from the original
forced-pair source, and `nonempty_movingCollisionMinimumResidual` feeds it to
the same residual.  Therefore the fresh endpoint adapter is not fresh merely
because it reaches (20).  Its potentially new datum is that the owner is the
killed endpoint mover and that copying the exactification word back to the
source co-realizes the sibling charge below.  Without a consumer of that
extra datum, the adapter is a source-enriched return to a known residual
rather than a strict atlas decrease.

The generic equality-arm construction itself is already checked as
`QuittingMarkedPairMinimumReturnActualizer` together with its declarations
`profiles`, `sourceProfiles`, `resolution_le_stageMass`,
`gainFloor_le_actualPayoffGain`, `markedOwnerDefect_eq_zero`, `packet`, and
`nonempty_threeRoleLimitChord_of_minimumReturn` in
`Research/Quitting/NormalizedPassportMinimumReturn.lean`.  What remains
unpackaged as one declaration is the source-facing composition from the
canonical strict killed endpoint to that generic family.

## 5. Strict copied sibling carries extra source-attached charge

If instead

\[
 \liminf_n D(U_n)>D_*,
\tag{21}
\]

then (12) gives a strict charge beyond the minimum absorption payment:

\[
 \liminf_n
   \bigl(R_n-(1-c_n)D_*\bigr)>0.
\tag{22}
\]

This arm retains more than an off-minimum carrier label:

* the same literal exactification word (W_n);
* exact cap--Nash provenance on the killed-mover endpoint branch (V_n);
* the minimum source sibling (X_n);
* the fixed routed terminal atom and post-mark tail;
* the killed endpoint coordinate (d_p(V_n)=0); and
* a fixed positive reached sum of concrete root Nash defects on the copied
  source branch.

Nevertheless, the rows counted in (R_n) are not exact cap--Nash roots on
that source branch.  They cannot be reinterpreted as exact
punishment-floor Bellman edges.  A cumulative positive defect sum is not an
exact cumulative absorption charge, and the existing exact path compilers do
not consume (22).

Thus strict copied-sibling ascent is mathematically distinct from the
unique-all-Continue endpoint minimizer.  Applying normalized-passport
minimization to the endpoint orbit gives the inert node when its slice
minimum remains above (D_*).  When the larger all-prefix slice has minimum
(D_*), its raw actualizers already give a minimum-return concentrated
packet, but they need not be exact cap-prefix descendants and need not retain
the whole-coordinate kill (d_p=0).  Only when a minimum-return sequence is
realized by exact cap stacks does the copied sibling test above apply; it then
adds (21)--(22) to the packet.

## 6. Exhaustive statement for normalized minimization and fresh exactification

Let \(K_{\theta,\psi}\) be the compact all-prefix decorated slice of
`FORCED_PAIR_REVIEW__NORMALIZED_PASSPORT_MINIMIZER_ELIMINATES_SUPPORT_ENTRY`,
rebased at the routed pure coalition and a fresh screened paid toggle.  Such a
fresh toggle exists for the singleton and nonsingleton routed roots in the
Fin4 hard residual; this is a local root statement, not a claim that its whole
gain is the old killed coordinate.

The strongest current exhaustive reduction is

\[
\boxed{
\begin{array}{c}
\text{strict off-minimum killed-mover endpoint}\\
\Downarrow\\
\text{off-minimum normalized-passport minimizer with unique all Continue}
\\[1mm]
\quad\lor\quad
\text{actual minimum-return concentrated packet at the routed coalition},
\\[1mm]
\text{and, if the return is by exact cap stacks,}\\
\qquad
\begin{cases}
\text{copied source sibling returns to the minimum fibre}
  &\Rightarrow\text{strict support-rank drop},\\
\text{copied source sibling remains strictly off-minimum}
  &\Rightarrow\text{quantitative sibling charge (22).}
\end{cases}
\end{array}}
\tag{23}
\]

The first split is exhaustive by compact minimization and exact prefix
invariance of the slice.  The second line is an actual-data output, but the
existing strong-packet dispatch may return the still-unconsumed static atomic
handoff; it is not claimed to finish Fin4.  The two indented alternatives are
distinguished by the actual semantic debt of (U_n), not by a reselected
witness, and are exhaustive once a minimum-return exactification sequence
(5) is selected.

It is important not to replace the all-prefix slice by a raw exact-prefix
orbit without proof.  Exact-root correspondences are closed but need not be
lower hemicontinuous.  A minimum point of the all-prefix closure can be
actualized by roots which were only approximately exact on the raw sources.
At such a point the marked local owner defect is retained, but the old whole
coordinate identity (d_p=0) need not be.  This is why the unqualified
two-way conclusion "rank drop or inertness" is unavailable at the current
interface.

## 7. Exact boundary regression

Section 9 of
`CODEX_ATLAS_GATEKEEPER__MONODROMY_VERTICAL_REPAIR.md` gives a Fin4 table with
a date-zero product root (q), a date-one pure square, and all-Never tail.
The root (q) is exact cap--Nash above the source corner (A), which has a
global-minimum post-date tail and a fixed paid response square.  Replacing
only the date-one root by the endpoint corner (A_i) changes player (h)'s
cap from zero to one.  The copied date-zero root then has (h)-coordinate
defect exactly (1/2).

Thus

\[
\begin{array}{c}
\text{exact source prefix}+\text{common low tail}
+\text{fixed atom}+\text{paid endpoint move}
\end{array}
\]

does not imply copied-prefix exactness after the move.  The table's global
minimum is zero, so it does not instantiate the positive-minimum hard
residual.  It is sharp enough to refute any attempted proof of that
implication using only the local prefix/atom/paid-square fields.

## 8. The charge is an exact whole-word cap square

The reached sum in (8) can be localized to a fixed player, although not in
general to a fixed row.

Write \(u_i(P)\) and \(B_i(P)\) for prescribed payoff and behavioral cap.
For each player define

\[
 R_{n,i}:=
 d_i(U_n)-c_nd_i(X_n).
\tag{24}
\]

The playerwise prefix telescope makes \(R_{n,i}\) the reached sum of that
player's root defects on the copied source branch, so

\[
 R_n=\sum_iR_{n,i}.
\tag{25}
\]

Endpoint exactness gives \(d_i(V_n)=c_nd_i(E_n)\).  Moreover, prescribed
payoff differences of the two horizontal siblings transport through the
common literal word with no error:

\[
 u_i(U_n)-u_i(V_n)
   =c_n\bigl(u_i(X_n)-u_i(E_n)\bigr).
\tag{26}
\]

Substituting \(d=B-u\) into (24), and using (26), yields

\[
\boxed{
R_{n,i}
=
\bigl(B_i(U_n)-B_i(V_n)\bigr)
-c_n\bigl(B_i(X_n)-B_i(E_n)\bigr).}
\tag{27}
\]

Thus \(R_{n,i}\) is exactly the cap curvature of the literal four-corner
square

\[
\begin{matrix}
X_n&\longrightarrow&E_n\\
\downarrow W_n&&\downarrow W_n\\
U_n&\longrightarrow&V_n .
\end{matrix}
\]

The corresponding prescribed-payoff square is exactly zero by (26).  This is
a source-matched square: no cap, profile, root word, or response value is
reselected after the comparison.

For the killed mover \(p\), the two horizontal pairs have identical
opponents, hence identical \(p\)-caps.  Equation (27) therefore gives

\[
\boxed{R_{n,p}=0.}
\tag{28}
\]

In Fin4, one fixed player \(i\ne p\) can consequently be selected along a
subsequence with

\[
\liminf_n R_{n,i}
\ge {1\over3}\liminf_n R_n
\ge {D_*(L-D_*)\over3L}>0.
\tag{29}
\]

This is the strongest unconditional localization: a fixed observer and a
literal full-word cap square with an exactly closed payoff square.

It is not automatically a common-response square.  A best response attaining
or approximating \(B_i(U_n)\) may stop inside \(W_n\).  Its probability of
reaching the horizontal tail then uses its own Continue probabilities, not
the prescribed joint factor \(c_n\).  Therefore (27) does not identify one
behavioral response whose four payoff values have the same curvature.
That missing response selection is precisely the cap-switching issue.

There is a sharp two-response algebraic regression.  Fix \(0<c<1\), choose
\(A,C>0\), and \(0<B<cA\).  Give two candidate responses the four values

\[
\begin{array}{c|rrrr}
 &U&V&X&E\\ \hline
a&cA&0&0&-A\\
b&B&B&C&C .
\end{array}
\tag{30}
\]

For each response separately,

\[
\bigl(v(U)-v(V)\bigr)-c\bigl(v(X)-v(E)\bigr)=0.
\tag{31}
\]

But after taking caps,

\[
\max\{cA,B\}-\max\{0,B\}
-c\bigl(\max\{0,C\}-\max\{-A,C\}\bigr)
=cA-B>0.
\tag{32}
\]

Thus a positive cap square need not contain any positive same-response
square, even with only two responses and with each individual square exactly
flat.  Since unrestricted caps are suprema of behavioral-response values,
no common-response localization follows from (27) by max algebra alone.
Additional dynamic or source structure must exclude this witness switch.

Nor can (29) be strengthened to a fixed positive **single-row** charge from
the debt account alone.  The abstract exact recurrence permits a word of
length \(N\) with constant survival factors tending to one and reached
defects \(R/N\) at every row.  The total reached charge is \(R\), while the
largest row charge tends to zero.  These scalar data obey the same
nonnegativity and transport equations used in (8)--(12).  A single-row floor
therefore requires additional quitting-table structure; it cannot follow
from the cap-stack and minimum-debt identities alone.

## 9. Reverse mixing is not the checked flat-support-entry branch

At the minimum endpoint \(V\), the copied sibling \(U\) differs only in
player \(p\)'s complete stopping law.  Let \(M_s\), \(0\le s\le1\), mix from
\(V\) toward \(U\) in that one stopping law.  The opponents of \(p\) are
fixed, so its cap is fixed and prescribed payoff is affine.  Hence

\[
\boxed{d_p(M_s)=s\,d_p(U).}
\tag{33}
\]

Thus reverse mixing activates the zero-debt coordinate \(p\) linearly.
This looks superficially like a flat support-entry tangent, but it does not
type into the checked predicate
HasQuittingStoppingLawFlatSupportEntry from
StoppingLaw/ExhaustiveTangentAlternative.lean.  That predicate requires
the **mover** indexing the reset column to belong to

\[
\mathrm{active}=\operatorname{supp}_+d(\mathrm{base}).
\]

Here the changed stopping law is exactly player \(p\)'s, while

\[
d_p(V)=0,
\qquad
p\notin\operatorname{supp}_+d(V).
\]

So \(p\) is an inactive mover, not an active mover feeding a zero-debt
recipient.  The stronger
exists_vanishingDebtAtomAccess_of_supportEntry has the same typing: its
atom mover is a subtype of the positive-debt support.  It cannot be invoked
with this reverse chord.

There is a lower-level theorem with weaker typing:
hasVanishingDebtAtomAlternative_of_endpointDebtRise accepts an arbitrary
mover and observer.  It can be applied here with both labels equal to \(p\),
base \(V\), and target \(U_p\), because (33) is a positive endpoint debt
rise.  This does **not** produce QuittingVanishingDebtAtomAccess:
that access structure additionally requires a positive-support mover and
observer_ne_mover.  With mover = observer, the common-response rectangle
collapses under the two overwriting updates, and the decoder falls into its
prescribed-atom side.  It recovers a terminal atom carrying the already known
horizontal payoff loss from \(V\) to \(U\); it does not create a new
off-diagonal atom or chronological consumer.

Changing the base to a proper interior mixture makes \(p\) active, but then
the direction toward \(V\) is support **loss**, not support entry; changing
the mover to another active player loses the actual one-player chord.
Accordingly (33) is real additional geometry, but it is not already consumed
by the current frontier access/chronological API.

## 10. What remains

Fresh exactification plus normalized-passport minimization gives a clean
classification, but not a terminal consumer:

* if the normalized slice stays off minimum, the named unique-all-Continue
  inert passport remains;
* if the slice reaches minimum, the actual endpoint sequence enters the
  checked strategic-or-collision packet residual;
* if the return is by exact stacks and the copied sibling is also minimum,
  the half-chord gives strict support-rank descent;
* otherwise the minimum packet co-realizes the additional sibling charge
  (22).

The remaining conjecture-facing task is therefore not to prove that a packet
exists.  It is to consume either the minimum-tail strategic/collision output
or the off-minimum inert passport into a terminal/return conclusion or a
regenerated well-founded rank.  A sibling-charge consumer would be a genuine
strengthening because it could turn the last exact-stack subarm into such an
output, but the broad packet adapter does not supply that conclusion by
itself.

## Sources inspected

* `exports/FIN4_FORCED_PAIR_MAXIMAL_PREFIX_RAY_DICHOTOMY.md`;
* `notes/FORCED_PAIR_REVIEW__NORMALIZED_PASSPORT_MINIMIZER_ELIMINATES_SUPPORT_ENTRY.md`;
* `notes/FORCED_PAIR_REVIEW__APPROXIMATE_SUPPORT_ENTRY_REEXACTIFICATION.md`;
* `notes/FORCED_PAIR_REVIEW__MINIMUM_FIBER_KILLED_MOVER_CHORD_AND_CLOSURE_SEAM.md`;
* `notes/ATLAS_GATEKEEPER__CANONICAL_PAIR_ENDPOINT_MINIMUM_FIBER_RANK_DROP.md`;
* `notes/ATLAS_GATEKEEPER__STRICT_PAIR_RAY_UNIQUE_CAP_CONSUMER.md`;
* `notes/CODEX_ATLAS_GATEKEEPER__MONODROMY_VERTICAL_REPAIR.md`;
* `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticDirectedTransport.lean`;
* `UniformEquilibrium/Diagnostics/Quitting/TerminalCapNashChronology.lean`;
* `UniformEquilibrium/Diagnostics/Quitting/TerminalCapNashEndpointTransport.lean`;
* `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticStoppingLawDebtConvexity.lean`;
* `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticResetReprojectionTemporalSplit.lean`;
* `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticLawCarrierCausalization.lean`;
* `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticLiveWeightedCollisionTransfer.lean`;
* `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPlateauIncidence.lean`;
* `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/PositiveMinimumDebtTangentFamily.lean`;
* `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/ExhaustiveTangentAlternative.lean`;
* `UniformEquilibrium/Diagnostics/Quitting/UniformExistenceBoundary.lean`;
* `Research/Quitting/ConcentratedSingleton/StrategicDispatch.lean`;
* `Research/Quitting/ConcentratedSingleton/NonSingletonResidual.lean`;
* `Research/Quitting/NormalizedPassportMinimizer.lean`;
* `Research/Quitting/NormalizedPassportMinimumReturn.lean`;
* `Research/Quitting/FinFourProducerAtlas/MinimumReturnForcedPair.lean`.

## Concrete next question

Can the strict excess charge in (22), together with the fixed routed atom and
the fact that the endpoint branch uses the same word exactly, be converted
into an actual terminal/return consumer of the minimum-tail collision
residual, rather than merely re-entering that residual?  A positive answer
would turn the source-enriched re-entry into a strict atlas edge.  A negative
answer should exhibit a positive-minimum source-attached regression, not only
the existing zero-minimum cap-switching example.
