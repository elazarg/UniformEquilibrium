# Pure-clock minimum-hit rank attack

Identity: `PAIRED_HULL_REVIEW`

## Status

The pure-minimum-hit arm has not been consumed.  The strongest valid result is
a permanent rank drop whenever a **positive** calendar label is deleted, plus
an exact reduction of every failure to the date-zero coalition/reset waist.
At that waist the checked Fin4 screened-orbit theorem applies literally and
reaches a singleton sibling in at most three profitable edges followed by one
uncharged pair-to-singleton route.  This does not close the branch: the
singleton is then reduced to the already open off-minimum paid port.

The deterministic maximum-debt orbit is a different construction.  It need
not reach a singleton: the checked theorem leaves a closed cycle of length
\(4\), \(6\), or \(8\).  The Fin4 monodromy impossibility theorem cannot be
applied to such a cycle because its terminal predicate declares **every**
pair terminal, whereas the maximum-debt successor of a pair may be an
outsider join to a triple.

## 1. Input and required output

Let \(I=\operatorname{Fin}4\).  Let \(D_*>0\) be the global minimum of total
terminal-semantic debt over actual behavioral profiles.  Suppose a literal
pure-clock exact-response path has first reached a pure-clock minimum

\[
 t^0\longrightarrow\cdots\longrightarrow t^n=M,
 \qquad D(t^k)>D_*\ (k<n),\qquad D(M)=D_*.
\]

The last mover (p) satisfies

\[
 U_p(M)-U_p(t^{n-1})=d_p(t^{n-1})\ge D_*/4,
 \qquad d_p(M)=0.
\]

All profiles and replacements have literal ancestry from the same retained
minimum source.

The desired new conclusion is a minimum-source child of the same type with a
strict natural-valued rank, or a contradiction/terminal consumer.  Merely
applying `pureTimeMinimum_exists_offMinimumPaidPort` to (M) returns to the
already open waist and is not such a conclusion.

## 2. A permanent positive-calendar support

For a pure-clock profile (t), define

\[
 P(t)=\{m\in\mathbb N:m>0\text{ and }t_i=m\text{ for some }i\}.
\]

Against pure-clock opponents, an unrestricted cap-attaining pure response is
one of

\[
 0,\qquad m_i,\qquad \infty,
\]

where (m_i) is the first finite opponent deadline.  Hence every canonical
exact-response edge satisfies

\[
 P(t')\subseteq P(t).
\tag{2.1}
\]

The anchored erasures and singleton-owner responses in
`PureTimeMinimumDescent.lean` have the same property: they replace a deadline
by Never or by an already occupied later opponent deadline.  Therefore (2.1)
holds through arbitrary interleavings of the canonical response orbit and the
checked pure-minimum descent.

If an equality-arm singleton response deletes an earliest deadline (m>0),
then

\[
 P(t')\subsetneq P(t).
\tag{2.2}
\]

The lost positive date can never be reintroduced by any later canonical
pure-clock best response.  Thus

\[
 \rho_+(t)=|P(t)|
\]

is a genuine renewable rank on every lane whose minimum-return steps delete a
positive date.

This is slightly stronger than the local deadline-rank statement: ordinary
deadline rank can be reset by reintroducing date zero, whereas a deleted
positive calendar label is permanently absent.

## 3. Exact residual: date zero

The only failure of (2.2) is a minimum profile whose earliest coalition quits
at date zero.  Write

\[
 K(M)=\{i:M_i=0\}.
\]

There are three exact observations.

### 3.1 First insertion of zero cannot itself hit the minimum

Suppose a source has no date-zero quitter and a mover changes to clock zero.
The target prescribed payoff of that mover is its singleton reward.  If the
target were a positive global minimum and the mover had target debt zero, the
checked singleton margin would give simultaneously

\[
 B_i=r_i(\{i\}),
 \qquad B_i-r_i(\{i\})\ge D_*>0,
\]

a contradiction.  Thus a minimum hit at date zero can occur only after a
date-zero quitter was already present; the last mover joins an existing
coalition.

### 3.2 Two sure date-zero quitters screen all later clocks

If (|K(M)|\ge2), replace every player outside (K(M)) by Never.  Prescribed
play is unchanged.  After any one player's complete behavioral deviation, at
least one opponent in (K(M)) still quits at date zero.  Consequently all
prescribed payoffs and all unrestricted caps are unchanged.  The resulting
literal pure-coalition profile

\[
 M^{K}_i=
 \begin{cases}
 0,&i\in K(M),\\
 \infty,&i\notin K(M)
 \end{cases}
\tag{3.1}
\]

is the same semantic minimum and has (P(M^K)=\varnothing).

This is a real contraction of the calendar data, but not yet of a renewable
global state rank: the date-zero coalition can change under later exact
responses.

### 3.3 The singleton date-zero case exits the minimum lane

If (|K(M)|=1), the checked singleton-minimum calculation forces the owner to
respond at the next occupied opponent deadline or by Never.  An equality
target deletes date zero; a strict target is off minimum.  With no later
opponent deadline, the exact response is Never and the all-Never target is
strictly off minimum.

Again, a later off-minimum response can rebuild a nonsingleton date-zero
coalition before the next minimum hit.  Thus deleting zero once is not a
renewable rank transition.

## 4. Why the last mover's zero debt does not orient the residual

Let (A=t^{n-1}) and (M=t^n), and let (p) be the last mover.  Since only
(p)'s strategy changes,

\[
 B_p(M)=B_p(A),\qquad
 U_p(M)-U_p(A)=d_p(A),qquad d_p(M)=0.
\]

The total-debt identity is

\[
 D(M)-D(A)
 =-d_p(A)+
   \sum_{j\ne p}\bigl(d_j(M)-d_j(A)\bigr).
\tag{4.1}
\]

Putting (D(M)=D_*) only fixes the aggregate nonmover leakage.  It does not
preserve any old zero coordinate, orient coalition membership, or imply that
the next minimum has smaller debt support.  In particular the response may
join an existing date-zero coalition, and reversing that one clock returns
literally to the preceding off-minimum source.  This is a horizontal returned
pair, not a well-founded transition.

The minimum-fibre pure-time descent does not repair (4.1).  If its next
profile stays minimum, its deadline rank falls; if it leaves the fibre, the
rank comparison is no longer a comparison of two recursive minimum nodes.
Restarting the rank after that exit is exactly the prohibited phase reset.

## 5. Pure-coalition core and the exact same-stage audit

At the screened profile (3.1), every cap-attaining response is clock zero or
Never.  For (|K|\ge2), the full unrestricted debts are exactly

\[
 d_i(M^K)=
 \begin{cases}
 \bigl[r_i(K\setminus\{i\})-r_i(K)\bigr]_+,&i\in K,\\[1mm]
 \bigl[r_i(K\cup\{i\})-r_i(K)\bigr]_+,&i\notin K.
 \end{cases}
\tag{5.1}
\]

Indeed an insider can only join the sure date-zero coalition or pass it by
Continuing; an outsider can only stay out or join it.  At least one opponent
quits at date zero in every comparison, so Never and arbitrarily late stopping
add no further value.  Random behavioral responses only convexify the two
endpoint values.

Thus a positive debtor supplies a strict one-coordinate coalition toggle.
Exact response dynamics toggles one membership of \(K\).  If a target stays
minimum, the mover lands on its zero-debt face.  If it is strict, the
construction has only returned to the off-minimum port.

For \(|K|=1\), the singleton owner is the only possible positive debtor at a
positive minimum and its Never response exits the minimum fibre.  For
\(|K|=2\), erasing either member gives a singleton profile; that target is
either already off minimum or its exact singleton response exits.  Larger
coalitions may rotate by outsider joins and member leaves before a pair is
reached.

### 5.1 The screened-orbit theorem applies without a tail hypothesis

Take the attained profile \(M^K\) itself as the common base profile, stage
zero, source coalition \(K\), and scale \(\lambda=1\).  Its source stage mass
and live mass are both one.  Therefore
`quittingFinFourPositiveMassNonsingleton_nonempty_screenedEndpoint` applies
directly.  No minimum-atom producer, low-tail estimate, or newly selected
realizer is required.

The returned `FinFourPureNonsingletonScreenedEndpoint` contains:

1. the literal starting sibling \(M^K\);
2. at most three strict best-endpoint sibling edges, each of gain at least
   \(D_*/4\) and with exact mover-debt subtraction;
3. a terminal pair; and
4. one literal Continue update from that pair to a singleton, with stage mass
   still one and with the complete post-date tail unchanged.

The closed alternative in
`exists_pureNonsingletonScreened_terminalOrbit_or_closedSegment` maps to a
`QuittingSameStageEndpointEdge` closed segment and is eliminated by
`not_nonempty_finFourSameStageEndpointClosedSegment`.  Thus the same-stage
impossibility theorem **does** consume the closed branch of this screened
dispatcher.

It does not consume the terminal branch.  The structure
`QuittingSameStageSingletonRoute` records only a routed singleton and a
stage-mass inequality.  In particular it has no field asserting that the
final Continue action is a best endpoint, has positive gain, kills the
mover's debt, or leaves a minimum child.  The downstream endpoint theorem
states this boundary explicitly: the final route is not asserted to be
profitable.

The singleton target is an actual pure-clock sibling of the same base.  If it
is off minimum, the result has reached the open paid-port waist.  If it is
minimum, the checked pure-time minimum descent produces an actual off-minimum
descendant.  Hence no source realizer has been lost, but no terminal consumer
or renewable rank has been produced either.

### 5.2 Canonical maximum-debt iteration is not the screened dispatcher

At a pure nonsingleton coalition, (5.1) identifies maximum debt with maximum
positive table-toggle gain.  Hence the deterministic map in
`PaidNonsingletonToggleCycle.lean` is exactly the canonical maximum-debt
toggle map relevant here.  Its checked finite-orbit theorem gives:

\[
 \text{selected toggle reaches a singleton}
 \quad\lor\quad
 \text{a simple nonsingleton cycle of period }4,6,\text{ or }8.
\tag{5.2}
\]

Every realized edge over \(M^K\) is a literal same-date unilateral update,
has gain at least \(D_*/4\), and has exact mover-debt subtraction.  One may
also split at the first vertex whose debt exceeds \(D_*\).  If no such vertex
exists, (5.2) leaves a horizontal minimum-fibre cycle.

This does not contradict the monodromy impossibility theorem.  The latter
requires `offset_not_terminal` for the predicate
`QuittingSameStageSingletonRoute`.  Every pair violates that requirement,
because some member can always be routed losslessly from the pair to a
singleton.  By contrast, the deterministic maximum-debt mover at a pair may
be an outsider whose profitable endpoint joins the pair and creates a triple.
The local cap formula does not force the selected maximum debtor to be a
leaving member.

Consequently the exact missing bridge is not a source producer.  It is a
**strategically oriented pair terminal**: at every reached pair one would
need either a profitable best-endpoint route to the singleton, a regenerated
minimum child with a strict renewable rank, or a terminal consumer for the
resulting off-minimum port.  None is a field of
`QuittingSameStageSingletonRoute`.

If one follows a closed maximum-toggle word instead, each mover's debt loss
is exactly restored by nonmover leakage.  This is the signed reset
circulation isolated by
`finite_stageFullBestEndpoint_cycle_signedCirculation`; it has no monotone
coordinate or coalition-cardinality orientation.  Formula (5.1) therefore
does not supply a hidden finite rank.

## 6. Exact failed implications

The following implications are unsupported, and the calculations above show
the missing field in each.

1. `last mover debt zero` does not imply preservation of earlier zeros;
   equation (4.1) permits their reactivation.
2. `pure minimum + deadline descent` does not give a renewable global rank;
   the strict arm exits the ranked state type.
3. `finite inherited alphabet` does not give well-foundedness; deterministic
   exact-response dynamics has a literal cycle.
4. `delete the earliest zero deadline` does not give permanent calendar
   descent; clock zero is always an available response and can be reintroduced.
5. `pure coalition + Fin4 monodromy no-go` does not give a contradiction;
   the checked no-go dispatches pair vertices through an uncharged route.
   It does, however, eliminate the closed branch of the screened dispatcher.
6. `canonical maximum-debt orbit + monodromy no-go` is ill-typed: a pair is
   terminal for the monodromy predicate but need not be terminal for the
   selected maximum-debt map.
7. `off-minimum-to-minimum paid response` is not temporal charge; its first
   disagreement need not be an exact Nash--Bellman root.

## 7. Strongest surviving reduction

As an actual-profile construction, the checked pure-time theorem already
contracts the entire pure-minimum-hit arm to

\[
 \boxed{
 \begin{array}{c}
 \text{a finite sequence of minimum-fibre steps with strict }|P|\text{ descent}\
 \text{followed by an actual off-minimum paid port}
 \end{array}}
\tag{7.1}
\]

The date-zero coalition is therefore not a new atlas output.  The screened
same-stage theorem gives a particularly short source-faithful route through
it, but its final pair-to-singleton step is uncharged.  The only genuine rank
found here is \(|P|\) while the construction remains on the minimum fibre.
No rank comparison survives the eventual off-minimum exit.  A completion of
Attack A must consume that paid-port waist or return from it with a renewable
rank; counting the reduction to the waist as success would be circular.

## 8. Sources checked

- `quittingContinuationBestResponseValue_pureTimeProfile_eq_max_two_at_zero`,
  `exists_quittingPureTime_capAttainer` in
  `UniformEquilibrium/Diagnostics/Quitting/PureTimeCapAttainment.lean`;
- `quittingContinuationBestResponseValue_pureTimeProfile_eq_max_three` in
  `UniformEquilibrium/Diagnostics/Quitting/PureTimeScreenedMenu.lean`;
- `pureTimeSingletonMinimum_response_or_deadlineRank_strict` in
  `UniformEquilibrium/Diagnostics/Quitting/PureTimeSingletonMinimumResponse.lean`;
- `pureTimeMinimum_exists_offMinimum` in
  `UniformEquilibrium/Diagnostics/Quitting/PureTimeMinimumDescent.lean`;
- `pureTimeMinimum_exists_offMinimumPaidPort` in
  `UniformEquilibrium/Diagnostics/Quitting/PureTimeMinimumPaidPort.lean`;
- `not_nonempty_finFourSameStageEndpointClosedSegment` and the pair-terminal
  dispatch in
  `Research/Quitting/SameStageEndpointMonodromyImpossible.lean`;
- `quittingFinFourPositiveMassNonsingleton_nonempty_screenedEndpoint` in
  `Research/Quitting/FinFourPureNonsingletonCollisionScreening.lean`;
- `exists_finFourMaximumToggle_terminalOrbit_or_closedSegment` and
  `FinFourMaximumToggleClosedSegment.period_eq_four_or_six_or_eight` in
  `Research/Quitting/PaidNonsingletonToggleCycle.lean`.

## 9. Next exact question

Let a retained positive-minimum source reach the pure date-zero coalition
profile \(M^K\), \(|K|\ge2\).  Can the terminal pair route in the checked
screened orbit be upgraded to a strategically oriented singleton response,
or can a closed maximum-debt cycle be converted into a returned source with a
strict renewable rank?  The local pure-clock formula and the existing
same-stage theorems do neither; they reduce both attempts to the universal
off-minimum paid-port/reset waist.
