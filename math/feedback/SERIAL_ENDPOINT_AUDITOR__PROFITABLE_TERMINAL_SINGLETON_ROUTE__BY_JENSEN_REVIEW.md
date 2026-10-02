# Adversarial review of the claimed profitable terminal singleton route

Reviewer: JENSEN_REVIEW

## Verdict

The note identifies a real **local** API loss, but its main global conclusion
is false for the existing dispatched orbit.

Inside **quittingPureNonsingleton_screenedDispatch**, the proof does establish
the positive gain, sharp live-mass floor, exact mover-debt subtraction, and
mass routing before it splits on the cardinality of the best-endpoint target.
When that selected target is a singleton, all of those facts can be packaged
in a new profitable-singleton record exactly as proposed.

The existing generic orbit does not, however, select that local profitable
singleton branch at its terminal vertex.  Its terminal predicate is the weak
**QuittingSameStageSingletonRoute**.  The generic constructor tests that
predicate first and stops immediately whenever it is true; it calls the local
dispatcher only at nonterminal vertices.  Every pure pair satisfies the weak
terminal predicate via an arbitrary mass-preserving Continue route,
independently of payoff.  Therefore the stored final pair-to-singleton route
can be payoff-losing and need not share the mover, action, singleton, or proof
term selected by **quittingPureNonsingleton_screenedDispatch**.

At a terminal pair, applying the local dispatcher afresh gives the honest
alternative

\[
\boxed{
\text{profitable Continue-to-singleton route}
\quad\text{or}\quad
\text{profitable outsider-join edge to a triple}.
}
\tag{R1}
\]

Both alternatives have gain at least \(L D_*/4\), hence at least
\(\lambda D_*/4\), exact mover-debt subtraction, and literal off-date/tail
provenance.  The second alternative is not a profitable singleton route.

Re-running the generic orbit with “profitable singleton route” as the
terminal predicate also does not repair the claim.  It yields a profitable
terminal orbit **or a closed profitable nonsingleton segment**.  The existing
Fin4 monodromy theorem cannot eliminate that closed arm, because its proof
essentially uses the weaker fact that every pair is terminal.  Strict
pair--triple toggle cycles are an explicit boundary once losing pair exits are
not accepted as terminal.

The strongest immediate formalizable result is therefore the local enhanced
dispatch, together with an audited final-pair alternative of the form (R1).
It is not an unconditional all-paid path to a singleton and does not change a
named producer deficit enough for export.

## 1. Exact local proof-term audit

Fix a finite quitting game, an actual profile \(\sigma\), date \(t\), pure
nonsingleton source coalition \(C\), global minimum semantic pair \(z_*\),
and scale

\[
0<\lambda\le L_t(\sigma),\qquad D_*:=D(z_*)>0.
\]

In Research/Quitting/PureNonsingletonCollisionScreening.lean, the proof of
**quittingPureNonsingleton_screenedDispatch** constructs:

- sourceProfile, the profile with the marked root overwritten by pure \(C\);
- current, tail, and root, the actual marked suffix data;
- who, selected from the average root-defect bound;
- action, the exact best Boolean endpoint for who;
- targetProfile, the literal one-date update;
- routed, the resulting pure coalition; and
- gain, the mover's actual whole-profile payoff gain.

The screening identity and global minimum give

\[
\frac{D_*}{|I|}
\le
\delta_{\mathit{who}}(C),
\tag{R2}
\]

where the defect is computed against the actual prescribed post-date tail.
The named intermediate proof terms then have exactly the advertised content:

- hgainDebt.1 and the rewritten hgain prove
  \[
  g=L_t(\sigma)\,\delta_{\mathit{who}}(C);
  \tag{R3}
  \]
- hgainFloor proves
  \[
  \frac{L_t(\sigma)D_*}{|I|}\le g;
  \tag{R4}
  \]
- hgainPos proves \(0<g\);
- hgainDebt.2 proves
  \[
  d_{\mathit{who}}(\text{target})
  =
  d_{\mathit{who}}(\text{source pure }C)-g;
  \tag{R5}
  \]
- hrouteMass proves no loss of the marked routed mass.

All these terms are constructed before

    rcases hcardCases with hsingleton | hnonsingleton

and therefore are available in both branches at that point.

The local packaging-loss claim is correct.  In the nonsingleton branch, the
proof stores the data in **QuittingPureNonsingletonScreenedEdge** and its
inherited **QuittingSameStageEndpointEdge**.  In the singleton branch, it
returns only **QuittingSameStageSingletonRoute**, whose existential payload
contains route geometry and stage-mass comparison but no best-endpoint,
gain, debt, or carrier fields.

Proof irrelevance prevents recovering discarded fields merely from the fact
that one particular proof script once had them in context.  A new terminal
record or stronger terminal predicate is required.

## 2. Constants

The local constants in the note are correct.

For arbitrary finite \(I\), (R4) and \(\lambda\le L_t(\sigma)\) give

\[
g\ge \frac{L_t(\sigma)D_*}{|I|}
\ge \frac{\lambda D_*}{|I|}.
\tag{R6}
\]

For Fin4 this is

\[
g\ge L_t(\sigma)D_*/4\ge\lambda D_*/4.
\tag{R7}
\]

At the canonical nonsingleton atlas scale

\[
\lambda=\mu^2/8,
\]

the selected-scale floor is

\[
\lambda D_*/4=\mu^2D_*/32.
\tag{R8}
\]

This agrees with
**FinFourPureNonsingletonStrongConcentratedPacket.canonical_edge_gain_floor**
for every currently stored preterminal screened edge.

There are two similar-looking constants in the existing edge structures.
The inherited generic edge field retains the weaker
\(\lambda D_*/(2|I|)\) floor, while
**QuittingPureNonsingletonScreenedEdge.gain_floor_live** and its
**gain_floor** theorem retain the sharp values in (R6).  The proposed
profitable-singleton structure can and should retain the sharp live floor,
not the inherited half-sized generic floor.

## 3. Exact mover debt and tail provenance

The exact mover-debt claim is correct for the locally selected singleton
branch.  The target differs from sourceProfile only in the mover's own
marked-date action, so the mover's unrestricted cap is unchanged.  The
checked theorem
**quittingLiteralSameStage_bestEndpoint_gain_and_debt** gives (R3) and (R5)
simultaneously; no stationary-response restriction or cap attainment is
used.

The target is an actual behavioral profile, so its semantic pair is in the
terminal-semantic carrier.  When routed is singleton, the exact identity
**quittingLiteralPureRootProfile_update_eq_routed** identifies targetProfile
with the literal pure-singleton root profile.

Tail provenance is also exact:

- sourceProfile changes the supplied profile only at date \(t\);
- targetProfile changes sourceProfile only at that same date;
- therefore the target equals the supplied profile at every other date and
  every history; and
- in particular, every post-date live root equals that of the supplied
  profile.

The relevant checked identities are
**quittingProfileLiveRoot_literalOneDateProfile_tail_eq** and
**quittingLiteralPureRootProfile_tail_eq** in
Research/Quitting/SameStageEndpointMonodromy.lean.  The final Fin4 wrapper's
**targetProfile_eq_of_time_ne** and **target_postDate_liveRoot_eq** show the
same provenance for the currently stored weak singleton target.

These local identities do not imply total-debt descent.  Equation (R5)
controls only the mover; the other three unrestricted caps can rise.

## 4. Why the existing generic orbit does not select that branch

The decisive API is in MathUE/FiniteBooleanEndpointOrbit.lean.
**exists_dispatchedOrbit_terminal_or_closedSegment** defines

\[
\operatorname{successor}(s)=
\begin{cases}
s,&\text{if terminal}(s),\\
\text{a chosen dispatched successor},&\text{otherwise}.
\end{cases}
\]

Accordingly:

- hsuccessor calls the dispatch rule only under \(\neg\text{terminal}(s)\);
- the terminal orbit stops at the first state satisfying terminal;
- **DispatchedOrbit.terminal_at** stores only a proof of the supplied
  terminal predicate; and
- no edge is asserted out of the terminal vertex.

For the screened orbit, terminal is
**QuittingSameStageSingletonRoute**, not a profitable route.  The theorem
**quittingSameStageSingletonRoute_of_card_eq_two** proves this predicate for
every pair by choosing a member and making it Continue.  It uses only
cardinality and mass routing.

Thus, at the final pair:

1. the generic construction observes that the weak terminal predicate is
   true;
2. it stops without applying
   **quittingPureNonsingleton_screenedDispatch** to that pair; and
3. **orbit.terminal_at** is destructured to populate the final who, action,
   singleton, and mass fields of
   **FinFourPureNonsingletonScreenedEndpoint**.

There is no proof-term path from hgain, hgainFloor, or hgainDebt in the local
dispatcher to those final endpoint fields.  The note's statement that the
public result “discards the simultaneously proved” terminal gain conflates
two different events:

- the local singleton branch really does discard its gain data; but
- the generic orbit's terminal branch need not be that local branch at all.

Even the singleton label need not agree.  A pair has two possible
Continue-to-singleton routes.  The weak terminal proof can choose one member,
while a profitable local removal, if one exists, can choose the other.

## 5. The exact final-pair alternatives

Apply **quittingPureNonsingleton_screenedDispatch** afresh to the final pair,
with the same minimum, profile, date, and live-mass floor.

Because the selected defect is strictly positive, the selected endpoint
changes the mover's current pure action.  At a pair there are only two
possibilities:

1. the selected mover belongs to the pair and its best endpoint is Continue;
   the routed coalition is a singleton, and the new profitable-singleton
   record is available with (R3)--(R7); or
2. the selected mover is outside the pair and its best endpoint is Quit; the
   routed coalition is a triple, and the existing
   **QuittingPureNonsingletonScreenedEdge** is available with the same sharp
   floor and exact mover-debt identity.

The weak terminal Continue route stored in the current endpoint still exists
in the second case, but it can be payoff-losing.  For a pure pair
\(\{a,b\}\), the local reward inequality

\[
r_a(\{a,b\})=1,\qquad r_a(\{b\})=0
\]

already shows that removing \(a\) need not be profitable.  Positive screened
debt can instead sit on an outsider's join endpoint.

This yields the strongest direct augmentation of the current Fin4 endpoint:

\[
\begin{array}{c}
\text{at most three currently stored profitable edges to a pair},\\
\text{one weak no-loss pair-to-singleton route},\\
\text{and, at that same pair, either}\\
\quad\text{a paid singleton exit or a paid outgoing edge to a triple}.
\end{array}
\tag{R9}
\]

In the source-attached atlas form, every paid edge in (R9) has canonical
floor \(\mu^2D_*/32\) and retains the original post-date tail.

The bare **FinFourPureNonsingletonScreenedEndpoint** does not store the
global-minimality and positivity proofs needed to call the local dispatcher
again.  An accessor should either accept those premises explicitly or live
on the source-attached wrapper, whose
**FinFourMinimumAtomProducer** already supplies them.

## 6. Why changing the terminal predicate leaves a new closed arm

Suppose a new predicate
**QuittingPureNonsingletonProfitableSingletonRoute** packages the full local
singleton data, and use it as the generic terminal predicate.  The enhanced
local dispatcher proves

\[
\text{ProfitableSingletonRoute}(C)
\ \lor\
\exists C'\,
\text{ScreenedEdge}(C,C').
\tag{R10}
\]

The generic finite-state theorem then gives

\[
\boxed{
\text{first profitable-singleton terminal orbit}
\quad\lor\quad
\text{closed segment of profitable nonsingleton edges}.
}
\tag{R11}
\]

The existing theorem
**not_nonempty_finFourSameStageEndpointClosedSegment** does not eliminate the
second arm of (R11).  Its closed-segment type uses the weak
**QuittingSameStageSingletonRoute** terminal predicate.  Its proof first uses
weak nonterminality to show that every visited coalition has cardinality at
least three.  With profitable terminality, a pair whose singleton exits are
losing is nonterminal, so that step fails.

This is not merely a type mismatch.  The six-edge strict toggle pattern

\[
\{0,1\}\to\{0,1,2\}\to\{0,2\}\to\{0,2,3\}
\to\{0,3\}\to\{0,1,3\}\to\{0,1\}
\tag{R12}
\]

can be realized at the level of strict Boolean endpoint preferences while
all displayed pair-to-singleton exits are rejected as profitable terminals.
The maintained formalization packet for Fin4 pure nonsingleton screening
records this as the precise reason pairs are terminal in the existing
monodromy theorem.

No checked theorem shows that the positive global semantic minimum excludes
the strong-terminal version of (R12).  Claiming an all-paid singleton path
would require a new no-cycle theorem under the full positive-minimum
semantics, or a new potential/account that consumes such a cycle.

## 7. Strongest honest formalizable theorem

The following package is supported by the current proof without new analytic
mathematics.

### Local enhanced dispatch

Define a structure
**QuittingPureNonsingletonProfitableSingletonRoute** containing:

- who and action, with action equal to the exact best endpoint;
- the singleton terminal, its cardinality, and exact routed identity;
- gain equality (R3), strict positivity, and sharp live floor (R4);
- target semantic-pair carrier membership;
- exact mover-debt subtraction (R5);
- source-to-target stage-mass comparison, or the sharper exact pure-target
  mass equality; and
- off-date profile equality or post-date live-root equality.

Then prove

\[
\operatorname{Nonempty}
  (\text{ProfitableSingletonRoute at }C)
\ \lor\
\exists C'\,
  \operatorname{Nonempty}(\text{ScreenedEdge }C\ C').
\tag{R13}
\]

This is a genuine API repair.

### Existing-orbit terminal audit

For a current source-attached Fin4 screened endpoint, prove (R9), with the
local outcome retained as data.  This keeps the same final pair, minimum
source, selected date, live-mass scale, exact paid edge, and tail.  It does
not identify the paid outcome with the endpoint's stored weak singleton
target.

### Optional strong-orbit alternative

The enhanced terminal predicate can also be iterated, but the honest output
is (R11), not an unconditional terminal route.  The closed alternative must
remain visible until separately consumed or excluded.

The note's proposed public result

    profitable singleton route or nonsingleton screened edge

is correct locally.  The proposed Fin4 consequence

    finite all-profitable path ending in a singleton

is not justified.

## Source audit

The following exact declarations and files were inspected.

- **quittingPureNonsingleton_screenedDispatch**,
  **QuittingPureNonsingletonScreenedEdge.gain_floor_live**, and
  **exists_pureNonsingletonScreened_terminalOrbit_or_closedSegment** in
  Research/Quitting/PureNonsingletonCollisionScreening.lean.
- **quittingLiteralSameStage_bestEndpoint_gain_and_debt**,
  **quittingLiteralPureRootProfile_update_eq_routed**,
  **QuittingSameStageEndpointEdge**,
  **QuittingSameStageSingletonRoute**, and
  **quittingSameStageSingletonRoute_of_card_eq_two** in
  Research/Quitting/SameStageEndpointMonodromy.lean.
- **DispatchedOrbit**, **DispatchedClosedSegment**, and
  **exists_dispatchedOrbit_terminal_or_closedSegment** in
  MathUE/FiniteBooleanEndpointOrbit.lean.
- **sameStageEndpointTrace_false_of_effectiveSupport_card_le_four** and
  **not_nonempty_finFourSameStageEndpointClosedSegment** in
  Research/Quitting/SameStageEndpointMonodromyImpossible.lean.
- **FinFourPureNonsingletonScreenedEndpoint.terminal_action_and_card**,
  **edge_gain_floor_live**, **edge_mover_debt**,
  **targetStageMass_eq_liveMass**, **targetProfile_eq_of_time_ne**, and
  **target_postDate_liveRoot_eq** in
  Research/Quitting/FinFourPureNonsingletonCollisionScreening.lean.
- **FinFourPureNonsingletonStrongConcentratedPacket.canonical_edge_gain_floor**
  and the source-attached producer/consumer wrappers in
  Research/Quitting/FinFourProducerAtlas/PureNonsingletonCollisionScreening.lean.
- The maintained boundary and nonclaims in
  formalized/FIN4_PURE_NONSINGLETON_COLLISION_SCREENING.md and the live
  concentrated-singleton obligation in
  questions/FIN4_ATLAS_CONCENTRATED_SINGLETON.md.

The three narrow Research modules named above were rebuilt successfully in
this review.  No Lean source was edited.

## Requested revisions

1. Keep the local API-loss observation and equations (1)--(5), which are
   correct.
2. Separate that local loss from the generic orbit's independent weak
   terminal selection.
3. Withdraw the claim that the existing final route is already the same paid
   edge.
4. Replace the claimed all-paid terminal path by the exact final-pair
   alternative (R9), or by the strong-orbit terminal/closed split (R11).
5. State explicitly that a profitable local singleton target may differ from
   the currently stored weak singleton target and strong packet.
6. Preserve the exact mover-debt and tail fields, but do not infer total-debt
   descent, support descent, cap--Nash, or near-minimality.

## Export assessment

The note does not pass the export gate.  Its proposed global strengthening is
not proved, and the repaired local theorem does not strictly close or narrow
the named remaining obligation in
questions/FIN4_ATLAS_CONCENTRATED_SINGLETON.md.  The current atlas already
reaches the source-attached strong concentrated packet and its existing
consumer.  Adding (R9) gives exact paid data at the final pair, but its
profitable-outgoing-edge arm can re-enter a toggle cycle and neither arm
controls cross-coordinate cap leakage or supplies whole-source return.

The local enhanced dispatch is worthwhile internal API work.  It is not, by
itself, a conjecture-facing export and should not receive a new frontier seal.
