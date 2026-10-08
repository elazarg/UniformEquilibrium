# Fin4 bird’s-eye path: robust strategic relays, then actual clocks

Owner: CODEX_MORSE.

Status: EXPLORATORY SYNTHESIS, not a proof, a new counterexample-class
reduction, or an export candidate. The conjecture remains open.
The requested endpoint is UE for EVERY signed four-player quitting table,
against EVERY unilateral behavioral deviation, with ONE payoff target
fixed before the requested accuracy.

This refresh replaces the earlier suggestion that a useful exact
continuation index should simply persist. Exact Nash paths can have
bounded charge on the ENTIRE payoff box even in a solved game.
The stronger surviving idea is a globally selected, absorption-relative
robust relay. Its strategic selection theorem is UNPROVED and is the
main mathematical gap, not an index fact already available.

## 1. The decisive picture

My strongest current intuition is:

> A useful equilibrium circuit need not exist as a finite exact Nash
> circuit. It can exist as a circuit of strategically compatible
> LIMITING ports whose finite approximations recharge at a corner.
> The error at that corner must be bought with actual absorption.

Think of continuation payoffs as prices for the future the construction
will really supply. A root is a transaction at those prices: independent
Quit/Continue coins buy terminal rewards now or the stated continuation.
A profitable early deviation and a profitable late deviation are two
different invoices. The construction succeeds only when the whole
itinerary prices both; naming a higher cap does not pay the invoice.

There are three physical moves:

1. a finite exact root, possibly a macroscopic simultaneous collision;
2. a finite stretch of small exact or approximate roots approaching
   a limiting continuation port;
3. a small charged connector that changes the active owner set at a
   nearly matched port, with both incentive and payoff errors bounded
   by tolerance × its own absorption.

The third move is the important addition. It is not an arbitrary jump
between nearby prices. A passive player may be unwilling to activate,
and an incumbent may become profitable after the jump. ALL four root
inequalities still have to be checked.

In the successful EC test, a ladder ends with error E, while a new
supplier can be activated with hazard r=√E. Its active regret is rE,
other root inequalities remain safe, and the port mismatch is O(E).
Consequently both errors divided by the new absorption r go to zero.
This gives a literal finite word at every tolerance, not a concatenation
of infinitely many clocks followed by a root “after infinity.”

The global intuition is that payoff obligations can relay between
owners rather than disappear after one response. Four-player product
roots should supply the missing coordination moves when a singleton
relay becomes blocked. Proper-child equilibrium constructions offer
other routes around a blocked port, but their outsiders must remain
priced in the ambient game. The mechanism selects a WHOLE compatible
relay, not a good next root at every possible port.

The unproved part is exactly why an arbitrary surviving table must
contain at least one such relay, or a correctly punishment-priced
absorbing exit. Neither “there are only four owners” nor ordinary
Nash degree establishes it. The rest of this note makes that obligation
concrete and separates it from the actual-clock endpoint.

## 2. The endpoint and the honest state of knowledge

The reward data are sixty real numbers r_i(S), for four recipients and
fifteen nonempty terminal coalitions. Never and live payoffs are zero.
The live date selecting a coalition pays zero; absorbing rewards begin
afterwards. Before absorption there is one public history. A player’s
entire behavioral deviation is an arbitrary stopping law on ℕ∪{Never}.

For an actual profile let U_i be prescribed payoff and B_i its complete
best-response cap. Write d_i=B_i−U_i≥0 and D=∑[i]d_i. A pure response
may stop at ANY finite date or Never. Bounds on a finite response menu
alone do not bound B.

It is enough to produce, for EVERY η>0, an actual profile with
B_i−U_i≤η for all four players. Compact payoff selection then produces
ONE fixed UE payoff; the strategy can depend on accuracy, the payoff
target cannot. The tracked terminal selection theorem supplies this
last passage, including sufficiently long finite horizons and all
behavioral deviations. Merely producing small stage regrets is not
that endpoint.

Existing arbitrary signed three-player existence is important, but
does not automatically lift to four players: the fourth player may
join profitably. Existing four-player inverse, matching, cyclic,
stationary, boxed-charge, weighted-floor, persistent-base and other
raw producers cover genuine classes, not all table space.

The reviewed scalar singular-circuit class adds a concrete producer:
a reward-only interval criterion yields common ports, exact ladder
inequalities and a closed circuit; finite reverse-order periodic
execution controls all full caps. It has a full sixty-coordinate open
chamber and a recipient-specific fourteen-coordinate free cylinder.
Its role here is EVIDENCE for the mechanism, not arbitrary-game coverage.

The strongest reviewed counterexample source is more restrictive.
If any counterexample exists, ONE fresh table can be selected with
positive own rewards and

    0<δ=Δ_all<Δ_abs=δ+g,       g>0.

Every original full-carrier minimum has the SAME debt vector d*,
strictly positive in EVERY coordinate. All four Never masses are
positive. A first random nonsure collision has a paid owner tying an
early and a later FINITE full-cap test, with different payoff kernels
on a positive opponent event.

This is the reviewed fully-paid nonsure finite-bridge source.
It has not been consumed. Its compact minima need not be attained
by raw integer-clock profiles, and its conditional tails need not
be Nash or minimizing. Its source does not silently retain the older
contact spectra or zero-debt four-finite-clock conclusions.

The current problem is therefore not a missing compactness theorem
or a missing finite strategy syntax. We have strong sources and
compilers. What is missing is a GLOBAL choice that yields a usable
whole word, rather than an exact but strategically sterile component.

## 3. Brief comparison with genuinely different global paths

Three alternatives deserve to remain independent.

**Whole-table perturbation.** Passive taxes keep own singletons fixed:
subtract a parameter from recipient i only when i is absent from the
terminal coalition, leaving Never zero. NOETHER’s live attempt has
zero-gap boundary constructions when any one parameter is sufficiently
large positive or negative. A positive worst tax would therefore be
interior. This may force a joint variational contradiction involving
ALL moving minimizing profiles and tied responses. That interior
consumer is open. A fixed-active-profile derivative is false, and an
interior maximum alone does not identify an equilibrium. This is a
genuinely different promising route, not a lemma of the relay picture.

**Native absorbing existence.** A reduction passes through all-own-zero
rewards with a positive absorbing gap; ordinary AllNever equilibrium
there is irrelevant. Proving absorbing approximate Nash for EVERY
own-zero table would close the original problem. True absorbing minima
have useful strict margins, but the positive-Never full minima and the
absorbing minima are different objects. Small or large row shifts do
not identify them or supply an executable continuation. This route
might avoid the continuation graph entirely; it currently lacks an
all-law absorbing producer.

**Whole-law repair or a negative certificate.** An actual finite-amplitude
change could directly lower the positive global SUM minimum.
Alternatively, a rational robust polynomial certificate on the WHOLE
fixed payoff box plus the correct no-sure-root hypothesis could certify
an actual counterexample. Both are conjecture-facing routes. Stationary
failure, exact-root monotonicity, bounded exact capacity, or a supplied
barrier are not sufficient negative certificates.

My choice here is the robust-relay route because the EC and reviewed
scalar-class constructions show a concrete way around exact-path
failure. It is not chosen because the other routes are disproved.
Its distinctive claim is about strategically completing singular
ports with finite absorption-relative errors, followed by global
component selection. Ordinary continuation index is only a possible
accounting device for that selection, not the proposed engine itself.

## 4. The relation that must actually be used

Fix ONE table, |r_i(S)|≤M, and a fixed box K=[−M−2,M+2]⁴.
Own singleton rewards are s_i=r_i({i}). For independent root rates
q∈[0,1]⁴ let

    c(q)=∏[i](1−q_i),       a(q)=1−c(q),
    h_i(q)=∏[j≠i](1−q_j).

Against continuation price v define

    Q_i(q)=∑[A⊆I\{i}]Pr_{q_-i}(A)r_i(A∪{i}),
    C_i(v,q)=∑[A≠∅]Pr_{q_-i}(A)r_i(A)+h_i(q)v_i,
    F_i(v,q)=q_i Q_i(q)+(1−q_i)C_i(v,q),
    e_i(v,q)=max(Q_i(q),C_i(v,q))−F_i(v,q).

Q and C are actual Quit and Continue endpoints. Exact root Nash is
e_i=0 for every i, including quiet and sure coordinates.

At positive tolerance τ the permitted robust edge (v,q,y) satisfies

    ‖y−F(v,q)‖_∞≤τ a(q),
    e_i(v,q)≤τ a(q) for EVERY i,
    v,y∈K.

The label q and its PHYSICAL charge a(q) are retained. Convex mixtures
of distinct successor prices are not declared edges. This is the
floor-free robust relation in the actual polynomial characterization;
a different floor-constrained relation must not replace it silently.

The desired global output is, for EVERY τ>0 and charge request L,
a finite compatible word of these edges with total charge at least L,
OR an exact sure Nash root at the true punishment vector. K is fixed
before τ and L. This is the already checked fixed-box UE endpoint
under normality and a positive singleton, not a new supplied-object API.

Construction order prefixes roots outward; chronological play reverses
the finite word. No response update, tax change, or table reselection
is inserted as a chronological move.

A useful mental compactification records limits of finite exact paths
whose total charge is finite. It can retain the limiting port and the
charge already accumulated. It DOES NOT declare a transition from
that port executable. An executable continuation exists only after
a finite approximation and a verified robust connector are supplied.

## 5. The proposed global mechanism, with its missing bridges exposed

### 5.1 First resolve intrinsic children, but keep their observers

Suppose a candidate relay is confined to a proper player subset.
Its intrinsic problem has at most three players, for which existence
is already known. Use its actual approximate clocks or root words,
not just a child payoff vector.

Now inspect the omitted players’ COMPLETE caps. If all are safe, that
child construction is an ambient equilibrium and the search ends.
If not, the unpaid outsider response is a concrete inequality for a
larger ambient root or a different itinerary. It is not a proof that
simply turning on the outsider repairs the old circuit.

Plausible bridge, UNPROVED: the actual intrinsic construction and its
violated observer inequalities produce either a new compatible ambient
relay segment or a globally alternative component, without permanently
losing the charge budget.

Why it might hold: child solutions supply real continuation ports and
full-clock inequalities; independent product roots supply the coalition
events that a singleton-only account discards. Pair and triple joining
conditions already yield several positive raw producers. But mixed
joining signs, spectator activation and nonlocal port compatibility
can obstruct a PARTICULAR component. The bridge must select globally
rather than promise a successor for every child or feasible price.

### 5.2 Resolve finite-charge sinks by strategic recharge

A selected exact path may have all owners active, positive relative
rates and finite total charge, then converge to an own-threshold port.
Discarding it as a failed infinite path throws away useful limiting
information. Its limit might lie on another charged branch.

The EC calculation supplies the constructive template:
truncate the old ladder close enough; take a new owner’s small root;
ensure quiet inequalities; choose its hazard much larger than the
truncation error but still small. Then match to the new branch with
error at most τ times the new physical charge. The old finite exact
capacity can jump at this corner, although the robust connector closes
the finite circuit.

Plausible bridge, UNPROVED: globally chosen limiting ports admit
such recharge, or a literal joint-root alternative, or a correctly
punishment-priced exit. The bridge must also handle competitive
binding owners where small simultaneous activation is unfavorable.

The restriction “globally chosen” is substantial. GS shows that
a unique fair exact path can converge with finite charge and a
positive terminal debt floor. RM37 shows that a feasible strict-below
port may have only a root whose successor leaves the desired region.
An arbitrary path, a fixed threshold domain and a local spectator
repair do not satisfy this bridge.

At a competitive corner the intended operation is NONLOCAL:
search other roots and other continuation ports, possibly make a
macroscopic product-root move, and return through a different child
or collision cell. The exact fixed-box relation permits above-own
excursions. It does not require staying in a singleton sublevel set.
Whether such a compatible itinerary is forced is open.

### 5.3 Select a relay globally, rather than following any next root

This is the weakest bridge and the decisive mathematical problem.

Proposed claim: in an arbitrary normal four-player table with a
positive singleton, absence of a true punishment-priced sure exit
forces a robustly usable component of the COMPLETE continuation
relation, not merely an ordinary index-carrying quiet component.

One possible proof would give a relative continuation index to
FULL Nash witnesses, physical charge and compatible ports, with
singular ports completed only by actual robust connectors.
It would show that all essential mass cannot be trapped on the
strict all-Continue sheet or competitive finite-charge sinks.
No such invariant or conservation theorem is proved here.

Why this might be true: an unsafe proper core supplies a concrete
joining constraint, not an arbitrary topological boundary label.
Four-player product-root equations tie every observer constraint
to the same finite reward table. A genuine full graph may force
a closed obligation relay even when its coarse matrix or boundary
field does not. The reviewed singular class exhibits a mixed
triple/pair relay; EC exhibits sequential corner recharge.

Why that intuition is not yet convincing as a theorem: coalition
labels can recur with different ports and incompatible future prices.
There is no monotone support rank. Four owners do not rule out nested
accumulation or acyclic global flow. A useful proof must derive a
table-specific obstruction to COMPLETE trapping; “no fifth observer”
is not that derivation.

The negative-certificate formulation makes the challenge falsifiable.
Under no UE the actual characterization supplies a positive rational
τ and rational polynomial P, bounded on K, strictly falling by
physical charge on EVERY permitted robust edge:

    P(y)+a(q)≤P(v).

Global selection must produce an actual finite word exceeding
the oscillation of THIS P, or otherwise contradict this all-edge
inequality using the SAME table’s strategic equations.
An exact-root path or abstract degree calculation cannot do it.

This is not an exportable conditional theorem: “assume the useful
component exists” would simply assume the missing producer.
The candidate contribution is the recharge mechanism and the
specific global selection question, not a solved existence bridge.

## 6. Full route, if those strategic bridges can be proved

Start from an arbitrary signed four-player table. Existing positive
branches may finish it, but their union is not assumed exhaustive.
For contradiction assume no UE. Actual abnormal-player and normal-core
adapters give a normal residual; single-pivot normalization gives a
normal table with one positive own singleton and the others zero.
This is an actual semantic adapter, not inverse affine invariance
with Never fixed. Alternatively select the reviewed NP table.
Use ONE of these tables for the entire graph argument.

At that fixed table:

1. If the true-punishment exact sure-root exit exists, consume it by
   the checked original-game payoff theorem.
2. Otherwise keep the full robust continuation relation. Begin with
   actual child constructions, full roots and their exact port data.
   Use global selection, not a demand that every feasible port works.
3. Retain finite-charge limiting arcs, but complete them by verified
   finite charged connectors. Include literal macroscopic collision
   roots and unsafe observer inequalities. Permit above-own excursions,
   component changes and nonlocal itinerary reselection.
4. Force finite absorption-relative words at every τ and requested
   charge. Equivalently, exclude the bounded robust polynomial rank
   forced by no UE. This is the substantive UNPROVED global step.
5. Apply the checked fixed-box packet/actual-profile endpoint.
   Produce actual independent stopping laws with all finite/Never caps
   controlled at every prescribed terminal accuracy. A supplied UE-tail
   jump–flow closure is not a substitute for this unconditional compiler.
6. Select a subsequence of terminal approximate Nash payoffs. Compact
   payoff selection gives ONE fixed uniform target and all sufficiently
   long finite-horizon behavioral-deviation bounds. Transport through
   the actual normalization adapter if that route was used.

All surviving branches are assigned a place, but NONE is declared
solved just by that assignment. A quiet exact fibre, a competitive
ghost endpoint, a random paid collision and a sole-sure deleted tail
are genuine strategic obligations of Steps2–4.

## 7. Why the positive-Never source and leakage are not omitted

At the NP table every minimum is fully paid, all Never masses are
positive, and Δ_abs exceeds Δ_all by g. A positive-debtor best reply
leaves the common-debt minimum family by a macroscopic amount.
The global construction is allowed to leave that family completely;
minimum-return resets are not assumed.

Repeating an old block has exact caps

    max(B_i, R_i/(1−h_i)),

where R_i is refusal/Never payoff in the block and h_i its deleted
survival. The born-cap debt is genuinely positive at the source.
Thus old-block repetition is NOT the proposed recharge operation.

A relay instead changes the continuation ports, rates and possibly
the order and supports before closing the word. It must price
every Quit-now and Continue-to-later response against the SAME
future. A paid first/later tie is a warning that those phase choices
are coupled, not an admissible free bridge to be pasted twice.

For a real tail pair (u,b), the full prefix semantics are

    u'_i=q_i Q_i+(1−q_i)(A_i+h_i u_i),
    b'_i=max(Q_i,A_i+h_i b_i),

with A_i the passive-opponent contribution. If u=b=v and the root is
Nash at v, both coordinates become F_i(v,q). An arbitrary price v is
not an actual diagonal tail; only the eventual actual compiler
justifies replacing annotations by realizable continuations.

For a periodic finite circuit with two fixed distinct suppliers,
EVERY deleted period has survival κ_i<1. Root-level errors accumulate
through the max-affine cap map, with geometric denominator 1−κ_i.
Never is included by sending the number of periods to infinity.
A sole sure supplier does NOT screen its own deleted tail; use the
true punishment value. For general charged packets the integrated
compiler handles the persistent-owner alternatives rather than
assuming joint absorption controls every player-deleted process.

Success at this SAME NP table would yield D<δ, a contradiction.
Relative gap closeness at another table, a cap increase at the old
minimum or a companion absorbing minimum is not success.

## 8. Decisive tests the proposed mechanism must survive

### A. EVERY exact menu selector can be bad

NOETHER RM38 gives a complete rational four-player table for which
the ENTIRE exact equilibrium correspondence on dates0,…,N,Never
consists of one delayed final root. Every N leaves FULL debt7/8:
a pure date beyond N is missed. The table is already covered by a
tracked raw triple inverse producer.

Therefore no selection among exact menu equilibria, however global,
can prove the general endpoint by those equilibria alone.
Approximate FULL-cap finite laws are not excluded. The relay picture
allows such laws rather than claiming exact menu equilibrium is dense
in the useful endpoint correspondence.

### B. Feasible strict-sublevel ports need not have a sublevel successor

NOETHER RM37 has own values1, true punishment
(−10,−3/2,−3/2,−10), and no sure root at ANY annotation above them.
At a feasible port v=(0,2,2,0), the FULL root is uniquely
q=(1/2)⁴ and its head is

    (7/2,47/16,27/10,21/8)> (1,1,1,1).

Its normal-core, R₀, degree1 and positive-simplex screens hold.
The exact admissible singleton-sublevel successor assertion fails.
It is not a no-UE source. Global selection may avoid that port or
use its above-own excursion; it may NOT infer a viable whole
threshold region from these raw premises.

### C. Unique fair all-active paths can stall

GS gives an actual full-table eigencone with UNIQUE full roots,
all four suppliers uniformly positive in projective proportion,
and feasible prices between true punishment and own singletons.
Every selected exact path has finite total charge and converges
to a quiet own port. Its finite forced-prefix family has an explicit
positive late-deviation debt floor.

Fairness, uniqueness, feasible prices and repeated use of all four
owners do not establish proper execution or good global selection.
The relay must genuinely reselect or recharge; it cannot attach a
free next root to that limit.

### D. Whole-box bounded EXACT capacity can coexist with UE

EC gives no sure root at ANY annotation and bounds the charge of
EVERY finite exact Nash path in the entire fixed box by1+log5.
Nevertheless four exact Zeno ladders have compatible limiting ports.
Verified finite corner connectors at EVERY positive relative tolerance
close a charged circuit, and literal periodic reverse-order profiles
have vanishing ALL-cap debt and one fixed payoff limit.

Thus “all exact finite paths have bounded charge” is not a negative
certificate. The exact cost-to-go has an upward discontinuity at
a recharge port. A continuous robust polynomial separator cannot
ignore it. This is the clearest positive test of the revised picture.

### E. Ordinary index and coarse boundary cones miss physical charge

NOETHER’s NG has ordinary full Nash index+1 concentrated on a unique
strict quiet fibre at a genuine positive-minimum cap. BD supplies a
nonvanishing extension pricing ALL literal boundary cones in a solved
table, with coarse degree0 despite a real charged circuit elsewhere.
R₀/StandardQ/full core and cone geometry alone do not select a useful
branch. A new relative invariant must carry actual Nash/port/charge
data, or it is measuring the wrong object.

### F. A nearby good circuit may disappear completely

CI’s one-entry perturbation kills EVERY nearby version of an old
four-stage circuit, including activation of the tied spectators,
while remaining inside a reviewed UE chamber. Robustness of UE
does not imply nearby continuation of that chosen itinerary.
The global route permits extra phases and NONLOCAL reselection.

### G. The adversarial no-UE source, not just solved fixtures

Finally apply the claimed selection rule to ONE fully-paid nonsure
NP table with δ,g,d* and its full early/later cap family.
It must output an actual packet/profile with D<δ, not only pass
TestsA–F on solved tables. Failure here would expose a missing
global selection premise rather than justify a new local assumption.

## 9. One concrete research target, and the weakest point

The next target is not another generic local root lemma. It is the
following specific attempt to make global recharge selection testable:

> Starting from the WHOLE robust relation of a surviving normal table,
> can finite-charge trapping be localized to a finite family of actual
> limiting ports, and can the COMPLETE joining/withdrawal equations
> rule out all its exits being simultaneously non-rechargeable?

A successful localization must retain the permitted relative tolerance,
literal root witnesses and port incidence. It may use semialgebraicity
at fixed positive τ; it may not replace approximate paths by exact
ones or convexify the root image. A finite family of obstruction labels
would permit an exhaustive actual-table algebraic test. An accumulation
of incompatible ghost ports would falsify that finite localization
and require a different global mechanism.

The first bounded test is whether the apparent coordination escape
at a port with two binding owners and reciprocal positive pair joins
actually discharges any of these simultaneous exit equations.
Existing strict-ray binding-pair and box-complementarity producers
must be checked first. Even a nonzero root would only solve the
LOCAL root obligation; it would not supply a return or a usable
component. If its hypotheses cannot be produced by the global trap,
do not turn the generic lemma into the next research deliverable.

The weakest bridge remains global strategic selection, especially
competitive trapping and nested singular ports. I do not presently
have a convincing rigorous argument that all signed tables force a
relay. The plausible intuition is an obligation cycle with physically
paid transfers; the actual proof must exclude simultaneous dead ends
using game-specific equations. That is stronger than the older
“essential index must continue” slogan and still genuinely open.

## 10. Exact evidence and source scope

This synthesis used the current conference FRONTIER and GOAL,
architecture notes on executable compact state, semantic barrier
duality and neutral chronology, and bounded exact-source navigation
through docs/FRONTIER.md and docs/TOOLKIT.md. No broad Lean census
or new literature survey is claimed.

Tracked declarations read under their imports:

- quittingGame_exists_uniformEquilibriumPayoff_iff_fixedBoxPackets_or_sureRoot,
  in UniformEquilibrium/Quitting/Projective/FixedBoxForwardCharacterization.lean;
- quittingGame_not_exists_uniformEquilibriumPayoff_iff_noSureRoot_and_rationalPotential,
  in UniformEquilibrium/Quitting/Projective/PolynomialForwardCertificateCharacterization.lean;
- the literal robust edge definitions, in
  UniformEquilibrium/Quitting/Projective/RobustChargedRelation.lean;
- IsQuittingFullExactRootPotential and its robust-potential restriction,
  in UniformEquilibrium/Quitting/Projective/ExactRootPotentialRestriction.lean;
- IsQuittingFullExactRootPotential.minimum_above_singleton and the
  arbitrary-minimum variants, in
  UniformEquilibrium/Quitting/Projective/FullExactRootPotentialMinimum.lean;
- quittingGame_exists_uniformEquilibriumPayoff_of_terminalNash_all_errors,
  in UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean.

CyclicSingletonTailData.certificate and its payoff consumer, in
UniformEquilibrium/Quitting/Cycles/CyclicSingletonTailProducer.lean,
already cover the EC table. EC is therefore a mechanism falsifier,
not new existence coverage. The current scalar singular-circuit export
is an independently reviewed ordinary raw-class theorem, not an
unconditional Lean theorem for all Fin4.

The fully-paid nonsure source is the reviewed ordinary packet
[ FULLY_PAID_NONSURE_FINITE_BRIDGE_SOURCE ](../exports/FULLY_PAID_NONSURE_FINITE_BRIDGE_SOURCE.md).
The independent scalar raw producer is
[ SCALAR_SINGULAR_CIRCUIT_UNIFORM_EQUILIBRIUM ](../exports/SCALAR_SINGULAR_CIRCUIT_UNIFORM_EQUILIBRIUM.md).
The exact GS, EC, CI and older menu/nonconvex tests remain in the
owned [global notebook](CODEX_MORSE__GLOBAL_QUITTING_OBSTRUCTION.md).
RM37–RM38 and BD/NG are in
[NOETHER’s notebook](CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION.md),
with their ordinary-versus-reviewed status retained there.

No Lean implementation, build, export placement or Git action
belongs to this exploratory synthesis. None of its unproved
strategic bridges is a theorem.
