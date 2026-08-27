# Fin4 three-role minimum targets regenerate their actual terminal law and atlas source

Author: `THREE_ROLE_CONSUMER`

Independent review:
[`THREE_ROLE_CONSUMER__TARGET_LAW_REGENERATION_AND_HORIZONTAL_RECURRENCE_BOUNDARY__BY_TARGET_LAW_REVIEW.md`](../feedback/THREE_ROLE_CONSUMER__TARGET_LAW_REGENERATION_AND_HORIZONTAL_RECURRENCE_BOUNDARY__BY_TARGET_LAW_REVIEW.md)

## Exact statement

Let $I=\operatorname{Fin}4$, let

\[
 r:\{S\subseteq I:S\ne\varnothing\}\longrightarrow\mathbb R^I
\]

be a quitting reward table, and let

\[
 \mathsf{source}:\operatorname{FinFourMinimumAtomProducer}(r,M)
\]

be a supplied minimum-atom source.  Write

\[
 z_*:=\mathsf{source.point}.1,
 \qquad
 D_*:=D(z_*)=\inf_\sigma D(\sigma)>0.
\]

Thus `source` retains one fixed Fin4 hard residual, a joint
semantic/terminal-law carrier point, global minimum provenance, positive
literal debt infimum, and a causal finite atom.

Let

```text
packet : QuittingReprojectionConcentratedPacket
  r profiles owner C cutoff scale
```

be a recurrent concentrated packet whose marked coalition $C$ is
nonsingleton.  Put

\[
 \rho:=\mathsf{packet.resolution}>0.
\]

At rank $k$, let $\sigma_k$ be the packet profile, $t_k$ its marked
date, and let $\tau_k$ be the literal profile obtained by replacing one
player's complete strategy by the selected pure endpoint at $t_k$.

Assume:

1. the source semantic debts return to the supplied minimum,

   \[
   D(\operatorname{Sem}(\sigma_k))\longrightarrow D_*;
   \tag{1}
   \]

2. there are fixed players $m,a\in I$ such that, frequently in $k$,
   `packetTransferRoles z_* packet k m a` holds.

The latter is the checked literal three-role transfer predicate.  It retains
a strict actual gain by $m$, exact subtraction from $m$'s unrestricted
behavioral debt, a distinct recipient $a$, and pure routing of the marked
coalition.

Then there exist:

* a Boolean endpoint action $e$;
* a fixed nonempty routed coalition
  \[
  T=\operatorname{Routed}(C,m,e);
  \]
* a strictly increasing sequence of retained ranks $k_n$;
* semantic carrier points $X,Y$; and
* a terminal law $\nu$;

such that, with $\tau_n:=\tau_{k_n}$, all of the following hold.

### Literal actualization and joint convergence

Every selected endpoint action equals $e$, every selected rank carries the
fixed roles $m,a$, and

\[
 \operatorname{Sem}(\sigma_{k_n})\longrightarrow X,
 \qquad
 \bigl(\operatorname{Sem}(\tau_n),
       \operatorname{Law}(\tau_n)\bigr)
   \longrightarrow (Y,\nu).
\tag{2}
\]

The joint point $(Y,\nu)$ belongs to the terminal-semantic/law carrier, and
its first projection is the same $Y$ appearing in (2).

### Fixed routed atom

At every retained rank,

\[
 \rho
 \leq
 \Pr_{\sigma_{k_n}}(C\text{ at }t_{k_n})
 \leq
 \Pr_{\tau_n}(T\text{ at }t_{k_n})
 \leq
 \operatorname{Law}(\tau_n)(T).
\tag{3}
\]

Consequently,

\[
 \boxed{\nu(T)\geq\rho>0.}
\tag{4}
\]

### Actualized three-role chord

The two semantic limits satisfy the existing `ThreeRoleLimitChord`
inequalities.  In Fin4 normalization,

\[
 D(X)=D_*,
 \qquad
 D(Y)\geq D_*,
\tag{5}
\]

\[
 d_m(Y)
 \leq
 d_m(X)-\frac{\rho^2D_*}{8},
\tag{6}
\]

and

\[
 d_a(Y)-d_a(X)
 \geq
 \frac{\rho^2D_*}{64}.
\tag{7}
\]

In particular, exactly one of the following holds.

1. **Strict ascent:** $D(Y)>D_*$.
2. **Minimum-target regeneration:** $D(Y)=D_*$, and there is a fresh
   \[
   \mathsf{next}:\operatorname{FinFourMinimumAtomProducer}(r,M)
   \]
   satisfying
   \[
   \mathsf{next.residual}=\mathsf{source.residual},
   \qquad
   \mathsf{next.point}=(Y,\nu),
   \tag{8}
   \]
   whose named causal terminal is exactly $T$, with
   \[
   \mathsf{next.point}.2(T)=\nu(T)\geq\rho.
   \tag{9}
   \]

The fresh source therefore includes arbitrarily deep, source-matched exact
cap--Nash chronologies causalized at the **actual endpoint joint law**
$(Y,\nu)$, not at an arbitrary law lift of $Y$.

## Conjecture-facing change

The maintained Fin4 atlas leaves a minimum-return `ThreeRoleLimitChord` as
one of its two final consumer classes.  Previously even recursive source
closure at a generic minimum target was not available: the public chord
stores only semantic limits and loses the terminal law and realizing
profiles.

This theorem restores the actual endpoint sequence before compactification
and proves:

\[
\boxed{
\text{generic minimum three-role target}
\Longrightarrow
\text{full Fin4 minimum-atom source regeneration at its own law}.}
\]

Thus target-law attainment and atlas-source reconstruction are no longer
part of the missing theorem.  What remains is orientation: the regenerated
source has not been shown to have smaller finite rank, and the fresh causal
chronology is not asserted to contain the old horizontal endpoint edge.

This is a strict source-provenance reduction, not a terminal or
uniform-equilibrium conclusion.

## Definitions and semantic scope

For an actual behavioral profile $\sigma$,

\[
 U_i(\sigma)
\]

is its terminal payoff, and

\[
 B_i(\sigma)=\sup_{\eta_i}
 U_i(\sigma[i\leftarrow\eta_i])
\]

is the supremum over all unilateral behavioral replacements, including
Never, arbitrarily late stopping, calendar-dependent behavior, and private
randomization.  Set $d_i=B_i-U_i$ and $D=\sum_i d_i$.

The terminal law is the complete probability law on finite nonempty quitting
coalitions together with the all-Never outcome.  Stage coalition mass in
(3) is unconditional: it already includes the probability of reaching the
marked live history.

The joint carrier is the closure of literal pairs

\[
(\operatorname{Sem}(\sigma),\operatorname{Law}(\sigma)).
\]

Membership of $(Y,\nu)$ therefore does not assert that one profile realizes
that point.  The causalization theorem used below constructs a new actual
realizing chronology and does not need attainment.

## Proof

### 1. Freeze all finite endpoint data cofinally

The frequent fixed-role hypothesis supplies a cofinal sequence of ranks on
which the mover and recipient are $m,a$.  The selected endpoint action of
$m$ is Boolean.  One of its two values occurs infinitely often.  Enumerate
that infinite set increasingly and call the resulting ranks $k_n$.

An increasing enumeration of an infinite subset of $\mathbb N$ tends to
infinity.  Hence restricting to $k_n$ preserves (1), every pointwise packet
mass bound, and every eventual small-excess estimate used in the three-role
transfer calculation.

The source coalition $C$, mover $m$, and action $e$ are now fixed, so
the routed coalition

\[
T=\operatorname{Routed}(C,m,e)
\]

is fixed.  Because $C$ has at least two members, inserting $m$, keeping
$C$, or erasing $m$ when $m\in C$ cannot produce the empty coalition.
Thus $T\ne\varnothing$.

### 2. Preserve the routed unconditional mass

The packet field `stageMass` gives the first inequality in (3).  The target
profile changes only $m$'s marked action to the pure endpoint $e$.
`quittingStageCoalitionMass_le_stagePureEndpointRouted` proves that this
operation does not decrease the routed **stage** mass.  Its proof keeps the
live mass unchanged and applies pure endpoint routing only to the root mass,
so no conditional/unconditional conversion is being assumed.

Every occurrence of $T$ at the marked stage contributes to the complete
terminal outcome $T$.  The checked stage-to-outcome inequality therefore
gives the final inequality in (3).

### 3. Compactify the endpoint semantic pair together with its law

Each source semantic point lies in the compact semantic carrier.  Each joint
endpoint point

\[
\bigl(\operatorname{Sem}(\tau_n),\operatorname{Law}(\tau_n)\bigr)
\]

lies in the compact joint carrier because $\tau_n$ is literal.  Compactness
of their product supplies a common subsequence converging to

\[
(X,(Y,\nu)).
\]

and preserves all previously frozen finite data.

Equivalently, one may first compactify the semantic target and then
compactify the joint endpoint sequence along that same subsequence.  The
first projection of the joint limit is exactly $Y$: continuity of the
projection and uniqueness of limits identify it with the already selected
semantic target.  This is the step that an arbitrary carrier-law lift would
not provide.

The law simplex is finite-dimensional, so evaluation at $T$ is continuous.
Taking limits in (3) proves (4).

### 4. Pass the literal transfer inequalities to the limits

Equation (1), cofinality of $k_n$, and continuity of total semantic debt
give $D(X)=D_*$.  Global minimality gives $D(Y)\geq D_*$.

At each selected rank, `ThreeRoleTransfer.gain_quantitative` and
`mover_debt_exact` give a mover loss of at least

\[
\frac{\rho^2D_*}{2\lvert I\rvert}
=\frac{\rho^2D_*}{8}.
\]

The source excess tends to zero.  The checked opposite-face averaging bound
therefore eventually gives the fixed recipient a rise of at least

\[
\frac{\rho^2D_*}{4\lvert I\rvert^2}
=\frac{\rho^2D_*}{64}.
\]

Debt-coordinate continuity passes these inequalities to the limit, proving
(6)--(7).  This is precisely the proof of the public
`exists_threeRoleLimitChord_of_frequently_packetTransferRoles`, with the
actual endpoint law retained rather than projected away.

### 5. Rebuild the minimum-atom source at the same endpoint law

If $D(Y)>D_*$, we are in the strict-ascent arm.

Assume instead $D(Y)=D_*$.  Since $(Y,\nu)$ belongs to the joint carrier,
its semantic projection $Y$ belongs to the semantic carrier.  The equality
with $D_*$ and the incoming source's minimum field prove that $Y$ is a
global semantic minimum.  The incoming fields also give

\[
0<\operatorname{quittingTerminalDebtSumInf}(r)
\]

and

\[
D(Y)=\operatorname{quittingTerminalDebtSumInf}(r).
\]

By (4), the named finite terminal $T$ has positive mass in the same joint
point.  Apply
`exists_deep_nearMinimum_capNashChronologies_with_causalSuffixAtom` directly
to

\[
(Y,\nu),\quad T.
\]

It returns a `QuittingMinimumLawCausalSuffixAtom r (Y,nu)` whose terminal is
literally $T$.  Its fresh actual profiles converge jointly to $(Y,\nu)$,
its exact cap--Nash words have depths tending to infinity, their front debts
converge to the positive literal infimum, and the $T$-atom survives at a
literal shifted suffix stage.

Finally define `next` using:

```text
residual    := source.residual
point       := (Y, nu)
point_mem   := the joint compact-limit membership
semantic_mem := its first-coordinate projection
minimum     := the inherited global-minimum inequality
inf_pos     := source.inf_pos
debt_eq_inf := D(Y) = D_* = source.debt_eq_inf
atom        := the causal suffix atom just constructed
```

This proves (8)--(9) and the theorem.

## Boundary tests

### Alternating endpoint actions

The endpoint action need not stabilize on the original sequence.  The proof
uses only that it is Boolean and passes to an increasing infinite
subsequence.  It does not claim eventual constancy.

### Vanishing live mass

A positive routed root probability would not be enough: its unconditional
stage mass could vanish.  The hypothesis is the packet's unconditional
`stageMass` floor.  This is why (3) remains quantitative after
compactification.

### Public chord without an actualizer

An arbitrary supplied `ThreeRoleLimitChord` does not imply the theorem.  Its
public fields omit the endpoint sequence and law; an arbitrary law lift of
`targetLimit` may have zero $T$-coordinate.  The actual packet and frequent
role witness, or an explicit actualized-chord structure, are essential.

### Strict ascent

When $D(Y)>D_*$, `(Y,nu)` cannot be packaged as a minimum source.  The
theorem makes no regeneration claim in that arm.

### Horizontal cycles

Repeated minimum-target regeneration need not decrease support or any other
known finite rank.  Strict better-response cycles exist in the finite
membership game.  A nonsingleton pure row absorbs immediately, so its
horizontal endpoint edges cannot be placed at successive dates merely by
ordering them.  The theorem deliberately does not call such a cycle a
chronological return.

## Source correspondence

The checked inputs are:

* `QuittingReprojectionConcentratedPacket` in
  `TerminalSemanticResetReprojectionTemporalSplit.lean`;
* `ThreeRoleTransfer`, `packetTransferRoles`, `ThreeRoleLimitChord`, and
  `exists_threeRoleLimitChord_of_frequently_packetTransferRoles` in
  `Research/Quitting/ConcentratedCollisionFourRoleMonodromy.lean`;
* `quittingStageCoalitionMass_le_stagePureEndpointRouted` in
  `TerminalSemanticLiveWeightedCollisionTransfer.lean`;
* `quittingStageCoalitionMass_le_terminalOutcomeMass` in
  `TerminalSemanticPureTimeRectangleDisintegration.lean`;
* joint-carrier compactness and literal-point membership in
  `TerminalSemanticResetIncidenceReturn.lean`;
* `QuittingMinimumLawCausalSuffixAtom` and
  `exists_deep_nearMinimum_capNashChronologies_with_causalSuffixAtom` in
  `TerminalSemanticLawCarrierCausalization.lean`; and
* `FinFourMinimumAtomProducer` in
  `Research/Quitting/FinFourProducerAtlas/Source.lean`.

The new content is the simultaneous retention of the endpoint semantic limit,
endpoint terminal law, and routed positive atom, followed by packaging the
existing same-point causalization as a fresh atlas source with unchanged hard
residual.  The public chord theorem currently discards exactly these data.

No literature theorem is invoked.

## Adapter and downstream use

The actual-data adapter is the checked recurrent concentrated packet plus
frequent fixed `packetTransferRoles`, with source debt returning to the
supplied minimum.  This is the exact input already used by the checked public
three-role chord construction.

In the equality arm, the output is a complete
`FinFourMinimumAtomProducer`, so every checked downstream producer-atlas
construction accepting that type can be restarted at `(Y,nu)`.  This restart
is same-rank unless a separate theorem supplies an orientation.

## Lean handoff

A narrow implementation can introduce:

```lean
structure ThreeRoleActualizedEndpointLaw ... where
  action : Bool
  terminal : {S : Finset (Fin 4) // S.Nonempty}
  ranks : ℕ → ℕ
  ranks_strictMono : StrictMono ranks
  sourceLimit targetLimit : QuittingTerminalSemanticPair (Fin 4)
  targetLaw : QuittingTerminalOutcome (Fin 4) → ℝ
  source_tendsto : ...
  target_joint_tendsto : ...
  terminal_eq_routed : ...
  terminalMass_floor : packet.resolution ≤ targetLaw (some terminal)
  chord : ConcentratedCollisionFourRole.ThreeRoleLimitChord ...
```

and then prove:

```lean
exists_actualizedThreeRoleEndpointLaw_of_frequently_packetTransferRoles

ThreeRoleActualizedEndpointLaw.nonempty_nextSource_of_targetDebt_eq_minimum
```

The first proof should adapt the existing chord extraction, freezing the
Boolean action before taking one compact subsequence in the product of the
source semantic carrier and target joint carrier.  The second should invoke
the generic named-terminal causalization theorem, not the Fin4 wrapper which
reselects an atom.

Focused checks should verify:

1. the output joint limit's first coordinate is definitionally or provably
   the chord target;
2. the routed stage mass is unconditional;
3. the new atom terminal is the routed terminal, not an existentially
   reselected label; and
4. `next.residual = source.residual` is retained literally.

## Scope and nonclaims

This result does not:

* follow from the public chord fields alone;
* assert that `(Y,nu)` is attained by one behavioral profile;
* extend the old endpoint edge into the new cap--Nash chronology;
* preserve the old marked dates or source profiles inside that chronology;
* produce a charged return, terminal approximate Nash profile, or uniform
  equilibrium payoff;
* prove a strict finite-rank decrease; or
* consume horizontal minimum-fibre better-response cycles.

It proves the complete same-law source regeneration needed before any such
oriented consumer can be attempted.

## Formalization record

This packet is formalized by one generic endpoint-law actualizer, one Fin4
regeneration layer, and the actual normalized-return source adapter.

1. `Research/Quitting/ConcentratedCollisionThreeRoleEndpointLaw.lean` defines
   `ConcentratedCollisionThreeRoleEndpointLaw`.  The theorem
   `ConcentratedCollisionFourRole.nonempty_threeRoleEndpointLaw_of_frequently_packetTransferRoles`
   freezes one mover, recipient, and Boolean endpoint action before taking one
   common compact subsequence of the source semantic pairs and endpoint joint
   semantic/law points.  The output retains strict ranks, fixed roles and
   action, both convergences, carrier membership, the routed terminal, and its
   limiting mass floor.  The accessors
   `ConcentratedCollisionThreeRoleEndpointLaw.resolution_le_sourceMarkedStageMass`,
   `ConcentratedCollisionThreeRoleEndpointLaw.sourceMarkedStageMass_le_routedTargetStageMass`,
   `ConcentratedCollisionThreeRoleEndpointLaw.routedTargetStageMass_le_terminalOutcomeMass`,
   and `ConcentratedCollisionThreeRoleEndpointLaw.perRank_mass_chain` expose
   the complete unconditional per-rank mass chain.  The latter retains the
   same explicit nonsingleton hypothesis used by the constructor.
2. The same module proves
   `QuittingMarkedPairMinimumReturnActualizer.nonempty_threeRoleEndpointLaw_of_minimumReturn`.
   It derives the fixed roles from the actual minimum-return packet after
   excluding recurrent tail escape; no public chord, endpoint law, roles, or
   positive terminal atom is supplied by the caller.
   `ConcentratedCollisionThreeRoleEndpointLaw.toThreeRoleLimitChord` is the
   exact forgetful projection to the older semantic-only chord.
3. `Research/Quitting/FinFourProducerAtlas/ThreeRoleRegeneration.lean` states
   the literal Fin4 constants in
   `ConcentratedCollisionThreeRoleEndpointLaw.finFour_mover_drop` and
   `ConcentratedCollisionThreeRoleEndpointLaw.finFour_recipient_rise`:
   `rho^2 * D_* / 8` and `rho^2 * D_* / 64`, respectively.
   `ConcentratedCollisionThreeRoleEndpointLaw.nonempty_finFourRegenerationOrAscent`
   returns strict target-debt ascent or exact minimum-target regeneration.
4. In the minimum-target arm,
   `ConcentratedCollisionThreeRoleEndpointLaw.nonempty_finFourMinimumTargetRegeneration`
   invokes the named-terminal causalization theorem at the retained endpoint
   joint point.  `FinFourThreeRoleMinimumTargetRegeneration.next_residual_eq`,
   `next_point_eq`, `next_terminal_eq`, `resolution_le_terminalMass`, and
   `next_terminalMass_eq_endpoint` show that the fresh
   `FinFourMinimumAtomProducer` has the incoming hard residual, the exact
   endpoint semantic/law point, the retained routed terminal, and precisely
   that terminal's endpoint-law mass, still at least `rho`.
5. `Research/Quitting/FinFourProducerAtlas/NormalizedReturn.lean` derives the
   actual decorated family, compact subsequence, convergent passport,
   enlarged-slice minimizer, minimum-return actualizer, endpoint law, and
   regeneration/ascent result from one fixed
   `FinFourOwnerCompressedMinimumReturnForcedPairPacket`.
   `FinFourOwnerCompressedMinimumReturnForcedPairPacket.nonempty_normalizedReturnThreeRole_or_strictInert`
   stores the strengthened equality branch, while
   `FinFourNormalizedReturnThreeRoleOrStrictInert.threeRole_or_strictInert`
   preserves the previous public chord surface as a forgetful theorem.
6. `FinFourMinimumAtomProducer.exists_normalizedReturnSource_for_all_resolutions`
   fixes one minimum-atom chronology and table-selected outsider before every
   admissible `lambda`.  The packet, compact subsequence, actualizer, endpoint
   roles and action, minimizer, and outcome may depend on `lambda`.
   `FinFourNormalizedReturnSourceCapstone.regenerationOrAscent_or_strictInert`
   is the source-level strongest displayed outcome.

Evidence seals:

- **M:** PASS.  The fixed-role extraction, common compactification, mass
  routing, exact debt constants, and same-point causalization match the
  reviewed proof and preserve all quantifiers.
- **L:** PASS.  Every declaration named above checks in Lean under the stated
  imports.  Promotion checks include direct and named builds, the Research
  reader, full build, generated axiom audit, trust, documentation,
  import-graph regression tests, proof-duplicate, derivable-telescope, and
  line/diff hygiene checks.  Important axiom prints use only `propext`,
  `Classical.choice`, and `Quot.sound`.
- **A:** PASS for the normalized Fin4 equality arm.  The actual source packet,
  compact selection, passport, minimizer, actualizer, roles, endpoint action,
  endpoint terminal law, and routed atom are constructed rather than accepted
  as certificates.  The generic endpoint-law theorem by itself remains a
  supplied-packet compiler.
- **C:** PASS for the equality branch through the endpoint-law
  ascent/regeneration classifier, and through a complete regenerated
  `FinFourMinimumAtomProducer` in the minimum-target subbranch.  The strict
  enlarged-slice inert arm and the strict endpoint-ascent node have no further
  checked completion consumer.

The endpoint joint point is a compact-carrier limit and need not be attained
by one behavioral profile.  The fresh causal chronology does not contain the
old endpoint edge or preserve its dates and source profiles.  Regeneration is
not a chronology return and has no proved support or finite-rank decrease.
An arbitrary public `ThreeRoleLimitChord` does not determine the endpoint law.
There is no recursive closure, charged return, terminal approximate Nash
profile, uniform-equilibrium payoff, or counterexample theorem.

The mathematical provenance remains this packet and the independent review
linked at its head.  No external literature theorem is imported.
