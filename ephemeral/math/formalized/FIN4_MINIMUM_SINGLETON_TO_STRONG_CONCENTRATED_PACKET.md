# A positive stage atom produces a strong concentrated packet

Authors: `STRENGTHENER`

Independent reviews:

* [`ATLAS_FALSIFIER`](../feedback/STRENGTHENER__MINIMUM_SINGLETON_TO_STRONG_CONCENTRATED_PACKET__BY_ATLAS_FALSIFIER.md)
* [`ATLAS_GATEKEEPER`](../feedback/STRENGTHENER__MINIMUM_SINGLETON_TO_STRONG_CONCENTRATED_PACKET__BY_ATLAS_GATEKEEPER.md)

## Exact statement

Let `iota` be a finite player type with decidable equality. Let `r` be any
quitting-game reward table on `iota`, let `tau` be one actual behavioral
profile, fix a nonempty terminal coalition `A`, a player `o`, and a date `t`.
Assume

\[
 A\ne\{o\},
 \tag{1}
\]

and put

\[
 m:=\Pr_\tau(\text{terminal coalition }A\text{ occurs at }t).
 \tag{2}
\]

Assume `m>0`. Let

\[
 z^+:=\operatorname{Sem}(\operatorname{tail}_{t+1}\tau),
 \qquad x:=\operatorname{root}_\tau(t),
\]

and let

\[
 a:=\operatorname{BestEndpoint}_o(r,(z^+)_U,x)\in\{C,Q\}.
 \tag{3}
\]

Define the actual target profile by the literal constructor

```lean
rho := quittingLiteralOneDateProfile r tau o t a
```

which changes only `o`'s action at date `t` to the pure action `a` and copies
its entire behavior strategy at every other date, including off-live
histories. Define

\[
 R=
 \begin{cases}
 A\setminus\{o\},&a=C,\\
 A\cup\{o\},&a=Q.
 \end{cases}
 \tag{4}
\]

The coalition `R` is nonempty: this is automatic in the Quit case, while in
the Continue case emptiness would force the nonempty coalition `A` to equal
`{o}`, contrary to (1).

Then:

1. the probability of reaching `t` is unchanged;
2. every live root before and strictly after `t` is unchanged;
3. the complete post-row behavioral tail, its prescribed payoff, and its
   semantic pair are unchanged;
4. the marked atom routes without loss:
   \[
   m\le\Pr_\rho(\text{terminal coalition }R\text{ occurs at }t); \tag{5}
   \]
5. `o` has exact zero local coordinate Nash defect at the updated row against
   the unchanged actual tail:
   \[
   \operatorname{Defect}_o((z^+)_U,\operatorname{root}_\rho(t))=0. \tag{6}
   \]

For every `lambda` with `0<lambda<=m`, repeat `rho` as a constant sequence,
use constant mark `t`, constant cutoff `t+1`, any positive scale tending to
zero, the identity subsequence, terminal `R`, and resolution `lambda`. These
data instantiate

```lean
QuittingReprojectionConcentratedPacket
  r profiles o terminal cutoff scale
```

and its normalized defect expression is identically zero. In particular one
may take `lambda=m`, so there is no loss in the source stage-mass constant.

The singleton version used by the Fin4 atlas is the special case `A={j}` and
`o!=j`: Continue routes to `{j}`, while Quit routes to `{j,o}`.

### Fin4 atlas corollaries

Every checked `FinFourAtlasWeakConcentratedSingletonCore source` supplies one
literal target profile, date, singleton terminal, positive resolution, and a
stage-mass lower bound. Therefore every such weak core produces the strong
packet at the same resolution.

This consumes all three weak singleton origins:

* the purified-singleton origin;
* the terminal-orbit singleton origin; and
* the owner-compressed minimum-law singleton origin.

For the third origin, if the selected minimum-law singleton mass is `mu>0`,
then every fixed `lambda<mu` is available through the checked owner-clock
compression and hence produces a strong packet of resolution `lambda`.

No terminal exploitability witness, minimum-fiber debt condition, or
assumption on the singleton owner's debt is used.

## Conjecture-facing change

This proves acceptable answer 1 of
[`questions/FIN4_ATLAS_DIFFUSE_MINIMUM_SINGLETON.md`](../questions/FIN4_ATLAS_DIFFUSE_MINIMUM_SINGLETON.md).
The diffuse minimum-law singleton leaf, and indeed every weak singleton core,
enters the existing strong recurrent concentrated node:

\[
 \boxed{
 \text{positive actual singleton stage atom}
 \Longrightarrow
 \text{strong concentrated packet with no mass loss}.}
 \tag{7}
\]

The source-attached Fin4 packet now also has a checked downstream contraction.
It yields either the existing concentrated strategic dispatch together with
an atomic-toggle or exact-deletion handoff, or the existing collision-minimum
residual on the same literal packet.  This consumes the weak singleton
entrance only to that disjunction; it does not close the collision residual or
complete the strong concentrated node.

There is an important limitation: existence of the packet type by itself is
not a restriction on reward tables. In any finite game with at least two
players, prescribe any nonempty pure coalition `A` at date zero, choose `o`
with `A!={o}`, and apply the generic theorem at its mass-one atom. Thus every
such game has some `QuittingReprojectionConcentratedPacket`. The atlas content
is only the retained attachment to its selected actual endpoint and literal
tail. Any downstream conjecture-facing consumer must use that external
source/minimum provenance; a theorem using only the packet fields would be a
universal quitting-game theorem.

## Definitions and assumptions

A behavioral quitting profile gives one mixed Quit/Continue action at the
unique live history at each date. Equivalently, the players have independent
complete stopping clocks in `Nat ∪ {infinity}`. Play stops at the least finite
clock and the terminal coalition is the set tied there. Stage masses in this
result are unconditional probabilities in the displayed actual profile.

The endpoint action in (3) compares the two exact one-row payoffs for `o`
against the opponents' current product root and the actual prescribed payoff
of the literal post-row tail. Ties are resolved in favor of Continue, matching
`quittingRootBestEndpointAction`.

The update is one legal behavioral deviation at one live row and copies the
same behavior afterwards. The theorem makes no stationarity, finite-horizon,
minimum-attainment, or marginal-limit assumption. It does not replace the
tail payoff by a semantic cap.

## Source correspondence

The local objects and transport facts are checked in the following files.

In `Research/Quitting/SameStageEndpointMonodromy.lean`:

* `quittingLiteralOneDateOverride` and
  `quittingLiteralOneDateProfile` provide the literal constructor;
* `quittingProfileLiveRoot_literalOneDateProfile` identifies its marked root;
* `quittingLiveMass_literalOneDateProfile_eq` proves exact reach preservation;
  and
* `quittingProfileLiveRoot_literalOneDateProfile_tail_eq` preserves every
  post-date live root.

In
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPlateauLocalizedOtherDefect.lean`:

* `quittingRootBestEndpointAction` selects the better exact pure endpoint;
* `quittingRootSuccessorPayoff_bestEndpoint_sub_eq_coordinateNashDefect`
  records the exact gain from selecting that endpoint.

In
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPlateauDefectStratification.lean`:

* `quittingRootCoalitionMass_le_pureEndpointRouted` proves no-loss root-mass
  routing; and
* `quittingPureEndpointRoutedCoalition_four_way` identifies the routed
  coalition. It is `A.erase o` for Continue and `insert o A` for Quit; in the
  singleton atlas specialization `o` is outside `{j}`, so these become `{j}`
  and `{j,o}`.

The target structure and generic semantic incidence are checked in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticResetReprojectionTemporalSplit.lean`:

* `QuittingReprojectionConcentratedPacket`; and
* `positive_stageCoalitionMass_has_semanticPrefixIncidence`.

The Fin4 weak core is checked in
`Research/Quitting/FinFourProducerAtlas/SemanticConnections.lean`:

* `FinFourAtlasWeakConcentratedSingletonCore.targetProfile`, `.stage`,
  `.singleton`, and `.resolution` expose the literal row;
* `.singleton_card` identifies its owner; and
* `.resolution_le_stageMass`, together with
  `FinFourMinimumAtomProducer.minimumSingletonClockResolution_pos`, supplies
  the quantitative hypotheses.

The minimum-law source compression is checked in
`Research/Quitting/FinFourProducerAtlas/MinimumSingletonClockCompression.lean`:

* `FinFourMinimumAtomProducer.exists_commonChronology_cofinal_ownerCompressedSingleton`;
* `FinFourOwnerCompressedSingletonEndpoint.targetProfile`; and
* `FinFourOwnerCompressedSingletonEndpoint.target_stageMass_gt`.

What is new is the exact local composition: any positive row `A` can be
best-endpoint-purified in a coordinate `o` unless `A={o}`, producing zero
marked defect and no-loss mass on the same literal tail; constant repetition
then fills the strong packet. Current packet constructors did not expose this
generic row adapter.

## Proof

### 1. Literal one-row transport

Let

\[
 \rho=\operatorname{LiteralOneDateProfile}(r,\tau,o,t,a).
\]

By definition, this behavioral strategy follows `tau` before `t`, plays `a`
surely at `t`, and resumes `tau` strictly afterwards. Hence all earlier roots,
all later roots, and the entire post-row tail are literal copies. Since the
profiles agree strictly before `t`, their live masses at `t` are equal.

### 2. No-loss two-mode routing

At the source event, exactly the members of `A` Quit at `t`. The root update
removes `o`'s old prescribed-action factor. If `a=C`, the event routes to
`A\setminus\{o\}`. If `a=Q`, it routes to `A\cup\{o\}`. Formally,
`quittingRootCoalitionMass_le_pureEndpointRouted` gives

\[
 \operatorname{RootMass}_x(A)
 \le
 \operatorname{RootMass}_{x[o\leftarrow a]}(R). \tag{8}
\]

Multiplying by the common nonnegative live mass gives (5). No survival
probability is divided out, so zero-probability boundary factors cause no
gap.

### 3. Exact zero local defect

The Quit and Continue endpoint payoffs for `o` depend on its opponents' root
and on the tail payoff, but not on `o`'s own mixing probability. Both are
therefore unchanged when `x_o` is replaced by the pure action `a`.

By definition, `a` attains their maximum. Under the updated pure marginal,
the prescribed successor payoff is exactly the payoff of `a`, hence exactly
that maximum. Since coordinate Nash defect is

\[
 \max\{Q_o,C_o\}-\text{prescribed successor payoff},
\]

it equals zero. This proves (6). Equivalently, unfold
`quittingRootBestEndpointAction`,
`quittingRootCoordinateNashDefect`, and the endpoint-mixture identity, then
split on `Q_o<=C_o`.

### 4. Constant repetition gives the packet

Fix `0<lambda<=m`. Define for every rank

\[
 \texttt{profiles(rank)}=\rho,\qquad
 \texttt{mark(rank)}=t,\qquad
 \texttt{cutoff(rank)}=t+1,
\]

take `scale(rank)=1/(rank+1)`, and use the identity subsequence.

* `resolution_pos` is `0<lambda`.
* `subseq_strictMono` holds for the identity.
* `mark_lt` is `t<t+1`.
* `stageMass` follows from `lambda<=m` and (5).
* Positive stage mass invokes
  `positive_stageCoalitionMass_has_semanticPrefixIncidence`, yielding current
  and tail carrier membership, the exact prefix identity for `rho`, and
  positive marked root mass.
* By (6), the numerator in `defect_tendsto` is identically zero. Division by
  the positive scale is zero, so the required limit is immediate.

These are all fields of `QuittingReprojectionConcentratedPacket`.

### 5. Fin4 weak-core and minimum-law adapters

Given a `FinFourAtlasWeakConcentratedSingletonCore`, use `singleton_card` to
write its terminal as `{j}`, choose any `o!=j`, and apply the theorem to its
`targetProfile` and `stage`, with `lambda=core.resolution`. The core's
resolution is positive and at most its stage mass. Retain the core externally
as the source provenance of the produced packet.

For a minimum-law singleton source with limiting mass `mu`, first use
`exists_commonChronology_cofinal_ownerCompressedSingleton` at any
`0<lambda<mu` to obtain one actual endpoint beyond any requested source depth.
Its marked singleton stage mass is greater than `lambda`; applying the local
theorem produces the strong packet at that resolution. One may repeat a single
endpoint, or retain a cofinal endpoint sequence and apply the same local
operation rankwise.

## Boundary tests

### All membership configurations are covered and the constant is sharp

If `o` is outside `A`, Continue retains `A` and Quit inserts `o`. If `o` is
inside `A`, Continue erases `o` and Quit retains `A`. Thus (4) covers all four
cases of the checked routing theorem.

For the singleton application, let `j` Quit surely at `t` and let every other
player Continue there. If the
two endpoint values for `o` tie, the checked selector chooses Continue, the
target terminal is `{j}`, and its mass is unchanged. If Quit is strictly
better for `o`, the target terminal is `{j,o}`, again with unchanged mass.
For example, zero rewards give the tie case; changing only `o`'s payoff on
`{j,o}` to one gives the strict-Quit case. Thus both modes are real and (5)
can be equality, so resolution `m` is sharp.

### The pair mode cannot be deleted

When Quit is the unique better endpoint, exact zero local defect at a pure
updated row forces `o` to Quit. The singleton must then route to `{j,o}`.
Thus the theorem cannot promise that the strong packet's terminal is always a
singleton.

### The singleton specialization needs a distinct player

For `A={j}`, the generic condition is `o!=j`. Hence the singleton corollary
needs at least two players and has no one-player analogue. Fin4 satisfies this
automatically.

### The excluded coalition is the exact boundary

If `A={o}` and Continue is the selected endpoint, routing erases `o` and
produces the empty coalition, which is not a terminal atom. Thus the generic
condition `A!={o}` cannot be removed. For a singleton `A={j}`, it reduces
exactly to choosing `o!=j`.

### Limiting minimum-law mass is not a finite-row floor

The minimum chronology supplies convergence of its singleton tail mass to
`mu`, not a one-sided lower bound by `mu`. Actual singleton masses may converge
to `mu` strictly from below. Therefore a source-facing uniform resolution
equal to `mu` is not forced; every fixed `lambda<mu` is. This does not affect
the generic theorem, which uses the exact mass of its supplied literal row.

### Other coordinates need not remain controlled

Best-endpoint purification makes only `o`'s marked local defect zero. It can
change other players' prescribed payoffs, caps, and debts. Thus no minimum-
fiber or no-new-support conclusion follows from this theorem alone.

### The packet interface is universally inhabitable

Take any nonempty coalition `A` in a game with at least two players and play
it purely at date zero. Its stage mass is one. Choosing `o` with `A!={o}` and
applying the theorem produces a concentrated packet, independently of every
reward sign. Hence packet existence alone is not a rank, hard-residual
condition, or counterexample contraction. This boundary example is also why
the atlas origin must remain externally attached in any later consumer.

## Adapter and consumer

The generic actual-data adapter is exactly one behavioral profile, one date,
one positive nonempty stage atom `A`, and a player `o` with `A!={o}`. The
conjecture-facing singleton specialization is supplied by the checked
`FinFourAtlasWeakConcentratedSingletonCore` for both of its origins, covering
all three singleton atlas leaves. The minimum-law wrapper
retains the original source, chronology, and selected endpoint; no reward
table, law, or semantic minimum is reselected.

The produced object is the already defined
`QuittingReprojectionConcentratedPacket`, not a new packet type.  Existing
downstream dispatches use this type in:

* `Research/Quitting/ConcentratedSingleton/Consumer.lean`;
* `Research/Quitting/ConcentratedSingleton/StrategicDispatch.lean`;
* `Research/Quitting/ConcentratedSingleton/Cancellation.lean`; and
* `Research/Quitting/ConcentratedCollisionFourRoleMonodromy.lean`.

The checked source-attached consumer now compresses the strategic arm to an
atomic-toggle handoff or exact player deletion and retains the collision arm
verbatim.  Thus it contracts the weak/diffuse singleton entrance, but does not
complete the strong concentrated node.

## Lean handoff

First add the elementary local identity:

```lean
theorem quittingRootCoordinateNashDefect_update_bestEndpoint_eq_zero
    (tail : Payoff iota) (root : iota -> PMF Bool) (who : iota) :
    quittingRootCoordinateNashDefect reward tail
      (Function.update root who
        (PMF.pure
          (quittingRootBestEndpointAction reward tail root who))) who = 0
```

Its proof unfolds the endpoint selector and defect, uses the endpoint-mixture
formula, and splits on the comparison of Quit and Continue values.

Then prove a generic dependent adapter, schematically:

```lean
theorem nonempty_concentratedPacket_of_stageMass_pos
    (tau : (quittingGame reward).BehaviorProfile)
    (terminal : QuittingTerminal iota) (o : iota)
    (hne : terminal.val != {o}) (stage : Nat)
    (lambda : Real) (hlambda : 0 < lambda)
    (hmass : lambda <= quittingStageCoalitionMass reward tau stage
      terminal) :
    exists profiles cutoff scale routedTerminal,
      Nonempty (QuittingReprojectionConcentratedPacket
        reward profiles o routedTerminal cutoff scale)
```

The implementation should retain the source profile, selected action, target
profile, routed terminal, and literal before/after root equalities in a small
adapter structure if later provenance needs them.

Use:

* `quittingLiteralOneDateOverride` and `quittingLiteralOneDateProfile`;
* `quittingProfileLiveRoot_literalOneDateProfile`;
* `quittingLiveMass_literalOneDateProfile_eq`;
* `quittingProfileLiveRoot_literalOneDateProfile_tail_eq`;
* `quittingRootCoalitionMass_le_pureEndpointRouted`;
* `quittingPureEndpointRoutedCoalition_four_way`; and
* `positive_stageCoalitionMass_has_semanticPrefixIncidence`.

Finally add wrappers from `FinFourAtlasWeakConcentratedSingletonCore` and from
`FinFourMinimumAtomProducer` with singleton terminal.

## Scope and nonclaims

The theorem proves exact local marked-row complementarity, not exact Nash of
the entire root for all players and not small full behavioral debt. It proves
no target-side near-minimality, no preservation of inactive debt support, no
cap--Nash stack for the changed source, no punishment-floor path, no fixed-law
return, no support-rank descent, no terminal approximation, and no uniform-
equilibrium payoff.

Although the one-row update preserves the entire post-row tail literally, the
old source cap--Nash stack is still certified only over its original suffix;
the marked update can change continuation caps seen by earlier roots.

The checked downstream theorem contracts the source-attached packet to a
strategic handoff or the unchanged collision-minimum residual.  It does not
close the latter arm, exclude the Fin4 hard residual, or prove a uniform-
equilibrium payoff.

## Formalization record

The maintained realization is Research-only and is reachable through
`Research/Quitting/FinFourExhaustiveProducerAtlas.lean`.

1. `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPlateauLocalizedOtherDefect.lean`
   proves
   `quittingRootCoordinateNashDefect_update_bestEndpoint_eq_zero`.  For the
   selected best endpoint, updating exactly that marginal makes the owner's
   coordinate Nash defect zero; the proof uses that the two endpoint values
   depend only on the opponents' marginals.
2. `Research/Quitting/PositiveStageAtomConcentratedPacket.lean` defines
   `QuittingStageAtomConcentratedPacketAdapter`.  Its accessors retain the
   actual source root and shifted tail, literal one-date target, routed
   terminal, exact opponent and off-date profiles, post-date live roots,
   semantic tail, owner cap, and selected-date live mass.  The declarations
   `sourceStageMass_le_targetStageMass`,
   `resolution_le_targetStageMass`, and `ownerMarkedDefect_eq_zero` expose the
   no-loss source atom and exact marked complementarity.

   `normalizedMarkedOwnerDefect_eq_zero` and
   `normalizedMarkedOwnerDefect_identically_zero` give the literal normalized
   identity for every scale, including before any positivity hypothesis;
   `normalizedMarkedOwnerDefect_tendsto_zero` gives its limit.  The constructor
   `packetWithScale` accepts any `scale : Nat -> Real` which is pointwise
   positive and tends to zero, and returns an actual
   `QuittingReprojectionConcentratedPacket`.  The canonical `packet` is the
   thin specialization to `1 / (rank + 1)`.  Finally,
   `QuittingStageAtomConcentratedPacketAdapter.nonempty_of_stageMass` constructs
   the adapter from the actual profile, nonempty source terminal, selected
   owner and date, positive resolution, and source stage-mass bound; no packet
   is supplied.
3. `Research/Quitting/FinFourProducerAtlas/StrongConcentratedPacket.lean`
   defines `FinFourSingletonStageStrongConcentratedPacket`,
   `FinFourAtlasWeakStrongConcentratedPacket`, and
   `FinFourOwnerCompressedStrongConcentratedPacket`.
   `FinFourSingletonStageStrongConcentratedPacket.nonempty_of_singleton_stageMass`
   chooses a distinct packet owner from an actual positive singleton row.
   `routedTerminal_mode_and_card` states the exact alternatives: Continue
   retains the original singleton, while Quit produces the two-player set.
   `FinFourAtlasWeakConcentratedSingletonCore.nonempty_strongConcentratedPacket`
   keeps the weak core's exact `mu^2 / 8` resolution.  The theorem
   `FinFourOwnerCompressedSingletonProducer.nonempty_strongConcentratedPacket`
   uses the producer's one already selected chronology and, for every
   `0 < lambda < mu` and every depth, returns a packet at exactly `lambda`.
4. `Research/Quitting/FinFourProducerAtlas/StrongConcentratedPacketConsumer.lean`
   defines `FinFourStrongConcentratedPacketConsumerResult` and proves
   `FinFourSingletonStageStrongConcentratedPacket.consumerResult`.  On the
   same retained minimum and literal packet, it returns either the full
   concentrated strategic dispatch together with a static atomic-toggle or
   exact-deletion handoff, or the unchanged
   `QuittingConcentratedCollisionMinimumResidual`.  The declarations
   `FinFourAtlasWeakConcentratedSingletonCore.nonempty_strongConcentratedPacketConsumption`
   and
   `FinFourOwnerCompressedSingletonProducer.nonempty_strongConcentratedPacketConsumption`
   attach this exact contraction respectively to the canonical weak core and
   to every admissible resolution and depth on the fixed chronology.

Evidence seals:

- **M:** PASS.  The endpoint identity, no-loss routing, exact two-mode Fin4
  calculation, arbitrary-scale zero normalization, fixed-chronology
  composition, and consumer implication have been mathematically audited.
- **L:** PASS.  The foundational, generic-adapter, Fin4 packet, consumer, and
  reader-atlas modules check in Lean.  At promotion, the reader `Research`
  umbrella, trust scan, proof-duplicate check, derivable-telescope check,
  documentation check, source-format checks, and targeted axiom prints pass.
  The audited declarations use only `propext`, `Classical.choice`, and
  `Quot.sound`.
- **A:** PASS.  The generic constructor starts from one actual profile and
  positive stage atom.  The Fin4 wrappers start from an actual weak atlas core
  or the retained minimum-singleton producer and construct their packet,
  owner, endpoint, and routed terminal rather than accepting them as supplied
  certificates.
- **C:** PASS for the exact source-attached strategic-versus-collision
  contraction in `StrongConcentratedPacketConsumer.lean`.  It is not a seal
  for the arbitrary supplied-scale constructor separately, nor for closing
  the collision residual, the full atlas, or the uniform-equilibrium
  conjecture.

The generic API uniformly assumes `A != {o}` so that the routed terminal is
nonempty independently of which endpoint is selected.  This assumption is
not logically needed in the Quit subcase, where insertion is automatically
nonempty.  No routed-terminal singleton is asserted unconditionally.

The changed target is not asserted full-root Nash, near-minimal, or equal to a
minimum semantic point.  Only the selected owner's marked coordinate defect
is zero; other players' local defects, payoffs, caps, and debts may change.
The source cap stack is not transported across the marked update.  The
minimum-law point remains an asymptotic semantic limit, not a profile hidden
as realizing that point.  No source chronology is reselected under the
resolution or depth quantifiers.

No target punishment floor, recurrence, return, regeneration, source-rank
descent, backward compiler, terminal approximation, collision closure,
atlas-completion closure, or downstream uniform-payoff theorem is proved.
The original mathematical provenance and independent review links at the
head of this packet are retained.
