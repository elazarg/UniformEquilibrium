# Review of universal self-tail closure

Reviewer: `ATLAS_GATEKEEPER`

## Verdict

**Mathematical core: valid, and strictly stronger than the original
two-anchor formulation. Export recommendation: yes, after stating the
stronger source-level contraction and keeping one packaging qualification
explicit.**

The literal self-tail splice is sound. More importantly, neither two quiet
anchors nor a `TailEscapeSubsequence` is needed for the conjecture-facing
application. The checked same-stage dispatch asks only for:

1. an actual profile with a positive nonsingleton atom at one displayed date;
2. a positive global minimum semantic point; and
3. small total debt of the literal continuation after that date.

It does **not** ask that the whole displayed profile be near-minimal, nor that
the copied pre-row roots remain cap--Nash after changing the continuation.
Every `SelectedRows` family supplies, eventually, a fixed positive displayed
atom and a near-minimum prefixed source. Copying the prefixed source through
the displayed row and restarting that same source after all Continue therefore
supplies the exact raw input to the dispatch.

Consequently the strongest honest statement is

\[
\boxed{
\text{nonsingleton Fin4 minimum-law causal atom}
\Longrightarrow
\text{source-attached same-stage singleton endpoint}
\Longrightarrow
\text{strong concentrated-singleton packet}.}
\]

This removes the high-tail/low-tail split itself from the maintained Fin4
atlas. It does not consume the resulting concentrated-singleton obligation.

## Exact declarations inspected

The source audit used the following declarations.

In
`Research/Quitting/NonsingletonMinimumLawLinearTransfer.lean`:

* `QuittingNonsingletonMinimumLawTransfer.prefixedProfile`;
* `shiftedStage` and `selectedStageMass`;
* `SelectedRows`;
* `QuittingMinimumLawCausalSuffixAtom.nonempty_selectedRows`;
* `SelectedRows.prefix_debt_tendsto`;
* `SelectedRows.eventually_stageMass_gt_square_div_eight`; and
* `TailEscapeSubsequence`.

In `Research/Quitting/FinFourProducerAtlas/Source.lean`:

* `FinFourMinimumAtomProducer`;
* `FinFourMinimumAtomProducer.minimumDebt_pos`;
* `FinFourLowTailRow`; and
* `FinFourMinimumAtomProducer.nonempty_tailEscape_or_lowTailRow`.

In `Research/Quitting/FinFourSameStageEndpointMonodromy.lean`:

* `quittingPartialPurification_then_finFourSameStage_dispatch`.

In `Research/Quitting/FinFourProducerAtlas/Leaves.lean`:

* `FinFourLowTailRow.nonempty_leaf`;
* `FinFourPurifiedSingletonProducer`;
* `FinFourTerminalSingletonProducer`; and
* `FinFourMonodromyProducer`.

In `Research/Quitting/FinFourProducerAtlas/MonodromyImpossible.lean`:

* `quittingSameStageSingletonRoute_of_card_eq_two`;
* `not_nonempty_finFourSameStageEndpointClosedSegment`; and
* the source-level corollaries excluding `FinFourMonodromyProducer`.

In the literal-prefix/tail infrastructure:

* `quittingLiteralRootStackProfile` in
  `UniformEquilibrium/Quitting/Root/LiteralExactPrefixStack.lean`;
* `quittingProfileLiveRoot_rootThenContinuation_zero` and
  `quittingProfileLiveRoot_rootThenContinuation_succ` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticResetIncidenceReturn.lean`;
* `shiftProfile_quittingRootThenContinuationProfile` in
  `UniformEquilibrium/ProofView/Concepts/Stochastic/Models/Quitting/RootContinuation.lean`;
* `quittingStageCoalitionMass_rootSequence_eq_of_prefix` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticElementaryTailCompression.lean`;
* `quittingTerminalSemanticPair_eq_of_liveRoot_eq` in
  `Research/Quitting/SameStageEndpointMonodromy.lean`; and
* `quittingSpineDebtExcess` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPlateauDefectTelescope.lean`.

For the downstream packet:

* `QuittingStageAtomConcentratedPacketAdapter` and its positive-stage-atom
  construction in
  `Research/Quitting/PositiveStageAtomConcentratedPacket.lean`;
* `FinFourSingletonStageStrongConcentratedPacket` and
  `FinFourAtlasWeakStrongConcentratedPacket` in
  `Research/Quitting/FinFourProducerAtlas/StrongConcentratedPacket.lean`; and
* `FinFourStrongConcentratedPacketConsumerResult` in
  `Research/Quitting/FinFourProducerAtlas/StrongConcentratedPacketConsumer.lean`.

No declaration inspected already states the self-tail closure or the resulting
source-level contraction. The existing atlas instead separates
`TailEscapeSubsequence` from `FinFourLowTailRow` according to the debt of the
*original* post-row continuation.

## Verification of the self-tail splice

Let `sigma` be an actual behavioral profile and `t : Nat`. Let

\[
P_t(\sigma)=[x_0,\ldots,x_t],\qquad
x_s=\operatorname{root}_\sigma(s),
\]

and define

\[
\operatorname{Close}_t(\sigma)=P_t(\sigma)\triangleright\sigma.
\]

This is an actual behavioral profile. Induction through the literal root-stack
constructor proves:

\[
\operatorname{root}_{\operatorname{Close}_t(\sigma)}(s)
=\operatorname{root}_\sigma(s)\quad(s\le t),
\tag{1}
\]

and

\[
\operatorname{tail}_{t+1}\operatorname{Close}_t(\sigma)=\sigma.
\tag{2}
\]

Equation (1) fixes the unconditional live mass through `t` and the conditional
coalition law at `t`. Hence, for every nonempty coalition `A`,

\[
\Pr_{\operatorname{Close}_t(\sigma)}(A\text{ at }t)
=\Pr_\sigma(A\text{ at }t).
\tag{3}
\]

Equation (2) is a full behavioral-profile equality, not only semantic
equivalence. Therefore

\[
\operatorname{SpineDebtExcess}
 (\operatorname{Close}_t(\sigma),D_*,t+1)
=D(\sigma)-D_*.
\tag{4}
\]

There is no observation or strategy-class issue: the construction changes a
prescribed continuation after one public all-Continue history. It does not
compare deviations or claim that old best responses remain fixed.

## Stronger source-level application

Let

```text
source : FinFourMinimumAtomProducer reward bound
```

and suppose

```text
1 < source.atom.terminal.val.card.
```

Select

```text
rows : SelectedRows reward source.point source.atom
```

using
`QuittingMinimumLawCausalSuffixAtom.nonempty_selectedRows`. Put

\[
\lambda=
\frac{\mu^2}{8},\qquad
\mu=source.point.2(\operatorname{some}(source.atom.terminal)).
\]

The atom mass is positive, so `lambda>0`. The selected-row theorems give

\[
\Pr_{\sigma_n}(S\text{ at }t_n)>\lambda
\quad\text{eventually},
\tag{5}
\]

where `sigma_n` is the literal prefixed profile and `t_n` its shifted mark,
and

\[
D(\sigma_n)\longrightarrow
\operatorname{quittingTerminalDebtSumInf}(r)=D_*.
\tag{6}
\]

Choose one index where (5) holds and

\[
D(\sigma_n)-D_*<\lambda D_*/2.
\tag{7}
\]

Global minimality makes the left side nonnegative, but only the strict upper
bound is needed by the dispatch. Define

\[
\widehat\sigma_n=\operatorname{Close}_{t_n}(\sigma_n).
\]

Equations (3)--(4) give literally

\[
\lambda\le
\Pr_{\widehat\sigma_n}(S\text{ at }t_n)
\]

and

\[
\operatorname{SpineDebtExcess}
(\widehat\sigma_n,D_*,t_n+1)<\lambda D_*/2.
\]

These are precisely the chronological hypotheses of
`quittingPartialPurification_then_finFourSameStage_dispatch`. The theorem's
signature contains no bound on `D(widehatSigma_n)` and no cap--Nash condition
on the copied word. Thus the call is valid even if changing the continuation
changes every old cap.

The raw output is a bounded literal same-stage purification ending either in
a singleton route or a closed endpoint segment. The latter is impossible by
`not_nonempty_finFourSameStageEndpointClosedSegment`. The surviving singleton
has positive stage mass on an actual one-date sibling and preserves the
literal post-date continuation. The positive-stage-atom adapter then produces
a strong concentrated packet without mass loss.

This proof uses only `SelectedRows`, so restricting its statement to a
`TailEscapeSubsequence` is unnecessarily weak. In particular, the old
high-tail versus low-tail dichotomy is not needed downstream.

## Review of the original two-anchor estimates

The two-anchor theorem in the note is also correct, but is secondary.
Suppose distinct players `a,b` have Continue probabilities at the marked root
bounded by `eta`. Prescribed play reaches the changed continuation only if
both Continue. Under a unilateral deviation by `a`, prescribed player `b`
still gates the changed continuation; symmetrically for `b`; under any other
deviation either anchor gates it. Coupling the same arbitrary behavioral
deviation in the original and repaired profiles therefore gives

\[
|U_i(\widehat\sigma[i\leftarrow\tau_i])
-U_i(\sigma[i\leftarrow\tau_i])|\le2M\eta.
\]

Taking suprema in both directions proves the same bound for each unrestricted
behavioral cap. Hence the displayed `16 M eta` total-debt bound on `Fin 4` is
safe.

A sharper optional account is

\[
|D(\widehat\sigma)-D(\sigma)|
\le2M(c_a+c_b+6c_ac_b),
\]

because prescribed payoff changes are gated by `c_a c_b`, the cap change for
`a` by `c_b`, that for `b` by `c_a`, and those for each of the other two
players by `c_a c_b`. The coarse bound is preferable if the exact constant is
not consumed.

With two sure Quitters the semantic and complete terminal-law identities are
exact even under every unilateral behavioral deviation. With only one sure
Quitter the deviator may remove that gate, and the note's counterexample
correctly shows that whole-profile cap stability can fail. These are sharp
boundary tests for the *optional near-minimum whole-profile* conclusion, not
for the universal dispatch.

## Packaging seam and required repair

The mathematical reduction should not be stated as if the repaired row were
already a `FinFourLowTailRow source`. That structure stores a rank in the
original `SelectedRows` family and its original post-row tail. The self-tail
closure is a new actual profile, and the copied roots need not remain exact
cap--Nash roots after the splice.

Likewise, the existing source-attached endpoint types in
`FinFourProducerAtlas/SemanticConnections.lean` are indexed by the old
`FinFourLowTailRow`. A formal proof should not manufacture that field by
semantic equivalence.

The narrow repair is to introduce an actual-row passport containing only the
fields used by the dispatch:

```text
structure FinFourActualLowTailRow (source) where
  profile : BehaviorProfile
  stage : Nat
  lambda : Real
  coalition : QuittingNonsingletonCoalition (Fin 4)
  lambda_pos : 0 < lambda
  lambda_le_stageMass : lambda <= stageMass profile stage coalition
  lowTail : spineDebtExcess profile D_* (stage + 1) < lambda * D_* / 2
```

It should additionally retain the `SelectedRows`, selected rank, and literal
self-tail equality in the source-attached adapter, rather than in the raw
passport. Generalize the purification/singleton endpoint wrappers to this raw
passport or add parallel wrappers. The already checked monodromy no-go is
generic in the raw dispatched trace and needs no source repackaging.

The strong packet must remain indexed by this new endpoint origin if the
result is described as **source-attached**. Mere existence of the generic
`QuittingReprojectionConcentratedPacket` would be vacuous as a table-level
restriction, as the strong-packet export itself warns.

## Exportable statement

The export should not be titled as a two-anchor result. Its minimal
self-contained conjecture-facing claim is:

> **Universal self-tail contraction of a nonsingleton Fin4 minimum-law
> source.** Given a `FinFourMinimumAtomProducer` whose selected causal atom is
> nonsingleton, there exist one selected actual prefixed source `sigma`, its
> marked date `t`, and an actual self-tail-closed profile `widehatSigma` such
> that (i) the marked nonsingleton mass is at least `mu^2/8`, (ii) the literal
> continuation of `widehatSigma` after that row is exactly `sigma`, (iii)
> `D(sigma)-D_* < (mu^2/8) D_*/2`, and (iv) bounded same-stage purification
> yields an actual singleton endpoint of at least the same stage mass with
> the same literal continuation. Consequently the source produces a
> source-attached strong concentrated-singleton packet.

This is a strict named narrowing of
`questions/FIN4_ATLAS_QUANTITATIVE_TAIL_ESCAPE.md` and of the nonsingleton arm
in `questions/FIN4_EXHAUSTIVE_PRODUCER_ATLAS.md`: quantitative tail escape is
not a separate downstream leaf. It is also stronger than the requested
tail-escape-only implication because it bypasses that classification.

## Scope and nonclaims

The export must state that it does not:

* preserve cap--Nash exactness of the copied pre-row roots;
* prove that the repaired whole profile or singleton target is near-minimal;
* preserve the original escaped post-row tail;
* turn suffix-law mass into current root absorption;
* consume the strong concentrated packet;
* produce terminal approximants, a cumulative near-return, semantic debt
  descent, or a uniform-equilibrium payoff; or
* answer the original tail-escape question by one of its terminal semantic
  consumers. It strictly removes that leaf by a source-preserving reduction
  to the separately maintained concentrated-singleton node.

## Lean handoff

The clean implementation order is:

1. define `quittingSelfTailClosure` generically via a list of the first
   `stage+1` live roots;
2. prove exact live-root equality through `stage`, exact stage-mass equality,
   and exact spine equality at `stage+1`;
3. add `FinFourActualLowTailRow` and adapters from both the old
   `FinFourLowTailRow` and a selected self-tail closure;
4. generalize the leaf constructors to the raw passport while retaining an
   origin field for the source-selected closure;
5. apply `not_nonempty_finFourSameStageEndpointClosedSegment`; and
6. compose the surviving singleton endpoint with the existing positive-stage
   strong-packet construction, retaining the new origin in the dependent
   packet.

Do not encode old cap-stack exactness as a field of the repaired row. It is
false in general and unused.

