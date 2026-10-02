# Universal self-tail closure of the Fin4 quantitative tail-escape leaf

Author: `ATLAS_FALSIFIER`

## Status

**Proof draft; not Lean-checked.** The original two-anchor argument in this
file was unnecessarily weak. The exact same-stage dispatch does not require
the repaired whole profile to be near the minimum fiber. It requires only a
fixed minimum point, a positive nonsingleton atom at the displayed date, and
a low-debt literal continuation after that date.

Every actual marked row admits such a continuation: retain its finite literal
past through the row and, after all Continue at that row, restart the same
actual near-minimum source profile from date zero. This closes the entire
`TailEscapeSubsequence` leaf back into the low-tail same-stage dispatch. No
sure quitter, cap-root exactness after the splice, or behavioral stability
estimate is needed.

The result is a source-preserving atlas contraction, not by itself a uniform-
equilibrium theorem. In full generality the repaired **tail** is near the
minimum fiber, while the repaired whole profile need not be. Composed with
the independently reviewed impossibility of `FinFourMonodromyProducer` and
the positive-stage-atom strong-packet adapter, it sends the quantitative
tail-escape leaf to the maintained strong concentrated-singleton node with
this explicit tail provenance. A two-anchor subfamily additionally retains a
cofinal near-minimum sequence of whole repaired source profiles.

## 1. A generic literal self-tail closure

Fix any finite quitting game, an actual behavioral profile `sigma`, and a
date `t`. Let

\[
 x_s:=\operatorname{root}_\sigma(s),\qquad 0\le s\le t,
\]

be the exact live roots of `sigma`. Form the finite root word

\[
 P_t(\sigma)=[x_0,x_1,\ldots,x_t]
\]

and the actual behavioral profile

\[
 \operatorname{Close}_t(\sigma)
 :=P_t(\sigma)\triangleright\sigma.
\tag{1}
\]

In repository notation this is

```text
quittingLiteralRootStackProfile reward prefixRoots sigma
```

where `prefixRoots` is the list of the first `t+1` values of
`quittingProfileLiveRoot reward sigma`.

This is not a carrier representative and does not select a new source. It is
one executable behavioral profile whose declared continuation after the
finite word is literally the supplied actual profile `sigma`.

### Exact past and atom preservation

Induction over the finite word, using

```text
quittingProfileLiveRoot_rootThenContinuation_zero
quittingProfileLiveRoot_rootThenContinuation_succ
```

gives

\[
 \operatorname{root}_{\operatorname{Close}_t(\sigma)}(s)
 =\operatorname{root}_\sigma(s)
 \qquad(0\le s\le t).
\tag{2}
\]

The unconditional stage mass at `t` depends only on the roots through `t`:
the earlier roots determine live mass, and the displayed root determines the
conditional coalition mass. Therefore, for every nonempty coalition `A`,

\[
 \Pr_{\operatorname{Close}_t(\sigma)}(A\text{ at }t)
 =\Pr_\sigma(A\text{ at }t).
\tag{3}
\]

This can be proved directly from
`quittingStageCoalitionMass_eq_liveMass_mul_rootCoalitionMass`,
`quittingLiveMass_eq_jointSurvivalWeight_profileLiveRoot`, and
`quittingJointSurvivalWeight_congr`. Equivalently, it is the arbitrary-
profile version of
`quittingStageCoalitionMass_rootSequence_eq_of_prefix`.

### Exact continuation equality

The root/continuation constructor satisfies

```text
shiftProfile_quittingRootThenContinuationProfile
```

for every realized root action. Iterating it through the `t+1` copied roots
gives the literal full-profile identity

\[
 \operatorname{tail}_{t+1}\operatorname{Close}_t(\sigma)=\sigma.
\tag{4}
\]

In particular, the stronger live-root identity holds at every offset,

\[
 \operatorname{root}_{\operatorname{tail}_{t+1}
        \operatorname{Close}_t(\sigma)}(s)
 =\operatorname{root}_\sigma(s),
\tag{5}
\]

and hence so does the exact semantic identity

\[
 \operatorname{Sem}
   (\operatorname{tail}_{t+1}\operatorname{Close}_t(\sigma))
 =\operatorname{Sem}(\sigma).
\tag{6}
\]

The semantic conclusion also follows from
`quittingTerminalSemanticPair_eq_of_liveRoot_eq`. Thus, for every reference
number `Dref`,

\[
 \operatorname{SpineDebtExcess}
   (\operatorname{Close}_t(\sigma),Dref,t+1)
 =D(\sigma)-Dref.
\tag{7}
\]

## 2. Application to every quantitative tail-escape row

Let

```text
E : TailEscapeSubsequence reward source.point source.atom
```

be the tail-escape leaf of a fixed
`FinFourMinimumAtomProducer reward bound`. At subsequence index `n`, write

\[
 k_n:=E.subseq(n),
\]

\[
 \sigma_n:=\operatorname{prefixedProfile}
    (E.rows.profiles)(E.rows.roots)(k_n),
\]

and

\[
 t_n:=\operatorname{shiftedStage}
    (E.rows.roots)(E.rows.mark)(k_n).
\]

Put

\[
 D_*:=D(source.point.1),\qquad
 \lambda:=\frac{\mu^2}{8}>0,
 \quad
 \mu:=source.point.2(\operatorname{some}(source.atom.terminal)).
\]

The retained fields give, for every `n`,

\[
 \Pr_{\sigma_n}
   (source.atom.terminal\text{ at }t_n)>\lambda.
\tag{8}
\]

They also give

\[
 D(\sigma_n)\longrightarrow D_*.
\tag{9}
\]

Indeed `E.rows.prefix_debt_tendsto`, composed with the strict cofinal map
`E.subseq`, converges to `quittingTerminalDebtSumInf reward`, and
`source.debt_eq_inf` identifies that number with `D_*`.

Define the self-tail-closed actual row

\[
 \widehat\sigma_n:=\operatorname{Close}_{t_n}(\sigma_n).
\tag{10}
\]

Equations (3), (7), (8), and (9) give

\[
 \lambda<
 \Pr_{\widehat\sigma_n}
   (source.atom.terminal\text{ at }t_n),
\tag{11}
\]

and

\[
 \operatorname{SpineDebtExcess}
   (\widehat\sigma_n,D_*,t_n+1)
 =D(\sigma_n)-D_*
 \longrightarrow0.
\tag{12}
\]

Since `lambda*D_*/2>0`, choose one sufficiently large `n` so that

\[
 \operatorname{SpineDebtExcess}
   (\widehat\sigma_n,D_*,t_n+1)
 <\lambda D_*/2.
\tag{13}
\]

Now invoke, literally,

```text
quittingPartialPurification_then_finFourSameStage_dispatch
```

with

```text
minimum      := source.point.1
baseProfile  := widehatSigma_n
stage        := t_n
lambda       := mu^2 / 8
coalition    := <source.atom.terminal, E.rows.collision>
```

and the existing fields

```text
source.semantic_mem
source.minimum
source.minimumDebt_pos
```

together with (11) and (13).

This invocation is exact. Inspection of the declaration in
`Research/Quitting/FinFourSameStageEndpointMonodromy.lean` shows that it asks
for no upper bound on `D(baseProfile)`, no `SelectedRows` object, and no
cap-Nash certificate for the copied word. Its only chronological inputs are
the actual profile, date, nonsingleton stage mass, and low debt of that
profile's literal post-date spine.

### Stronger adapter: bypass the high-tail/low-tail split entirely

Nothing in the construction uses `E.tail_excess_floor`. In fact it does not
need a `TailEscapeSubsequence` at all.

Start from a `FinFourMinimumAtomProducer source` whose selected minimum-law
atom is nonsingleton. The checked theorem

```text
QuittingMinimumLawCausalSuffixAtom.nonempty_selectedRows
```

produces one `SelectedRows` family. Two statements are eventually true along
that same family:

```text
rows.eventually_stageMass_gt_square_div_eight source.point_mem
rows.prefix_debt_tendsto
```

After identifying the debt infimum with `D_*`, choose one common sufficiently
late rank at which the stage mass exceeds `lambda` and the actual prefixed
source debt is within `lambda*D_*/2` of `D_*`. Self-tail-close that row. Its
marked mass is unchanged and its post-date tail is exactly the chosen
near-minimum prefixed source, so the raw same-stage dispatch applies.

Therefore the maintained classification theorem

```text
source.nonempty_tailEscape_or_lowTailRow
```

is not needed downstream. Self-tail closure converts **every** sufficiently
late selected row into an actual low-tail row, irrespective of the debt of
its original post-mark continuation. The high-tail branch measures a property
of the originally selected tail, but the same-stage consumer permits an
actual source-matched replacement tail and does not require the whole new
row to preserve source semantics.

Combining with the singleton minimum-law owner-clock compression, the maximal
Fin4 statement is:

\[
 \boxed{
 \text{Fin4 hard residual}
 \Longrightarrow
 \text{one source-attached concentrated-singleton endpoint/packet}.}
\tag{14}
\]

Here “source-attached” means that the fixed hard residual, minimum semantic/
law point, causal atom, selected actual source, copied marked past, and exact
post-date near-minimum tail are all retained. It does **not** mean that the
self-tail-closed whole profile or the routed singleton target is near the
minimum fiber.

## 3. What universal closure does and does not preserve

Replacing the continuation can drastically change the semantic pair of the
whole repaired profile when the marked root has only one sure quitter or no
sure quitter. Hence the old two-anchor coupling estimates were correct as a
statement about whole-profile semantic stability.

They are irrelevant here. The same-stage theorem never asks for that
stability. It performs its partial purification at the marked date and pays
for every update using the low-debt continuation after that date. The actual
past need only carry the fixed nonsingleton mass. Self-tail closure supplies
exactly those two facts on opposite sides of the same literal row.

Likewise, the copied roots need not remain exact cap-Nash roots after the tail
is changed. Cap-Nash exactness belonged to the original continuation and can
indeed be destroyed by the splice. No step above reuses it. Its only role was
upstream: producing the near-minimum actual source sequence `sigma_n` and its
positive marked atom.

The universal output is therefore:

* one actual row with the original literal marked past and atom;
* an exact post-date tail equal to the actual near-minimum profile `sigma_n`;
* the raw bounded same-stage purification/endpoint dispatch; and, after the
  monodromy no-go, a finite source-attached route to a singleton.

It is **not** a claim that the starting repaired row or the final singleton
target lies near the minimum fiber. The generic strong-packet construction
from the singleton is universal as a local theorem; the nontrivial atlas data
retained here are the fixed minimum point, the finite copied source row, and
the exact near-minimum continuation on its far side.

## 4. Stronger two-anchor output: cofinal near-minimum repaired sources

The original two-anchor estimate remains useful for one stronger conclusion.
Suppose, after passing to a subsequence, there are fixed distinct players
`a,b` whose Continue probabilities at the marked root satisfy

\[
 c_{a,n}\to0,\qquad c_{b,n}\to0,
 \qquad \eta_n:=\max(c_{a,n},c_{b,n})\to0.
\tag{15}
\]

Assume `|r_i(A)|<=M`. Compare `sigma_n` and its self-tail closure using their
common literal past through `t_n`. Under prescribed play, the changed
continuation can be reached only when both anchors Continue. Under an
arbitrary unilateral deviation by `i`, at least one anchor remains prescribed:

* if `i=a`, player `b` remains and exposes the new tail with probability at
  most `c_{b,n}`;
* if `i=b`, use `c_{a,n}`;
* otherwise either anchor gives the same upper bound.

Therefore, uniformly over every history-dependent behavioral deviation,

\[
 |U_i(\widehat\sigma_n[i\leftarrow\tau_i])
   -U_i(\sigma_n[i\leftarrow\tau_i])|
 \le 2M\eta_n.
\tag{16}
\]

Taking suprema in both directions gives

\[
 |B_i(\widehat\sigma_n)-B_i(\sigma_n)|\le2M\eta_n,
\tag{17}
\]

and hence on `Fin 4`

\[
 |D(\widehat\sigma_n)-D(\sigma_n)|\le16M\eta_n.
\tag{18}
\]

Thus

\[
 D(\widehat\sigma_n)\longrightarrow D_*.
\tag{19}
\]

Applying the same-stage dispatch at every sufficiently large index and using
the raw monodromy impossibility yields a **cofinal sequence of actual
near-minimum repaired sources**, each carrying the fixed nonsingleton mass
floor and a finite literal same-stage route to a singleton. The route's final
singleton target is not asserted to be near-minimum. This is the strongest
output currently justified by the two-anchor estimate.

With exactly two sure quitters at one row, the comparison errors in
(16)--(18) are zero: after any unilateral deviation at least one sure quitter
remains, so absorption at that row is certain and the replacement continuation
is never reached.

One sure quitter is insufficient for whole-profile stability. If that player
deviates to Continue, the replacement continuation can be exposed with fixed
probability. This boundary does not affect the universal raw dispatch because
that dispatch does not request whole-profile stability.

## 5. Composition with the maintained atlas

The raw conclusion of
`quittingPartialPurification_then_finFourSameStage_dispatch` is exactly the
one used by `FinFourLowTailRow.nonempty_leaf` in
`Research/Quitting/FinFourProducerAtlas/Leaves.lean`:

1. a singleton reached during bounded partial purification; or
2. complete purification followed by a terminal singleton or a dispatched
   closed monodromy segment.

The reviewed result
[`FIN4_MONODROMY_PRODUCER_IMPOSSIBLE`](../exports/FIN4_MONODROMY_PRODUCER_IMPOSSIBLE.md)
shows that the stored Fin4 monodromy segment is impossible. Its proof uses
only the raw dispatched trace fields, so it applies equally to the trace
returned from the self-tail-closed row; it does not use the original
`FinFourLowTailRow` constructor.

In either surviving singleton branch, the actual routed singleton retains
the same positive stage-mass floor and its literal post-date tail. The generic
result
[`FIN4_MINIMUM_SINGLETON_TO_STRONG_CONCENTRATED_PACKET`](../exports/FIN4_MINIMUM_SINGLETON_TO_STRONG_CONCENTRATED_PACKET.md)
then best-endpoint-purifies any fixed nonowner and produces a strong
concentrated packet with no mass loss.

Thus, at the mathematical classification level,

\[
\boxed{
\text{Fin4 quantitative tail escape}
\Longrightarrow
\text{source-attached strong concentrated-singleton packet}.}
\tag{20}
\]

This removes `escapedTailChargeOrRegeneration` as a separate atlas completion
contract, provided the new raw-low-row origin retains the external data just
listed. It does not consume the resulting strong concentrated packet; that
remains the common downstream obligation. In particular, the conclusion is
not being counted as terminal approximation, near-return, or well-founded
semantic descent.

### Current Lean packaging seam

The structures `FinFourPurifiedSingletonProducer` and
`FinFourTotalPurificationProducer` store

```text
low : FinFourLowTailRow source
```

even though `FinFourLowTailRow.nonempty_leaf` uses only the raw actual-row
data displayed in the invocation above. The self-tail-closed profile is not a
member of the original `SelectedRows` family, so it should not be falsely
packaged as a `FinFourLowTailRow`.

This is an interface-only repair. Introduce a small raw low-tail row passport,
for example

```text
structure FinFourActualLowTailRow (source) where
  profile : BehaviorProfile
  stage : Nat
  lambda : Real
  coalition : QuittingNonsingletonCoalition (Fin 4)
  lambda_pos : 0 < lambda
  lambda_le_stageMass : ...
  lowTail : quittingSpineDebtExcess ... < lambda * D_* / 2
```

make the purification producers depend on that passport, and provide adapters
from both `FinFourLowTailRow` and the self-tail closure. No mathematical
hypothesis or conclusion changes. Alternatively, add parallel constructors
for the raw dispatch and normalize them at the semantic-connections layer.

## 6. Lean-facing local targets

The reusable local definition and lemmas should be generic in the finite
player type:

```lean
def quittingSelfTailClosure
    (reward) (profile : BehaviorProfile) (stage : Nat) : BehaviorProfile :=
  quittingLiteralRootStackProfile reward
    (List.ofFn (fun k : Fin (stage + 1) =>
      quittingProfileLiveRoot reward profile k))
    profile

theorem quittingSelfTailClosure_liveRoot_eq_of_le ...

theorem quittingStageCoalitionMass_selfTailClosure ... :
  quittingStageCoalitionMass reward
      (quittingSelfTailClosure reward profile stage) stage terminal =
    quittingStageCoalitionMass reward profile stage terminal

theorem quittingAllContinueProfileSpine_selfTailClosure ... :
  quittingAllContinueProfileSpine reward
      (quittingSelfTailClosure reward profile stage) (stage + 1) = profile

theorem quittingSpineDebtExcess_selfTailClosure ... :
  quittingSpineDebtExcess reward
      (quittingSelfTailClosure reward profile stage) reference (stage + 1) =
    quittingTerminalDebtSum reward profile - reference
```

The exact full-profile spine identity follows by induction over the list from
`shiftProfile_quittingRootThenContinuationProfile`. If `List.ofFn` creates
avoidable indexing friction, define the prefix word recursively and prove the
same four lemmas simultaneously.

The Fin4 adapter then composes `E.rows.prefix_debt_tendsto` with
`E.subseq_strictMono.tendsto_atTop`, selects one sufficiently large index, and
calls `quittingPartialPurification_then_finFourSameStage_dispatch` exactly as
in Section 2.

## 7. Scope and nonclaims

This theorem does not:

* preserve cap-Nash exactness of the copied roots after the splice;
* say that the repaired whole profile is near the minimum fiber;
* turn the old escaped tail into current root absorption;
* produce an exact admissible chronology or uniform payoff directly; or
* consume the downstream strong concentrated packet.

None of these claims is needed for the atlas contraction. The source data
used are one literal marked row and one actual near-minimum source profile;
the same source is restarted after that row. No semantic carrier point is
substituted for the continuation.

## 8. Remaining question

After this contraction the tail-escape leaf is not independent. The atlas's
remaining conjecture-facing producer problem is the common strong
concentrated-singleton node: consume its source attachment into terminal
approximants, a cumulative admissible return, or a source-preserving
well-founded regeneration.
