# Followup 3 renewable child adapter and the two-port coherence boundary

**Author:** CODEX_SOURCE_GATE  
**Status:** ordinary-mathematical source/rank adapter proved; source-local
backward seam and off-minimum positive-root arm remain open  
**Date:** 2026-08-30

## 1. Question and answer

I audited source adapter (2) in `gpt/NONZERO_PERSIST_ATTEMPT_1.md`, Followup
3.  Its two prospective children are:

1. the same-minimum strict-support endpoint `T` obtained from the source
   profiles `s_n`, best-response targets `t_n`, and literal half stopping-law
   profiles; and
2. the literal positive-root prefixes `y_n = x ▷ t_n` in the off-minimum
   branch.

The first child **can** be made into a complete, same-residual,
source-faithful `FinFourMinimumAtomProducer` and then entered into the checked
renewable support-cardinality lane.  The construction uses the literal
`t_n`, not an unrelated realizing sequence.  The initial half-parent-to-child
support drop supplies a genuine one-use rank decrease, after which every
recursive edge is one of the checked strict-support descendants.  Any
source-independent terminal conclusion compiles back through the finite
trace.

The positive-root child has the same conclusion **only when its prefixed
limit lands exactly on the global minimum fibre**.  If it remains strictly
off minimum, it cannot be a `FinFourMinimumAtomProducer`; its strictly
decreasing real debt is not well founded, and the summable-hazard calculation
in Followup 3 permits an infinite Zeno descent without a finite rank.

There is also a sharp compiler boundary.  Neither regeneration gives an
uncharged map transporting source-local response or cap data back across the
best-response seam.  On the same-minimum branch the killed payer debt is
transferred in aggregate to the other three players, forcing a fixed
nonpayer leakage.  Moreover, the retained marked atom lives at the upstream
reattached port, while the minimum zero-payer-debt child is the downstream
port.  These two ports cannot be silently identified.

Thus adapter (2) splits as follows.

```text
same-minimum strict-support child
  -> literal same-residual source
  -> finite renewable support trace
  -> any source-independent terminal consumer;                 PROVED

positive-root child on the minimum fibre
  -> literal same-residual source
  -> one-use entry into the same finite trace;                  PROVED

positive-root child strictly off minimum
  -> strict real/Zeno descent only;                             OPEN

parent-source local certificate
  <- child-source local certificate across the horizontal seam OPEN,
     and impossible with vanishing uncharged all-coordinate error.
```

No Lean file was changed.

## 2. Declarations inspected

The source and chronology types are:

* `FinFourMinimumAtomProducer` in
  `Research/Quitting/FinFourProducerAtlas/Source.lean`;
* `FinFourMinimumAtomChronology` and
  `FinFourMinimumAtomProducer.nonempty_chronology` in
  `Research/Quitting/FinFourProducerAtlas/MinimumSingletonClockCompression.lean`;
* `QuittingMinimumLawCausalSuffixAtom` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticLawCarrierCausalization.lean`.

The source-faithful reconstruction ingredients are:

* `exists_retainedProfile_terminalSemanticLawCluster` in
  `Research/Quitting/MinimumFiberDebtTransfer.lean`;
* `exists_positive_finiteLawAtom_of_finFourHardResidual_minimum` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinFourMinimumLawFiniteAtom.lean`;
* `nonempty_sourceFaithfulMinimumCausalChronology` in
  `Research/Quitting/SourceFaithfulMinimumLawCausalization.lean`.

The generic support handoff is
`QuittingMinimumEndpointSupportRankHandoff` and
`exists_minimumEndpointSupportRankHandoff_or_debtAscent` in
`Research/Quitting/StoppingLawMinimumEndpointSupportRankHandoff.lean`.
The current checked declaration requires exact zero target debt at every
index.  Followup 3 uses the ordinary extension with target debt tending to
zero; Section 3.1 below records why that extension is valid.

The renewable lane is:

* `FinFourRenewableMinimumSourceNode` in
  `CanonicalPairEndpointSourceRegeneration.lean`;
* `FinFourFullReplacementSourceRegeneration` and
  `FinFourRenewableSupportDescent` in
  `CanonicalPairFullReplacementSourceRegeneration.lean`;
* `FinFourRenewableTrace`, `nonempty_renewalTrace`, and its support-cardinality
  bounds in `CanonicalPairRenewableSourceRank.lean`; and
* `FinFourRenewableTrace.consume` in
  `CanonicalPairMinimumEndpointRenewal.lean`.

For comparison, the canonical initial adapter is
`CanonicalPairEndpointSourceRegeneration`; it uses a stronger concentrated
endpoint packet with an already named positive marked atom.  The construction
below uses the weaker recursive pattern: jointly lift the literal child
profiles, select a positive coordinate of that exact law, and reselect a
finite-window causal mark without changing the profile family.

The positive-root checked boundary is
`FinFourStrictRayPositiveRootReturn.nonempty_minimumLawHandoff_or_offMinimumDescent`
in `StrictRayPositiveRootReturn.lean`.  Its own module comment correctly says
that the off-minimum arm has no renewable rank or quantitative consumer.

## 3. Same-minimum child regeneration

### 3.1 Exact input

Let `source` be the incoming `FinFourMinimumAtomProducer`, with hard residual
`source.residual` and positive minimum debt

\[
 D_* = D(source.point.1)>0.
\]

Assume the corrected two-cut and best-response argument supplies actual
profiles `s_n,t_n`, a fixed payer `p`, and, after a common strict
subsequence, semantic limits

\[
 Z(s_n)\to S,\qquad Z(t_n)\to T,
\]

with

\[
 D(S)=D(T)=D_*,\qquad d_p(S)=g>0,\qquad d_p(t_n)\to0.
\tag{1}
\]

Only player `p` differs between `s_n` and `t_n`.  Let `h_n` be the literal
half stopping-law mixture of the two `p` strategies.  The stopping-law debt
convexity and global minimality argument gives a limit `H` satisfying

\[
 D(H)=D_*,\qquad
 d_i(H)=\frac{d_i(S)+d_i(T)}2,
\tag{2}
\]

and therefore

\[
 \operatorname{supp}_+(T)\subsetneq\operatorname{supp}_+(H).
\tag{3}
\]

The checked generic handoff theorem assumes `d_p(t_n)=0` for every `n`.
Nothing in its compactness proof needs that pointwise equality except the
passage to `d_p(T)=0`.  Under (1), continuity gives exactly the same limit
equality.  All finite-index debt convexity inequalities remain valid, and
the equality in (2) follows after summing and using minimum total debt on both
limits.  Hence the asymptotic-zero extension used by Followup 3 is valid
ordinary mathematics.  It is not yet a named checked declaration.

Denote this extended handoff by `handoff`; it retains:

* the exact target profile sequence `t_n` on its selected subsequence;
* `endpointCluster = T` and `halfCluster = H`;
* a tangent family `nextFamily` based exactly at `T`; and
* the strict support inclusion (3).

### 3.2 Joint-law lift of the literal target profiles

Apply `exists_retainedProfile_terminalSemanticLawCluster` to the selected
literal target profiles.  It returns a further strict subsequence and a joint
semantic/law point `J_T` such that

\[
  J_T\in\mathcal C^{\rm joint},qquad
  J_T.1=T,
\tag{4}
\]

and

\[
  \bigl(Z(t_{n_k}),\operatorname{Law}(t_{n_k})\bigr)\to J_T.
\tag{5}
\]

This is the required ancestry statement: the joint law is selected from the
same best-response endpoints that killed the block payer's debt.

Since `T` lies on the same global minimum fibre, (4) gives

\[
 D(J_T.1)=D_*=\operatorname{InfDebt}(r).
\tag{6}
\]

The theorem
`exists_positive_finiteLawAtom_of_finFourHardResidual_minimum`, applied to
`source.residual` and this exact `J_T`, selects a finite coalition `C_T` with

\[
 J_T.2(C_T)>0.
\tag{7}
\]

No law over the same semantic point is reselected.

Now apply `nonempty_sourceFaithfulMinimumCausalChronology` to `J_T`, `C_T`,
and the exact profile family in (5).  It retains those profiles and returns
cutoffs, positive finite marks, and arbitrarily deep exact cap--Nash root
words.  Its fields assemble a
`QuittingMinimumLawCausalSuffixAtom reward J_T`.

### 3.3 Complete child source and node

Define `childSource : FinFourMinimumAtomProducer reward bound` by

```text
residual     := source.residual
point        := J_T
point_mem    := joint carrier membership from (4)
semantic_mem := its first-coordinate carrier membership
minimum      := the minimum property transported through J_T.1 = T
inf_pos      := source.inf_pos
debt_eq_inf  := (6)
atom         := the causal atom built from (5)--(7).
```

The public `FinFourMinimumAtomChronology childSource` is the same causal
chronology, so its profile field is literally a subsequence of `t_n`.
In particular

\[
 childSource.residual=source.residual.
\tag{8}
\]

Use `handoff.nextFamily` as the child's tangent frontier.  Its stored base
equality and `J_T.1=T` give a node

```text
childNode : FinFourRenewableMinimumSourceNode reward bound
```

with `childNode.source = childSource`.  This is a complete renewable node;
the tangent family need not have been extracted from the causal atom
chronology, exactly as documented by the checked node definition.

Repeat the identical construction on the literal half-mixture profiles
`h_n`. Their semantic limit is the minimum point `H`, so a retained joint-law
cluster, positive finite law atom, and source-faithful causal chronology give
a complete same-residual `halfSource`. Attach `handoff.parentFamily`, whose
base is exactly `H`, to obtain

```text
halfNode : FinFourRenewableMinimumSourceNode reward bound.
```

Thus both ends of the initial strict-support edge are actual complete minimum
sources built from their literal profile families. The initial edge is not a
checked `FinFourRenewableSupportDescent`, because `t_n` is a generic complete
best-response replacement rather than a `FullReplacementCluster` selected
from `halfNode.frontier`. It is a new one-use bridge into the existing graph;
all subsequent recursive edges are the checked full-replacement descents.

This proves the requested source regeneration for the same-minimum child and
also supplies an honest source at its half parent.

## 4. A genuine finite rank from the half parent

The generic handoff has the regenerated `halfNode` at `H` and `childNode` at
`T`. Define bridge-tagged states

```text
bridgeSource(halfNode)
tangent(node)
terminal
```

and the rank

\[
 R(\mathsf{terminal})=0,\qquad
 R(\mathsf{tangent}(N))=1+|\operatorname{supp}_+(N)|,\qquad
 R(\mathsf{bridgeSource}(H))=1+|\operatorname{supp}_+(H)|.
\tag{9}
\]

The source-to-source bridge edge is strict by (3). Every later node-to-node
edge is a checked
`FinFourRenewableSupportDescent`, so its support is a strict subset of the
parent support.  Exit edges land at rank zero.  Hence every declared edge
strictly lowers the single natural rank (9); there is no constructor back to
`bridgeSource`.

Since `Fin 4` has four players and the first child already has support
strictly below `supp_+(H)`, its support has cardinality at most three.
`FinFourRenewableMinimumSourceNode.nonempty_renewalTrace` therefore reaches a
terminal exit after at most two further recursive child edges.  Counting the
entry edge, this adapter has height at most three.

This is not a comparison against a freshly reset parent at every stage. The
literal half source is spent once; all subsequent recursion lives in the
checked source-node graph and strictly descends the support of the preceding
node.

## 5. Exact backward-consumer scope

Let `P` be a proposition depending only on the reward table, not on a local
source node.  If every `FinFourRenewableTerminalExit terminalNode` implies
`P`, the checked `FinFourRenewableTrace.consume` gives `P` at the child node.
The one-time entry does not change the table, so this is also a backward
compiler from the Followup 3 handoff to `P`.

In particular, if the three terminal exits are supplied with the global
consumers listed in `FIN4_RENEWAL_TERMINAL_EXIT_CONSUMERS.md`, then the child
adapter compiles their uniform-equilibrium conclusion all the way back.  No
comparison of parent and child deviation menus is required for such a global
existential conclusion.

This is the exact same compiler-free scope as
`CanonicalPairMinimumEndpointSupportRankHandoff.consume_renewalTerminalExit`.
It does **not** transport a property mentioning the incoming source profile,
the original marked date, its cap, or its response menu.

## 6. Why a source-local backward seam is unavailable

There are two independent obstructions.

### 6.1 Fixed Fin4 debt leakage

On the same-minimum branch, (1) gives

\[
 \sum_{i\ne p}\bigl(d_i(T)-d_i(S)\bigr)
 =d_p(S)-d_p(T)=g.
\tag{10}
\]

Thus some nonpayer `j` satisfies

\[
 d_j(T)-d_j(S)\ge g/3>0.
\tag{11}
\]

This is the same intrinsic horizontal leakage used by the canonical renewal
audit; it requires only equal total debt and killing the payer.  Any proposed
seam comparing every player's source and target deviation gain with error
`o(1)` would, after taking suprema, force all debt-coordinate changes to be
`o(1)`, contradicting (11).  A valid source-local compiler must therefore be
charged, centered, or deliberately discard the parent-local response data.

This does not rule out raw cap closeness when prescribed payoff moves with
the cap, and it does not rule out a future charged compiler.

### 6.2 The marked atom and zero-debt endpoint occupy different ports

Followup 3 retains the original row only in the reattached profiles

\[
 \widehat t_n=A_n\triangleright x_n^{mark}\triangleright t_n.
\tag{12}
\]

The endpoint `T`, its zero payer debt, and the strict support comparison are
properties of the downstream `t_n`.  The original marked atom is an outcome
of the upstream `\widehat t_n`; that marked-row occurrence and its mass are
not events of the suffix `t_n`.  The same coalition label may of course occur
again inside the suffix, but no field identifies such a later occurrence
with the retained upstream mark.

The regeneration in Section 3 honestly selects a new positive finite atom of
the downstream joint law and causalizes it along the literal `t_n`.  Nothing
identifies that selected atom with the upstream marked atom.  Conversely,
causalizing the reattached `\widehat t_n` would produce a source at the
semantic limit of `\widehat t_n`, not at `T`; minimum debt and zero payer debt
need not survive reattachment.

Therefore one cannot form a single source state possessing both ports'
fields merely by record assembly.  This is a coherence no-go, not a missing
compactness lemma.

## 7. Positive-root prefixed child

Suppose `T` is the off-minimum downstream endpoint and `x` is one fixed exact
cap--Nash root at `T.2` with absorption `a>0`.  Followup 3 uses the actual
profiles

\[
 y_n=x\triangleright t_n
\tag{13}
\]

and thins their cap defects summably.  Their joint semantic/law limit `Y`
obeys

\[
 D(Y)=(1-a)D(T)<D(T).
\tag{14}
\]

### 7.1 Minimum-fibre landing

If `D(Y)=D_*`, repeat Section 3 with the literal profile family `y_n`.
Joint lifting, finite-atom selection at that exact joint law, and
source-faithful causalization produce a same-residual
`FinFourMinimumAtomProducer` whose chronology is a subsequence of the actual
positive-root prefixes.

The specialized strict-ray version is already checked as
`FinFourStrictRayMinimumLawHandoff`; the source-faithful construction above
adds the literal `y_n` ancestry required by Followup 3.

Attach a tangent family at `Y` using
`exists_positiveMinimumDebtTangentFamily_of_pair`, form a renewable node, and
run `nonempty_renewalTrace`.  A one-use incoming phase of rank `6` enters a
node of rank at most `5`, after which support cardinality decreases on every
recursive edge.  Thus the minimum-landing positive-root child is renewable
and has the same source-independent backward consumer as Section 5.

There need not be a support drop at the root prefix itself.  Indeed `D_*>0`
rules out `a=1`, and exact cap Nash gives coordinatewise

\[
 d_i(Y)=(1-a)d_i(T),
\tag{15}
\]

so `Y` and `T` have the same positive-debt support.  The one-use phase tag,
not a fictitious support drop, accounts for this entry.

### 7.2 Strictly off-minimum landing

If `D(Y)>D_*`, the defining `minimum` and `debt_eq_inf` fields of
`FinFourMinimumAtomProducer` are false at `Y`.  No source adapter can package
that point as a minimum producer without changing the point.

Iteration of positive roots does not repair this automatically.  With
cap-defect residuals `rho_k` and absorptions `a_k`, the exact account is

\[
 D_{k+1}=(1-a_k)D_k+\rho_k.
\tag{16}
\]

Under `D_k\ge D_*>0` and `\sum_k\rho_k<\infty`, Followup 3 correctly derives
`\sum_k a_k<\infty`.  This is compatible with infinitely many strict steps
and no finite minimum landing.  For example, the scalar choice

\[
 a_k=1-e^{-2^{-k-2}},\qquad \rho_k=0,
\]

has a positive product `\prod_k(1-a_k)` and hence a strictly decreasing debt
sequence with a limit still above `D_*` after choosing `D_0` appropriately.
This scalar regression is not a quitting-game counterexample, but it is sharp
for every inference available from (16).

Accordingly the off-minimum positive-root arm remains exactly what
`StrictRayPositiveRootReturn.lean` says it is: a strict real descent with no
renewable rank or terminal consumer.

### 7.3 Why paid/reset regeneration does not close the off-minimum arm

The `RESET_REGEN` packets do not supply a hidden minimum-source adapter here.
`maximalOneStepPaidResetRegeneration_or_uniqueAllContinue` reconstructs an
actual paid/reset descendant when its input already carries the paid row,
zero reset coordinate, positive incidence, and fixed-law reset dispatch. Its
descendant remains a paid/reset source, not a
`FinFourMinimumAtomProducer` at an off-minimum semantic point.

Moreover, on repeated positive-absorption descendants, exact cap Nash scales
every debt coordinate by the same Continue mass. The support and normalized
debt vector are therefore constant, while positive global minimum debt makes
the product of Continue masses stay bounded away from zero. This is the
checked/independently audited Zeno normal form: absorptions are summable, but
no support rank drops and no finite minimum landing follows.

Finally, the downstream prefix profile `y_n` in (13) does not by itself carry
the upstream marked paid row or reset incidence. Reattaching those fields
changes the semantic point, just as in Section 6.2. Thus applying paid/reset
regeneration would first require another two-port source bridge, and even
then its infinite Zeno arm is the same unresolved real-valued descent rather
than the renewable support lane.

## 8. Final packet-level verdict

Source adapter (2) is no longer one monolithic open statement.

* **Same-minimum strict-support child:** source reconstruction, same-residual
  ancestry, renewable natural rank, finite trace, and backward compilation
  of source-independent terminal conclusions are proved in ordinary
  mathematics from the existing fields.
* **Positive-root child landing at the minimum:** the same conclusion holds,
  using a one-use phase rather than a false support drop.
* **Positive-root child remaining off minimum:** no renewable producer or
  well-founded rank follows; the Zeno scalar account is the sharp surviving
  regression.
* **Source-local backward compiler:** not supplied.  The fixed nonpayer debt
  leakage and the upstream/downstream two-port split rule out treating it as
  a vanishing-error or record-repackaging seam.

The remaining formal work is narrow: implement the asymptotic-zero variant
of `exists_minimumEndpointSupportRankHandoff_or_debtAscent` and package the
generic literal-target regeneration of Section 3.  The mathematical terminal
consumers of the renewable trace and the off-minimum positive-root Zeno arm
remain separate frontier questions.
