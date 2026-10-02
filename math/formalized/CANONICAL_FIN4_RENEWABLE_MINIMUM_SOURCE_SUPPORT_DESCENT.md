# Renewable canonical Fin4 minimum-source support descent

Authors: `GPT`, `CODEX_ROOT`

Independent review:
[`CODEX_ROOT`](../feedback/CANONICAL_FIN4_RENEWABLE_HANDOFF__BY_CODEX_ROOT.md)

Fresh adversarial scope review:
[`CODEX_BANACH`](../feedback/CANONICAL_FIN4_RENEWABLE_HANDOFF__CORRECTED__BY_CODEX_BANACH.md)

Earlier falsification and repair boundary:
[`CODEX_BANACH`](../feedback/CANONICAL_FIN4_RENEWABLE_HANDOFF__BY_CODEX_BANACH.md)

## Exact statement

Fix a four-player quitting reward table `reward`, a reward bound `bound`, and
the checked source-attached data

```text
source       : FinFourMinimumAtomProducer reward bound
returnSource : FinFourOwnerCompressedMinimumReturnForcedPairSource source
packet       : FinFourOwnerCompressedMinimumReturnForcedPairPacket
                 returnSource lambda
handoff      : CanonicalPairMinimumEndpointSupportRankHandoff packet.
```

There is a well-founded transition system of finite height with three kinds
of state:

1. one incoming canonical-handoff state;
2. minimum-source tangent nodes; and
3. nonrecursive residual exits.

A minimum-source tangent node contains

```text
node.source   : FinFourMinimumAtomProducer reward bound
node.frontier : QuittingPositiveMinimumDebtTangentFamily reward
```

and satisfies the literal attachments

```text
node.source.residual = source.residual
node.frontier.base   = node.source.point.1.
```

The incoming state has a transition to a first node whose source is rebuilt
from a strict subsequence of the handoff's literal paid endpoint profiles.
Its joint-law semantic coordinate is exactly the handoff endpoint cluster,
its selected finite terminal is the handoff endpoint terminal, and its causal
chronology retains the corresponding original endpoint dates.

Every minimum-source tangent node has the following exhaustive dispatch.

1. **Positive total slope:** some active mover has positive total tangent
   slope.  This is a nonrecursive residual exit.
2. **Flat support entry:** a flat tangent column enters a coordinate having
   zero debt at the base.  This is a nonrecursive residual exit.
3. **Off-minimum paid endpoint:** a literal full-replacement cluster lies
   strictly above the global minimum and carries an eventually positive
   source-matched first-disagreement row.  This is a nonrecursive residual
   exit.
4. **Minimum-fibre child:** a literal full-replacement cluster lies on the
   global minimum fibre.  The exact full-replacement profile sequence is
   rebuilt as a complete child minimum source, and the child tangent family
   has positive-debt support strictly contained in the parent's support.

Only the fourth output is recursive.  Define

```text
rank(exit)       = 0
rank(node N)     = 1 + card(N.frontier.positiveDebtSupport)
rank(incoming)   = 6.
```

Every transition strictly decreases this single natural-valued rank.  Since a
positive-minimum tangent support is nonempty and has cardinality at most four,
there are at most three node-to-node recursive descents after the initial
regeneration.

In addition, every recursive minimum-fibre replacement satisfies an exact
horizontal debt-transfer law.  If `b` is the parent base, `c` is the child
endpoint cluster, and `m` is the replaced active mover, then

```text
d_m(c) = 0,
d_m(b) > 0,
sum_i d_i(c) = sum_i d_i(b),
sum_{i != m} (d_i(c) - d_i(b)) = d_m(b).
```

Consequently, for some nonmover `i`,

```text
d_i(c) - d_i(b) >= d_m(b) / 3 > 0.
```

Thus no coordinatewise debt-nonincrease theorem and no symmetric uncharged
uniform-in-response unilateral-gain comparison with vanishing error can hold
across this horizontal seam.  The debt ledger alone does not rule out
closeness of the raw cap vectors, because the prescribed payoffs may move too.

## Conjecture-facing change

This strictly narrows the obligation in
[`CODEX_ROOT__RESOLVED_FIN4_RENEWABLE_CANONICAL_SUPPORT_HANDOFF.md`](../notes/CODEX_ROOT__RESOLVED_FIN4_RENEWABLE_CANONICAL_SUPPORT_HANDOFF.md)
by completing its source-reconstruction and renewable-rank subproblem through
a finite-origin phase and exhaustive next dispatch.  It does **not** complete
alternative 1 as literally stated, because it supplies no backward compiler
across the parent-to-full-replacement seam.

Previously, the checked canonical handoff proved only one strict support
inclusion relative to a newly constructed half-mixture parent.  It did not
reconstruct a complete minimum source at the endpoint, and therefore did not
orient repeated regeneration.  The present theorem:

- reconstructs the first complete source from the handoff's literal endpoint
  profiles and dates;
- reconstructs every recursive child from the parent's literal
  full-replacement profiles;
- preserves the original hard residual at every node;
- exposes an exhaustive one-step dispatch instead of hiding recursion inside
  strong induction; and
- uses one global rank whose origin phase cannot recur.

The three residual exits and the horizontal backward-composition problem
remain separate conjecture-facing obligations.  The result contracts the
nonrenewable handoff into a finite-height renewable reduction to those exits;
it does not consume them into a uniform-equilibrium payoff.

## Definitions and assumptions

For a terminal semantic pair `z = (U,B)`, write

```text
d_i(z) = B_i(z) - U_i(z)
D(z)   = sum_i d_i(z)
support+(z) = {i : 0 < d_i(z)}.
```

`FinFourMinimumAtomProducer reward bound` contains:

- a quantitative four-player hard residual for the same reward table;
- a joint semantic/outcome-law carrier point `point`;
- global minimality of `D(point.1)` and equality to the literal debt infimum;
- positivity of that infimum; and
- a positive finite terminal atom together with an actual source-matched
  causal chronology and arbitrarily deep exact cap--Nash prefix words.

`QuittingPositiveMinimumDebtTangentFamily reward` contains a globally
minimizing semantic base, actual source and one-player full-replacement profile
families, their tangent matrix, and exact cluster/re-extraction data.

A node requires equality only between the tangent base and the semantic
coordinate of its minimum source.  It deliberately does not require the
tangent source profiles to equal the chronology stored by the source atom.
The recursive tangent dispatch uses the former; the hard-residual and
same-point finite-atom reconstruction use the latter.

All profiles are literal behavioral profiles.  Caps quantify over arbitrary
unilateral behavioral deviations, including Never and unbounded stopping
times.  The source reconstruction does not replace those caps by stationary
or finite-horizon deviations.

## Source correspondence

The checked entrance is
`CanonicalPairMinimumEndpointSupportRankHandoff` in
`Research/Quitting/FinFourProducerAtlas/CanonicalPairMinimumEndpointSupportRankHandoff.lean`.
Its named endpoint/source/half convergence theorems guarantee that the
concentrated endpoint packet and the support handoff use one coherent
subsequence.

The target source type is `FinFourMinimumAtomProducer` in
`Research/Quitting/FinFourProducerAtlas/Source.lean`.  Its causal field is
`QuittingMinimumLawCausalSuffixAtom`, defined in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticLawCarrierCausalization.lean`.

The two source-faithful construction theorems are in
`Research/Quitting/SourceFaithfulMinimumLawCausalization.lean`:

- `nonempty_sourceFaithfulMinimumCausalization` retains a supplied realizing
  profile family and supplied uniformly positive marked dates;
- `nonempty_sourceFaithfulMinimumCausalChronology` retains a supplied profile
  family while honestly reselecting positive dates from finite terminal-mass
  windows.

The latter chronology has exactly the fields required to build a
`QuittingMinimumLawCausalSuffixAtom`.  This packaging pattern is already
checked in
`FinFourSourceFaithfulReselectedMarkRegeneration.atom` and `.next` in
`Research/Quitting/FinFourProducerAtlas/SourceFaithfulThreeRoleRegeneration.lean`.

The pointwise atom theorem
`exists_positive_finiteLawAtom_of_finFourHardResidual_minimum` is in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinFourMinimumLawFiniteAtom.lean`.
It applies to every supplied minimizing joint-law point; it does not select an
unrelated law over the same semantic coordinate.

The recursive support facts are checked in
`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/MinimumFiberSupportDrop.lean`:

- `FullReplacementCluster.debtChange_eq_tangent_of_flat_of_minimumFiber`;
- `FullReplacementCluster.mover_debt_eq_zero`; and
- `FullReplacementCluster.positiveDebtSupport_card_lt_of_exactDiagonal_of_flat_of_noEntry_of_minimumFiber`.

The exhaustive minimum-fibre/off-minimum split is
`FullReplacementCluster.minimumFiberSupportRankDescent_xor_offMinimumPaidFirstDisagreement`
in
`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/FlatCirculationSupportRankElimination.lean`.
That file's `reducedSupportRankAlternative` already proves termination by
strong induction, but it does not retain a complete source at each recursive
endpoint.  The new content is the literal-law source reconstruction and the
explicit globally ranked transition system.

## Proof

### 1. Joint-law lift of a retained semantic sequence

Let `profiles n` be actual profiles whose semantic pairs converge to `z`.
Each joint point

```text
J_n = (Sem(profiles n), Law(profiles n))
```

lies in the compact terminal semantic/law carrier.  Select a strictly
increasing subsequence on which `J_n` converges to `q`.  Projection gives
convergence of its semantic coordinate to `q.1`.  The original semantic
convergence persists on the subsequence, so uniqueness of limits yields

```text
q.1 = z.
```

This construction retains the supplied profile sequence up to a strict
subsequence; it does not choose another semantic realizer.

### 2. Initial endpoint source reconstruction

Let

```text
p_n = packet.rayPaidTargetProfile
        (handoff.endpointPacket.subsequence n),
t_n = handoff.endpointPacket.subsequence n,
T   = handoff.endpointPacket.terminal,
z   = handoff.supportHandoff.endpointCluster.
```

The checked handoff gives `Sem(p_n) -> z`.  Apply the joint-law lift and call
the limit `q`; then `q.1 = z`.

The endpoint concentrated packet gives the fixed bound

```text
packet.rayResolution^2 <=
  StageMass(p_n, t_n, T)
```

for every `n`, and `packet.rayResolution > 0`.  The complete terminal-law
coordinate for `T` dominates each individual stage mass.  Equivalently, after
passing to the joint limit, the same terminal coordinate is at least the
positive floor.  Hence

```text
0 < q.2(some T).
```

The endpoint total debt is the incoming global minimum.  Together with the
incoming source's positive debt infimum, this supplies the remaining
hypotheses of `nonempty_sourceFaithfulMinimumCausalization` for the exact
profiles `p_(a n)` and exact marks `t_(a n)` selected by the joint-law
subsequence `a`.

Package the resulting causalization as a
`QuittingMinimumLawCausalSuffixAtom reward q`, and then form
`endpointSource : FinFourMinimumAtomProducer reward bound` using the unchanged
hard residual.  Its chronology uses the literal endpoint profiles and dates.

The handoff already supplies a re-extracted tangent family based at `z`.
Since `endpointSource.point.1 = q.1 = z`, these two objects form the first
minimum-source tangent node.

### 3. Recursive source reconstruction

Fix a node, an active mover `m`, and a full-replacement cluster `c` in the
flat/no-entry/minimum-fibre branch.  The checked endpoint object supplies an
actual sequence

```text
f_n = node.frontier.fullReplacementProfile m (endpoint.subseq n)
```

whose semantic pairs converge to `c`.

Jointly compactify a further strict subsequence of `f_n`.  Its joint-law limit
`q` satisfies `q.1 = c`.  Because `c` has the same total debt as the parent
base and that base is globally minimizing, `q.1` is globally minimizing.

Apply `exists_positive_finiteLawAtom_of_finFourHardResidual_minimum` to this
exact `q` and the node's retained hard residual.  Obtain a finite terminal `T`
with

```text
0 < q.2(some T).
```

Apply `nonempty_sourceFaithfulMinimumCausalChronology` to the same composed
full-replacement profile sequence.  It retains every supplied profile while
selecting finite windows and positive marked dates.  Package its fields into a
causal suffix atom and then a complete child source.  The child's residual is
the parent's residual and its semantic point is `c`.

The checked minimum-fibre support theorem already supplies a tangent family
based at `c` with

```text
support+(child) proper-subset support+(parent).
```

Pair this frontier with the reconstructed source to obtain the recursive child
node.

### 4. Exhaustive dispatch

Apply the checked tangent-family exhaustive alternative.

- A positive total slope gives exit 1.
- Flat support entry gives exit 2.
- In either flat/no-entry branch, choose an active mover; positive minimum
  debt ensures that active support is nonempty.
- Choose a literal full-replacement cluster for that mover.
- Apply
  `minimumFiberSupportRankDescent_xor_offMinimumPaidFirstDisagreement`.
  Its off-minimum arm gives exit 3.  Its minimum-fibre arm gives the recursive
  child constructed above.

These alternatives exhaust every node.  Only the child constructor returns a
node.

### 5. Well-founded rank

Every node support is a subset of the four players, so its rank is at most
five, below incoming rank six.  Every recursive edge has strict support
inclusion and therefore strictly smaller support cardinality.  Every residual
exit has rank zero.  There is no transition constructor whose target is the
incoming state.

Thus every transition strictly decreases the displayed natural rank, and the
transition relation is well founded.  Positive total debt makes node support
nonempty, so the longest possible recursive chain is

```text
4 players -> 3 players -> 2 players -> 1 player,
```

with at most three node-to-node descents.

### 6. Exact horizontal debt leakage

For a recursive minimum-fibre endpoint, the checked mover theorem gives
`d_m(c)=0`.  The mover is active at the parent, so `d_m(b)>0`.  Equality of
total debts gives

```text
0 = sum_i (d_i(c)-d_i(b)).
```

Separating the mover term yields

```text
sum_{i != m} (d_i(c)-d_i(b)) = d_m(b).
```

There are three nonmovers.  If each of their changes were less than
`d_m(b)/3`, their sum would be less than `d_m(b)`.  Therefore one nonmover has
increase at least `d_m(b)/3`.

In the flat branch, the checked coordinate theorem further identifies each
change with the corresponding tangent entry.  The seam therefore carries a
nonzero signed debt-transfer vector whose sum is zero.

## Boundary tests

### Positive boundary: rank renewal is independent of the incoming support

The first regenerated tangent support may have any cardinality from one to
four and need not compare with the incoming source support.  The rank still
decreases because the incoming phase has the fixed rank six and can never be
re-entered.  Subsequent recursive comparisons are ordinary strict support
inclusions.  This is precisely the case that defeated the earlier one-time
endpoint-versus-half rank.

### Negative boundary: no arbitrary horizontal response transport

Consider two active players `p,j`, embedded in Fin4 with the other two players
passive.  Let the parent profile prescribe Never for both.  Give `j` payoff
one only on simultaneous quitting by `{p,j}`, and zero otherwise.  The payoff
contrast for `j` between `QuitAt 0` and Never is zero at the parent.  After
replacing `p` by sure Quit at date zero, the same response contrast is one.
A common all-Continue or cap--Nash prefix only multiplies the contrast behind
the child; it does not reconstruct the parent contrast.

This example is not a positive-minimum counterexample.  It falsifies the
general cross-seam response identity used by the earlier version of the
handoff.

### Intrinsic negative boundary: debt leakage is unavoidable

Under the actual minimum-fibre recursive hypotheses, the exact ledger forces
some nonmover debt increase of at least `d_m(b)/3`.  Thus neither

```text
forall i, d_i(c) <= d_i(b)
```

nor a uniform coordinatewise debt error tending to zero can hold.  Any future
cross-seam compiler must carry, centre, cancel, or pay this transfer.

## Adapter and consumer

The actual-data adapter is the checked
`CanonicalPairMinimumEndpointSupportRankHandoff packet`.  The initial
regeneration uses its coherent endpoint packet directly.  Every recursive
adapter uses the parent frontier's literal full-replacement profiles directly.
No unrelated minimum law, source profile, or tangent base is selected.

The downstream structural consumer is the checked reduced tangent dispatch:
positive total slope, flat support entry, or off-minimum paid first
disagreement.  The new transition theorem removes minimum-fibre support
descent as a terminal residual by rebuilding it as a recursive child of
strictly smaller rank.

This is a strict reduction of the canonical handoff to a smaller atlas
boundary.  It is not a behavioral backward compiler and is not a consumer of
the three remaining residual exits into uniform equilibrium.

## Lean handoff

A single Research module should suffice:

```text
Research/Quitting/FinFourProducerAtlas/
  CanonicalPairMinimumEndpointRenewal.lean
```

Suggested new declarations are:

```text
QuittingSemanticSequenceLawLift
nonempty_semanticSequenceLawLift

CanonicalPairEndpointMinimumSourceRegeneration
nonempty_endpointMinimumSourceRegeneration

FinFourMinimumSourceTangentNode
FinFourMinimumFiberSourceDescent
nonempty_minimumSourceRenewalDispatch

CanonicalPairRenewableSourceRankState
CanonicalPairRenewableSourceRankTransition
canonicalPairRenewableSourceRank
canonicalPairRenewableSourceRank_transition_lt
CanonicalPairRenewableSourceRankCertificate
nonempty_canonicalPairRenewableSourceRankCertificate

FullReplacementCluster
  .exists_other_debtIncrease_div_three_of_minimumFiber
CanonicalPairMinimumEndpointSupportRankHandoff
  .exists_other_endpointDebtIncrease_div_three
```

The joint-law lift should use compactness of the checked carrier and uniqueness
of the semantic limit.  The initial reconstruction should call
`nonempty_sourceFaithfulMinimumCausalization`; recursive reconstruction should
call `nonempty_sourceFaithfulMinimumCausalChronology`.  The latter can be
packaged into the source atom exactly as in
`FinFourSourceFaithfulReselectedMarkRegeneration.atom`.

Do not add a backward compiler, response transport, or parent/child source
sequence equality field.  Source-faithful response transport is valid only
through a newly selected prefix over one fixed suffix.

The transition certificate should prove well-foundedness by subrelation to the
natural rank.  The three nonrecursive outputs should be represented explicitly
as residual exits rather than labelled terminal game outcomes.

## Scope and nonclaims

This result does not prove:

- terminal approximate Nash profiles;
- a uniform-equilibrium payoff;
- a positive admissible near-return;
- a cap or response compiler across full replacement;
- that positive slope, support entry, or a paid off-minimum row is already
  consumed; or
- that the finite four-player quitting-game conjecture is resolved.

It proves renewable source reconstruction and strict finite support descent
for the minimum-fibre branch, and it identifies an unavoidable charged seam
that any stronger backward composition must respect.

## Formalization record

The export packet at intake had SHA-256
`79c0ea0cc75721e42ede1d54c33f5197d0607c7f65f0b79db1d90f9d02c8c779`.
The generic minimum-fibre debt account was integrated at repository revision
`df143575d8d4b7a0e49155884c191025be60b484`, and the source-regeneration and
renewable-rank implementation at
`f0f1b342c6a956121c586030616f4d17e4d69ebf`.  The exact compact-height,
same-residual, Fin4 one-third-transfer, and horizontal no-go surfaces were
completed and pushed at
`12525820b822ba804ed41e5b4d519e4ade098efc`.

The checked implementation has the following layers.

1. `Research/Quitting/FinFourProducerAtlas/`
   `CanonicalPairEndpointSourceRegeneration.lean` retains the handoff's
   literal endpoint profiles and dates in `CanonicalPairEndpointJointLimit`
   and `CanonicalPairEndpointSourceRegeneration`.
   `CanonicalPairMinimumEndpointSupportRankHandoff.nonempty_endpointSourceRegeneration`
   builds the complete same-residual minimum source, while
   `CanonicalPairEndpointSourceRegeneration.next_semantic_eq_endpointCluster`,
   `chronology_profile_eq`, and `chronology_mark_eq` expose the exact endpoint
   and provenance literally.
2. `Research/Quitting/FinFourProducerAtlas/`
   `CanonicalPairFullReplacementSourceRegeneration.lean` performs the same
   construction for every recursive literal full-replacement sequence.
   `FinFourRenewableMinimumSourceNode.nonempty_fullReplacementSourceRegeneration`
   retains the parent's hard residual, and
   `FinFourRenewableMinimumSourceNode.nonempty_supportDescent` packages the
   strict positive-debt-support inclusion into
   `FinFourRenewableSupportDescent`.
3. `Research/Quitting/FinFourProducerAtlas/`
   `CanonicalPairRenewableSourceRank.lean` gives the exhaustive node dispatch
   in `terminalExit_or_nonempty_supportDescent` and the finite trace in
   `nonempty_renewalTrace`.  `canonicalPairRenewableRank` is exactly zero on
   the residual state, one plus support cardinality on tangent nodes, and six
   on the one-use incoming state.
   `canonicalPairRenewableTransition_rank_lt`,
   `canonicalPairRenewableTransitionRel_wellFounded`, and
   `not_canonicalPairRenewableTransitionRel_from_terminal` make strictness,
   well-foundedness, and nonrecursive residual termination literal.
   `FinFourRenewableTrace.descentCount_le_three` gives the exact bound of three
   recursive node-to-node descents.  The trace and certificate
   `exists_terminalExit_sameResidual` projections retain the original hard
   residual at the final structural exit.
4. `Research/Quitting/MinimumFiberDebtTransfer.lean` records the exact signed
   account in `FullReplacementCluster.minimumFiber_debtTransfer` and the
   generic equal-share theorem
   `exists_nonmover_debtChange_moverDebt_div_card_le`.  The Fin4 specialization
   is literal in
   `FinFourRenewableSupportDescent.exists_nonmover_debtChange_moverDebt_div_three_le`,
   and the original endpoint handoff has the parallel theorem
   `CanonicalPairMinimumEndpointSupportRankHandoff.exists_other_endpointDebtIncrease_div_three`
   in `CanonicalPairMinimumEndpointRenewal.lean`.
5. `abs_quittingTerminalSemanticDebt_sub_le_of_forall_deviationGain_abs_le`
   passes a uniform full-behavior deviation-gain comparison to the associated
   debt coordinates.  Together with exact source and full-replacement
   convergence, it proves
   `FullReplacementCluster.not_hasVanishingHorizontalDeviationLeak_of_minimumFiber`;
   every recursive descent re-exports that impossibility as
   `FinFourRenewableSupportDescent.not_hasVanishingHorizontalDeviationLeak`.
6. `Research/Quitting/FinFourProducerAtlas/`
   `CanonicalPairMinimumEndpointRenewal.lean` exposes the structural output as
   `exists_renewalTerminalExit`,
   `exists_renewalTerminalExit_sameResidual`, and
   `consume_renewalTerminalExit`.  The conditional capstone
   `exists_uniformEquilibriumPayoff_of_renewalExitConsumers` clearly requires
   downstream consumers for all three residual alternatives; it is not an
   unconditional uniform-equilibrium theorem.

Evidence seals:

- **M:** PASS.  The compact joint-law lifts, source-faithful causalizations,
  exhaustive dispatch, strict finite-support recursion, exact Fin4 height and
  descent bound, signed debt transfer, and uniform deviation-gain no-go match
  the reviewed statement.  The initial support need not compare with the
  incoming support: the incoming state has fixed rank six and cannot recur.
- **L:** PASS.  The Research dependency closure and umbrella build.  Direct
  axiom probes for the debt Lipschitz theorem, horizontal no-go, one-third
  transfer, well-founded rank, three-descent bound, same-residual certificate,
  and initial handoff transfer report only `propext`, `Classical.choice`, and
  `Quot.sound`.  These Research declarations are outside the production
  `AxiomAudit.lean` scope and are not represented as production integration.
- **A:** PASS for the stated canonical branch.  The initial adapter consumes
  the actual `CanonicalPairMinimumEndpointSupportRankHandoff packet` and its
  coherent endpoint packet.  Each recursive adapter uses the current node's
  literal full-replacement profiles, compactifies only a strict subsequence,
  and rebuilds its own complete source with the unchanged hard residual.  No
  unrelated minimum law, profile family, or conclusion-equivalent rank
  certificate is supplied.
- **C:** PASS for the claimed structural reduction.  The minimum-fibre child
  is consumed recursively until one of positive total slope, flat support
  entry, or an off-minimum paid first-disagreement endpoint is returned with
  the same residual.  `consume_renewalTerminalExit` eliminates that output
  into any source-independent downstream proposition.  This is not terminal
  `C`: none of the three residual exits is unconditionally consumed into a
  terminal approximation or uniform-equilibrium payoff.

Validation at revision `12525820b822ba804ed41e5b4d519e4ade098efc`
included the documentation gate, 109 script unit tests, execution of all 33
registered experiments, import-graph, proof-duplicate, reward-bound,
redundant-order, derivable-telescope, and trust checks, and a full
`lake build` of 11,078 jobs.

Nonclaims:

- the theorem applies to the actual canonical minimum-endpoint handoff branch,
  not every Fin4 source or every branch of the producer atlas;
- the three structural exits remain genuine downstream obligations;
- no response comparison is transported backward across a replacement seam;
  rather, the uniform uncharged comparison of every nonmover behavioral
  deviation gain is proved impossible;
- the debt no-go does not rule out closeness of prescribed payoffs, raw cap
  vectors, or envelopes separately;
- no theorem gives a positive admissible near-return, terminal approximate
  Nash profile, uniform-equilibrium payoff, contradiction, or counterexample;
  and
- the result supersedes the former one-time canonical support-handoff boundary
  only on its minimum-fibre branch.  It does not make the branch-global Fin4
  uniform-existence conclusion unconditional.
