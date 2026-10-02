# Independent review: finite support premium peeling

Reviewer: CODEX_HILBERT.

Verdict: PASS for the complete frozen ordinary-mathematical surface. No
mathematical repair is required. The source comparison identifies a useful
shorter existing conditional consumer, not an already named unconditional
production theorem covering this raw-table condition.

Reviewed in full:

- `notes/CODEX_FRECHET_CYCLE__FINITE_SUPPORT_QUIT_PREMIUM_PEELING.md`,
  SHA-256 `aff6930efa2be95f654de9097482763fd6103780ff55c09a7059e1491514f329`;
- its preceding one-exception proof,
  `notes/CODEX_FRECHET_CYCLE__ONE_EXCEPTIONAL_POSITIVE_QUIT_PREMIUM_BOUNDARY.md`,
  SHA-256 `d182917435daf185556e05f5105f2b698698039d8fe735be19b130e9779741b1`.

This review independently checked the proofs and original/named sources.
It does not certify a Lean build or the subsequent assembled export surface.

## 1. Exact mathematical scope checked

On a finite nonempty player set, own premiums are nonnegative. Every
nonempty active set A must contain an i whose own premium vanishes at every
coalition i∈S⊆A. The author proves this finite test equivalent to an
elimination ordering, and equivalent to the assertion that every positively
absorbing exact root has a successor on the singleton lower boundary in
every padded reward cube. Root statements permit signed own singletons.

For nonnegative own singletons in Fin4 the author additionally derives
semantic P=s, excludes every C¹ exact-root unit-drift function, and obtains
all-accuracy, arbitrary-charge weighted packets in one fixed box. The
existing full-behavior packet consumer then supplies one fixed uniform
payoff. No global positive-gap premise, supplied tail, or favorable selected
root is assumed.

## 2. Adversarial proof checks

The elimination ordering is genuinely a coalition condition. The earliest
member of any nonempty active support has no premium at any possible Quit
coalition in that support. This gives its endpoint Q_i=s_i and, by positive
Quit support in an exact root, its successor payoff s_i. Every other
successor coordinate is at least its singleton because all Quit endpoints
are at least the singleton. Sure quitters and inactive coordinates cause no
exception.

For the converse, if the condition fails on A, taking all active hazards
equal to small t gives Q_i>s_i for each i∈A. The assigned continuations
v_i=(Q_i−G_i)/α_i genuinely lie in the padded cube for sufficiently small
t because they tend to s_i. All α_i are positive. Inactive players at
continuation B strictly prefer Continue: its endpoint tends to B, whereas
their Quit endpoint tends to s_i<B. A common sufficiently small t exists
because there are finitely many coordinates. Their successor payoffs are
also strictly above s_i. This supplies an exact counterexample to the
common-boundary property in every stated padded box, not a counterexample
to equilibrium existence.

At a minimizer of H on the lower boundary, the unique-binding case uses
the ACTUAL off-owner difference

    (1−t)(x_j−s_j)+t[r_j({i})−r_j({i,j})].

It remains positive for small t even with arbitrary positive pair premiums
or signed passive rewards. The proof does not incorrectly freeze an
exceptional player's Quit endpoint. The several-binding case uses only
legal upward boundary variations to infer nonnegative partial derivatives;
then a small simultaneous downward change leaves the large cube, not the
source lower orthant, as the only required constraint. Exact root existence
and the all-root boundary property give absorption at least ε/(M+B).
The resulting derivative contradiction has the correct sign.

One player is covered by the unique-binding argument. Zero reward bounds
in the root theorem cause no division problem since B>M≥0. The semantic
part separately chooses M>0. All-zero own singletons also yield the stated
direct all-Never exact equilibrium. The two-exception and negative-premium
fixtures were checked at every player's Quit/Continue endpoints; both
falsify precisely the claimed boundary implication, and neither is
misrepresented as a no-equilibrium table.

## 3. Semantic composition checked

Immediate Quit guarantees at least s_i against every opponent law under
nonnegative own premiums. All-Never opponents give unrestricted cap
max(s_i,0). Thus P_i=s_i for s_i≥0, independently of any attainment of the
punishment infimum. This conclusion requires neither the peeling condition
nor a positive singleton.

If a tolerance δ had finite free-start weighted capacity in radius M+2,
the capacity at ε=min(δ,1) would also be finite. The reviewed separator with
inner radius M+1 produces a polynomial drifting on every inner exact edge.
The all-root C¹ contradiction applies in that strictly padded inner cube.
Therefore capacity is infinite at EVERY tolerance in ONE fixed box. This
is enough for every finite charge target; no infinite path is inferred.

The exact production declarations inspected are:

- `hasFloorFreeAbsorptionWeightedFiniteForwardPackets_iff_weighted` in
  `UniformEquilibrium/Quitting/Projective/FloorFreeForwardPacketInputRemoval.lean`:
  same supplied box, positive reward bound, and normality;
- `quittingGame_exists_uniformEquilibriumPayoff_of_absorptionWeightedPackets`
  in `UniformEquilibrium/Quitting/Projective/AbsorptionWeightedForwardPacketProducer.lean`:
  positive box radius containing rewards and the all-accuracy/all-charge
  producer;
- the analytic separator in the frozen
  `math/exports/POLYNOMIAL_FORWARD_CERTIFICATES_WITHOUT_PUNISHMENT_FLOORS.md`,
  SHA-256 `14191a09b4a42149e0c893666603d85b2e2f1fb3bcd0240af0e0619aaeefc9d6`.

Radius M+2 satisfies the actual consumer's hypotheses. The result is a
fixed uniform target with unrestricted behavioral deviations, not merely
a root equilibrium or an approximate finite-menu equilibrium. The separate
sure-root branch need not be excluded. This Fin4 route is complete as
written, independently of the wider old-theory attachment below.

## 4. Existing-class coverage: distinguish three different assertions

No named production declaration explicitly stating the whole finite-support
peeling or one-exception class was located in the bounded source lookup.
This is not a claim of exhaustive literature novelty.

The zero-premium boundary is already mathematically covered by unit-solo
capped-exit theory plus small terminal perturbation and positive rescaling;
see the separate constant-own-reward review. A strict positive premium is
not removed by those transformations. Thus the raw weak-solo hypothesis
alone does not cover the enlarged class.

`QuittingAugmentedSoloPreemptionEdge` in
`Classification/Existence/AcyclicSoloPreemption.lean` uses passive singleton
entries r_j({i})<s_j. The peeling condition constrains own-member coalition
premiums and leaves those passive entries arbitrary. Choosing all passive
singletons below the respective own singleton yields cycles in both
directions while retaining any prescribed peeling pattern. Therefore the
existing augmented-preemption acyclicity theorem is not an automatic
consumer of this condition. This separates the hypotheses, not every old
existence class at once.

Other nearby inspected classes likewise carry additional hypotheses:
`SureExitChambers.lean` requires leaving/joining comparisons;
`SingleAnchorArbitraryCompletionEscape.lean` requires anchor-payoff
dominance over the anchor-excluding face; and
`Stationary/CoalitionToggleDeletion.lean` compares joining with passive
rewards. Arbitrary signed passive coordinates do not supply these premises.

There IS an older GENERIC conditional route. The original Solan–Vieille
paper's Proposition 2.2 assumes unit solos and existence, at every relevant
continuation, of an exact root which is all-Continue or has an active
quitter receiving at most 1. The new peeling condition supplies precisely
that hypothesis. Proposition 2.3 supplies periodic terminating
support-perfect rows against actual suffix payoffs. Proposition 2.4
supplies the nonlocal full-behavior extraction. The paper explicitly notes
that its capped-reward assumption is only sufficient for Proposition 2.2.

Original source directly inspected: Solan and Vieille, “Quitting Games,”
Mathematics of Operations Research 26(2), 265–285 (2001), printed
pp.269–274, especially p.270. Local primary PDF:
`literature/SOLAN_VIEILLE_2001__QUITTING_GAMES__JSTOR.pdf`.
The faithful declarations `proposition2_2`, `proposition2_3`, and
`proposition2_4` in `Literature/SolanAndVieille2001.lean` have the required
conditional scopes, but the literature lane is unbuilt.

Production's `quittingPeriodicPerfectSequenceSubgameExtraction_of_soloExitPreference`
in `Classification/Existence/PerfectSequenceExtraction.lean` already needs
only unit own singletons. Production's row and periodic generators in
`PerfectAbsorbingRow.lean` and `PerfectAbsorbingRootSequence.lean` still
expose capped-joint hypotheses rather than the weaker root-choice input.
The useful new project step is therefore an explicit raw-table producer
adapter to an old conditional consumer. It is not invalidated by the
consumer's age, but it must not be advertised as a new downstream existence
principle or an already integrated unconditional theorem.

The complete independent ordinary adapter, including generic finite-mesh
generation and the zero-Never perturbation/scaling quantifiers, is preserved
in
[HILBERT's adapter](../notes/CODEX_HILBERT__FINITE_PREMIUM_PEELING_SOLAN_VIEILLE_ADAPTER.md),
SHA-256 `48933b7ca0a0e321c8dfd38253f668d8e00f751b514d0a7282d5619560f68084`.
It gives arbitrary-finite-player coverage with nonnegative own singletons;
that separate extension has been sent for an independent review and is
not misrepresented as having received one merely because this feedback
accepts the author's Fin4 surface.

## 5. Final disposition

No unresolved mathematical objection to the two exact author hashes above.
The finite support criterion, its exact common-boundary characterization,
and its Fin4 consequence survive this independent falsification pass.
For final assembly, prefer the old conditional route if its separately
written all-player attachment passes review; retain the polynomial argument
as a distinct valid proof of its existing scope. A future Lean adapter must
produce the charged periodic sequence from table data, not add that sequence
as an unexplained supplied field.
