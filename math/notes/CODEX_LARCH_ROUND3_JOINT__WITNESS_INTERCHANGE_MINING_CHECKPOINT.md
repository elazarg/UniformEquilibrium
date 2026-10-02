# Witness interchange: bounded mining checkpoint

Author: CODEX_LARCH_JOINT. Research audit, 2026-09-07.

**Status: no new theory candidate nominated.** The bounded search found a
real recurring mathematical issue, but its useful positive mechanisms are
already explicit theories in the repository. The generic missing statement
would either be false or restate the common-witness obligation. This is a
negative mining result, not a proof that the larger codebase contains no
further abstraction. No Lean checking, Lean edits, export, or UE advance is
claimed here.

## 1. Question and search boundary

When do separately realizable certificates admit one shared underlying
parameter? When may existential witnesses be forgotten before composition?
Can distant declarations reveal a useful common-fiber theorem stronger than
the interfaces they already use?

The source fingerprints were quantifier order, common fixed profile,
universal opponent completion, explicit witness coordinates, equality of an
intermediate object, common order orientation, and restriction surjectivity.
This was not a proof-text or nearby-commit similarity search. The principal
comparison was between adaptive security/welfare assembly and compact ranked
adapter composition; narrower checks covered owner-separated potentials,
causal stopped dispatch, lattice gluing, finite compatibility, and inverse
limits. No multitubes investigation was performed.

The intended output would have been a reusable theorem with two concrete
instances, rather than a new hypothesis naming the unsolved application.

## 2. The exact algebraic obstruction

Let X be a set of actual witnesses, p : X → Y a reported observation, and
C_i ⊆ X a finite family of certificate constraints. Always

    p(⋂_i C_i) ⊆ ⋂_i p(C_i).

For a particular y, membership in the right side means

    ∀ i, ∃ x_i, p(x_i)=y and x_i∈C_i.

Membership in the left side means

    ∃ x, p(x)=y and ∀ i, x∈C_i.

Equality at y therefore holds exactly when the nonempty sets
`C_i ∩ p⁻¹{y}` have nonempty common intersection. This is an exact diagnostic,
but contributes no existence theorem by itself.

Three separate repairs would be needed for three separate losses:

1. **Witness compatibility:** retain or construct a common point of those
   fibers. Even convexity and pairwise compatibility do not suffice in
   arbitrary dimension. In ℝ², the three convex constraints x≥1, y≥1,
   x+y≤1 intersect pairwise but have empty total intersection.
2. **Model compatibility:** a convex combination must stay in the actual
   witness class. Half the product point mass at (0,0), plus half the product
   point mass at (1,1), is not a product law: its marginals each give 1/2 to
   both values, whose independent product gives positive off-diagonal mass.
3. **Composition compatibility:** an observation must preserve the relevant
   future attachment. Equal current observations need not remain equal after
   the same operation.

The first two examples are elementary falsifiers, not proposed new results.
The repository already contains stronger, application-specific versions of
all three warnings.

## 3. Distant instance A: robust coordinatewise witnesses already glue

`isUniformEquilibriumPayoff_of_oneSidedGuarantees_of_weightedWelfareCap`
(`UniformEquilibrium/Certificates/Adaptive/WeightedSecurityWelfareAssembly.lean`)
combines one security strategy for each player. Its decisive fingerprint is
that each chosen strategy guarantees its coordinate **against every opponent
completion**. Thus choosing the other players' strategies does not invalidate
the guarantee. A positive weighted welfare ceiling supplies the missing
upper bounds and deviation caps. This is a substantive positive gluing
mechanism already embodied in the theorem.

Its abstract product-domain calculation is short. For X=∏_i X_i and constraints
C_i⊆X, define the robust own-coordinate set

    S_i = {x_i : every x with this i-coordinate belongs to C_i}.

If each S_i is nonempty, every choice in ∏_i S_i belongs to ⋂_i C_i. This
uses the universal completion quantifier, not just nonemptiness of C_i.
Replacing it by `∀i ∃x∈C_i` is invalid even for singleton constraints in a
two-point common witness space.

There is a different valid assembly in
`OwnerSeparatedAdaptivePotentialData.toAdaptivePotentialSystemAt`
(`UniformEquilibrium/Certificates/Adaptive/OwnerSeparatedAdaptivePotentialSystem.lean`).
Every owner-specific certificate already uses the same fixed profile and
initial state. The constructor takes each owner's deviation-potential
coordinate, while preserving a common on-path certificate and explicitly
accounting for target mismatch. It does not glue separately chosen profiles.
Removing unused off-owner components of its input structure might simplify
an interface; the mathematical owner-coordinate separation is already stated
and used. It is not a missing common-profile theorem.

## 4. Distant instance B: composition already uses literal fiber products

`CompactRankedOutcomeAdapter.successorOutcomeDomain`
(`MathUE/Topology/CompactRankedOutcome.lean`) retains an actual successor edge,
its certificate, and a lower-level node/outcome pair. The last conjunct is
literal equality of the child node with the source of the lower outcome.
This is exactly the fiber product required for composition. The compactness
proof keeps the attachment equality closed in a Hausdorff node space before
projecting. The source then provides
`CompactRankedOutcomeAdapter.isCompact_successorOutcomeDomain`,
`CompactRankedOutcomeAdapter.isCompact_outcomeUpTo`, and
`CompactRankedOutcomeAdapter.projectedOutcomeSet_eq_outcomeUpTo`.

The one-step version is already packaged by `CompactProofRelevantAdapter`
and `CompactProofRelevantAdapter.isCompact_visibleSet`
(`MathUE/Topology/CompactProofRelevantAdapter.lean`). Its fields explicitly
require compact witness carriers, a closed legal relation, total legal
witnesses, and continuity on that relation. Merely having a witness for each
reported scalar would not satisfy these fields.

Static import inspection found no directed dependency path between
`WeightedSecurityWelfareAssembly` and `CompactRankedOutcome` in either
direction. The former directly imports invariant-weight mathematics and the
adaptive certificate; the latter directly imports general Mathlib topology.
They are genuinely different code neighborhoods. Their common diagnostic is
witness dependence, but their sufficient hypotheses do different work:
robust product choices in A; closed literal attachments in B. Replacing both
by an abstract relation intersection would erase the existence mechanisms
without strengthening either consumer.

## 5. Existing mathematical coverage and failure tests

The following exact declarations further narrow the missing-theory claim.

| Mechanism | Existing declaration and source | Why it matters here |
| --- | --- | --- |
| One common order | `exists_common_of_nonempty_of_upwardClosed`, `MathUE/ContinuationLatticeGluing.lean` | Joins separate witnesses because every constraint is upward closed in the same semilattice. The quantitative antitone-violation version is also present. |
| Signed linear compatibility | `exists_potential_iff_no_signed_incompatibility`, `MathUE/FiniteLinearCompatibility.lean` | Already gives a common-potential alternative rather than merely separate scalar feasibility. |
| Small convex obstruction | `exists_sparse_infeasible_branch_subsystem`, `MathUE/DirectedTransport/MaxAffine/Sparse.lean` | Already supplies the Helly-style sparse obstruction that a generic convex-fiber proposal would invoke. |
| Compatible infinite choices | `CompactSurjectiveTower.completeCodeSet_nonempty`, `MathUE/Topology/CompactSurjectiveInverseLimit.lean` | The tower records legal restrictions and surjective lifting, not just nonempty stages. |
| Actual conditional composition | `CausalDispatcherJointLawAt`, `UniformEquilibrium/Certificates/Public/CausalTerminalChildDispatcher.lean` | Records reconstruction and joint-law factorization for one actual profile. |

The causal consumer
`FiniteChildAdaptivePotentialFamily.deviation_stage_of_variableStoppedChildren`
(`UniformEquilibrium/Certificates/Public/VariableStoppingAdaptiveDispatcher.lean`)
uses restrictions of a single root deviation at stopped histories. Separate
child deviation witnesses would not constitute this disintegration. This
supports the audit's quantifier distinction, but is already an explicit
construction with an actual joint-law premise.

For an exact composition falsifier, inspect
`exists_terminalSemantic_commonWitness_noncompositionality`
(`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticCommonWitnessNoncompositionality.lean`).
Two profiles have equal terminal semantic pairs, equal joint survival, and
the same exact pure-time witness, while a common continuation splice changes
their caps differently. The source's `splicedP_envelope_owner` gives 2 and
`splicedQ_envelope_owner` gives 1+s; at s=1/2 the values are 2 and 3/2.
Their labelled deleted survivals differ. Adding the phrase “common witness”
to current scalar observations does not restore composition.

The compressed mathematical records confirm that this coverage is not just
scattered source boilerplate:

- [Executable adapter grammar and constrained-root no-go](../formalized/EXECUTABLE_ADAPTER_GRAMMAR_AND_CONSTRAINED_ROOT_NO_GO.md)
  already develops witness-retaining composition, projective compatibility,
  and a precise obstruction to enlarging the compact adapter class.
- [Finite-deadline Nash projective boundary and compatibility](../formalized/FINITE_DEADLINE_NASH_PROJECTIVE_BOUNDARY_AND_COMPATIBILITY.md)
  distinguishes separate finite equilibria from compatible selections and
  gives an actual quantitative adjacent-deadline criterion.
- [Adaptive unchanged-child extension no-go](../exports/ADAPTIVE_CHILD_EQUILIBRIUM_EXTENSION_NO_GO.md)
  rules out a universal extension that preserves the supplied child marginals,
  even when the parent game itself has an equilibrium.

The pre-existing
[common-realization note](CODEX_LARCH__GOC_COMMON_REALIZATION_AND_SECTOR_OBSTRUCTION.md)
already separates common probability laws from common independent-controller
realizations. Rephrasing the same distinction as a fiber theorem would not
meet this pass's novelty requirement. No competing-risk or rank-one
obstruction was developed again.

## 6. Disposition

Reject a new general “common witness theory” candidate on this evidence. The
promising abstractions were already present, and the universal strengthening
of separate feasibility is false. A junction-tree or acyclic relation-gluing
proposal would require actual overlapping local witness interfaces with a
verified acyclic incidence structure; this bounded search did not establish
two such consumers. It should not be proposed merely because the vocabulary
resembles these declarations.

One concrete reopening criterion is a source pair that shares **the same
nontrivial fiber-amalgamation hypothesis**, with each source rebuilding the
same existence mechanism and neither covered by the mechanisms above. That
would justify a common theorem. The current pair shares a failure mode, not
a missing positive theorem.

Verification here was a static source and hypothesis audit, exact elementary
counterexample checking, and a project import-graph path check. No compiler,
experiment, or external-source theorem was used. This checkpoint needs no
export and makes no claim about the UE frontier.
