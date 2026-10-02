# Intervention-preserving reductions and a sector obstruction for UE

Author: CODEX_LARCH. UniformEquilibrium research note, 2026-09-07.

## Scope and mathematical question

This note concerns possible mathematical imports into UniformEquilibrium.
Its external motivation is a supplied sketch from GoC, a separate,
independently developed project. The relevant idea is to describe a process
through its responses to interventions and ask when several projected
descriptions belong to one realizable process. No knowledge of GoC is needed
below, and this note neither documents that project nor recommends its scope
or research priorities.

For UE, the question is whether compression or decomposition preserves one
system of independent behavioral strategies and its unrestricted unilateral
responses. In a quitting game, players independently choose stopping laws;
the first quitting date and tied coalition determine terminal rewards. A
player's cap is the supremum of its expected terminal reward over every
replacement of its own strategy, with opponents fixed. Maximal terminal
exploitability is the largest cap minus prescribed payoff across players.

This note records a finite exact obstruction, two narrow theorem targets,
and relevant comparisons. It is ordinary mathematics, not Lean-checked
or exported. CODEX_LARCH_DUAL independently checked the two-state MDP example
and its all-action interpretation. The proposed UE applications remain
conditional research directions, not independently established producers.

## 1. An exact obstruction already at the MDP level

There are two live states and a killing cemetery. Actions A and B have
substochastic matrices on the live states

    A = [[1,0],[0,0]],       B = [[0,1],[1,0]].

A stays at state 1 and kills at state 2; B swaps the live states. At each
state the controller may independently choose either row. Consider common
nonnegative superharmonic certificates

    C = {u≥0 : Au≤u and Bu≤u}.

The B inequalities imply u₁=u₂, so C is exactly the ray t(1,1), t≥0.
These same inequalities control every deterministic rowwise policy and
every randomized policy. In particular u=(1,1) generates an extreme ray
of the all-action certificate cone.

For the fixed A policy, its harmonic/potential decomposition is

    h = lim_n Aⁿu = (1,0),
    p = u−h = (0,1) = Σ_(n≥0) Aⁿ(u−Au).

This is an actual harmonic/potential split, not merely a partition of path
labels. But Bh=(0,1) is not ≤h, and Bp=(1,0) is not ≤p. Neither component
remains in the common certificate cone.

Thus an extreme common certificate can be mixed relative to one policy's
conservative/potential sectors. B exchanges those sectors. There is no
contradiction with sector purity under constraint-preserving projections:
that is exactly the hypothesis which fails. Nor is this a decomposition
inside C; it leaves C, which is the point of the example.

### A precise sufficient condition to investigate

For a finite fixed substochastic kernel K and finite nonnegative u with
Ku≤u, the elementary Riesz calculation gives

    h=lim_n Kⁿu,       p=Σ_(n≥0)Kⁿ(u−Ku),       u=h+p.

The identity follows by telescoping and monotone convergence. To extend
this to common controlled certificates, seek positive linear complementary
projections H,P with H+P=I that map the common certificate cone into itself
and identify the intended sectors. Then every extreme ray must lie wholly
in one projection's range. The abstract extreme-ray implication is short;
constructing meaningful common projections is the substantive task.

A restrictive sufficient mechanism is that both positive complementary
projections commute with every admissible transition operator. This
preserves all their superharmonic inequalities. Many useful Riesz
decompositions are not represented by globally positive complementary
projections on the whole ambient space, so this is a testable special case,
not a universal characterization. Weaker cone-preservation conditions may be
more appropriate. For UE, any proposed decomposition of controlled
certificates should first survive this small MDP calibration, then retain
the same opponents and source strategies across all deviation tests.

## 2. Common realization must retain the right model

For the proposed UE application, distinguish two lifting questions:

1. a common probability law satisfying marginal constraints;
2. a common independent-controller process satisfying information and
   factorization constraints.

Solving the first does not solve the second. Independent behavioral
realizability and compatibility under deviations are essential additional
requirements. A convex relaxation must not silently replace them by shared
randomization or by separate source profiles for different tests.

The repository already records joint counterfactual data in
[the full replacement-kernel atlas](../ideas/CONTINUATION_GAME_STATE/FULL_REPLACEMENT_KERNEL_ATLAS.md).
It is algebraically closed under fixed replacements, but moving replacements
at escaping deadlines expose a joint-limit defect. Moreover, a sequence of
horizontal strategy replacements is not a chronology of reached histories.
Keeping all counterfactual coordinates alone does not solve either problem.

The bounded target is a realization/completion theorem for the exact family
of contexts used by one consumer, including compatibility after its next
replacement. A finite obstruction or a required third-order response
coordinate would be useful; storing the answer to every possible future
query would mostly repackage the original problem.

## 3. Recovery, safe repair, and operational distance

Fix one intervention family T and let μ_P(τ) be the terminal law of a
candidate independent profile P under intervention τ. Include prescribed
play and every unilateral behavioral replacement when those are the required
semantics. Define the operational discrepancy

    d_T(P,Q)=sup_(τ∈T) TV(μ_P(τ),μ_Q(τ)).

If d_T≤δ and rewards are bounded by M, prescribed payoffs and full unilateral
caps differ by at most 2Mδ, and maximal exploitability differs by at most
4Mδ. These elementary inequalities are not the desired new theorem. The
useful theorem would construct Q from small compressed data and bound this
supremum using a tractable certificate.

One actual realization Q must work for all τ. Constructing a different Q_τ
for every test does not satisfy the statement. Composition additionally
needs the test family to be stable under pulling tests through the permitted
attached continuations. Otherwise a locally small discrepancy can become
visible after composition.

Two existing research sketches illustrate distinct conclusions:

- [Boolean support repair](CODEX_LARCH_GEOMETRY__BOOLEAN_CONSTRAINT_REPAIR_UNDER_INTERVENTIONS.md)
  compares one actual source to a simpler root with uniform unilateral cap
  control. Its same-date coupling controls intervention laws; later retiming
  preserves cap values but reindexes deadline tests. It therefore requires
  that reindexing if stated as an operational comparison after compression.
- [Finite dated-law completion](CODEX_LARCH_DUAL__COMPETING_RISKS_CAP_FIBERS.md)
  generally cannot reconstruct the original hidden cap. It selects a
  cap-minimizing realization in the same observable fiber. This is safe
  strategic repair, not recovery of every original counterfactual response.

A UE interface for these fibers should keep recovery and optimization
within a fiber separate. That distinction prevents an apparent reconstruction
theorem from silently changing the system being reconstructed.

## 4. Boundary directions need an operational test

A vanishing unnormalized branch can retain a nontrivial conditional law or
projective direction. Its significance depends on the allowed tests. If all
tests retain the branch's small probability, bounded-payoff effects vanish.
If a permitted intervention removes the censoring event, that same hidden
continuation can affect a cap by an order-one amount.

This is why a direction over zero mass can matter strategically without
being assigned fictitious positive unconditional mass. A useful boundary
compactification must show that its additional coordinates control these
tests or admit common-realization constraints. Retaining every conceivable
direction without such a consumer is not yet a reduction.

## 5. External comparisons relevant to the UE questions

**Compatibility obstructions.** Abramsky and Brandenburger's
[sheaf-theoretic contextuality framework](https://arxiv.org/abs/1102.0264)
expresses contextuality as failure of global sections. This suggests looking
for explicit compatibility obstructions, but supplies no quitting-game
realization theorem. Independent product strategies and retention of one
actual source remain additional constraints in the UE problem.

**Operational distinguishability.** Gutoski's
[distance for quantum strategies](https://arxiv.org/abs/1008.4636) measures
distinguishability of interactive quantum strategies. This is a close
precedent for measuring discrepancies by all permitted interactions rather
than only unperturbed state distributions. The elementary terminal-law
comparison in Section 3 is the concrete classical interface considered here;
no quantum-strategy theorem is being applied to UE without an adapter.

## Next UE-facing questions

1. For one proposed decomposition of a UE controlled certificate, identify
   its certificate cone and test whether the sector maps preserve all
   deviation inequalities on the same source. Use the two-state MDP example
   to reject policy-specific splitting presented as a common decomposition.
2. For one existing quitting consumer, find the smallest response family closed under
   its actual operations and prove either common approximate recovery or a
   canonical cap-improving lift. Include the existing zero-mass and
   moving-deadline falsifiers from the outset.

The acceptance criterion is a new UE adapter, a sharper obstruction, or a
reduction of a named consumer's hypotheses. A general response formalism
without one of those consequences would not advance this project's task.
