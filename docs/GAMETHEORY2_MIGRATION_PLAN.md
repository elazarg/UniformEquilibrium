# GameTheory2 migration plan

This is the living engineering plan for eventually replacing the pinned
`GameTheory/` dependency with the canonical `v2` development. It records target
architecture and acceptance gates, not a chronology of inspected commits. It
does not authorize the cutover, a second simultaneous dependency, or a
compatibility fork. The current tree must continue to build against the pinned
v1 dependency until a separate cutover decision is made.

## Reproducibility gate

The canonical `v2` branch is published at the existing GameTheory remote, but a
moving branch is not a dependency pin. Before any dependency edit:

1. select one immutable reviewed `v2` commit;
2. verify its Lean, Mathlib, and auxiliary dependency revisions against this
   project;
3. build it from a clean clone using its architecture audits; and
4. record the immutable commit in the actual gitlink/manifest change.

Do not edit the manifest merely to follow an auxiliary dependency revision.
Toolchain, fixed-point, and manifest changes arrive together with the real
cutover and its required `lake update`.

## Compatibility census

Treat the successor as source-incompatible. Its design does not preserve the
v1 module graph or declaration names, and similarly named objects do not imply
compatible types. Regenerate a machine-readable direct-import and external-
declaration census from the tree immediately before any port; do not preserve
an old measured count in this living plan.

The project depends pervasively on v1 `StochasticGame`, PMF histories,
behavioral profiles, quitting roots, asymptotic calculus, and Fink interfaces.
The game-facing `QuittingRewardAdapter` also directly uses the v1 reward
carrier. That edge belongs at the semantic adapter boundary and is not a reason
to move game semantics into `MathUE`.

The replacement is therefore a semantic port, not a module rename. Delete
obsolete structure fields only as part of a checked vertical slice; simple
literal changes do not validate the surrounding play semantics.

## Semantic differences that control the plan

| Concern | Pinned GameTheory | Inspected GameTheory2 | Migration consequence |
| --- | --- | --- | --- |
| Game carrier | `StochasticGame` stores `State`, `Act`, PMF transition, stage payoff, discount, and discount proofs | `GameTheory.Stochastic.Game` stores `State`, `Action`, `FinDist` transition, and stage utility | Literal field changes are easy; dependent APIs must be rewritten |
| Finite laws | Public Mathlib `PMF` and `pmfPi` calculus | Public `FinDist` API; its `pmfPi` representation is private and `pi` is public | Do not apply a textual `PMF` to `FinDist` substitution |
| Histories | `Fin t`-indexed chronological records plus current state | Protocol execution with reverse-chronological `List StageRecord` public history | Prove an exact history/law bridge or keep a proved local proof-facing view |
| Behavior | Initial-state-independent behavior profiles over every finite history | Protocol profiles indexed in their type by the chosen initial state | Profile adapters must carry the initial state and prove runner equivalence |
| Uniform payoff | Project-used v1 finite-horizon uniform quantifiers | `Stochastic.Game.IsUniformEquilibriumPayoff` over canonical Protocol horizons | Reuse the successor predicate; do not fork the solution concept |
| Quitting games | Dedicated game, root, asymptotic, perturbation, punishment, and closure APIs | No quitting module | Quitting semantics must become project-owned above the successor core |
| Discounted Fink | Legacy PMF/kernel/simplex stack | Successor-native `FinDist`, `UtilityGame`, and canonical mixed-Nash construction in `Analysis.Stochastic.Fink` | Rewrite certificates against the new theorem; aliases are not credible |

The uniform-payoff definitions have the same essential contract: for every
positive error, choose one profile and one threshold that work for every later
finite horizon, while approximating one fixed target payoff. This is the
semantic anchor for the port. Equivalence still needs a checked bridge between
the two concrete history runners; matching prose or quantifier order is not a
proof.

GameTheory2 deliberately hides the PMF representation of `FinDist`. Generic
countable-probability mathematics that is genuinely useful outside finite
games may remain Mathlib-PMF-based in `MathUE`. Finite stochastic semantics
should use `FinDist` through its public `pure`, `map`, `bind`, `pi`, `prob`, and
`expect` interface. A theorem belongs in `GameTheoryMath` only when the
successor project accepts ownership; otherwise project-specific generic work
remains in `MathUE`.

The successor's experimental `PostArchitecture.StochasticProofView` is useful
as a specification: it provides proof-facing public-history policies, profile
round trips, one-step runner exposure, and compatibility with unilateral
profile update. It is not a production migration waist. In particular it does
not provide the v1 indexed-history correspondence, generic finite-horizon law
and payoff equality, or the canonical uniform-payoff bridge, and its hostile
fixture does not exercise action-dependent transitions. Production code must
not import the experimental module. Reuse its design only through a promoted
stable successor interface or a project-owned facade over public v2 APIs.

## Target dependency shape

The intended post-cutover dependency direction is:

```text
GameTheory2 Stochastic.Game + FinDist + Protocol
                         |
                         v
project-owned stochastic proof facade with proved runner/law equivalence
                         |
                         v
UniformEquilibrium.Quitting.Foundation
                         |
                         v
quitting paths, compilers, certificates, diagnostics, and headline theorems
```

The facade is not a namespace-preserving copy of v1. It may retain a
proof-friendly indexed-history view only if it proves exact finite-history law
and payoff equivalence to the canonical Protocol runner. The canonical public
uniform-payoff conclusion remains GameTheory2's predicate.

Quitting-specific definitions belong under
`UniformEquilibrium.Quitting.Foundation`, not `MathUE` and not a vendored
legacy `GameTheory` namespace. Generic PMF lemmas remain in `MathUE`; finite-law
lemmas should be restated over `FinDist` only when a real successor-facing
consumer exists.

## Staged execution plan

### 0. Select a reproducible successor pin

Select a reviewed immutable commit from the canonical `v2` branch, verify a
clean clone, and record its build and architecture-audit commands. No gitlink
or Lake change precedes this gate.

### 1. Freeze a machine-readable v1 surface census

While the current dependency still builds, record direct module imports,
external declaration references, and representative semantic consumers. Add
small regression fixtures for history laws, finite-horizon payoff, unilateral
profile update, stationary profiles, and the uniform-payoff quantifiers. The
census is a migration worklist, not an API preservation promise.

### 2. Triage generic mathematics

For every used legacy `Math.*` declaration, choose exactly one owner:

1. existing Mathlib theorem;
2. existing successor `GameTheoryMath` or public `FinDist` theorem;
3. genuinely project-owned generic theorem in `MathUE`; or
4. delete it with its obsolete consumer.

Do not vendor the legacy generic-mathematics tree wholesale. Port narrow
leaves only after a live consumer identifies their needed statement.

### 3. Prove one stochastic semantic waist

Construct a project facade over successor `Stochastic.Game`, `FinDist`, and
perfect monitoring. Prove, for one finite horizon:

- correspondence of chronological indexed and Protocol list histories;
- equality of joint-action and next-state laws;
- equality of finite-average payoff;
- correspondence of unilateral profile update; and
- equivalence of the project's proof-facing uniform constructor with the
  canonical successor uniform-payoff predicate.

This phase must use a nontrivial action-dependent transition fixture and a
profitable-deviation control. Definitional equality on a constant game is not
adequate evidence.

### 4. Rebuild the quitting foundation above the waist

Move the Boolean Continue/Quit carrier, terminal reward, coalition law, root
payoffs, stationary formulas, and asymptotic finite-horizon interfaces into the
project-owned quitting foundation. Port them to the facade and prove that the
concrete quitting game compiles to successor stochastic semantics.

The critical vertical slice is: one quitting game, one behavioral profile, one
unilateral deviation, one terminal payoff equality, and one theorem concluding
the canonical successor uniform-payoff predicate.

### 5. Port by dependency depth

After the vertical slice is green, port in this order:

1. quitting root and finite-horizon calculus;
2. path/profile and asymptotic interfaces;
3. projective, punishment, and certificate compilers;
4. special-case and diagnostic consumers;
5. static/repeated/zero-sum APIs already redesigned in GameTheory2; and
6. vanishing-discount and Fink consumers against successor-native
   `Analysis.Stochastic.Fink`.

Each package must remove a v1 dependency edge and add a checked successor
consumer. Thin name aliases are acceptable only for genuinely identical
nonsemantic leaves, never for histories, profiles, laws, or equilibrium
predicates.

### 6. Cut the dependency once

Change the submodule, `lakefile.lean`, and manifest only after the vertical
slice and its semantic regression fixtures pass. At that point run
`lake update`, `lake exe cache get`, the successor architecture audits, the
project trust/docs/import checks, and a full `lake build`.

Do not import v1 and v2 together: they share broad public namespaces and would
make declaration ownership ambiguous. A namespace-renamed v1 fork duplicates
semantics and is reserved only as an explicitly time-boxed emergency scaffold,
not as the migration architecture.

## Per-phase acceptance gates

Every migration package must provide:

- an exact old-consumer inventory and new owner;
- at least one positive semantic fixture and one hostile control;
- narrow source and named-module builds;
- no new v1 import outside the shrinking compatibility boundary;
- no private `FinDist.toPMF` representation dependency;
- unchanged uniform-payoff quantifiers, proved through the canonical predicate;
- current generated axiom audit, trust scan, docs, and import graph; and
- a full build for dependency, manifest, umbrella, or semantic-waist changes.

The migration is complete only when the v1 gitlink is gone, all project-owned
modules build from a clean clone against the published successor pin, and the
semantic bridge tests and exhaustive axiom audit are nonvacuous. Until then,
status reports must say which slice has been ported and must not describe the
repository as migrated.
