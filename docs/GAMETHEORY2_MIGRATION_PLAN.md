# GameTheory2 migration plan

This document records the engineering plan for eventually replacing the pinned
`GameTheory/` dependency with the current GameTheory2 development. It does not
authorize that cutover, a second simultaneous dependency, or a compatibility
fork. The present engineering roadmap may prepare boundaries and tests, but it
must continue to build against the pinned v1 dependency until a separate
cutover decision is made.

## Current reproducibility gate

The audited dependency snapshots are:

| Item | Audited value |
| --- | --- |
| Current pinned GameTheory gitlink | `02898a2d8b918f9b106a683420ca78c99867560e` |
| Locally inspected GameTheory2 head | `8464fd300683eca4163fc6a7b1710ad26d1861d6` |
| Lean toolchain | `v4.32.2` in both trees |
| Mathlib revision | `905b95818eb32af7874a58b427f50c1711a5e96c` in both manifests |
| Current fixed-point dependency | nested gitlink `6839b05aad04d5a10a8062d9e8b2ee3c4abd92f7` |
| GameTheory2 fixed-point dependency | git revision `9571dd7e0ff0af9c9e9becb2738a309cf48387c1` |

The inspected GameTheory2 checkout has no configured remote. That is a hard
operational blocker: the repository cannot record a reproducible submodule URL
and another checkout cannot fetch the inspected commit. Before any dependency
edit, GameTheory2 needs a canonical published remote, an immutable reviewed
commit, and a successful clean-clone build at that commit.

The shared Lean and Mathlib versions remove one source of migration noise. The
fixed-point revision change does not justify an early manifest edit; it should
arrive with the actual dependency cutover and its required `lake update`.

## Compatibility census

This is a source-architecture census, not a claim that similarly named
declarations have compatible types.

- The current dependency has 484 modules below its `GameTheory/` and `Math/`
  source roots; the inspected successor has 344 below `GameTheory/` and
  `GameTheoryMath/`. Only 18 module names coincide.
- This project directly imports 56 distinct dependency modules. None exists at
  the same module path in the inspected successor.
- The additional direct edge is `GameTheory.Basic`, imported by the
  game-facing `UniformEquilibrium.Quitting.Classification.LCP.QuittingRewardAdapter`.
  It supplies the v1 reward carrier at the semantic adapter boundary; it is
  not a reason to move game semantics into the generic `MathUE` lane.
- Lexical reach indicators across `MathUE`, `UniformEquilibrium`, `Research`,
  and `Theorems` find `StochasticGame` in 589 files, `BehaviorProfile` in 382,
  `.Act` in 254, `PMF` in 739, and `quittingGame` in 398. The `.Act` and `PMF`
  scans use identifier boundaries. These counts include comments and
  declaration sites; they measure migration breadth, not API usage precisely.
- There are 22 inspected `StochasticGame` structure literals in 21 files. All
  store discount zero, so deleting the obsolete discount fields is mechanical;
  their surrounding play semantics are not.

The successor's own `V1CapabilityMap.md` explicitly describes it as
source-incompatible. Its design rejects declaration-for-declaration ports and
compatibility aliases in favor of successor-native owners. The replacement is
therefore a semantic port, not a module rename.

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

### 0. Make the dependency fetchable

Publish GameTheory2 at a canonical remote, select a reviewed commit, verify a
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

Do not vendor the legacy `Math/` tree wholesale. Port narrow leaves only after
a live consumer identifies their needed statement.

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
