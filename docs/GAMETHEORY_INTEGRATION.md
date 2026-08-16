# GameTheory integration

`GameTheory/` is the pinned foundational dependency for finite games,
finite-support stochastic execution, and the canonical native
uniform-equilibrium predicate. Project-owned mathematical extensions live in
`MathUE/`; quitting-game semantics and research results live in
`UniformEquilibrium/`.

## Semantic boundary

The project uses two proved views of the same finite stochastic execution:

- GameTheory's native `Stochastic.Game`, `FinDist`, Protocol history, and
  initial-state-indexed behavioral-policy interfaces; and
- the indexed PMF proof view under `UniformEquilibrium/ProofView/Concepts/`.

`UniformEquilibrium/ProofView/Native/` is the semantic boundary between them.
Its history maps are exact on coherent public histories. Its execution theorem
identifies the compiled finite law with the native Protocol runner. Its payoff
and unilateral-update theorems feed the exact equivalence
`isUniformEquilibriumPayoff_toNative_iff`.

The proof view is a mathematical interface, not an alternative solution
concept. Conclusions crossing the boundary use GameTheory's native predicate.

## Ownership rules

- Use GameTheory declarations directly when their public statement fits.
- Put game-independent project mathematics in `MathUE/`.
- Keep `MathUE/` independent of game-semantic `GameTheory.*` modules.
- Put Boolean Continue/Quit games, terminal rewards, roots, paths, and
  compilers in `UniformEquilibrium/Quitting/`.
- Do not depend on private `FinDist` representations. Use public operations such
  as `pure`, `map`, `bind`, `pi`, `prob`, and `expect`.
- Do not duplicate GameTheory foundations merely to obtain preferred names or
  proof syntax.

An interface belongs upstream in GameTheory when it is useful for finite games
independently of this project's quitting-game program. Project-specific
adapters stay here even when their implementation is generic Lean.

## Dependency and verification contract

The gitlink identifies the exact GameTheory revision. A dependency-pin,
toolchain, Lake, semantic-boundary, or umbrella change requires:

1. focused checks of each changed owner and representative consumer;
2. the documentation, import-graph, trust, duplicate-proof, and telescope
   gates;
3. regeneration of `AxiomAudit.lean` when the module inventory changes; and
4. a full `lake build`.

The native bridge must cover finite-history laws, finite-average payoffs,
unilateral profile updates, and the fixed-target uniform-payoff quantifiers. A
constant-transition fixture alone is insufficient evidence for changes to this
boundary; action-dependent transitions and a profitable deviation must remain
covered.
