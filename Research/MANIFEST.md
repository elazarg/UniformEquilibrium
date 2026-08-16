# Research manifest

`Research.lean` is the explicit umbrella for compileable, not-yet-promoted
Lean research. Ordinary compileable modules are reachable from that umbrella;
intentional exceptions are documented below.

- general mathematical prototypes are under `Research/General/`;
- game-free semantic accounts are under `Research/Semantics/`;
- quitting-game investigations are under `Research/Quitting/`; and
- coordinated finite counterexample studies are under
  `Research/Counterexamples/`.

The period-eleven conditional compiler and parameterized semantic/checker
interfaces live under `Research/Quitting/BlockPair/K11/`. Its local manifest
defines the maintained trust boundary and admission rule.

Research modules may use canonical production declarations through narrow
direct imports. They do not recreate those declarations or preserve
forwarding-only module shims.

Research modules preserve their declarations and namespaces so that proofs
can be reviewed and promoted without an API translation layer. Imports must
remain within the project or point to trusted production/math
libraries; research code is never imported by production umbrellas.

Promotion requires a reviewed theorem interface, kernel-checked proofs, and
appropriate placement in `UniformEquilibrium`, `MathUE`, or the shared
`GameTheory` library. Forwarding-only shims, files outside the dependency
boundary, and files that violate the trust policy are not Research modules.
