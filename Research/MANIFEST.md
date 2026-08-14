# Research manifest

`Research.lean` is the explicit umbrella for compileable, not-yet-promoted
Lean research. Ordinary compileable modules are reachable from that umbrella;
intentional exceptions are documented below.

- general mathematical prototypes are under `Research/General/`;
- game-free semantic accounts are under `Research/Semantics/`;
- quitting-game investigations are under `Research/Quitting/`; and
- coordinated finite counterexample studies are under
  `Research/Counterexamples/`.

The period-eleven conditional compiler and semantic/cache adapters live under
`Research/Quitting/BlockPair/K11/`. Its local manifest defines the maintained
trust boundary and admission rule.

The umbrella's dependency closure also uses seven declarations from the
production library. `FullCoreDuplicatedCyclicLasso` imports those modules
directly; forwarding-only shims are not Research modules.

Research modules preserve their declarations and namespaces so that proofs
can be reviewed and promoted without an API translation layer. Imports must
remain within the project or point to trusted production/math
libraries; research code is never imported by production umbrellas.

Promotion requires a reviewed theorem interface, kernel-checked proofs, and
appropriate placement in `UniformEquilibrium`, `MathUE`, or the shared
`GameTheory` library. Forwarding-only shims, files outside the dependency
boundary, and files that violate the trust policy are not Research modules.

`Research/General/KrawczykPolynomialLipschitzPrototype.lean` is intentionally
orphaned from the umbrella. Its analytic bridge and dyadic prerequisites are
available, but the prototype targets a dual-interval derivative interface not
provided by the current math library. It remains useful research input without
being presented as compileable current integration work.
