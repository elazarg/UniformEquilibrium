# Integrated formal development

This directory contains the integrated game-semantic line of the uniform-
equilibrium research project. Its modules define stochastic-game
constructions, certificates, examples, diagnostics, special cases, and open
existence statements. Integration means that the material is checked and part
of the active formal theory; it does not promise an externally stable API.

Open claims are proposition definitions. They become theorem declarations only
when a kernel-checked proof is available; production contains no placeholder or
axiom-backed proofs.

## Main areas

- `Architectures/` packages reusable strategy and response architectures.
- `Certificates/` contains sufficient conditions and their compilers.
- `Conjecture/` states general open claims as definitions.
- `Diagnostics/` records proved obstructions, separations, and consequences.
- `Examples/` contains canonical stochastic-game examples.
- `Quitting/` contains the main finite-quitting program.
- `SpecialCases/` proves structured positive results.
- `VanishingDiscount/` develops discounted limits and analytic obstructions.

Use [the toolkit](../docs/TOOLKIT.md) to select an interface by mathematical
role. Internal modules import narrow dependencies; `import UniformEquilibrium`
loads the whole integrated development for navigation and project-wide checks.
