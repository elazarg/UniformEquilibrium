# Research

This directory contains reusable, human-maintained Lean declarations, checkers,
and interfaces whose relevance, ownership, or generality is not yet settled.
Their meaning must survive replacing or deleting any particular experimental
instance. Files follow the repository trust policy even when they are orphaned
from the integrated umbrella.

Research modules must not import `Experiments`; the static import-graph check
enforces this lane boundary. Concrete run inputs and outputs, generated
payloads, reports, caches, logs, and raw runs are not Research records.

Promote accepted game-semantic results to `UniformEquilibrium` and accepted
game-independent results to `MathUE` or GameTheory's shared `Math` library.
