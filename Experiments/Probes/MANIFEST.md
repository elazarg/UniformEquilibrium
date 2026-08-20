# Standalone experiment probes

These programs are bounded, standalone probes retained for research context;
they are not part of the registered `Experiments/Base` suite. Their outputs
are evidence about the stated finite computation only, not general theorems.

Run a probe directly from the repository root, for example:

```text
python Experiments/Probes/backward_absorption_gamma_eta.py
```

The current probes are:

- `backward_absorption_gamma_eta.py`: backward-absorption residual signatures
  for one perturbed period family;
- `harmonic_module_audit.py`: module-invariance and rebasing audit for
  endpoint-harmonic spans;
- `homotopy_germ_endgame.py`: numerical continuation and endgame screens for
  selected quitting-game weights;
- `owner_cokernel_typed_holonomy.py`: owner-indexed cokernel re-encoding of a
  typed two-cycle holonomy; and
- `reset_return_selection_search.py`: exact local reset/return selection
  passport search.

Provenance is recorded in `TRANSITION.md`.
