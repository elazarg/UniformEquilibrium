# Packet recheck of repaired-stress Simon Lyapunov obstruction

Reviewer: `CODEX_NOETHER`

Reviewed packet: `exports/REPAIRED_STRESS_CYCLE_NO_SIMON_LYAPUNOV.md`.

## Verdict

**REVISE with two bounded exactness corrections, then ACCEPT.** The previously
accepted mathematics is reproduced correctly. The microedge formulas,
carrier argument, graph orientation, exact cost, source-novelty limitation,
probability scope, boundary tests, and Lean handoff all check. The packet has
no lifecycle-status header.

The two corrections below do not change the result or proof.

## Required bounded corrections

1. **Quantify strictness on the finite-cell conclusion.** The generic
   predicate `HasFiniteCellLyapunovCertificate` takes a real `constant` but
   does not itself assert that the constant is positive. A constant-zero
   certificate is not excluded by a positive-cost cycle. Therefore replace
   each unqualified claim that the table “admits no
   `HasFiniteCellLyapunovCertificate`” by the exact statement:

   > for every `epsilon>0`, every finite cell type and supplied cell/potential
   > data, and every `c_0>0`, the production predicate
   > `HasQuittingSimonFiniteCellLyapunovCertificate reward epsilon ... c_0 ...`
   > is false.

   Name `HasQuittingSimonFiniteCellLyapunovCertificate`
   (`UniformEquilibrium/Quitting/Classification/SimonFiniteOrbit/SuppliedCorrespondence.lean`)
   in the source section. The existing telescope through
   `HasFiniteCellLyapunovCertificate.exists_globalPotential` proves exactly
   this strict version. It does not and need not exclude nonpositive
   constants.

2. **Align the source player type or state the reindexing.** The packet opens
   with `I=Z/4Z` and then says the table “is
   `RepairedFourPlayerStress.stressWeight`,” but the named source declaration
   uses `RepairedFourPlayerStress.Player := Fin 4`. Either set `I=Fin 4` in
   the packet and explain that cyclic superscripts are label arithmetic
   modulo four, or explicitly transport the displayed `ZMod 4` table along a
   named bijection with `Fin 4`. The raw table is mathematically identical,
   but the present literal declaration correspondence is not type-correct.

## Six-repair checklist

- Author and independent-review metadata replace the notebook status; no
  lifecycle or formalization-status header appears.
- `QuittingSimonFiniteOrbitCarrier`, `QuittingSimonFEdgeAt`,
  `QuittingSimonFiniteOrbitCost`, and
  `HasFiniteCellLyapunovCertificate.exists_globalPotential` are named with
  the correct files. The production finite-cell wrapper only needs the
  addition above.
- The four microedge differences are stated exactly:
  `0`, `beta-3+2*beta*t<=-3h`, `beta-2=-(1+h)`, and
  `1+h-2*beta*t<=h`; the last uses `m<N`, so
  `beta^(m+1)>=beta^N=1/2`.
- The source audit honestly says that the circulation and subdivision already
  exist and that only the Simon carrier/graph specialization and strict-
  potential obstruction are new.
- The three requested boundary checks are present: the unsubdivided
  `1/2` threshold, the terminal-index fence, and the zero-cost self-loop.
- The Lean handoff correctly prioritizes the rational `epsilon=1/2` cycle and
  leaves the every-tolerance subdivision as a separate strengthening.

After the strict-constant and player-type repairs, I have no residual export-
gate objection.
