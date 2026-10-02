# Three-cycle passive inheritance: consolidated review

The raw-table sufficient theorem survives the independent mathematical and
source reviews. It is a substantive special-case existence result, not a
resolution of arbitrary four-player quitting games. Its new contribution is
the ambient passive-row producer; the explicit active three-player cycle is
already available in the repository.

Independent evidence:

- [CODEX_CAUCHY](THREE_CYCLE_PASSIVE_INHERITANCE__BY_CODEX_CAUCHY.md) checked
  the raw inverse criterion, actual continuation values at every microdate,
  unrestricted behavioral deviations, independent censoring, signed
  finite-horizon comparison, and nonnegative-inverse boundary. Exact attempts
  to remove the passive condition and to avoid subdivision explain why those
  hypotheses and operations matter.
- [CODEX_FROBENIUS](THREE_CYCLE_PASSIVE_INHERITANCE__BY_CODEX_FROBENIUS.md)
  checked source correspondence, the full matrix support inventory, the
  degree-one example and open neighborhood, and the extent of the new class.
  The review also states and proves the general row-cone inheritance lemma
  for a supplied balanced child cycle.

These reviews have complementary scopes: the first checks the strategic proof
and the second checks source correspondence and matrix-class comparisons.
No mathematical objection to the combined core theorem was identified.
No new Lean declaration was checked here.

## Mathematical content

Choose three players whose singleton-relative principal matrix is invertible
with entrywise nonnegative inverse. Require each outside player's
singleton-relative row, restricted to these players, to be a nonnegative
linear combination of the three principal rows. The packet constructs a fixed
uniform-equilibrium payoff, for arbitrary signed own-singleton levels and
arbitrary nonsingleton rewards. Every outside player can play Never.

The crucial new control is at every continuation date, not only at the
initial target. The outside player's surplus is the same nonnegative linear
combination of the child continuation surpluses. This supplies its singleton
floor throughout the schedule. Subdivision makes collision opportunities
small, and the full stopping-time comparison charges this error only once.

The existing `RightSingletonCycle` construction in
`UniformEquilibrium/Quitting/Classification/ThreePlayer/CyclicCompiler.lean`
supplies the active cycle and rates. The new adapter supplies an ambient
`BalancedSingletonCycleCertificate`, whose
`BalancedSingletonCycleCertificate.isUniformEquilibriumPayoff`
consumer is in
`UniformEquilibrium/Quitting/Cycles/BalancedSingletonCertificate.lean`.
Thus no unproduced strategic witness is assumed in the raw-table theorem.

The example belongs to an open singleton-matrix region of degree one, outside
the specific full-matrix inverse-positive, ambient projective-Q-bar,
integral-tournament, and once-per-owner signed-four-cycle tests compared by
the reviewers. This is a bounded comparison of criteria, not a claim of
disjointness from every existing equilibrium class. Degree-one matrix data
are not the complete strategic hard-residual hypothesis.

## Statement and attribution corrections

1. Credit `rightAlpha`, `rightBeta`, `rightGamma`, `rightCoarse`, and the
   three-player compiler as existing mathematics. Also credit the specialized
   `FinFourIntegralTournamentBalancedSingleton.certificate` lift in
   `UniformEquilibrium/Quitting/Classification/LCP/FinFourIntegralTournamentBalancedSingleton.lean`.
   The rate formulas should not be advertised as new.
2. Define exploitability explicitly as maximum unilateral regret. The
   displayed bounds are per-player/maximum bounds, not bounds on summed debt.
3. The standalone document mentions a generated checks JSON that is absent
   from the reviewed input bundle. Either include the reproduced artifact or
   rely on the supplied reproducible script without suggesting that artifact
   is already attached. This does not affect the proof.

The general certificate-inheritance lemma should be separated
from the raw three-player inverse criterion and their composition. The former
is conditional inheritance; their composition is the complete reward-class
producer. The weak-inverse perturbation and reward-closedness arguments remain
credited dependencies.

## Reproduction and reviewed input

The coordinator read both packet documents and the complete verifier, then
ran its three checking functions without calling its artifact-writing main:

```sh
python3 -c 'import runpy; d=runpy.run_path("gpt/VERIFY_THREE_CYCLE_PASSIVE_INHERITANCE.py"); print(d["matrix_certificate"]()); print(d["symbolic_rate_checks"]()); print(d["finite_regressions"]())'
```

All four symbolic identities and all eleven enumerated matrix supports
passed. The sole admitted inhomogeneous support is the displayed triple.
The finite checks passed on 192 profiles over 48 signed tables, with 768
independent full-cap comparisons. These are exact regression checks, not
proofs of universal coverage. No Lean build or axiom audit was run.

Reviewed source revision: `5aac30ad2553dadd5895dc79fbc4f1f5680d7570`.
Input SHA-256 values:

```text
THREE_CYCLES.md
4dca327dc6520779379dc433c8e123f26b121ef4a68359fdad8a2b4abeb8977c
THREE_CYCLE_PASSIVE_INHERITANCE.md
9ae1811afdf92984235c74dc5203b15b7ac575abe2fea70fa701e62bdeec75a0
VERIFY_THREE_CYCLE_PASSIVE_INHERITANCE.py
7eaba3a57ca72a4ceebf805a7b794d251ce38376bd45e7c16ca2947f28d8902c
```

The class is sufficient, not exhaustive: the row-cone test need not hold for
an arbitrary four-player table. The corrections above concern attribution
and notation, not the core existence argument.
