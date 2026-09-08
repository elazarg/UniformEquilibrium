# Paired collision disjunction: formalization dependencies

Status: CODEX_FORMALIZER intake audit. The exported packet was read in full;
this record does not claim implementation or a Lean check of its new family.
Source: `math/exports/PAIRED_COLLISION_REWARD_EQUILIBRIUM_DISJUNCTION.md`.

The input is one literal fifteen-row reward table with one real parameter.
Only its twelve pair-member coordinates vary. The conclusion concerns every
real parameter in that family, not the arbitrary paired-singleton collision
cylinder. Rates and the payoff target must precede accuracy and truncation.

## Independent construction tasks

1. Define the parameterized table and identify its parameter-one instance
   with the existing paired example. Verify the unchanged singleton matrix,
   the capped-joint exit for parameters at most one, and the sure-pair exit
   for parameters at least four.
2. In the periodic interval from one to two, construct the admissible rates
   by the two intermediate-value arguments, including the positive
   denominators and strict bounds. Prove the actual phase equations and
   quiet-player inequalities, then use the existing periodic behavioral
   verification. A supplied rate pair or cap certificate does not complete
   this task.
3. Prove the independent finite-clock censoring formulas for prescribed
   payoffs and complete caps. Retain after-support stopping dates and Never.
   The finite-horizon bound is one-sided for deviations; censored opponents
   have positive Never mass, so the infinite-profile geometric contraction
   cannot be reused without this argument.
4. In the stationary interval from two to four, establish the common-hazard
   endpoint identities and the two scalar sign tests, produce the interior
   root, and apply the stationary complete-cap and uniform-payoff consumers.
5. Assemble the overlapping four-range theorem for every real parameter,
   with the periodic exact-suffix and finite-law results stated separately.

## Reuse and scheduling

`periodTwoProfile_isExactTerminalNash` and
`periodTwo_isUniformEquilibriumPayoff`
(`UniformEquilibrium/Quitting/Examples/BlockPair/FourPlayerPairedSingletonPeriodTwo.lean`)
already exist for the fixed parameter-one example. Their presence was checked
statically here; extending them to the whole family still requires the rate
producer and literal reward identities above.

The packet supplies the remaining named low-parameter and stationary
consumers. Their application to this new table is an implementation task,
not an inferred seal from their names. This packet does not depend on the
new integer-degree library. It can follow a completed packet worker without
taking the dedicated Literature slot or interrupting the rational selector
and discounted Bellman constructions already underway.
