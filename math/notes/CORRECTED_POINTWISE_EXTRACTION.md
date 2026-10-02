# Corrected pointwise extraction from approximate equilibria

Status: structural classification note; no longer a conjecture-closing
question because the premise itself has a checked direct uniform-payoff
consumer.

## Setting

For a finite quitting reward table, let `ε` range over positive accuracies.
The corrected structured alternatives are: stationary approximate
equilibrium, instant punishment, a well-supported absorbing sequence, or a
stationarily generated approximate-equilibrium family with a finite
stationary prefix followed by roots and a punishment cap.

## Question

Starting only from the assertion that for every `ε > 0` there exists an
arbitrary behavioral terminal `ε`-Nash profile, prove the exact pointwise
alternative used by the corrected classification: at every positive scale,
one of the four alternatives above is available with the required common
reward bounds and support data. The extraction must retain the punished
player, finite prefix horizon, actual punishment profile, positive live mass,
and global deviation inequality. If the pointwise assertion is too strong,
give a finite quitting counterexample or state the weakest replacement.

## Why this is useful

The checked fixed-branch theorem already reduces a valid pointwise alternative
to stationary, instant, well-supported, or diffuse stationarily-generated
branches. Supplying the missing extraction would move the classification from
a conditional interface to a theorem about arbitrary approximate equilibria.

## Checked inputs and consumers

- `fixedCorrectedQuittingBranch_of_pointwiseAlternative`
  (`UniformEquilibrium/Quitting/Classification/Existence/CorrectedFixedBranch.lean`)
  consumes the four-way pointwise premise.
- `QuittingDiffuseStationaryPrefixFamily` and
  `exists_quittingDiffuseStationaryPrefixFamily`
  (`UniformEquilibrium/Quitting/Classification/Existence/StationarilyGeneratedWitnessRegimes.lean`)
  retain the diffuse witness fields once that premise is supplied.
- `quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
  (`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`)
  identifies the terminal positive endpoint.

## Not proved

The current pointwise theorem is deliberately an input proposition; it does
not extract these branches from arbitrary behavioral profiles.

## Acceptable answers

A positive answer gives the quantified extraction and all retained fields. A
negative answer gives an explicit approximate-equilibrium sequence for which
every proposed branch loses one named field. A proof that selects only
stationary or periodic profiles does not answer the question.

## Dependencies

None required.
