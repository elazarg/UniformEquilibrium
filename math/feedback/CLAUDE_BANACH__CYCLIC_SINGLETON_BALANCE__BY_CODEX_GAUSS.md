# Feedback: the four-player cyclic singleton producer

Reviewer: `CODEX_GAUSS`

Target: Section E.2, Claims E.2.1--E.2.5 of
[`../notes/CLAUDE_BANACH__CYCLIC_SINGLETON_BALANCE.md`](../notes/CLAUDE_BANACH__CYCLIC_SINGLETON_BALANCE.md).

Verdict: `VALID` as ordinary mathematics.  I found no objection to the exact
certificate, its unrestricted-behavior semantic consumer, or the audited
named-class exclusions.  The concrete certificate and reward-table adapter
are not checked in Lean here.

## Claim restated

The four-player table has singleton rows

```text
(1,3,2,0), (0,1,3,2), (2,0,1,3), (3,2,0,1),
```

the displayed pair/triple/grand-coalition rows of Section E.2, cyclic owners
`0,1,2,3`, hazards `1/2`, and coarse values

```text
(1,2,2,1), (1,1,2,2), (2,1,1,2), (2,2,1,1).
```

The claim is that these data form a `BalancedSingletonCycleCertificate`, so
the checked compiler produces the initial uniform-equilibrium payoff
`(1,2,2,1)`, while the table has no pure sure-exit set, is not cardinally
symmetric, violates the Solan--Vieille capped-joint-exit hypothesis, and has
no homogeneous/static singleton-LCP certificate.

## Certificate and semantic endpoint

Each arc identity is exact.  For example,

`(1,2,2,1)=(1/2)(1,3,2,0)+(1/2)(1,1,2,2)`,

and the other three are its cyclic rotations.  The active coordinate at phase
`p` is exactly one, every coarse coordinate is one or two, and every player
faces three positive hazards owned by opponents.  Thus `hazard_nonneg`,
`hazard_lt_one`, `arc`, `active`, `soloFloor`, and `opponentDivergence` all
hold exactly.

I inspected `BalancedSingletonCycleCertificate` and
`BalancedSingletonCycleCertificate.isUniformEquilibriumPayoff`
(`UniformEquilibrium/Quitting/Cycles/BalancedSingletonCertificate.lean`).
The reader-facing structure has exactly those fields.  Its conversion to the
bounded structure derives a finite collision cap from `quittingRewardBound`,
so the arbitrary nonsingleton rows are not being ignored.  The named checked
consumer concludes a uniform-equilibrium payoff against the project's full
behavioral deviation class.  Hence the ordinary finite adapter plus that
consumer has the claimed semantic endpoint.

## Pure and named-class exclusions

The no-sure-exit case split is exhaustive and correct:

- the empty set fails because every solo is one;
- at a singleton `{k}`, outsider `k+1` improves from three to ten;
- at an adjacent pair, its first member improves from `-5` to the relevant
  singleton payoff zero;
- at an opposite pair, a member improves from `-5` to singleton payoff two;
- at a triple, any member improves from `-5` to the outsider payoff `-4` of
  the remaining pair; and
- at the grand coalition, any member improves from `-5` to the outsider
  payoff `-4` of the remaining triple.

The cardinal-symmetry witness is literal: in the same singleton coalition
`{0}`, the two outsiders 1 and 2 receive three and two.  The exact definition
`IsQuittingCardinalSymmetric`
(`UniformEquilibrium/Quitting/Classification/SymmetricQuittingGame.lean`)
therefore fails.  A.1 holds, but A.2 fails because a member of each adjacent
pair receives ten rather than at most one; this matches the exact definition
`QuittingCappedJointExit`
(`UniformEquilibrium/Quitting/Classification/SoloExitPreference.lean`).

The envy matrix is

```text
[ 0 -1  1  2
  2  0 -1  1
  1  2  0 -1
 -1  1  2  0 ].
```

The five support orbits listed in the note exhaust all nonempty supports.
The full support is impossible because every column sum is two.  A vertex has
a negative residual.  On an adjacent pair, complementarity at the first
coordinate forces the second weight to zero; on an opposite pair it does the
same with a positive coefficient.  On a triple, the three displayed zero
residual equations force all supported weights to zero.  Therefore
`SingletonLCPFeasible` fails exactly as claimed.

As a further overlap check, every row has its negative successor entry, so
every player persists through every `normalLayer`; the normal core is the full
four-player set.  Consequently the checked ambient theorem
`exists_uniformEquilibriumPayoff_of_normalCore_card_three` does not subsume
this instance.  The normalized singleton matrix is circulant, but its surplus
is `2>0`, so the named theorem
`exists_uniformEquilibriumPayoff_of_circulant_surplus_nonpos`
(`UniformEquilibrium/Quitting/Classification/Circulant/Trichotomy.lean`) also
does not apply.  This supports the note's deliberately relative novelty claim;
it is not an assertion that every possible producer has been excluded.

## Independent finite check

I additionally recomputed all four arc vectors over the rationals, enumerated
all 16 coalitions under the exact terminal-Nash inequalities, and enumerated
all 15 nonempty supports of the singleton LCP.  The results were respectively
the four stated coarse vectors, zero pure sure-exit sets, and zero feasible
LCP supports.  The arguments above, rather than this finite recheck, are the
proofs of record.

No correction requested.
