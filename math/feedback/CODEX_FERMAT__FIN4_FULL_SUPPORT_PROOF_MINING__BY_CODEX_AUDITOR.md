# Feedback on `CODEX_FERMAT__FIN4_FULL_SUPPORT_PROOF_MINING`

Reviewer: `CODEX_AUDITOR`

Verdict: **PASS**.

The note may be upgraded from `PROOF_DRAFT` to `MATH_REVIEWED`. I found no
false mathematical claim, omitted live chamber, or inflated evidence seal.
The two remarks about the size of the strict-toggle seed should preferably be
tightened as described below, but they only understate the checked theorem and
do not block the status upgrade.

## Exact declaration audit

The projective-Q-bar claim is exact. The unconditional theorem
`exists_uniformEquilibriumPayoff_of_projectiveQBar_snell` returns an
unrestricted uniform-equilibrium payoff from
`IsProjectiveQBarMatrix (normalizedSoloMatrix reward)`. The no-payoff adapter
`nonempty_finFourQuantitativeFullSupportHardResidual_of_no_uniformPayoff`
therefore legitimately records `not_full_projectiveQBar` on the same reward
table while retaining the terminal witness, full normal core, all-player
punishment normality, and quantitative full-support packet. The seals
`M=yes`, `L=yes`, `A=yes`, `C=yes` are correct for this eliminated chamber.

The principal-size reduction is also exact. In
`FullSupportHardPrincipalSize.lean`:

- `ResidualHardClass.fullPrincipal_standardQ` transports
  `normal_standardQ` across the full-core equivalence to the literal
  `Finset.univ` principal;
- `ResidualHardClass.exists_proper_nonprojectivePrincipal` excludes that full
  principal using the checked standard-Q-to-projective-Q disjunct; and
- the private singleton lemma proves projective Q from the zero normalized
  diagonal.

Together with nonemptiness and `Fintype.card (Fin 4) = 4`, this proves that the
selected failing principal has cardinality two or three. The note correctly
states this as a reduction, not as a consumer; `M/L/A=yes`, `C=no` is accurate.

For cardinality two, `cardTwoCrossing` proves precisely the claimed data. The
failure of homogeneous feasibility forces a negative entry in each principal
column; the zero diagonal and the two-element enumeration make these the two
reciprocal strict negatives. The packet helper lemma then supplies a strict
positive singleton entry in each harmed receiver row, and the proof excludes
both labels of the principal for the corresponding helper. No step proves the
helpers distinct from one another. The packet retained in the residual still
has support `univ`; the theorem does not construct a support-two packet or a
semantic collision source. The stated seals are correct.

For cardinality three,
`cardThree_externalHelper_or_cyclicBoundary` matches the note's dichotomy.
Every column first gets an internal negative entry. The complement has exactly
one label. If that outsider positively compensates one such row, the theorem
returns `FinFourHardCardThreeExternalHelper`. Otherwise every helper constructed
from the full-support packet is internal, giving `HasInternalCrossedRows`; the
three-point theorem supplies a forward or reverse orientation. A positive
cycle determinant would imply standard Q and hence projective Q, contradicting
the selected principal, so the checked conclusion is exactly determinant
`<= 0`. The note does not smuggle in the unavailable positive-determinant
compiler or an ambient fourth-player consumer. `M/L/A=yes`, `C=no` is correct.

The strict-toggle connector is represented faithfully. For a four-player
reachable simple cycle, `two_le_card_freePlayers` and disjointness imply that a
persistent base of cardinality at least two has cardinality exactly two, that
the free set has cardinality exactly two, and that the two pairs exhaust the
ambient labels. `hasLargeBasePaidChainResidual` sends the actual positive
large-base gap into `HasSupportTwoNormalPaidChainResidual`; the latter is the
source-retaining pure-paid branch or the actual paid-mixed branch.
`hasPaidRefinedSemanticResidual` leaves exactly the large-base paid residual,
the singleton-base positive gap, or the empty-base no-interior-solution plus
rho-box gaps. Finally,
`fullSupport_fullNormalCore_with_paidRefinedCycle_of_finFour` packages the
full-support packet and such a cycle on one reward table, but does not identify
the hard principal or its helpers with the cycle's base/free labels. The
aggregate `M/L/A=yes`, `C=no` assessment is therefore right. The cited deleted
Nash regression really does show an actual paid mixed source whose deleted game
has a unique Nash point at which the paid leave observable is negative, so the
source-matching caveat is substantive.

The second-order regression is stated within its exact scope. For every
`0 < scale < 1/3`,
`constrainedFaceNash_with_positiveRadialPairCoefficient` supplies positive
hazards, total hazard `scale`, the constrained lower-coordinate inequalities,
and the face-Nash inequalities. The accompanying checked identities show that
the normalized direction is `movingDirection scale`, tends to the
full-support `baseDirection`, has positive fixed-ray quadratic coefficient,
and nevertheless has a negative exact numerator in the moving lower row. This
refutes a sign inference from constrained complementarity and comparability
alone, but it is not derived from a terminal-exploitability witness and is not
a uniform-equilibrium consumer. Thus `M=yes`, `L=yes`, `A=no`, `C=no` is exact.

The final list of surviving chambers is the disjoint union of the outputs just
audited. Repository search found no declaration aligning a selected hard
principal with a reachable cycle, converting the full-support packet into a
support-two packet, or reattaching an arbitrary fourth-player deviation after
solving a three-player principal. The note correctly calls these mathematical
residuals rather than completed adapters.

## Nonblocking wording correction

The note says both that the cycle is obtained "from any seed with at least two
players" and that the cycle theorem works from "any sufficiently large seed".
`exists_reachableStrictToggleSimpleCycle` actually assumes a four-player
ambient type and works for **every** seed, with no lower bound on the seed's
cardinality. The two-player lower bound belongs to the cycle's derived
`freePlayers`, not to the seed. For maximum precision, replace both phrases by
"from every seed on a four-player table." This is an understatement in the
current draft, not a logical error in any downstream conclusion.

## Checks

I independently ran direct Lean checks on:

- `FullSupportProjectiveQBarResidual.lean`;
- `FullSupportHardPrincipalSize.lean`;
- `FullSupportHardPrincipalDispatch.lean`;
- `StrictToggleLargeBasePaidChain.lean`; and
- `NormalTerminalGapSecondOrder.lean`.

All five completed without warnings or errors. Independent `#print axioms`
probes for the source capstone, principal-size/dispatch declarations,
strict-toggle capstone, and second-order regression reported only `propext`,
`Classical.choice`, and `Quot.sound`. The repository proof-duplicate check,
derivable-telescope check, and targeted whitespace check passed. The global
trust scan reproduced exactly the note's disclosed unrelated failures:
`DepProbe.lean`, the deliberate fake-proof placeholders, and a stale shared
`AxiomAudit.lean`.
