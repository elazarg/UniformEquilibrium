# Export-gate review of `TWO_CYCLE_LASSO_HARD_PAIR_ALIGNMENT`

Reviewer: `CODEX_RAMSEY`

Verdict: **REMOVE from `exports/`; retain in `notes/`.**  The mathematics is
correct, self-contained, and useful, but the packet does not satisfy the
conjecture-facing importance/consumer gate in `exports/README.md` or the
partial-answer boundary in `questions/FOUR_PLAYER_SINGLETON_PACKET_DISPATCH.md`.

## Mathematical audit

The finite theorem passes independently.

- `MarkedRootedLasso` has exactly the asserted eight two-cycle constructors:
  two `rootedTwo`, three `oneToTwo`, and three `twoToTwo`.  The remaining
  constructors have counts `3+3+3=9`.
- With the repository convention
  `owner -> other`, the dictionary
  `quittingSoloPreempts_iff_normalizedSoloMatrix_le_neg` gives
  `M(other,owner) <= -gamma`.  Reciprocal cycle edges therefore give both
  off-diagonal entries of the literal cycle pair strictly negative.
- The projective-Q obstruction uses the correct cemetery convention.  For
  `q=(-1,-1)`, residual nonnegativity reads
  `0 <= -c + y A(u,v)` and `0 <= -c + x A(v,u)`.  Nonnegativity of
  `c,x,y` and strict negativity of the two entries force `c=x=y=0`, contrary
  to total mass one.  Complementarity is unnecessary.
- The pair has cardinality two, so the checked
  `FinFourQuantitativeFullSupportHardResidual.cardTwoCrossing` applies to this
  exact pair.  Its helper labels are outside the pair and may coincide, as
  stated.
- In `rootedTwo_next`, `marker_eq` identifies `certificate.collider` with
  `geometry.next`, while the rooted lasso root is `certificate.owner`; the
  sharpening is exact.

The positive matrix test, the one-edge homogeneous boundary, the probability
and unrestricted-deviation nonclaim, the source list, and the proposed Lean
decoder/case-split handoff are all accurate.  The source adapter is also real:
the no-uniform branch supplies the hard residual and the same terminal witness
supplies the marked geometry.

## Failed export criterion

The output is only another finite residual:

```text
Nonempty (FinFourHardCardTwoCrossing residual P).
```

`cardTwoCrossing` is not an arbitrary-behavior equilibrium compiler, a
Bellman/chronological producer, or a contradiction.  The packet explicitly
acknowledges that it does not eliminate any of the eight marked geometries and
does not produce a semantic edge or payoff.  Grouping eight marked cases into
one common algebraic treatment is a useful proof-organizational alignment, but
it does not close a named conjecture subchamber, enter a checked semantic
consumer, or decrease a declared well-founded invariant.

This is exactly below the partial-answer threshold stated in
`FOUR_PLAYER_SINGLETON_PACKET_DISPATCH.md`, which retains a partial result only
when its checked composition closes a named subchamber, enters an existing
compiler, or strictly decreases a declared well-founded invariant using actual
source data.  It also falls under the export README's exclusion of a local
lemma/supplied finite verifier without a semantic consumer.  Calling the
17-to-10 bookkeeping merge a “strict conjecture-facing narrowing” does not
repair that missing endpoint: all eight two-cycle semantic cases remain live.

Accordingly no mathematical repair is needed.  The result should remain in
the author's inventory note and can become exportable if a later theorem
consumes `FinFourHardCardTwoCrossing` on the aligned pair into an unrestricted
semantic compiler, contradiction, or genuine invariant descent.

## Delta gate: reviewed `rootedTwo_next` semantic extension

The conference owner subsequently authorized the finite alignment question's
importance/export placement independently of the earlier consumer objection.
Under that instruction, the packet-level verdict for the amended mathematics
is **PASS**.  The earlier removal recommendation does not apply to the
user-authorized placement decision.

The added source hypotheses are exactly those already carried by the packet:
the same `QuittingTerminalExploitabilityWitness`, the same immediate
singleton-collision certificate, and the `rootedTwo_next` constructor of the
same marked preemption lasso.  Its marker equation makes
`P={owner,collider}` the decoded hard pair.

Applying `exists_leave_or_join_gain P` is exact.  Because owner and collider
are distinct,

```text
P.erase collider={owner},
P.erase owner={collider}.
```

Collider leave contradicts the collision inequality by `2*gamma<=0`.
Owner leave gives

```text
r(P)(owner)+gamma<=r({collider})(owner),
```

and the **reverse** rooted-two edge is
`QuittingSoloPreempts reward gamma collider owner`, namely

```text
r({collider})(owner)+gamma<=r({owner})(owner).
```

Thus the constant and orientation in `(A2)` are exactly `2*gamma`.  The
other toggle arm is literally the outside join `(A3)`.

The unordered `cardTwoCrossing` pair can be relabelled as owner/collider.
Its positive entries translate through
`normalizedSoloMatrix_eq_soloReward_sub` to the two strict helper inequalities
in `(A8)`, and both helpers lie outside `P`.  In `Fin 4`, if a third outside
label `s` differs from both chosen helpers, the two helpers coincide; the
packet correctly does not claim their uniqueness.

The extension adds no probability or restricted-strategy approximation.  It
uses the checked terminal witness at a pure coalition and exact terminal
reward inequalities.  Its source remains unrestricted behavioral terminal
exploitability, while its conclusion remains finite payoff-table data.  The
packet continues to disclaim any Bellman root, reached chronology,
sure-exit certificate, or uniform-payoff compiler.  Therefore the amendment
preserves the packet's mathematical correctness and scope without requiring
repair.
