# Packet gate for `FIN4_PUNISHMENT_NORMAL_ATOMIC_COLLISION_HANDOFF`

Reviewer: `CODEX_RAMSEY`

## Verdict

**REVISE, then PASS.**  The mathematics, actual-data composition, behavioral
semantics, boundary tests, source audit, Lean handoff, and nonclaims all pass.
The exact-statement section needs one bounded quantifier repair before the
packet satisfies item 1 of `exports/README.md`: Corollaries B--C currently use
free `bound`/`certificate` data, and Corollary C reuses `gamma` without saying
that it is the terminal gap stored in `residual` rather than the witness fixed
above Theorem A.

The required repair is purely literal.  State Corollary B for

```text
bound : Real,
residual : FinFourQuantitativeFullSupportHardResidual reward bound,
gamma = residual.witness.terminalGap,
```

and state Corollary C after additionally quantifying

```text
certificate : QuittingImmediateSingletonCollision reward gamma,
chain : FinFourRootedTwoNextOwnerLeaveCollisionChain residual certificate.
```

All inequalities in B--C should then use this `gamma`.  No proof change is
needed.  After that edit my verdict is **PASS**.

### Post-repair type check

The first quantifier repair is present, but one further literal specialization
is needed.  The Exact statement globally fixes an arbitrary finite type `I`
and a reward table on `I`; Corollary B then writes a
`FinFourQuantitativeFullSupportHardResidual reward bound` and quantifies
`b : Fin 4` without resetting `I`.  Add, before Corollary B,

```text
Now specialize I=Fin 4 (so reward is a table on Fin 4).
```

or restate the Fin4 reward table there.  Corollary C inherits that
specialization.  This is again only a statement-typing repair, but the packet
remains **REVISE** until it is explicit; after it, the mathematical **PASS**
verdict is final.

**Final verification.**  The packet now explicitly specializes `I=Fin 4`
before Corollary B, restates the Fin4 reward type, and retains the repaired
`bound`, `gamma`, `certificate`, and `chain` quantifiers.  Final packet verdict:
**PASS**.

## Atomic-blocker specialization

At the pure singleton root with owner `b`, the checked sure-owner barrier is
applicable.  Its two scalar components simplify with the orientations stated
in the packet:

```text
quittingAtomicBlockerBalance = reward({b})(b)-P_b,
quittingForcedOwnerOutsiderCoordinateDefect(j)
  = max(0,reward({b,j})(j)-reward({b})(j))  (j != b).
```

Punishment normality kills the owner-refusal arm.  The terminal gap is
strictly positive, so the pure endpoint furnished by
`exists_outsider_pureEndpoint_gain_ge_of_nonneg_blockerBalance` cannot be the
Continue endpoint, whose gain is zero.  It is therefore Quit and gives the
claimed collision inequality with the full terminal-gap constant.  This
argument remains valid for a singleton player type as well: in that case the
hypotheses themselves are inconsistent, as the barrier forces a positive
outsider defect from an empty outsider set.

The probability audit is exact.  A sure owner absorbs every outsider's
behavioral replacement at date zero.  If the owner instead replaces its
whole strategy, the one-stage punishment continuation is controlled through
`quittingStationaryUnilateralCap`; thus the source barrier is not merely a
normal-form or pure-deviation estimate.

## Full-support and rooted-two adapters

For the `Fin 4` residual, `packet_support_eq_univ` and
`packet.mem_support_iff` give positive mass at each label.  The packet fields
`positive_mass_pins_target` and `punishment_le_target` then give

```text
P_b <= packet.target(b) = reward({b})(b)
```

on the same reward table.  Applying Theorem A at each label therefore yields
the four claimed collision inequalities.  Finite choice gives a
fixed-point-free self-map of `Fin 4`, whose functional graph necessarily has
a cycle of length 2, 3, or 4; no stability property is silently attached to
that cycle.

In the collider-leave arm of
`FinFourRootedTwoNextOwnerLeaveCollisionChain`, the signs are

```text
reward({c,s})(c)+gamma <= reward({s})(c),
reward({s,t})(t)+0      >= reward({s})(t)+gamma.
```

If `t=c`, these are opposite strict-gap inequalities on the same two numbers
and imply `2*gamma<=0`, contrary to positivity.  Since the singleton
collision already gives `t!=s`, the new label lies outside `{c,s}`.  The
other `second_gap_toggle` arm already supplies an outsider of that pair with
the same gap.  The case split is exhaustive and preserves the original
reward table and residual witness.

## Remaining export checks

- The user-authorized singleton-dispatch alignment is genuinely narrowed:
  punishment normality removes the owner-refusal alternative and the
  rooted-two collider-leave arm gains a third-label, gap-sized continuation.
- The positive, zero-defect, abnormal-owner, and third-label tests exercise
  the constant, orientation, and load-bearing premise.  In the abnormal-owner
  test, Never gives cap at least zero and the specified Never opponent gives
  cap at most zero, so the displayed refusal balance is indeed `-1`.
- The source audit correctly credits
  `AtomicBlockerPaidGeometry.lean` for the strategic engine and identifies
  only the same-table packet/rooted-two composition as new ordinary
  mathematics.  No literature attribution is involved.
- The Lean handoff names the right simplification lemmas and checked
  consumers and does not put the desired collision map into a source
  structure.
- The packet correctly does not claim an exact root, Bellman edge,
  chronology, stationary compiler, monotone invariant, or solution of the
  remaining shared-helper/hard-helper arms.
