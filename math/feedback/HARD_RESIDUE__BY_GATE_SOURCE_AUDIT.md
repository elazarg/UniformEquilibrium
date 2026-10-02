# Source/freshness audit of `HARD_RESIDUE.md`

## Verdict

**FAIL for export in its present form.**

The material before `## Followup` is mathematically sound, uses actual
behavioral sources with the right unrestricted-cap semantics, and is already
recorded essentially verbatim as the independently reviewed note
[`CHATGPT_EXTERNAL__NONCOLLAPSING_MAXIMAL_PAID_RESET_ORBIT.md`](../notes/CHATGPT_EXTERNAL__NONCOLLAPSING_MAXIMAL_PAID_RESET_ORBIT.md).
It is therefore not fresh export content.  Its checked inputs still stop before
the recursive wrapper claimed in ordinary mathematics.

The followup is fresh, but its displayed two-clock theorem is false under its
stated notion of diffusion.  The proposed Lean signature silently replaces
raw absorption tending to zero by the strictly stronger conditioned-mesh
hypothesis.  Even that repaired conditional theorem is not attached to a
chronology produced by the Fin4 hard residual.

## Exact correspondence for the maximal paid/reset orbit

The checked one-step source is exactly:

- `QuittingPaidCapLiftedSource.MaximalOneStepPaidResetRegeneration`; and
- `QuittingPaidCapLiftedSource.maximalOneStepPaidResetRegeneration_or_uniqueAllContinue`

in
`Research/Quitting/PaidCapMaximalOneStepRegeneration.lean`.

These declarations do preserve an actual behavioral profile, the same global
minimum, a zero-debt reset coordinate, positive same-law opponent incidence,
and a fresh fixed-law reset dispatch.  Their caps are the unrestricted
behavioral caps stored in `quittingTerminalSemanticPair`; their paid witnesses
are legal deterministic pure stopping-time deviations, including `Never`.
There is no strategy-class downgrade here.

The exact scalar maximal-prefix ray, survival lower bound, retained suffix-atom
bound, and summable absorption account already appear in:

- `Research/Quitting/MaximalCapSemanticPrefixOrbit.lean`; and
- `Research/Quitting/MaximalCapSemanticPrefixReturn.lean`.

In particular, the latter already contains
`QuittingMaximalCapSemanticPrefixRayStall.summable_absorption` and the retained
law/atom results.  The checked double-source hard-residual adapter is
`sourceMaximalRegeneration_or_repairedMaximalRegeneration_or_doubleUnique` in
`Research/Quitting/FinFourPaidCapMaximalDoubleRegeneration.lean`.

What is not a named checked declaration is the recursive paid/reset orbit with
a public per-step gain equation.  The current one-step proof constructs the
descendant certificate with

```text
descendant.gain = jointContinue(root) * source.gain,
```

not with the opponent-survival factor displayed in `HARD_RESIDUE.md`.  The
sharper opponent-survival choice is mathematically available by re-extracting
the paid row, but is not the present theorem surface.  The conservative joint-
survival equality is already sufficient for the noncollapse estimate.

All of this correspondence, including the valid four-player local
unique-all-Continue example, is already documented in
`notes/CHATGPT_EXTERNAL__NONCOLLAPSING_MAXIMAL_PAID_RESET_ORBIT.md`.  That note
also records the honest frontier: the result does **not** answer
`questions/FIN4_PAID_RESET_REGENERATION_RANK.md`, because it supplies neither a
well-founded rank nor a near-return/terminal consumer.

## Counterexample to the stated two-clock theorem

Take two players `p,q` and the symmetric rewards

```text
r_p({p}) = 0,   r_p({q}) = 1,   r_p({p,q}) = 2,
r_q({q}) = 0,   r_q({p}) = 1,   r_q({p,q}) = 2.
```

Choose `0 < h_0 < 1/2` and recursively set

```text
h_{t+1} = h_t / (2 * (1 - h_t)).
```

At date `t`, let both players Quit independently with probability `h_t`, and
put

```text
v_t(p) = v_t(q) = 2 h_t.
```

For either player, immediate Quit and Continue have exactly the same value:

```text
Q_t = 2 h_t,
C_t = (1 - h_t) * 2 h_{t+1} + h_t = 2 h_t.
```

Thus every root is an exact endpoint-Nash root and
`v_t = T_{x_t} v_{t+1}`.  Only `p,q` are active.  Also `h_t -> 0`, so the raw
one-stage absorption

```text
alpha_t = 1 - (1 - h_t)^2
```

tends to zero.  Every suffix has positive eventual absorption, and by symmetry
both players carry the same positive conditioned singleton share arbitrarily
far out.  Finally

```text
v_t -> 0 = r_p({p}) = r_q({q}).
```

Nevertheless,

```text
normalizedSoloMatrix reward p q = r_p({q}) - r_p({p}) = 1,
normalizedSoloMatrix reward q p = r_q({p}) - r_q({q}) = 1.
```

This contradicts the stated conclusion.

The proof fails exactly where it says boundary tightness makes the block
telescope's left side `o(A_n+B_n)`.  Here the remaining absorption scale tends
to zero at the same rate as the boundary error; ordinary convergence to the
singleton reward does not give the required relative-rate estimate.

## Conditioned-mesh mismatch

The prose assumes only

```text
1 - jointContinue(x_t) -> 0.
```

The proposed Lean declaration instead assumes

```text
Tendsto (quittingTailConditionedAbsorptionWeight roots) atTop (nhds 0).
```

These are not equivalent.  The counterexample above has raw mesh tending to
zero but its current absorption remains a nonvanishing fraction of all future
absorption, so its conditioned mesh does not tend to zero.

A plausible repaired theorem would work throughout with the conditioned
chronology and assume vanishing conditioned mesh plus positive conditioned
singleton shares.  The nearest checked result is
`normalizedSoloMatrix_eq_zero_of_fencedSoloWindows` in
`UniformEquilibrium/Quitting/Cycles/DiffuseTailSoloStructure.lean`; it requires
an actual recurrent charged solo-window family.  No declaration matching
`normalizedSoloMatrix_pair_eq_zero_of_twoClockDiffuseTail` or
`HasPositiveConditionedSingletonShare` currently exists.

The proposed Lean signature also omits the boundary-convergence/actual-tail
data needed to identify an arbitrary Bellman value sequence with the intended
terminal boundary.  The conditioning API keeps this distinction explicit in
`PhantomBoundaryConditioning.lean`.

## Hard-residual attachment

The checked hard-residual theorem
`FinFourQuantitativeFullSupportHardResidual.exists_nonprojectivePrincipal_card_two_or_three`
in
`UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/FullSupportHardPrincipalSize.lean`
produces only a table-level nonprojective principal.  For a two-element
principal, `negative_offDiagonal_of_pair_nonprojective` in
`FullSupportHardPrincipalDispatch.lean` indeed forces both off-diagonal entries
to be strictly negative.

It does **not** produce one exact Nash--Bellman chronology having eventual
pair support, positive singleton shares, vanishing conditioned mesh, and tight
boundary values.  Nor do the four alternatives listed at the end follow as
existing consumers:

- vanishing conditioned singleton share is not by itself a regenerated
  minimum-source support drop;
- failure of tightness does not by itself provide the uniform local refusal
  gap required by `summable_selectedRefusalCharge_of_nash`; and
- an endpoint-Nash root sequence is not automatically the global
  root-sequence Nash object required by that refusal theorem.

Accordingly the followup neither answers nor presently narrows
`questions/FIN4_HARD_RESIDUAL_SEMANTIC_CLOSURE.md`.  After correcting the
diffusion hypothesis, the block calculation may be worth retaining as an
internal conjectural lemma, but it needs both a proof in the conditioned
variables and a source-faithful hard-residual adapter before reconsideration
for export.
