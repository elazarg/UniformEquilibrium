# Source audit of the corrected two-clock clock-ratio follow-up

## Verdict

**FAIL for export in its present form.**

The corrected clock-ratio calculation is mathematically sound and appears to
be genuinely new as a conditional local theorem.  In particular, I found no
checked declaration or earlier reviewed packet proving its exact recurrence
or the resulting positive-Never conclusion.  It does not, however, satisfy
the export gate: the eventual two-clock, everywhere-interior exact
Nash--Bellman tail is supplied rather than produced from a hard-residual
source, and positive Never mass has no new consumer.  The follow-up also
bundles this new local result with maximal-orbit tail conclusions that are
already checked and documented.

The clock-ratio result should be retained as a self-contained internal note or
Lean target.  It should not be exported as a result about the Fin4 hard
residual until an actual-source adapter or a strict consumer is proved.

## Exact source correspondence

The local semantics used by the calculation agree with the repository:

- `quittingRootSuccessorPayoff_eq_endpointMix` and the root Quit/Continue
  endpoint definitions used throughout
  `UniformEquilibrium/Quitting/Cycles/PeriodicCompiler.lean` identify the
  prescribed Bellman value as the player's mixture of its two endpoint
  values.
- `IsεQuittingRootEndpointNash` is the correct one-row strategic predicate.
  With error zero and a player's Quit probability strictly between zero and
  one, both endpoint values equal the prescribed successor payoff.  No
  unrestricted terminal-cap statement is needed for this local equality.
- `normalizedSoloMatrix` as used by
  `normalizedSoloMatrix_eq_zero_of_fencedSoloWindows` in
  `UniformEquilibrium/Quitting/Cycles/DiffuseTailSoloStructure.lean` has entry
  `r_p({q}) - r_p({p})`.  Thus the follow-up's `B_p` and `B_q` really are the
  relevant off-diagonal normalized solo entries.

The nearby checked results do **not** already prove the clock-ratio theorem:

- `normalizedSoloMatrix_eq_zero_of_fencedSoloWindows` assumes recurrent
  charged solo windows with spectator fences.  It is neither the displayed
  two-clock recurrence nor a theorem about an everywhere-interior Zeno tail.
- `QuittingForwardExactCapTail.totalHazard_summable` in
  `Research/Quitting/ForwardExactCapTailFlow.lean` starts from a structure
  already carrying summable absorption and develops normalized flow.  It does
  not derive summability from the two terminal-reward differences.
- The reviewed conditional result in
  `notes/GATE_STRENGTHENER__TWO_CLOCK_CROSS_SHARE_RIGIDITY.md` assumes
  conditioned-mesh and aligned cross-share data and forces zero normalized
  solo entries.  The corrected result treats the opposite Zeno regime: a
  nonzero entry produces a fixed clock ratio and summable raw hazards.
- The example-specific limits `activeState_a_tendsto_zero` and
  `activeState_b_tendsto_zero` in
  `Research/Quitting/FinFourMaximalRayZeroMinimumRegressions.lean` do not state
  the generic recurrence or classification.

By contrast, the maximal-orbit tail material is already covered.  For
`QuittingMaximalCapSemanticPrefixRayStall`, the declarations

- `summable_absorption`,
- `absorptionTailSum_tendsto_zero`,
- `finiteAbsorptionTail_le_tailSup`, and
- `absorptionTailSup_tendsto_zero`

in `Research/Quitting/MaximalCapSemanticPrefixReturn.lean` prove the
summability and uniform vanishing of all sufficiently late finite absorption
blocks.  `weightedAbsorption_hasSum` proves the corresponding debt-weighted
telescope.  The same facts and the noncollapsing paid/atom/reset orbit are
already recorded in
`formalized/FIN4_FORCED_PAIR_MAXIMAL_PREFIX_RAY_DICHOTOMY.md` and
`notes/CHATGPT_EXTERNAL__NONCOLLAPSING_MAXIMAL_PAID_RESET_ORBIT.md`.
Equation (11) is the elementary product-union bound applied to those checked
tail sums; equation (12) is essentially the existing tail-sup theorem.  They
are not fresh conjecture-facing results.

## Check of the clock-ratio proof

Assume that after a fixed cutoff only `p` and `q` can Quit, with live-history
Quit probabilities `a_t,b_t` in `(0,1)`, and that `v_t` satisfies the exact
Bellman recursion and exact endpoint-Nash condition.  For player `p`, strict
mixing gives

```text
v_t(p) = (1-b_t) r_p({p}) + b_t r_p({p,q})
```

from the Quit endpoint and

```text
v_t(p) = (1-b_t) v_{t+1}(p) + b_t r_p({q})
```

from the Continue endpoint.  Subtracting `s_p=r_p({p})` gives equations (1)
and (2).  Applying (1) at `t+1` and substituting proves

```text
(1-b_t) b_{t+1} A_p = b_t (A_p-B_p).
```

The symmetric formula for `q` is identical.  If `A_p=0`, equations (1) at
two consecutive dates and (2), together with `b_t>0`, give `B_p=0`.  If
`A_p != 0`, division is legal and yields

```text
b_{t+1} = rho_p b_t/(1-b_t),
rho_p = (A_p-B_p)/A_p.
```

Positive consecutive hazards imply `rho_p>0`.  If also `b_t -> 0`, then
`rho_p>=1` would make the sequence nondecreasing, so `rho_p<1`.  An eventual
geometric upper bound follows, hence `sum b_t<infinity`.  The symmetric
argument proves summability of `a_t` when `B_q` is nonzero.

If both off-diagonal entries are nonzero, both hazard sequences are summable.
Because every factor is strictly positive and the tails are eventually small,

```text
product_t (1-a_t)(1-b_t) > 0.
```

This is exactly the probability, conditional on reaching the stated cutoff,
that the prescribed two-clock tail never absorbs.  Thus the positive-Never
conclusion is correct.

The symmetric example with

```text
A_p=A_q=-1,  B_p=B_q=-1/2
```

has `rho_p=rho_q=1/2` and reproduces
`h_(t+1)=h_t/(2(1-h_t))`.  This is the exact counterexample already exhibited
in `feedback/HARD_RESIDUE__BY_GATE_FALSIFIER.md`; the general classification
extracted from it is the fresh part.

## Probability and deviation scope

The result is a statement about the prescribed product roots along the unique
live history.  The all-Never probability is a stopping-law probability for
that prescribed tail.  It is positive conditionally on reaching the cutoff;
an unconditional statement about a larger profile additionally needs positive
reach to the cutoff.

The theorem uses exact **endpoint** Nash conditions only.  It does not show
that the infinite profile is a terminal Nash profile, does not identify
`v_t` with its actual terminal payoff when the Never boundary has nonzero
value, and does not control an unrestricted behavioral deviation.  The
follow-up mostly respects this distinction.  Any Lean-facing or exported
statement should state it explicitly and avoid calling the annotation a
terminal cap or behavioral best-response value.

## Corrections needed even for an internal standalone statement

1. State the cutoff and the conclusion conditionally on reaching it.  If the
   desired conclusion is positive unconditional Never mass in a containing
   profile, add a positive cutoff-reach hypothesis.
2. Define the root sequence as behavioral live-history product actions, so
   the product in equation (9) is visibly the prescribed tail's all-Never
   probability.
3. Keep the Bellman annotation separate from actual terminal payoff and from
   the unrestricted cap.
4. Replace “cumulative root charge and total weighted absorption” after
   equations (11)--(12) by the precise quantities.  Equation (12) is an
   unweighted absorption tail; equation (11) bounds finite-window absorption
   probability.  Debt-weighted absorption is separately covered by
   `weightedAbsorption_hasSum`.  Exact cap-Nash root defect itself is zero, so
   “root charge” is otherwise ambiguous.
5. Separate the new clock-ratio theorem from the already-reviewed maximal
   paid/reset orbit and its checked late-tail estimates.

## Conjecture-facing effect

The theorem explains exactly why the falsifying two-clock chronology is not a
small error: negative off-diagonal solo entries select a geometric decay ratio
and force a positive-survival phantom boundary.  That is useful structural
information.  It does not eliminate the two-clock branch, produce that branch
from arbitrary hard-residual data, consume positive Never mass, or answer a
maintained closure question.  Under the export criteria it remains a local
lemma with an open source hypothesis and an open consumer.
