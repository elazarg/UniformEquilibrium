# Observable closure under feedback, and the memory obstruction

Author: CODEX_LARCH. Internal theory-finding sketch, 2026-09-07.
Status: elementary proofs below passed
[independent review](../feedback/CODEX_LARCH__OBSERVABLE_FEEDBACK_CLOSURE_AND_MEMORY__BY_CODEX_LARCH_OBSERVATION.md)
with no unresolved objection; not Lean-checked.
This concerns reusable controlled-process mathematics, not a UE proof gap.

## Question and relation to the code

When does a small linear space of observables remain sufficient after
controllers can choose actions separately at each state? Is that enough
when controllers can remember discarded states?

The [finite-observable transport note](CODEX_LARCH_ROUND2_OBSERVATION__FINITE_OBSERVABLE_CLOSURE_FOR_RESIDUAL_TRANSPORT.md)
uses a particularly strong and useful condition: every action has the SAME
effect on retained observables. It consequently allows arbitrary adaptive
controls. If we instead want to retain differing action responses, mere
invariance of a space is a different claim, with different information needs.

Two bounded source neighborhoods expose the distinction:

- `finiteAveragePayoff_scheduledPlayerOwned_le_of_invisible`
  (`UniformEquilibrium/VanishingDiscount/Analytic/PlayerOwned/InvisiblePlayerOwnedDeviationBoundary.lean`)
  uses action-row equality after every public history. It does not infer
  history-law equality from state-law equality.
- `IsStronglyLumpable`, `adaptiveMarkovStep_map_of_stronglyLumpable`, and
  `QuotientGluingInterface.liftStep_map_fst`
  (`MathUE/Probability/QuotientShadowLift.lean`) separate a supplied Markov
  quotient from the stronger all-history `controlled_quotient` hypothesis.

The proposed theory explains exactly why these interfaces differ. A bounded
search for row-switch, feedback-invariant, indicator-invariant, and
history/lumpability formulations did not locate the criterion below. This is
not an exhaustive novelty claim; its ingredients are elementary linear
algebra and controlled Markov chains.

## 1. Exact criterion for arbitrary state feedback

Let S be finite. At each state s let A_s be a finite nonempty action set
with transition rows q_(s,a). Supply a baseline stochastic matrix P whose
row P_s belongs to conv{q_(s,a):a∈A_s}. A stationary randomized feedback
matrix K independently selects K_s in this convex hull at each state.
Let W be a linear subspace of ℝ^S containing the constant function 1.
Write e_s for the indicator of the singleton {s}.

**Feedback-closure theorem.** Every such K maps W into W if and only if:

    P W ⊆ W,
    for every s, either e_s∈W, or
       (q_(s,a)−P_s)·w=0 for every a∈A_s and w∈W.       (1)

Proof of necessity: P is itself allowed. Replace just its row at s by
q_(s,a); the resulting matrix is also allowed. Its difference from P acts as

    w ↦ e_s [(q_(s,a)−P_s)·w].                         (2)

If any bracket is nonzero, invariance and linearity force e_s∈W.
Otherwise the row-annihilation alternative holds. For sufficiency, K−P is
a sum of row operators of the form (2), with convexly averaged brackets.
Each term lies in W under (1), and so does Pw.

Thus a state at which control visibly changes a retained prediction must
have its own singleton indicator retained. States not individually retained
must have observationally invisible control. The theorem depends on being
allowed to switch rows independently; it does not apply to a constrained
controller that must use one common action at all states.

## 2. A finite minimal closure algorithm

For desired outputs F, start with W_0=span({1}∪F). Iterate

    W_(n+1)=W_n+P W_n+Σ_(s,a) D_(s,a) W_n,
    D_(s,a)=e_s⊗(q_(s,a)−P_s).

After at most |S| strict rank increases this stabilizes. The result is the
smallest space containing F and constants that is invariant under every
stationary randomized feedback matrix. The proof follows directly from
(2) and closure under the listed linear maps.

This avoids enumerating the product of all local action choices. It also
gives a diagnostic trace: adding an observable may expose one state's
control, force its indicator into the space, and then expose more states
after baseline propagation. An apparently small prediction space can
therefore expand to the full state space for an identifiable algebraic
reason, rather than because of an unsuccessful numerical approximation.

Products K_0⋯K_(T−1) preserve the final W. Consequently two initial laws
agreeing on W give the same expected final outputs under each common
time-dependent Markov policy. This assertion concerns a fixed common policy
for both initial laws, with actions depending on current state and date.

## 3. Full memory defeats this conclusion

The preceding equivalence need not hold for the SAME policy allowed to
remember the full state history. Here is a four-state exact example.

Let S={a,b,c,d}. Baseline transitions send a and b to c; c stays c and d
stays d. Only c has a second action, which sends it to d. Let

    W=span{1,e_c,e_d}.

Baseline propagation sends e_c to 1−e_d and e_d to e_d. The only nonzero
action-row difference is at c, whose indicator belongs to W. Thus (1)
holds and all feedback matrices preserve W. Initial laws δ_a and δ_b agree
on W; every common time-dependent Markov policy gives them identical
observable expectations.

Now use one common history policy: at date 1 in state c, take the action
to d exactly when the initial state was a. At date 2 the observable e_d
equals 1 from initial a and 0 from initial b. Both initial histories have
the same compressed history ({a,b},c), so this policy does not descend to
the quotient. Remembered information, not a faulty stochastic transition,
breaks the claim.

Indeed W is already the full function algebra on the partition
{{a,b},{c},{d}}. Even a genuine partition quotient and strong lumpability
for every Markov feedback matrix do not imply preservation of every
full-history policy under the same policy identifier.

## 4. What survives, and what is not claimed

There are three distinct valid packages:

1. **Action-invisible linear observables.** All action rows agree on W.
   Arbitrary history-dependent choices preserve its expected predictions,
   as in the reviewed transport lemma.
2. **Feedback-invariant linear observables.** Condition (1) holds.
   Markov-policy compositions descend on distribution classes; full-history
   equivalence requires additional information hypotheses.
3. **An actual partition and quotient-adapted policies.** If transition
   kernels commute with the partition for each admissible action, and the
   policy reads only the quotient history, the controlled history kernel
   commutes as well. This supplies the kind of `controlled_quotient`
   condition already required by the source lifting theorem.

The counterexample concerns response preservation for each SAME policy.
It does not show different optimal values from a and b: both starts can
reach d using a suitable Markov policy. Optimizing over policies and
preserving a common response map are different mathematical requirements.
No claim is made here about minimal quotients for unrestricted-memory
response maps, or about independent-player realization after compression.

## Assessment

This is an extension of the controlled-observability candidate, not a third
unrelated grand theory. Its concrete contributions are the row-switch iff
criterion, a finite minimal closure construction, and an exact separation
between Markov closure and history-compatible compression. Their value is
explaining and organizing hypotheses already distributed across the code.

The independent review checked (1), the closure construction, and the
four-state example. A next consolidation question is which existing
compression interfaces require only Markov closure and which explicitly
require quotient-adapted histories. No UE source producer, Lean change, or
export is sought.
