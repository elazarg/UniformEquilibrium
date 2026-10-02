# Audit of the Fin4 same-source paid/reset cap-port composite

**Reviewer:** `CODEX_RAMSEY`  
**Date:** 2026-08-25  
**Object reviewed:**
[`notes/CHATGPT_EXTERNAL__FIN4_SAME_SOURCE_PAID_RESET_CAP_PORT.md`](../notes/CHATGPT_EXTERNAL__FIN4_SAME_SOURCE_PAID_RESET_CAP_PORT.md)  
**Verdict:** **PASS.**  The proposed composition has no mathematical gap.
Every quantitative cap-lift conclusion is already a named checked theorem.
The only missing item is one convenience wrapper which selects the positive
minimum, paid/reset target, paid row, and cap-lifted source in a single
existential statement.

## 1. Positive global minimum from the terminal witness: PASS

For literal `Fin 4`, the witness supplies

```text
witness.not_exists_uniformEquilibriumPayoff.
```

Applying the forward direction of

```text
not_exists_uniformEquilibriumPayoff_iff_hasPositiveMinimumTerminalSemanticDebt
```

produces one `minimum` with all three fields needed later:

```text
minimum ∈ quittingTerminalSemanticCarrier reward,
∀ candidate ∈ carrier, DebtSum(minimum) ≤ DebtSum(candidate),
0 < DebtSum(minimum).
```

There is no missing compactness or positivity premise.  The inhabitance
required by the equivalence is automatic for `Fin 4` (and is also forced by
the terminal witness in the general theorem).

## 2. Same-profile paid/reset production: PASS

Given pairwise distinct `owner baseFirst baseSecond`, the hypotheses line up
exactly with

```text
QuittingTerminalExploitabilityWitness.exists_finFour_pairBasePaidResetDispatch.
```

It returns

```text
target : FinFourPairBasePaidResetTarget reward witness owner
  baseFirst baseSecond,
returned,
QuittingFixedLawResetDispatch reward minimum target.semanticPair target.mass
  owner baseFirst returned.
```

The target's definitions are literal:

```text
target.profile
  = quittingStationaryProfile reward
      (quittingPersistentBaseRoot {baseFirst,baseSecond} ...),
target.semanticPair = quittingTerminalSemanticPair reward target.profile,
target.mass = quittingTerminalOutcomeMass reward target.profile.
```

On this same profile and complete law, `target.owner_reset` gives zero owner
debt and `target.first_incidence` gives unit owner/base incidence.  Moreover

```text
target.localization.debtor ∈ {baseFirst,baseSecond}
```

and

```text
target.paid_row : Nonempty
  (QuittingPaidFirstDisagreementRow reward target.profile
    target.localization.debtor witness.terminalGap).
```

Thus the paid observer is one of the forced pair and the row has exactly the
full terminal gap.  Classical choice may select the row.  No equality with
the separately returned reset-face pair is claimed or needed.

This last distinction is essential: `target.profile` is simultaneously the
paid-row source, reset **target**, and cap-lift suffix.  The dynamic reset
dispatch starts from `minimum` and returns `returned`; the cap lift does not
start at `returned`.

## 3. Construction of the generic cap source: PASS

The following fields are supplied without additional hypotheses:

```text
minimum    := minimum,
minimum_le := hminimum,
minimum_pos := hminimumPositive,
profile    := target.profile,
observer   := target.localization.debtor,
gain       := witness.terminalGap,
gain_pos   := witness.terminalGap_pos,
row        := Classical.choice target.paid_row.
```

They form a literal

```text
QuittingPaidCapLiftedSource reward.
```

The structure does not require the source prescribed payoff to dominate the
punishment floor, a curvature witness, a source/receiving approximation, or
any reset-dispatch field.  Therefore

```text
QuittingPaidCapLiftedSource.nonempty_summablePort
```

applies directly.

## 4. Profile recursion and relation orientation: PASS

The checked recursion is

```text
x_0 = target.profile,
x_(n+1) = quittingRootThenContinuationProfile reward q_n x_n,
q_n = quittingCapLiftedPrefixRoot reward x_n.
```

Behaviorally, `x_(n+1)` first plays the newly inserted root `q_n`; conditional
on joint Continue it then runs `x_n`.  Hence the old target is the unchanged
innermost suffix after `n` inserted dates.

The Bellman annotation has the tail-to-prefixed-current orientation

```text
b_(n+1) = quittingRootSuccessorPayoff reward b_n q_n.
```

Thus the semantic relation runs `b_n -> b_(n+1)`, while literal play of
`x_(n+1)` encounters the new root before the continuation `x_n`.  The
composite does not reverse either orientation and does not turn the nested
profiles into a forward reset chronology.

The root is available at every stage by

```text
exists_isZeroQuittingRootNash
```

and its exact property is packaged as

```text
quittingCapLiftedPrefixRoot_exactNash.
```

It is exact Nash against the literal profile's unrestricted behavioral cap
`b_n`, not against its prescribed payoff `u_n`.

## 5. Exact debt scaling, summability, and reach: PASS

Let

```text
c_n = quittingStationaryContinueMass q_n,
a_n = quittingRootAbsorptionMass q_n = 1-c_n,
D_n = DebtSum(Sem(x_n)),
D_* = DebtSum(minimum).
```

The coordinatewise cap-Nash transport theorem is summed in

```text
quittingCapLiftedPrefixProfile_debt_succ,
```

giving exactly

```text
D_(n+1)=c_n D_n.
```

Every `Sem(x_n)` is an actual carrier point, so `D_*≤D_n`.  Consequently

```text
D_* a_n ≤ D_n-D_(n+1).
```

The complete finite telescope requested in the composite is already the
conjunction

```text
QuittingPaidCapLiftedSource.partialAbsorption_budget:

D_* Σ_(n<N) a_n ≤ D_0-D_N
  ∧ D_0-D_N ≤ D_0-D_*.
```

The bounded nonnegative partial sums yield
`QuittingPaidCapLiftedSource.absorption_summable`.

The division by `D_0` is legitimate.  The named theorem

```text
QuittingPaidCapLiftedSource.initialDebt_pos
```

derives `0<D_0` from `0<D_*≤D_0`; no extra source-debt hypothesis is being
smuggled into the ratio.

If

```text
S_N = quittingCapLiftedSuffixReach reward target.profile N
    = ∏_(n<N)c_n,
```

then

```text
quittingCapLiftedPrefixProfile_debt_eq_suffixReach_mul
```

is the exact identity `D_N=S_N D_0`, and

```text
QuittingPaidCapLiftedSource.reachFloor_le_suffixReach
```

is exactly `D_*/D_0≤S_N`.  Under the nested profile recursion, `S_N` is the
joint probability that all outer roots Continue and the unchanged target
suffix is entered.

The composite note calls this Continue mass `q_n`.  This is mathematically
correct, but `c_n` is safer notation because the Lean development and the
older packet use `q_n` for the product root itself.

## 6. Arbitrary paid-row transport: PASS, including both orientations and Never

The basic checked identity

```text
quittingPureTimeDeviationPayoff_sub_rootThenContinuation_shift_one
```

quantifies over arbitrary

```text
first second : Option Nat.
```

The shift maps `some t` to `some (1+t)` and maps `none` (Never) to `none`.
Both shifted deviations make the observer Continue through the inserted root,
so their common outer absorbing term cancels and their difference is
multiplied by the observer-deleted Continue mass.  Induction gives

```text
QuittingPaidCapLiftedSource.pureTimePayoff_sub_shift
```

for every finite prefix and every ordered pair of finite/Never witnesses.
Therefore this calculation does not choose an orientation and covers either
the source or receiving witness being earlier, including the case that the
later witness is Never.

The exact decoder produces `ShiftedPaidRow`; its witness equalities identify
the new witnesses with the literal shifts.  The checked methods

```text
ShiftedPaidRow.receivingEarlier_eq,
ShiftedPaidRow.start_eq,
ShiftedPaidRow.later_eq
```

retain the original orientation and relative delay.  In addition,

```text
ShiftedPaidRow.liveMass_eq
```

gives the exact original live mass multiplied by the observer-deleted prefix
reach.

Since observer-deleted reach dominates joint suffix reach, every finite
prefix has a decoded row whose stored gain is exactly

```text
(D_*/D_0) * witness.terminalGap > 0.
```

Its realized payoff difference is at least that stored gain.  This is the
content of `nonempty_shiftedPaidRow`, not an identification of paid live mass
with root absorption.

## 7. Semantic convergence and the all-Continue port: PASS

Summable absorption enters the checked cap port

```text
nonempty_summableChargeAllContinuePort_of_summable_absorption.
```

It supplies cap convergence, every marginal Quit probability tending to
zero, the punishment floor and singleton inequalities at the limit, and an
exact all-Continue cap self-loop.

The parallel literal semantic pairs are handled by

```text
QuittingPaidCapLiftedSource.nonempty_summableSemanticPort.
```

Their cap coordinates converge through the cap port and their nonnegative
debts are antitone, so the prescribed coordinates converge as cap minus debt.
Closedness of the terminal semantic carrier keeps the limiting pair in the
carrier.  Its `selfLoop` field is exactly all-Continue semantic prefix
invariance.

This is a carrier limit of the finite literal profiles.  It is not an actual
infinite behavioral profile that reaches `target.profile` after infinitely
many outer dates.  The composite's wording “terminal-semantic all-Continue
limit port” respects this boundary.

## 8. Comparison with the reviewed packet and current declarations

[`formalized/PAID_CAP_LIFTED_SUMMABLE_PORT.md`](../formalized/PAID_CAP_LIFTED_SUMMABLE_PORT.md)
and its review gave the same mathematical cap/debt/reach/shift/limit package.
The current Lean file
`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/PaidCapLiftedSummablePort.lean`
now checks the formerly new pure-time shift identity, the exact row decoder
with chronology, the semantic-limit wrapper, and `nonempty_summablePort`.

One implementation detail has become simpler: the reviewed prose packet used
the maximal-absorption cap root from the older `Research` development.  The
current checked file chooses an arbitrary exact cap-Nash root at every stage.
All displayed conclusions use only exact cap Nash, so maximality is not a
mathematical premise of this composite.

A narrow declaration search found no existing theorem whose conclusion
simultaneously returns the pair-base paid/reset dispatch and the cap-lifted
summable port.  The component declarations do not merely approximate that
claim; they compose definitionally as above.

## 9. Minimal missing named wrapper and exact nonclaims

The only missing lemma is a source-facing wrapper of the following form:

```text
QuittingTerminalExploitabilityWitness.
  exists_finFour_pairBasePaidResetCapLiftedSummablePort
```

which, from three pairwise distinct labels, chooses:

1. an attained positive global minimum;
2. `target`, `returned`, and the checked fixed-law reset dispatch;
3. a row from `target.paid_row`;
4. the corresponding `QuittingPaidCapLiftedSource`; and
5. a member of that source's `SummablePort`.

For a reusable implementation, the smallest helper definition would be

```text
FinFourPairBasePaidResetTarget.capLiftedSource
```

parameterized by the positive minimum data and choosing `target.paid_row`.
The wrapper then consists only of the positive-minimum equivalence, the
existing reset-dispatch theorem, and `source.nonempty_summablePort`.

No new debt, probability, stopping-time, compactness, or all-behavior lemma is
missing.  The composite still does **not**:

- identify the cap limit or any cap prefix with `returned`;
- turn the summable port into a payoff near-return;
- spend a fixed positive amount of cap-root charge;
- transport curvature near-optimality fields to shifted rows; or
- prove a uniform-equilibrium payoff.

Accordingly this is a correct and useful same-source composition, but its
conjecture-facing open seam remains the already stated discharge/restart of
the summable paid port.
