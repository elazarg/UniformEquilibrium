# Actual paid first-disagreement suffix compactification

Author: `CODEX_MINER`

Status: **independently reviewed/PASS at the stated internal scope; no export
recommendation.**  Review:
[`CODEX_RAMSEY`](../feedback/CODEX_MINER__ACTUAL_PAID_FIRST_DISAGREEMENT_SUFFIX_COMPACTIFICATION__BY_CODEX_RAMSEY.md).
The literal first-disagreement
clock can be deleted without losing the full gap.  After finite-label and
compact subsequence selection this gives a time-zero marked relaxation over a
minimum semantic point, unless the reached suffix stays a fixed debt distance
above the minimum.  The latter is a genuine actual-profile excursion, but no
inspected charged, support-rank, or paid-path consumer closes it.  It can be
fed source-matched into a new paid cap port, whose terminal-gap dispatch is
again quantitative descent or literal inert stall; excess debt does not
exclude the inert arm or bound the descent scale below.  The exact
missing datum is full live reach: the checked lower bound controls only the
opponents' deleted survival.  A two-player realizable regression shows that
the observer's own survival can tend to zero even with a unit behavioral gain,
a unit paid row, and both selected witnesses in their literal stopping-law
supports.

This note does not claim a counterexample under the positive-global-minimum
hypothesis.  Its negative conclusion is scoped to the currently checked
interfaces and to the proposed inference from paid-row live mass alone.

Audit performed at repository head `fed7258`.

## 1. Question and checked source

Fix a finite player type, terminal reward table `reward`, a terminal gap
`Gamma>0`, and a positive global semantic-debt minimum

```text
D_* = D(minimum)>0.
```

Let

```text
P : QuittingActualProfilePaidCapMinimumApproximation
      reward minimum Gamma.
```

Write `sigma_n=P.profile n`, and write `r_n` for the paid row stored in
`(P.actual n).source`.  Its observer, first-disagreement date, orientation,
relative later time, deleted live mass, and reached gain are denoted by

```text
o_n, s_n, b_n, d_n, ell_n, g_n.
```

The checked equalities `source_profile` and `source_gain` are important:
`r_n` is a row on the literal profile `sigma_n` and has gain exactly `Gamma`.
This is not a row selected at an unrelated carrier approximation.

The primary files inspected were:

- `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/`
  `ActualProfilePaidCapMinimumApproximation.lean`, especially
  `QuittingActualProfilePaidCapMinimumApproximation` and
  `HasTerminalExploitabilityGap.`
  `nonempty_actualProfilePaidCapMinimumApproximation`;
- `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/`
  `ActualProfileTerminalGapPaidCap.lean`, especially
  `exists_supported_pureTimePayoff_sub_at`,
  `exists_paidFirstDisagreementRow_at`, and
  `QuittingActualProfileTerminalGapPaidCapPort`;
- `UniformEquilibrium/Diagnostics/Quitting/`
  `TerminalSemanticPaidFirstDisagreement.lean`;
- `UniformEquilibrium/Quitting/Paths/SurvivalWeightedSuffixRegret.lean`;
- `UniformEquilibrium/Diagnostics/Quitting/Frozen/`
  `ConditionedActualProfilePacket.lean`;
- `UniformEquilibrium/Quitting/Paths/SurvivalPrefixBridge.lean`;
- `UniformEquilibrium/Diagnostics/Quitting/`
  `TerminalSemanticResetReprojectionWindow.lean` and
  `TerminalSemanticReachedRowDebtLocalization.lean`;
- `UniformEquilibrium/Diagnostics/Quitting/`
  `TerminalSemanticPaidFirstDisagreementOrientation.lean`;
- `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/`
  `PaidCapPortExactTrichotomy.lean` and
  `NormalizedCurvatureStrategicDispatch.lean`;
- `UniformEquilibrium/Diagnostics/Quitting/`
  `TerminalSemanticStrictTailEscapeReturn.lean`, especially
  `strictTailEscape_allContinue_stalls`; and
- `UniformEquilibrium/Diagnostics/Quitting/`
  `PaidFirstDisagreementPayoffNearReturn.lean`.

The closest prior note is
[`CODEX_RAMSEY__NORMALIZED_PAID_MARK_COMPACTIFICATION_NO_GO.md`](CODEX_RAMSEY__NORMALIZED_PAID_MARK_COMPACTIFICATION_NO_GO.md).
It already shows that absolute witness times are noncompact and that a
projective marked state can retain an inert all-Continue fixed point.  The new
points here are the exact normalization of the newly checked *actual
minimum-approximating* rows, the resulting compact time-zero relaxation, and
the separate observer-survival denominator which can still vanish after the
clock has been normalized.

## 2. The deleted live mass has a uniform floor

Let `R=quittingRewardBound reward`.  The row field `gain_le_liveMass` gives

```text
Gamma <= 2 R ell_n.                                  (2.1)
```

Since `Gamma>0`, `(2.1)` first implies `R>0`, and hence

```text
ell_n >= Gamma/(2R)>0.                               (2.2)
```

The row also gives

```text
Gamma <= ell_n g_n.                                  (2.3)
```

Opponent survival lies in `[0,1]`.  Thus `(2.3)` implies `g_n>0` and

```text
g_n >= Gamma.                                        (2.4)
```

No division by a possibly zero reach is hidden here.  This is exactly the
reason the division-free row estimate is useful.

## 3. Exact deletion of the common clock

Define the actual reached suffix profile

```text
tau_n = quittingAllContinueProfileSpine reward sigma_n s_n.  (3.1)
```

`quittingBehaviorLiveHazard_allContinueProfileSpine_eq_shift` identifies its
literal hazards with the shift by `s_n`.  Rebase the two witnesses by deleting
that common delay.  One witness is now `some 0`; the other is the same relative
later time `d_n`.  Keep the same orientation `b_n`.

### Proposition 3.1 (source-matched normalized paid row)

For every `n`, `tau_n` has a paid first-disagreement row for `o_n` with

```text
start             = 0,
later             = d_n,
receivingEarlier  = b_n,
liveMass          = 1,
reachedGain       = g_n,
gain              = Gamma.                           (3.2)
```

In particular this is still a full-`Gamma` row.

**Proof.**  The chronology in `r_n` says that its two absolute witnesses are
`some s_n` and `quittingAbsolutePureTime s_n d_n`, in the order specified by
`b_n`.  Shift identity turns them into `some 0` and `d_n`.  Opponent survival
from zero to zero is one.  The exact first-disagreement decoder therefore
turns the original local expression defining `g_n` into the difference of
the two pure-time payoffs on `tau_n`, with no factor `ell_n`.  Equation `(2.4)`
supplies `Gamma<=1*g_n`; the division-free live-mass field follows from
`Gamma<=2R`, itself a consequence of `(2.1)` and `ell_n<=1`.  All remaining
fields are the shifted chronology and `r_n.later_strict`. `QED`

This proposition removes the escaping *common clock*.  It does not assert
that a limit of the relative later times exists in `Option Nat`.

There is also an API distinction worth preserving.  The proof of
`exists_supported_pureTimePayoff_sub_at` knows that the source witness lies in
the prescribed stopping-law support and the receiving witness lies in the
chosen deviation's support.  `QuittingPaidFirstDisagreementRow` and
`QuittingActualProfileTerminalGapPaidCapPort` do not retain those two proofs.
They can be retained by rebuilding the producer, but they cannot be projected
from an arbitrary value of the current structures.

## 4. Compact time-zero marked relaxation

Pass to a subsequence on which `o_n=o` and `b_n=b`; both labels range over
finite sets.  Put

```text
X_n = quittingTerminalSemanticPair reward tau_n,
y_n = quittingProfileLiveRoot reward tau_n 0,
q_n = quittingFixedOpponentsQuitValue reward y_n o 0,
z_n = quittingRootSequenceRelativePureTimeTerminalValue
        reward (quittingProfileLiveRoot reward tau_n) o 0 d_n.
```

The semantic carrier and the finite product root simplex are compact, and
`z_n` is in `[-R,R]`.  A common further subsequence therefore has

```text
X_n -> X,       y_n -> y,       z_n -> z.              (4.1)
```

The coalition polynomial defining the immediate-Quit value is continuous,
so `q_n->q(y)`.  Proposition 3.1 passes to the limit as

```text
b=true  -> q(y)-z >= Gamma,
b=false -> z-q(y) >= Gamma.                            (4.2)
```

Moreover both `q_n` and `z_n` are literal pure-time deviation values on
`tau_n`.  The checked identity
`quittingContinuationBestResponseValue_eq_sSup_pureTimeDeviationPayoff`
therefore gives

```text
q(y) <= X.2(o),             z <= X.2(o).               (4.3)
```

Thus `(X,y,o,b,z)` is a compact **time-zero marked relaxation** with a full
gap.  It is intentionally called a relaxation: if `d_n` escapes, `z` need not
be represented by a pure time against one actual tail realizing `X`, and `y`
need not determine that tail.

Since `X` is in the semantic carrier, global minimality gives `D(X)>=D_*`.
Consequently the common subsequence has the exact alternative

```text
(M)  D(X)=D_*;

(E)  D(X)>D_*, and for eta=(D(X)-D_*)/2>0,
     eventually D(X_n)>=D_*+eta.                       (4.4)
```

Arm `(M)` is the promised compact time-zero marked minimum approximation.
Arm `(E)` is a fixed excursion by actual reached suffix profiles, not merely
an abstract carrier excursion.

## 5. Full reach is not the paid-row live mass

For the original profile define

```text
a_n = product over t<s_n of the probability that o_n Continues at t,
m_n = quittingLiveMass reward sigma_n s_n.
```

The exact bridge
`quittingSurvivalPrefix_eq_opponentSurvivalWeight_mul_own` gives

```text
m_n = ell_n a_n.                                      (5.1)
```

Thus `(2.2)` controls only the first factor.  It gives no lower bound on
`a_n` or on the actual probability `m_n` of reaching the marked row.  If the
support proofs discarded by the present structure are rebuilt, source-witness
support gives `a_n>0` pointwise, but still no uniform positive floor.

There is one useful exact debt relation.  Summing
`quittingLiveMass_mul_spineDebt_le_initialDebt` over the players gives

```text
m_n D(X_n) <= D(Sem(sigma_n)).                         (5.2)
```

Since the right side tends to `D_*`, an excursion
`D(X_n)>=D_*+eta` eventually implies, after making the source error at most
`eta/2`,

```text
m_n <= (D_*+eta/2)/(D_*+eta)
    = 1-eta/(2(D_*+eta)).                              (5.3)
```

So a fixed suffix-debt excursion forces a fixed amount of absorption before
the suffix.  This is honest quantitative information.  It is not a positive
reach floor, a floor-admissible Bellman path, or cap charge.  Combining
`(5.1)` with `(2.2)` only gives the conditional upper estimate

```text
a_n <= (2R/Gamma)m_n,                                 (5.4)
```

which is nontrivial only in a restricted numerical regime.

After one more subsequence, the complete honest split is therefore

```text
(C0) a_n -> 0;

(CM) a_n >= a_0>0 eventually and D(X)=D_*;

(CE) a_n >= a_0>0 eventually and D(X)>D_*.             (5.5)
```

In the last two arms the marked row has macroscopic full reach at least
`a_0 Gamma/(2R)`.  Neither arm, however, supplies the extra sure-Quit,
vanishing-observer-debt, floor, or root-Nash hypotheses of a current consumer.

## 6. Exact realizable conditioning-escape regression

This example isolates `(C0)` after the common clock has already been deleted.
It also shows that retaining the original support proofs does not repair the
uniform reach problem.

Take players `o,p` and rewards

```text
r_{o,p}(o)=1,
every other reward of o is 0,
every reward of p is 0.                               (6.1)
```

Let `epsilon_n>0` tend to zero.  In `sigma_n`:

- `p` Continues through dates `<n` and Quits surely at date `n`;
- `o` Quits at date zero with probability `1-epsilon_n`; conditional on
  continuing, it waits and Quits at date `n+1`.

Both prescribed branches pay `o` zero, while deviating to Quit at date `n`
creates the collision and pays one.  Hence

```text
U(sigma_n)=(0,0),  B(sigma_n)=(1,0),  D(sigma_n)=1.    (6.2)
```

The prescribed stopping law of `o` assigns positive mass `epsilon_n` to
`n+1`, and the pure deviation law assigns mass one to `n`.  Choosing

```text
sourceWitness=n+1, receivingWitness=n
```

therefore gives a supported paid row with

```text
Gamma=1, s_n=n, ell_n=1, g_n=1.                       (6.3)
```

But the observer's own survival and the full live mass are

```text
a_n=m_n=epsilon_n -> 0.                               (6.4)
```

After normalization at `n`, player `p` Quits now and `o` waits one date.  The
normalized profile still has semantic pair `(U,B)=((0,0),(1,0))` and has the
unit time-zero collision-versus-wait mark.  Thus even **no semantic excursion
at all** does not turn the deleted live-mass floor into macroscopic actual
reach.

All Continue is also an exact root Nash response to the displayed cap at this
normalized profile: `o` gets continuation value one and only zero from
quitting alone, while `p` is indifferent at value zero.  Thus the local
normalized paid-row/cap algebra is compatible with an inert first stage.
This observation is still only local, because the table's global minimum is
zero.

The reward table has global minimum debt zero, attained when both players
Quit immediately, and it does not have a global unit terminal gap.  Therefore
this is not a countermodel to the full positive-minimum source theorem.  It is
a realizable falsification of the local implication

```text
full behavioral gain + supported full paid row
+ ell_n >= Gamma/(2R) + exact clock normalization
  -> uniformly positive actual reach.                 (6.5)
```

It differs from the earlier escaping-clock regression: here the clock is
successfully normalized and it is the conditioning denominator of the
marked observer which escapes.

## 7. Exact paid-port regeneration, and why it does not close

Proposition 3.1 does give more than an abstract excursion.  For each `tau_n`,
use its **same normalized row** (same `o_n`, orientation, relative later time,
and reached gain) together with the original positive global minimum to build
a new `QuittingPaidCapLiftedSource`, and choose its checked `SummablePort`.
Thus the actual excursion is accepted by the existing paid-cap machinery
without reselecting an unrelated terminal witness.

The terminal gap rules out `ChargedNearReturn`, so the exact output is

```text
QuantitativeDebtDescent or InertStall.                 (7.1)
```

This is the strongest source-matched regeneration presently available.  It
does not finish arm `(E)`.  `QuantitativeDebtDescent` pays
`D_* rho/(2R)`, but neither the fixed excess `eta` nor the normalized paid row
gives a positive lower bound on `rho`; iterating such real decreases need not
be well founded.  More sharply, being a fixed distance above the minimum does
not contradict `InertStall`: the minimum-fiber contraction inequalities bound
absorption and displacement **above** by source excess, not below away from
zero.  The checked theorem `strictTailEscape_allContinue_stalls` isolates the
same boundary directly: whenever the off-minimum tail cap dominates all
singleton rewards, all Continue is exact cap--Nash, fixes the strict escape,
and fails zero-tolerance return selection.

The remaining narrow declaration audit gives the following exact mismatches.

1. The original port attached to `sigma_n` does not identify the arbitrary
   prescribed prefix from `tau_n` back to `sigma_n` with cap charge or cap
   displacement.  In the minimum approximation those two original-port
   quantities already tend to zero.  The regenerated port at `tau_n` instead
   ends at `(7.1)`.
2. `sum_liveMass_mul_spineOpponentAbsorptionDebtCharge_le_epsilon_add_defect`
   assumes *every* shifted tail through a stopped horizon is near the
   reference minimum and still leaves the occupation sum of local Nash
   defects.  A single endpoint `tau_n` in `(E)` supplies neither premise nor
   conclusion.
3. `exists_fixed_other_reachedRowGain_subsequence` in
   `TerminalSemanticReachedRowDebtLocalization.lean` requires a uniform full
   reach floor, a sure-Quit observer at the actual row, and vanishing initial
   observer debt.  The paid row supplies only deleted reach; its orientation
   concerns a pure-time replacement profile, not necessarily the actual
   root of `sigma_n`.
4. `PaidFirstDisagreementAdmissiblePayoffNearReturnConsumer` requires the
   maintained floor-admissible near-return path and paid-source provenance.
   Neither semantic excursion nor pre-row absorption `(5.3)` constructs that
   path.
5. The two temporal-orientation theorems do produce legal deviations from
   appropriate pure-time replacement profiles (and, with a near-cap witness,
   a fixed outsider endpoint).  Their own module statement correctly says
   that they do not re-enter a reset chord or chronological producer.  A
   terminal gap already guarantees a legal deviation; this is not a closure
   mechanism.

Accordingly the desired strong two-arm claim

```text
normalized suffix near D_*
or fixed suffix excursion entering an existing charged/support/paid consumer
```

does not close through any inspected interface.  What is proved is the
compact alternative `(4.4)`, the exact reach bookkeeping `(5.1)--(5.4)`, the
three-arm boundary `(5.5)`, and the source-matched but non-well-founded
regeneration `(7.1)`.

## 8. Surviving theorem target

The smallest useful strengthening would retain one of the following in the
actual minimum-approximation producer:

1. a uniform lower bound on the prescribed observer's survival to the chosen
   source witness;
2. an exact floor/root-Nash certificate for the literal prefix from the
   reached suffix back to the source; or
3. a consumer converting the fixed pre-row absorption in `(5.3)` into a
   maintained charged edge while preserving the paid observer and suffix.

With (1), the normalized marked row has uniform full reach.  Additional
sure-Quit and debt-localization data would still be needed for the current
reached-row consumer.  With (2) or (3), arm `(E)` could become a genuine
payoff-near-return or descent branch.  Positive global minimum by itself is
used in `(4.4)` and `(5.3)`, but no checked theorem currently turns it into
one of these operational fields.

## 9. Lean handoff if this boundary is formalized

The narrow useful formal packet has three independent declarations.

1. A normalization constructor taking
   `QuittingPaidFirstDisagreementRow reward sigma observer Gamma` to a row on
   `quittingAllContinueProfileSpine reward sigma row.start` with `start=0`,
   `liveMass=1`, the same `later`, orientation, reached gain, and gain.  The
   proof should use the spine hazard shift and the exact relative pure-time
   decoder, not division by `row.liveMass`.
2. The summed debt localization `(5.2)`, obtained by summing
   `quittingLiveMass_mul_spineDebt_le_initialDebt` over `Finset.univ`.
3. An enriched version of
   `HasTerminalExploitabilityGap.exists_paidFirstDisagreementRow_at` retaining
   both stopping-law support proofs.  Its documentation must state that
   support yields only pointwise positive own survival, not a uniform bound.

The compact subsequence theorem is mathematically routine but requires a
purpose-built finite marked carrier for `(X,y,o,b,z)`.  It should not claim
that the scalar `z` is attained by a pure time at the limit.

## 10. Independent review

`CODEX_RAMSEY` checked in particular:

1. the normalized row's exact edge identity and full-`Gamma` inequality;
2. the distinction between deleted opponent survival and full actual reach;
3. the summed debt inequality `(5.2)` and constant in `(5.3)`;
4. every payoff, cap, support, and survival calculation in the regression;
5. the scoped nonclaim concerning positive global minimum; and
6. the consumer-signature audit in Section 7.

The verdict is PASS for the internal compact-relaxation/source-regeneration
scope, with no export recommendation.  The only formal handoff qualification
is that the hazard-shift identity in Proposition 3.1 should be paired with the
exact pure-time common-prefix payoff factorization when written in Lean; this
is not a mathematical objection.
