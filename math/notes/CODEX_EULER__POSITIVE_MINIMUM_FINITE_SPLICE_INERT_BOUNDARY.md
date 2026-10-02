# Positive-minimum finite splicing returns to the inert boundary

Author: `CODEX_EULER`

Status: **proved ordinary-mathematics compactness screen; independent review
requested.**  The cap-tight branch produces actual finite-deadline profiles
converging to the same positive minimum semantic point, but those profiles
remain uniformly non-Nash and their freshly selected `Fin 4` paid cap ports
are eventually literal inert stalls.  The complementary branch retains a
positive `Never`-mass times player-deleted-survival obstruction.  Thus finite
splicing does not regenerate the paid descent, consume the inert port, or
construct terminal approximants.

## 1. Exact question

Let `reward` be a quitting reward table on `Fin 4`.  Assume that the game has
no uniform-equilibrium payoff.  Choose the **strict minimum plateau selected
by**
`exists_finFour_strictMinimumPlateau_openDebtHomotopyTube_of_no_uniformPayoff`,
and write

```text
X_* = (U_*,B_*) in quittingTerminalSemanticCarrier reward
```

It minimizes total terminal-semantic debt and has the reviewed open
all-Continue tube.  Write

```text
D_* = quittingTerminalSemanticDebtSum X_* > 0.
```

Choose actual behavioral profiles `sigma_n` such that

```text
Sem(sigma_n) -> X_*.
```

The narrow question tested here is whether escaping temporal mass in these
profiles can be recentered or finitely spliced to produce one of the outputs
needed by `PAID_ADMISSIBLE_PAYOFF_NEAR_RETURN`:

1. terminal approximate Nash profiles;
2. an actual semantic source below `D_*`; or
3. an actual regenerated paid port which is not the same inert stall.

The answer from the current finite-splice interface is negative.  Its exact
alternative is recorded below.

## 2. The one-player splice modulus

Fix an actual profile `sigma`, a mover `i`, and abbreviate the mover's live
hazard by `h`.  For a cutoff `N`, the checked dimensionless error is

```text
E(sigma,i,N)
  = LateFiniteMass(h,N)
    + NeverMass(h) * MaxPairDeletedSurvival(sigma,i,0,N).       (2.1)
```

The terminal cutoff of `(2.1)` is

```text
c(sigma,i)
  = NeverMass(h) * MaxPairDeletedSurvivalLimit(sigma,i,0).      (2.2)
```

These are exactly `quittingFiniteSpliceError` and its limit in
`TerminalSemanticStoppingLawFiniteSplice.lean`.  The maximum is over the
observer deleted together with the mover.  That deletion is essential: it is
what makes the comparison uniform over every behavioral deviation of every
observer.

If `sigma^[i,N]` denotes the profile obtained by moving all of `i`'s stopping
mass after `N`, including `Never`, to date `N`, then for every observer `j`
and reward bound `M`, the checked estimates give

```text
|U_j(sigma)-U_j(sigma^[i,N])| <= 2 M E(sigma,i,N),
|B_j(sigma)-B_j(sigma^[i,N])| <= 2 M E(sigma,i,N),             (2.3)
|D_j(sigma)-D_j(sigma^[i,N])| <= 4 M E(sigma,i,N).             (2.4)
```

The cap coordinate in `(2.3)` is the unrestricted behavioral best-response
envelope, not a pure-time or stationary cap.

The checked diagonal selection
`exists_finiteSpliceCutoffs_tendsto_zero_of_capTight` says that, along a
sequence, if `(2.2)` tends to zero, cutoffs tending to infinity can be chosen
so that `(2.1)` tends to zero.

## 3. Four-player finite-splice alternative

Choose an order `i_0,i_1,i_2,i_3` of `Fin 4`.  Starting from
`sigma_n^0=sigma_n`, try to cap the four players successively.  At stage `k`,
pass to a subsequence on which the bounded nonnegative quantity

```text
c_n^k = c(sigma_n^k,i_k)                              (3.1)
```

converges.  There are two alternatives.

### Theorem 3.1 (finite splicing or an essential deleted-clock obstruction)

At least one of the following holds after subselection.

1. **Essential temporal escape.**  At some stage `k` there is `kappa>0` such
   that

   ```text
   NeverMass(i_k's law in sigma_n^k)
     * MaxPairDeletedSurvivalLimit(sigma_n^k,i_k,0) >= kappa   (3.2)
   ```

   for every remaining `n`.

2. **Full finite splicing.**  There are recursively chosen cutoffs
   `N_n^k -> infinity` and actual profiles

   ```text
   sigma_n^{k+1} = (sigma_n^k)^[i_k,N_n^k]
   ```

   such that

   ```text
   Sem(sigma_n^4) -> X_*                              (3.3)
   D(Sem(sigma_n^4)) -> D_*.                          (3.4)
   ```

   Every prescribed player law in `sigma_n^4` quits surely by its finite
   cutoff.

#### Proof

At stage `k`, compactness of `[0,1]` gives a convergent subsequence of
`c_n^k`.  If its limit is positive, shrink it to obtain `(3.2)`.  If its
limit is zero, apply
`exists_finiteSpliceCutoffs_tendsto_zero_of_capTight` and define
`sigma_n^{k+1}` using the returned cutoffs.  Equations `(2.3)` show that both
coordinates of the semantic pair change by a quantity tending to zero.
There are only four stages, so the triangle inequality gives `(3.3)`.
Equation `(2.4)`, or continuity of total debt applied to `(3.3)`, gives
`(3.4)`.

The capped hazard is unchanged before its cutoff, quits surely at the cutoff,
and Continues afterwards.  Later stages change other players only.  Hence
every final prescribed law is proper and supported before its finite cutoff.
`QED`

This is an exhaustive screen for the proposed player-by-player finite-splice
compactification.  Alternative 1 is not merely ordinary late mass: it is
late `Never` mass which remains visible against some player-deleted opponent
clock, exactly the term needed to control unrestricted envelopes.

## 4. The full-splice branch is not a terminal approximation

### Corollary 4.1

In Theorem 3.1(2), the fully capped profiles remain a fixed positive distance
from terminal Nash.  More precisely, no sequence `epsilon_n -> 0` can satisfy

```text
(quittingGame reward).IsεAsymptoticNash
  (quittingTerminalPayoff reward) epsilon_n sigma_n^4.         (4.1)
```

#### Proof

If `(4.1)` held, the checked theorem
`quittingTerminalSemanticDebtSum_le_card_mul_of_isEpsilonAsymptoticNash`
would give

```text
D(Sem(sigma_n^4)) <= 4 epsilon_n -> 0,
```

contradicting `(3.4)` and `D_*>0`.  Quantitatively, for every sufficiently
large `n`, at least one player has semantic debt at least `D_*/8`: eventually
the total is at least `D_*/2`, and there are four coordinates.  `QED`

Thus moving all temporal mass to finite dates does not produce the terminal
approximants requested by the main conjecture.  The cutoffs diverge with `n`;
there is no common compact finite horizon.

## 5. Fresh paid-port regeneration returns to literal inertness

Every `sigma_n^4` is an actual behavioral profile.  Under the fixed terminal
exploitability witness, the checked actual-profile adapter therefore selects
a new full-gap paid first-disagreement row and a same-source paid cap port at
each `sigma_n^4`.  This is genuine fresh source provenance; no paid row is
claimed to survive the four splices.

The independently reviewed Fin4 theorem in
[`CODEX_EULER__FIN4_EVENTUAL_LITERAL_INERT_MINIMUM_APPROXIMATION.md`](CODEX_EULER__FIN4_EVENTUAL_LITERAL_INERT_MINIMUM_APPROXIMATION.md)
applies to any actual sequence whose semantic pairs converge to the selected
strict minimum plateau.  Combining it with `(3.3)` gives:

### Corollary 5.1 (regenerated ports are eventually inert)

For all sufficiently large `n`, the freshly selected paid cap port at
`sigma_n^4` is a literal `InertStall`:

```text
totalAbsorption = 0,
capDisplacement = 0,
every outer cap root = all Continue,
every finite cap prefix has semantic pair Sem(sigma_n^4).      (5.1)
```

Its full-gap paid row persists in the unchanged suffix with unit outer reach,
but no outer root supplies an absorption event on which to pay that row.

This is the exact conjecture-facing implication of Theorem 3.1.  Full finite
splicing does regenerate actual paid sources, but it returns them to the same
inert boundary.  It supplies neither a lower-debt source nor a charged return.

## 6. Why minimum debt gives no sign improvement

For every actual finite splice, global minimality gives only

```text
D_* <= D(Sem(sigma_n^{k+1})).                         (6.1)
```

The symmetric estimate `(2.4)` shows closeness, not descent.  Its direction
cannot be reversed.  In particular, cap-tightness plus `(6.1)` only proves
that the capped source is another minimum-approaching source.

If cap-tightness fails, `(3.2)` prevents `(2.3)--(2.4)` from tending to zero.
No current inequality converts `(3.2)` into outer cap-root absorption,
terminal Nash error tending to zero, or a paid Bellman edge.  The surviving
quantity is a complete-law/player-deleted clock interaction, not a semantic
debt decrement.

This agrees with, but is distinct from,
[`CODEX_RAMSEY__POSITIVE_MINIMUM_ATTAINMENT_COMPLETION_SCREEN.md`](CODEX_RAMSEY__POSITIVE_MINIMUM_ATTAINMENT_COMPLETION_SCREEN.md).
That note excludes the one-singleton Fermat escape by the Fin4 uniform
singleton gap and isolates the unrestricted cap surcharge of a weak
completion.  The present theorem analyzes the exact finite-splice route:
cap surcharge is controlled precisely in the cap-tight branch, yet that
branch still regenerates only eventually inert positive-debt sources.

## 7. Exact obstruction and stop condition

The attempted attainment route ends in the following sharp boundary:

```text
positive-minimum actual approximants
  -> essential Never x pair-deleted-survival mass
     or finite-deadline actual approximants with D -> D_*
        -> freshly selected full-gap paid ports
        -> eventual literal inert stalls.                         (7.1)
```

Neither output in `(7.1)` meets a maintained consumer.  Any continuation must
add one genuinely new implication:

```text
Never x pair-deleted-survival >= kappa
  -> terminal approximation / charged return / maintained rank drop,
```

or consume the literal inert marked row itself.  Recentring, finite capping,
and reapplying the actual-profile port do not do so.  I therefore stop this
attainment lane here rather than repackage the same inert port.

## 8. Sources and nonclaims

Checked declarations inspected:

- `quittingFiniteSpliceError`,
  `tendsto_quittingFiniteSpliceError_terminal`,
  `exists_finiteSpliceCutoffs_tendsto_zero_of_capTight`,
  `abs_quittingTerminalPayoff_finiteCap_sub_le`,
  `abs_quittingContinuationBestResponseValue_finiteCap_sub_le`, and
  `abs_quittingTerminalSemanticDebt_finiteCap_sub_le` in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/TerminalSemanticStoppingLawFiniteSplice.lean`;
- `exists_finiteSpliceCutoffs_mixtureNash_markedEvent_of_capTight` in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/TerminalSemanticStoppingLawFiniteSpliceNashification.lean`;
- `quittingTerminalSemanticDebtSum_le_card_mul_of_isEpsilonAsymptoticNash`
  in `UniformEquilibrium/Diagnostics/Quitting/OneActiveAlignedRankCollapse.lean`;
- `HasTerminalExploitabilityGap.nonempty_actualProfilePaidCapPort` and
  `HasTerminalExploitabilityGap.nonempty_actualProfilePaidCapMinimumApproximation`
  in the actual-profile paid-cap endpoint files; and
- `exists_open_exactAllContinueTube_debtHomotopy` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinFourStrictMinimumPlateauIsolation.lean`.

The finite-splice statements are Lean checked.  The four-stage composition
and its eventual-inert corollary are ordinary mathematics pending independent
review.

This note does **not** prove that a positive minimum is behaviorally attained,
that alternative `(3.2)` occurs in every nonattained sequence, or that it is
impossible.  It does not preserve one marked paid row through all four caps,
identify observers across stages, lower total debt, create an exact Bellman
edge, or prove a uniform-equilibrium payoff.
