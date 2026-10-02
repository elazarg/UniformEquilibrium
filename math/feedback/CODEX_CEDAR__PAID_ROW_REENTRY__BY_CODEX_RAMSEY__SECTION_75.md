# Review of Section 75

Reviewer: `CODEX_RAMSEY`

Claim reviewed: a Nash point of the three-free-player induced game with the
singleton owner `d` made sure Quit gives an actual stationary semantic source
whose free coordinates are already at their unrestricted caps and above their
punishment floors.  The uniformly positive singleton-owner floor excess is
therefore concentrated in `d`'s semantic debt.  If `d`'s prescribed payoff is
below its floor, an attained stationary best response repairs `d` with fixed
gain and transfers every remaining floor defect to a free coordinate.

## Verdict

**PASS**, including Corollary 75A, in the explicitly stated semantic-source
scope.  The argument does not produce an exact Nash--Bellman edge or a payoff
return, and the note correctly does not claim either one.

## Audit

### Reselection input

The input from reviewed Proposition 29.2 is exactly the one used here.  For
`F={c,x,y}` and persistent singleton base `{d}`, the full induced binary game
has a nonempty compact Nash set, and the terminal witness gives one constant
`delta>0` such that every point `z` in that set satisfies

```text
K_d(z) >= delta.
```

No boundary-face paid defect or connection from the old paid point is needed
for Proposition 75.  The claim is consequently valid for any reselected
induced Nash point, as stated.

### Free coordinates and unrestricted deviations

After extending `z` by setting `d` to Quit surely, the repeated stationary
profile absorbs at its first date.  If a free player `j` deviates by an
arbitrary history-dependent behavioral strategy, `d` still Quits at that
date, so only `j`'s initial Quit/Continue randomization can affect its payoff.
The two pure initial-action payoffs are precisely the two endpoint payoffs in
the induced binary game.  Its Nash inequality says that the prescribed mixed
action attains their maximum.  Therefore this is not merely a bounded-
controller statement:

```text
B_j(sigma)=U_j(sigma).
```

The minmax upper leg
`quittingPunishmentValue_le_stationaryUnilateralCap` applied to the fixed
opponent row then gives `P_j<=B_j=U_j`.  Thus `(75.2)` and the free-coordinate
part of `(75.4)` have the claimed unrestricted-deviation semantics.

### Owner calculation, including the all-Continue boundary

Let `Q=U_d`, let `beta` be the one-row survival probability of all free
players, and let

```text
N = H/(1-beta)  if beta<1,
N = 0           if beta=1,
```

where `H` is the one-row absorption reward to an always-Continuing `d`.
The exact stationary-cap theorem gives

```text
B_d=max(Q,N).
```

Here the Quit branch equals `Q` because `d` is prescribed sure Quit.  The
floor-priced Continue value is exactly

```text
C_d(P_d)=H+beta P_d=(1-beta)N+beta P_d.
```

This identity remains correct at `beta=1`: then `H=N=0` and both sides equal
`P_d`.

The punishment upper leg gives `P_d<=max(Q,N)`.  If the maximum were `Q`,
then `N<=Q` and `P_d<=Q`, so the displayed convex combination would be at
most `Q`, contradicting `K_d=C_d(P_d)-Q>=delta>0`.  Hence

```text
B_d=N>=P_d,
K_d <= N-Q = B_d-U_d.
```

This proves `(75.3)` without a missing contraction assumption and also
settles the degenerate `beta=1` case.

### Cap-attaining replacement and floor localization

The checked constant-row attainment theorem supplies an actual behavioral
best response of `d`, including at `beta=1`.  Replacing only `d` leaves its
opponent profile fixed, so its cap remains the old `B_d`; its new prescribed
payoff equals that cap.  Consequently its new debt is zero, its payoff is at
least `P_d`, and its gain is at least `delta`, proving `(75.5)`.  This does
not assert that free players retain either their payoff or their cap.  The
note correctly localizes any post-replacement floor damage to those free
coordinates rather than claiming it is small.

For Corollary 75A, the terminal exploitability gap applies to the actual
replacement profile.  Since `d` has zero debt, a coordinate with debt at
least `Gamma` must lie in `F`.  If the new prescribed vector is not floor
safe, its violating coordinate also lies in `F`, because the repaired
owner's payoff is at least `P_d`.  This proves `(75.8)--(75.9)`.

### Corollary 75B

**PASS.**  The strict inequality `K_d>0` already proved that the stationary
cap branch is `N>Q`, so the cap-attaining owner reply may specifically be
chosen as Always Continue.  (At the zero-opponent-absorption boundary this
is the `Never` payoff `N=0`.)  Therefore the repaired profile `tau` is again
a constant product row.

For the free debtor `j`, write `Q_j` for the immediate-Quit endpoint and
`N_j` for the Never endpoint against the fixed stationary opponents.  The
exact stationary cap theorem gives

```text
B_j(tau)=max(Q_j,N_j).
```

If the opponents have positive one-row absorption, solving the stationary
fixed-point equation for `j`'s prescribed constant hazard expresses
`U_j(tau)` as a convex combination of `Q_j` and `N_j`.  If they have zero
absorption, a positive own hazard eventually gives `Q_j`, while zero own
hazard gives the Never value `N_j=0`.  Thus in all cases

```text
|Q_j-N_j| >= B_j(tau)-U_j(tau) >= Gamma.
```

The decoder
`exists_quittingPaidFirstDisagreementRow_of_pureTimePayoff_sub` accepts the
source and receiving pure times in either temporal orientation.  Choose
`some 0` and `none` so the lower endpoint is the source witness and the
higher endpoint the receiving witness.  Its internal first-disagreement
split handles both `Q_j>=N_j` and `N_j>Q_j`; no assumption that the receiving
witness is chronologically later is missing.  Since `Gamma>0` and the debtor
lies in `F`, it yields exactly

```text
Nonempty (QuittingPaidFirstDisagreementRow reward tau j Gamma),
j != d.
```

This is a checked-format behavioral paid row at the repaired stationary
profile, not an exact Nash--Bellman edge or a return path.

## Scope

The output is an actual terminal semantic profile and a literal unilateral
strategy replacement.  It is not a simultaneous exact root, an admissible
Bellman edge, or an exact connector back to the paid boundary point.  In the
floor-safe first arm it supplies a unique-debtor semantic carrier; in the
repair arm it identifies exactly where floor damage can move.  The note's
remaining-obligation paragraph preserves these distinctions.
