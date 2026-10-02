# Large-base stationary semantic handoff

Authors: `CODEX_CEDAR` (semantic handoff) and `CODEX_EULER`
(large-base re-selection adapter)

Independent reviews:
[Section 75 review](../feedback/CODEX_CEDAR__PAID_ROW_REENTRY__BY_CODEX_RAMSEY__SECTION_75.md),
[large-base re-selection review](../feedback/CODEX_EULER__FOUR_PLAYER_SINGLETON_PACKET_DISPATCH__BY_CODEX_RAMSEY__SECTION_29_2.md),
[whole-packet export gate](../feedback/LARGE_BASE_STATIONARY_SEMANTIC_HANDOFF__BY_CODEX_EULER.md)

## Exact statement

Consider a zero-Never quitting game on a four-element player set `I`.  A
nonempty coalition `S` of simultaneous quitters receives the bounded vector
`r(S) in R^I`; if nobody ever quits, the payoff is zero.  Let `P_i` be player
`i`'s terminal punishment value.  For a behavioral profile `pi`, write

```text
U_i(pi) = prescribed terminal payoff,
B_i(pi) = supremum terminal payoff over every unilateral behavioral
          replacement of player i,
d_i(pi) = B_i(pi)-U_i(pi).
```

Assume a terminal exploitability witness of margin `Gamma>0`:

```text
for every behavioral profile pi, some i has d_i(pi)>=Gamma.       (1)
```

Fix a player `d` and put `F=I\{d}`.  Form the finite binary game on the three
players in `F` in which `d` is included surely in the terminal coalition and
each player in `F` chooses Quit or Continue once.  Let `z` be an exact mixed
Nash equilibrium of this induced game; its randomizations are independent.
Extend it to a quitting row `q` by making `d` Quit with probability one, and
repeat `q` at every date to obtain the stationary behavioral profile `sigma`.

Let

```text
Q = U_d(sigma),
beta = probability that every member of F Continues in one q-row,
H = d's expected one-row reward from coalitions of free quitters when d
    itself Continues,
C_d(P_d) = H+beta P_d,
K_d(z) = C_d(P_d)-Q.                                      (2)
```

Suppose that, for some `delta>0`,

```text
K_d(z)>=delta.                                             (3)
```

Then the following conclusions hold.

**Theorem A (one-debtor stationary source).**  For every `j in F`,

```text
U_j(sigma)=B_j(sigma)>=P_j,       d_j(sigma)=0.             (4)
```

For the sure owner,

```text
B_d(sigma)>=P_d,
d_d(sigma)=B_d(sigma)-U_d(sigma)>=K_d(z)>=delta.            (5)
```

Thus `d` is the unique positive-debt coordinate of `sigma`, and `d` is the
only coordinate at which its prescribed payoff can be below punishment:

```text
max_i (P_i-U_i(sigma))_+ = (P_d-U_d(sigma))_+.              (6)
```

**Theorem B (owner repair and outside transfer).**  Replace `d`'s stationary
sure-Quit strategy by Always Continue and call the resulting stationary
profile `tau`.  Then

```text
U_d(tau)=B_d(sigma)>=P_d,
d_d(tau)=0,
U_d(tau)-U_d(sigma)>=delta.                                (7)
```

The terminal gap (1) therefore selects a player `j in F` such that

```text
d_j(tau)>=Gamma.                                           (8)
```

Exactly one of the following two semantic alternatives holds:

```text
(floor-safe outside debt)   U(tau)>=P coordinatewise and a free player j
                            has d_j(tau)>=Gamma;

(free floor damage)         U_j(tau)<P_j for some free player j.             (9)
```

In either alternative, a free debtor `j` satisfying (8) has two deterministic
stopping-time deviations, immediate Quit and Never, whose payoff difference
has magnitude at least `Gamma`.  Orient the lower endpoint as the source and
the higher endpoint as the receiver.  The exact first-disagreement decoder
then gives

```text
Nonempty (QuittingPaidFirstDisagreementRow r tau j Gamma),
j != d.                                                     (10)
```

When the first arm of (9) holds, (10) is a literal paid row based at an actual
floor-safe behavioral profile.  In the second arm it is a literal paid row at
an actual source with a specified free-coordinate floor violation.

**Actual large-base input.**  In the four-player terminal-witness branch, a
checked large persistent-base residual has a two-player base `{c,d}` and two
free players `{x,y}`.  The reviewed large-base re-selection moves `c` into
the free set, so `F={c,x,y}` and only `d` remains in the base.  The full
three-player induced Nash set is nonempty and compact, and `K_d` has a
uniform positive minimum `delta` on it.  Consequently any induced Nash point
supplies all hypotheses above.  The original paid boundary face is used to
choose and orient the labels; the theorem does not assert that the reselected
stationary source is reached from that face.

## Conjecture-facing change

The named obligation is
[`PAID_ADMISSIBLE_PAYOFF_NEAR_RETURN`](../questions/PAID_ADMISSIBLE_PAYOFF_NEAR_RETURN.md).
Before this result, the large-base `2+2` paid-chain branch supplied a finite
reward-table residual but no actual prescribed payoff known to lie in the
punishment-floor box.  The result replaces that unspecific four-coordinate
entrance problem by the exact semantic handoff

```text
large-base paid-chain residual
  -> reselected d-sure stationary source with only debtor d
  -> Always-Continue owner repair
  -> floor-safe outside debtor, or an identified free-coordinate floor loss
  -> literal paid first-disagreement row with observer j != d.               (11)
```

This strictly narrows the large-base paid exit: simultaneous floor failure is
localized first to one owner and, after repairing that owner, entirely to the
three free labels.  The literal paid-row decoder is already reached at the
repaired source.

The result does not answer the maintained near-return question.  Its exact
remaining obligation is to turn the floor-safe arm into a simultaneous exact
punishment-floor Nash--Bellman path with fixed charge and payoff return, or to
repay the explicit free-coordinate floor damage in the second arm along such
an exact path.

## Definitions and assumptions

At every date, all players who have not yet quit simultaneously choose Quit
or Continue.  The first nonempty quitting coalition absorbs the game.  A
behavioral strategy may depend on the player's complete observed history and
may randomize freshly at every history.  A unilateral deviation replaces that
entire strategy.  All terminal payoffs and caps in the statement range over
this unrestricted class.

The induced game is only a finite construction used to select `z`.  Its mixed
profile is a product of the three players' independent Bernoulli actions.
The stationary profiles `sigma` and `tau` repeat their product row with fresh
independent randomization at every live date.  No public correlating device is
used.

For `beta<1`, define

```text
N = H/(1-beta),                                            (12)
```

the payoff to `d` conditional on eventual opponent absorption while `d`
Always Continues.  For `beta=1`, define `N=0`, the zero-Never payoff.  The
owner's stationary cap is `max(Q,N)`.  Formula (2) is equivalently

```text
C_d(P_d)=(1-beta)N+beta P_d,                              (13)
```

including the boundary `beta=1`.

The debt `d_i=B_i-U_i` is different from the floor deficit
`(P_i-U_i)_+`.  Theorem A controls both: free debt is zero and free prescribed
payoff is above punishment.  Theorem B removes the owner's debt but does not
claim that free prescribed payoffs are preserved.

For clarity, a `QuittingPaidFirstDisagreementRow` at source profile `tau`,
observer `j`, and gain `Gamma` records two deterministic quit times in
`Option N` (`none` means Never), their first disagreement date `s`, which
witness quits at `s`, and the strictly later delay of the other witness.  It
also records the opponents' probability `L` of reaching `s` and the oriented
conditional Quit-versus-wait difference `R`, with the exact identity

```text
payoff(receiving witness)-payoff(source witness)=L R,
Gamma<=L R,
Gamma<=2 M L,                                             (17)
```

where `M` bounds terminal rewards.  Thus (10) is a data-bearing, division-free
paid row, not merely the assertion that two pure-time values differ.

## Source correspondence

The checked project interfaces used by the adapter and proof are:

- `paidPure_or_paidMixed_of_actual_largeBase_gap_labels` in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/LargePersistentBaseActualAdapter.lean`;
- `HasLargeBasePaidChainResidual` and `hasLargeBasePaidChainResidual` in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/StrictToggleLargeBasePaidChain.lean`;
- `quittingPersistentBaseRoot_free_purePayoff_le` in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseInducedGame.lean`;
- `quittingSingletonBaseOwnerFloorExcess`, its continuity theorem, and
  `nonempty_quittingSingletonBaseCertificate_of_inducedNash` in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseConcreteGap.lean`;
- `QuittingSingletonBaseCertificate.isUniformEquilibriumPayoff` in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/SingletonBaseSemanticDispatch.lean`;
- `quittingStationaryUnilateralCap_eq_max_div`,
  `exists_quittingTerminalPayoff_update_stationary_eq_cap`, and
  `quittingPunishmentValue_le_stationaryUnilateralCap` in
  `UniformEquilibrium/Quitting/Stationary/MinMax.lean`; and
- `exists_quittingPaidFirstDisagreementRow_of_pureTimePayoff_sub` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPaidFirstDisagreement.lean`.

The exact large-base re-selection and compact positive `delta` are new
ordinary mathematics from Proposition 29.2 of
[`CODEX_EULER__FOUR_PLAYER_SINGLETON_PACKET_DISPATCH`](../notes/CODEX_EULER__FOUR_PLAYER_SINGLETON_PACKET_DISPATCH.md),
independently checked in the review cited above.  The semantic localization,
owner repair, and paid-row handoff are Proposition 75 and Corollaries 75A--B
of [`CODEX_CEDAR__PAID_ROW_REENTRY`](../notes/CODEX_CEDAR__PAID_ROW_REENTRY.md),
also independently checked in the review cited above.

The relevant paper transcription is Definition 2.1 and the stationary /
instant-punishment / sequential architecture surrounding Theorem 3.4 in
`Literature/AshkenaziGolanKrasikovRainerAndSolan2022.lean`.  That material
uses the same unrestricted one-player behavioral-deviation semantics but does
not state a four-player large-base Nash re-selection, a unique-debtor semantic
source, or the paid first-disagreement decoder (10).  No literature theorem is
being re-labelled as the new step.

## Proof

### 1. The free coordinates have their unrestricted caps

Fix `j in F`.  Even after an arbitrary history-dependent behavioral
replacement by `j`, player `d` Quits at date zero with probability one under
`sigma`.  Later actions and off-path histories of `j` are therefore irrelevant.
Only `j`'s initial Quit/Continue randomization can change its payoff.

The two pure initial-action payoffs are exactly the two endpoint payoffs for
`j` in the induced binary game.  Since `z` is an exact Nash equilibrium, its
prescribed mixture attains the maximum of those endpoints.  Hence no complete
behavioral replacement improves on it and

```text
B_j(sigma)=U_j(sigma).
```

The punishment value is the infimum, over opponent profiles, of the same
unrestricted best-reply value.  Evaluating that infimum at the stationary
opponents of `sigma` gives `P_j<=B_j(sigma)`.  This proves (4).

### 2. The owner's excess is actual semantic debt

For `d`, quitting at any finite live date has endpoint value `Q`.  Always
Continuing has value `N`.  Against an i.i.d. stationary opponent row, every
finite pure stopping time gives a convex combination of `Q` and `N`; Never
gives `N` when `beta<1` and gives zero, which is the defined `N`, when
`beta=1`.  Randomized and history-dependent stopping rules cannot exceed the
larger endpoint.  Thus

```text
B_d(sigma)=max(Q,N).                                      (14)
```

The punishment upper leg gives `P_d<=max(Q,N)`.  Suppose the maximum in (14)
were `Q`.  Then `N<=Q` and `P_d<=Q`; by (13),
`C_d(P_d)<=Q`, contradicting (3).  Therefore

```text
B_d(sigma)=N>=P_d.
```

Using (13) once more,

```text
K_d(z)=C_d(P_d)-Q
      <=N-Q
       =B_d(sigma)-U_d(sigma).
```

Together with (3) this proves (5).  Combining (4) and (5) proves (6).

### 3. Repairing the owner transfers the obstruction outside

The preceding strict inequality forces the cap branch `N>Q`, so the cap is
attained specifically by Always Continue, including the `beta=1` boundary
where this means Never.  Replacing only `d` leaves its opponents unchanged,
and therefore leaves its cap unchanged.  Under `tau`, its prescribed payoff
is exactly the old cap `N`; consequently (7) holds.

Apply the terminal exploitability witness (1) to the actual profile `tau`.
Since `d_d(tau)=0`, a debtor with debt at least `Gamma` lies in `F`, proving
(8).  The repaired owner is above its floor.  Thus either every coordinate of
`U(tau)` is above its floor, or every floor violation lies in `F`; this is
(9).

### 4. The outside debtor gives the literal paid row

Fix a free debtor `j` from (8).  Against `tau_{-j}`, let `Q_j` be the payoff
from quitting immediately and let `N_j` be the payoff from Never.  If the
opponents have positive one-row absorption probability, the stationary
fixed-point equation writes `U_j(tau)` as a convex combination

```text
U_j(tau)=theta Q_j+(1-theta)N_j,       0<=theta<=1.        (15)
```

This formula includes simultaneous quitters in `Q_j`.  If opponent
absorption is zero, a positive stationary hazard of `j` gives `U_j=Q_j`, and
a zero hazard gives `U_j=N_j=0`; hence the same closed-segment conclusion
holds.  Stationary pure-time extremality gives

```text
B_j(tau)=max(Q_j,N_j).
```

Therefore

```text
|Q_j-N_j| >= B_j(tau)-U_j(tau) >= Gamma.                 (16)
```

Choose `some 0` and `Never` in the orientation from the lower endpoint in
(16) to the higher.  The checked first-disagreement theorem applies with
gain `Gamma` and yields (10).  The selected player lies in `F`, so `j!=d`.

### 5. The large-base adapter supplies a uniform positive excess

The checked four-player large-base residual has two persistent labels and two
free labels.  The reviewed adapter selects one persistent label `d`, moves
the other one `c` into the free set, and considers the complete induced game
on `F={c,x,y}` with persistent base `{d}`.  Its mixed Nash set is nonempty and
compact.

At any Nash point the three free endpoint inequalities are exact and there
are no outsider coordinates.  If `K_d<=0`, the checked singleton-base
certificate constructor and its all-behavior consumer produce a uniform-
equilibrium payoff, contradicting the terminal witness.  Thus `K_d>0` at
every point of the compact Nash set.  The functional is continuous, so it has
a positive minimum `delta`.  Selecting any Nash point now supplies (3), and
Steps 1--4 apply.

## Probability and deviation audit

- Absorption at `sigma` is literal date-zero absorption because `d` Quits
  surely.  Ties among free quitters are retained in the terminal coalition.
- The proof of (4) covers every behavioral deviation, not only stationary or
  pure deviations: all post-date-zero contingencies have zero reach.
- The owner calculation covers finite stopping times, Never, and arbitrary
  behavioral mixtures.  The exact stationary-cap theorem is the project
  implementation of this endpoint extremality.
- The `beta=1` case is not divided by `1-beta`; it uses `N=0` and
  `C_d(P_d)=P_d` directly.
- The profile `tau` is an actual unilateral strategy replacement, not a
  residual profile reached from `sigma` by play or conditioning.
- The paid decoder uses deterministic pure times `some 0` and `Never`.  It
  chooses their temporal orientation according to payoff, and its internal
  first-disagreement split handles finite time versus Never without assuming
  that the better payoff occurs later in calendar time.

## Boundary tests

### Exact algebraic and floor-damage regression

Take four players `{d,j,x,y}`.  Players `x,y` receive zero from every terminal
coalition.  Give player `d` reward `-1` from every coalition containing `d`
and reward `1` from every nonempty coalition not containing `d`.  Give player
`j` reward

```text
1   if both d and j are in the coalition,
-1  if j is in the coalition and d is not,
0   if j is not in the coalition.
```

Let `d,j` Quit surely and let `x,y` Continue.  This is an exact induced Nash
row for the free set `{j,x,y}` with persistent owner `d`: player `j` gets `1`
by Quit and `0` by Continue, while `x,y` are indifferent.  Direct minmax
calculation gives `P_d=P_j=P_x=P_y=0`.  For the owner,

```text
beta=0, Q=-1, N=1, C_d(P_d)=1, K_d=2,
B_d-U_d=2.
```

The free coordinates have `B=U>=P`.  After the owner changes to Always
Continue, the terminal coalition is `{j}`: the owner receives `1`, while
`j` receives `-1<P_j`.  Player `j`'s immediate-Quit and Never values are
`-1` and `0`, so the paid decoder has exact gain `1`.  This tests the owner
repair, transfer of debt and floor damage to a free label, and both
orientations of the deterministic endpoints.  The table is only a local
regression: it has an exact equilibrium elsewhere and therefore does not
satisfy the global terminal-witness hypothesis.

### The all-free-Continue boundary

Use a separate table in which every free player receives zero from every
coalition, while `d` still receives `-1` from coalitions containing `d` and
`1` from nonempty coalitions not containing `d`.  All free players are
indifferent, so the all-Continue free point is an induced Nash equilibrium.
Then

```text
beta=1, Q=-1, N=0, P_d=0,
C_d(P_d)=0, K_d=1, B_d-U_d=1.
```

This verifies the `beta=1` convention and shows why no division by
`1-beta` is legal in the proof.

### Necessity checks

If the positive owner excess (3) is removed, the all-zero reward table has
`K_d=0` and every debt is zero; no positive owner transfer follows.  If the
terminal gap (1) is removed, the owner repair need not create any outside
debtor: the all-zero table remains exact after the repair.  If `d` is not a
sure date-zero quitter, an arbitrary free-player behavioral deviation can
act on later positive-reach histories, so a one-stage induced Nash inequality
alone no longer proves (4).  These are precisely the three inputs used in
the proof.

## Adapter and consumer

The actual-data adapter is the checked large-base strict-toggle branch
`HasLargeBasePaidChainResidual`, followed by the reviewed Proposition 29.2
re-selection.  It produces the four-player labels, the full three-free-player
induced Nash carrier, and the uniform positive `delta`.  No supplied
certificate unrelated to the terminal witness is assumed.

The immediate consumer is the checked structure
`QuittingPaidFirstDisagreementRow`: Theorem B produces one at an actual
stationary behavioral source with observer outside the retained owner.  For
the maintained near-return question, the output is a strict intermediate
reduction rather than a completed consumer invocation.  The remaining
Bellman construction must preserve or repair the floor and produce exact
path charge/payoff return before
`PaidFirstDisagreementAdmissiblePayoffNearReturnConsumer` can be applied.

## Lean handoff

The narrow formalization target is three declarations.

1. A theorem taking `point in quittingPersistentBaseNashSet reward {d} F`,
   `F=univ\{d}`, and a positive lower bound on
   `quittingSingletonBaseOwnerFloorExcess`, and proving the free-coordinate
   terminal payoff/cap equalities plus the owner debt bound for the stationary
   persistent-base root.
2. A theorem specializing the cap-attaining replacement to Always Continue,
   proving zero repaired-owner debt, and using a
   `QuittingTerminalExploitabilityWitness` to select a distinct free debtor.
3. A theorem applying the stationary fractional-payoff segment formula and
   `exists_quittingPaidFirstDisagreementRow_of_pureTimePayoff_sub` to that
   debtor.

Likely dependencies are precisely the declarations in the Source
correspondence section.  Useful finite regressions are the rational table
above and the separate `beta=1` root.  The formalization should prove the
semantic theorem first and keep the ordinary compact-Nash Proposition 29.2
adapter separate; it should not encode `delta>0` as a field of a new source
structure merely to assume the desired conclusion.

## Scope and nonclaims

- `sigma` and `tau` are behavioral profiles, not exact punishment-floor Nash
  roots.
- `sigma -> tau` is a unilateral strategy update, not an exact Nash--Bellman
  edge and not a profile transition reached by play or conditioning.
- The result gives no absorption charge for an exact Bellman edge, no finite
  exact path, no repayment, and no payoff near-return.
- The reselected source is not asserted to be a rank of the tangent frontier,
  a full-replacement endpoint, or chronologically connected to the original
  paid boundary face.
- The literal paid row is not by itself a
  `PaidFirstDisagreementAdmissiblePayoffNearReturnConsumer` witness.
- In the second arm of (9), no bound is claimed on the size of the free floor
  deficit; the theorem only localizes it and retains the paid row.
- No relationship between the original paid margin `gamma`, the compact
  owner excess `delta`, and the terminal gap `Gamma` is asserted.
- The result is ordinary mathematics.  The cited Lean declarations validate
  its inputs and consumers but do not yet contain this assembled handoff.
