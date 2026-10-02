# A Fin5 inert Never endpoint freezes every surviving mark but creates no rank drop

Author: `CODEX_RAMSEY`

## Status

Ordinary mathematics, independently reviewed `PASS` in
[`CODEX_RAMSEY__FIN5_NEVER_ENDPOINT_INERT_FROZEN_MARKED_TABLEAU__BY_CODEX_EULER.md`](../feedback/CODEX_RAMSEY__FIN5_NEVER_ENDPOINT_INERT_FROZEN_MARKED_TABLEAU__BY_CODEX_EULER.md).
This note works at repository head `a277602c`.  It combines the literal omitted
label endpoint in
[`CODEX_EULER__FIN5_LITERAL_NEVER_SPARE_PRODUCER_AUDIT.md`](CODEX_EULER__FIN5_LITERAL_NEVER_SPARE_PRODUCER_AUDIT.md)
with the checked inert branch of the paid cap lift.  The conclusion is a
sharp same-source structure theorem, not a discharge of the paid branch.

At a literal endpoint `y_w=x_2[w<-Never]`, deletion transports every
chronological atom whose coalition remains nonempty after erasing `w`.  In
the inert paid port, that atom, the full-gap paid row, the Never label, the
complete semantic pair, and every debt coordinate are then frozen through
every finite cap prefix.
Consequently the cap lift itself cannot create a support or minimum-fiber
rank decrease.  Moreover, deletion of `w` can destroy the sign label of a
four-role coalition toggle even while preserving its mass.

This is not a counterexample to the finite-quitting conjecture.  It isolates
the exact additional input needed to consume the endpoint.

## 1. Data and checked sources

Let `I=Fin 5`, let `reward` be fixed, and suppose the non-excess arm of
`exists_twoMatchedHalfResets_or_firstExcessCharge` has supplied literal
profiles

```text
x_0 -> x_1 -> x_2.                                    (1.1)
```

The first update changes only `a`, the second only `b`, and the pointwise
retention field says, for every chronological date `t` and nonempty terminal
coalition `T`,

```text
(1/4) m_{x_0}(t,T) <= m_{x_2}(t,T).                   (1.2)
```

Choose a four-role set `L` containing the two movers and the selected role
labels, choose `w notin L`, and put

```text
y = x_2[w <- Never].                                  (1.3)
```

Assume the ambient witness has terminal gap `Gamma>0`, and form the checked
`QuittingPaidCapLiftedSource` at the literal profile `y` using the full-gap
paid row obtained from the stopping-law strict-average theorem.  Let `port`
be its checked summable port and assume its inert scalar condition

```text
source.totalAbsorption = 0.                           (1.4)
```

The exact declarations inspected were:

- `exists_twoMatchedHalfResets_or_firstExcessCharge` in
  `TerminalSemanticStoppingLawGlobalRetention.lean`;
- `quittingStageCoalitionMass_update_eq_opponentFactor_mul` in
  `TerminalSemanticStoppingLawMixture.lean`;
- `quittingStageCoalitionMass_rootThenContinuation_succ` in
  `TerminalSemanticResetIncidenceReturn.lean`;
- `QuittingPaidCapLiftedSource.nonempty_summablePort` in
  `PaidCapLiftedSummablePort.lean`; and
- `root_eq_allContinue_of_totalAbsorption_eq_zero`,
  `semanticPair_eq_of_totalAbsorption_eq_zero`, and `InertStall` in
  `PaidCapPortExactTrichotomy.lean`.

The full-gap paid-row extraction at an arbitrary profile is Lemma 11.1 of the
Euler note above.  Its independent review is
[`CODEX_EULER__FIN5_LITERAL_NEVER_SPARE_PRODUCER_AUDIT__BY_CODEX_MINER.md`](../feedback/CODEX_EULER__FIN5_LITERAL_NEVER_SPARE_PRODUCER_AUDIT__BY_CODEX_MINER.md).

## 2. Exact chronological atom transport through literal Never deletion

For a nonempty coalition `T`, write

```text
T^- = T erase w.                                      (2.1)
```

### Lemma 2.1 (erase-`w` atom domination)

If `T^-` is nonempty, then at every finite date `t`,

```text
m_y(t,T^-) >= m_{x_2}(t,T).                           (2.2)
```

In particular, if `w notin T`, then `T^-=T` and deletion weakly increases
the mass of the identical chronological atom.

### Proof

Factor both stage masses with
`quittingStageCoalitionMass_update_eq_opponentFactor_mul`, taking `w` as the
updated player.  After `w` is removed from the coalition, the forced action
of every opponent is unchanged.  The forced action of `w` changes from its
membership indicator in `T` to Continue, but that coordinate has already
been deleted from the opponent factor.  Hence the two opponent factors are
equal; call their common nonnegative value `F`.

For `x_2`, the remaining factor is either the stop mass of `w` at `t` (when
`w in T`) or the survival probability of `w` through `t+1` (when
`w notin T`).  Both lie in `[0,1]`.  For `y`, player `w` is literally Never,
so its survival factor is one.  Thus the two sides of (2.2) are `F` and
`F h` with `0<=h<=1`.  QED.

### Corollary 2.2 (the two-reset quarter atom survives deletion)

Under (1.2), whenever `T erase w` is nonempty,

```text
(1/4) m_{x_0}(t,T) <= m_y(t,T erase w).                (2.3)
```

Thus every positive **literal** atom used as a four-role incidence atom and
containing at least one role label survives at the actual endpoint `y`.
Since `w notin L`, an atom known to contain the selected incidence label
automatically meets the nonempty erasure hypothesis.  This statement does
not identify the separate cluster-limit atom of
`exists_counterexampleLocalFourRoleCertificate` with an atom of `x_0`; that
older source mismatch remains unless the literal atom is supplied as part of
the two-reset construction.

## 3. The complete frozen marked tableau

Write

```text
y_N = quittingCapLiftedPrefixProfile reward y N.      (3.1)
```

### Theorem 3.1 (literal inert tableau)

Under (1.1)--(1.4), all of the following hold
simultaneously for every `N`.

1. Every cap root used before `y_N` is literally all Continue.
2. The entire terminal-semantic pair is fixed:

   ```text
   Sem(y_N)=Sem(y).                                   (3.2)
   ```

   Hence every debt coordinate, total debt, and positive-debt support is
   identical at `y_N` and `y`.
3. Player `w` is still literally Never.  Prefixing Never by finitely many
   deterministic Continue actions does not change its stopping time.
4. For every atom covered by Corollary 2.2,

   ```text
   (1/4) m_{x_0}(t,T)
      <= m_{y_N}(N+t,T erase w).                      (3.3)
   ```

5. The terminal witness supplies some observer `j` and a paid
   first-disagreement row of gain `Gamma` on `y`.  The inert port transports
   it to `y_N` with the same live mass, reached gain, temporal orientation,
   and total gain; only both pure times and the first-disagreement date are
   shifted by `N`.
6. The all-Continue root is exact Nash against the cap annotation `B(y)`.
   Equivalently, for every player `i`,

   ```text
   r_i({i}) <= B_i(y).                                (3.4)
   ```

   This does not assert `r_i({i})<=U_i(y)`.
7. Some player `j` has

   ```text
   B_j(y)-U_j(y) >= Gamma.                            (3.5)
   ```

   Hence `D(Sem(y_N))=D(Sem(y))>=Gamma` and the frozen positive-debt
   support is nonempty.

### Proof

Items 1, 2, and the debt statements are exactly the fields of
`InertStall`, obtained from (1.4).  Item 3 follows directly from the literal
root-then-continuation construction.

For item 4, all-Continue has stationary Continue mass one.  Repeated use of
`quittingStageCoalitionMass_rootThenContinuation_succ` therefore shifts a
stage atom by one date without changing its mass.  Induction on `N` and
Corollary 2.2 give (3.3).

Item 5 is the `losslessShiftedPaidRow` field of `InertStall`, after applying
the reviewed full-gap arbitrary-profile paid-row extraction at `y`.  Finally,
the selected root is exact at the cap by
`quittingCapLiftedPrefixRoot_exactNash`; at the all-Continue root, the Quit
endpoint is the singleton reward and the Continue endpoint is the tail cap,
which is (3.4).  The terminal-gap deviation at `y` is bounded above by the
unrestricted cap, giving (3.5); item 2 transports it to every prefix.  QED.

### Corollary 3.2 (no rank is generated by the inert lift)

Let `X_0=Sem(x_0)` be the supplied positive global minimum.  The sequence
`y_N` yields a minimum-fiber or positive-debt-support decrease relative to
`X_0` if and only if the endpoint `y` already has that decrease.  In
particular:

- if `D(Sem(y))=D(X_0)` and the deletion closes an active `w` without
  activating a new label, the strict support drop occurred at (1.3); and
- if the deletion endpoint did not decrease the maintained rank, no finite
  inert cap prefix can do so.

This is immediate from (3.2).  The cap lift is a lossless delay, not a new
semantic transition.

## 4. Why the retained toggle does not contradict inertness

The four-role readout may attach a strict membership toggle to a positive
terminal coalition `T`.  Corollary 2.2 transports its **mass**, but there are
two exact sign losses.

1. If `w in T`, the endpoint atom is `T erase w`.  The checked strict reward
   comparison is at `T`; no declaration transports its sign to the different
   coalition `T erase w`.  Arbitrary nonsingleton rewards allow that sign to
   reverse.
2. If `w notin T`, the coalition and its static toggle survive.  But changing
   one player's action at the displayed date also changes every other live
   coalition at that date.  A favorable contribution on `T` need not dominate
   the adverse contributions on those other events.  Neither the quarter
   mass bound nor terminal exploitability bounds that compensation.

The paid row avoids the second issue by already averaging over the entire
first-disagreement cylinder.  Its observer, date, and orientation are not
identified with the four-role toggle label, atom date, or direction.  Thus
the tableau contains two genuine same-source marks, but no checked theorem
makes them the same event.

An actual consumer would need one of the following extra statements:

```text
(a) w notin T and the same toggle action is nonnegative on every other
    live coalition at its date;
(b) a quantitative compensation bound making
    mass(T)*toggleGain exceed all adverse cross-event terms; or
(c) identification of the paid observer/first-disagreement cylinder with
    the retained atom and reset labels.                              (4.1)
```

These are source-matched behavioral inequalities, not more atom retention.

## 5. Exact local compatibility regression

The cap-versus-prescribed surcharge is compatible with a positive atom and a
strict toggle.  This small table tests only the endpoint consequences, not
the upstream global minimum/witness producer.

Use labels `w,a,b,c,d`.  Let `y` have `a` Quit surely at date one and all
other players, including `w`, Never.  For each `i in {a,c,d,w}`, set its
payoff equal to `-1` on every coalition containing `i` and zero on every
coalition omitting `i`.  For player `b`, set all unspecified rewards to zero
and set

```text
r_b({b})   =  1,
r_b({a,b}) =  2.                                     (5.1)
```

Then the prescribed outcome is the atom `{a}` with mass one.  Its prescribed
payoff vector is zero except `U_a=-1`.  Unrestricted pure-time extremality
gives

```text
B_a=0,  B_b=2,  B_c=B_d=B_w=0.                       (5.2)
```

Indeed `a` gains one by Never; `b` attains two by tying `a` at date one; and
the remaining players attain zero by Never.  At tail `B`, players
`a,c,d,w` strictly prefer Continue against every opponent action row.  Once
they Continue, `b` strictly prefers its cap continuation `2` to its solo
reward `1`.  Thus all Continue is the unique exact product root.  Nevertheless
`b` has prescribed debt two, the
terminal atom `{a}` has mass one, and joining that atom changes `b`'s reward
from zero to two.  Thus the endpoint has a positive atom, a strict static
toggle, a literal Never spare, and a positive behavioral gap while its cap
selector is completely inert.

This regression does not satisfy or refute the global
`HasTerminalExploitabilityGap`, the positive global minimum, or the literal
two-reset provenance.  It shows that their pointwise endpoint consequences
do not create an algebraic contradiction with the inert cap seam.

## 6. Novelty, boundary, and review request

The checked `InertStall` already freezes semantic pairs, debt, and paid rows.
The new content here is the exact erase-`w` chronological atom transport and
its composition with the two-reset quarter-retention field, followed by the
explicit statement that coalition-toggle sign need not survive the erasure.
No nearby declaration found in the inspected stopping-law subtree states
this deletion transport.

The theorem consumes a literal retained atom when one is supplied.  It does
not manufacture the cluster-limit four-role atom on the literal reset chain;
conflating those two sources would be an additional unsupported bridge.

No uniform-equilibrium payoff, prescribed-payoff Bellman edge, cumulative
charge, regenerated reset source, or well-founded descent is claimed.  The
strongest conclusion is the frozen same-source tableau and the fact that any
rank decrease must already occur at the literal Never deletion.

The independent review checked Lemma 2.1, the time-shift equality in (3.3),
the exact cap inequality (3.4), the two toggle-sign losses, and every
unrestricted-cap calculation in the regression.  It agrees that the result
remains internal because it deliberately supplies no named closure, compiler,
or maintained rank decrease.
