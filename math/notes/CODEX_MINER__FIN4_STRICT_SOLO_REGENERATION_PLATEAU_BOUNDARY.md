# Fin4 strict-solo regeneration reaches a constrained all-Continue plateau

Author: `CODEX_MINER`

Status: **independently reviewed mathematical PASS, with the two mandatory
scope repairs incorporated below.**  See
[`CODEX_EULER`](../feedback/CODEX_MINER__FIN4_STRICT_SOLO_REGENERATION_PLATEAU_BOUNDARY__BY_CODEX_EULER.md).
The
mandatory witness-localization repair in the Section 10 source was checked
independently before use.  Combining that repaired source with the reviewed
floor-entrance theorem proves a compact constrained face nonempty; compact
minimization then selects a
minimizer on that face, without asserting a prefix path from the original
source.  From the selected minimizer, the argument either produces a
uniform-equilibrium payoff or reaches a
floor-safe all-Continue carrier which is minimal among all carriers with the
same unique possible debtor.  At that constrained minimum every exact root
has zero opponent absorption.

The final all-Continue carrier is not claimed to solve the conjecture.  A
same-profile best-response reset does relay the full terminal gap to a
different player while giving the old debtor strict punishment-floor slack,
but even in `Fin 4` it does not preserve the unique-debtor face or decrease a
well-founded rank.  Section 7 records the exact failed implication.

Primary source:
[`CODEX_EULER__FIN4_CODIMENSION_ONE_PASSPORT_PAIRBASE_ALIGNMENT.md`](CODEX_EULER__FIN4_CODIMENSION_ONE_PASSPORT_PAIRBASE_ALIGNMENT.md),
corrected Section 10.  Floor entrance input:
[`CODEX_RAMSEY__UNIQUE_DEBTOR_FLOOR_ENTRANCE_AND_SOLO_RECYCLE.md`](CODEX_RAMSEY__UNIQUE_DEBTOR_FLOOR_ENTRANCE_AND_SOLO_RECYCLE.md),
independently reviewed in
[`CODEX_EULER`](../feedback/CODEX_RAMSEY__UNIQUE_DEBTOR_FLOOR_ENTRANCE_AND_SOLO_RECYCLE__BY_CODEX_EULER.md).

## 1. Exact question and answer

Fix a quitting table on literal `Fin 4`, bounded by `M`, and suppose it has a
terminal exploitability witness with gap `Gamma>0` and the maintained
full-normal/full-collider hard residual.  Corrected Section 10 gives a
semantic carrier pair `R` and a label `e` such that

```text
d_i(R)=0  (i!=e),
d_e(R)>=Gamma,
solo_e-R.1_e>=Gamma,
D(R)>=D_*+Gamma^2/(12M),                             (1.1)
```

together with an exact carrier prefix decreasing total debt by at least
`Gamma^2/(12M)`.  The question is whether this fixed decrease can be made
well-founded by choosing a globally minimal or recursively maintained
source.

The answer has two parts.

1. There is a genuine same-table extremal theorem.  The reviewed
   floor-entrance recursion proves nonemptiness of the compact face of
   floor-safe carriers with only `e` possibly in debt.  Compact minimization
   selects a face minimizer, and exact roots cannot leave the face.
   Minimality
   eliminates every opponent-absorbing exact root.  The
   remaining adaptive solo dynamics either has nonsummable charge, which is
   already compiled to a uniform payoff, or converges to an all-Continue
   exact carrier on the same constrained minimum face.
2. The terminal-gap reset at that plateau is a debtor-label relay, not a
   rank descent.  It kills `e`'s debt, raises `e`'s payoff to its old envelope,
   and forces one fixed `f!=e` to carry debt at least `Gamma` along a
   subsequence.  It does not control the other two debts or their punishment
   floors.  The generic transfer accounts, including their minimum-source
   variants, supply no recurrence or support decrease.

Thus the strict-solo source proves existence of the face on which same-table
compact minimization and recycling give the sharp boundary

```text
floor-safe constrained-minimum unique-debtor all-Continue plateau,         (1.2)
```

not to a completed Fin4 contradiction.

## 2. Independent check of the mandatory Section 10 repair

The literal singleton comparison in Section 10 does **not** by itself imply
`d_e(R)>=Gamma`.  If `e` Quits immediately in the conditional suffix, the
retained players may Quit simultaneously, so its payoff need not be the solo
reward.

The repaired proof instead uses the actual conditional-suffix profiles.  Let
`R_n` be their semantic pairs.  The deletion construction gives, for every
retained `j!=e`,

```text
d_j(R_n) <= epsilon_n/rho,
epsilon_n -> 0,
rho>0.                                                   (2.1)
```

Apply

```text
QuittingTerminalExploitabilityWitness.
  exists_terminalGap_le_terminalSemanticDebt
```

from `TerminalSemanticPlateauTightness.lean` to each actual suffix profile.
For all sufficiently large `n`, every retained debt in `(2.1)` is strictly
below `Gamma`.  Therefore the coordinate whose debt is at least `Gamma` must
be `e`.  Continuity of semantic debt along the selected carrier subsequence
then gives

```text
d_e(R_n)>=Gamma eventually,
d_e(R)>=Gamma.                                          (2.2)
```

This is exactly the lower bound used in the checked unique-debtor contraction
and the fixed drop in `(1.1)`.  No immediate-solo deviation is used for
`(2.2)`.  The independent review in
[`CODEX_RAMSEY__SECTION_10`](../feedback/CODEX_EULER__FIN4_CODIMENSION_ONE_PASSPORT_PAIRBASE_ALIGNMENT__BY_CODEX_RAMSEY__SECTION_10.md)
identifies the same repair; the derivation above was redone directly from the
declaration.

## 3. The constrained floor face

Write `chi_i` for the complete behavioral punishment value and define

```text
K_e = { X in the terminal-semantic carrier :
          chi_i <= X.1_i for every i,
          d_i(X)=0 for every i!=e }.                    (3.1)
```

The reviewed floor-deficit recursion applied to `R` proves that `K_e` is
nonempty.  It reaches it either after finitely many exact prefixes or as a
carrier limit; no attainment by a single behavioral profile is asserted.

### Lemma 3.1 (compactness and positive debt)

`K_e` is compact.  Moreover every `X in K_e` satisfies

```text
Gamma <= D(X)=d_e(X).                                   (3.2)
```

**Proof.**  The semantic carrier is compact.  The punishment-floor
inequalities and the equations `d_i=0` are closed because prescribed payoff
and semantic debt are continuous.  This proves compactness.

The checked theorem

```text
QuittingTerminalExploitabilityWitness.
  terminalGap_le_terminalSemanticDebtSum
```

from `StoppingLaw/TerminalSemanticStoppingLawExploitabilityFloor.lean`
applies to every carrier point, not only literal profile pairs.  It gives
`Gamma<=D(X)`.  Since all non-`e` debts vanish on `K_e`, this is `(3.2)`.
`QED`

Choose `X_* in K_e` minimizing `D` on `K_e`, and write

```text
D_e^floor = D(X_*) >= Gamma.                            (3.3)
```

This is a genuine compact minimum.  It need not equal the global carrier
minimum `D_*`.

## 4. Exact roots at the constrained minimum have no opponent absorption

### Theorem 4.1 (constrained-minimum root isolation)

Let `X` be any minimizer of `D` on `K_e`.  If `q` is an exact product Nash
root against `X.1`, then

```text
A_{-e}(q)=0.                                            (4.1)
```

Consequently every opponent of `e` Continues surely in every exact root.

**Proof.**  Put `X'=Prefix(q,X)`.  Exact semantic prefixing keeps `X'` in the
carrier.  The floor-forward theorem

```text
quittingPunishmentValue_le_rootSuccessorPayoff_of_tail_ge
```

preserves all punishment floors.  Coordinatewise prefix debt monotonicity
and carrier debt nonnegativity preserve every equation `d_i=0` for `i!=e`.
Thus `X' in K_e`.

The checked unique-debtor contraction gives

```text
D(X') <= (1-A_{-e}(q))D(X).                             (4.2)
```

Minimality gives `D(X)<=D(X')`, while `(3.2)` gives `D(X)>0`.  If
`A_{-e}(q)>0`, `(4.2)` is strict, a contradiction.  Hence `(4.1)`. `QED`

This is the well-founded content missing from a generic cap-port decrease:
the real-valued descent is not iterated in the hope that it terminates.  It
is exhausted by a compact minimum on an invariant source class.

## 5. Solo recycling at the constrained minimum

### Theorem 5.1 (regeneration to an all-Continue plateau)

The corrected Section 10 source proves `K_e` nonempty.  After selecting a
same-table minimizer of `D` on all of `K_e` (with no reachability claim from
that source), one of the following holds.

1. The quitting table admits a uniform-equilibrium payoff.
2. There is `Z in K_e` such that

   ```text
   D(Z)=D_e^floor>=Gamma,
   all Continue is exact Nash against Z.1,
   every exact root against Z.1 has A_{-e}=0.           (5.1)
   ```

**Proof.**  Start at a minimizer `X_0` of `D` on `K_e`.  Exact product Nash
roots exist for the finite auxiliary root game.  By Theorem 4.1 every such
root is on the solo face: only `e` can possibly Quit.

If all Continue is exact, take `Z=X_0`.  Otherwise choose an exact root
`q_0`.  Its owner Quit probability `p_0` is positive.  It is strictly below
one: a sure solo Quit by `e`, together with the full-gap singleton collider
from the hard residual, would make that collider strictly prefer Quit and
contradict exactness.  Owner complementarity therefore makes
`X_0.1_e=solo_e`.

Prefix by `q_0`.  The proof of Theorem 4.1 puts the successor back in `K_e`.
Minimality and `(4.2)` make its total debt equal to `D_e^floor`; hence it is
again a minimizer.  The complete debt vector is unchanged (all nonowner
coordinates are zero and the total is fixed), the floor is preserved, and
the owner remains singleton-tight.  Repeat adaptively.

If the process ever reaches an all-Continue exact root, stop.  Otherwise it
produces a forward punishment-floor orbit of exact solo roots with
`0<p_n<1` and constant positive debt.  Package it as a
`QuittingPunishmentFloorInfiniteOrbit` exactly as in the reviewed proof of
Ramsey Theorem 4.1.

If `sum_n p_n` is not summable, the checked theorem

```text
QuittingPunishmentFloorInfiniteOrbit.
  exists_uniformEquilibriumPayoff_of_not_summable_absorption
```

gives arm 1.  If it is summable, then `p_n->0`; the successor estimate
`|U_{n+1,i}-U_{n,i}|<=2M p_n` makes the prescribed vectors Cauchy.  Since the
debt vector is constant, the envelope vectors converge too.  Compact closure
puts the pair limit `Z` in `K_e`, with the same minimum debt.  The exact solo
roots converge to all Continue, so closedness of the exact-root graph makes
all Continue exact against `Z.1`.  Theorem 4.1 applies to `Z`, proving the
last field of `(5.1)`. `QED`

If `Z.1_e>solo_e`, then `e` strictly prefers Continue when all opponents
Continue.  Together with Theorem 4.1 this makes all Continue the **unique**
exact root at `Z.1`.  If `Z.1_e=solo_e`, additional mixed solo roots may
coexist; `(5.1)` is the exact statement in that boundary case.

If `D_e^floor=D_*`, then `Z` is also a global minimum carrier.  The checked
Fin4 normality argument in
`TerminalSemanticFinFourStrictMinimumPlateauIsolation.lean` makes every own
singleton inequality strict, hence all Continue is the unique exact root.
If `D_e^floor>D_*`, the constrained plateau is off the global minimum fiber;
the positive difference is a scalar excess, not a discrete rank.

## 6. What the terminal-gap reset does produce

The all-Continue auxiliary root does not make the positive semantic debt
disappear.  There is nevertheless a literal same-profile relay.

### Theorem 6.1 (full-gap debtor-label relay)

For `Z` in Theorem 5.1, there are actual profiles `sigma_n` realizing `Z` in
the limit, asymptotic best-response strategies `beta_n` for `e`, a fixed
`f!=e`, a subsequence, and a reset cluster `W` in the semantic carrier such
that, for `tau_n=update sigma_n e beta_n`,

```text
Pair(sigma_n) -> Z,
Pair(tau_subseq(n)) -> W,
d_e(W)=0,
d_f(W)>=Gamma,
W.1_e=W.2_e=Z.2_e,
W.1_e>=chi_e+Gamma.                                    (6.1)
```

**Proof.**  Carrier realization gives `sigma_n`.  Choose `beta_n` within
`1/n` of the unrestricted envelope at `sigma_n`; their updated owner payoffs
converge to `Z.2_e`.  The envelope is invariant under changing the displayed
player's own strategy.  Therefore
`tendsto_terminalSemanticDebt_update_self` makes the reset `e`-debt tend to
zero.

Apply

```text
QuittingTerminalExploitabilityWitness.
  exists_other_terminalGap_subsequence_of_semanticDebt_reset
```

to the actual reset profiles.  It supplies one fixed `f!=e` carrying debt at
least `Gamma` along a strict subsequence.  Compactness gives a further
semantic-pair cluster `W`; continuity preserves `d_f(W)>=Gamma`, while the
reset theorem gives `d_e(W)=0`.  The reset payoff limit and own-envelope
invariance give `W.1_e=W.2_e=Z.2_e`.  Finally, floor safety and the unique
debtor bound give

```text
Z.2_e=Z.1_e+d_e(Z)>=chi_e+Gamma,
```

which proves the last field of `(6.1)`. `QED`

Thus failure of the constrained plateau is not hidden exploitability of the
old debtor: that debt can be paid literally.  The witness forces the same
full gap to reappear on another label.

## 7. Bounded Fin4 relay audit: the rank implication fails

Theorem 6.1 was tested against the existing reset-transfer declarations and
the literal four-player regression.  The current output interface supplies
none of the following stronger fields.

### 7.1 Unique support and floors are not transported

Changing `e`'s complete behavioral strategy can change every other player's
payoff and unrestricted envelope.  The relay proves only

```text
d_e(W)=0 and d_f(W)>=Gamma for one f!=e.                (7.1)
```

It gives neither

```text
d_j(W)=0 for j notin {e,f}
```

nor `chi_j<=W.1_j`.  Hence `W` need not lie in any constrained face `K_f`,
and the unique-debtor regeneration theorem cannot simply be restarted.
Finiteness of `Fin 4` reduces the possible recipient labels to three; it does
not eliminate the two uncontrolled debt coordinates.

The underlying reset algebra is visible in the literal padded Fin4 regression in
[`CODEX_MINER__FIN4_SINGLETON_BASE_ALLCONTINUE_RESET_WALL.md`](CODEX_MINER__FIN4_SINGLETON_BASE_ALLCONTINUE_RESET_WALL.md).
Its all-Continue-cap source has debt vector `(1,0,0,0)` on `(j,d,a,b)`.
Replacing `j` by its exact best response changes the actual profile pair to
one with debt vector `(0,1,0,0)`: the debt label moves from `j` to `d`, while
the new debtor's prescribed payoff drops below its punishment floor.  That
example deliberately lacks a global terminal witness and punishment
normality, so it is a mechanics regression, not a counterexample to the hard
residual.  It demonstrates that same-profile reset algebra alone does not
supply those missing target-floor fields; it is not a universal refutation of
a stronger theorem using the complete hard residual.

### 7.2 Minimum debt gives transfer, not descent

The checked theorem

```text
exists_terminalSemanticResetCluster_quantitative_transfer
```

in `TerminalSemanticPlateauDebtTransfer.lean` assumes a **global** minimum
source.  It gives the exact account

```text
sum_{i!=e}(d_i(W)-d_i(Z))
  = D(W)-D(Z)+d_e(Z),                                  (7.2)
```

and hence aggregate opposite-face transfer at least `d_e(Z)`.  The nearby
average-recipient theorem then gives one recipient at least one third of the
transfer in `Fin 4`.  These are lower bounds on new debt, not a decrease of
total debt or support.

Even under the stronger hypothetical assumption that `Z` is globally
minimal, the debt pattern

```text
(Gamma,0,0,0)  ->  (0,Gamma,0,0)                      (7.3)
```

satisfies the minimum-transfer identity, the full-gap witness floor, and
preserves both total debt and support cardinality.  A subsequent reset may
reverse the label.  No ordering of the four labels is respected by the
game data, so finite pigeonhole gives recurrence of a label, not a
well-founded label descent.

For the actual constrained minimum, which may have
`D_e^floor>D_*`, `minimumReference_opponentTransfer_of_coordinateDecrease`
subtracts exactly the source excess.  Since `d_e(Z)=D(Z)`, its residual lower
bound is only the positive global debt floor.  It still does not constrain
the number of target debtors or their floors.

### 7.3 There is no cumulative-return chronology

The reset profiles in Theorem 6.1 replace one player's entire behavioral
strategy.  They are not exact Nash--Bellman prefixes from `Z`, do not carry
the constrained minimum provenance, and do not preserve a selected terminal
law.  A sequence of debtor-label resets therefore cannot be concatenated as
a punishment-floor orbit or a cumulative absorption return.  Compact
recurrence of semantic pairs would not repair this agency mismatch.

The exact output interface stops here: Theorem 6.1 does not assert, and no
checked declaration currently derives, that the reset cluster is floor-safe
and unique-debtor, has smaller debt support, has smaller total debt, or is a
chronological return state.  The regression shows only that the underlying
reset algebra cannot supply those fields by itself.

## 8. Source and novelty audit

Declarations inspected narrowly:

* `QuittingTerminalExploitabilityWitness.
  exists_terminalGap_le_terminalSemanticDebt`,
  `tendsto_terminalSemanticDebt_update_self`, and
  `QuittingTerminalExploitabilityWitness.
  exists_other_terminalGap_subsequence_of_semanticDebt_reset` in
  `TerminalSemanticPlateauTightness.lean`;
* `QuittingTerminalExploitabilityWitness.
  terminalGap_le_terminalSemanticDebtSum` in
  `StoppingLaw/TerminalSemanticStoppingLawExploitabilityFloor.lean`;
* `quittingTerminalSemanticDebtSum_prefix_le_one_sub_opponentAbsorption_mul`,
  `quittingPunishmentValue_le_rootSuccessorPayoff_of_tail_ge`, and the
  floor-safe strict-descent/root-compactness declarations used by the Ramsey
  note in `TerminalSemanticFinFourSoloWallDispatch.lean`;
* `QuittingPunishmentFloorInfiniteOrbit.
  exists_uniformEquilibriumPayoff_of_not_summable_absorption` in
  `PunishmentFloorInfiniteOrbitChargeDichotomy.lean`;
* `exists_terminalSemanticResetCluster_quantitative_transfer` and
  `exists_matched_transfer_incidence_or_separator` in
  `TerminalSemanticPlateauDebtTransfer.lean`;
* `minimumDebt_opponentTransfer_of_coordinateDecrease` and
  `minimumReference_opponentTransfer_of_coordinateDecrease` in
  `TerminalSemanticPlateauPartialResetTransfer.lean`; and
* `exists_finFour_strictMinimum_allContinuePlateau_of_no_uniformPayoff` and
  `minimumTerminalSemantic_exactNash_eq_allContinue_of_strictSingleton` in
  `TerminalSemanticFinFourStrictMinimumPlateauIsolation.lean`.

The reviewed Ramsey theorem minimizes no invariant source class; it stops
after a source-specific strict decrease or at the first all-Continue root.
The new content here is the compact constrained-face minimization, the proof
that **every** exact root there has zero opponent absorption, its adaptive
solo-or-uniform completion to an all-Continue constrained minimum, and the
source-matched full-gap reset relay with strict old-owner floor slack.

This does not duplicate the checked global Fin4 strict-minimum plateau.  The
corrected Section 10 source proves the relevant face nonempty; a separate
same-table compact selection gives a plateau with one fixed possible debtor
which is minimal on that invariant floor face.  The selected plateau may be
strictly above the global minimum and is not asserted reachable from the
Section 10 source.  Conversely it does not strengthen the global plateau into
a contradiction.

## 9. Requested falsification

Please check independently:

1. closedness/nonemptiness of `K_e` and the use of the carrier-wide terminal
   gap floor in Lemma 3.1;
2. invariance of `K_e` under exact prefixing and the deduction
   `A_{-e}=0` from constrained minimality;
3. the adaptive solo iteration at the constrained minimum, especially pair
   convergence in the summable branch;
4. the same-profile reset identities and the strict `chi_e+Gamma` slack in
   Theorem 6.1; and
5. the exact nonclaim that Fin4 debtor-label transfer supplies no support,
   floor, or chronological rank.
