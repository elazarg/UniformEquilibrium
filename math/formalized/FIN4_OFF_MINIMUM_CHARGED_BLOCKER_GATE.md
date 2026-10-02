# Fixed charge off the minimum fiber forces debt descent or a normal blocker gate

Author: `CODEX_CEDAR`

Independent reviews:

- [CODEX_RAMSEY](../feedback/CODEX_CEDAR__FOUR_PLAYER_CONJECTURE_CAPSTONE__BY_CODEX_RAMSEY__PROPOSITION_5.md)
- [CODEX_EULER](../feedback/CODEX_CEDAR__FOUR_PLAYER_CONJECTURE_CAPSTONE__BY_CODEX_EULER__PROPOSITION_5.md)

Upstream reviewed adapter:
[strict minimum-plateau isolation](../formalized/FIN4_STRICT_MINIMUM_PLATEAU_ISOLATION.md)

## Exact statement

Let the player type be literally `Fin 4`, and let

```text
reward : {S : Finset (Fin 4) // S.Nonempty} -> Payoff (Fin 4)
```

be a finite quitting reward table.  Put

```text
M=max(1,max_(S,i)|reward(S)_i|),
s_i=reward({i})_i,
P_i=quittingPunishmentValue reward i.
```

Assume that the game has no uniform-equilibrium payoff.  Let `Gamma>0` be
the resulting terminal exploitability gap.  By the reviewed upstream
adapter, every player is punishment-normal,

```text
P_i<=s_i,                                             (1)
```

and the terminal-semantic carrier has positive minimum total debt `D_*>0`.

For a terminal-semantic carrier pair `X=(U,B)`, write

```text
d_i(X)=B_i-U_i,
D(X)=sum_i d_i(X).
```

Let `(X_n,q_n)` be any sequence satisfying, literally,

```text
X_n in quittingTerminalSemanticCarrier reward,
IsεQuittingRootNash reward X_n.1 0 q_n,
P_i<=X_n.1_i for every i,
a<=A(q_n) for one fixed a>0,                          (2)
```

where `A(q)` is the one-row absorption probability.  Define the exact
semantic prefix and its debt drop by

```text
X'_n=quittingTerminalSemanticPrefix reward q_n X_n,
Delta_n=D(X_n)-D(X'_n).                               (3)
```

Then one of the following exhaustive alternatives holds.

1. **Macroscopic semantic debt descent.**

   ```text
   liminf_n Delta_n>0.                                (4)
   ```

   In particular, for every `eta>0`, only finitely many consecutive rows with
   `Delta_n>=eta` can occur in one literal exact semantic-prefix chronology,
   because every carrier has debt at least `D_*`.

2. **Quantitative normal blocker gate.**  There is a subsequence, still
   denoted by `n`, for which `Delta_n->0`, and there are a limiting carrier
   `X`, a limiting exact root `q`, and distinct players `k,i` with the
   following properties.  Writing `p=q_k(Quit)`,

   ```text
   a/8<=p<=1-Gamma/(4M),                              (5)
   q=soloRoot(k,p),
   d_j(X)=0 for j!=k,
   d_k(X)=D(X)>=D_*>0,
   X.1_k=s_k.                                         (6)
   ```

   Thus `k` is the unique limiting debtor and is genuinely mixed.  Define

   ```text
   Q_i=(1-p)s_i+p reward({k,i})_i,
   R_i=reward({k})_i,
   T_i=(Q_i-pR_i)/(1-p).                              (7)
   ```

   Then

   ```text
   P_i<=Q_i<T_i<=X.1_i,
   R_i<Q_i.                                           (8)
   ```

   If `Y` is obtained from `X.1` by replacing only coordinate `i` by `T_i`,
   then

   ```text
   IsεQuittingRootNash reward Y 0 q.                  (9)
   ```

   The tail `Y` is in the reward box and above the behavioral punishment
   floor.  Player `i`, who still plays Continue in `q`, is exactly
   indifferent between Quit and Continue at `Y`.  The row retains charge
   `A(q)=p>=a/8`.

Alternative 2 produces a prescribed payoff and an exact root, not a new
terminal-semantic carrier pair with prescribed payoff `Y`.  It also does not
force player `i` into positive Quit support.

## Conjecture-facing change

The maintained producer in
[`PAID_ADMISSIBLE_PAYOFF_NEAR_RETURN.md`](../questions/PAID_ADMISSIBLE_PAYOFF_NEAR_RETURN.md)
requires exact punishment-floor paths with one fixed positive edge charge.
The upstream minimum-fiber packet proves that every such charged carrier-tail
edge starts a fixed debt distance above the global minimum, but it did not
describe a family whose charge persists while its debt drop tends to zero.

This packet gives an exhaustive well-founded reduction for that family.
Macroscopic drop spends the nonnegative carrier obstruction `D-D_*` by a
fixed amount.  Vanishing drop cannot diffuse among several owners or close
on a solo face: it converges to a quantitatively interior solo owner carrying
all debt and exposes a distinct normal blocker at an explicit floor-safe
indifference threshold.  Thus the remaining zero-drop obligation is exactly
to activate that blocker in an exact root, or to prove that the root-selection
jump enters an already compiled branch.  Collision diffusion, a nearly sure
owner, and a closed solo endpoint are no longer possibilities in this arm.

This is a strict reduction, not the requested payoff near-return.

## Definitions and probability audit

A product root is an independent Boolean row `q=(q_i)`.  Its exact coalition
mass is

```text
mu_q(C)=product_(i in C)q_i product_(i notin C)(1-q_i).
```

Its absorption mass is `A(q)=sum_(C nonempty)mu_q(C)`, its collision mass is
the same sum over `|C|>=2`, and player `j`'s opponent-absorption mass is

```text
O_j(q)=1-product_(ell!=j)(1-q_ell).
```

`IsεQuittingRootNash reward V 0 q` means exact one-row Nash optimality at
the prescribed continuation payoff `V`: every action used with positive
probability maximizes the corresponding forced-action endpoint.  No public
correlation is introduced.

A terminal-semantic carrier pair is the prescribed terminal payoff and the
unrestricted behavioral best-response envelope of an executable behavioral
profile, or a point of their compact closure.  Consequently every debt
coordinate is nonnegative.  Prefixing executes the independent root for one
row and, on all-Continue, uses the original executable tail.  It preserves
carrier membership.  The debt inequalities below use unrestricted behavioral
best responses through the envelope; they are not stationary-regret
inequalities.

The behavioral punishment floor in (2) and (8) is the true unrestricted
punishment value.  Its comparison with the stationary unilateral cap is the
checked upper-leg theorem, not an assumption that deviations are stationary.

## Proof

If (4) fails, nonnegativity of the exact semantic debt drop gives a
subsequence with `Delta_n->0`.  Work on that subsequence.

### Debt drift removes collision

Exactness makes every coordinate Nash defect zero.  The checked semantic
debt ledger therefore gives

```text
sum_j O_j(q_n)d_j(X_n)<=Delta_n.                       (10)
```

Every collision contains an opponent of every player.  Hence
`collision(q_n)<=O_j(q_n)` for each `j`, and

```text
D_* collision(q_n)
 <= collision(q_n)D(X_n)
 <= sum_j O_j(q_n)d_j(X_n)
 <= Delta_n.                                          (11)
```

Thus collision mass tends to zero.

Absorption is exactly collision mass plus the four singleton masses.  By
(2), eventually their sum is at least `a/2`; one fixed singleton `{k}` has
mass at least `a/8` along a further subsequence.  Compactness of the carrier
and the product-root cube gives

```text
X_n->X,   q_n->q.                                     (12)
```

The limiting collision mass is zero while `mu_q({k})>=a/8`.  Two positive
Quit marginals in a product root would give positive collision mass.  Hence
`q` is a solo root owned by `k`, and

```text
p=q_k(Quit)=mu_q({k})>=a/8.                            (13)
```

### All limiting debt belongs to the solo owner

For every `j!=k`, the exact coalition-debt ledger applied to `{k}` gives

```text
mu_qn({k})d_j(X_n)<=d_j(X_n)-d_j(X'_n).               (14)
```

Every coordinate drift on the right is nonnegative and their sum is
`Delta_n`.  The common lower bound `mu_qn({k})>=a/8` therefore sends each
`d_j(X_n)` with `j!=k` to zero.  The carrier is closed, so `X` remains a
carrier pair and `D(X)>=D_*`.  This proves (6)'s debt statements.

Exact root Nash is closed under the joint limit.  Carrier payoffs are boxed,
and the floor condition in (2) is closed.  The checked terminal-gap marginal
cap now yields

```text
p<=1-Gamma/(4M).                                      (15)
```

Thus both actions of `k` have positive support.  Against a solo root, `k`'s
forced-Quit value is `s_k` and its forced-Continue value is `X.1_k`.
Indifference proves `X.1_k=s_k`.

### Normality forces a distinct blocker

Let `r_k` be the full singleton payoff vector `reward({k})`.  Suppose the
same positive solo root were exact at tail `r_k`.  Punishment normality (1)
gives `P_k<=s_k`.  The checked punishment-completed solo-cycle theorem would
then make `r_k` a uniform-equilibrium payoff, contrary to the standing
branch.  Therefore the root is not exact at `r_k`.

The owner is automatically indifferent there.  Some distinct Continue
player `i` must therefore have a profitable immediate-Quit deviation.  Its
forced-Quit and forced-Continue values at `r_k` are respectively

```text
Q_i=(1-p)s_i+p reward({k,i})_i,
R_i=reward({k})_i,
```

so `R_i<Q_i`.

At the actual limiting tail `X.1`, player `i` plays Continue and exactness
gives

```text
Q_i<=pR_i+(1-p)X.1_i.                                 (16)
```

Since `p<1`, (7), (16), and `R_i<Q_i` imply

```text
Q_i<T_i<=X.1_i.                                       (17)
```

Against the solo opponent row, `i`'s exact stationary unilateral cap is
`max(Q_i,R_i)=Q_i`.  The checked punishment upper leg gives `P_i<=Q_i`.
This proves (8), including that `T_i` is boxed.

Finally, a player's root endpoint condition depends on the tail only through
that player's own coordinate.  Replacing only coordinate `i` by `T_i` leaves
every other player's condition unchanged, while

```text
pR_i+(1-p)T_i=Q_i
```

makes `i` exactly indifferent.  This proves (9) and the retained charge.

## Boundary tests

1. **Positive charge is essential.**  If `a=0`, take every `q_n` to be
   all-Continue.  Collision and debt drop vanish, but no positive solo owner
   or blocker can be selected.

2. **No-uniform normality is essential.**  In the constant-zero four-player
   reward table, every root is exact at every zero tail.  A positive solo
   root closes at its singleton vector and has no strict blocker.  The table
   has the uniform payoff zero, so it lies exactly outside the theorem's
   branch.

3. **The product-root hypothesis is used sharply.**  Zero collision plus
   positive singleton mass implies one active owner for an independent
   product row.  For an arbitrarily correlated coalition lottery, positive
   masses on two different singleton coalitions can coexist with zero
   collision, so the unique-owner conclusion would be false.

4. **The two alternatives cannot be collapsed.**  A family with
   `Delta_n>=eta>0` never enters the limiting argument; its rows consume at
   least `eta` of semantic debt each when placed consecutively.  Conversely,
   when `Delta_n->0`, (11) rules out any fixed collision mass, but it does not
   rule out the fixed singleton charge retained in (13).

5. **Indifference is not activation.**  At the constructed tail `Y`, setting
   `q_i(Quit)=0` is still an exact best response.  The theorem consequently
   does not infer a two-active root or a terminal-semantic realization of
   `Y`; both would be false deductions from endpoint equality alone.

## Source correspondence

The no-uniform adapter and the same-table all-player normality are supplied by
`uniformPayoff_or_nonempty_finFourQuantitativeFullSupportHardResidual` in
`UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/FullSupportProjectiveQBarResidual.lean`
and by the reviewed packet
[`FIN4_STRICT_MINIMUM_PLATEAU_ISOLATION`](../formalized/FIN4_STRICT_MINIMUM_PLATEAU_ISOLATION.md).
The latter also supplies `D_*>0` and the carrier debt moat.

The proof uses these checked declarations:

- `sum_opponentAbsorptionMass_mul_debt_le_sumDebt_drift_add_totalNashDefect`
  and `quittingRootCoalitionMass_mul_debt_le_drift_add_nashDefect` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPlateauDefectCharge.lean`;
- the collision and singleton-mass identities in
  `UniformEquilibrium/Quitting/AbsorptionPath/CollisionConcentration.lean`;
- `exactFloorRoot_quitProbability_le_one_sub_terminalGap_div_four_mul` in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/TerminalGapExactRootMarginalCap.lean`;
- `soloReward_lt_punishmentValue_of_soloEndpointNash` in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/AtomicSoloLimitConsequences.lean`;
- `isUniformEquilibriumPayoff_soloReward_of_endpointNash_of_punishmentIR`
  in `UniformEquilibrium/Quitting/Punishment/SoloCycleCompletion.lean`; and
- `quittingPunishmentValue_le_stationaryUnilateralCap` in
  `UniformEquilibrium/Quitting/Stationary/MinMax.lean`.

The new content is their quantitative composition at an arbitrary sequence
of actual carrier tails: collision removal, unique-debtor localization, and
the explicit floor-safe blocker threshold.  It is not a restatement of a
literature theorem.

## Adapter and consumer

The adapter is literal but carrier-enriched.  An exact semantic-prefix
chronology starting from an actual carrier has carrier tails `X_n`, exact
roots at `X_n.1`, and semantic prefixes `X'_n`.  Selecting fixed-charge rows
from such chronologies supplies (2)--(3).  A payoff-only admissible path does
not automatically supply this lift.  The theorem then either decreases the
well-founded obstruction `D-D_*` by a fixed amount or outputs the displayed
off-minimum blocker gate.

The intended downstream consumer is
`PaidFirstDisagreementAdmissiblePayoffNearReturnConsumer` in
`UniformEquilibrium/Diagnostics/Quitting/PaidFirstDisagreementPayoffNearReturn.lean`.
This packet does not yet satisfy that consumer: the gate still needs an exact
blocker-activation/root-selection theorem or a nonlocal debt-repayment path.

## Lean handoff

The narrow formal target is a sequential theorem on literal `Fin 4`:

```text
theorem exists_macroscopicDebtDrop_or_chargedSoloBlockerGate
    (witness : QuittingTerminalExploitabilityWitness reward)
    (normal : forall i, IsQuittingNormalPlayer reward i)
    (hcarrier : forall n, X n in quittingTerminalSemanticCarrier reward)
    (hnash : forall n, IsεQuittingRootNash reward (X n).1 0 (q n))
    (hfloor : forall n i, P i <= (X n).1 i)
    (hcharge : forall n, a <= quittingRootAbsorptionMass (q n)) :
    ...
```

It should reuse the two debt-charge declarations above, compactness of the
carrier and finite product simplex, the exact-floor marginal cap, and the
solo punishment obstruction.  Useful finite checks are:

- the `a/8` singleton pigeonhole constant for four players;
- zero product collision implying at most one positive marginal;
- the coordinate formula (14); and
- substitution of (7) into the outsider endpoint equality.

No new structure should assume the blocker, unique debtor, or convergence as
fields; those are the theorem's conclusions.

## Scope and nonclaims

- The player type is literally `Fin 4`; no reindex adapter is claimed.
- The roots are independent product roots, not correlated coalition
  lotteries.
- The sequence need not be one chronology.  The well-founded telescope in
  alternative 1 applies only when the selected rows are consecutive semantic
  prefixes.
- A generic payoff-only punishment-floor path does not automatically carry
  terminal-semantic pairs, so the theorem does not supply its own
  carrier-enriched lift from the maintained near-return relation.
- The constructed `Y` is a boxed punishment-floor payoff tail, not proved to
  be the prescribed payoff of a carrier pair.
- The blocker is indifferent but inactive.  No nearby two-owner root,
  support persistence, Bellman edge, payoff return, or uniform-equilibrium
  payoff is produced.
- The result does not consume the paid near-return question by itself.

## Checked Lean realization

The useful statement is proved in Lean in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinFourOffMinimumChargedBlockerGate.lean`.
The headline declaration
`exists_macroscopicDebtDrop_or_chargedSoloBlockerGate` gives the literal
positive-`liminf` debt-drop alternative or a strict-subsequence blocker gate
from the displayed carrier, exact-root, floor, and fixed-charge source data.
The resulting `FinFourChargedSoloBlockerGate` retains the source carrier pair,
the limiting exact root, the quantitative rate bounds, the unique-debtor
identities, the floor-safe blocker-tail exactness, and a blocker attaining the
maximum outsider joining gap.

This earns `M`, `L`, and `A`.  It has a checked downstream obstruction consumer
through `FinFourChargedSoloBlockerGate.pairPremium_or_every_exactRepayment` in
`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/ChargedSoloBlockerGateRepayment.lean`,
so it also earns `C` for the stated reduction.  The consumer does not produce a
uniform-equilibrium payoff.  In particular, the synthetic updated blocker tail
is proved boxed, floor-safe, and exact, but is not asserted to belong to the
terminal-semantic carrier.
