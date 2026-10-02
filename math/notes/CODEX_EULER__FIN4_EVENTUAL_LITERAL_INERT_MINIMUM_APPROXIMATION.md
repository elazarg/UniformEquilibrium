# Fin4 minimum-approaching paid cap ports are eventually literally inert

Author: `CODEX_EULER`

Status: **independently reviewed PASS; internal, not export-ready.**  Review:
[`CODEX_RAMSEY`](../feedback/CODEX_EULER__FIN4_EVENTUAL_LITERAL_INERT_MINIMUM_APPROXIMATION__BY_CODEX_RAMSEY.md).
This strictly sharpens the maintained Fin4 inert boundary, but it does not
consume that boundary or prove a uniform-equilibrium payoff.

## 1. Question and checked interfaces

Let `reward` be a quitting reward table on literal `Fin 4`.  Assume a positive
terminal exploitability gap `Gamma`, and let

```text
X_* = (U_*, B_*)
```

be the strict positive minimum plateau supplied on the no-uniform-payoff arm.
Write `D_* = D(X_*) > 0`.

The checked carrier-density theorem

```text
HasTerminalExploitabilityGap.nonempty_actualProfilePaidCapMinimumApproximation
```

in
`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/ActualProfilePaidCapMinimumApproximation.lean`
already supplies actual profiles `sigma_n`, full-gap paid cap sources and
summable ports such that

```text
Sem(sigma_n) -> X_*,
D(Sem(sigma_n)) -> D_*,
A_n -> 0,
rho_n -> 0.
```

Indeed the checked inequalities in
`PaidCapMinimumFiberContraction.lean` are stronger than the proposed abstract
sequence dichotomy:

```text
D_* A_n   <= D(Sem(sigma_n)) - D_*,
D_* rho_n <= 2 R (D(Sem(sigma_n)) - D_*).
```

Thus no subsequence of these ports can have total absorption bounded below by
a fixed positive constant.  The purported first arm is impossible already;
there is no new invocation of the cumulative-charge consumer to make.

The additional Fin4 input is

```text
exists_open_exactAllContinueTube_debtHomotopy
```

in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinFourStrictMinimumPlateauIsolation.lean`.
It gives an open payoff tube `T` containing the whole closed debt segment

```text
H(t) = B_* - t (B_* - U_*),  0 <= t <= 1,
```

and says that all Continue is the unique exact product-root Nash equilibrium
against every tail in `T`.  In particular, `B_* = H(0)` belongs to `T`.
The same file packages the required same-table minimum point and tube as

```text
exists_finFour_strictMinimumPlateau_openDebtHomotopyTube_of_no_uniformPayoff.
```

## 2. Eventual literal-inertness theorem

### Theorem 2.1

Choose the carrier-density profiles `sigma_n` converging semantically to the
strict Fin4 minimum plateau `X_*`, and for each `n` choose the actual full-gap
paid cap port returned by
`nonempty_actualProfilePaidCapMinimumApproximation`.  Then there is `N` such
that for every `n >= N`:

1. every canonical cap root prefixed outside `sigma_n` is literally the
   all-Continue root;
2. every finite cap-prefix profile has exactly the same full terminal-semantic
   pair as `sigma_n`;
3. the complete port absorption is exactly zero, not merely small; and
4. the selected port satisfies

   ```text
   QuittingPaidCapLiftedSource.InertStall source_n port_n.
   ```

Consequently the full-gap paid row on `sigma_n` is transported losslessly to
every finite literal prefix with reach one and unchanged gain.

In particular, if the sole hypothesis is nonexistence of a uniform-equilibrium
payoff, first choose a `QuittingTerminalExploitabilityWitness` using
`nonempty_terminalExploitabilityWitness_of_not_exists_uniformEquilibriumPayoff`.
Use its positive `terminalGap` and gap field in the actual-profile adapter,
and use
`exists_finFour_strictMinimumPlateau_openDebtHomotopyTube_of_no_uniformPayoff`
to choose the same-table `X_*` and tube.  Thus the statement is not conditional
on an extra supplied plateau or gap beyond the maintained Fin4 counterexample
arm.

### Proof

Semantic convergence and continuity of the second projection give

```text
B(sigma_n) -> B_*.
```

Since `T` is open and contains `B_*`, choose `N` such that
`B(sigma_n) in T` for every `n >= N`.  Fix such an `n` and abbreviate
`sigma = sigma_n`.

We prove simultaneously by induction on the prefix depth `m` that

```text
Sem(PrefixProfile(sigma,m)) = Sem(sigma)                 (2.1)
```

and that the root used at depth `m` is all Continue.  The semantic equality is
trivial at depth zero.  Assuming (2.1), the selected canonical root is exact
Nash against the envelope of the current prefix profile by
`quittingCapLiftedPrefixRoot_exactNash`.  That envelope equals `B(sigma)`,
which lies in `T`.  Uniqueness in the tube therefore identifies the selected
root with all Continue.

The successor semantic pair is

```text
quittingTerminalSemanticPrefix reward allContinue Sem(sigma).
```

Because this all-Continue root is exact Nash at the cap, the checked identity

```text
quittingTerminalSemanticPrefix_allContinue_eq_self_iff_isZeroNash_at_cap
```

in `UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean` makes this
pair exactly `Sem(sigma)`.  This closes the induction.

Every stage absorption is therefore zero.  The defining nonnegative series
for `source_n.totalAbsorption` is identically zero, hence its sum is zero.
Finally

```text
QuittingPaidCapLiftedSource.inertStall_of_totalAbsorption_eq_zero
```

packages all the literal semantic, reach, and paid-row conclusions in item 4.
QED.

## 3. Exact frontier change

The general finite-player theorem gives only

```text
A_n -> 0 and rho_n -> 0.
```

On the reviewed Fin4 strict minimum plateau, Theorem 2.1 improves this to

```text
eventually A_n = 0 and every selected port is a literal inert stall.   (3.1)
```

This realizes the inert obstruction at actual, full-gap behavioral sources
arbitrarily close to the minimum carrier point even when no behavioral profile
realizes the minimum itself.  It is therefore a genuine sharpening of the
live inert boundary, but in the unfavorable direction: local minimum-fiber
isolation forces the obstruction rather than eliminating it.

## 4. Why the existing Fin4 double port does not close (3.1)

The checked

```text
FinFourSingletonBaseResetRepairPaidCapDoublePort.
  sourceDescent_or_repairedDescent_or_doubleInert
```

starts from a particular singleton-base same-law reset producer and its
literal owner repair.  No checked field says that either of those two actual
source semantic pairs approaches `X_*`, lies in the tube `T`, or has debt
tending to `D_*`.

Conversely, the arbitrary carrier-density profiles `sigma_n` in Theorem 2.1
do not carry the singleton-base/reset/repair structure required to construct
that double port.  Therefore one cannot identify the two ports in the double
construction with two members of the sequence above.  Even if that missing
source alignment were supplied, the declared double-port conclusion permits
both ports to be inert and hence would still be compatible with (3.1).

## 5. Why the Fin5 retained atom does not exclude eventual inertness

The reviewed Fin5 frozen-tableau theorem transports a literal chronological
atom through deletion and through every inert cap prefix.  Its point is
precisely that a positive source atom and a full-gap paid row are compatible
with a unique all-Continue cap selector:

* the atom and paid row live in the unchanged literal suffix law;
* cap roots are selected against the behavioral envelope, not the prescribed
  payoff; and
* a favorable atom contribution need not dominate the other events changed by
  a unilateral stopping-time deviation.

Thus retained atom mass supplies no positive **outer cap-root absorption**.
It neither contradicts (3.1) nor activates the cumulative-charge consumer.
The explicit regression in
`notes/CODEX_RAMSEY__FIN5_NEVER_ENDPOINT_INERT_FROZEN_MARKED_TABLEAU.md`
already shows local compatibility of a positive atom, positive behavioral
debt, and a unique all-Continue cap root.  Moreover, the Fin5 retained-atom
source is a selected literal Never endpoint, whereas the carrier-density
profiles above are unrelated reselections.

## 6. Novelty audit and nonclaims

Narrow searches inspected:

* `ActualProfilePaidCapMinimumApproximation.lean`;
* `PaidCapMinimumFiberContraction.lean`;
* `PaidCapPortExactTrichotomy.lean`;
* `TerminalSemanticFinFourStrictMinimumPlateauIsolation.lean`;
* `SingletonBaseResetRepairPaidCapDoublePort.lean`;
* the maintained paid question and the reviewed Fin5 frozen tableau.

The first file already declares convergence `A_n -> 0` and `rho_n -> 0`.
No inspected declaration or maintained document states eventual exact
inertness of the actual minimum-approximating ports.  The proof above is the
new composition of envelope convergence with the open tube and the literal
cap-prefix recursion.

This note does **not**:

* produce a uniform-equilibrium payoff or cumulative-charge near-return;
* attain the minimum carrier point by a behavioral profile;
* identify the paid observer with a reset, collision, deletion, or retained
  atom label;
* identify the arbitrary density sequence with the singleton double port or a
  Fin5 Never endpoint; or
* turn the persistent paid suffix row into a positive-charge Bellman edge.

The exact remaining consumer problem is stronger and cleaner: exclude or use
an actual sequence of full-gap paid profiles approaching `X_*` whose canonical
cap lifts are already literally inert at every sufficiently late index.

## 7. Lean handoff

The natural theorem should extend
`QuittingActualProfilePaidCapMinimumApproximation` in the literal `Fin 4`
no-uniform branch.  Obtain the selected `X_*` and `T` directly from
`exists_finFour_strictMinimumPlateau_openDebtHomotopyTube_of_no_uniformPayoff`,
then project
`semantic_tendsto` to the envelope coordinate and use eventual membership in
`T`.  For each late index, prove by induction on `m`:

```text
quittingTerminalSemanticPair reward
  (quittingCapLiftedPrefixProfile reward (profile n) m)
= quittingTerminalSemanticPair reward (profile n)
```

and

```text
quittingCapLiftedPrefixRoot reward
  (quittingCapLiftedPrefixProfile reward (profile n) m)
= quittingAllContinueRoot.
```

Then rewrite `QuittingPaidCapLiftedSource.totalAbsorption` as the sum of the
zero stage absorptions and invoke
`inertStall_of_totalAbsorption_eq_zero`.  The proof must use the tube at the
**envelope/tail** coordinate `B(sigma_n)`, not at the prescribed coordinate
`U(sigma_n)`.
