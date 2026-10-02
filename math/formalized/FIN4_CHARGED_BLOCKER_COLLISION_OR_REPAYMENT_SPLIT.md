# A charged four-player blocker forces pair premium or exact repayment

Author: `CODEX_CEDAR`

Independent reviews:

- [CODEX_RAMSEY](../feedback/CODEX_CEDAR__FOUR_PLAYER_CONJECTURE_CAPSTONE__BY_CODEX_RAMSEY__PROPOSITION_6.md)
- [CODEX_EULER](../feedback/CODEX_CEDAR__FOUR_PLAYER_CONJECTURE_CAPSTONE__BY_CODEX_EULER__PROPOSITION_6.md)

Upstream reviewed producer:
[off-minimum charged blocker gate](FIN4_OFF_MINIMUM_CHARGED_BLOCKER_GATE.md)

## Exact statement

Let the player type be literally `Fin 4`, and let

```text
reward : {S : Finset (Fin 4) // S.Nonempty} -> Payoff (Fin 4)
```

be a finite quitting reward table.  Choose `M>=1` with
`|reward(S)_j|<=M` for every nonempty coalition `S` and player `j`.  Assume
that the game has no uniform-equilibrium payoff, and let `Gamma>0` be its
fixed terminal exploitability gap.  Write

```text
s_j=reward({j})_j,
P_j=quittingPunishmentValue reward j.
```

The checked four-player hard residual gives

```text
P_j<=s_j                                                     (1)
```

for all four players.

Fix `a>0`.  Suppose the zero-debt-drop arm of the reviewed off-minimum
charged blocker gate has supplied distinct players `k,i`, a rate `p`, and a
boxed punishment-floor payoff `Y` such that

```text
alpha=a/8,
d=Gamma/(4M),
alpha<=p<=1-d,                                               (2)
q=soloRoot(k,p),
Y_k=s_k,
IsExactQuittingRootNash reward Y q.                          (3)
```

For every owner `ell`, outsider `j!=ell`, and rate `x`, put

```text
g_(ell,j)(x)
  =(1-x)s_j+x reward({ell,j})_j-reward({ell})_j,
G_ell(x)=max_(j!=ell) g_(ell,j)(x).                         (4)
```

Because (2) supplies an element of `[alpha,1-d]`, that interval is nonempty.
Define

```text
g_a=min_(ell in Fin 4, x in [alpha,1-d]) G_ell(x).           (5)
```

Then

```text
g_a>0.                                                       (6)
```

The blocker `i` may be reselected among the outsiders of `k` so that it
attains `G_k(p)`.  Define

```text
b=reward({k,i})_i,
R=reward({k})_i,
Q=(1-p)s_i+p b,
g=Q-R,
T=(Q-pR)/(1-p).                                             (7)
```

The upstream gate permits replacing only coordinate `i` of its tail by `T`;
we continue to call the resulting floor-safe boxed payoff `Y`.  The root
`q=soloRoot(k,p)` is still exact at `Y`, player `i` is indifferent and plays
Continue, and

```text
g>=g_a,
T-Q=p g/(1-p)>=alpha g_a.                                  (8)
```

At least one of the following two alternatives holds.

1. **Pair-reward premium.**

   ```text
   reward({k,i})_i-reward({k})_i>=g_a/2.                    (9)
   ```

2. **Source-anchored one-coordinate exact repayment.**  Starting with
   `V_0=Y` and `q_0=q`, extend the supplied first row to any infinite exact
   punishment-floor Nash--Bellman orbit

   ```text
   V_(t+1)=Succ(V_t,q_t).                                   (10)
   ```

   Then

   ```text
   V_1(i)=Q,                                                (11)
   ```

   the annotations converge coordinatewise to a payoff `L`, and

   ```text
   L_i-Q>=alpha g_a/2.                                      (12)
   ```

   Hence at some finite `t>=1`,

   ```text
   V_t(i)-V_1(i)>=alpha g_a/4.                              (13)
   ```

   In the exact Bellman-relation orientation, (10) gives the finite path

   ```text
   V_t -> V_(t-1) -> ... -> V_1 -> V_0.                    (14)
   ```

   Its last edge is the originally supplied root `q_0`, whose absorption
   charge is `p>=alpha`.  Thus the fixed one-coordinate repayment occurs on
   a literal exact floor path anchored to the charged source row.

The first alternative is a strict reward-table comparison, not positive
probability of the coalition `{k,i}`.  The second alternative controls only
coordinate `i`; it is not a payoff near-return.

## Conjecture-facing change

The live producer in
[`PAID_ADMISSIBLE_PAYOFF_NEAR_RETURN.md`](../questions/PAID_ADMISSIBLE_PAYOFF_NEAR_RETURN.md)
asks for exact punishment-floor paths containing one uniformly charged edge
and having arbitrarily close endpoint payoff vectors.  The upstream blocker
gate stopped at an inactive outsider made exactly indifferent at a synthetic
floor-safe tail.

This packet removes the possibility that the inactive gate is arbitrarily
flat.  On every fixed charge cell it has one uniform game-dependent gap
`g_a>0`.  That gap must appear in one of the two maintained nonlocal escape
mechanisms:

- a fixed pair-collision reward premium; or
- a literal exact floor path which retains the original charged edge and
  repays a fixed amount in the blocker coordinate.

This is a strict quantitative reduction of the zero-debt-drop arm.  What
remains is to turn the pair premium into source-matched collision/debt spend,
or synchronize the other three payoff coordinates in the repayment arm.

## Definitions and semantic audit

A product root consists of independent Boolean Quit/Continue laws for the
four players.  `soloRoot(k,p)` makes only `k` Quit with probability `p`.
There is no public correlation.  Its absorption charge is exactly `p`.

`IsExactQuittingRootNash reward V q` means exact one-stage Nash optimality at
the prescribed continuation payoff `V`.  The forced-action inequalities are
over the two current actions.  Because a player's own mixing rate does not
alter that player's two forced-action endpoints, an inactive indifferent
player is not thereby proved to enter the support.

The punishment floor is the unrestricted behavioral punishment value.  Each
annotation in (10) lies in the canonical reward box and above that floor.
Ordinary finite mixed-Nash existence selects an exact product root at each
new boxed floor tail; exact successor and floor invariance then permit
dependent choice.  The orbit is a sequence of exact Bellman annotations, not
a terminal behavioral profile.  Its limit is likewise an annotation, not a
realized terminal payoff.

The terminal exploitability witness bounds every finite exact floor prefix.
It therefore makes the orbit's absorption masses summable, makes its value
increments absolutely summable, and supplies the all-orbits limit used in
(12).  This use of unrestricted terminal deviations occurs through the
checked witness and the behavioral punishment floor; the packet does not
replace them by stationary deviations.

## Proof

### 1. The compact blocker gap is positive

Fix an owner `ell` and `x in [alpha,1-d]`.  Suppose `G_ell(x)<=0`.
At the full singleton payoff vector `r_ell=reward({ell})`, the owner is
indifferent under `soloRoot(ell,x)`: both its Quit endpoint and its Continue
endpoint equal `s_ell`.  Formula (4) says that every outsider's Quit-minus-
Continue endpoint difference is nonpositive.  Hence the positive solo root
is exact endpoint Nash at `r_ell`.

By (1), `P_ell<=s_ell`.  The checked punishment-completed solo compiler then
makes `r_ell` a uniform-equilibrium payoff.  This contradicts the standing
no-uniform branch.  Therefore

```text
G_ell(x)>0                                                (15)
```

for every owner and every rate in the compact interval.  Each `G_ell` is the
maximum of three affine functions.  Continuity, finiteness of the owner set,
and compactness now prove (6).

The interval qualification is sharp at the level of the definition: if
`alpha>1-d`, the set in (5) is empty and no minimum `g_a` is defined.  In the
actual zero-drop arm this cannot occur, because the supplied `p` satisfies
(2).

### 2. The exact seam

Choose `i` attaining `G_k(p)`.  Then (4), (6), and (7) give

```text
g=Q-R=G_k(p)>=g_a.                                      (16)
```

The upstream endpoint-coordinate replacement proves that `T` is boxed and
floor-safe, and that changing only coordinate `i` preserves every other
player's root condition.  For player `i`, the definition of `T` gives

```text
(1-p)T+pR=Q=(1-p)s_i+p b.                              (17)
```

Thus its Continue and Quit endpoints coincide.  Rearranging (17) gives

```text
T-Q=p(Q-R)/(1-p)=p g/(1-p),                            (18)
```

which proves (8), since `p>=alpha` and `p<1`.

### 3. Pair premium or solo deficit

If `b-R>=g/2`, (9) follows from (16).  Otherwise

```text
b-R<g/2.                                               (19)
```

Using

```text
g=(1-p)(s_i-R)+p(b-R),                                 (20)
```

we obtain

```text
s_i-Q
 =p(g-(b-R))/(1-p)
 >p g/(2(1-p))
 =(T-Q)/2
 >=alpha g_a/2.                                       (21)
```

This is the fixed blocker-coordinate deficit immediately after the charged
row.

### 4. Exact repayment on every anchored extension

The initial tail is boxed and above the punishment floor, and `q_0=q` is
exact there.  At each later boxed floor tail, finite mixed-Nash existence
and exact floor propagation supply the next exact root and successor.
Dependent choice therefore gives (10) while preserving the specified first
row.

The first successor in coordinate `i` is its Continue endpoint in (17), so
(11) holds.  Under the terminal exploitability witness, the checked all-
orbits limit theorem supplies `L` and proves

```text
L_i>=s_i.                                               (22)
```

Combining (21) and (22) proves (12).  Coordinate convergence then gives a
finite `t` satisfying (13).  Reversing the annotation recursion gives the
relation path (14), and its final edge is exactly the initially fixed row of
charge `p>=alpha`.  This proves the second alternative.

## Boundary tests

These tests isolate the algebra.  They are not claimed counterexamples to the
uniform-equilibrium conjecture.

1. **Pair-premium side.**  Take `p=1/2` and, in outsider coordinate `i`,

   ```text
   s_i=0,  reward({k})_i=-2,  reward({k,i})_i=0.
   ```

   Then `Q=0`, `g=2`, `T=2`, and `b-R=2>=g/2`.  Equality (18) reads
   `T-Q=2` exactly.

2. **Repayment side and orientation.**  In the two displayed coordinates
   `k,i`, take

   ```text
   reward({k})=(0,0),
   reward({i})=(0,1),
   reward({k,i})=(0,0),
   p=1/2,  Y=(0,1).
   ```

   The solo-`k` row is exact at `Y`, has `Q_i=1/2`, `R_i=0`, `g=1/2`,
   `T_i=1`, and `b-R=0<g/2`.  Its successor is `(0,1/2)`.  A sure-`i` exact
   row then has successor `(0,1)=Y`, giving the literal reverse Bellman
   two-edge return and verifying the edge orientation.  This small table is
   outside the no-uniform branch; indeed the return is a solved positive
   cycle.  It is only a regression for the formulas and direction.

3. **Why the pair premium is not collision mass.**  The root in (3) has
   `q_i(Quit)=0`, so its coalition probability on `{k,i}` is exactly zero
   even when (9) is strict.  A separate support/root-selection argument is
   indispensable.

## Source correspondence

The actual-data producer is the reviewed packet
[`FIN4_OFF_MINIMUM_CHARGED_BLOCKER_GATE`](FIN4_OFF_MINIMUM_CHARGED_BLOCKER_GATE.md).
Its inputs are actual terminal-semantic carrier tails, exact roots at their
prescribed payoffs, a common positive absorption floor, and the literal
semantic debt drop under prefixing.  In its vanishing-drop arm it supplies
exactly (2)--(3) and (7)--(8), including box and punishment-floor safety.

That packet in turn uses the same-table declarations

- `uniformPayoff_or_nonempty_finFourQuantitativeFullSupportHardResidual` in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/FullSupportProjectiveQBarResidual.lean`;
- the debt ledgers in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPlateauDefectCharge.lean`;
- `exactFloorRoot_quitProbability_le_one_sub_terminalGap_div_four_mul` in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/TerminalGapExactRootMarginalCap.lean`;
- `soloReward_lt_punishmentValue_of_soloEndpointNash` in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/AtomicSoloLimitConsequences.lean`;
- `isUniformEquilibriumPayoff_soloReward_of_endpointNash_of_punishmentIR` in
  `UniformEquilibrium/Quitting/Punishment/SoloCycleCompletion.lean`; and
- `quittingPunishmentValue_le_stationaryUnilateralCap` in
  `UniformEquilibrium/Quitting/Stationary/MinMax.lean`.

The exact-orbit limit is the checked theorem
`QuittingTerminalExploitabilityWitness.infiniteOrbit_exists_value_limit` in
`UniformEquilibrium/Diagnostics/Quitting/Capacity/InfiniteOrbitLimit.lean`.
The orbit and its finite truncations are defined in
`UniformEquilibrium/Quitting/Bellman/Finite/PunishmentFloorInfiniteOrbit.lean`;
the floor and successor bounds used in its construction are in
`UniformEquilibrium/Quitting/Bellman/Finite/PunishmentFloorInfiniteOrbitLimit.lean`.

The new ordinary mathematics is the compact uniformization (5)--(6), the
pair-premium split (9)/(19), and the source-anchored use of the all-orbits
limit to obtain the finite exact repayment (13)--(14).  No literature result
is strengthened or attributed.

## Adapter and consumer

The adapter is the zero-drop output of the upstream carrier-enriched
semantic-prefix theorem.  A generic payoff-only floor path does not by itself
supply that terminal-semantic provenance.  Once the gate is produced, the
present theorem applies entirely inside the exact punishment-floor relation.

The intended consumer is
`PaidFirstDisagreementAdmissiblePayoffNearReturnConsumer` in
`UniformEquilibrium/Diagnostics/Quitting/PaidFirstDisagreementPayoffNearReturn.lean`,
or equivalently the unpackaged theorem
`quittingGame_exists_uniformEquilibriumPayoff_of_admissiblePath_payoffNearReturns`
in `UniformEquilibrium/Quitting/Projective/PunishmentFloorNearReturn.lean`.
This packet does not yet meet either consumer: (9) still needs an actual
source-matched collision/debt excursion, while (13) still needs simultaneous
control of the other three payoff coordinates.

## Lean handoff

The narrow new theorem should take the reviewed blocker-gate conclusion as
input rather than rebuilding terminal-semantic compactness.  Suggested shape:

```text
theorem chargedSoloBlocker_pairPremium_or_exists_exactRepayment
    (witness : QuittingTerminalExploitabilityWitness reward)
    (normal : forall j, IsQuittingNormalPlayer reward j)
    (ha : 0<a)
    (gate : FinFourChargedSoloBlockerGate reward a) :
    PairRewardPremium reward gate (g_a/2) \/
    ExistsAnchoredExactCoordinateRepayment reward gate
      (a/8) ((a/8)*g_a/4)
```

The proof should reuse:

- finiteness of the three-outsider maximum and compactness of the closed rate
  interval;
- the checked punishment-completed solo compiler for positivity of `g_a`;
- exact coordinate replacement from the blocker-gate theorem;
- an initial-root-preserving infinite-orbit extension lemma (or a short
  dependent-choice construction from finite mixed-Nash existence and floor
  invariance); and
- `infiniteOrbit_exists_value_limit`.

Finite regressions should verify (18), (21), the empty-interval guard, and the
reverse relation orientation.  Do not add the pair premium as a field of the
gate structure: it is one conclusion of the new theorem.

## Scope and nonclaims

- The player type is literally `Fin 4`; no reindex adapter is claimed.
- The rate interval in (5) is used only after the actual gate supplies the
  point `p` proving it nonempty.
- The blocker is selected after `k,p`; it need not be the originally named
  outsider before maximizing `G_k(p)`.
- The pair premium (9) is a reward-table comparison.  It does not imply that
  `{k,i}` occurs, that `i` has positive root support, or that semantic debt is
  spent.
- The repayment arm is an exact payoff-annotation path, not a claim that its
  limit is a realized terminal payoff.
- Only coordinate `i` is repaid.  The other three coordinates may make
  macroscopic excursions, so no payoff near-return or positive admissible
  cycle is obtained.
- The theorem does not close the paid exit, construct a uniform-equilibrium
  payoff, or prove the full four-player conjecture.

## Checked Lean realization

The compact uniform gap and universal exact-orbit repayment split are proved by
`FinFourQuantitativeFullSupportHardResidual.exists_pos_uniformSoloBlockerGap`
and `chargedSoloBlocker_pairPremium_or_every_exactRepayment` in
`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/ChargedSoloBlockerRepayment.lean`.
The actual gate adapter is
`FinFourChargedSoloBlockerGate.pairPremium_or_every_exactRepayment` in
`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/ChargedSoloBlockerGateRepayment.lean`.
It uses the gate's attained outsider argmax, extends the literal gate root to an
anchored exact punishment-floor orbit, and concludes the displayed fixed pair
premium or fixed blocker-coordinate repayment for every such anchored orbit.

The packet therefore has `M`, `L`, `A`, and `C` for this strict obstruction
split.  Its consumer is not a uniform-equilibrium compiler: the premium arm
still lacks source-matched collision mass, and the repayment arm controls only
one coordinate.
