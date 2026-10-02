# A four-player solo wall forces carrier debt descent or a two-debtor stationary source

The full packet is checked in Lean across
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinFourSoloWallDispatch.lean`.
In particular, `exists_strictCarrierDebtDescent_of_opponentAbsorptionFloor`,
`exists_first_soloPrefix_outsiderWall`,
`pairPremium_pairJoin_or_leaveJoinStationaryTwoDebtorHandoff`,
`exists_uniformSoloSemanticSpine_of_finitePrefixes`, and
`not_exists_outwardUniformSoloCarrierChain_of_normal` cover the compact root
separation, strict carrier-debt descent, first outsider wall, reversed finite
window compactification, and exclusion of an infinite uniformly interior
outward solo chain.  The useful generic free-coordinate identity
`persistentBase_inducedNash_free_semantics` is also checked.

Section 19 is checked by
`nonempty_finFourPairBaseStationaryTwoDebtorHandoff`
(`UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/PairBaseStationaryTwoDebtorHandoff.lean`).
It constructs the persistent-base Nash point with quantitative free
absorption and a heavy strict-superset atom, solves both free coordinates,
localizes positive debt to the base with a terminal-gap debtor, and supplies a
literal paid first-disagreement row on the actual stationary profile.  The
charged-gate composition
`FinFourChargedSoloBlockerGate.pairBaseHandoff_or_leaveJoinHandoff_or_everyExactRepayment`
is checked in
`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/ChargedSoloBlockerClosureDispatch.lean`.
The packet therefore has `M`, `L`, and `A`, with `C` for its exact internal
dispatches.  It has no payoff-return or uniform-payoff `C`.

Author: `CODEX_CEDAR`

Independent reviews of the new wall dispatch:

- [CODEX_EULER](../feedback/CODEX_CEDAR__FOUR_PLAYER_CONJECTURE_CAPSTONE__BY_CODEX_EULER__PROPOSITION_9.md)
- [CODEX_RAMSEY](../feedback/CODEX_CEDAR__FOUR_PLAYER_CONJECTURE_CAPSTONE__BY_CODEX_RAMSEY__PROPOSITION_9.md)

Independent reviews of the composed stationary handoffs:

- [Section 18 review](../feedback/CODEX_EULER__FIN4_SEARCH_SPACE_INVENTORY__BY_CODEX_RAMSEY__SECTION_18.md)
- [Section 19 review](../feedback/CODEX_EULER__FIN4_SEARCH_SPACE_INVENTORY__BY_CODEX_RAMSEY__SECTION_19.md)
- [Section 21 composition review](../feedback/CODEX_EULER__FIN4_SEARCH_SPACE_INVENTORY__BY_CODEX_RAMSEY__SECTION_21.md)

Upstream reviewed producers:

- [off-minimum charged blocker gate](../formalized/FIN4_OFF_MINIMUM_CHARGED_BLOCKER_GATE.md);
- [charged blocker premium/repayment split](../formalized/FIN4_CHARGED_BLOCKER_COLLISION_OR_REPAYMENT_SPLIT.md).

## Exact statement

Let the player type be literally `Fin 4`.  Let `reward` be a finite quitting
reward table, choose `M>=1` bounding every reward coordinate in absolute
value, and assume the game has no uniform-equilibrium payoff.  Fix

```text
witness : QuittingTerminalExploitabilityWitness reward,
Gamma=witness.terminalGap>0,
```

and write

```text
s_h=reward({h})_h,
P_h=quittingPunishmentValue reward h.
```

The checked four-player residual gives `P_h<=s_h` for every player.

Suppose the zero-drop branch of the upstream charged blocker gate has produced
a literal terminal-semantic carrier pair `X`, a player `k`, a rate `x`, and
constants `alpha,d,D>0` such that

```text
alpha<=x<=1-d,
q=soloRoot(k,x),
IsεQuittingRootNash reward X.1 0 q,
d_k(X)=D,
d_h(X)=0  for h!=k,
X.1_k=s_k.                                                (1)
```

Here `d_h(X)=X.2_h-X.1_h` is unrestricted behavioral semantic debt.  The
upstream compact blocker theorem also supplies a positive number `g_a` such
that, at every such gate, some outsider `i!=k` satisfies

```text
g_(k,i)(x)
 =(1-x)s_i+x reward({k,i})_i-reward({k})_i
 >=g_a>0.                                                  (2)
```

Then finitely many literal exact semantic prefixes on the same reward table
lead to at least one of the following two outcomes.

1. **Strict source-native semantic-debt descent.**  There are a carrier pair
   `W`, an exact product root `z` at the prescribed tail `W.1`, and
   `omega>0` such that

   ```text
   W.1 -> Prefix(z,W).1,
   absorption(z)>=omega,
   D(Prefix(z,W))<=D(W)-omega*D,
   D(W)=D.                                                (3)
   ```

   Both payoff annotations are boxed and punishment-floor safe.  The arrow
   is the exact Bellman relation's tail-to-current orientation.  The pair
   prefix is a literal terminal-semantic carrier prefix.

2. **Actual stationary two-debtor semantic handoff.**  One of the following
   same-table stationary sources exists.

   - The checked singleton-base object
     `FinFourLeaveJoinStationaryTwoDebtorHandoff` is nonempty; or
   - four pairwise distinct labels `k,i,j,o` and a stationary product profile
     `sigma` exist in which `k,i` Quit surely and `j,o` play a Nash point of
     the induced binary game, with semantic pair `(U,B)`, such that

     ```text
     B_j=U_j,                 B_o=U_o,
     P_j<=U_j,                P_o<=U_o,
     {h:B_h-U_h>0} subset {k,i},
     max(B_k-U_k,B_i-U_i)>=Gamma,                       (4)
     Pr_sigma(terminal strictly contains {k,i})
       >=Gamma/(Gamma+2M).                              (5)
     ```

     In the second subcase one strict superset of `{k,i}` has mass at least

     ```text
     Gamma/[3(Gamma+2M)],                               (6)
     ```

     The selected positive-mass atom has a strict terminal-witness membership
     toggle, and the stationary pure-time decoder supplies a literal
     source-matched paid first-disagreement row for a debtor in `{k,i}` with
     gain `Gamma`.

The alternatives are inclusive.  The theorem does not say that the
reselected stationary source is reached chronologically from `W`.

## Conjecture-facing change

The prior blocker gate stopped at a reached wall where an outsider strictly
wanted to Quit, because exact root selection could still choose all-Continue
or another solo root.  The present theorem eliminates that selection wall.
Changed solo roots can occur only finitely often: an infinite restart would
compactify backward to a fixed-owner semantic spine whose survival tends to
zero, contradicting punishment normality.

The only non-descent output is no longer a static pair or triple reward
comparison.  Section 18 turns a positive pair premium into either a checked
singleton-base stationary handoff or a full-gap pair-to-triple join; Section
19 turns the latter join into the pair-base stationary source in (4)--(6).
Thus the zero-drop solo wall has exactly two typed destinations:

- a strict exact carrier-debt descent; or
- an actual stationary source with two solved unrestricted coordinates, debt
  on at most two coordinates, a fixed nonsingleton atom, and a paid row.

This strictly narrows the paid branch.  It does not yet prove a payoff
near-return or a uniform-equilibrium payoff.

## Definitions and semantic audit

A product root uses independent private Quit/Continue randomization.  A solo
root makes only its owner Quit.  `IsεQuittingRootNash reward V 0 q` is exact
one-stage Nash optimality at continuation payoff `V`.

A terminal-semantic carrier pair is a prescribed payoff and its unrestricted
behavioral best-response envelope, or a compact limit of such pairs.  It need
not be attained by one behavioral profile.  Semantic prefixing executes the
product row and uses the carrier tail after joint Continue; it preserves the
carrier.  Debt is computed from the unrestricted behavioral envelope, not a
stationary-regret proxy.

In the stationary handoff, one or two sure quitters absorb at date zero.
Consequently any unilateral behavioral deviation by a free player is decided
at date zero, so its induced binary-game Nash inequality is its full
unrestricted best-response inequality.  No public correlation, bounded
controller, or stationary-deviation restriction is used.

## Proof

### 1. Reach a strict blocker wall

At any gate satisfying (1), choose an outsider `i` maximizing (2).  The
reviewed solo-prefix wall theorem repeatedly prefixes the same exact solo
root.  It preserves the carrier, the complete unique-debtor vector, `D`, and
the owner equality `X.1_k=s_k`.  After finitely many prefixes it reaches a
carrier pair `W` at which the chosen outsider has strictly positive
Quit-minus-Continue difference against that solo root.

Put

```text
c=reward({k,i})_i-reward({k})_i.                       (7)
```

If `c>0`, go to Step 4.  Assume henceforth `c<=0`.

### 2. Every non-solo exact root gives strict debt descent

Let `E(W)` be the set of exact product roots at `W.1`.  The product-root cube
is compact, the exact Nash graph is closed, and finite mixed-Nash existence
makes `E(W)` nonempty.  Hence `E(W)` is compact.

Suppose no root in `E(W)` is supported in the singleton face `{k}`.  Zero
opponent absorption for `k` is exactly the assertion that every outsider of
`k` Continues surely, so the continuous opponent-absorption function is
strictly positive throughout `E(W)`.  Therefore

```text
omega=min_(z in E(W)) OppAbs_k(z)>0.                   (8)
```

Choose any `z in E(W)`.  Exact semantic prefixing preserves zero debt for
every outsider.  The checked block-action debt transport for the sole debtor
gives

```text
d_k(Prefix(z,W))
 <=OppContinue_k(z)d_k(W)
 <=(1-omega)D.                                         (9)
```

This proves (3), including absorption at least `omega`.  Carrier closure and
exact floor propagation give the stated semantic and floor provenance.

### 3. A solo exact root strictly raises the owner rate, and infinite restart is impossible

Otherwise select an exact root in `E(W)` supported inside `{k}` and call its
owner rate `y`.  For the wall blocker, the Quit-minus-Continue difference
against a solo environment of rate `u` is the affine function

```text
F(u)=(1-u)(s_i-W.1_i)+u c.                            (10)
```

The incoming gate has `F(x)>0`; exactness of the selected root, in which `i`
Continues surely, gives `F(y)<=0`.

If `y=0`, all-Continue exactness gives `F(0)<=0`, and `c<=0` then contradicts
`F(x)>0`.  If `c=0`, `F(x)>0` implies `F(u)>0` for all `u<1`, whereas the
checked terminal-gap marginal cap gives `y<=1-d<1`.  Thus `c<0`.  Formula
(10) is then strictly decreasing and yields

```text
x<y<=1-d.                                             (11)
```

The wall debt-preservation identity makes `(W,y)` another gate satisfying
(1), with the same owner and debt vector.  Restart the construction.

If restart never terminates, flatten its finite repeated-root words into an
outward sequence

```text
Z_(n+1)=Prefix(root_n,Z_n),
alpha<=root_n(k)(Quit)<=1-d,                           (12)
```

with every outsider of `k` pure Continue.  Choose terminal indices `n_m>=m`
and a diagonal subsequence such that, for every fixed backward depth `t`,

```text
pair_t=lim_m Z_(n_m-t),
rho_t =lim_m root_(n_m-t-1)                            (13)
```

exist.  Continuity and closedness give

```text
pair_t=Prefix(rho_t,pair_(t+1)),
rho_t exact at pair_(t+1).1.                          (14)
```

This is the required behavioral-spine orientation; it is why the terminal
windows are reversed.  Every limiting owner hazard is at least `alpha`, so
the spine survival is at most `(1-alpha)^n` and tends to zero.  The first
root also has Continue mass at least `d`.  The checked solo-spine occupation
theorem then gives `s_k<P_k`, contradicting `P_k<=s_k`.  Hence restart ends
after finitely many walls.

### 4. Every positive pair premium enters a stationary two-debtor source

If `c>0`, the checked terminal membership-toggle theorem applied to the pure
pair `{k,i}` gives either a member leave or an outsider join with the full gap
`Gamma`.  The member cannot be `i`, since that would contradict `c>0`.

In the member-leave branch, punishment normality supplies the complementary
join needed by the checked
`FinFourLeaveJoinStationaryTwoDebtorHandoff` constructor.

In the outsider-join branch choose the joining outsider `j` and the remaining
label `o`.  Keep `{k,i}` sure and choose a Nash equilibrium `(x,y)` of the
induced binary game on `{j,o}`.  If `x<1`, Continue support for `j` and
affineness of its endpoint difference imply

```text
y>=Gamma/(Gamma+2M);
```

if `x=1`, free-player absorption is already one.  This proves (5).  Expanding
the independent law gives the three strict-superset atoms, whose sum is the
left side of (5), and hence (6).

The two sure base players make the induced Nash inequalities valid against
all behavioral deviations of `j,o`, proving zero debt and punishment-floor
safety in those coordinates.  The terminal witness supplies debt at least
`Gamma` in a base coordinate.  The checked stationary cap identity and
Quit-now/Never decoder then give the source-matched paid row.  This proves
the second main alternative.

## Boundary tests

1. **The relation orientation is not behavioral chronology.**  If
   `Z'=Prefix(z,Z)`, the exact Bellman relation is `Z.1 -> Z'.1`; execution
   reads from the current row toward continuation `Z`.  Reversing this arrow
   makes the diagonal formula (14) false.

2. **The `c=0` boundary is excluded only because the owner is bounded away
   from sure Quit.**  With `F(u)=(1-u)a` and `a>0`, the only zero is `u=1`.
   The marginal cap `u<=1-d` is therefore essential.

3. **Compact separation is source-specific.**  The number `omega` in (8) is
   positive for the reached fixed wall, but no game-wide lower bound is
   claimed.  If singleton-face exact roots approached the set, the minimum
   could vanish; that is precisely the restart branch.

4. **The pair-base atom constant is sharp for this pigeonhole.**  The three
   strict supersets may have equal masses, so total mass `alpha` guarantees
   only one atom of mass `alpha/3` without extra data.

5. **Stationary reselection is nonchronological.**  The induced Nash point is
   chosen afresh from the same reward table.  Nothing in the construction
   makes it the continuation of the wall prefix; the theorem states no such
   path.

## Source correspondence

The literal carrier gate and constants are supplied by the two reviewed
upstream packets named above.  Proposition 9 in
`notes/CODEX_CEDAR__FOUR_PLAYER_CONJECTURE_CAPSTONE.md` is the new wall
dispatch.  Sections 18--19 of
`notes/CODEX_EULER__FIN4_SEARCH_SPACE_INVENTORY.md` supply the two stationary
handoffs, and its independently reviewed Corollary 21.1 is the exact
composition used here.  The packet expands that corollary only to make the
export self-contained.

The proof uses the following checked declarations:

- carrier prefix closure and the block-action debt identity in
  `UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`;
- the exact-root marginal cap in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/TerminalGapExactRootMarginalCap.lean`;
- `QuittingTerminalExploitabilityWitness.atomic_restrictions_of_soloSemanticSpine_survival_zero`
  in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticSoloSpineOccupation.lean`;
- `QuittingTerminalExploitabilityWitness.exists_leave_or_join_gain` in
  `UniformEquilibrium/Quitting/Classification/TerminalExploitabilityToggles.lean`;
- `exists_atomicCollision_gain_of_normal` in
  `UniformEquilibrium/Quitting/Boundary/Repair/PunishmentNormalAtomicCollision.lean`;
- `nonempty_finFourLeaveJoinStationaryTwoDebtorHandoff` in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/LeaveJoinStationaryTwoDebtorHandoff.lean`;
- `quittingPersistentBaseNashSet_nonempty` and the persistent-base root
  definitions in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseInducedGame.lean`;
- `quittingTerminalSemanticPair_stationary_envelope_eq_cap` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticNegativeVertexGerm.lean`;
- `exists_oriented_quitNow_never_gap_of_stationary_cap_debt` in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/LargeBaseStationarySemanticHandoff.lean`;
- `exists_quittingPaidFirstDisagreementRow_of_pureTimePayoff_sub` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPaidFirstDisagreement.lean`.

The wall restart, its backward compactification, and the finite composition
with the pair-base handoff are new ordinary mathematics.  No literature claim
is strengthened or used as theorem evidence.

## Adapter and consumer

The adapter is carrier-enriched.  A generic payoff-only exact floor path does
not supply the semantic pairs in (1).  The upstream zero-drop compact limit
does, and the wall construction thereafter uses literal carrier prefixes.

The descent arm reduces the nonnegative carrier obstruction `D-D_*`; it is an
exact semantic edge, but the theorem does not prove that the same gate
regenerates after support changes.  The stationary arm enters the existing
paid-source lane with a fixed nonsingleton atom and at most two debtors.  The
intended final consumer remains
`PaidFirstDisagreementAdmissiblePayoffNearReturnConsumer` in
`UniformEquilibrium/Diagnostics/Quitting/PaidFirstDisagreementPayoffNearReturn.lean`.
The later pair-base fixed-law adapter proves that its returned reset face has
exactly the stationary paid target's prescribed payoff.  Even so, neither arm
constructs the positive punishment-floor-admissible endpoint-Nash edge and
return path required by `QuittingFixedLawResetAdmissibleClosureSeam`, so the
consumer is not yet supplied.

## Lean coverage

The source-native descent, first-wall, finite-window compactification, and
infinite-spine exclusion are checked in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinFourSoloWallDispatch.lean`.
The singleton-base stationary branch is checked by
`nonempty_finFourLeaveJoinStationaryTwoDebtorHandoff`
(`UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/LeaveJoinStationaryTwoDebtorHandoff.lean`).
The pair-base branch is checked by
`nonempty_finFourPairBaseStationaryTwoDebtorHandoff`
(`UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/PairBaseStationaryTwoDebtorHandoff.lean`),
and the charged-gate premium/repayment composition is checked by
`FinFourChargedSoloBlockerGate.pairBaseHandoff_or_leaveJoinHandoff_or_everyExactRepayment`
(`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/ChargedSoloBlockerClosureDispatch.lean`).

The checked declarations retain the `c=0`/`y=1` boundary distinction, the
diagonal extraction's late-index condition, tail-to-current semantic-prefix
typing, and the literal three-atom mass expansion.  They do not package the
whole mathematical narrative as one new universal conjecture-closing
declaration.

## Scope and nonclaims

- The player type is literally `Fin 4`; no reindex adapter is claimed.
- The initial gate is a literal carrier limit, not necessarily the semantic
  pair of one attained behavioral profile.
- The descent amount `omega*D` is positive at the selected wall but is not
  uniform across future support-changing iterations.
- The stationary handoff is an actual behavioral source but is not reached
  from the wall by play, conditioning, or Bellman continuation.
- A nonsingleton terminal atom is not an exact Bellman edge charge.
- The theorem does not construct a payoff near-return, a positive admissible
  cycle, a uniform-equilibrium payoff, or a proof of the full conjecture.
