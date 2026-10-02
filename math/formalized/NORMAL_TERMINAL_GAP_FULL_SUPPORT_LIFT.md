# Full normal core and a terminal gap force full singleton support

Author: `CODEX_EULER`

Independent review:
[`CODEX_RAMSEY`, terminal-gap lift](../feedback/CODEX_EULER__FOUR_PLAYER_SINGLETON_PACKET_DISPATCH__BY_CODEX_RAMSEY__SECTION_31.md),
[`CODEX_RAMSEY`, normal-core connector and composition](../feedback/CODEX_EULER__FOUR_PLAYER_SINGLETON_PACKET_DISPATCH__BY_CODEX_RAMSEY__SECTION_36.md)

## Exact statement

Let `I` be a finite player set and let

```text
r : {nonempty S subset I} -> R^I
```

be a finite quitting-game reward table.  First, for every player `i`,

```text
i in normalCore(normalizedSoloMatrix r)
  -> quittingPunishmentValue(r,i) <= r({i})_i.        (NC)
```

Thus the recursively normal core is contained in the set of
punishment-normal players.  This is a one-way inclusion.

For the quantitative lift, assume additionally that `n=|I|>=2`.  Write

```text
s_i = r({i})_i,
M   = max_{nonempty S,i} |r(S)_i|,
chi_i = quittingPunishmentValue(r,i).
```

Assume that every player is punishment-normal,

```text
chi_i <= s_i                                             (1)
```

and that there is a number `g>0` such that every behavioral profile `sigma`
has a player `i` and a complete unilateral behavioral deviation `tau_i` with

```text
U_i(sigma)+g <= U_i(tau_i,sigma_{-i}).                  (2)
```

Then there is a probability vector `mu` on `I` satisfying

```text
mu_i >= 1/C > 0,
C = 1 + 2M(n-1)/g,                                     (3)
```

and

```text
sum_j mu_j r({j})_i >= s_i             for every i.    (4)
```

Consequently, with target `v_i=s_i`, the pair `(mu,v)` is a
`QuittingNormalizedSingletonSourcePacket r` and has full support.

For the literal player type `I=Fin 4`, let
`witness : QuittingTerminalExploitabilityWitness r`.  Put

```text
g = witness.terminalGap,
C = 1 + 2M(4-1)/g.
```

Then the same reward table satisfies

```text
normalCore(normalizedSoloMatrix r)=univ,             (4F)
```

every player is punishment-normal by (NC), and there is a normalized
singleton source packet `packet` with

```text
packet.mass(i) >= 1/C > 0 for every i in Fin 4.      (4P)
```

In particular, at least one of the following holds for every quitting game on
`Fin 4`:

- the game has a uniform-equilibrium payoff;
- the same reward table has a normalized singleton source packet with support
  all four players; moreover its normalized solo matrix has full normal core
  and every player is punishment-normal.

The finite-valued complexity

```text
4 - card(packet.support)
```

therefore drops from every positive value to `0` in the no-uniform branch.
The hypothetical counterexample residual is simultaneously full support,
full normal core, and punishment-normal.  The result is not a solution of that
residual.

## Conjecture-facing change

The maintained question
[`FOUR_PLAYER_SINGLETON_PACKET_DISPATCH.md`](../questions/FOUR_PLAYER_SINGLETON_PACKET_DISPATCH.md)
accepts an exact residual with a finite-valued complexity that strictly
decreases.  Before the connector (NC), the support-two and support-three
branches required separate crossed-sign and outsider dispatches.  In the
no-uniform branch, however, the checked four-player theorem gives full normal
core.  The new connector makes all four players punishment-normal, and the
normal terminal-gap lift then produces a full-support packet directly.

Thus no proper packet support is a conjecture-facing residual.  The unresolved
object has support four and full normal core simultaneously, and every player
is punishment-normal.  This is strictly narrower than the bare full-support
obligation: subsequent matrix or nonsingleton dispatches may use every player
as both a stabilized core member and a punishment-normal player.

## Definitions and assumptions

A behavioral strategy may depend on the entire observed finite history.  A
behavioral profile uses independent private randomization at each information
set.  The quitting game terminates at the first date with a nonempty Quit
coalition and pays the corresponding terminal reward; Never pays zero.

Condition (2) is exactly `HasTerminalExploitabilityGap r g`.  It quantifies
over every behavioral profile and permits the deviating player to replace its
entire behavioral strategy.

A normalized singleton source packet consists of a nonnegative mass `mu`, a
target `v`, and the fields

```text
sum_i mu_i = 1,
v_i <= sum_j mu_j r({j})_i,
s_i <= v_i,
chi_i <= v_i,
0 < mu_i -> v_i=s_i.
```

For the constructed target `v=s`, the solo floors and all pins are
equalities, (1) is the punishment floor, and (4) is the only remaining packet
inequality.

## Source correspondence

The exact terminal-gap definition and its equivalence with nonexistence of a
uniform-equilibrium payoff are
`HasTerminalExploitabilityGap` and
`not_exists_uniformEquilibriumPayoff_iff_exists_terminalExploitabilityGap` in
`UniformEquilibrium/Quitting/Terminal/ExploitabilityGap.lean`.

Against a stationary product root, unrestricted behavioral deviations are
controlled and attained by the declarations

```text
quittingStationaryFullRateUnilateralCap
quittingTerminalPayoff_update_stationary_le_fullRateUnilateralCap
exists_behaviorStrategy_terminalPayoff_eq_fullRateUnilateralCap
isεAsymptoticNash_stationary_iff_fullRateUnilateralCap_le
```

in
`UniformEquilibrium/Quitting/Stationary/FullRateStationaryVerifier.lean`,
together with

```text
exists_quitNow_or_never_terminalPayoff_eq_unilateralCap
```

in `UniformEquilibrium/Quitting/Stationary/BestResponse.lean`.  Under strict
opponent contraction, these results say that the unrestricted cap is attained
by immediate Quit or Never.

The output structure is
`QuittingNormalizedSingletonSourcePacket` in
`UniformEquilibrium/Quitting/Classification/ThreePlayer/AnalyticPacket.lean`.
The new normal-core connector uses

```text
exists_core_blocker_of_mem_normalCore
normalizedSoloMatrix_eq_soloReward_sub
abnormal_singletonFloor_chain
```

from, respectively,
`Quitting/Classification/LCP/NormalCore.lean`,
`Quitting/Classification/PreemptionGateDictionary.lean`, and
`Quitting/Classification/AbnormalSingletonConsequences.lean`.

The full-normal-core conjunct (4F) is the checked theorem

```text
normalCore_eq_univ_of_fourPlayer_not_exists_uniformEquilibriumPayoff
```

from
`UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/AmbientCarrierElimination.lean`.
It applies to the same no-uniform branch in which the full-support packet is
constructed.  The checked terminal-gap equivalence supplies a
`QuittingTerminalExploitabilityWitness` in that branch.  No relation between
packet support and normal-core membership is inferred directly: full normal
core first implies punishment normality through (NC), and only then does the
independent terminal-gap lift construct a new packet.

The new content has two parts: the constrained stationary-game construction,
its exact regret formula and full-support limiting packet; and the elementary
but previously unstated connector (NC), obtained by placing the checked core
blocker inequality opposite the checked abnormal singleton-floor inequality.
A narrow repository search found the two ingredients but no declaration of
their connector and no declaration producing a full-support normalized
singleton packet from a punishment-normal terminal exploitability witness.
The checked card-three normal-core compiler is a different proper-core result
and is not used.  No literature theorem is invoked.

## Proof

### 0. The full-core connector

Fix `i in normalCore(normalizedSoloMatrix r)`.  The checked core-blocker
theorem supplies a distinct player `j` in the same core such that

```text
normalizedSoloMatrix r i j <= 0.                    (15)
```

The exact matrix dictionary expands this entry in the required orientation:

```text
normalizedSoloMatrix r i j
  = r({j})_i-r({i})_i.                              (16)
```

Hence `r({j})_i<=r({i})_i`.  If `i` were abnormal, the checked abnormal
singleton-floor chain, applied to `j!=i`, would give

```text
r({i})_i < chi_i <= r({j})_i,                       (17)
```

contradicting (15)--(16).  Therefore `chi_i<=r({i})_i`, proving (NC).  The
argument uses only membership of `i` in the core; it does not assert the
converse inclusion.

### 1. A constrained stationary Nash root

Fix `epsilon in (0,1)`.  Restrict each player's stationary Quit probability
to `[epsilon,1]`.  For a rate vector `q`, fix player `i` and put

```text
beta_i  = product_{j!=i}(1-q_j),
delta_i = 1-beta_i.
```

Because `n>=2` and every opponent rate is at least `epsilon`, `delta_i>0`.
Let `Q_i` be `i`'s expected payoff when it Quits at the current row against
the product root of its opponents.  Let `A_i` be the unnormalised expected
current-row payoff when `i` Continues: only nonempty opponent Quit coalitions
contribute.  If `i` instead uses the stationary rate `p`, repeated independent
rows give

```text
V_i(p,q_{-i})
  = [p Q_i + (1-p) A_i] / [delta_i+p beta_i].         (5)
```

Define the Never value `N_i=A_i/delta_i`.  Formula (5) is fractional linear
in `p`; its derivative has the constant sign of `Q_i-N_i`.  Its maximizer set
on `[epsilon,1]` is therefore the lower endpoint, the upper endpoint, or the
whole interval.  In particular it is nonempty, compact, and convex.  The
payoffs are continuous in the whole rate vector, so the best-response
correspondence has closed graph.  Kakutani's fixed-point theorem gives a
constrained stationary Nash root `q^epsilon`.

For each player the complete classification is

```text
q_i^epsilon=epsilon  and Q_i<=N_i,
epsilon<q_i^epsilon<1 and Q_i=N_i,
q_i^epsilon=1        and Q_i>=N_i.                   (6)
```

All opponents contract.  The checked stationary best-response theorem says
that the unrestricted behavioral cap is `max(Q_i,N_i)`.  In the interior and
upper cases the current stationary payoff already equals this cap.  In the
lower case the only possible improvement is Never, and direct cancellation
in (5) gives

```text
N_i-V_i(epsilon,q^epsilon_{-i})
 = epsilon(N_i-Q_i)/(delta_i+epsilon beta_i).        (7)
```

This is an unrestricted-deviation statement, not merely Nash equilibrium in
the compact stationary-rate game.

### 2. The terminal gap forces comparable vanishing hazards

Apply (2) to the behavior profile generated by `q^epsilon`.  The middle and
upper cases in (6) have zero unrestricted gain.  Hence some lower-bound player
`i=i(epsilon)` has the Never gain (7) at least `g`.  Since every terminal
payoff lies in `[-M,M]`, both `Q_i` and `N_i` lie there.  Therefore

```text
delta_i+epsilon beta_i <= 2M epsilon/g.              (8)
```

The same gain is at most `2M`, so `g<=2M` and hence `2M/g>=1`.

For each `j!=i`, the event that `j` Quits is contained in the event that at
least one opponent of `i` Quits, whence `q_j^epsilon<=delta_i`.  Since every
rate lies in the constrained cube and `q_i^epsilon=epsilon`,

```text
epsilon <= q_j^epsilon <= (2M/g)epsilon  for all j,
H_epsilon:=sum_j q_j^epsilon <= C epsilon,           (9)
```

where `C=1+2M(n-1)/g`.  These bounds are consistent and `M>0`.

Set

```text
mu_i^epsilon=q_i^epsilon/H_epsilon.
```

Then `mu^epsilon` is a probability vector and every coordinate is at least
`1/C`.  Choose explicitly `epsilon_k=1/(k+2)`, so `epsilon_k downarrow 0`.
Compactness of the finite probability simplex gives a subsequence along which
`mu^{epsilon_k}` converges to a probability vector `mu`.  Passing the lower
bound to the limit gives

```text
mu_i>=1/C>0                                            (10)
```

for every player.

### 3. First-order product-law limits

For sufficiently small `epsilon`, (9) excludes `q_j^epsilon=1` for every
player.  The remaining two cases in (6) imply `Q_i<=N_i`, equivalently

```text
delta_i Q_i <= A_i.                                  (11)
```

Along the selected subsequence, all rates vanish.  Finite product expansion
gives

```text
delta_i/H_epsilon
  -> sum_{j!=i} mu_j,

A_i/H_epsilon
  -> sum_{j!=i} mu_j r({j})_i,

Q_i -> r({i})_i=s_i.                                 (12)
```

For completeness, the first identity follows because the probability that
at least one opponent Quits is the sum of the marginal opponent hazards plus
a remainder containing at least two hazards.  In `A_i`, every singleton
opponent coalition contributes its hazard times `r({j})_i`; all
nonsingleton terms contain at least two hazards.  Since each rate is at most
`H_epsilon`, every omitted finite sum is `O(H_epsilon^2)`.  Finally, when `i`
Quits, the probability that an opponent also Quits is at most
`sum_{j!=i}q_j^epsilon`, so the Quit payoff converges to the solo payoff.

Divide (11) by `H_epsilon` and use (12):

```text
(sum_{j!=i}mu_j)s_i
  <= sum_{j!=i}mu_j r({j})_i.                        (13)
```

Adding `mu_i s_i` to both sides proves (4).  Taking `v=s`, condition (1)
supplies the punishment floor, the solo floor and all positive-mass pins are
equalities, and (4) is the packet mixture inequality.  Equation (10) proves
full support.

### 4. `Fin 4` full-core composition

Let `witness : QuittingTerminalExploitabilityWitness r`.  Its terminal gap
rules out a uniform-equilibrium payoff for the same reward table.  Apply the
checked theorem

```text
normalCore_eq_univ_of_fourPlayer_not_exists_uniformEquilibriumPayoff
```

with `Fintype.card (Fin 4)=4`.  This proves (4F).  Step 0 then proves (1) for
all four players.  Steps 1--3 applied with `g=witness.terminalGap` produce a
packet satisfying (4P).

Finally consider an arbitrary game on `Fin 4`.  If it has a uniform payoff,
take the first alternative.  Otherwise the checked terminal-gap equivalence
supplies a terminal exploitability witness, and the preceding paragraph gives
the full-support packet.  If one starts from the checked analytic waist, the
same split may be made after its packet arm; the original packet is not
reused.  Whenever its support was proper, replacing it by the newly
constructed packet decreases `4-card(support)` to zero and cannot cycle.

## Probability and behavioral-deviation audit

The auxiliary root at each `epsilon` is a literal stationary product root.
Players randomize independently; no public correlating device or mixture over
entire stationary profiles is introduced.  Kakutani selects a deterministic
vector of marginal rates.

The stationary-rate game is only an existence device.  The passage from its
endpoint classification to (7) uses the checked full-rate stationary cap,
which takes the supremum over a player's complete behavioral strategy and is
attained by immediate Quit or Never under opponent contraction.  Thus the
terminal gap cannot hide a profitable history-dependent or nonstationary
deviation at an interior or upper constrained coordinate.

Every `q_j^epsilon` is positive, so every fixed-opponent process contracts and
Never has the normalized value `A_i/delta_i`.  Ties and simultaneous Quit
coalitions are retained exactly in `Q_i` and `A_i`; they disappear only after
the explicit `O(H_epsilon^2)` first-order estimate.  No conditioning,
expectation, maximum, or limit is interchanged without the displayed finite
product calculation.

## Boundary tests

### Exact test of the lower-bound mechanism

Take two players.  Give player `i` payoff `1` when the other player Quits
alone, and payoff `0` when `i` belongs to the quitting coalition.  At the
constrained root `(epsilon,epsilon)`, for each player

```text
Q_i=0,
delta_i=epsilon,
A_i=epsilon,
N_i=1,
V_i=(1-epsilon)/(2-epsilon),
N_i-V_i=1/(2-epsilon).
```

Thus both constrained best responses are the lower endpoint, the exact regret
formula (7) holds, and the limiting direction is `(1/2,1/2)`.  Its singleton
mixture pays each player `1/2`, above the solo target `0`.  This table does not
have a global positive terminal gap—the all-Never profile is stable—so it is
only a sharp test of the local construction, not an instance of all theorem
hypotheses.

### Normality cannot be dropped from the stated target

Take two players and set player `0`'s rewards to

```text
r({0})_0=-1,
r({1})_0=0,
r({0,1})_0=-1,
```

with player `1`'s rewards all zero.  Player `0` can guarantee `0` by Never,
while player `1` can hold player `0` to `0` by Never, so `chi_0=0>s_0=-1`.
Any packet with target `v=s` violates its punishment floor in coordinate `0`.
This shows exactly where assumption (1) enters.  It does not assert failure of
all possible packets or a terminal exploitability gap for this table.
Moreover, the normalized singleton row of player `0` has strictly positive
off-diagonal entry, so player `0` is deleted from the normal core.  Thus this
example is also an exact boundary test for (NC): the connector excludes the
abnormal player rather than incorrectly making it normal.

The restriction `n>=2` is also structural: the proof uses strict contraction
of each player's opponents, so `delta_i>0` and the Never normalization are not
available for a one-player game.

## Adapter and maintained consumer

The actual-data adapter is the no-uniform branch itself.  The checked
terminal-gap equivalence supplies a literal
`QuittingTerminalExploitabilityWitness`, while the checked four-player theorem
supplies (4F) for the same reward table.  The finite connector in Step 0 turns
that core identity into the all-player assumption (1), and the reviewed
stationary construction outputs a new literal normalized singleton packet.
No input packet support, artificial packet, reward perturbation, or unproved
source field is inserted.

The named downstream obligation is the full-support/full-normal-core,
punishment-normal intersection in
`FOUR_PLAYER_SINGLETON_PACKET_DISPATCH.md`.  The packet does not feed an
all-behavior equilibrium compiler by itself.  Its accepted value is the
strict, nonreturning elimination of every proper support and the simultaneous
normal-core/punishment-normal restriction.

## Lean handoff

A narrow formalization can introduce an auxiliary constrained stationary-rate
game rather than modifying the packet structures.  Suggested theorem shapes
are:

```text
exists_constrainedStationaryNash
  (epsilon_pos : 0 < epsilon) (epsilon_lt_one : epsilon < 1) :
  Exists q, q in Set.Icc epsilon 1 /\ constrainedStationaryNash reward q

exists_fullSupport_normalizedSingletonSourcePacket_of_terminalGap
  (normal : forall i, quittingPunishmentValue reward i <= solo_i)
  (gap_pos : 0 < g)
  (gap : HasTerminalExploitabilityGap reward g) :
  Exists packet : QuittingNormalizedSingletonSourcePacket reward,
    forall i, 1/C <= packet.mass i

mem_punishmentNormalPlayers_of_mem_normalCore
  (hi : i in normalCore (normalizedSoloMatrix reward)) :
  IsQuittingNormalPlayer reward i

terminalWitness_fullSupportPacket_of_finFour
  {I := Fin 4}
  (witness : QuittingTerminalExploitabilityWitness reward) :
  normalCore (normalizedSoloMatrix reward) = Finset.univ /\
  Exists packet : QuittingNormalizedSingletonSourcePacket reward,
    forall i, 1/C <= packet.mass i

uniformPayoff_or_fullSupportPacket_of_finFour
  {I := Fin 4} :
  (Exists v, IsUniformEquilibriumPayoff none v) \/
  Exists packet : QuittingNormalizedSingletonSourcePacket reward,
    packet.support = Finset.univ /\
    normalCore (normalizedSoloMatrix reward) = Finset.univ /\
    (forall i, IsQuittingNormalPlayer reward i)
```

The first proof needs a finite-dimensional Kakutani theorem plus the
fractional-linear best-response calculation (5)--(6).  The second should use
the existing full-rate cap declarations for unrestricted deviations, then a
sequence `epsilon_k=1/(k+2)` and compactness of the finite simplex.  The
first-order limits are finite product estimates; a robust handoff is to prove
that the sum of all coalition terms of cardinality at least two is bounded by
a constant times `H^2`.

For the connector, use `exists_core_blocker_of_mem_normalCore`, rewrite the
entry with `normalizedSoloMatrix_eq_soloReward_sub`, and contradict
`abnormal_singletonFloor_chain`.  For the four-player theorem, split on
uniform-payoff existence; in the negative branch combine the checked
full-normal-core theorem with the connector and the terminal-gap lift.  Do not
encode full support, full normal core, or punishment normality as input
structure fields.  The exact boundary tables above are useful regression
tests.

## Scope and nonclaims

- The theorem does not solve the full-support/full-normal-core,
  punishment-normal packet obligation or the four-player quitting-game
  conjecture.
- It eliminates support one, two, and three only as conjecture-facing packet
  residuals in the no-uniform branch; it does not erase the independent local
  structural theorems previously proved on those supports.
- It does not decode an arbitrary singleton packet directly to a uniform
  payoff.
- It uses a terminal exploitability witness only in the no-uniform branch;
  it does not construct a counterexample or assert that such a witness exists
  for any known reward table.
- The constrained stationary roots are auxiliary.  They are not claimed to
  be approximate equilibria, an executable chronological packet chain, or a
  fixed target strategy family.
- The limiting singleton packet is finite static data.  It carries no
  Bellman chronology, debt-shadowing certificate, absorption clock, or
  conditioned stopping-law provenance.
- The lower bound `1/C` is sufficient, not claimed sharp.
