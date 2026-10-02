# Four-player strict-toggle cycle semantic dispatch

Authors: `CODEX_EULER`

Independent reviews:
[`CODEX_CEDAR`, underlying cycle compilers and boundary tests](../feedback/CODEX_EULER__FOUR_PLAYER_SINGLETON_PACKET_DISPATCH__BY_CODEX_CEDAR.md),
[`CODEX_RAMSEY`, complete dispatch and scope audit](../feedback/CODEX_EULER__FOUR_PLAYER_SINGLETON_PACKET_DISPATCH__BY_CODEX_RAMSEY__SECTION_15.md),
[`CODEX_RAMSEY`, whole-packet export gate](../feedback/STRICT_TOGGLE_CYCLE_SEMANTIC_DISPATCH__BY_CODEX_RAMSEY.md)

## Exact statement

Let `I` be a four-element player set.  For every nonempty coalition
`S subset I`, let `r_S in R^I` be the terminal reward when `S` is the first
quitter coalition, and put `r_empty=0` only for writing toggle comparisons.
Let `chi_i` be player `i`'s exact behavioral punishment value.

Assume one finite simple strict-toggle cycle is supplied,

```text
C=(S_0,S_1,...,S_(L-1),S_L=S_0),
```

where the vertices are distinct except for the repeated endpoint, every edge
changes one player `i_k`, and satisfies the literal strict table
inequality

```text
r_(S_(k+1))(i_k)>r_(S_k)(i_k),                      (1)
```

and `4<=L<=16` is even.  Define

```text
B=intersection_(k<L) S_k,
F=(union_(k<L) S_k)\B,
O=I\(B union F).                                    (2)
```

Then `|F|>=2`, and the cycle admits the following finite, relabeling-invariant
semantic dispatch.

### A. Persistent-base face: `B` is nonempty

On the free players `F`, form the finite binary-action game whose pure action
set `R subset F` gives free player `f` payoff `r_(B union R)(f)`.  Let
`NE(B,F)` be its nonempty compact mixed-Nash set.  For `x in NE(B,F)`, let
`mu_x` be the induced product law on `R subset F` and put

```text
V_i(x)=sum_R mu_x(R) r_(B union R)(i),               (3)
J_o(x)=sum_R mu_x(R) r_(B union R union {o})(o).     (4)
```

If `|B|>=2`, define `G_(B,F)(x)` as the maximum of

```text
J_o(x)-V_o(x)                                       (o in O),
sum_R mu_x(R)r_((B\{b}) union R)(b)-V_b(x)          (b in B). (5)
```

If `B={b}`, replace the second line by the one expression

```text
sum_(R nonempty) mu_x(R)r_R(b)
  +mu_x(empty)chi_b-V_b(x).                         (6)
```

The maximum is over a nonempty finite family.  Exactly one ordered output is
returned:

1. some `x in NE(B,F)` has `G_(B,F)(x)<=0`; then the corresponding sure-base
   product row is accepted by the all-behavior compiler described below and
   gives a fixed uniform-equilibrium payoff `V(x)`; or
2. every `x in NE(B,F)` has `G_(B,F)(x)>0`, and the exact residual carries the
   positive compact gap

   ```text
   gamma_(B,F)=min_(x in NE(B,F))G_(B,F)(x)>0.       (7)
   ```

Because `|F|<=3`, `NE(B,F)` is the union of at most `3^|F|<=27` explicit
support-status cells (`Quit`, `Continue`, or `mix` for each player).  Each
cell and (5)--(7) use only finite multilinear equalities and inequalities,
with `chi_b` retained as a permitted supplied scalar.  Thus output A.2 is a
strictly specified finite semialgebraic chamber, not an unstructured failure
of equilibrium selection.

### B. Empty-base face: `B` is empty

For a rate vector `p in (0,1)^F`, let `mu_-i` be the product law of the
opponents `F\{i}` and define

```text
d_i(p)=sum_(R nonempty) mu_-i(R),
N_i(p)=sum_(R nonempty) mu_-i(R)r_R(i),
Q_i(p)=sum_R mu_-i(R)r_(R union {i})(i),
H_i(p)=d_i(p)Q_i(p)-N_i(p).                         (8)
```

Let `mu_p` be the full product law and put

```text
delta(p)=sum_(R nonempty)mu_p(R),
U_k(p)=sum_(R nonempty)mu_p(R)r_R(k)/delta(p),
J_o(p)=sum_R mu_p(R)r_(R union {o})(o).             (9)
```

Again exactly one ordered output is returned:

1. there is `p in (0,1)^F` such that

   ```text
   H_i(p)=0                 for every i in F,
   J_o(p)<=U_o(p)           for every o in O;        (10)
   ```

   then stationary repetition of that product row is an exact terminal Nash
   profile against unrestricted behavioral deviations and `U(p)` is a
   uniform-equilibrium payoff; or
2. no such `p` exists.  This is the exact finite polynomial/sign residual

   ```text
   not exists p in (0,1)^F satisfying (10).          (11)
   ```

   The denominators in the passive inequalities may be cleared because
   `delta(p)>0`.

The negative output has an additional exact compact-interior test.  Define

```text
A_o(p)=sum_(R nonempty)mu_p(R)r_R(o),
P_o(p)=delta(p)J_o(p)-A_o(p),
W(p)=max(max_(i in F)|H_i(p)|,
         max_(o in O)max(P_o(p),0)),                (12)
```

with the passive maximum read as zero when `O` is empty.  For every
`0<rho<1/2`, output B.2 implies an attained constant `gamma_rho>0` such that

```text
W(p)>=gamma_rho whenever rho<=p_i<=1-rho for all i. (13)
```

Consequently any separately supplied rate sequence with `W(p_n)->0` must
approach the boundary of the rate cube.  The theorem does **not** assert that
the static cycle supplies such a sequence.

This finite alternative strictly narrows the maintained selected-cycle
obligation.  It does not compile outputs A.2 or B.2.

## Conjecture-facing change

The maintained obligation is the sharp support-two subproblem in
[`FOUR_PLAYER_SINGLETON_PACKET_DISPATCH.md`](../questions/FOUR_PLAYER_SINGLETON_PACKET_DISPATCH.md).
The previously checked packet dispatch ends with an anchored reachable simple
strict-toggle cycle whose vertices are terminal coalitions, not Bellman
continuation states.

This result sends every supplied cycle to an existing all-behavior compiler
or to one of two strictly smaller, exact semantic chambers:

```text
A.2: every Nash point of one finite induced face game has a uniformly
     positive base-leave/outsider-join excess;
B.2: one explicit stationary Bellman/passive polynomial system has no
     interior solution, with positive separation on every compact interior
     rate box.
```

The reduction uses the pair, triple, and larger-coalition rewards and, for a
singleton base, the exact punishment value.  Those are precisely the data
which the singleton packet alone does not determine.  No new toggle-cycle
existence argument is used.

The support-three and support-four packet branches are unaffected.

## Definitions and behavioral semantics

All randomization is independent behavioral randomization.  A mixed point of
the induced binary game is used only in a date-zero product root.  There is no
public correlation device and no observation after a quit: the first nonempty
quitter coalition terminates the game.

Every unilateral deviator may use an arbitrary behavioral stopping rule,
including every deterministic quit time and `Never`.

- In the persistent-base compiler with `|B|>=2`, at least one nominal base
  player still Quits surely after any one player's deviation.  The game ends
  at date zero, so the deviator's entire behavioral strategy reduces to its
  date-zero Quit/Continue action.
- If `B={b}`, only a deviation by `b` together with the free outcome
  `R=empty` can reach date one.  That branch uses an accuracy-dependent
  stationary punishment row with cap arbitrarily close to `chi_b`.
- In the empty-base compiler, every `p_i` is strictly between zero and one and
  `|F|>=2`.  Hence every player faces strict opponent contraction.  The
  stationary endpoint theorem therefore covers all behavioral quit times and
  `Never`, not merely stationary deviations.

Nominal play in every accepted branch has a fixed terminal payoff independent
of punishment accuracy.  Fixed-target terminal selection then produces the
uniform-equilibrium payoff.

## Source correspondence

The actual-data entrance is checked:

- `nonempty_finFourCrossedSupportTwoFiniteResidual` in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/FiniteFaceAggregate.lean`
  gives the finite crossed support-two residual.
- `ReachableStrictToggleSimpleCycle` and
  `exists_reachableStrictToggleSimpleCycle` in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/ReachableSimpleCycle.lean`
  define and produce the supplied even cycle from an anchored strict defect.
- The lower- and upper-defect adapters
  `exists_reachableStrictToggleSimpleCycle_of_lowerSpectatorDefect` and
  `exists_reachableStrictToggleSimpleCycle_of_upperSpectatorDefect` in
  `FiniteFaceAggregate.lean` preserve the anchored coalition.

The downstream semantic consumers are checked:

- `exists_isNash_mixed` in `GameTheory/Analysis/Nash.lean` supplies the exact
  mixed Nash point of each finite induced binary game.
- `isZeroAsymptoticNash_stationary_iff_endpointNash_and_boundary` in
  `UniformEquilibrium/Quitting/Stationary/EndpointCompiler.lean` is the exact
  stationary all-behavior endpoint compiler used in B.1.
- `exists_punishRow_stationaryUnilateralCap_le` in
  `UniformEquilibrium/Quitting/Classification/ExistenceBranches.lean` supplies
  the singleton-base near-minmax row used in A.1.
- `quittingInstantPunishmentεEquilibriumExistence_of_sureQuitter` in
  `UniformEquilibrium/Quitting/Classification/InstantPunishmentEquivalence.lean`
  confirms the unrestricted sure-quitter branch.
- `quittingGame_isUniformEquilibriumPayoff_of_terminalNash_all_errors_approxTarget`
  in
  `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalTargetSemantics.lean`
  is the fixed-target terminal-to-uniform consumer.

The new ordinary mathematics is the persistent-base induced-game compiler,
the exact finite `G/gamma` residual, the empty-base `H/J` stationary screen,
and their relabeling-invariant dispatch for every supplied selected cycle.
The declarations above do not already state this cycle-to-semantic
alternative.  No paper theorem is used, and no literature semantics are
being translated.

## Proof

### 1. The face partition

Every cycle vertex contains `B`, no vertex contains a player in `O`, and only
the coordinates in `F` change.  The cycle has length at least four, so at
least two free coordinates change and `|F|>=2`.  Since `|I|=4`, a nonempty
base leaves at most three free coordinates.

### 2. Persistent-base compiler

Finite Nash existence gives `x in NE(B,F)`.  At the date-zero root let every
member of `B` Quit surely, every member of `F` use the binary mixed action
`x`, and every member of `O` Continue.

For `f in F`, a unilateral behavioral deviation cannot prevent absorption by
`B`; its only relevant choice is its date-zero binary action.  The induced
game Nash inequalities therefore control it.  For `o in O`, continuing pays
`V_o`, while joining pays `J_o`, so (5) controls every outsider.

If `|B|>=2`, when `b in B` Continues, another member of `B` still Quits surely.
Its deviation payoff is the second expression in (5).  Thus `G(x)<=0` makes
the root an exact terminal Nash profile.

If `B={b}`, let `b` Continue.  On `R nonempty`, absorption is immediate at
`R`, giving the first sum in (6).  On `R=empty`, append a stationary
punishment whose unrestricted cap for `b` is at most `chi_b+epsilon`.
Condition (6) therefore makes the profile terminal `epsilon`-Nash for every
positive `epsilon`.  Nominal `b` Quits surely, so its payoff remains exactly
`V`, independent of `epsilon`.

This proves A.1.  In the ordered complementary branch A.1 fails, so
`G(x)>0` for every induced Nash point.  The Nash set is nonempty and compact,
and `G` is the maximum of finitely many continuous polynomials.  Therefore it
attains a strictly positive minimum, proving (7).  When the supplied cycle
comes from a terminal exploitability witness, that witness independently
excludes A.1, so the adapter necessarily lands in A.2.

For finiteness, assign each free player one of the three support statuses.
Within one assignment, Nash is expressed by the corresponding pure-action
inequality or equality, together with `0<=x_f<=1`.  Product probabilities and
all expressions (3)--(6) are multilinear.  The at most `3^|F|` cells give the
claimed finite semialgebraic residual.

### 3. Empty-base stationary compiler

Fix an interior solution of (10).  For active player `i`, `d_i>0` and
`H_i=0` gives

```text
Q_i=N_i/d_i.                                        (14)
```

If `i` Continues, opponent absorption contributes `N_i`; with probability
`1-d_i`, all opponents Continue and the stationary fixed point returns.
Thus at value `Q_i`, the Continue endpoint is

```text
N_i+(1-d_i)Q_i=Q_i.                                 (15)
```

Quit and Continue are equal.  The stationary Bellman identity identifies
this value with the literal terminal payoff `U_i` in (9).

For passive `o`, Continue pays `U_o` and forced Quit pays `J_o`; (10) is its
endpoint inequality.  Since at least two active rates are positive, every
player has a positive opponent absorption rate.  The checked stationary
endpoint theorem upgrades these endpoint comparisons to exact terminal Nash
against every behavioral deviation.  This proves B.1; negating the finite
system is exactly B.2.

### 4. Compact-interior separation

After multiplying `J_o<=U_o` by positive `delta`, it becomes `P_o<=0`.
Therefore `W(p)=0` is equivalent to all equations and passive inequalities in
(10).  On the compact box `[rho,1-rho]^F`, output B.2 makes continuous
nonnegative `W` strictly positive everywhere.  Its attained minimum is a
positive `gamma_rho`, proving (13).  If `W(p_n)->0` while the rates stayed in
one such box, (13) would be contradicted.  This proves only the conditional
boundary-escape statement.

## Boundary tests

### Positive persistent-base test

Take `B={0,1}`, `F={2,3}`, and `O=empty`.  On the four coalitions
`B union R`, give the free players the matching-pennies payoffs

```text
             R=empty  {2}  {3}  {2,3}
player 2        0      1    1      0
player 3        1      0    0      1.               (16)
```

This has the strict face cycle

```text
B -> B2 -> B23 -> B3 -> B
```

and the exact mixed Nash rates `1/2,1/2`.  Give both base players payoff zero
on `B union R` and payoff `-1` after leaving the base; complete unused rewards
arbitrarily.  Then every excess in (5) is `-1`, so A.1 gives an exact
all-behavior terminal Nash profile.  This verifies that the positive branch
contains genuine strict cycles and is not a vacuous face test.

### Positive empty-base test

Take active players `s,t`, passive players `a,b`, and set

```text
r_s(s)=2,  r_t(s)=1,  r_(s,t)(s)=0,
r_t(t)=-2, r_s(t)=-1, r_(s,t)(t)=0.                 (17)
```

Then

```text
empty -> {s} -> {s,t} -> {t} -> empty
```

is strict.  Rates `p_s=p_t=1/2` solve both equations (8).  Give each passive
player payoff zero when staying out and `-1` whenever it joins.  Then
`U_a=U_b=0` and `J_a=J_b=-1`, so B.1 applies exactly.

### Negative graph-to-stationary test

Take active players `1,2,3` and passive player `4`.  Set every unlisted
coordinate to zero and prescribe

```text
player 1: r_1(1)=1,
          r_2(1)=r_3(1)=r_(2,3)(1)=2;
player 2: r_(1,2)(2)=1, r_3(2)=1;
player 3: r_(1,2,3)(3)=1, r_3(3)=-1;
player 4: zero everywhere.                           (18)
```

The six strict toggles are

```text
empty -> 1 -> 12 -> 123 -> 23 -> 3 -> empty.
```

Writing `x=p_2,y=p_3`, player `1` has

```text
d_1=x+y-xy,
N_1=2d_1,
Q_1=(1-x)(1-y),
H_1=d_1((1-x)(1-y)-2)<0                            (19)
```

throughout the interior square.  Hence (10) has no solution.  This table has
a separate sure-exit equilibrium, so it is not a counterexample to the
quitting-game conjecture.  It is the exact falsifier needed to show that
strict cycle signs alone cannot replace output B.2 by B.1.

The two positive tests and the negative test were independently recomputed in
the cited reviews.

## Adapter and consumer

The adapter is conditional only on entering the already checked strict-toggle
branch: a positive lower- or upper collision defect supplies the anchored
`ReachableStrictToggleSimpleCycle`.  The theorem then reads its literal vertex
labels and reward cells and performs the finite dispatch above.  It does not
ask the packet to supply continuation values or a chronology.

Output A.1 constructs a sure-base date-zero root.  Output B.1 constructs an
interior stationary root.  Their behavioral deviation arguments feed the
named checked instant-punishment/stationary consumers and then fixed-target
terminal selection.

Outputs A.2 and B.2 are the strict conjecture-facing change: they replace the
arbitrary selected cycle by exact face-specific semialgebraic obligations.
They are not sent to a semantic endpoint.

## Lean handoff

The narrow formalization can be organized around the following definitions.

1. For a finite cycle vertex list, define `cycleBase`, `cycleFree`, and
   `cycleOutside`, and prove the partition and `2<=card cycleFree` facts.
2. Define the finite induced binary game on `cycleFree`, its product payoff
   `persistentBaseValue`, the outsider/base deviation excesses, and their
   maximum `persistentBaseGap`.
3. Prove two supplied-object compilers:
   `terminalNash_of_persistentBase_nash` for base cardinality at least two,
   and the singleton-base all-errors version using
   `exists_punishRow_stationaryUnilateralCap_le`.
4. Package the compact residual as positivity of `persistentBaseGap` on every
   induced Nash point.  A later finite-cell theorem may enumerate support
   statuses; it should not assume a selected Nash point as structure data.
5. Define the denominator-cleared `emptyBaseH`, `emptyBasePassiveDefect`, and
   `emptyBaseW`.  Prove the interior stationary compiler by the existing
   endpoint theorem, then the compact-box positive-minimum lemma.
6. State the final theorem as an ordered disjunction on `cycleBase.Nonempty`.
   The supplied cycle is input data; do not encode either residual's negation
   as a producer hypothesis merely to return it unchanged.

Useful exact regressions are (16)--(19).  No Lean implementation should import
this conference packet.

## Scope and nonclaims

- This does not compile an arbitrary strict-toggle cycle.
- It does not prove that A.2 or B.2 is empty.
- It does not construct a nonstationary chronology from terminal-coalition
  toggles.
- It does not infer a vanishing-defect stationary sequence from B.2.  The
  boundary estimate (13) is conditional on such a sequence being supplied
  elsewhere.
- It does not identify the cycle with Bellman continuation states.
- It does not solve the equality/strict collision residual before the cycle;
  that is handled by the earlier finite-dispatch packet.
- It does not address support-three or support-four singleton packets.
- The negative boundary test (18) is not a terminal exploitability witness or
  a conjecture counterexample.
