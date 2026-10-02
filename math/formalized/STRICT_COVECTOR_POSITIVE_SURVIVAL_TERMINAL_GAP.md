# Global Late-Tail Strict Covector and Positive-Solo Phantom Cost

Author: `CODEX_GAUSS`

Independent reviews:

- [`CODEX_NOETHER`, strict-covector tail](../feedback/CODEX_GAUSS__CURL_FREE_TOGGLE_POTENTIAL__BY_CODEX_NOETHER__ROUND_15.md)
  and
  [`CODEX_NOETHER`, unrestricted terminal gap](../feedback/CODEX_GAUSS__CURL_FREE_TOGGLE_POTENTIAL__BY_CODEX_NOETHER__ROUND_16.md);
- [`CODEX_CEDAR`, second unrestricted-class falsification](../feedback/CODEX_GAUSS__CURL_FREE_TOGGLE_POTENTIAL__BY_CODEX_CEDAR__ROUND_9.md).
- [`CODEX_NOETHER`, final source/novelty gate](../feedback/STRICT_COVECTOR_POSITIVE_SURVIVAL_TERMINAL_GAP__BY_CODEX_NOETHER.md).

The first review checks the strict-covector construction from the
residual-hard source data.  The latter two independently reconstruct the
phantom/deleted-clock identities, uniform pure-time comparison, exact
behavioral supremum, positive-solo limit, and fixed-target consequence.  The
second review also rechecks finite residual charge and the sufficiently late
positive survival product.  No mathematical objection remains.  The strict-
covector and positive-survival alternatives are now proved in Lean by the
declarations cited below.
The final gate review identified and this version incorporates one important
source correction: the canonical counterexample tail and its summable joint
absorption are already supplied by named checked declarations.  On that
source, the new content is the single strict covector and the exact
positive-solo all-behavior price, not bare tail extraction or summability.

## Exact statement

Let `I` be a nonempty finite player type and let

```text
r : {S : Finset I // S.Nonempty} -> (I -> Real)
```

be a quitting reward table.  Put

```text
s_i   = r({i})_i,
M_i,j = r({j})_i-s_i,
chi_i = the behavioral punishment value of player i.             (1)
```

A **convergent diffuse exact floor tail** consists of payoff vectors
`X_n : I -> Real` and independent one-row Quit probabilities
`p_n,i in [0,1]`, for `n in Nat`, with the following properties.

1. `X_n -> b` coordinatewise for one payoff vector `b`, and `b_i>=s_i` for
   every `i`.
2. With

   ```text
   Q_n=1-product_i(1-p_n,i),                                  (2)
   ```

   one has `Q_n->0` and `Q_n>0` for infinitely many `n`.
3. Every row is an exact Nash--Bellman edge with continuation `X_(n+1)`:
   its expected one-row payoff is `X_n`, and neither forced pure Quit nor
   forced pure Continue improves any coordinate.  Equivalently, the pair
   `(X_n,p_n)` and tail `(X_(n+1),p_(n+1))` satisfy
   `IsQuittingNashBellmanEdge r` in the repository's orientation.
4. Every displayed payoff dominates the punishment floor:
   `chi_i<=X_(n,i)` for every `n,i`.

When `Q_n>0`, let `D_n` be the row's expected terminal reward conditional on
at least one player quitting.  Exact Bellman evaluation is then

```text
X_(n+1)-X_n=Q_n*(X_(n+1)-D_n).                      (3)
```

Let `ResidualHardClass r` have its exact repository meaning: the recursive
normal core is nonempty, its normalized singleton matrix has no homogeneous
simplex solution and is standard-Q, while the full normalized matrix fails
projective Q-bar.

### Theorem A: one covector, finite charge, positive survival

Assume `ResidualHardClass r` and a convergent diffuse exact floor tail.
Then either the game already has a uniform-equilibrium payoff, or the
following conclusions all hold.

Define

```text
c=b-s,
E={i : c_i=0}.                                                (4)
```

The set `E` is nonempty, every member satisfies `chi_i<=s_i`, and after one
finite cutoff every positive Quit probability is owned by a member of `E`.
There are a unit covector `ell`, a number `kappa>0`, and a cutoff `N` such
that, for every `N<=n<m`,

```text
ell dot (X_m-X_n)
  >= (kappa/2)*sum_(k=n)^(m-1) Q_k.                 (5)
```

Consequently

```text
H_n:=sum_(k>=n)Q_k < infinity,
ell dot (b-X_n) >= (kappa/2) H_n,                  (6)
```

and the all-Continue probability

```text
C_n:=product_(k>=n)(1-Q_k)                          (7)
```

is strictly positive for every sufficiently late `n`.  Moreover `C_n->1`.

### Theorem B: exact unrestricted price of executing the tail

The second theorem needs only exact Nash--Bellman evaluation, convergence
`X_n->b`, and finite total charge `sum_n Q_n<infinity`; it does not need
`ResidualHardClass`.

Let `profile_n` be the behavioral quitting profile obtained by executing the
root sequence `p_n,p_(n+1),...`, with terminal payoff zero on the event that
everyone Continues forever.  Write

```text
U_i(n)=quittingTerminalPayoff r profile_n i,                    (8)
```

and define exact coordinate exploitability against replacement of player
`i`'s entire behavioral strategy by

```text
e_i(n)=sup_dev [quittingTerminalPayoff r
                  (update profile_n i dev) i-U_i(n)].           (9)
```

Let `F_i(t)` be player `i`'s one-row payoff at row `t` when `i` is forced to
Quit while all opponents retain their prescribed independent marginals.
Then, for every player `i`,

```text
U_i(n) -> 0,

e_i(n)-max(0,sup_(t>=n)F_i(t)) -> 0,

e_i(n) -> max(0,s_i).                                          (10)
```

Thus, if all own singleton rewards are nonpositive, the profiles `profile_n`
deliver the fixed target zero with terminal Nash error tending to zero, and
zero is a uniform-equilibrium payoff.  Conversely, on the no-uniform-payoff
branch of Theorem A,

```text
max_i e_i(n) -> max_i max(0,s_i)>0.                             (11)
```

The positive survival atom is therefore not a vanishing compactness error:
executing later suffixes exposes one fixed positive-solo deviation cost.

## Conjecture-facing change

There are two deliberately separate scopes.  As a general conditional
theorem, Theorem A applies to any supplied convergent diffuse exact floor tail
and rules out changing boundary-tight support, varying comparison horizons,
and unbounded residual absorption through one strict covector.

For the canonical counterexample source, the repository already supplies the
tail and summable joint absorption: this is not new evidence in the packet.
The new reduction on its nonplateau residual-hard arm is that one common
covector controls every late support and every horizon by `(5)--(6)`, and
Theorem B prices the resulting positive-survival suffix exactly against all
behavioral deviations.  The complementary eventual-all-Continue arm is the
already named phantom plateau branch, not an omitted tail-existence case.

Theorem B identifies the exact semantic price of that atom against every
unilateral behavioral strategy.  On the checked zero-solo branch it vanishes,
but that branch already has a uniform payoff.  Any residual-hard
counterexample must have a positive solo coordinate, and the forced-survival
tail then has a fixed positive terminal gap.  A successful universal producer
must pay that gap by a punishment/return attachment; another compactness or
survival-limit argument cannot erase it.

This is a strict reduction of the positive-tail obligation, not a proof of
the conjecture and not a counterexample.

## Definitions, probability mode, and deviations

At each row the players randomize independently between Continue and Quit.
The only live public history is that everyone has continued so far.  A
nonempty quitting coalition terminates play with the literal source-table
reward `r(S)`; the all-Continue-forever event pays zero.  The root sequence is
deterministic and publicly known.

The deviation supremum in `(9)` ranges over every behavioral strategy of one
player, not just stationary, finite-memory, or deterministic-time
deviations.  In a quitting game such a strategy is an arbitrary randomized
stopping clock along the unique live history.  The proved-in-Lean pure-time
extremality theorem cited below says its payoff supremum is exactly the
supremum over deterministic finite Quit times and pure Never.  No public
correlation device or sunspot signal is introduced.

Theorems A--B concern terminal payoffs.  The final zero-target consequence
uses the checked terminal-to-uniform selection theorem, so the target is one
fixed vector and only the approximating profile may depend on accuracy.

## Source correspondence and novelty audit

The following existing declarations were inspected under their stated
imports.

- `QuittingTerminalExploitabilityWitness.nonempty_positiveDebtDynamicTailWitness`
  (`UniformEquilibrium/Diagnostics/Quitting/Chronology/PositiveDebtDynamicTailWitness.lean`)
  is the checked actual-game source of the canonical convergent exact
  dynamic-debt tail.  Its fields already include literal exact edges,
  coordinatewise convergence, hazards tending to zero, a distinguished
  summable deleted-player clock, and `jointAbsorption_summable`.
- `QuittingPositiveDebtDynamicTailWitness.punishmentValue_le_tailValue`
  (`UniformEquilibrium/Diagnostics/Quitting/Debt/DynamicTailCapCarrier.lean`)
  supplies the punishment floor at every date of that canonical tail.
- `QuittingPositiveDebtSelfLoopLimit.soloReward_le_value`
  (`UniformEquilibrium/Quitting/Debt/Dynamic/PositiveDebtSelfLoopLimit.lean`)
  supplies `b_i>=s_i` at its limiting exact all-Continue self-loop.
- `exists_terminalGapDynamicDebtTail_summableAbsorption`
  (`UniformEquilibrium/Diagnostics/Quitting/Debt/ViolationCollapse.lean`)
  is the checked source of the canonical summable-absorption fact.  Therefore
  finite charge is a conclusion of the general conditional theorem, but not
  a new restriction of this named counterexample tail.
- `tail_eq_limitDebtPoint_of_eventually_allContinue` and
  `exists_exact_late_phantomSemantics_of_eventually_allContinue`
  (`UniformEquilibrium/Diagnostics/Quitting/Chronology/EventualAllContinuePlateau.lean`)
  identify the complementary plateau branch.  The infinitely-many-positive-
  rows hypothesis in Theorem A is precisely the nonplateau arm.
- `IsQuittingNashBellmanEdge`
  (`UniformEquilibrium/Quitting/Bellman/Finite/NashBellmanSpine.lean`) is the
  actual-table adapter for each exact row in the hypothesis.
- `ResidualHardClass.no_homogeneous`
  (`UniformEquilibrium/Quitting/Classification/LCP/Gate.lean`) supplies the
  checked normal-core matrix exclusion used in Theorem A.
- `exists_uniformEquilibriumPayoff_of_normalNoHarmSingletonOwner`
  (`UniformEquilibrium/Quitting/Classification/LCP/ProjectiveQBarBehavioralDecoder.lean`)
  is the checked semantic dispatch for the vertex case in the separation
  argument.
- `quittingValuePath_eq_terminalValue_add_survivalLimit_mul`
  (`UniformEquilibrium/Quitting/Cycles/PhantomBoundaryRestart.lean`) is the
  checked phantom-boundary identity underlying the terminal value formula.
- `sSup_range_quittingTerminalPayoff_update_eq_pureTime`
  (`UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean`)
  supplies exact unrestricted-behavior coverage.
- `quittingGame_isUniformEquilibriumPayoff_of_terminalNash_tendsto`
  (`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`)
  consumes the fixed zero target and vanishing terminal Nash errors.
- `IsQuittingZeroSolo` and
  `quittingGame_isUniformEquilibriumPayoff_zero_of_zeroSolo`
  (`UniformEquilibrium/Quitting/Punishment/ZeroSoloDisjunct.lean`) identify the
  already checked nonpositive-solo overlap.

The checked phantom theorem prices the prescribed boundary copy, but it does
not compute the unrestricted exploitability of the executable suffix.  The
checked pure-time theorem identifies the behavioral supremum for a supplied
profile, but it does not prove the uniform late-tail comparison with forced
Quit values.  A narrow search for `phantom`, `survivalLimit`, `pureTime`,
`terminal exploitability`, `strict covector`, and `positive solo` found no
existing declaration combining `(5)--(11)`.  No paper theorem is used.

The result has an actual-data adapter because every row is a literal
`IsQuittingNashBellmanEdge` for `r`, every terminal outcome uses `r`, and the
matrix in the separation argument is the literal normalized singleton matrix
of `r`.  Moreover, a terminal exploitability witness already produces the
canonical exact floor tail through the declarations just named.  The packet
does not produce `ResidualHardClass`, and it treats the nonplateau condition
as one branch: if positive rows do not persist, the checked eventual-plateau
theorems apply.  Thus the general theorem remains conditional on a supplied
tail, while its counterexample-facing corollary has an existing actual source
adapter and adds the common-covector/positive-solo reduction.

## Proof

### 1. Eventual support is boundary-tight and production-normal

Suppose player `i` has `p_n,i>0` at arbitrarily late dates.  Since
`p_n,i<=Q_n->0`, these hazards are eventually strictly between zero and one.
Exact endpoint Nash and Bellman evaluation then make forced Quit and forced
Continue equal to the current coordinate.

The chance that any opponent Quits is at most `sum_(j!=i)p_n,j`, hence tends
to zero.  Forced Quit therefore tends to `r({i})_i=s_i`, while forced
Continue and the current value tend to `b_i`.  Thus `b_i=s_i`, so `i in E`.
Finiteness of `I` gives one common cutoff after which all positive hazards are
supported on `E`.  Infinitely many positive-absorption rows and pigeonhole
make `E` nonempty.  Passing `chi_i<=X_n,i` to the limit gives
`chi_i<=b_i=s_i`, so every member of `E` is production-normal.

### 2. Zero is excluded from the full late drift simplex

Consider the compact convex set

```text
D_E={c-M*mu : mu is a probability vector supported on E}.       (12)
```

If `0 in D_E`, then `M*mu=c>=0`; on every positive coordinate of `mu`,
membership in `E` gives `(M*mu)_i=c_i=0`.  Thus `mu` is a full homogeneous
simplex witness supported on production-normal owners.

If `mu` has at least two positive coordinates, zero diagonal and zero
supported residual imply that each supported row has a distinct supported
nonpositive entry.  Induction through the recursive normal layers puts its
support in `normalCore`.  Restriction then contradicts
`ResidualHardClass.no_homogeneous`.

If `mu` is the vertex at `j`, then `M*mu>=0` says
`r({j})_i>=s_i` for every player `i`; production normality says
`chi_j<=s_j`.  Hence `j` is a `QuittingNormalNoHarmSingletonOwner`, and the
named checked theorem produces a uniform-equilibrium payoff.  On the other
branch of Theorem A this is excluded.  Therefore `0 notin D_E`.

Let `d*` be the closest point of `D_E` to zero.  Strict convex separation
with `ell=d*/||d*||` gives a `kappa>0` such that

```text
ell dot (c-M*mu)>=kappa                                      (13)
```

for every probability vector supported on `E`.

### 3. Conditional collisions are lower order

At a late row with `Q_n>0`, every `p_n,i<=Q_n`.  Pair counting bounds the
probability of at least two quitters by a constant depending only on `|I|`
times `Q_n^2`.  Conditional on absorption, multi-quitter mass is therefore
`O(Q_n)`.

Normalize the unique-quitter probabilities to a probability vector `mu_n`.
It is supported on `E`, and boundedness of the finite reward table gives,
uniformly along the tail,

```text
D_n=sum_i mu_n,i*r({i})+o(1).                                 (14)
```

Since `X_(n+1)->b`, equations `(13)--(14)` make

```text
ell dot (X_(n+1)-D_n)>=kappa/2                                (15)
```

after one common cutoff.  Multiply by `Q_n` and use exact Bellman equation
`(3)`.  At `Q_n=0`, both sides of the resulting row inequality are zero.
Summing proves `(5)`.

The left side of `(5)` stays bounded as `m->infinity`; therefore the tail
sum in `(6)` must be finite.  Taking the limit gives `(6)`.  Since
`Q_n->0` and `sum Q_n<infinity`, the standard infinite-product criterion
gives `C_n>0` for every late `n`, and removing a summable prefix of factors
gives `C_n->1`.

### 4. Exact terminal and deviation identities

Fix a late suffix start `n`.  Iterating the exact Bellman recursion and using
`X_t->b` gives

```text
U_i(n)=X_n,i-C_n*b_i.                                         (16)
```

Let

```text
rho_i(n,t)=product_(k=n)^(t-1) product_(j!=i)(1-p_k,j),
rho_i(n)=product_(k>=n) product_(j!=i)(1-p_k,j),
Delta_i(t)=X_t,i-F_i(t)>=0.                                  (17)
```

Exact endpoint Nash makes forced Continue reproduce the prescribed value at
every late row.  Running that recursion forever, or until a deterministic
Quit time `t`, and subtracting `(16)` gives

```text
NeverGain_i(n)=(rho_i(n)-C_n)*(-b_i),

TimeGain_i(n,t)=C_n*b_i-rho_i(n,t)*Delta_i(t).                 (18)
```

Finite total joint charge dominates every opponent-only charge, so

```text
C_n->1,
rho_i(n)->1,
sup_(t>=n)|rho_i(n,t)-1|->0.                                 (19)
```

Using `Delta_i(t)=X_t,i-F_i(t)`, the second identity in `(18)` rearranges
exactly to

```text
TimeGain_i(n,t)-F_i(t)
 =(rho_i(n,t)-1)F_i(t)
  +(C_n-rho_i(n,t))*b_i
  +rho_i(n,t)*(b_i-X_t,i).                                   (20)
```

The finite reward table bounds `F_i`; convergence `X_t->b` is uniform on
every late tail.  Hence `(20)` tends to zero uniformly over `t>=n`, while
the Never gain also tends to zero.

The proved-in-Lean pure-time extremality theorem identifies the supremum of
payoffs over all behavioral deviations with the supremum over the options in
`(18)`.  Translation by `U_i(n)`, together with the zero-gain option supplied
by the original strategy, proves the middle limit in `(10)`.

Finally, forcing `i` to Quit at row `t` produces singleton `{i}` unless an
opponent also Quits.  The latter probability tends to zero, so boundedness and
finiteness give `F_i(t)->s_i`.  Tail suprema of a convergent bounded real
sequence converge to its limit, proving the last limit in `(10)`; `(16)`
proves the first.

If every `s_i<=0`, finiteness of `I` makes the maximum terminal Nash error
tend to zero and `(16)` makes the terminal payoff vector tend to zero.  The
named fixed-target theorem produces the claimed uniform payoff.  Under no
uniform payoff some `s_i>0`, yielding `(11)`.  Also endpoint Nash gives
`F_i(t)<=X_t,i`, so any such coordinate satisfies `b_i>=s_i>0`.

## Boundary tests

1. **Positive-solo cost.**  In the one-player table with `r({i})_i=1`, take
   `X_n=1` and any strictly positive summable hazards, for example
   `p_n=2^(-n-2)`.  Every row is exact Nash--Bellman.  Here
   `U(n)=1-C_n` and quitting immediately gains `C_n`, so `e(n)=C_n->1`,
   exactly `(10)`.
2. **Nonpositive solo.**  With the same algebra and solo reward `-1`,
   `U(n)=C_n-1`; pure Never gains `1-C_n->0`, and `(10)` gives limit zero.
   This test is semantic only: the displayed negative value need not dominate
   the behavioral punishment floor.
3. **Finite charge is essential.**  In the positive one-player table, replace
   the summable hazards by `p_n=1/(n+2)`.  Then `C_n=0`, actual payoff is one,
   and exploitability is zero, not the positive solo value.  Thus Theorem B
   cannot omit finite total charge.
4. **The homogeneous/solved dispatch is essential to strict separation.**
   In the positive one-player example, `E={i}`, `c=0`, and `M=0`, so
   `0 in D_E` and no strict covector exists.  The game is already solved by
   immediate Quit, exactly the alternative in Theorem A.
5. **Infinitely many positive rows is used only for nonempty `E`.**  If all
   late rows are all-Continue, summability and positive survival are trivial,
   but the pigeonhole argument does not produce an active tight owner.

## Adapter and consumer

For the general theorem, the source adapter is literal: the hypotheses use
actual reward rows, actual product roots, actual exact endpoint Nash
inequalities, and the checked `IsQuittingNashBellmanEdge` relation.  No
auxiliary completion table or supplied verifier changes the rewards.
`ResidualHardClass` is the named actual-matrix gate.

For the counterexample-facing specialization,
`nonempty_positiveDebtDynamicTailWitness` and
`punishmentValue_le_tailValue` already produce the exact floor tail, and the
same witness already stores `jointAbsorption_summable`.  Theorem A is used on
the infinitely-often-positive, nonplateau arm; the eventual-zero-absorption
arm is routed to `EventualAllContinuePlateau.lean`.  On this named source the
new interface is `(5)--(6)`, not the existence or finite charge of the tail.

The all-behavior consumer is
`sSup_range_quittingTerminalPayoff_update_eq_pureTime`; the fixed-target
consumer is
`quittingGame_isUniformEquilibriumPayoff_of_terminalNash_tendsto`.  Thus the
terminal conclusion uses the project's unrestricted unilateral behavioral
deviation contract.  The zero-solo endpoint overlaps the independently
checked direct producer and is not claimed as a new class.

## Checked Lean realization

`QuittingConvergentDiffuseExactFloorTail.uniformPayoff_or_exists_strictCovectorPositiveSurvival`
checks the general supplied-tail alternative, including finite and infinite
horizon covector bounds, summable absorption, and eventual positive suffix
survival
(`UniformEquilibrium/Quitting/Chronology/ConvergentDiffuseExactFloorTail.lean`).
The canonical positive-debt-tail version is checked by
`QuittingPositiveDebtDynamicTailWitness.uniformPayoff_or_exists_strictCovectorPositiveSurvival`,
and the actual terminal-exploitability-witness adapter is
`QuittingTerminalExploitabilityWitness.exists_strictCovectorPositiveSurvivalTail`
(`UniformEquilibrium/Diagnostics/Quitting/Chronology/StrictCovectorDynamicTail.lean`).
These declarations constrain a hypothetical counterexample tail; they do not
consume the positive Never atom or prove a new uniform payoff in the residual
positive-solo branch.

## Scope and nonclaims

- This packet does not prove that every finite quitting game supplies the
  convergent diffuse tail in the hypotheses.  It does record that a terminal
  exploitability witness supplies the canonical tail; `ResidualHardClass`
  and the nonplateau arm remain separate hypotheses/branches.
- It does not attach or punish the positive Never atom, construct a paid
  return, or produce a uniform payoff when some solo reward is positive.
- It is not a counterexample and gives no positive terminal exploitability
  gap against profiles outside the displayed tail family.
- It does not claim that every exact Nash--Bellman tail has finite charge;
  the residual-hard/solved-branch separation and convergence hypotheses are
  essential to Theorem A.
- The strategy-class statement in Theorem B is unrestricted only because the
  exact checked pure-time extremality theorem applies to quitting profiles on
  the unique live history.  No analogous completeness claim is made for
  general stochastic games.
- The zero-solo uniform-payoff corollary is already proved in Lean by a direct
  producer.  On a general supplied tail, Theorem A also derives finite
  charge.  On the canonical counterexample tail finite charge was already a
  checked field; the new content there is the common strict-covector law and
  the exact positive-solo price of the surviving atom.
