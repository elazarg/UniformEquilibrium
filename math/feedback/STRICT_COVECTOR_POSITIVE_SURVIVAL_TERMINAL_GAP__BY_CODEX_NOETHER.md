# Export-Gate Audit: Strict Covector and Positive-Survival Terminal Gap

Reviewer: `CODEX_NOETHER`

Reviewed packet:
[`../exports/STRICT_COVECTOR_POSITIVE_SURVIVAL_TERMINAL_GAP.md`](../exports/STRICT_COVECTOR_POSITIVE_SURVIVAL_TERMINAL_GAP.md)

Scope: exact agreement with reviewed Gauss Propositions 54--55, the two-review
unrestricted-deviation gate, the canonical counterexample-tail adapter, and
the claimed conjecture-facing novelty.  This is a source and ordinary-
mathematics audit, not a Lean check of the exported theorems.

## Verdict

**Theorem A and Theorem B agree exactly with the independently reviewed
ordinary mathematics, and I found no mathematical objection.**  The support,
normality, separation, collision, Bellman, infinite-product, phantom,
pure-time, and fixed-target steps are all stated with the quantifiers and
signs checked in Noether Rounds 15--16.  The unrestricted part of Theorem B
has the required second falsification audit in Cedar Round 9.

**One source/novelty correction is required before treating the packet as
having passed the final export gate.**  The packet currently describes the
existence of the convergent diffuse tail as merely open and presents finite
charge as part of the conjecture-facing change.  For the canonical
counterexample tail, the repository already supplies a sharper named source
adapter and already stores summable joint absorption.  The new strict change
on that source is the global common-covector law `(5)--(6)` and the exact
all-behavior positive-solo price `(10)--(11)`, not the bare summability fact.
The packet should state this distinction explicitly.

## 1. Exact agreement with Proposition 54

The set `E={i:b_i=s_i}`, eventual support in `E`, production normality, and
the compact drift set

```text
D_E={b-s-M*mu : mu in Simplex(E)}
```

are identical to Gauss Proposition 54.  The nonvertex case correctly uses
the recursive-normal restriction before invoking
`ResidualHardClass.no_homogeneous`; the vertex case correctly dispatches by
`exists_uniformEquilibriumPayoff_of_normalNoHarmSingletonOwner`.  Thus the
packet does not silently apply the normal-core homogeneous exclusion to an
arbitrary ambient support.

For independent product roots, `p_(n,i)<=Q_n`, so pair counting gives
unconditional collision mass `O(Q_n^2)` and conditional collision mass
`O(Q_n)`.  This makes the conditional delivery uniformly equal to its
singleton mixture up to `o(1)`.  The Bellman orientation

```text
X_(n+1)-X_n=Q_n*(X_(n+1)-D_n)
```

is correct.  The `Q_n=0` row is handled without division.  Summation yields
the printed strict-covector inequality for every late `n<m`; bounded payoff
motion then implies finite charge, and the standard product criterion gives
positive late survival and `C_n->1`.

## 2. Exact agreement with Proposition 55

The executable suffix pays zero on the all-Continue-forever event, so the
phantom identity is

```text
U_i(n)=X_(n,i)-C_n*b_i.
```

The opponent-deleted survival intervals in `(17)--(18)` exclude the forced-
Quit row itself, as required.  The uniform estimate in `(20)` controls all
deterministic times `t>=n`, including times depending on `n`.  Pure Never has
gain `o(1)`.  Therefore the checked declaration
`sSup_range_quittingTerminalPayoff_update_eq_pureTime`
(`UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean`)
really upgrades the calculation to every unilateral behavioral strategy.

The forced-Quit value converges to the literal singleton reward because all
opponent hazards tend to zero.  Hence the exact exploitability limit is
`max(0,r_i({i}))` coordinatewise.  The fixed zero target and vanishing
terminal errors feed
`quittingGame_isUniformEquilibriumPayoff_of_terminalNash_tendsto`
(`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`)
exactly.  No one-shot-deviation principle or attained best response is being
assumed.

## 3. The canonical source adapter is already named and stronger

For a `QuittingTerminalExploitabilityWitness`, the checked declaration
`QuittingTerminalExploitabilityWitness.nonempty_positiveDebtDynamicTailWitness`
in
`UniformEquilibrium/Diagnostics/Quitting/Chronology/PositiveDebtDynamicTailWitness.lean`
supplies a canonical `QuittingPositiveDebtDynamicTailWitness`.  Its fields
already include:

- exact dynamic-debt edges, whose first component is the literal
  `IsQuittingNashBellmanEdge` required by the packet;
- coordinatewise payoff convergence and root hazards tending to zero;
- summable joint absorption and the distinguished deleted-player clock; and
- an actual source-table root sequence.

`QuittingPositiveDebtDynamicTailWitness.punishmentValue_le_tailValue`
(`UniformEquilibrium/Diagnostics/Quitting/Debt/DynamicTailCapCarrier.lean`)
supplies the all-date punishment floor.  The limiting exact all-Continue
self-loop supplies `b_i>=r_i({i})` through
`QuittingPositiveDebtSelfLoopLimit.soloReward_le_value`
(`UniformEquilibrium/Quitting/Debt/Dynamic/PositiveDebtSelfLoopLimit.lean`).
The packet's infinitely-many-positive-rows hypothesis is precisely the
nonplateau arm: if it fails, zero absorption is eventual, hence every late
root is all Continue, the branch analyzed in
`UniformEquilibrium/Diagnostics/Quitting/Chronology/EventualAllContinuePlateau.lean`.

Most importantly, the canonical witness already has the field
`jointAbsorption_summable`, originating in the checked theorem
`exists_terminalGapDynamicDebtTail_summableAbsorption`
(`UniformEquilibrium/Diagnostics/Quitting/Debt/ViolationCollapse.lean`).
Therefore Theorem A's derivation of finite charge is mathematically useful
for an arbitrary supplied tail satisfying the packet hypotheses, but it is
not a new narrowing of the canonical counterexample tail.  On that named
source the new content is:

1. every late support change is controlled by one strict covector and the
   quantitative residual-charge bound `(5)--(6)`; and
2. executing the already positive-survival suffix has the exact unrestricted
   positive-solo gap `(10)--(11)`.

## 4. Required packet repair and gate result

The `Source correspondence`, `Conjecture-facing change`, and `Adapter and
consumer` sections should add the canonical declarations above and separate
the following two scopes.

- **General conditional theorem:** from any supplied convergent diffuse exact
  floor tail plus `ResidualHardClass`, Theorem A proves finite charge and the
  strict covector law.
- **Named counterexample-tail reduction:** the canonical terminal-
  exploitability tail is already summably absorbing; on its nonplateau
  residual-hard arm, the packet newly supplies the common covector and the
  exact positive-solo all-behavior cost.

The packet must not say or imply that `ResidualHardClass` or the nonplateau
arm is produced for every game; both remain hypotheses/branches.  Conversely,
it should not say merely that the tail source is open, because the checked
counterexample witness already produces the canonical exact floor tail.

With that source/novelty correction, the packet meets the mathematical and
unrestricted-strategy review gates.  Until it is incorporated, I recommend
holding final export acceptance: the mathematics is valid, but gate items 4
and 6 currently identify the wrong new conjecture-facing contribution.

## Post-review resolution

Gauss incorporated the requested correction and I reread the revised packet.
It now names
`QuittingTerminalExploitabilityWitness.nonempty_positiveDebtDynamicTailWitness`,
`QuittingPositiveDebtDynamicTailWitness.punishmentValue_le_tailValue`,
`QuittingPositiveDebtSelfLoopLimit.soloReward_le_value`,
`exists_terminalGapDynamicDebtTail_summableAbsorption`, and the two exact
`EventualAllContinuePlateau.lean` declarations.  Its conjecture-facing,
source-audit, adapter, handoff, and nonclaim sections all distinguish the
general conditional finite-charge theorem from the already-summable
canonical counterexample tail.  The packet now claims as new on the latter
only the common-covector law `(5)--(6)` and positive-solo all-behavior price
`(10)--(11)`.

**Residual verdict: ACCEPTED FOR FORMALIZATION as written.**  The adapter
names and scope are exact, no duplicate finite-charge novelty claim remains,
and I find no residual export-gate objection.  This remains mathematical
evidence only, with no `L`, `A`, or `C` seal.
