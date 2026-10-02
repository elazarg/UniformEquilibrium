# Independent falsification of componentwise weighted potentials

Reviewer: `CODEX_MINER`

Verdict: **PASS mathematically, with mandatory but nonmathematical statement
and source-handoff repairs before export.**  The SCC orientation, weighted
increment calculation, quadratic and rank-one adapters, and unrestricted
behavioral consumer are correct.  I found no counterexample, including at the
empty and singleton boundaries.  Equation (2) must say `i != j`, and the
source audit should add the checked ordinal-toggle-potential bridge and repair
the proposition number in the Gauss comparison.

## Claim checked

For a finite quitting table, suppose the own membership gain has the affine
form

```text
g_i(S) = w_i(S union {i}) - w_i(S)
       = a_i + sum_{j in S} c_ij                 (i notin S).
```

Put an edge `j -> i` when `c_ij != 0`.  On each SCC assume positive weights
`lambda_i` with

```text
lambda_i * c_ij = lambda_j * c_ji
```

for every **distinct** `i,j` in that SCC.  The note claims that the finite
table has a sure-exit coalition, and therefore a pure stationary exact
terminal Nash profile against arbitrary unilateral behavioral deviations and
a uniform-equilibrium payoff.

## 1. SCC orientation

The orientation in the note is the correct one.  An edge `j -> i` means that
the action of `j` enters the membership gain of `i`.  Order condensation
components so every cross-component edge points from an earlier component to
a later component.  Then:

- the gain of a player in `C_k` can depend on selected players in earlier
  components, and these contributions are exactly the terms placed in
  `theta_i`;
- it can depend on players in its own component, handled by the block
  potential; and
- it cannot depend on a later component, since a nonzero such coefficient
  would be a backward condensation edge.

Thus processing source components toward sink components is essential and is
done correctly.  After `T_k` is chosen, later choices cannot invalidate its
member or outsider inequalities.  Reversing the order would fail already for
one one-way influence, but the displayed order does not.

The positivity-weighted reciprocity also implies that, inside an SCC,
`c_ij` is nonzero exactly when `c_ji` is nonzero.  This is stronger than
strong connectivity alone but is a legitimate hypothesis, not a hidden proof
step.

## 2. Weighted-potential increments

For fixed earlier union `S_<k`, let

```text
theta_i = a_i + sum_{j in S_<k} c_ij,
psi_{ij} = lambda_i c_ij = lambda_j c_ji.
```

For `i notin T`, direct subtraction from (8) gives

```text
Phi_k(T union {i}) - Phi_k(T)
  = lambda_i theta_i + sum_{j in T} psi_{ij}
  = lambda_i (theta_i + sum_{j in T} c_ij).
```

The deletion difference is the same expression at `T \ {i}` with the
opposite sign.  Maximization and `lambda_i>0` therefore give precisely (9)
and (10).  On assembling `S*`, the affine gain formula turns them into the
two defining clauses of `IsQuittingSureExitSet`; no strictness assumption or
division by a possibly zero interaction is used.

There is also a useful checked handoff omitted from the note.  The block
argument defines a global ordinal potential: for a coalition `S`, form the
component potentials in condensation order, with each component's `theta`
computed from `S` on earlier components, and order the resulting finite tuple
lexicographically.  A profitable toggle in `C_k` leaves every earlier tuple
coordinate unchanged and strictly increases coordinate `k`; later
coordinates may change arbitrarily.  Ranking the finitely many tuple values
produces `HasQuittingToggleOrdinalPotential`.  Hence the checked declarations

```text
exists_sureExitSet_of_toggleOrdinalPotential
quittingGame_exists_uniformPayoff_of_toggleOrdinalPotential
```

in
`UniformEquilibrium/Quitting/Stationary/TogglePotential.lean` are a shorter
existing downstream bridge than a new direct semantic proof.  They do not
duplicate the new actual-coefficient/SCC adapter, which remains ordinary
mathematics.

## 3. Empty and singleton boundaries

The empty player type is harmless.  Its SCC list and constructed coalition
are empty and both sure-exit families are vacuous.  The exact checked
consumer in `SureExitSet.lean` assumes only `Fintype` and `DecidableEq`, not
`Nonempty`, so it covers this case.

For one player, the sole SCC has no distinct-pair equation.  The potential is
`0` at the empty subset and `lambda_i a_i` at the singleton.  A maximizer
chooses the singleton when `a_i>=0` and the empty set when `a_i<=0` (either at
equality), exactly matching the singleton sure-exit versus all-Continue
boundary.  Here `quittingSetReward reward empty = 0` supplies the required
nonabsorption convention.

This boundary audit exposes one wording defect: (2) presently writes
`(i,j in C)` although `c_ii` was never defined.  It must read “for distinct
`i,j in C`.”  The singleton and empty statements then become literal rather
than conventional.

## 4. Quadratic adapter

For (3), toggling `i` into `S` adds the linear term `a_ii` and exactly the
pair terms `b_{i,{i,j}}` for `j in S`.  Every `a_ij` with `j!=i` and every
pair term not containing `i` occurs on both sides and cancels.  This remains
true for `S=empty`, where the extended empty reward is zero and
`r_i({i})=a_ii`.  Thus (4) is exact.

Reciprocal symmetry `b_{i,{i,j}}=b_{j,{i,j}}` makes `c_ij=c_ji`, so unit
weights satisfy the SCC equations.  The claimed freedom of passive linear
and quadratic coefficients is genuine: those coefficients affect payoff
levels but never the toggling player's membership difference.

The negative reciprocal triangle is a valid strictness test.  Unit weights
symmetrize all three negative interactions, whereas the directed negative
triangle has sign product `-1` and therefore fails
`EveryDirectedInfluenceCyclePositive`.  It is not covered by
`quittingGame_exists_uniformPayoff_of_cycleBalancedSignConsistentInfluence`.

## 5. Rank-one adapter

On a nontrivial SCC suppose `c_ij=x_i y_j` and all products `x_i y_i` have
the same nonzero sign `sigma`.  Then `x_i,y_i` are nonzero and

```text
lambda_i c_ij
  = |y_i/x_i| x_i y_j
  = sigma y_i y_j
  = lambda_j c_ji.
```

The displayed positive weight is therefore correct for either common sign.
Independently, strong connectivity of a nontrivial rank-one SCC forces each
`y_i` nonzero from an outgoing edge `i -> k`, and each `x_i` nonzero from an
incoming edge `l -> i`.  Singleton SCCs impose no distinct-pair equation and
may take any positive weight.

For precision, the corollary should say “on **each** nontrivial SCC, the
products have a common nonzero sign,” with the common sign allowed to differ
between SCCs.  A single global common sign is stronger and also sufficient;
the current singular wording “on a nontrivial SCC” is ambiguous.

## 6. Behavioral consumer and failure example

The source correspondence with
`UniformEquilibrium/Quitting/Paths/SureExitSet.lean` is exact:

- `isεAsymptoticNash_pureSetRoot_iff_isQuittingSureExitSet` states the
  equivalence at error zero for the full behavioral strategy class; and
- `isUniformEquilibriumPayoff_setReward_of_isQuittingSureExitSet` upgrades the
  constructed set reward to a uniform-equilibrium payoff.

No stationary-deviation-only inference is being made.

The two-player nonsymmetrizable test also checks out.  The four coalitions
fail the pure test in turn: player 2 joins at `empty`, player 1 leaves at
`{1}`, player 1 joins at `{2}`, and player 2 leaves at `{1,2}`.  At quit rates
`(1/2,1/2)`, conditional terminal masses of `{1}`, `{2}`, and `{1,2}` are all
`1/3`, both values are zero, and each player's Quit and Continue endpoints
are both zero.  Repeating the stationary root therefore gives an exact
behavioral terminal Nash profile by the checked stationary best-response
machinery.  Passive players receiving `-1` exactly when they join and zero
otherwise optimally continue, so the stated padding remains valid.

## 7. Source and export repairs

The comparison to the older Gauss note has the right mathematical content
but the wrong label.  The symmetric pairwise-interaction subclass is Section
3 following **Proposition 2** of
`notes/CODEX_GAUSS__CURL_FREE_TOGGLE_POTENTIAL.md`; Proposition 3 is the
different quit-complementarity theorem.  That citation should be repaired.

The source audit should additionally name `TogglePotential.lean` and explain
the lexicographic ordinal-potential adapter above.  The note is right that
`QuittingInfluenceBlockCertificate` is not a faithful handoff: its switched
increasing-differences blocks would discard the negative reciprocal triangle.

Subject to those repairs, this is a complete new special-case producer with
an actual-data adapter and a checked unrestricted-behavior consumer.  It is a
reasonable export candidate after the required second independent
falsification review; it does not narrow the arbitrary hard residual without
a separate theorem producing the affine symmetrizable structure.
