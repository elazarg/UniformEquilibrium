# Review of `CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION`, Round 20

Reviewer: `CODEX_GAUSS`

Date: 2026-08-23

## Claim checked

I independently tried to falsify Section 56, Proposition 54: full projective
Q-bar of the normalized singleton matrix implies a uniform-equilibrium payoff.
The proposed construction restricts the continuous absorption path to the
production minmax-normal players, embeds it in the ambient game, dispatches a
harmful surviving deleted clock through Proposition 48, and otherwise compares
the continuum and logarithmically discretized opponent-only laws uniformly over
every pure Quit time and `Never`.

This is a review of ordinary mathematics. Proposition 54 is not a Lean
declaration. In particular, the subtype reward-table adapter and the equality
between the Literature and production punishment values are not checked here
as named Lean facts.

## Verdict

**VALID ordinary mathematics, with no mathematical objection found.** The
normal-subtype lift, the positive-survival case, the opponent-law estimate, the
fixed target, and the passage from pure times to unrestricted behavioral
deviations all survive the checks below. This is one substantive falsification
review of unrestricted strategy coverage; the conference gate still requires a
second independent review before a theorem of this scope can be exported.

## 1. Normal-subtype path and ambient lift

Let

```text
N = {i | quittingPunishmentValue reward i <= s_i}.
```

Outside the zero-solo branch, some `s_j>0`. The checked inequality
`quittingPunishmentValue_le_max_solo` in
`UniformEquilibrium/Quitting/Stationary/MinMax.lean` gives
`quittingPunishmentValue reward j <= s_j`, so `N` is nonempty.

For the subtype reward table, the receiver's solo baseline is unchanged and an
owner singleton is sent to the corresponding ambient singleton. Hence its
`normalizedSoloMatrix` is literally the principal restriction of the ambient
matrix. Every nonempty principal subset of `N` maps injectively to a nonempty
ambient principal subset. Reindexing a projective LCP solution proves inherited
projective Q-bar. This uses only the definition `IsProjectiveQBarMatrix` in
`UniformEquilibrium/Quitting/Classification/LCP/MatrixClasses.lean`; I found no
hidden use of the normal-core matrix.

The continuous path supplied by
`exists_continuous_zeroPerfect_of_projectiveQBar` in
`UniformEquilibrium/Quitting/AbsorptionPath/PrincipalQContinuousPath.lean` is
singleton-supported on `N`. After embedding it, every omitted coordinate has
zero derivative. For an omitted player `k`, abnormality and Simon's `lemma3`
give, for each path owner `j in N`,

```text
r({j})_k >= chi_k > s_k.
```

The residual law at every `t<1` is a probability mixture of precisely those
normal-owner singleton rows, so its `k` coordinate is strictly above `s_k`.
Thus the omitted player's lower sequential inequality holds, while the upper
inequality has a false antecedent because its singleton derivative is zero.
There are no jumps. I found no omitted-player perfection condition left
unchecked.

The source adapter used here is mathematically exact: both `MinMaxQuit` in
`Literature/Simon2007.lean` and `quittingPunishmentValue` minimize over an
opponent plan the supremum over the replaced player's complete live hazard
sequence, with first-quit terminal rewards and zero on nontermination. A
quitting game has only the all-Continue live history, so history-dependent
behavior reduces to that sequence. This equality should nevertheless remain
listed as an unformalized adapter until a named production declaration states
it.

## 2. Transversality branch

All omitted players have logarithmic rate zero, hence deleted survival
`exp(-T) -> 0`. Therefore a positive deleted-survival limit can belong only to
an owner in `N`. Proposition 53's identity then gives exactly two cases:

- a harmless atom, for which `-R_i(infinity)s_i <= 0`; or
- a profitable `Never` deviation, for which `s_i<0` and
  `r({i})_k >= s_k` for every ambient player `k`.

In the second case `i` is production-normal and the last inequalities are
exactly Proposition 48's no-harm hypotheses. Its reviewed finite-prefix plus
actual-punishment construction gives stationarily generated approximate
equilibria. The checked declarations
`quittingApproximateEquilibriumExistence_of_stationarilyGenerated` and
`quittingGame_exists_uniformEquilibriumPayoff_of_approximateEquilibriumExistence`
in
`UniformEquilibrium/Quitting/Classification/Existence/StationarilyGeneratedBranch.lean`
then supply the semantic endpoint. Positive deleted survival itself is not
incorrectly excluded; a nonnegative solo makes it harmless.

## 3. Exact opponent-only comparison

Fix a deviating player `i` and one block. Put

```text
A_j = integral_block a_j,  H = sum_{j != i} A_j,
Q_k = exp(-sum_{ell<k} H_ell).
```

Deleting `i` gives exactly the same start-of-block survival `Q_k` in both
models. In the continuum model, the conditional mass of singleton opponent
`j` in the block is

```text
integral_block exp(-integral_blockStart^u sum_{l != i} a_l) a_j(u) du,
```

so it lies in `[exp(-H) A_j, A_j]`. In the product row the exact unique-`j`
mass is

```text
(1-exp(-A_j)) exp(-(H-A_j))
  = exp(-H)(exp(A_j)-1),
```

which lies in the same interval. Therefore the singleton `L1` discrepancy is
at most `H(1-exp(-H))`.

The product collision mass among opponents is at most `H^2/2`. For
`0<=H<=h`,

```text
1-exp(-H) >= H exp(-H) >= H exp(-h),
```

and hence

```text
H^2/2 <= (h exp(h)/2)(1-exp(-H)).
```

Finally,

```text
sum_k Q_k(1-exp(-H_k)) = 1-R_i(infinity).
```

Weighting the two block errors by `Q_k` gives the claimed global outcome-law
bound

```text
L(h) = h + h exp(h)/2.
```

This calculation remains valid when some `H_k=0`, when the denominator-free
law has a positive survival atom, and when `R_i(infinity)>0`. The continuum
and discrete laws assign exactly the same mass `R_i(infinity)` to `Never`,
with terminal payoff zero.

## 4. Pure Quit times, target, and unrestricted behavior

If `i` is forced to Quit in block `n`, all earlier opponent outcomes are
covered by `M L(h)`. Conditional on survival to the forced row, the chance
that an opponent quits simultaneously is at most `1-exp(-H_n)<=h`; replacing
that coalition payoff by `s_i` costs at most `2Mh`. Thus

```text
discretePureQuit_i(n)
  <= continuumPureQuit_i(nh) + M L(h) + 2Mh
  <= gamma_i(0) + M h(3+exp(h)/2).
```

The second inequality is precisely the finite-time Snell comparison of
Proposition 53. `Never` uses the same comparison without the simultaneous-row
term. This covers every `Option Nat` pure time uniformly in `n`.

I also rechecked the pieces of Proposition 51 used here. With block total
hazard `h`, continuum singleton masses and product unique-singleton masses lie
in the same coordinate intervals, while collision mass is at most `h^2/2`.
Geometric weighting by `exp(-kh)` gives

```text
D(h)=h+h^2/(2(1-exp(-h))) -> 0,
```

and therefore the prescribed discrete payoff is within `E(h)=M D(h)` of the
single fixed vector `gamma(0)`. The target is chosen with the path, before the
accuracy and before `h`.

Consequently every pure-time deviation gain is at most `F(h)+E(h)`, uniformly
over finite Quit times and `Never`. The exact equality
`sSup_range_quittingTerminalPayoff_update_eq_pureTime` in
`UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean` upgrades
this to replacement of the player's entire behavioral strategy. The checked
fixed-target consumer
`quittingGame_isUniformEquilibriumPayoff_of_terminalNash_all_errors_approxTarget`
in
`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalTargetSemantics.lean`
then applies.

## 5. Falsification tests

- **One positive owner, no opponent rate:** `H_k=0` for every block and
  `R_i(infinity)=1`. Both opponent laws are the same `Never` atom; the
  discretized geometric solo absorption has the exact singleton target.
- **One negative owner:** the normal set can be empty, showing why the
  zero-solo split must precede the subtype construction. All-Continue is the
  checked exact equilibrium.
- **Positive surviving clock:** retaining `R_i(infinity)>0` does not break the
  telescoping sum; it changes its right side from `1` to
  `1-R_i(infinity)` and gives the same atom in both laws.
- **Omitted abnormal player active on a positive-measure interval:** impossible
  by construction, since its embedded rate is identically zero. The ambient
  perfection definition asks only the lower inequality there.
- **Simultaneous forced-quit collision:** this is not hidden in the singleton
  comparison; it is exactly the separate `2Mh` term.

None produces a counterexample.

## Remaining formal/source obligations

Before promotion, the result still needs the conference's second independent
unrestricted-class review. A later Lean implementation will also need explicit
adapters for subtype reward restriction/reindexing, the ambient path embedding,
and the equality of Simon's `MinMaxQuit` with production
`quittingPunishmentValue`. Those are implementation obligations, not gaps in
the ordinary proof above.
