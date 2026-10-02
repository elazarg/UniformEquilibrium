# Projective Q-Bar Uniform-Payoff Decoder

Author: `CODEX_NOETHER`

Independent unrestricted-class falsification reviews:

- [`CODEX_GAUSS`, Round 20](../feedback/CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION__BY_CODEX_GAUSS__ROUND_20.md)
- [`CODEX_CEDAR`, Round 15](../feedback/CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION__BY_CODEX_CEDAR__ROUND_15_PROJECTIVE_QBAR.md)

Both reviews report valid ordinary mathematics with no objection. They are
independent attempts to falsify the subtype lift, transversality fork,
positive-survival boundary, probability estimates, fixed target, and coverage
of every unilateral behavioral deviation. The final actual-data capstones are
now proved in Lean by the declarations cited below.

## Exact statement

Let `I` be a nonempty finite player set. A finite quitting reward table is a
function

```text
r : {nonempty finite subsets S of I} -> R^I.
```

At every date each player independently chooses Continue or Quit. The game
ends at the first date whose quitting coalition `S` is nonempty and pays
`r(S)`; it pays zero if every player continues forever. Strategies are
arbitrary behavioral strategies. Define

```text
s_i    = r({i})_i,
M_ij   = r({j})_i-s_i.
```

A matrix `B` on a finite nonempty set `J` is projective Q if, for every
`q in R^J`, there exist nonnegative weights

```text
z_0, (z_j)_(j in J),
z_0+sum_j z_j=1,
```

and a nonnegative vector

```text
w_i=z_0 q_i+sum_j B_ij z_j
```

such that `z_i w_i=0` for every `i`. The ambient matrix `M` is projective
Q-bar if every nonempty principal submatrix is projective Q.

**Theorem.** If `M` is projective Q-bar, then there exists a payoff vector
`v in R^I` such that

```text
(quittingGame r).IsUniformEquilibriumPayoff none v.
```

The target `v` is chosen before the accuracy. For every positive accuracy the
constructed terminal approximate-Nash profiles are tested against replacement
of one player's entire behavioral strategy, including every finite stopping
time and Never. The checked quitting terminal-to-uniform semantics then gives
the usual all-sufficiently-long-horizons uniform-payoff conclusion.

## Conjecture-facing change

The production LCP gate defines `ProjectiveQBarMatrixBranch` in
`UniformEquilibrium/Quitting/Classification/LCP/Gate.lean`. Its field
`full_projectiveQBar` supplies exactly the theorem's matrix hypothesis, but
the previously checked endpoint is only a continuous sequentially zero-perfect
absorption path. Such a path is not itself a strategy or equilibrium.

This theorem supplies the missing direct all-behavior decoder and therefore
closes `ProjectiveQBarMatrixBranch` in ordinary mathematics. It does not solve
`ResidualHardClass` and does not settle the full finite-quitting conjecture.

## Proof

### 1. Restrict the path to production-normal players

Let

```text
chi_i = inf_(opponent behavioral plans) sup_(behavioral replies of i)
          terminalPayoff_i
```

be the quitting punishment value, and call `i` normal when `chi_i<=s_i`.
If every `s_i<=0`, all Continue is an exact terminal Nash profile with payoff
zero. The checked zero-solo consumer then makes zero a uniform-equilibrium
payoff.

Otherwise choose `j` with `s_j>0`. The checked inequality

```text
chi_j<=max(s_j,0)=s_j
```

is `quittingPunishmentValue_le_max_solo`
(`UniformEquilibrium/Quitting/Stationary/MinMax.lean`). Hence the subtype

```text
N={i | chi_i<=s_i}
```

is nonempty.

Restrict the reward table to coalitions and payoff coordinates in `N`. Its
normalized singleton matrix is the principal restriction of `M`. Every
nonempty principal subset of `N` maps injectively to a nonempty ambient
principal subset, so ambient projective Q-bar and finite reindexing give
projective Q-bar on the restricted table.

The checked theorem
`exists_continuous_zeroPerfect_of_projectiveQBar`
(`UniformEquilibrium/Quitting/AbsorptionPath/PrincipalQContinuousPath.lean`)
therefore supplies a continuous sequentially zero-perfect absorption path on
`N`. Embed its singleton mass coordinates in the ambient game and set every
other coalition coordinate to zero.

For a player in `N`, the continuation payoff and both perfection inequalities
are unchanged. An omitted player `k` is abnormal. Simon's `lemma3`
(`Literature/Simon2007.lean`), under the ordinary identification of the
paper's live-hazard minmax with `quittingPunishmentValue`, gives

```text
r({j})_k>=chi_k>s_k                 for every j in N.                 (1)
```

Every residual continuation law of the embedded path is a probability mixture
of those normal-owner singleton rows. Thus its `k` coordinate is strictly
above `s_k`. This is the lower continuous sequential-perfection condition.
The omitted singleton coordinate is identically zero, so the upper condition,
whose premise is positive own derivative, is vacuous. The embedded path is an
ambient continuous sequentially zero-perfect path.

### 2. Rates, indifference support, and the deleted-clock identity

Write `pi_i(t)` for its cumulative singleton mass and `gamma(t)` for its
conditional continuation payoff. Total mass is `t`. Coordinate monotonicity
therefore gives

```text
0<=pi_i(v)-pi_i(u)<=v-u.
```

Every coordinate is one-Lipschitz and absolutely continuous. A nonsingleton
coordinate has lower-right derivative zero at every interior time; at ordinary
differentiability points this is its usual derivative. Hence every
nonsingleton coordinate is identically zero.

Pass to logarithmic time `tau=-log(1-t)`. There are measurable rates
`a_i(tau)>=0`, defined almost everywhere, such that

```text
sum_i a_i(tau)=1,
gamma(tau)=integral_[tau,infinity)
  exp(-(u-tau))*sum_i a_i(u)r({i}) du.                               (2)
```

Sequential perfection gives `gamma_i(tau)>=s_i`. At almost every point with
`a_i(tau)>0`, the positive own derivative invokes the reverse inequality.
Thus

```text
a_i(tau)>0  ->  gamma_i(tau)=s_i              almost everywhere.    (3)
```

For player `i`, delete her clock and set

```text
R_i(T)=exp(-integral_0^T (1-a_i(u)) du).                             (4)
```

Differentiating `(2)` at Lebesgue points and using `(3)` gives

```text
(R_i gamma_i)'=-R_i*sum_(j!=i) a_j r({j})_i.
```

The right side is absolutely integrable because its absolute value is at most
`B R_i(1-a_i)=-B R_i'`, where `B` bounds singleton rewards. Therefore, for
every finite `T`,

```text
gamma_i(0)
 = integral_0^T R_i(u)*sum_(j!=i)a_j(u)r({j})_i du
   +R_i(T)gamma_i(T).                                                (5)
```

Replacing the final continuation by a Quit-now payoff `s_i` can only lower
the right side. Hence every finite deterministic Quit time is weakly
unprofitable in this continuum stopping model. Never has exact gain

```text
Never_i-gamma_i(0)=-lim_(T->infinity) R_i(T)gamma_i(T).               (6)
```

At most one player has positive limiting deleted survival. If `R_i(infinity)`
is positive, opponent rate is integrable, so the residual law in `(2)`
converges to the singleton row `r({i})`. Consequently

```text
gamma(T)->r({i}),
r({i})_k>=s_k for every k,
lim_T R_i(T)gamma_i(T)=R_i(infinity)s_i.                             (7)
```

Thus a profitable Never deviation is possible exactly when a unique
exceptional owner `i` has positive deleted survival, negative `s_i`, and the
no-harm inequalities in `(7)`.

Every omitted player has `a_i=0` almost everywhere and therefore
`R_i(T)=exp(-T)->0`. An exceptional owner must lie in `N` and is normal.

### 3. Dispatch the harmful exceptional atom

We record the finite-punishment argument so this packet does not defer this
branch. Suppose a normal owner `i` satisfies

```text
r({i})_k>=s_k                    for every k!=i.                      (8)
```

Fix an equilibrium slack `epsilon>0` and an independent punishment slack
`delta>0`. Let `B` bound every terminal and profile payoff. For `L` dates,
only `i` is scheduled to Quit, independently with probability `a`; after
survival of all `L` dates, switch to a behavioral `delta`-punishment of `i`.
Put `z=(1-a)^L`.

Against the infinite rare-`i` row, any outsider's pure-time gain is at most
`2Ba`: without simultaneous collision it compares `s_k` with `r({i})_k` by
`(8)`, and collision has probability at most `a`. Replacing the infinite tail
after date `L` changes both prescribed and deviating payoffs by at most `2Bz`,
so outsider regret is at most

```text
2Ba+4Bz.                                                             (9)
```

Owner `i` gets `s_i` from every Quit before the splice. A response reaching
the punishment gets at most `chi_i+delta<=s_i+delta`, while the prescribed
payoff is at least `s_i-2Bz`. Owner regret is at most

```text
delta+2Bz.                                                           (10)
```

Pure-time extremality covers arbitrary behavioral deviations in `(9)`.
Choose `a` small and then `L` large so the non-`delta` terms are below
`epsilon`. These profiles are stationarily generated approximate equilibria.
The checked theorems
`quittingApproximateEquilibriumExistence_of_stationarilyGenerated` and
`quittingGame_exists_uniformEquilibriumPayoff_of_approximateEquilibriumExistence`
(`UniformEquilibrium/Quitting/Classification/Existence/StationarilyGeneratedBranch.lean`)
give a uniform-equilibrium payoff. This closes the profitable-Never branch.

In the complementary branch, `(5)`--`(6)` say that every continuum finite
Quit time and Never pays at most `gamma_i(0)` for every player. Positive
deleted survival is allowed; it is harmless when the product in `(6)` is
nonnegative.

### 4. Logarithmic product discretization

Fix `h>0` and set

```text
A_(k,i)=integral_[kh,(k+1)h) a_i(u) du,
p_(k,i)=1-exp(-A_(k,i)).                                             (11)
```

Then `A_(k,i)>=0` and `sum_i A_(k,i)=h`. At discrete date `k`, let player `i`
Quit independently with probability `p_(k,i)`. The joint Continue probability
of every block is exactly `exp(-h)`, so the profile absorbs almost surely.

In a whole block, the continuum singleton mass and product unique-singleton
mass for coordinate `i` both lie in

```text
[exp(-h)A_(k,i), A_(k,i)].                                          (12)
```

The singleton `L1` discrepancy is at most `h(1-exp(-h))`, and product
collision mass is at most `h^2/2`. Weighting blocks from any suffix by
`1,exp(-h),exp(-2h),...` gives the uniform full-law bound

```text
D(h)=h+h^2/(2(1-exp(-h))) -> 0.                                     (13)
```

If `M` bounds the absolute value of every terminal reward coordinate and
`V_k` is the discrete prescribed payoff from block `k`, then

```text
|V_k-gamma(kh)|<=E(h):=M D(h)                                       (14)
```

for every player and every `k`. This includes the fixed-target estimate
`|V_0-gamma(0)|<=E(h)`.

### 5. Global opponent-only comparison

Fix a deviating player `i` and write

```text
H^i_k=sum_(j!=i) A_(k,j)=h-A_(k,i),
Q^i_k=exp(-sum_(ell<k)H^i_ell)=R_i(kh).                              (15)
```

The equality is exact: both sides are the survival probability after deleting
player `i`'s clock. Conditional on block entry, the continuum opponent-only
mass of singleton `j` and the product unique-`j` mass both lie in

```text
[exp(-H^i_k)A_(k,j), A_(k,j)].                                      (16)
```

The product mass is exactly

```text
exp(-H^i_k)*(exp(A_(k,j))-1).
```

Thus the singleton discrepancy in the block is at most

```text
H^i_k*(1-exp(-H^i_k)).                                               (17)
```

Opponent collisions have mass at most `(H^i_k)^2/2`. Since
`0<=H^i_k<=h`,

```text
(H^i_k)^2/2
 <= (h*exp(h)/2)*(1-exp(-H^i_k)).                                   (18)
```

Finally, survival telescopes even when its limit is positive:

```text
sum_k Q^i_k*(1-exp(-H^i_k))=1-R_i(infinity)<=1.                     (19)
```

The complete continuum and discrete opponent-only outcome laws therefore
have global `L1` discrepancy at most

```text
L(h)=h+h*exp(h)/2.                                                    (20)
```

Their survival atoms have the same mass `R_i(infinity)` and payoff zero.

If player `i` is forced to Quit at discrete date `n`, all earlier opponent
outcomes are covered by `(20)`. At date `n`, simultaneous opponent quitting
has probability at most `1-exp(-H^i_n)<=h`; replacing its coalition payoff by
the continuum solo payoff costs at most `2Mh`. Uniformly in `n`,

```text
discretePureQuit_i(n)
 <= continuumPureQuit_i(nh)+F(h)
 <= gamma_i(0)+F(h),

F(h)=M*h*(3+exp(h)/2).                                               (21)
```

For Never the same bound holds without the final `2Mh` term. Equations
`(14)` and `(21)` show that every pure-time deviation gains at most
`F(h)+E(h)` over the prescribed profile.

The exact equality
`sSup_range_quittingTerminalPayoff_update_eq_pureTime`
(`UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean`)
identifies the supremum over all unilateral behavioral deviations with the
supremum over finite pure Quit times and Never. Hence the product profile is
an unrestricted terminal `(F(h)+E(h))`-Nash profile.

Given `epsilon>0`, choose `h` so that `F(h)+E(h)<epsilon` and
`E(h)<epsilon`. The profile is terminal `epsilon`-Nash and its payoff is
coordinatewise `epsilon`-close to the one fixed target `gamma(0)`. The checked
consumer
`quittingGame_isUniformEquilibriumPayoff_of_terminalNash_all_errors_approxTarget`
(`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalTargetSemantics.lean`)
makes `gamma(0)` a uniform-equilibrium payoff. This closes the complementary
branch and proves the theorem.

## Probability, information, and deviation audit

- All randomizations are independent mixed actions at each live date. No
  public correlating device or hidden signal is assumed.
- A quitting game has one live public history: all previous players continued.
  An arbitrary behavioral strategy therefore induces an arbitrary
  time-indexed Quit hazard on that history.
- The prescribed product profile absorbs almost surely because each block has
  joint survival `exp(-h)`.
- A unilateral deviator may replace her complete behavioral strategy. Pure-
  time extremality is an exact checked equality, not a bounded-controller
  approximation.
- The pure-time family includes every finite Quit date and Never. A positive
  opponent-deleted Never atom is retained explicitly in `(19)`--`(20)`.
- Collision coalitions are not discarded. Opponent collisions occur in
  `(18)`, while collision with a forced quitter is the separate `2Mh` term.

## Boundary tests

1. **One negative-solo player.** The production-normal subtype may be empty.
   This is why the zero-solo branch is taken first; all Continue is the exact
   equilibrium.
2. **One positive-solo player.** The owner has `R(infinity)=1`. Never pays
   zero and cannot beat the positive singleton target. The logarithmic product
   profile is geometric singleton absorption.
3. **Positive deleted survival.** Formula `(19)` becomes
   `1-R(infinity)`, not `1`; the common survival atom remains in both laws.
4. **Negative normal exceptional owner.** This case is not passed to the
   direct decoder. The no-harm inequalities `(7)` invoke the finite-punishment
   construction `(9)`--`(10)`.
5. **Omitted abnormal player.** Its rate is identically zero. It needs only
   the lower sequential inequality, supplied strictly by `(1)`; there is no
   unsupported equality claim.
6. **Forced-row collision.** Arbitrary rewards on coalitions containing the
   deviator and opponents are covered by the explicit `2Mh` term.

## Source correspondence and novelty

Relevant checked declarations are:

- `IsProjectiveQBarMatrix` and `principalMatrix`
  (`UniformEquilibrium/Quitting/Classification/LCP/MatrixClasses.lean`);
- `exists_continuous_zeroPerfect_of_projectiveQBar`
  (`UniformEquilibrium/Quitting/AbsorptionPath/PrincipalQContinuousPath.lean`);
- `quittingPunishmentValue_le_max_solo`
  (`UniformEquilibrium/Quitting/Stationary/MinMax.lean`);
- `sSup_range_quittingTerminalPayoff_update_eq_pureTime`
  (`UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean`);
- `quittingApproximateEquilibriumExistence_of_stationarilyGenerated` and
  `quittingGame_exists_uniformEquilibriumPayoff_of_approximateEquilibriumExistence`
  (`UniformEquilibrium/Quitting/Classification/Existence/StationarilyGeneratedBranch.lean`);
- `quittingGame_isUniformEquilibriumPayoff_of_terminalNash_all_errors_approxTarget`
  (`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalTargetSemantics.lean`);
  and
- `quittingGame_isUniformEquilibriumPayoff_zero_of_zeroSolo`
  (`UniformEquilibrium/Quitting/Punishment/ZeroSoloDisjunct.lean`).

Simon, *The structure of non-zero-sum stochastic games* (2007), `lemma3` in
`Literature/Simon2007.lean`, supplies `(1)`. There is no named checked adapter
identifying its `MinMaxQuit` with production `quittingPunishmentValue`; that
semantic identification is part of this ordinary proof.

AGKRS, *Absorption paths and equilibria in quitting games*, arXiv-v1 Theorems
4.13 and 5.2, published Theorems 4.15 and 5.4, already claim the theorem-level
existence class. Published Remark 5.5 also anticipates lifting a continuous
path from a player subset when omitted coordinates receive nonnegative
normalized payoffs. The project transcription
`Literature/AshkenaziGolanKrasikovRainerAndSolan2022.lean` deliberately does
not declare the path-to-equilibrium theorem: its final global inference is not
represented by an available semantic decoder, and the stronger universal
sequential-perfection implication is refuted by
`not_quittingSequentialPerfectionErrorExponent`
(`UniformEquilibrium/Quitting/Classification/ErrorExponentRefutation.lean`).

The exported novelty is therefore not the theorem-level class. It is a
rigorous repaired direct route from the checked continuous path to a checked
all-behavior fixed-target endpoint: canonical restriction to production-normal
owners, exact deleted-clock transversality, generated-branch dispatch, and the
global opponent-only `O(h)` comparison. This is a new direct route to an
established semantic endpoint and closes a named live project branch.

## Adapter and consumer

The actual-data adapter starts with an arbitrary reward table satisfying the
projective-Q-bar matrix hypothesis. Its production-normal restriction,
strategic fork, and ambient semantic conclusion are assembled in the checked
capstones cited below.

There are two downstream consumers:

- harmful transversality uses the checked generated-branch-to-uniform-payoff
  chain; and
- harmless transversality uses the checked fixed-target terminal-to-uniform
  theorem.

The checked capstones assemble these premises and reach the unrestricted
behavioral-deviation semantics.

## Checked Lean realization

`quittingPunishmentNormalPathStrategicFork` and
`quittingPunishmentNormalPathDecoder_of_snell` assemble the checked path fork
and decoder.  The raw-matrix semantic capstones
`exists_uniformEquilibriumPayoff_of_punishmentNormal_projectiveQBar_snell` and
`exists_uniformEquilibriumPayoff_of_projectiveQBar_snell` are proved in
`UniformEquilibrium/Quitting/AbsorptionPath/PunishmentNormalPathStrategicSnell.lean`.
The latter starts from `IsProjectiveQBarMatrix (normalizedSoloMatrix reward)`
on the actual reward table and produces an unrestricted-behavior
uniform-equilibrium payoff.

## Scope and nonclaims

- This packet does not prove the full finite-quitting conjecture.
- It does not produce a strategy for `ResidualHardClass`.
- It does not claim the AGKRS theorem-level conclusion is new.
- It does not formalize Simon's literature/production minmax adapter.
- It does not claim that an arbitrary sequentially zero-perfect path decodes;
  the normal-owner restriction and transversality dispatch are essential.
- It does not use correlated randomization or restrict the deviator to a
  finite controller, stationary response, or one-shot deviation.
- The projective-Q-bar actual-data adapter and semantic conclusion are proved
  in Lean; the residual hard class remains outside the theorem.
