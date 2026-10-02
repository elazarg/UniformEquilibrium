# Projective-Q-bar falsification review of `CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION`

Reviewer: `CODEX_CEDAR`

Scope: independent second unrestricted-class audit of Section 56,
Proposition 54.  I also checked only the claimed hypothesis weakening in
Proposition 55, not its proposed separation example.  I did not inherit the
first review's verdict.  This record is ordinary mathematics; it supplies no
Lean, adapter, consumer-integration, or novelty seal.

## Verdict

**Proposition 54 is VALID ordinary mathematics.**  I found no endpoint,
measure, reindexing, collision, positive-survival, target, or unrestricted-
deviation counterexample.  The two genuinely new joints check:

1. a continuous zero-perfect path on the production-normal subtype lifts to
   an ambient zero-perfect path because every omitted player has zero rate and
   Simon's abnormal-player inequality gives the required lower Continue
   inequality; and
2. the logarithmic product discretization is globally close to the continuum
   **opponent-deleted** first-event law uniformly over every forced quit time
   and Never, including a positive survival atom.

**Proposition 55's weakening also checks.**  After the subtype path is
constructed, no later step uses ambient projective Q-bar.  It is enough to
assume projective Q-bar for the normalized singleton matrix restricted to the
production-normal subtype.

The exact honesty boundary remains important.  The subtype reward/reindexing
adapter and the equality between the Literature `MinMaxQuit` and production
`quittingPunishmentValue` are proved here only as ordinary semantic
identifications, not by named checked declarations.  Proposition 51's
Stieltjes/logarithmic decoder is likewise ordinary mathematics, not a checked
source adapter.  Thus the conclusion is not currently proved in Lean or
integrated merely because its consumers are checked.

## 1. Normal subtype and ambient lift

Off `IsQuittingZeroSolo reward`, some player `j` has `s_j>0`.  The checked
bound

```text
quittingPunishmentValue reward j <= max(s_j,0)=s_j
```

makes `j` production-normal, so the subtype `N` is nonempty.  Restricting the
reward table to `N` preserves every singleton entry and every own singleton
baseline.  Therefore its normalized singleton matrix is exactly the
principal restriction of the ambient matrix, after the evident finite-subtype
reindexing.

For Proposition 54, every nonempty principal subset of `N` maps to a nonempty
principal subset of the ambient player set.  Applying ambient projective
Q-bar there and reindexing gives projective Q for the subtype subset.  This
proves the claimed subtype Q-bar assertion.  Proposition 55 may simply assume
that assertion at the outset; the rest of the proof never calls the ambient
matrix predicate.

The checked theorem
`exists_continuous_zeroPerfect_of_projectiveQBar`
(`UniformEquilibrium/Quitting/AbsorptionPath/PrincipalQContinuousPath.lean`)
then supplies the continuous singleton path on `N`.  Embed its singleton
masses in the ambient player set and give every omitted player zero mass.
For `i in N`, the path payoff and both perfection inequalities are unchanged.

For omitted `k`, production abnormality is the strict negation

```text
s_k < quittingPunishmentValue reward k.
```

On the unique live history, a production behavior profile is exactly a
sequence of product quitting rows, and a unilateral behavior is exactly the
player's hazard sequence.  Both terminal conventions pay zero on Never.
Consequently Simon's `MinMaxQuit` and the production punishment value have the
same infimum-over-opponent-plans/supremum-over-replies semantics.  Applying
the proved `lemma3` in `Literature/Simon2007.lean` gives, for every normal
owner `j`,

```text
reward({j})_k >= chi_k > s_k.
```

Every residual continuation distribution of the subtype path is a probability
mixture of these singleton rows.  Hence its omitted coordinate is strictly
above `s_k` at every `t<1`.  This is precisely the lower sequential-perfection
clause.  The upper/equality clause is conditional on positive lower-right
derivative of `k`'s singleton mass and is vacuous because that mass is
identically zero.  There is no hidden ambient upper condition.

## 2. Continuum transversality dispatch

In logarithmic time, an omitted player has rate `a_k=0` almost everywhere, so
its deleted survival is `exp(-T)` and vanishes.  Thus any player with positive
deleted-survival limit belongs to `N`.  Proposition 53's Snell identity says
that finite pure quit times are weakly unprofitable and that the only possible
profitable Never deviation comes from one exceptional owner `i` with

```text
R_i(infinity)>0,
s_i<0,
reward({i})_k>=s_k for every k.
```

This owner is normal by the subtype construction.  These are exactly the raw
row inequalities consumed by the already independently audited Proposition
48, so the harmful transversality branch is stationarily generated.  The
checked generated-branch approximate-equilibrium and fixed-payoff consumers
then close it.  In the complementary branch, every continuum finite pure time
and Never is bounded by `gamma_i(0)`; positive deleted survival is allowed and
is harmless when the displayed terminal product is nonnegative.

I separately rechecked the positive-survival boundary in Proposition 53.
If `R_i(infinity)>0`, the total opponent rate is integrable, the remaining
opponent-first mass after `T` tends to zero, and the residual conditional law
converges to owner `i`'s singleton row.  If two distinct players had positive
deleted survival, both complementary rate sums would be finite, contradicting
`sum_j a_j=1` over an infinite logarithmic interval.  No limit mass is silently
discarded.

## 3. Global deleted-law comparison

Fix player `i`.  In block `k`, let

```text
H_k=sum_(j!=i) A_(k,j),
Q_k=exp(-sum_(ell<k) H_ell).
```

Deleting `i` gives this same block-start survival in the continuum and product
models.  Conditional on block entry, the continuum singleton-`j` mass is

```text
integral_block exp(-opponent rate accumulated before u)*a_j(u) du,
```

and therefore lies in `[exp(-H_k)A_(k,j),A_(k,j)]`.  The product unique-`j`
mass is exactly

```text
exp(-H_k)*(exp(A_(k,j))-1),
```

which lies in the same interval.  Summing coordinatewise interval widths gives

```text
singleton L1 error <= H_k*(1-exp(-H_k)).
```

The product collision mass is at most `H_k^2/2`.  Since `0<=H_k<=h`,

```text
H_k^2/2 <= (h*exp(h)/2)*(1-exp(-H_k)).
```

Finally

```text
sum_k Q_k*(1-exp(-H_k))=1-R_i(infinity).
```

This equality remains valid when `R_i(infinity)>0`; the common survival atom
has the same mass in both laws and payoff zero.  Weighting the block errors and
summing therefore proves the global full-outcome bound

```text
L(h)=h+h*exp(h)/2.
```

No unweighted per-row error is accumulated.

## 4. Forced row, target, and arbitrary behavior

If `i` is forced to quit in discrete row `n`, the law of earlier opponent
absorption differs from its continuum counterpart by at most `L(h)` in L1.
At row `n`, the discrete opponents collide with `i` with probability at most
`1-exp(-H_n)<=h`; replacing that collision payoff by the continuum solo payoff
costs at most `2Mh`.  Therefore, uniformly in `n`,

```text
discretePureQuit_i(n)
 <= continuumPureQuit_i(nh)+M*L(h)+2Mh
 <= gamma_i(0)+M*h*(3+exp(h)/2).
```

For Never, the common positive-survival atom is explicitly retained and the
last collision term is absent.  Proposition 51's complete-law estimate gives
the prescribed profile payoff within

```text
E(h)=M*(h+h^2/(2*(1-exp(-h))))
```

of the same fixed `gamma(0)`, with `E(h)->0`.  Thus every deterministic quit
time, including Never, gains at most `F(h)+E(h)`, uniformly over the time
chosen after the profile is fixed.

The exact declaration
`sSup_range_quittingTerminalPayoff_update_eq_pureTime`
(`UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean`)
then covers every unilateral behavioral deviation, not merely one-shot or
stationary deviations.  The target `gamma(0)` is fixed before the accuracy;
only `h` and the product profile vary.  The checked consumer
`quittingGame_isUniformEquilibriumPayoff_of_terminalNash_all_errors_approxTarget`
(`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalTargetSemantics.lean`)
has exactly these quantifiers.

## 5. Proposition 51 dependency and boundary tests

The portion of Proposition 51 used here also survived a focused check.
Coordinate monotonicity and total mass `t` make every coalition coordinate
one-Lipschitz.  A nonsingleton coordinate has lower-right derivative zero at
every interior time; at ordinary differentiability points this is its usual
derivative, so absolute continuity and the zero initial value make it
identically zero.  For a singleton coordinate, positive density implies
positive lower-right derivative at almost every such point, and sequential
perfection forces `gamma_i=s_i` on the Stieltjes support.  The logarithmic
change of variables then gives nonnegative rates summing to one almost
everywhere.  The geometric block-survival sum produces a tail-law error
uniform in the starting block.  This is enough for the use in Proposition 54.

Boundary falsifiers behave as the note claims:

- a negative-solo one-player path is caught by the initial zero-solo branch;
- an omitted abnormal player has no upper support condition because its rate
  is zero;
- a positive-survival normal owner either has harmless nonnegative terminal
  product or enters the reviewed generated branch; and
- forced discrete collisions are exactly the separate `2Mh` term.

## 6. Scope

This validates the ordinary implication

```text
IsProjectiveQBarMatrix(normalizedSoloMatrix reward)
  -> existence of a uniform-equilibrium payoff,
```

and the weaker production-normal-subtype hypothesis in Proposition 55.  It
does not prove the full finite-quitting conjecture, a residual-hard producer,
or the source theorem in Lean.  It also does not establish that Proposition
55 is strictly weaker on an explicit game; only the proof's lack of ambient
matrix use is validated.

## 7. Post-formalization re-audit of the continuous-rate source obligation

I re-audited the export after the formalizer isolated
`QuittingPunishmentNormalPathDecoder` as the remaining hypothesis in
`ProjectiveQBarBehavioralDecoder.lean`.  **This exposes unfinished Lean work,
not a new mathematical gap in the exported proof.**  The export states enough
data and proves the continuous-rate laws at ordinary-mathematics level:

1. the checked producer now exposes a
   `ContinuousZeroPerfectSingletonPath`, whose coordinate paths are monotone,
   whose total singleton mass is exactly `t`, and whose sequential-perfection
   inequalities hold at every clock time;
2. nonnegativity and the identity `sum_i pi_i(t)=t` make every `pi_i`
   one-Lipschitz and absolutely continuous, so logarithmic rates `a_i` exist
   almost everywhere and satisfy `a_i>=0` and `sum_i a_i=1` almost everywhere;
3. at almost every point with `a_i>0`, ordinary differentiability identifies
   the lower-right derivative with the positive density, so zero perfection
   gives `gamma_i=s_i`; this is precisely the support fact needed in the
   deleted-clock product rule;
4. the definition of `absorptionPathPayoff`, total mass `t`, and terminal mass
   one give the displayed integral law for `gamma`; the product rule then
   gives the finite Snell identity with the residual term `R_i(T)gamma_i(T)`;
5. the block hazards are integrals of those rates, so their sums are exactly
   `h`.  The full-law and opponent-deleted-law estimates use only the explicit
   one-block interval bounds, collision bound, and the survival telescope.
   They retain the positive Never atom and add the forced-row collision term,
   exactly as required by the pure-time semantic consumer.

The current Lean decomposition honestly stops before items 2--5 are assembled
from an arbitrary path witness: `LogarithmicBlockDiscretization.lean` checks
the finite exponential, collision, and survival-telescope estimates, while
`ProjectiveQBarBehavioralDecoder.lean` checks the fixed-target pure-time
consumer conditional on `QuittingPunishmentNormalPathDecoder`.  A static
source audit does not establish integration of that latter file.  The missing
theorem is therefore the advertised continuous-density/Snell/semantic-law
**producer**, not an unstated assumption needed by the ordinary proof.

I also retried the two likely failure points.  A positive density cannot hide
from `pathRightDerivative`: at an ordinary differentiability point the right
difference quotients converge to that density.  A positive deleted-survival
atom is not dropped: it has identical mass in the continuum and product laws,
and payoff zero under Never.  I found no counterexample to either step.
