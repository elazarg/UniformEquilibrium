# Fin4 quantile-center and outer-hierarchy prototype

## Status

**Executable exact evaluator/constraint generator plus floating experiment.**
No numerical output is a lower certificate.  The prototype is
[`fin4_quantile_center_prototype.py`](../experiments/fin4_quantile_center_prototype.py).
It uses only the Python standard library.

The finite-clock center in the prototype is the **literal actual set**
`A_K`, not its closure.  Current checked code proves that this set is compact
and that every bounded complete stopping-law profile is reconstructed by a
finite product-root word followed by an exact all-Continue suffix, preserving
Never mass, the full terminal semantic pair, and unrestricted caps.  Thus the
upper problem has an actual finite-clock minimizer.  The floating layer merely
searches for that minimizer; it does not replace `A_K` by a closure.

The exact layer passes all current regressions.  The calibrated paired-
singleton scan found no positive outer lower signal.  It instead exposed an
exact obstruction to searching the first hierarchy levels: for every
normalized Fin4 table, `L_M=0` for all `M<=24`; on the normalized boundary
table the literal all-Never center proves `L_M=0` through `M=96`.

**Independent review: final PASS after the requested generator repairs.**  See
[`feedback/CODEX_EULER__FIN4_QUANTILE_CENTER_OUTER_PROTOTYPE__BY_CODEX_RAMSEY.md`](../feedback/CODEX_EULER__FIN4_QUANTILE_CENTER_OUTER_PROTOTYPE__BY_CODEX_RAMSEY.md).
Miner independently reviewed Proposition 3.2 and its exact cutoff **PASS** in
[`feedback/CODEX_EULER__FIN4_QUANTILE_CENTER_OUTER_PROTOTYPE__BY_CODEX_MINER.md`](../feedback/CODEX_EULER__FIN4_QUANTILE_CENTER_OUTER_PROTOTYPE__BY_CODEX_MINER.md).

## 1. Implemented mathematical object

For `K` finite dates, each player has marginal variables

\[
 x_{i,0},\ldots,x_{i,K-1},x_{i,N}\ge0,
 \qquad \sum_t x_{i,t}=1.                              \tag{1.1}
\]

The exact layer generates the product-coalition polynomial

\[
 p_x(S)=\sum_{t<K}
    \prod_{i\in S}x_{i,t}
    \prod_{j\notin S}\left(\sum_{u>t}x_{j,u}+x_{j,N}\right),
 \qquad
 U_i=\sum_{S\ne\varnothing}p_x(S)r_i(S).              \tag{1.2}
\]

For each player it independently generates every pure-time deviation
polynomial at

\[
 0,\ldots,K-1,\quad K\text{ (strictly after support)},\quad N. \tag{1.3}
\]

The after-support polynomial includes the solo row when every opponent is
Never.  The Never polynomial instead assigns zero on that event.  Every
candidate is declared as `V_(i,tau)` and linked to its exact polynomial by an
equality.  The cap constraints are emitted as

\[
 B_i\ge V_{i,\tau}\quad(\forall\tau),
 \qquad
 \prod_\tau(B_i-V_{i,\tau})=0.                         \tag{1.4}
\]

Thus the generated cap is the exact finite maximum.  The checked theorem
`sSup_range_quittingTerminalPayoff_update_eq_pureTime` upgrades it to every
behavioral deviation.

The script also generates the extended outer system

\[
 R_M=\bigcap_{m=1}^M
 \{z:\exists a_m\in A_{8m+1},\ \|z-a_m\|_\infty\le12/m\}, \tag{1.5}
\]

including literally prefixed declarations and occurrences for every product
center, all distance inequalities, a declared shared variable `F`, and the
five concrete factors in the finite graph of

\[
 F(z)=\max(0,\max_i(z_{B_i}-z_{U_i})).                 \tag{1.6}
\]

Commands:

```text
python3 experiments/fin4_quantile_center_prototype.py self-test
python3 experiments/fin4_quantile_center_prototype.py dump-constraints 2 --full --lambda-value 1
python3 experiments/fin4_quantile_center_prototype.py dump-outer 1 --full --lambda-value 1
```

The full JSON is a closed exact rational polynomial-system description.  It is not
an RCF proof trace.  No CAD/SMT package is installed in the conference
environment, so exact global infeasibility verification remains a separate
layer.

## 2. Exact regression suite

`self-test` performs all calculations with `fractions.Fraction`.

### All-Never

On the normalized Solan--Vieille boundary table,

\[
 U=(0,0,0,0),\qquad B=(1/4,1/4,1/4,1/4).              \tag{2.1}
\]

The evaluator returns these values exactly.

### After-support versus Never

Against all-Never opponents, a player quitting at the auxiliary date `K`
gets its solo payoff `1/4`, whereas deviating to Never gets zero.  The
generated polynomials and direct evaluator both return

\[
 V_{i,K}=1/4,qquad V_{i,N}=0.                          \tag{2.2}
\]

### Late literal tie

With players `0,2` quitting at date two and players `1,3` Never, the prescribed
payoff is exactly the row of coalition `{0,2}`:

\[
 U=(1/4,1/4,1/4,0).                                    \tag{2.3}
\]

This checks that chronological location does not erase ties.

### Known exact equilibrium

At the stationary paired-singleton completion divided by four, player `0`
quitting immediately while all others Never has

\[
 U=B=(0,3/4,-1/4,-1/4),\qquad F=0.                    \tag{2.4}
\]

This matches the checked unrestricted terminal-Nash theorem for the unscaled
table.

### Product mass and generated formulas

On a nontrivial rational two-date profile, the fifteen first-coalition masses
plus all-Never mass sum exactly to one.  Every emitted `U_i` polynomial and
every emitted supported/after-support/Never `V_(i,tau)` polynomial evaluates
exactly to the direct stopping-law calculation.

## 3. Exact small-level outer obstruction

### Proposition 3.1

For every normalized Fin4 reward table,

\[
 L_M=0\qquad\text{for every }M\le24.                   \tag{3.1}
\]

#### Proof

Use the all-Never center in every `A_(8m+1)`.  Its semantic pair is

\[
 U_i=0,qquad B_i=b_i:=\max(0,r_i(\{i\}))\in[0,1].
\]

Let the common outer point have

\[
 z_{U_i}=z_{B_i}=b_i/2.
\]

Then `F(z)=0` and its sup distance from the all-Never center is at most
`1/2`.  For `m<=M<=24`, `12/m>=1/2`, so the same center witnesses every
neighborhood constraint.  Hence `z in R_M` and the nonnegative minimum is
zero.  QED.

This is not a numerical failure.  It proves that the exported constants make
the first 24 outer levels universally incapable of returning a positive
certificate.

For the interpolation family below and `0<lambda<=1`, the own-solo payoff is
`lambda/4`, so the same construction has distance `lambda/8` and proves

\[
 L_M=0\quad\text{through }M\le\lfloor96/\lambda\rfloor. \tag{3.2}
\]

At `lambda=0` the distance is zero, so the same all-Never center certifies
`L_M=0` at every level; no division by `lambda` is used.

The executable exact command

```text
python3 experiments/fin4_quantile_center_prototype.py outer-zero-witness --lambda-value 1 --M 96
```

returns the boundary-table witness `z_U=z_B=(1/8,...,1/8)`.  At
`lambda=3/4`, it verifies zero through `M=128` with diagonal value `3/32`.

### Proposition 3.2: exact post-all-Never zero certificate

Let `a in A_K` be an actual finite-clock center with `K<=9`, and put
`f=F(a)`.  If `f>0`, then

\[
 L_M=0\qquad\text{for every }M\le\lfloor24/f\rfloor.   \tag{3.3}
\]

Indeed, insert zero-mass finite dates before Never to regard the same literal
profile as a point of every `A_(8m+1)`.  The coordinatewise midpoint

\[
 z_{U_i}=z_{B_i}={a_{U_i}+a_{B_i}\over2}
\]

has `F(z)=0` and distance `f/2` from `a`.  Since `12/m>=f/2` for every
`m<=M`, that one actual center witnesses every constraint defining `R_M`.
For `f=0` it works at every level.

For `lambda=3/4`, the all-Never certificate first fails at the exact level
`M=129`.  The stored rational four-date profile has

\[
 f={2868660135241342669\over320000000000000000000}
   \mathrel{\approx}0.0089645629.                       \tag{3.4}
\]

Its exact midpoint therefore certifies `L_129=0`, and in fact certifies
`L_M=0` through `M=2677`.  This is an exact feasible point of the literal
outer system, not a numerical inference.  The certificate verifier substitutes
the rational marginals back into every emitted prescribed-payoff and declared
deviation-value polynomial, checks all cap inequalities and tightness, and then
checks the exact outer distance.  The executable certificate, which prints
every marginal and every semantic coordinate, is

```text
python3 experiments/fin4_quantile_center_prototype.py \
  profile-zero-witness --preset lambda34-k4 --M 129
```

Thus `M=129` is the first level not covered by the all-Never diagonal for this
family, but it is **not** a nonzero lower-certificate level.  After the stored
actual center is taken into account, the first level not covered by an explicit
exact rational zero witness is `M=2678`.

## 4. Calibrated paired-singleton family

The searched rational family is

\[
 r^\lambda={1\over4}\bigl((1-\lambda)r^{\rm stat}
                    +\lambda r^{\rm bdry}\bigr),
 \qquad 0\le\lambda\le1.                              \tag{4.1}
\]

Here `r^stat` is the checked stationary paired-singleton completion and
`r^bdry` the checked Solan--Vieille period-two completion.  Every reward lies
in `[-1,1]`.  The interpolation retains the same normalized paired-singleton
solo comparison matrix up to the common positive scale `1/4`, so this is a
calibrated residual-hard singleton family.  I do not claim a new checked Lean
adapter saying that every interpolated completion inhabits the full residual
structure.

There is an exact pure-profile screen.  Player `0` quitting immediately and
everyone else Never is terminal Nash precisely through the cross-pair join
inequality

\[
 {-2+3\lambda\over4}\le{-1+\lambda\over4},
\]

which is equivalent to `lambda<=1/2`; the same inequality applies to player
`3`, while the partner inequality is automatic.  Thus the exact zeros found
at `lambda=0,1/4,1/2` are expected and are not solver artifacts.

## 5. Floating search and rational upper witnesses

The floating layer uses seeded random simplex starts, mixture moves, annealed
acceptance, vertex polishing, and exact warm-start embedding
`A_K subset A_(K+1)`.  It minimizes the actual finite-clock exploitability
`F(U(x),B(x))`.  It supplies upper witnesses only.

Representative search:

```text
python3 experiments/fin4_quantile_center_prototype.py scan \
  --max-k 4 --lambda-steps 4 --restarts 14 --steps 2200 --seed 20260826
```

Independent random runs varied materially, confirming that these are local
upper searches rather than estimates of `U_K`.  A seeded run followed by
denominator-`100000` rationalization produced the stored `lambda=3/4`
certificate in Proposition 3.2.  Representative exact rationalized `K=4`
upper witnesses are:

| `lambda` | exact exploitability | decimal |
|---|---:|---:|
| `3/4` | `2868660135241342669 / 320000000000000000000` | `0.0089645629` |
| `1` | `87214890329273 / 10000000000000000` | `0.0087214890` |

These values were re-evaluated by the Fraction layer against all supported
dates, after-support, and Never.  They are exact **upper** witnesses, not dual
or lower certificates.

As a second calibration, the script truncates the checked period-two boundary
profile using the rational approximation

\[
 a={672771\over901720},
 \qquad
 b={4a^2-1\over3a^2};                                  \tag{5.1}
\]

the selecting quartic residual is about `-6.77e-12`.  All remaining survival
mass is placed on exact Never.  Fraction evaluation gives:

| `K` | exact-witness exploitability (decimal) |
|---:|---:|
| 1 | `1.86524e-1` |
| 2 | `1.02220e-1` |
| 4 | `3.07003e-2` |
| 8 | `2.76918e-3` |
| 16 | `2.25305e-5` |
| 32 | `1.49154e-9` |
| 64 | `1.64423e-13` |

The exact fractions are intentionally left to executable output because they
grow very large.  This regression confirms the expected finite-clock escape
toward the checked period-two uniform equilibrium.

## 6. Search verdict

No positive `L_M` signal or candidate dual certificate was found.

- The exact all-Never construction forces zero outer minima through levels
  far beyond the feasible full-symbolic prototype range for this family.
- The endpoint `lambda=1` has a checked uniform payoff, and its rational
  periodic truncations rapidly produce small actual exploitability.
- The interior `lambda=3/4` likewise produced small rational actual witnesses.
- A local failure to find a lower profile would not certify a positive outer
  minimum in any event.

The first level not universally killed by the all-Never proof is `M=25`,
already involving centers through `K=201`.  Proposition 3.2 shows why this is
only a necessary screen: any one small actual center with exploitability `f`
kills every level through `floor(24/f)`.  For the displayed `lambda=3/4`
family this pushes the first currently unblocked level to `M=2678`, with a
largest center clock bound `K=21425`.  This is the concrete computational
bottleneck exposed by the prototype.

## 7. Exact/floating boundary and next test

Proved/exact in this note:

- generated product payoff and full pure-time cap polynomials;
- a closed, collision-free namespaced outer system with declared deviation
  values and objective graph;
- exact evaluation of rational profiles;
- the five regression families above;
- Proposition 3.1 and the family-specific all-Never outer witnesses;
- Proposition 3.2 and the exact `lambda=3/4`, `M=129` zero certificate;
- rational finite-clock upper profiles and their exact exploitabilities.

Experimental only:

- stochastic minimization over marginal simplexes;
- any impression of the true finite-center optimum from a search run;
- the absence of a positive signal in unverified global optimization.

The next bounded algorithmic test is not a larger random scan.  It is an exact
RCF or certified branch-and-bound feasibility check for

\[
 R_M\cap\{F=0\}
\]

at the first level not already killed by an explicit rational zero witness,
using symmetry reduction of the chosen family.  Until such a check produces
an infeasibility trace, there is no lower certificate or conjecture-facing
claim.

## 8. Checked source correspondence

The current formalized finite-clock interface is
`Research/Quitting/EscapeAwareQuantileClockHierarchy.lean`.  In particular:

- `quittingFiniteClockSemanticReachable` is the set modeled by the generated
  marginal system;
- `quittingFiniteClockSemanticReachable_eq_range_fold` reconstructs each
  bounded stopping-law semantic pair from a finite product-root word with an
  exact all-Continue suffix;
- `quittingTerminalSemanticPair_finiteClockWordProfile_eq_fold` identifies
  the recursive finite word with its literal behavioral profile;
- `quittingFiniteClockWordProfile_stoppingLaw_isFinite` retains the exact
  Never atom and excludes later finite mass;
- `quittingFiniteClockSemanticReachable_isCompact` proves that the literal
  reachable set, rather than a closure, is compact; and
- `exists_finiteClockSemanticPair_exploitability_eq_upper` proves attainment
  of the finite-clock upper value at an actual finite-clock semantic pair.

The same file still isolates the common-quantile approximation rate as the
named input `HasEscapeAwareQuantileClockCompression`; the exact prototype
does not pretend to verify that analytic theorem or an RCF infeasibility
certificate.  Exact unrestricted cap reduction uses
`sSup_range_quittingTerminalPayoff_update_eq_pureTime` from
`UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean`.
