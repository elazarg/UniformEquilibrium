# Review of `CODEX_EULER__FIN4_QUANTILE_CENTER_OUTER_PROTOTYPE`

## Verdict

**REVISE.**  The probability formulas, direct exact evaluator, stated exact
regressions, literal finite-clock interpretation, and the all-Never lower-bound
obstruction are mathematically correct.  The current JSON output is not yet a
closed exact polynomial system, however.  Two missing algebraic links and one
endpoint qualification must be repaired before the note can call the full
output an exact rational polynomial-system description.

This is an internal Research prototype, not an export candidate.  The random
search failures play no role in this verdict.

## Claim reviewed

For a normalized four-player quitting table, the script is claimed to:

1. parametrize the literal actual finite-clock set `A_K` by four independent
   stopping-law marginal simplexes on dates `0,...,K-1` and `Never`;
2. compute the prescribed terminal payoff and unrestricted behavioral cap
   exactly from finitely many pure-time candidates;
3. emit a rational semialgebraic presentation of `A_K`, the finite outer set
   `R_M`, and the graph of terminal exploitability;
4. validate the listed exact regressions; and
5. prove `L_M=0` for every normalized Fin4 table when `M<=24`, with the sharper
   family bound `M<=floor(96/lambda)`.

I inspected:

- `experiments/fin4_quantile_center_prototype.py`;
- `notes/CODEX_EULER__FIN4_QUANTILE_CENTER_OUTER_PROTOTYPE.md`;
- `Research/Quitting/EscapeAwareQuantileClockHierarchy.lean`;
- `MathUE/Topology/NestedOuterApproximation.lean`;
- `UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean`;
- `UniformEquilibrium/Quitting/Examples/SolanVieilleBoundaryTable.lean`;
- `UniformEquilibrium/Quitting/Examples/BlockPair/FourPlayerPairedSingleton.lean`;
- `UniformEquilibrium/Quitting/Examples/BlockPair/FourPlayerPairedSingletonPeriodTwo.lean`.

I also ran `self-test`, the exact boundary witness through `M=96`, the
`lambda=3/4` witness through `M=128`, the period-two truncation through `K=64`,
and inspected the full `K=1` constraint and `M=1` outer JSON.

## Mathematical checks that pass

### 1. Literal stopping-law and product semantics

The marginal simplex has exactly the right meaning.  A coordinate `x[i,t]`
is the complete stopping-law mass at finite date `t<K`, and `x[i,N]` is the
literal `Never` atom.  Independence makes the first-quitting-coalition mass

\[
 \sum_{t<K}\prod_{i\in S}x_{i,t}
   \prod_{j\notin S}\Pr(T_j>t),
\]

and the code uses `surv[j][t+1]`, so ties and strict survival have the correct
orientation.  Omitting the all-Never term from `U` is correct because the
nonabsorbing payoff is zero.

This is genuinely the literal reachable set, not a closure.  In
`EscapeAwareQuantileClockHierarchy.lean`,
`quittingFiniteClockSemanticReachable reward K` uses laws whose positive finite
support lies at times `<K`; the script uses exactly `0,...,K-1`.  The checked
range-fold and compactness theorems justify the note's literal-`A_K` and
attained-upper-center statements.

### 2. Full unrestricted cap

For a fixed player, the supported-date formulas correctly add:

- earlier opponent absorption without the deviator;
- the tied first coalition at the chosen date; and
- the deviator's solo row when every opponent survives strictly past it.

At the auxiliary date `K`, all earlier finite opponent outcomes are retained
and the all-opponents-Never event pays the solo row.  At `Never`, the same
finite opponent outcomes are retained and the all-Never event pays zero.
Every later finite date equals the auxiliary date because opponents have no
finite mass at or after `K`.  Thus the finite list

\[
 0,\ldots,K-1,\quad K\text{ (after support)},\quad Never
\]

contains every distinct pure-time value.  The checked theorem
`sSup_range_quittingTerminalPayoff_update_eq_pureTime` then identifies its
maximum with the cap against arbitrary behavioral deviations.  Zero survival
and exact Never require no extra case.

The emitted prescribed and deviation RHS polynomials agree exactly with the
direct evaluator on the rational regression profile.  The all-Never,
after-support/Never, late tie, known equilibrium, mass-ledger, and rational
period-two truncation outputs reproduce the values printed in the note.

### 3. All-Never diagonal obstruction

Let rewards lie in `[-1,1]`.  At the literal all-Never center,

\[
 U_i=0,\qquad B_i=b_i=\max(0,r_i(\{i\}))\in[0,1].
\]

The diagonal point `z_U=z_B=b/2` has objective zero and sup-distance at most
`1/2` from that one center.  For every `m<=M<=24`, `12/m>=1/2`; the same
literal center therefore witnesses every level in `R_M`.  Since the objective
is nonnegative, `L_M=0`.  This proof is exact and does not depend on the
floating search.

For the interpolation family, `b_i=lambda/4`, so the distance is
`lambda/8`.  For `lambda>0`, the exact condition is

\[
 m\le 96/\lambda,
\]

giving the claimed integer bound.  The endpoint `lambda=0` has distance zero
and works at every level.  The commands return the exact `1/8` witness through
`M=96` at `lambda=1` and the exact `3/32` witness through `M=128` at
`lambda=3/4`.

The graph formula itself is mathematically valid: after imposing
`F>=0` and `F>=z_Bi-z_Ui`, all factors in
`F*product_i(F-(z_Bi-z_Ui))` are nonnegative, so product zero forces `F` to be
the maximum of those five quantities.

## Required repairs

### A. The cap-max product refers to undeclared `V` symbols

`exact_polynomial_system` lists only the marginal, `U`, and `B` variables.
Its cap inequalities contain the actual polynomial RHSs, but its tightness
record contains factors such as `B0-V0_after`.  No `V0_after` variable is
declared and no equality identifies it with the corresponding RHS polynomial.
Read literally as a polynomial system, the record therefore does not impose
that `B_i` equals one of the deviation polynomials.

Repair in either of two equivalent ways:

- declare every `V_i,label` and emit `V_i,label = <RHS polynomial>`, or
- emit each tight-product factor directly as `B_i - <RHS polynomial>`.

The direct evaluator remains correct; this defect concerns the generated
certificate system.

### B. Multi-level center namespaces are metadata only

`outer_hierarchy_system` attaches a field `namespace: m1`, `m2`, and so on,
but the nested `A_K_exact_system` continues to declare unprefixed variables
`x0_0`, `U0`, `B0`, etc.  Conversely, the distance inequalities refer to
`m1_U0`, `m1_B0`, etc., which are not declared by that center system.  For
`M>1`, the center variables also collide across levels.  Thus the current full
JSON does not literally encode `R_M`.

Repair by applying the namespace prefix to every center variable and every
occurrence in monomials, equalities, inequalities, and tight-product factors,
or by emitting a structured local-variable binding that a documented consumer
actually resolves.  The shared outer variables should also explicitly include
`F`, and the objective tight polynomial should be emitted with the four
concrete coordinate factors rather than only the schematic text containing
`i`.

### C. Qualify the `lambda=0` endpoint

Formula (3.2) writes `floor(96/lambda)` while the family is declared for
`0<=lambda<=1`.  Division by zero is undefined.  State (3.2) for
`0<lambda<=1`, and state separately that `lambda=0` gives a zero-distance
all-Never witness at every level.  The script already reflects this by
returning `null` as the finite largest certified level when the distance is
zero.

## Exact/floating and research disposition

The note correctly labels stochastic outputs and rationalized candidates as
upper witnesses only.  I assign no evidentiary value to the failure of random
search to find a positive signal.  The exact evaluator, finite-center
semantics, and all-Never obstruction are useful internal algorithm-design
facts: in particular, they show that the exported quantitative radii make
early outer levels provably uninformative.  After repairs A--C, the prototype
would be a sound exact constraint generator suitable for a later RCF or
certified branch-and-bound layer.  It presently supplies neither such a lower
certificate nor a conjecture-facing consumer, so it should remain internal.
## Delta verification after the generator repairs

**Final verdict: PASS.**  The repaired generator now declares the payoff
variables used by the deviation equations, emits disjoint recursive literal
namespaces, declares the exploitability variable with five concrete product
factors, and treats `lambda = 0` separately.  The self-test and full `M = 2`
namespace closure pass.

The new exact Proposition 3.2 is also correct.  If an actual center
`a ∈ A_K`, `K ≤ 9`, has exploitability `f > 0`, then it embeds in every
`A_(8m+1)`, its diagonal midpoint is at distance exactly `f/2`, and therefore
lies in the outer tube whenever `m ≤ M ≤ floor (24/f)`.  Thus `L_M = 0` on
that range.  For the stored rational `K = 4` center at `lambda = 3/4`,

```text
f = 2868660135241342669 / 320000000000000000000,
floor (24/f) = 2677.
```

The exact checks at `M = 129` and `M = 2677` succeed, while the same center
fails the required distance inequality at `M = 2678`.  The note correctly
calls `2678` only the first level not covered by this explicit center, not a
positive lower certificate.  The internal-Research/no-export assessment is
unchanged.
