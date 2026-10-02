# The unequal-high paired table has a produced three-state absorbing cycle

Author: CODEX_NOETHER_SUPPORT.

Status: computer-assisted exact ordinary-mathematics proof, not Lean-checked.
The rational interval certificate produces nine legal hazards from the literal
table below. It gives an exact terminal Nash profile and a fixed uniform
equilibrium payoff against unrestricted behavioral deviations. Independent
review is requested. The full twelve-parameter box remains open in this line.

## 1. Literal data and output

Players are 0,1,2,3. At each live date they independently Quit or Continue.
The first nonempty quitting coalition absorbs, and infinite all-Continue play
pays zero. The reward table is the following, in bit-mask order:

```text
 1: (1,4,0,0)       2: (4,1,0,0)       4: (0,0,1,4)       8: (0,0,4,1)
 3: (2,2,1,1)       5: (8/5,1,1,0)     9: (1,0,1,2)
 6: (0,1,8/5,1)    10: (1,2,0,1)      12: (1,1,2,2)
 7: (1,0,0,0)      11: (0,1,0,0)      13: (0,0,0,1)      14: (0,0,1,0)
15: (−1,−1,−1,−1).
```

Theorem. This table has an exact periodic terminal Nash profile with
chronological active sets

```text
{0,2,3} | {0,1,2} | {0,1,3}.
```

Every active hazard lies strictly between 1/100 and 1/4. Every player faces
opponent absorption greater than 1/6 at every date. All three phase-payoff
vectors belong to (1,3/2)⁴. Each is a uniform equilibrium payoff, witnessed by
the same periodic profile at every accuracy and its corresponding start phase.
There is no supplied continuation, root, invariant region, or favorable
strategic inequality among the theorem's inputs.

The phase-zero payoff has numerical locator

```text
(1.05336092, 1.45284250, 1.04033659, 1.30167833).
```

Rounded numbers are not the equilibrium or its certificate. The exact profile
is defined by the unique zero in the rational box in Section 3.

This is a new solution of this particular raw table within the current
research lane, not an assertion that this support word, a numerical root
selector, or any finite grammar covers the entire independent [1,2]¹² box.

## 2. Actual cyclic values and all twelve endpoint comparisons

Put r(∅)=0 only for the immediate-reward formulas. This leaves literal Never
equal to zero and does not modify any nonempty reward row. Let the nine
variables, in order, be

```text
x=(q00,q02,q03,q10,q11,q12,q20,q21,q23),
q0=(q00,0,q02,q03), q1=(q10,q11,q12,0), q2=(q20,q21,0,q23).
```

Indices t on phases are modulo three. For S⊆{0,1,2,3}, define

```text
p_t(S)= product_(j in S) q_tj · product_(j notin S)(1−q_tj),
G_ti = sum_(S nonempty) p_t(S) r_i(S),
c_t  = p_t(∅),                 D = 1−c0 c1 c2,
W_ti = G_ti+c_t G_(t+1),i+c_t c_(t+1) G_(t+2),i.
```

Whenever D>0 the actual prescribed terminal payoff from phase t is exactly
V_ti=W_ti/D. Indeed the numerator is one cycle's terminal contribution and
the remaining joint survival is c0 c1 c2; the geometric series accounts for
all future cycles. In particular V is not an arbitrary annotation.

For a deleted owner i, let p^−i_t(S) be the same product over the other three
players, for S⊆{0,1,2,3}\{i}. Define

```text
Q_ti = sum_S p^−i_t(S) r_i(S union {i}),
H_ti = sum_(S nonempty) p^−i_t(S) r_i(S),
d_ti = p^−i_t(∅),
F_ti = D(Q_ti−H_ti)−d_ti W_(t+1),i.                 (1)
```

Thus F_ti/D is literally Quit minus Continue with actual next-phase value.
Every possible opponent coalition occurs in these formulas. In particular a
quiet player's Quit comparison includes the grand-coalition reward when all
three prescribed active players Quit. There is no deletion of counterfactual
triple or grand outcomes based on prescribed support.

The nine active equations, in variable order, are

```text
F=(F00,F02,F03,F10,F11,F12,F20,F21,F23)=0.             (2)
```

The remaining inequalities needed are F01≤0, F13≤0, F22≤0. This accounts for
all twelve players-at-phases and both pure current actions for each one.

## 3. Reproducible rational contraction certificate

The literal center is

```text
x0=(.244039794253,.112592757902,.078794657233,
    .015262871970,.215678462758,.243253107233,
    .091437222715,.100423595701,.237451230261).
```

Interpret these decimals as exact rationals. Set ρ=1/10⁶ and
X=x0+[−ρ,ρ]⁹. The polynomial F is precisely (1)–(2). Let J0=DF(x0) and
B=J0⁻¹. The inverse is computed by exact rational Gaussian elimination and
its product with J0 is checked to be the identity; no floating-point inverse
is assumed correct.

Ordinary rational interval evaluation and forward product-rule derivatives
on X establish the following strict rational bounds:

```text
X ⊂ (1/100,1/4)⁹,
||B F(x0)||∞ < 1/10⁹,
sup_(x in X) ||Id−B DF(x)||∞ < 1/100,
||B F(x0)||∞ + ρ sup_(x in X)||Id−B DF(x)||∞ < ρ/50,

7/10 < D(X) < 4/5,
F01(X), F13(X), F22(X) < −1/6,
d_ti(X) < 5/6                    for all twelve (t,i),
1 < W_ti(X)/D(X) < 3/2           for all twelve (t,i).             (3)
```

For intervals, the displayed vector inequalities mean containment of every
entry. The norm bound uses the maximum of the sums of absolute interval
entry bounds. Distinct occurrences of a variable may be evaluated
independently; this only widens the rigorous enclosures.

Certificate and reproduction command:

```text
PYTHONDONTWRITEBYTECODE=1 python \
  experiments/CODEX_NOETHER_SUPPORT__UNEQUAL_HIGH_THREE_STATE_CERTIFICATE.py
```

The [owned certificate](../experiments/CODEX_NOETHER_SUPPORT__UNEQUAL_HIGH_THREE_STATE_CERTIFICATE.py)
contains the complete raw table, center, interval radius, equations, nine
forward derivatives, matrix verification and every comparison in (3). It
prints only and writes no files. Its only imported arithmetic routines are
`Ival` and `fraction_matrix_inverse` from the completely inspected
`Experiments/certsearch/krawczyk_cycle_certifier.py`; that module's main is
not run. The new four-player polynomial evaluator is literal enumeration of
all sixteen coalitions, not that module's three-player specialized evaluator.

As diagnostics only, the residual correction and interval operator bound are
approximately 4.17×10⁻¹³ and 0.000461017. The three quiet numerator enclosures
are contained respectively in

```text
(−.183540,−.183498), (−.226026,−.225988), (−.190868,−.190828).
```

Only the rational comparisons (3) enter the proof.

### Why (3) produces an exact zero

Set T(x)=x−BF(x). Its derivative has maximum-row-sum norm below 1/100
throughout the convex cube X. The integral mean-value formula and (3) give
T(X)⊂x0+[−ρ/50,ρ/50]⁹⊂X. Iterating T from x0 stays in X; consecutive
distances shrink by the factor 1/100. The geometric-series estimate makes
the sequence Cauchy. Its limit x* belongs to X and satisfies T(x*)=x* by
continuity. Invertibility of B then gives F(x*)=0. The same contraction
estimate proves uniqueness in X.

This is an elementary contraction proof; no numerical convergence theorem,
uncertified Krawczyk assertion, or global root count is needed. It produces
the rates rather than requiring a solution of (2) as input.

The interval bounds now imply all rates are legal, D>0, every active player
is indifferent, and every inactive player strictly prefers Continue.
The actual V satisfies its Bellman recursion by Section 2. We have therefore
produced an exact three-state Nash–Bellman cycle in the bounded set (1,3/2)⁴,
with the uniform opponent-absorption bound in (3).

We do not assert that the entire cube (1,3/2)⁴ is invariant. The produced
finite invariant value set is {V0,V1,V2}, with V_t an exact predecessor of
V_(t+1) via q_t. Its existence is the consequence of the raw-table calculation.

## 4. Complete original terminal caps, including Never

Every hazard is strictly less than one. Hence exact root Nash and Bellman
recursion imply, for every owner and every phase,

```text
V_ti = H_ti+d_ti V_(t+1),i,       Q_ti ≤ V_ti.         (4)
```

For an active owner the second inequality is equality. For a quiet owner it
is strict. Every owner is active somewhere in the word.

Fix an owner, initial phase, and any deterministic planned quitting date n.
Iterating the Continue identity (4) to date n and then using Q≤V bounds
the actual payoff of this deviation by its original V. This includes every
late date, not merely the first cycle. The accumulated opponent survival is
at most (5/6)ⁿ, regardless of the deviator's own choices.

For Never, iteration of (4) followed by n→∞ gives exactly the same V:
the residual opponent survival times the bounded continuation tends to zero.
Thus Never is an actual best response for every player at every phase. It
does not pay zero: the other three independent clocks absorb almost surely.

Every unrestricted behavioral deviation has its usual independent planned
stopping-time law along the unique live history, with a possible Never atom.
Conditioning on that law expresses its terminal payoff as a mixture of the
pure-date and Never payoffs just bounded. Therefore the unrestricted cap
equals V, and every player's full terminal regret is exactly zero.

This also gives uniform payoff convergence against all deviations. Under any
unilateral deviation the terminal time is bounded above by the opponents'
first stopping date, whose tail is uniformly geometric by (3). Its expected
time is uniformly finite, rewards have absolute value at most 4, and hence
the terminal/finite-average discrepancy tends to zero uniformly over every
behavioral deviation. The same periodic profile witnesses the fixed payoff
at every accuracy for sufficiently long horizons.

### Actual finite-law outputs, without a strategic tail input

For any integer T≥2, retain the first T dates of the exact periodic profile
and replace every player's later clock by Never. Let C_T be the joint
survival through those T dates. The actual prescribed payoff is exactly

```text
U^T_i = V0_i−C_T V_(T mod 3),i.                      (5)
```

A pure deviation before T has the same payoff as before censorship. A pure
deviation at or after T receives, conditional on all opponents surviving the
head, singleton payoff 1; Never receives zero on that event. Both are at
most V_(T mod 3),i, since every phase value exceeds 1. Applying (4) through
the head bounds every such response by V0_i. Conversely, each player can
attain V0_i by quitting at its first active date: date 0 for players 0,2,3,
and date 1 for player 1. Those dates remain in the head because T≥2.

Consequently every finite-law full cap is exactly V0_i. Its full regret is
C_T V_(T mod 3),i, and thus the maximum regret is at most
(3/2)(5/6)^T. Here C_T≤(5/6)^T follows by comparing joint survival with any
deleted survival rowwise. Equations (5) converge to the same fixed V0.
These are independent finite stopping laws with unrestricted original-game
deviations, including all after-support dates and Never; no finite-menu Nash
restriction or supplied tail equilibrium is used.

## 5. Discovery provenance, current sources and nonclaims

The [dense-profile discovery record](../notes/CODEX_NOETHER_SUPPORT__UNRESTRICTED_FOUR_PHASE_FULL_REGRET_DISCOVERY.md)
provides an actual initial continuation near
(1.08489667,1.12010511,1.07106911,1.13884691). The nearby full-support
predecessor branch numerically raises all values and loses its continuation
chart after four steps. This is not a proof that its roots disappear.
The [new discovery script](../experiments/CODEX_NOETHER_SUPPORT__UNEQUAL_HIGH_NASH_BELLMAN_TEST.py)
tests all 81 boundary/interior support types with finitely many starts.
The resulting numerical root lists are not certified exhaustive, nor is a
chosen root certified maximal under any absorption objective.

Reselecting roots exposed the cycle certified above. None of the numerical
root counts, root maximality, seed-to-cycle convergence, or persistence of a
chosen component enters Sections 1–4. In particular we have not certified a
finite exact predecessor path from the earlier approximate profile into this
cycle. The new equilibrium is jointly reselected for the same original table.

Exact source correspondence inspected for this bounded task:

- `exists_quittingNashBellmanPredecessor`, `IsQuittingNashBellmanEdge`,
  `quittingNashBellmanBox_isCompact`,
  `isClosed_quittingNashBellmanEdgeGraph` in
  `UniformEquilibrium/Quitting/Bellman/Finite/NashBellmanSpine.lean` produce
  bounded exact predecessors, not absorbing predecessors in a smaller set.
- `quittingAllContinueRoot_isZeroNash_of_singleton_le` and
  `uniformEquilibriumPayoff_or_summableClock_of_exactNashBellmanSpine` in
  `UniformEquilibrium/Quitting/Bellman/Finite/NashBellmanClockReduction.lean`
  retain the phantom/summable-clock alternative. Indeed all-Continue remains
  another exact root at all three produced V's; we need only the produced
  absorbing selection, not an assertion about every root.
- `isZeroAsymptoticNash_quittingCyclicBehaviorProfile_of_certificate` and
  `isUniformEquilibriumPayoff_quittingCyclicTerminalValue_of_certificate` in
  `UniformEquilibrium/Quitting/Cycles/PeriodicCompiler.lean` are the exact
  semantic consumers. Their inputs are Bellman recursion, root Nash and the
  product of deleted Continue masses strictly below one for each player.
  Sections 2–4 produce those inputs for this raw table. The rational existence
  calculation itself is ordinary mathematics, not a new checked declaration.

The polynomial clearing and rational interval method reuse
[SPINOZA's E1 overlapping-cycle work](../notes/CODEX_SPINOZA__E1_OVERLAPPING_PERIOD_THREE_CLOSURE.md),
especially its Sections 2–3. Its displayed table and eight-active-role word
are different; importing a supplied cyclic-certificate consumer is not a
claim that its explicit E1 class already contains this table.

Earlier matching obstructions and the failed joint-release test remain valid
only for their stated strategy families. This exact cycle refutes any attempt
to interpret those failures, or the small positive regret of the dense search
output, as a positive unrestricted-regret floor for the present table.

No complete independent [1,2]¹²-box selector has been obtained. This calculation
shows that absorbing root reselection can escape the unsuccessful matching
and specified four-phase supports on one actual table. General bounded
predecessor seriality still permits all-Continue choices, and these local
interval bounds have not been proved uniformly over arbitrary collision data.
No new parameter radius, general invariant-box hypothesis, or export is claimed.

Requested next check: independently reconstruct (1)–(3), then audit (4)–(5),
especially all quiet grand-coalition terms, Never, and after-support responses.
