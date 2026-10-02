# Complete-response empirical products in the canonical game

Identity: CODEX_HILBERT. Status: one exact update lemma plus a reproducible
finite experiment. No convergence or asymptotic nonconvergence theorem is
proved. This is a bounded test of a specified approximate-selection rule,
not an export, a new exact-menu equilibrium selector, or a general no-go.

## 1. Actual rule and target

Fix a canonical Fin4 quitting table with own singletons e₀ and Never zero.
At each accuracy we seek ONE actual product stopping law with small finite
menu error and small pivot excess L₀=W₀+D₀−U₀. These errors are evaluated
on the SAME law, with unrestricted behavioral deviations.

Choose an exact one-date menu Nash law p¹² as initialization. The weight 12
is fixed; it conveniently makes the test initialization integral. For n≥12:

1. For every player i compute its FULL best response against pⁿ₋ᵢ. Because
   the opponents have finite support, this is the maximum of finitely many
   pure dates, one date after their last finite atom, and literal Never.
2. Choose Never if it attains that maximum; otherwise choose its earliest
   maximizing finite date bᵢⁿ. Thus ties and the omitted pivot action are
   specified, not delegated to an arbitrary selector.
3. Simultaneously update each COMPLETE marginal independently by

       pᵢ^(n+1) = [n pᵢⁿ + δ_(bᵢⁿ)]/(n+1).

4. As a possible output at budget n, retain the best-so-far pᵐ, 12≤m≤n,
   measured by its actual full exploitability. This is an explicit search
   rule, not a hypothesis that its error tends to zero.

The output is the PRODUCT of the four empirical marginal laws. It is NOT
the correlated empirical distribution of the four-tuples of responses used
in earlier rounds. No public random seed chooses a common earlier round.
Any generic statement about regret of a correlated history would therefore
require a separate theorem before it could apply to this output.

Every iterate is a genuine finite law. For its current full menu, each
nonpivot full cap equals its finite-menu cap, while the pivot cap has the
one extra late candidate. The rule computes all four full caps explicitly.
It does not preserve the three nonpivot comparisons as constraints.

## 2. Canonical test table and initialization

Use the table in `CODEX_HILBERT__CANONICAL_PIVOT_BOUNDARY_HOMOTOPY.md`.
With active predecessor i−1 modulo three, for nonempty S:

    r₀(S)=1+1_{2∈S} if 0∈S; 3·1_{2∈S} otherwise;
    rᵢ(S)=1_{i−1∈S} if i∈S; 3·1_{i−1∈S}−1 otherwise, i=1,2;
    r₃(S)=0 if 3∈S; 1 otherwise.

The unique one-date menu Nash has Quit0 probabilities (1/3,1/4,1/2,0)
and Never otherwise. Its full debt vector is (3/8,0,0,0). With weight 12,
the three active Quit counts are (4,3,6), and Never counts are (8,9,6).
Dummy Never weakly dominates every finite date against EVERY opponent law
on this table: quitting changes a possible absent-player payoff 1 into 0,
and Never already obtains 0 on all-Never. The prescribed tie rule therefore
keeps its marginal equal to Never at all iterations. All four-player
comparisons are nevertheless covered; the dummy debt is identically zero.

This table has an explicit exact period-three terminal Nash profile and
finite truncations of that profile with full regret tending to zero, as
proved in the companion note. Failure to discover these profiles would be
a failure of this search rule, not of approximate selection on the table.

## 3. Exact first-update failure of safety preservation

At the initialization, the chosen responses are (Quit1,Never,Never,Never).
For an arbitrary relaxation fraction 0≤x≤1, mixing that response profile
coordinatewise into the initialization gives

    p₀(0)=(1−x)/3, p₀(1)=x, p₀(Never)=2(1−x)/3;
    p₁(0)=(1−x)/4, p₁(Never)=(3+x)/4;
    p₂(0)=(1−x)/2, p₂(Never)=(1+x)/2.

Exact enumeration of pure response dates 0,1,2,Never gives the FULL debts

    d₀=(1−x)(3x²+4x+9)/24,
    d₁=x(1−x)(7x+5)/24,
    d₂=x(x+1)(x+5)/12,
    d₃=0.                                             (A)

For 0<x<1, the caps are attained respectively at late Quit, Never, and
Quit0. Endpoint ties cause no change to (A). In particular any nonzero
step immediately makes player 2 exploitable, and every interior step makes
BOTH originally safe active nonpivots exploitable. One cannot call the new
profile safe except for its pivot solely because the initialization was.

For clarity, the pure payoffs are:

    i=0: F(0)=(3−x)/2,
         F(1)=F(2)=(x−5)(x−3)/8, W=3(1−x)/2;
    i=1: F(0)=(1−x)/3, F(1)=(2x²+1)/3,
         F(2)=W=(7x²+3x+2)/6;
    i=2: F(0)=(1−x)/4, F(1)=(x−3)(x−1)/12,
         F(2)=W=−(2x²+13x−3)/12.

Every date beyond 2 has the displayed late value. Taking each player's
own-law average and subtracting it from the maximum proves (A), including
all mixed behavioral deviations by pure-time extremality. The actual first
empirical step is x=1/13 and has exact debt vector

    (788/2197, 36/2197, 77/2197, 0).

This is only a failed invariant, NOT a proof that iterated best responses
cannot later restore approximate safety.

## 4. Exact-arithmetic finite trajectory

I ran iterations n=12 through 100000 with integer response comparisons and
the stated tie rule. Fractions were converted to decimals only for display.
The best full exploitability over EVERY inspected iterate was

    155636/1157625 ≈ 0.1344442285, at n=105.

The selected n=105 laws have finite counts at dates 0,1,2,3 respectively:

    player0: (6,9,80,2), Never count8;
    player1: (70,6,0,0), Never count29;
    player2: (13,82,3,0), Never count7;

all divided by 105. Their full active debt numerators over denominator
1157625 are (40114,155636,148823). The BEST iterate thus has a NONPIVOT
as its largest debtor. At this law D₀=29/1575 and pivot excess is
40114/1157625. In particular a small deleted-survival term alone does not
repair the newly created menu regrets.

Some later values, displayed only as finite-run diagnostics:

| n | menu length | pivot debt | player1 debt | player2 debt |
|---:|---:|---:|---:|---:|
| 1000 | 7 | 0.24120229 | 0.05761476 | 0.20001131 |
| 10000 | 11 | 0.33939104 | 0.04193706 | 0.16791698 |
| 100000 | 16 | 0.33144163 | 0.03723407 | 0.25502877 |

At n=100000, D₀=53977/2000000000 is already very small. Large current
debt is not just the original omitted-date escape charge of an exact-menu
Nash law: these empirical products themselves have substantial displayed
menu regret. No positive lower bound for all future iterations is inferred.

## 5. Reproduction and payoff derivation

For active i let j=i−1 and k=i+1 modulo three. Let cᵢ(t) be its integer
finite counts, zᵢ its Never count, and Sᵢ(t)=zᵢ+Σ[u≥t]cᵢ(u). Every
pure-response payoff has denominator n². Its prefix ledger increment is

    i=0: 3cⱼ(t)Sₖ(t);
    i=1,2: 2cⱼ(t)Sₖ(t)−[Sⱼ(t)−cⱼ(t)]cₖ(t).

The first term includes predecessor quitting alone or tied with the other
opponent; the second is the negative absent-player payoff when only the
other opponent quits. At a pure own Quit at t, add cⱼ(t)Sₖ(t), and for
the pivot also add Sⱼ(t)Sₖ(t). This retains literal same-date collisions.
After the last finite atom the ledger is the Never payoff; the pivot's
late response additionally gets zⱼzₖ. Its prescribed payoff is the
own-law average and has denominator n³.

The following standalone reproduction requires NumPy, uses no floating
comparisons, and writes no files. For the stated 100000-iteration range,
all integer intermediates are bounded by a fixed small multiple of n³,
well below signed 64-bit range. Increasing that range requires checking
the bound or switching all arithmetic to Python integers.

```python
import numpy as np
from fractions import Fraction

C = np.array([[4], [3], [6]], dtype=np.int64)
z = np.array([8, 9, 6], dtype=np.int64)
best = None
for n in range(12, 100001):
    S = np.flip(np.cumsum(np.flip(C, axis=1), axis=1), axis=1) + z[:, None]
    debts, replies = [], []
    for i in range(3):
        j, k = (i - 1) % 3, (i + 1) % 3
        inc = (3*C[j]*S[k] if i == 0 else
               2*C[j]*S[k] - (S[j] - C[j])*C[k])
        Z = np.r_[0, np.cumsum(inc)]
        W = int(Z[-1])
        F = np.r_[Z[:-1] + C[j]*S[k] +
                  (S[j]*S[k] if i == 0 else 0),
                  W + (z[j]*z[k] if i == 0 else 0)]
        B = max(W, int(F.max()))
        U = int(np.dot(C[i], F[:-1]) + z[i]*W)
        debts.append(Fraction(n*B - U, n**3))
        replies.append(-1 if W == B else int(np.flatnonzero(F == B)[0]))
    E = max(debts)
    if best is None or E < best[0]:
        best = E, n
    if max(replies) >= C.shape[1]:
        C = np.pad(C, ((0, 0), (0, 1)))
    for i, t in enumerate(replies):
        if t < 0:
            z[i] += 1
        else:
            C[i, t] += 1
print(best)
# (Fraction(155636, 1157625), 105)
```

## 6. Bounded source check and present verdict

The source route is actual finite timing and complete pure-time responses,
not correlated equilibrium. Inspected dependencies are
`quittingFiniteDeadlineReplyCap` and `isQuittingFiniteDeadlineNash_iff_pure`
in `UniformEquilibrium/Quitting/Terminal/FiniteDeadlineReplyCap.lean`, and
the finite-law cap and late-date identities recorded with exact declaration
names in `feedback/TRANSFORM__BY_CODEX_HILBERT.md`. The initial canonical
Nash law and successful periodic comparator are proved in the companion
homotopy note. A narrow search of the terminal/diagnostic stopping-law and
generic simplex sources found no convergence result for this empirical rule.
No convergence theorem from game-theoretic learning literature is invoked.

The useful exact result is the simultaneous reactivation of the nonpivot
debts in (A). The bounded experiment does not identify a new producer and
does not prove failure of the empirical rule at arbitrarily late iterations.
An asymptotic convergence or explicit cycling proof would be needed to
settle this particular algorithm. No such premise is hidden in the output
selection rule. The canonical approximate-selection question remains open.

## 7. Second-table checkpoint: a much simpler late-date chase

Before a separate final-assembly review interruption, I tested the SAME
empirical-product rule on only the table data and explicit geometric
comparator in `gpt/EXACT_EXAMPLE.md`. This is not a second review of that
submission's uniqueness or limit theorem; FRECHET was assigned that review.

Its active reward rows for coalitions 0,1,2,01,02,12,012 are respectively
(1,7,7), (7,0,7), (7,7,0), (6,8,7), (9,7,5), (7,5,8), (7,6,6).
Dummy Never weakly dominates every finite response and is selected by the
specified tie rule. Initialize from the submitted one-date law with Quit
probabilities (2/7,4/7,1/7). Retain initial weight12: integer counts are
(24,48,12), Never counts(60,36,72), total84; add7 to each selected action
per update, so the total denominator at iteration n is7n.

Exact integer response comparisons through n=10000 gave:

| n | menu length | pivot debt | player1 debt | player2 debt |
|---:|---:|---:|---:|---:|
| 30 | 10 | 1.276272109 | 1.988380952 | 0.249904762 |
| 100 | 45 | 2.380159347 | 3.021106286 | 0.107307429 |
| 1000 | 495 | 2.933892302 | 3.451111649 | 0.011876222 |
| 10000 | 4995 | 2.993347499 | 3.495101117 | 0.001198765 |

Best inspected full regret was 38580/107653 at n=13, with no later
improvement. The observed late-time chase is simpler than the first table's
pattern: player0 chooses a fresh late date, player1 follows at the previous
date, player2 keeps choosing Never. The apparent limits3 and7/2 are NOT
proved by this finite run. Exact eventual response inequalities would be
needed before claiming them.

The submitted successful approximate witness instead lets only player0
quit, with hazard1/2, truncated at the requested menu. This suggests a
genuinely approximation-aware modification: prefer Never whenever its
payoff is within ε_n of the full cap, not only at an exact tie. Chasing a
vanishing last-date collision advantage may be unnecessary for an
approximate selector. Whether this modification actually works remains
untested at this checkpoint; no generic learning guarantee is invoked.

## 8. A modified actual selector: exact success on the second table

The following is a NEW, fully specified rule, distinguished from Section1.
Initialize p¹ as all-Never, with unit initial weight, NOT the weighted
exact-menu Nash initialization used in the earlier runs. At step n≥1 let
F be all dates through ONE date after the current last finite atom, plus
Never. Compute full pure caps on this finite list. Set ε_n=1/√n.

- The pivot chooses the LATEST finite date in this list attaining its full
  cap. Such a date exists: the canonical positive singleton makes the late
  value at least the Never value. No unbounded "latest date" is used.
- Each nonpivot chooses Never if B_i−W_i≤ε_n; otherwise it chooses the
  EARLIEST finite full-cap attainer in the same list.
- Update each marginal by pᵢ^(n+1)=[n pᵢⁿ+δ_b]/(n+1), independently.

This uses approximation deliberately: a nonpivot may keep Never despite
a small strictly profitable collision response. The pivot tie rule spreads
finite atoms when that causes no loss; it does not impose a private clock
penalty or claim payoff equivalence. The output remains a product law,
not a correlated historical mixture. At n=1 with no finite atoms, the one
fresh candidate is date0. Both tables in this NEW comparison use exactly
this all-Never initialization. No effect is attributed solely to the new
tolerance or tie rule, since initialization changed as well.

On the second table this algorithm is EXACTLY solvable. For every n≥1,
the pivot has mass1/n at each date0,…,n−2, mass1/n at Never, and all
nonpivots choose Never. The finite list is empty when n=1.

Proof by induction: every finite pivot response pays1, so its latest listed
attainer is the fresh date n−1. For n≥2, player1's pure response at a
represented date t pays (7t+8)/n; its Never and every after-menu value are
7(n−1)/n. Its maximum gain over Never is exactly1/n at t=n−2.
Player2's corresponding represented-date payoff is (7t+5)/n, everywhere
below its Never value7(n−1)/n. Dummy3 obtains at most zero, attained by
Never: a collision with the pivot pays−1, every other available outcome
pays zero. Therefore each nonpivot chooses Never because1/n≤1/√n.
At n=1 all nonpivot caps are zero, so the induction also starts correctly.
The empirical update produces precisely the next uniform marginal.

For n≥2 the resulting ORIGINAL full debt vector is

    (1/n, 1/n, 0, 0).

All finite and Never responses were checked above; arbitrary behavioral
replacements are their mixtures. Thus both displayed-menu error and pivot
late excess tend to zero, with actual menu length N=n−1. The target payoff
is (1,7,7,0), approached by prescribed values
(1−1/n,7−7/n,7−7/n,0). No initial approximate equilibrium or useful
profile was supplied to the rule.

This is a positive algorithmic contrast on an already solved test table,
not a new arbitrary-table existence theorem. Its simple success is consistent
with the submitted geometric one-owner witness; it constructs uniform
diffuse dates instead of geometric dates.

## 9. The same modified rule still needs a cyclic-table mechanism

With EXACTLY the same all-Never unit initialization, tie rules, and tolerance
on the first cyclic table, an integer-comparison run through n=10000 gave
best full error40368/274625≈0.14699317 at n=65. At n=10000 the full active
debts were approximately(0.020835675,0.251407705,0.301620310).
These are finite experimental statements, not an asymptotic obstruction.
The pivot's nearly vanishing debt is not enough: the two active nonpivots
remain substantially exploitable.

Unlike the second table, its player2 receives−1 when only the pivot quits.
A pivot-only diffuse law therefore makes that nonpivot's Never response
bad by an order-one amount, not a small collision correction. The tolerance
rule correctly stops leaving that player at Never; it then lacks a proof
that the ensuing independent empirical mixtures become jointly safe.
This is the concrete information a further global construction must use.
No tolerance tuning or parameter sweep was performed.

For exact reproduction of these modified runs, use the Section5 ledger on
the first table, initialize all finite counts empty and all Never counts1,
and run n from1. At each update the pivot takes the LAST maximizer in F;
a nonpivot takes Never exactly when (B_num−W_num)²≤n³, otherwise the FIRST
finite maximizer. This squared integer comparison is exactly
(B−W)≤1/√n because B_num−W_num≥0 and the pure payoff denominator is n².
For the second table use its listed reward rows and the generic two-opponent
ledger: sum each nonempty current opponent coalition's integer product mass
times its reward, then add the forced-own-Quit endpoint similarly. Initial
weight12 and its old counts must NOT be retained for the modified rule.
