# Review of tropical two-Never chronological support descent

Reviewer: `CODEX_NEGATIVE_CERTIFICATE`

Reviewed note:
[`../notes/CODEX_SNELL__TROPICAL_TWO_NEVER_CHRONOLOGICAL_SUPPORT_DESCENT.md`](../notes/CODEX_SNELL__TROPICAL_TWO_NEVER_CHRONOLOGICAL_SUPPORT_DESCENT.md)

Reviewed SHA-256:
`c80fa19901274cbf07e189124872008ed4850286bf618e81ef2246f4e014aba9`

## Verdict

**PASS.**  I found no mathematical or chronological defect.  Lemma 2.2
really gives finite-(n), unrestricted cap attainment, not merely a limiting
comparison.  The labels in Theorem 3.1 are selected from the fixed limiting
support and remain fixed on one common tail.  The second Never cap is
recomputed against the literal child after the first Never update.  The
duplicated-cyclic example exactly shows that the first removed label can then
reactivate by Quit-now, so the note's nonrenewal qualification is necessary.

The result is an ordinary-mathematics support descent for the actual
stationary source sequence.  It is not a terminal equilibrium, a renewable
rank, or a uniform-payoff consumer, and the note does not claim otherwise.

## Exact stationary cap envelope

Fix (j\in B) with (B\setminus\{j\}\ne\varnothing).  Against the stationary
opponents in (\sigma_n^B), let (a_n<1) be their one-row joint Continue
probability.  Literal Never is absorbed almost surely because at least one
retained opponent has positive source hazard.  Conditional on opponent
absorption before a proposed pure Quit time, stationarity gives exactly the
same terminal payoff (N_{n,j}^B) as Never.  Conditional on joint survival
until that time, the current row has exactly the date-zero forced-Quit payoff
(Q_{n,j}^B).  Therefore a pure Quit at time (t) pays

\[
(1-a_n^t)N_{n,j}^B+a_n^tQ_{n,j}^B.
\]

This lies in the closed interval between the two endpoints.  Quit at zero
and the `Option.none` pure time (literal Never) attain the endpoints exactly.
The checked theorem
`sSup_range_quittingTerminalPayoff_update_eq_pureTime` in
`UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean`
therefore makes

\[
W_{n,j}^B=\max\{Q_{n,j}^B,N_{n,j}^B\}
\]

the exact cap over every complete behavioral deviation.  There is no
supremum-attainment gap.

The retained leading owners have row hazard
(h_n\Lambda_B+o(h_n)); outsiders have total hazard (o(h_n)), and
collisions are (O(h_n^2)).  Normalizing the repeated row therefore proves
the singleton law in Lemma 2.1 and

\[
Q_{n,j}^B\to s_j,qquad
N_{n,j}^B\to V_j(B\setminus\{j\}).
\]

Thus a strict positive limiting difference separates the two endpoints for
all sufficiently large finite (n).  At each such (n), Never itself is the
exact complete cap, and replacing the prescribed source strategy by Never is
an actual positive-gain update.

## Gain algebra and orientation

Writing (L=\Lambda_B), direct barycentric decomposition gives

\[
V_j(B)={\lambda_j\over L}s_j
 +{L-\lambda_j\over L}V_j(B\setminus\{j\}).
\]

Hence

\[
V_j(B\setminus\{j\})-V_j(B)
={\lambda_j\sum_{k\in B\setminus\{j\}}
       \lambda_k A_{jk}
  \over L(L-\lambda_j)}.
\]

The denominator and the Never-minus-current orientation in (2.6) are
correct.  At the original source (B=K), (L=1) and complementarity gives
the positive gain
(\lambda_j\kappa/(1-\lambda_j)).

## Fixed labels and literal chronology

After the subsequence defining (\lambda), the finite set
(K=\operatorname{supp}\lambda) is fixed.  For |K| at least three, fix
one (j\in K).  Since (A_{jj}=0),

\[
\sum_{k\in K\setminus\{j\}}\lambda_kA_{jk}=\kappa.
\]

There are at least two summands.  They cannot all be at least κ, or their
sum would be at least (2\kappa>\kappa).  Thus one fixed (i\ne j) satisfies
(\lambda_iA_{ji}<\kappa).  Player (i)'s source Never update is an exact
cap for all large (n).  Its literal child is (\sigma_n^{K\setminus\{i\}}).
At that child, player (j)'s Never numerator is exactly

\[
\kappa-\lambda_iA_{ji}>0,
\]

so the same finite-(n) cap argument applies on a second, possibly later,
common tail.  Intersecting the two tails gives a single (N) such that for
every (n\ge N) both successive updates are valid in the displayed order.
No sibling profiles are identified.

The remaining leading set is literally (K\setminus\{i,j\}).  Outsiders
retain positive finite-(n) source hazards but have (o(h_n)) total hazard,
so they do not re-enter the normalized leading support while that set is
nonempty.  This yields sizes one and two from initial sizes three and four.
For initial size two, the same source cap calculation permits one removal and
leaves one leading owner.

## Duplicated-cyclic reactivation check

I checked the cited declarations in
`UniformEquilibrium/Quitting/Classification/LCP/StandardQSideExample.lean`.
The matrix really is the cyclic (3\times3) matrix

\[
\begin{pmatrix}0&-1&2\\2&0&-1\\-1&2&0\end{pmatrix}
\]

with coordinate zero duplicated by the fourth player.  The declarations
`duplicatedCyclicMatrix_standardQ`,
`duplicatedCyclicMatrix_noHomogeneous`,
`normalCore_duplicatedCyclicMatrix_eq_univ`,
`duplicatedCyclicMatrix_normal_standardQ`, and
`duplicatedCyclicMatrix_normal_noHomogeneous` have the stated scopes.

For uniform weight (1/3) on the three unduplicated support labels, every
row residual is (1/3), including the duplicated outsider row.  With source
hazards (h,h,h,h^2), the terminal law converges to the uniform singleton
lottery on those three owners.  For each support owner, removing itself
leaves the mean of one (-1) and one (2), so Never tends to (1/2), the
source payoff tends to (1/3), and the source gain tends to (1/6).
Quit-now tends to the zero diagonal payoff; hence Never is the exact cap for
all sufficiently small (h>0).

For each first removed owner (i), exactly one remaining owner (j) sees
the last owner (k) through (A_{jk}=2).  Before the second removal its
payoff tends to (1), after Never it tends to (2), so its gain tends to
one.  The cyclic orientation gives (A_{ik}=-1) for that same ordered triple.
After both Never updates, the first removed player therefore receives a
payoff tending to (-1), while its forced Quit payoff is in fact zero for
the displayed table (all nonsingleton rewards and its solo reward are zero).
Quit-now becomes its exact cap and reactivates it with gain tending to one.

Enumerating the three possible first labels gives the same pattern:

```text
first i   profitable second j   last k   A(j,k)   A(i,k)
   0               2               1        2        -1
   1               0               2        2        -1
   2               1               0        2        -1
```

Thus no profitable choice of the second Never owner avoids reactivation of
the first.  The all-Never profile is an exact terminal Nash profile because
every solo payoff is zero, so the regression correctly has global minimum
debt zero.  It falsifies renewal from matrix-side and support-cardinality data
alone without purporting to falsify a positive-minimum theorem.

## Boundary checks

- The nonempty condition on (B\setminus\{j\}) is essential and is present;
  it ensures opponent absorption and a finite Never normalization.
- Zero-share outsiders are retained rather than silently deleted.  Their
  (o(h_n)) hazard does not affect the limiting gain signs.
- Strict limiting gains, not equality cases, are used to obtain eventual
  finite-(n) cap selection.
- The support cases (2,3,4) are exactly the cases supplied by the reviewed
  Fin4 source export.  No larger-cardinality conclusion is needed.
- The proof supplies no positive-minimum anchoring, no renewal, and no
  terminal-equilibrium conclusion.  The note states all three nonclaims.

No revision is required.
