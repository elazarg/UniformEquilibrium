# Review of the regular-clock no-go and blocker separation

Reviewer: Codex Maxwell

## Verdict

**REPAIR AND STRENGTHEN.** Theorem 1 is correct. Its phase aggregation,
collision estimate, current-phase Quit test, Never test, and the boundary
case in which the limiting owner distribution is a point mass all survive
independent falsification.

The rate hypotheses in Theorem 1 are unnecessary. For a fixed-period word,
convergence of every root to all Continue is enough: normalize by the actual
total period hazard. This gives a strictly stronger no-go for the regular
branch of `../COMP.md`.

The proposed positive-zero-order continuation in the note's final requested
check needs a correction. A positively absorbing zero-order limit need not be
an exact terminal equilibrium when exactly one player remains active. Slower
opponents can punish that player's Never deviation at every approximating
profile and disappear in the limit. An exact two-player example is given
below. The correct fixed-period boundary is:

* no zero-order active player: all-Never is already exact, or the homogeneous
  simplex branch occurs;
* at least two zero-order active players: the limiting periodic profile is an
  exact terminal Nash profile;
* exactly one zero-order active player `i`: all other coordinates are solved,
  and the limiting debt is concentrated at `i` with value
  `(-r_i({i}))_+`.

The rational blocker/support-entry separation in Section 3 is also correct.
It is a separation of the displayed interface, not a counterexample to the
quitting-game conjecture or a realization of the entire hard residual.

## 1. Audit of Theorem 1

Let

\[
 a_i^n=\sum_{k<K}q^n_{ki},\qquad a^n=\sum_i a_i^n.
\]

The period starts in a fixed phase. This does not bias the limiting singleton
owner distribution. The survival factor preceding any one phase is
`1+O(h_n)`, uniformly because `K` is fixed, so the probability during one
period that `i` is the unique quitter is

\[
 a_i^n+O(h_n^2).
\]

The total collision probability in one period is `O(h_n^2)`, while period
absorption is bounded below by `rho h_n`. Repetition of the same independent
period therefore accumulates only `O(h_n)` total collision probability.
Consequently the eventual singleton-owner law converges to

\[
 q_i=\lim_n a_i^n/a^n.
\]

This verifies the phase and geometric-lifetime step used to obtain

\[
 v_i=\sum_j q_jr_i(\{j\}).
\tag{1}
\]

Quitting at the current initial phase collides with an opponent with
probability `O(h_n)`. Hence its payoff is `r_i({i})+O(h_n)`, and vanishing
terminal exploitability gives

\[
 v_i\ge r_i(\{i\}),
\qquad (Mq)_i\ge0.
\tag{2}
\]

If `0<q_i<1`, under the Never deviation the opponents still have period
hazard comparable to `(1-q_i)h_n`. Their collision probability remains
negligible after geometric repetition, so Never converges to

\[
 L_i=\frac{\sum_{j\ne i}q_jr_i(\{j\})}{1-q_i}.
\tag{3}
\]

Vanishing exploitability gives `v_i >= L_i`. But

\[
 v_i=q_ir_i(\{i\})+(1-q_i)L_i.
\]

Together with (2), this forces equality of both endpoints and hence
`(Mq)_i=0`. If `q_i=1`, then `q` is the point mass at `i`, so
`(Mq)_i=M_{ii}=0`; no limiting Never calculation is needed. If `q_i=0`,
complementarity is vacuous. Thus Theorem 1 proves exactly the repository's
`HasHomogeneousSimplexSolution` predicate.

No current-phase, Never, complementarity, or phase-bias counterexample was
found.

## 2. Rate-free strengthening

### Theorem A (vanishing-root fixed-period alternative)

Let `I` be a nonempty finite player set, fix `K>=1`, and let `sigma_n` be the
behavioral profile obtained by periodically repeating `K` product roots
`x^n_0,...,x^n_{K-1}`. Suppose

\[
 \max_{k<K,i\in I}q^n_{ki}\longrightarrow0
\]

and the terminal exploitability of `sigma_n` tends to zero. Then one of the
following holds:

1. the all-Never profile is an exact terminal Nash profile; or
2. the normalized singleton matrix has a homogeneous simplex LCP solution.

If the period has positive absorption for all sufficiently large `n`, the
second alternative holds.

### Proof

Pass to a subsequence on which either the period absorption is zero for every
`n`, or is positive for every `n`. In the zero case every root is all Continue,
so every `sigma_n` is the all-Never profile. Its fixed exploitability is zero.

In the positive case put

\[
 h_n:=a^n=\sum_{k,i}q^n_{ki}>0.
\]

Then `h_n -> 0`, every coordinate satisfies `q^n_{ki} <= h_n`, and elementary
inclusion-exclusion for the finite period gives

\[
 \Pr(\text{period absorption})=h_n+O(h_n^2).
\]

In particular it is at least `h_n/2` eventually. Theorem 1's proof applies
with this endogenous scale, `C=1`, and `rho=1/2`. This proves the homogeneous
alternative. No assumed relation between a previously chosen small parameter
and the root hazards is required.

This removes all purported intermediate scales from a fixed-period producer:
one always normalizes by the total period hazard.

## 3. Exact zero-order boundary

After taking a subsequence, let every finite collection of root probabilities
converge:

\[
 x^n_k\longrightarrow x^0_k.
\]

Define the zero-order active set

\[
 Z=\{i:\exists k<K,\ x^0_{ki}(Q)>0\}.
\]

### Theorem B (fixed-period zero-order classification)

Assume the terminal exploitability of `sigma_n` tends to zero.

1. If `Z` is empty, Theorem A applies.
2. If `|Z|>=2`, the literal periodic profile generated by
   `x^0_0,...,x^0_{K-1}` is an exact terminal Nash profile against all
   behavioral deviations.
3. If `Z={i}`, every player `j != i` has zero terminal debt at the limiting
   periodic profile, while

   \[
   d_i=\max\{r_i(\{i\}),0\}-r_i(\{i\})
      =(-r_i(\{i\}))_+.
   \tag{4}
   \]

   Hence the limiting profile is exact if and only if
   `r_i({i})>=0`.

### Proof

If `|Z|>=2`, then after deleting the strategy of any one player, at least one
other zero-order active player remains. Thus the opponents of every player
absorb during one period with a probability bounded below uniformly in `n`.
For a fixed player, truncate an arbitrary deviation after `m` periods. The
payoff contribution of the discarded tail is bounded by the reward range
times `(1-delta)^m`, uniformly in `n` and in the deviation. Finite-horizon
deviation values are continuous in the finitely many root coordinates.
Therefore the unrestricted behavioral cap is continuous at the limiting word.
The prescribed payoff is continuous by the same geometric-tail argument.
Passing `B_i(sigma_n)-U_i(sigma_n) -> 0` to the limit gives exact terminal Nash.

If `Z={i}`, the same uniform-opponent-absorption argument applies to every
`j!=i`, because player `i` remains an active opponent. Their limiting debts
are zero. Against the limiting opponents of `i`, however, every opponent
always Continues. Prescribed play eventually terminates with coalition `{i}`,
so its payoff is `r_i({i})`. Quitting at any finite date gives the same payoff,
whereas Never gives zero. This proves (4).

### Singleton-active counterexample

Take two players `0,1`, period `K=1`, and reward table

\[
 r_0(S)=-1\quad(S\ne\varnothing),
 \qquad r_1(S)=0\quad(S\ne\varnothing).
\]

Let player `0` Quit each round with probability `1/2`, and player `1` Quit
each round with probability `1/n`. For every finite `n`, this is an exact
terminal Nash profile against all behavioral deviations:

* under every strategy of player `0`, player `1` eventually Quits if needed,
  so absorption occurs almost surely and player `0` receives `-1`;
* player `1` always receives zero.

The roots converge to the positively absorbing word `(1/2,0)`. At that limit,
player `0` receives `-1` under prescribed play but receives zero by deviating
to Never. Thus the positive-absorption limit is not terminal Nash.

This exactly isolates the singular boundary missed by the note: one
zero-order clock can be disciplined by a lower-scale clock which vanishes in
the limit.

## 4. Rational blocker separation

The displayed calculations check exactly:

\[
 Mp=(3/10,9/20,3/10,1/20)>0
\]

for `p=(3/10,1/20,9/20,1/5)`, and on `P={1,3}`,

\[
 M_P^T(1/2,1/2)=(-1,-3/2).
\]

The six order-two principal determinants are

\[
 -6,2,3,2,-6,1,
\]

the four order-three determinants are

\[
 10,-3,5,8,
\]

and the determinant is `25`. No singleton column is nonnegative. Hence the
matrix has no homogeneous simplex solution: a support of size at least two
would give a singular principal submatrix, while a singleton support would
give a nonnegative column.

The common-host cycle is also literal. At

\[
 A=\{0,2\},\ B=\{0,1,2\},\ C=I,\ D=\{0,2,3\},
\]

players `0,2` always Quit, so every selected mover's unrestricted deviation
collapses to its date-zero endpoint. Setting the four mover-coordinate values
as stated gives unit gain on every edge. Setting player `2`'s payoff to `2` on
all four displayed coalitions and using `r_2({0})=M_{20}=2` gives zero player-2
debt at `A`; setting `r_2({0,1})=R` gives

\[
 d_2(B)\ge(R-2)_+.
\]

This reward coordinate changes none of the matrix, blocker, direction, or
selected mover gains. Section 3 therefore correctly refutes automatic
no-new-support from those data.

The example does not show insufficiency of all fields in a
`FinFourQuantitativeFullSupportHardResidual`: standard-Q and the remaining
hard-residual fields are not asserted for the displayed matrix. Its correct
scope is precisely the interface stated in the note's Question.

## 5. Rank passport and source correspondence

Conditions (13)--(15) are sufficient as stated. Global minimality upgrades
total-debt nonincrease to minimum-fiber equality; no-entry and disappearance
give strict support inclusion. The checked declaration

`QuittingPositiveMinimumDebtTangentFamily.exists_reextracted_of_minimumFiber_of_supportSubset_of_vanished`

in
`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/PositiveMinimumDebtTangentFamily.lean`
then regenerates an actual tangent family at the new base. This is a consumer,
not a producer of the passport.

The homogeneous matrix predicate was checked against
`HasHomogeneousSimplexSolution` in
`UniformEquilibrium/Quitting/Classification/LCP/MatrixClasses.lean`, and the
hard exclusion against `ResidualHardClass.no_homogeneous` in
`UniformEquilibrium/Quitting/Classification/LCP/Gate.lean`.

## 6. Conjecture-facing and export verdict

The rate-free Theorem A is stronger than the original note and strictly
narrows the named `COMP.md` producer obligation: in a hard residual carrying a
terminal exploitability witness, **no fixed-period chronology whose roots
converge to all Continue can be the missing periodic producer**, regardless of
its rate or any intermediate scale. Theorem B additionally shows that every
fixed-period positive zero-order limit is consumed except the unique-active,
negative-singleton singular boundary.

That pair is substantial enough to be an export candidate as one precise
impossibility/reduction packet. It is not ready for `exports/` yet. The author
must first incorporate the rate-free theorem and correct the positive
zero-order claim. Because the result explicitly passes from unrestricted
behavioral exploitability to exact terminal Nash, the export rules require a
second independent review with an explicit falsification attempt. This file is
the first such falsification review. The blocker separation may accompany the
packet as a boundary test, but it should not be presented as satisfying all
hard-residual fields.

