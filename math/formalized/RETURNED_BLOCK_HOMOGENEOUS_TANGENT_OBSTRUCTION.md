# Returned-Block Homogeneous-Tangent Obstruction

Author: `CODEX_GAUSS`

Independent review:
[`CODEX_NOETHER`](../feedback/CODEX_GAUSS__CURL_FREE_TOGGLE_POTENTIAL__BY_CODEX_NOETHER__ROUND_11.md)

The reviewer independently checked the probability-weighted endpoint signs,
fixed- and varying-horizon compactness, the product-law expansion, the
aggregate-error telescope, and the normal-core scope correction.  No
mathematical objection remains.

## Exact statement

Let `I` be a nonempty finite player type with decidable equality, and let

```text
r : {S : Finset I // S.Nonempty} -> (I -> Real)
```

be an arbitrary quitting reward table.  Put

```text
s_i   = r({i})_i,
M_i,j = r({j})_i-s_i.                                (1)
```

A finite returned product block consists of a positive finite phase count
`m`, phase payoffs `v_k : I -> Real`, and playerwise Quit hazards
`p_k,i in [0,1]`, with phase indices read cyclically.

For one hazard vector `p`, write

```text
P_p(S)=product_(i in S) p_i * product_(i notin S)(1-p_i).
```

For tail payoff `t`, its exact successor payoff is

```text
T_i(t,p)=P_p(empty)*t_i
  + sum_(nonempty S) P_p(S)*r(S)_i.                  (2)
```

Let `Quit_i(t,p)` and `Continue_i(t,p)` be the same expectation after player
`i` is forced respectively to Quit and Continue while all opponents retain
their independent hazards.  Define

```text
D_i(t,p)=Quit_i(t,p)-Continue_i(t,p).                (3)
```

The block's total hazard, aggregate absolute Bellman residual, and aggregate
endpoint regret are

```text
S = sum_(k,i) p_k,i,                                 (4)

B = sum_(k,i) |v_k,i-T_i(v_(k+1),p_k)|,              (5)

E = sum_(k,i) [max(0,(1-p_k,i)*D_i(v_(k+1),p_k))
                  + max(0,-p_k,i*D_i(v_(k+1),p_k))]. (6)
```

The two terms in `(6)` are exactly the pure-Quit and pure-Continue regrets in
the repository's `IsεQuittingRootEndpointNash` convention.  They are not the
absolute raw difference `|D_i|`.

### Theorem A: arbitrary-horizon tangent obstruction

For every positive integer `n`, let a finite returned block be supplied; its
phase count may depend on `n`.  Assume:

1. all phase payoff coordinates in all blocks have one common finite absolute
   bound;
2. `S_n>0` and `S_n -> 0`;
3. `B_n/S_n -> 0`; and
4. `E_n/S_n -> 0`.

Then `M` has a homogeneous simplex LCP solution: there is a probability vector
`mu` on `I` such that

```text
(M mu)_i>=0,
mu_i>0 -> (M mu)_i=0.                               (7)
```

In repository language, the conclusion is
`HasHomogeneousSimplexSolution M`.

### Theorem B: uniform small-charge gap

Fix a finite payoff bound `K` and suppose

```text
not HasHomogeneousSimplexSolution M.                 (8)
```

Then there are constants `delta,c>0`, depending on `r` and `K`, such that
every finite returned product block satisfying

```text
|v_k,i|<=K,       0<S<=delta
```

obeys the uniform relative gap

```text
B+E>=c*S.                                            (9)
```

The phase count in Theorem B is arbitrary and is not bounded in advance.

## Conjecture-facing change

`ResidualHardClass.no_homogeneous`
(`UniformEquilibrium/Quitting/Classification/LCP/Gate.lean`) excludes a
homogeneous solution on the recursively normal alpha-player principal matrix.
The present theorem strictly narrows the returned-block route on that live
branch:

```text
no-homogeneous normal core
  + core-supported returned product blocks
  + relative aggregate semantic error tending to zero
  => total accumulated hazard cannot vanish.         (10)
```

Thus a source-matched cross-face construction supported in the normal core
cannot disappear into the all-Continue boundary while keeping aggregate
Bellman and standard endpoint-Nash error negligible relative to absorption.
It must instead carry nonvanishing accumulated charge and moving payoff,
compactify to an exact positive returned block when its horizon is bounded,
or dispatch to another solved branch.

This is a reduction of the producer obligation, not a producer.  In
particular, it identifies why the missing chronology in
`PaidFirstDisagreementAdmissiblePayoffNearReturnConsumer`
(`UniformEquilibrium/Diagnostics/Quitting/PaidFirstDisagreementPayoffNearReturn.lean`)
cannot be replaced by arbitrarily small returned loops on the normal core.

## Definitions and assumptions

Each phase uses independent Bernoulli randomization by the players.  The
empty outcome continues to the next phase payoff; every nonempty coalition
terminates with the literal source-table reward.  Phases are finite and their
last continuation returns to phase zero.

The theorem assumes no equilibrium, punishment-floor, or sequential
observation structure beyond the local product rows and their supplied phase
payoffs.  It tests the two endpoint deviations at each row.  It does not
assert that the block is itself a behavioral strategy, that a deviator is
restricted to one-shot play, or that local endpoint conditions alone control
an unrestricted behavioral deviation.  Its conclusion is algebraic.

The common payoff bound is essential for uniform first-order estimates.
Actual Nash--Bellman blocks in the project normally lie in a canonical reward
box, but Theorems A--B state the needed bound directly.

## Source correspondence

The exact existing declarations inspected are:

- `IsεQuittingRootEndpointNash`
  (`UniformEquilibrium/Quitting/Root/SuccessorCertificate.lean`), whose two
  inequalities are exactly the probability-weighted regrets in `(6)`;
- `HasHomogeneousSimplexSolution`
  (`UniformEquilibrium/Quitting/Classification/LCP/MatrixClasses.lean`), the
  conclusion `(7)`;
- `normalizedNormalPlayerMatrix` and `normalCore`
  (`UniformEquilibrium/Quitting/Classification/LCP/NormalCore.lean`), which
  identify the alpha-player principal matrix;
- `ResidualHardClass.no_homogeneous`
  (`UniformEquilibrium/Quitting/Classification/LCP/Gate.lean`), the checked
  hard-branch hypothesis used by `(10)`; and
- `singletonLCPFeasible_of_stationaryEndpointNash_tangent`
  (`UniformEquilibrium/Quitting/Stationary/ApproximabilityCompactification.lean`),
  the closest checked one-row analogue.

The last declaration treats stationary self-loops.  A narrow search for
`homogeneous`, `tangent`, `cycle`, `block`, `returned`, and
`SingletonLCPFeasible` in the cycle, path, Bellman, and stationary subtrees
found no fixed- or varying-horizon returned-block telescope with aggregate
semantic regret.  No paper theorem is invoked.  The new content is the
returned-block total-variation and telescoping reduction.

## Proof

Let `R` bound every terminal reward coordinate and let `K` bound the phase
values.

### Step 1: exact one-row estimates

For one row put `q=sum_i p_i`.  Then

```text
|T_i(t,p)-t_i| <= (K+R)q.                            (11)
```

Indeed absorption has probability at most `q`, and on absorption the payoff
coordinate differs from the tail by at most `K+R`.

There is also the exact first-order bound

```text
|T_i(t,p)-t_i-sum_j p_j(r({j})_i-t_i)|
  <=2(K+R)q^2.                                       (12)
```

To prove it, let `P_0` be the no-quitter probability, `P_j` the probability
that `j` is the unique quitter, and `P_multi` the probability of at least two
quitters.  Union and pair counting give

```text
0<=P_0-(1-q)<=q^2/2,
0<=sum_j(p_j-P_j)<=q^2,
P_multi<=q^2/2.                                     (13)
```

Expanding `(2)` into empty, singleton, and multiple coalitions bounds the
remainder by

```text
(K/2+3R/2)q^2<=2(K+R)q^2.
```

Finally,

```text
|D_i(t,p)-(s_i-t_i)|<=(K+3R)q.                      (14)
```

After `i` is forced to Quit, an opponent quits with probability at most `q`,
costing at most `2Rq` relative to `s_i`.  After `i` is forced to Continue,
an opponent quits with probability at most `q`, costing at most `(K+R)q`
relative to `t_i`.  The triangle inequality proves `(14)`.

### Step 2: all phase values converge to one payoff

For block `n`, put `q_n,k=sum_i p_n,k,i`.  From `(11)` and the Bellman
residuals, the total variation of the phase payoffs is at most

```text
(K+R)S_n+B_n.                                       (15)
```

This tends to zero.  Extract a convergent subsequence of the bounded phase-zero
payoffs, with limit `w`.  Equation `(15)` makes every phase payoff, despite
the varying phase count, uniformly converge to that same `w`.

### Step 3: endpoint signs and support pinning

By `(14)`, every endpoint difference converges uniformly to `s_i-w_i`.

If `w_i<s_i`, the first regret in `(6)` is eventually bounded below by a
positive constant at every phase, since every `p_n,k,i<=S_n->0`.  This
contradicts `E_n->0`.  Hence

```text
w_i>=s_i.                                            (16)
```

Normalize cumulative owner hazards:

```text
mu_n,i=(sum_k p_n,k,i)/S_n.                          (17)
```

After another subsequence, `mu_n` converges to a probability vector `mu`.
If `w_i>s_i`, every endpoint difference in coordinate `i` is eventually
strictly negative by one uniform margin.  The second regret in `(6)`, summed
over phases and divided by `S_n`, then forces `mu_n,i->0`.  Thus

```text
mu_i>0 -> w_i=s_i.                                   (18)
```

### Step 4: telescope the returned Bellman equations

Sum `(12)` and the signed Bellman residuals around the block.  The phase
payoffs telescope exactly.  Moreover,

```text
sum_k q_n,k^2 <= S_n^2.                              (19)
```

Divide by `S_n`.  The Bellman contribution is bounded by `B_n/S_n`, the
nonlinear contribution by a constant times `S_n`, and all tails converge
uniformly to `w`.  Passing to the limit gives

```text
0=sum_j mu_j(r({j})-w).                              (20)
```

Therefore

```text
(M mu)_i=sum_j mu_j(r({j})_i-s_i)=w_i-s_i.
```

Equations `(16)` and `(18)` are exactly residual nonnegativity and
complementarity.  This proves Theorem A.

### Step 5: uniform gap

If Theorem B were false, for every positive integer `n` one could choose a
returned block with

```text
0<S_n<=1/n,       (B_n+E_n)/S_n<1/n.
```

The common value bound is `K`, and nonnegativity separately gives
`B_n/S_n->0` and `E_n/S_n->0`.  Theorem A would produce a homogeneous
solution, contradicting `(8)`.  This proves Theorem B.

## Boundary tests

1. **Homogeneous positive boundary.**  With one player, `M=[0]`.  Taking the
   phase payoff equal to the solo payoff makes every one-phase hazard an exact
   returned row, including hazards tending to zero.  Theorem A correctly
   returns the unique homogeneous simplex vector.

2. **Nonvanishing returned block.**  The checked Solan--Vieille paired
   completion has normalized matrix `pairedSingletonMatrix`, which has no
   homogeneous simplex solution by `pairedSingletonMatrix_noHomogeneous`
   (`UniformEquilibrium/Quitting/Examples/BlockPair/FourPlayerPairedSingletonLCP.lean`).
   Its checked period-two block has positive nonvanishing absorption.  This is
   exactly the survivor allowed by Theorem B, not a counterexample to it.

3. **Collision-row independence at vanishing charge.**  The
   `boundaryReward` and `stationaryCompletionReward` tables have the same
   paired singleton matrix but different collision rows.  Collision
   contributions are bounded by `(19)` and disappear in Theorem A's
   first-order telescope.  The latter game also has a checked pure stationary
   equilibrium, so this comparison is not a game counterexample.

4. **Weighted-gap test.**  If `p=alpha*lambda` and a raw endpoint difference
   is `D=-kappa*alpha`, the profitable Continue regret is only
   `-pD=kappa*lambda*alpha^2`.  This falsifies replacement of `(6)` by an
   unweighted claim such as `|D|<=epsilon`.  The proof uses the cumulative
   weighted regret exactly where support pinning is needed.

## Adapter and consumer

For any finite subtype `C` of players, restrict the reward table by mapping a
nonempty coalition of `C` into `I` and restricting payoff coordinates to `C`.
Singleton normalization commutes literally with this restriction.

Taking

```text
C=normalCore (normalizedSoloMatrix r)
```

makes the restricted normalized singleton matrix equal to
`normalizedNormalPlayerMatrix r`.  An ambient product block whose hazards are
zero off `C` has exactly the restricted Bellman and endpoint laws in every
coordinate of `C`.  Hence `ResidualHardClass.no_homogeneous` and Theorem B
give the normal-core-supported relative gap `(10)` from actual source-table
data.

The checked normal-core and punishment-normal specializations are recorded by
the declarations cited below.  The analogous punishment-normal reward
restriction is
`quittingPunishmentNormalReward` and
`normalizedSoloMatrix_quittingPunishmentNormalReward`
(`UniformEquilibrium/Quitting/Classification/LCP/NormalPrincipalReward.lean`).

The packet does not itself feed a semantic consumer.  Its conjecture-facing
role is the permitted export category of a proved reduction that strictly
narrows a named live producer obligation.  A successful nonvanishing
chronology would still need to enter a checked consumer such as
`PaidFirstDisagreementAdmissiblePayoffNearReturnConsumer`; the theorem does
not construct that input.

## Probability, information, and deviation audit

The probability law is exactly a finite sequence of independent simultaneous
product rows.  The proof uses no public correlation, hidden signal, stopping
time, infinite product, or interchange of an unrestricted behavioral
best-response supremum with a limit.

The two deviations in `(6)` are the exact local pure endpoints, with the
prescribed own-action probabilities retained in their regrets.  This is the
same local predicate used by the repository's Nash--Bellman compilers.  The
theorem makes no assertion that these local conditions alone certify a full
unrestricted behavioral equilibrium.  Accordingly it claims neither an
all-behavior consumer nor a full strategy-class completeness result.

## Checked Lean realization

The finite-row estimates and homogeneous-tangent obstruction are proved in
`UniformEquilibrium/Quitting/Stationary/ReturnedBlockTangentObstruction.lean`,
including `relativeError_gap_of_noHomogeneous` and
`hasHomogeneousSimplexSolution_of_vanishing_returnedBlocks`.  The principal,
normal-core, and punishment-normal adapters are checked by
`exists_pos_principalReturnedBlock_relativeError_gap`,
`ResidualHardClass.exists_pos_normalCoreReturnedBlock_relativeError_gap`, and
`exists_pos_punishmentNormalReturnedBlock_relativeError_gap`
(`UniformEquilibrium/Quitting/Classification/LCP/ReturnedBlockTangentGap.lean`).
For literal `Fin 4`,
`hasAmbientReturnedBlockRelativeErrorGap_of_fourPlayer_counterexample`
(`UniformEquilibrium/Diagnostics/Quitting/FourPlayerReturnedBlockGap.lean`)
provides the counterexample-facing adapter.  None of these declarations is an
all-behavior uniform-equilibrium consumer.

## Scope and nonclaims

- The supplied-block obstruction and the named principal/normal-core adapters
  are proved in Lean.
- It is an impossibility/reduction theorem for supplied returned blocks, not a
  producer of blocks, paths, or strategies.
- It does not prove a uniform-equilibrium payoff or a terminal exploitability
  gap.
- The residual-hard corollary applies directly to blocks supported inside the
  recursive normal core.  It does not exclude ambient blocks using abnormal
  owners.
- With varying horizons, the **aggregate** Bellman and endpoint regrets must
  be `o(S)`.  A rowwise error whose total accumulation is uncontrolled is
  outside the theorem.
- Nonvanishing accumulated hazard, moving-payoff chronology, exact positive
  returned blocks, and solved-branch dispatch remain open survivors.
- The constants in Theorem B are existential and depend on the reward table
  and value bound; no computable modulus is claimed.
