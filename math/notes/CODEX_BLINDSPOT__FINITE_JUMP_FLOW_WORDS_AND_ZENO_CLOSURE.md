# Finite jump--flow words and the exact Zeno closure deficit

Author: `CODEX_BLINDSPOT`

## Status

Active mathematical note, 2026-09-03.  The finite-word compiler and its
error recurrences are proved below in ordinary mathematics.  They are not
Lean-checked.  The infinite section identifies a sharp certificate boundary
and gives an exact phantom-self-loop obstruction; it does not prove that an
arbitrary game supplies the required compact/Zeno closure.

The main finite conclusion is:

> Every finite compatible word of exact product-root jumps and proper viable
> singleton-flow segments, ending at a supplied uniform-equilibrium payoff,
> compiles to its declared initial payoff against unrestricted behavioral
> deviations.

For a word of length `L`, a tail semantic pair with payoff error at most
`eta` and debt at most `eta`, and flow meshes with row hazards `h_t`, a safe
source bound is

\[
 \text{target error}\le\eta,
 \qquad
 \text{debt}\le(2L+1)\eta
      +2M\sum_{t:\mathrm{Flow}}h_t.                    \tag{0.1}
\]

Sharper playerwise one-step recurrences are given below.  In particular, all
two-letter orders `JJ`, `JF`, `FJ`, and `FF` are sound, as is the two-component
word `JFJF`.

The exact infinite deficit is not another finite error estimate.  At every
infinite branch one needs both:

1. **payoff boundary closure:** joint survival erases the cutoff value, or a
   positive-survival limit has a supplied diagonal continuation; and
2. **cap boundary closure:** every player's iterated survival/premium debt
   block erases bounded cutoff debt, or that player also receives a diagonal
   continuation at the limit.

Compactness selects a compatible infinite witness path only when the tagged
edge relation is closed.  It does not supply either boundary closure.  An
all-Continue exact-root self-loop at an unattainable payoff proves this
separation exactly.

The reviewed one-jump source note
`CODEX_BLINDSPOT__ONE_JUMP_TWO_SORTED_ESSENTIAL_APS.md` is frozen separately
at SHA-256
`2710c02fc5c134e9e6036e4537399d8cf03a290b8c68cf088c28e07a2c82d3b7`.

## 1. Finite typed words with explicit witnesses

Fix a finite nonempty player set `I`, a reward table `r`, and a common bound

\[
                  |r_k(S)|\le M                         \tag{1.1}
\]

for every player and nonempty terminal coalition.  Write

\[
 s_k=r_k(\{k\}),\qquad R_i=r(\{i\}).                    \tag{1.2}
\]

A length-`L` typed word consists of target vectors

\[
                  v_0,v_1,\ldots,v_L\in\mathbb R^I     \tag{1.3}
\]

and one explicit witness at each `t<L` of one of the following two types.

### Jump witness `J_t`

There is a product root `x_t` such that

\[
 v_t=F_r(x_t,v_{t+1}),                                  \tag{1.4}
\]

and `x_t` is exact root Nash at `v_{t+1}`:

\[
 F_r(x_t,v_{t+1})_k\ge
 F_r(x_t[k\leftarrow z_k],v_{t+1})_k                  \tag{1.5}
\]

for every player `k` and every replacement Bernoulli marginal `z_k`.

### Proper flow witness `F_t`

There are an owner `i_t` and `0<p_t<1` such that

\[
 v_t=p_tR_{i_t}+(1-p_t)v_{t+1},qquad
 (v_t)_{i_t}=s_{i_t},                                  \tag{1.6}
\]

and both endpoints are singleton-viable:

\[
 (v_t)_k\ge s_k,qquad (v_{t+1})_k\ge s_k
 \quad(k\in I).                                        \tag{1.7}
\]

The witnesses are retained as part of the word.  Payoff membership in a
convexified image is not a substitute for them.

### Literal execution

Start with an actual tail behavior profile `sigma_L`.

- For `J_t`, prefix the current tail by the single product root `x_t`.
- For `F_t`, choose a mesh width `N_t\ge1`, put

  \[
   q_t=(1-p_t)^{1/N_t},\qquad h_t=1-q_t,                \tag{1.8}
  \]

  and prefix by `N_t` identical roots at which only owner `i_t` Quits, with
  probability `h_t`.

Perform these operations backward from `t=L-1` to `t=0`.  This constructs one
ordinary behavior profile.  No public correlation device and no
transfinite stage are used.

## 2. Semantic error variables

Let an actual continuation profile have semantic pair `(u,b)`, with
prescribed terminal payoff `u` and all-behavior best-response cap `b`.  At a
declared target `y`, define playerwise target error and debt bounds by

\[
 |u_k-y_k|\le e_k,qquad
 0\le b_k-u_k\le d_k.                                  \tag{2.1}
\]

The second inequality covers every complete behavioral deviation, not only a
root marginal or a bounded stopping time.

For scalar bookkeeping let

\[
                   e=\max_k e_k,qquad d=\max_k d_k.     \tag{2.2}
\]

## 3. Exact one-jump error transport

Consider a jump witness from target `y` to `v=F_r(x,y)`.  Let

\[
 \alpha=\Pr_x(\text{all players Continue}),\qquad
 \beta_k=\Pr_x(\text{all opponents of }k\text{ Continue}). \tag{3.1}
\]

Then `0\le\alpha\le\beta_k\le1`.

### Lemma 3.1

If the tail satisfies (2.1), the prefixed profile has semantic pair `(u',b')`
satisfying

\[
                  |u'_k-v_k|\le\alpha e_k              \tag{3.2}
\]

and

\[
 0\le b'_k-u'_k
 \le \beta_kd_k+(\beta_k+\alpha)e_k
 \le \beta_kd_k+2\beta_ke_k.                           \tag{3.3}
\]

#### Proof

The root payoff depends on the continuation only on the all-Continue event,
so

\[
                  u'_k-v_k=\alpha(u_k-y_k),             \tag{3.4}
\]

which gives (3.2).

If player `k` forces Quit at the root, the continuation is irrelevant.  If it
forces Continue, the continuation-cap perturbation has coefficient
`beta_k`.  Exact root Nash says that the declared target value `v_k` is the
maximum of the declared pure-Quit and pure-Continue endpoint values.  Hence

\[
 b'_k-v_k\le\beta_k(d_k+e_k).                            \tag{3.5}
\]

Combining (3.4)--(3.5) gives

\[
 b'_k-u'_k
 \le\beta_k(d_k+e_k)+\alpha e_k,
\]

which is (3.3).  `□`

The weaker scalar recurrence is

\[
                         e'\le e,qquad d'\le d+2e.      \tag{3.6}
\]

Unlike a purely qualitative continuity proof, (3.3) retains the
player-specific opponent-survival contraction needed at an infinite cutoff.

## 4. Exact one-flow-block error transport

Consider a proper flow witness from `y=v_{t+1}` to `z=v_t`, with owner `i`,
mass `p`, and mesh hazard `h` as in (1.8).  The prescribed payoff after the
block is exactly

\[
                         u'=pR_i+(1-p)u,                 \tag{4.1}
\]

so

\[
                    |u'_k-z_k|\le(1-p)e_k.              \tag{4.2}
\]

### Lemma 4.1: owner coordinate

For the owner,

\[
                         0\le b'_i-u'_i\le d_i+2e_i.    \tag{4.3}
\]

#### Proof

Because `p<1`, the active equality in (1.6) implies `y_i=s_i`.  A deviation by
the owner replaces all of its prefix hazards.  It can obtain `s_i` by
quitting or at most `b_i` by reaching and deviating in the tail.  Thus its
cap is at most `max(s_i,b_i)`.  From (2.1),

\[
 \max(s_i,b_i)\le s_i+d_i+e_i,
 \qquad u'_i\ge s_i-e_i,
\]

which proves (4.3).  `□`

The lack of a factor `(1-p)` in front of `d_i` is real: by deleting its own
hazard, the owner can force access to the tail.

### Lemma 4.2: outsider coordinates

For `k\ne i`,

\[
 0\le b'_k-u'_k
 \le\max\bigl\{(1-p)d_k,\ 2Mh+e_k\bigr\}.              \tag{4.4}
\]

#### Proof

Write

\[
 A=r_k(\{i\}),\qquad S=r_k(\{k\}),\qquad
 C=r_k(\{i,k\}).                                       \tag{4.5}
\]

At mesh row `m`, conditional on survival, the ideal remaining value is

\[
 Y_m=(1-q^{N-m})A+q^{N-m}y_k.                           \tag{4.6}
\]

The remaining absorption mass belongs to `[0,p]`, so `Y_m` lies between the
viable endpoints `y_k` and `z_k`; hence `Y_m\ge S`.  Replacing `y_k` by `u_k`
lowers this value by at most `e_k`.  Quitting at that row yields `qS+hC`, so
its conditional gain is at most

\[
                 qS+hC-(S-e_k)\le2Mh+e_k.               \tag{4.7}
\]

Continuing through the block and then deviating in the tail gains
`(1-p)d_k`.  Before absorption the history is only an all-Continue string, so
an arbitrary behavioral deviation is a convex combination of first-quitting
row values and the tail response.  Taking the maximum gives (4.4).  `□`

A safe scalar recurrence following from (4.2)--(4.4) is

\[
                         e'\le e,qquad
 d'\le d+2e+2Mh.                                       \tag{4.8}
\]

## 5. Finite composition theorem

### Theorem 5.1

Let (1.3) carry a compatible length-`L` typed word.  Suppose an actual tail
profile at `v_L` satisfies scalar target error `e_L\le\eta` and debt
`d_L\le\eta`.  Execute every flow witness with mesh hazard `h_t`.  Then the
source profile satisfies

\[
                          e_0\le\eta                    \tag{5.1}
\]

and

\[
 d_0\le(2L+1)\eta
       +2M\sum_{t<L:\,F_t}h_t.                          \tag{5.2}
\]

#### Proof

Apply Lemma 3.1 at every jump and Lemmas 4.1--4.2 at every flow, working
backward.  Each operation weakly decreases scalar target error, while the
safe debt increment is at most `2eta`, plus `2Mh_t` at a flow.  Starting from
`d_L\le eta` gives (5.2).  `□`

### Corollary 5.2: every finite compatible word compiles

If `v_L\in UE(r)`, then `v_0\in UE(r)`.

#### Proof

For each requested error choose a terminal approximate Nash tail whose
semantic pair is `eta`-close to `(v_L,v_L)`.  With `L` fixed, choose `eta` so
that `(2L+1)eta` is small.  For every flow choose `N_t` sufficiently large
that the finite sum in (5.2) is small.  Equations (5.1)--(5.2) give terminal
payoff convergence to the fixed target `v_0` and unrestricted terminal
exploitability tending to zero.  Fixed-target terminal acceptance yields
`v_0\in UE(r)`.  `□`

This is a producer-free compiler theorem.  It does not assert that arbitrary
game data admit such a word or terminal base payoff.

## 6. The requested two-component tests

Write words in chronological source-to-tail order.  Let the terminal pair at
`v_2` have errors `(eta,eta)`.

| Word | Source debt bound | Extra condition |
| --- | ---: | --- |
| `JJ` | `5 eta` | two exact root/tail witnesses |
| `JF` | `5 eta + 2M h_1` | the flow endpoints are viable |
| `FJ` | `5 eta + 2M h_0` | the flow endpoints are viable |
| `FF` | `5 eta + 2M(h_0+h_1)` | both flow segments are proper and viable |

In every row, source target error is at most `eta`.  Thus all four two-letter
orders compile as the tail error and flow mesh hazards tend to zero.

If “two jump/flow components” means two consecutive `JF` blocks, the word is

\[
                         J_0F_1J_2F_3.                  \tag{6.1}
\]

Theorem 5.1 gives

\[
 d_0\le9\eta+2M(h_1+h_3),\qquad e_0\le\eta.            \tag{6.2}
\]

This explicitly tests two roots with two distinct tail targets.  Each root is
kept with the continuation vector at which it is exact Nash; no root is
reprojected to the other component's cap or payoff.

## 7. Why finite induction does not prove an infinite fixed point

The finite theorem always ends at a payoff already in `UE(r)`.  In a greatest
self-generating family, an infinite branch may have no such base.  Letting
`L\to\infty` in (5.2) is useless: its safe bound grows like `2L eta`, and the
tail approximation itself was obtained from the terminal `UE` assumption.

The missing assertion is therefore not “errors can be made small at every
fixed depth.”  It is a boundary theorem that closes payoff and cap semantics
simultaneously at every infinite branch.

## 8. Exact no-go: a compact exact-root self-loop can be a phantom

Take any finite nonempty player set and set every terminal reward coordinate
equal to `-1`:

\[
                         r_k(S)=-1                       \tag{8.1}
\]

for every `k` and nonempty `S`.  Let

\[
                         v_k=1                           \tag{8.2}
\]

for every player, and let `x` be the all-Continue root.  Then

\[
                         F_r(x,v)=v.                     \tag{8.3}
\]

Moreover `x` is exact root Nash at `v`: Continue gives `1`, while forcing
Quit gives `-1`.  Hence the compact singleton `{v}` is postfixed/self-
generating for the payoff-level exact jump operator: its only point has the
displayed continuation back in `{v}`.  (The full jump image may contain other
payoffs; equality with `{v}` is neither needed nor claimed.)

But no actual behavior profile has terminal payoff coordinate `1`.  Every
coordinate is a convex combination of terminal reward `-1` and the Never
payoff `0`, and therefore belongs to `[-1,0]`.  In particular,

\[
                         v\notin UE(r).                  \tag{8.4}
\]

This example proves all of the following.

1. Compactness, exact Bellman equality, exact root Nash, and even singleton
   fibers do not make an infinite self-loop executable.
2. The greatest payoff fixed point of an unrestricted jump operator can
   contain unattainable values.
3. A positive-survival infinite branch needs a real continuation semantic
   pair; it cannot cite its own payoff equation as that continuation.

The example is also singleton-viable, since `1\ge-1`.  Viability does not
repair the boundary.

## 9. The exact finite-dimensional cap transport at a jump

For a player `k`, an exact jump root has opponent survival

\[
 \beta_{t,k}=\Pr(\text{all opponents of }k\text{ Continue})              \tag{9.1}
\]

and exercise premium

\[
 g_{t,k}=\max\{0,Q_{t,k}-C_{t,k}\}.                    \tag{9.2}
\]

On an exact semantic pair whose prescribed coordinate is the root's declared
continuation, prefixing acts on nonnegative tail debt `d` by

\[
 \mathcal B_{t,k}(d)
   =\max\{0,\beta_{t,k}d-g_{t,k}\}.                    \tag{9.3}
\]

This is the checked identity
`quittingTerminalSemanticDebt_prefix_eq_blockAct` in
`UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`, using
`Math.SurvivalWeightedObstruction.Block.act`.

For a finite exact jump prefix, the sharp surviving cutoff debt is the
composition

\[
 \mathcal B_{0,k}\circ\mathcal B_{1,k}\circ\cdots
   \circ\mathcal B_{n-1,k}(D).                         \tag{9.4}
\]

The simpler sufficient estimate

\[
 \mathcal B_{0,k}\circ\cdots\circ\mathcal B_{n-1,k}(D)
 \le D\prod_{t<n}\beta_{t,k}                           \tag{9.5}
\]

discards the premiums.  Equation (9.4), not merely the product in (9.5), is
the exact cap state that an infinite closure must control.

For a singleton-flow macro owned by `i_t`, the limiting opponent-survival
factor is

\[
 \beta_{t,k}^{\rm flow}=
 \begin{cases}
  1,&k=i_t,\\
  1-p_t,&k\ne i_t.
 \end{cases}                                           \tag{9.6}
\]

The owner factor `1` again records that a deviation can delete its own
hazard.  Collision errors from the discrete mesh must be added as a
perturbation of (9.3); they are not part of the algebraic flow arc.

## 10. Compact path selection: necessary structural closure

The faithful state is witness-carrying and two-sorted:

- `Flow(i,v)` retains its owner, mass, selected continuation, and any Flesch
  successor used on a flow-to-flow edge;
- `Jump(v;x,y)` retains the product root `x`, its exact continuation target
  `y`, Bellman equality, and root Nash inequalities.

To obtain an infinite path from finite extendibility by compactness, one needs
the following structural facts.

1. The payoff carrier is compact.
2. The product-root simplex is compact.
3. The jump witness graph is closed.  This follows on a compact payoff
   carrier from continuity of `F_r` and closedness of the exact Nash
   inequalities.
4. The flow witness graph is closed after accounting for endpoint strata.
   The live condition `p<1` is not closed; either impose a uniform live bound
   `p\le1-delta`, or compactify `p=1` as a separately executable terminal
   stratum.
5. Zero-mass `p=0` edges are compact but allow false progress.  A face-
   avoidance, charge-divergence, or rank condition must exclude an infinite
   zero-progress branch.
6. Every finite witness prefix extends inside the same compact tagged
   carrier.

Under these conditions, an inverse-limit/finitely-branching compactness
argument can select a compatible infinite witness path.  The nonconvexity of
jump fibers is not itself a problem for path selection because the witness is
retained.  It is a problem only if one first convexifies and forgets the
witness.

These six items select syntax.  Example (8.1)--(8.4) shows that they do not
yet select an executable semantic boundary.

## 11. Exact payoff and cap closure at infinity

Consider a selected infinite operation path.  Let `alpha_t` be the joint
all-Continue coefficient of operation `t`: for a jump it is the root's joint
survival, and for a flow macro it is `1-p_t`.  Put

\[
                         A_n=\prod_{t<n}\alpha_t.        \tag{11.1}
\]

Assume the target vectors stay uniformly bounded.

### 11.1 Payoff boundary

Finite Bellman substitution gives an exact cutoff term `A_n v_n`.  Therefore
one of the following is required on every infinite branch.

- **Absorbing limit:** `A_n\to0`; the bounded cutoff payoff is erased.
- **Live limit:** `A_n\to A_\infty>0`, and the branch carries an actual limit
  continuation semantic pair whose prescribed coordinate is the required
  limit target.  The prefix alone cannot determine this value.

The phantom self-loop has `A_n=1` and no live-limit continuation, so it fails
exactly here.

### 11.2 Cap boundary

Fix player `k` and a uniform a priori debt bound `D` (for bounded rewards,
`D=2M` suffices for literal terminal pairs).  Ignoring mesh perturbations, the
sharp zero-boundary requirement is

\[
 \mathcal B_{0,k}\circ\cdots\circ
 \mathcal B_{n-1,k}(D)\longrightarrow0.                 \tag{11.2}
\]

The simpler but stronger deleted-player survival condition

\[
                         \prod_{t<n}\beta_{t,k}\to0     \tag{11.3}
\]

implies (11.2).  The exact form (11.2) also permits exercise premiums to kill
debt when (11.3) is inconclusive.

For discrete approximations of flow operations, let `rho_{t,k}` be the local
collision/target perturbation.  Define the perturbed action

\[
 \mathcal B^{\rho}_{t,k}(d)
   =\max\{0,\beta_{t,k}d-g_{t,k}\}+\rho_{t,k}.           \tag{11.4}
\]

The robust cap condition is: at every requested accuracy one can choose all
flow meshes and a cutoff `n` so that

\[
 \mathcal B^{\rho}_{0,k}\circ\cdots\circ
 \mathcal B^{\rho}_{n-1,k}(D)\le\varepsilon
 \quad\text{for every }k.                              \tag{11.5}
\]

This is the exact finite-dimensional formulation of “mesh errors do not
survive the chronology.”  A weighted summable collision budget is a useful
sufficient condition, but (11.5) is the invariant statement.

At a live limit where (11.2) does not hold, the supplied continuation must be
diagonal in the relevant cap coordinate as well as correct in payoff.  A
payoff-only limit is insufficient.

## 12. Positive-survival Zeno limits

An `omega`-long sequence of actual discrete stages has no stage after all of
them.  Thus a new phase after a positive-survival accumulation point cannot
be implemented by literally appending an action at time `omega`.

The uniform-payoff semantics nevertheless allow an accuracy-indexed Zeno
approximation: at accuracy `epsilon`, execute a sufficiently long finite
prefix of the pre-limit phase and switch to the post-limit continuation at a
finite cutoff.  For this to be sound, a **limit-completion rule** must supply:

1. a tagged carrier state `s_lambda` at the positive-survival limit;
2. convergence of the pre-limit declared continuation values to the payoff
   coordinate of `s_lambda`;
3. an attainable semantic pair approaching the diagonal
   `(v_lambda,v_lambda)` for the post-limit continuation; and
4. uniform control of the composed prefix maps so the switch error satisfies
   both (11.1) and (11.5).

At higher nested accumulation orders the same rule is required recursively.
One clean organization is a well-founded ordinal rank: terminal or already
compiled components have rank zero, and a positive-survival limit may point
only to a lower-rank continuation.  A genuinely coinductive same-rank cycle
needs a separate diagonal-semantic-carrier theorem; payoff fixed-point
membership alone is refuted by Section 8.

This is the exact sense in which “component then jump” differs from “jump then
component.”  A jump before a component is one finite prefix.  A jump after an
entire divergent component is invisible because survival is zero.  A jump
after a positive-survival Zeno component requires the four-part limit
completion above.

## 13. A concise infinite certificate interface

The preceding analysis suggests the following supplied-object interface.

An infinite jump--flow execution certificate at target `v_0` consists of:

1. a compact two-sorted witness carrier and closed extendible edge graph;
2. one compatible finite or infinite branch beginning at `v_0`;
3. bounded target values and exact jump Bellman/root-Nash witnesses;
4. proper viable flow witnesses and accuracy-indexed discrete meshes;
5. at every zero-survival branch, payoff erasure (11.1) and playerwise robust
   cap erasure (11.5); and
6. at every positive-survival limit, the four-part diagonal limit completion
   of Section 12.

Given these fields, finite truncation plus fixed-target terminal acceptance
is a plausible direct compiler.  The compiler beyond ordinary natural-number
zero-survival paths is **not proved in this note**.  The point of the
interface is to expose precisely which data compact fixed-point membership
does not provide.

## 14. Proved facts versus open proposals

### Proved here in ordinary mathematics

- The playerwise jump transport inequalities (3.2)--(3.3).
- The playerwise flow transport inequalities (4.2)--(4.4), including the
  unrestricted stopping-time reduction.
- The finite-word error bound (5.1)--(5.2) and finite compiler Corollary 5.2.
- Soundness of all two-letter orders and of the two-component `JFJF` word.
- The compact exact-root phantom self-loop (8.1)--(8.4).
- Necessity of an actual continuation on a positive-joint-survival branch.

### Existing checked facts used as interfaces

- Exact root prefixing of terminal semantic pairs and its continuity in
  `UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`.
- Literal debt block action
  `quittingTerminalSemanticDebt_prefix_eq_blockAct` in that file.
- The fixed-target terminal acceptance theorem in
  `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`.
- The segment/full-prefix distinction in
  `UniformEquilibrium/Quitting/EssentialAPS/Basic.lean` and
  `ConvexProgress.lean`.

### Proposed, not proved

- Arbitrary finite quitting games produce a nonempty compact tagged carrier
  satisfying the infinite certificate interface.
- The unrestricted greatest fixed point of the two-sorted operator is
  executable.
- A well-founded ordinal completion exists for every positive-survival Zeno
  branch.
- Robust block erasure (11.5) follows automatically from essential APS face
  avoidance after arbitrary product-root jumps are added.

## 15. Next concrete question

Prove a `Nat`-indexed zero-survival capstone first:

> A bounded infinite compatible jump--flow path with `A_n\to0`, robust
> playerwise debt-block erasure (11.5), exact jump witnesses, and proper viable
> flow meshes makes `v_0` a uniform-equilibrium payoff.

This avoids transfinite syntax and tests whether (11.5) is the right lifted
invariant.  If it succeeds, the next genuinely new lemma is the
positive-survival limit-completion splice of Section 12.  Compact greatest-
family production should wait until both semantic consumers are proved.
