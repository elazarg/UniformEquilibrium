# Whole-law logit selection on two canonical stress tables

Author: `CODEX_FRECHET_CYCLE`.

Status: two explicit uniform neighborhood exclusions and a uniform local
boundary-family result are proved below as ordinary mathematics. No Lean
check, independent review, export, or exclusion of every remote logit
component is claimed. The known successful approximate families on both
tables cannot be limits of common-temperature, uniform-prior whole-law
logit equilibria. This is a representability failure of this regularizer,
not a counterexample to approximate finite-menu selection.

A structurally changed regularizer now has a positive result on G:
[`CODEX_FRECHET_CYCLE__TIME_PRIOR_LOGIT_GEOMETRIC_PRODUCER.md`](CODEX_FRECHET_CYCLE__TIME_PRIOR_LOGIT_GEOMETRIC_PRODUCER.md)
proves that fixed player-dependent time priors and the joint choice
`τ_N=4^(−N)` yield weighted-logit fixed points with vanishing full regret
and early absorption. This is a single-table mechanism result, not coverage
of arbitrary canonical games.

## 1. Data, mechanism, and bounded source comparison

There are four independent stopping clocks in `ℕ ∪ {Never}`. The first
nonempty quitting coalition absorbs with its specified reward; all Never
pays zero. On `F_N={0,…,N−1,Never}`, let `fᵢ(t;p₋ᵢ)` be the actual
terminal payoff of pure time `t`. For one common temperature `τ>0`, the
whole-law logit equations are

```text
pᵢ(t) = exp(fᵢ(t;p₋ᵢ)/τ) / Σ[u∈F_N]exp(fᵢ(u;p₋ᵢ)/τ).       (L)
```

These are equations for independent laws on actual finite menus, not for
individual root hazards. A fixed point exists by Brouwer. Each solution is
strictly positive on its menu and has menu regret at most `τ log(N+1)`.
That familiar entropy bound is not a new result and does not bound an
omitted pivot date. All conclusions below use the literal payoff equations.

The first table, H, is the canonical table in
[`CODEX_HILBERT__CANONICAL_PIVOT_BOUNDARY_HOMOTOPY.md`](CODEX_HILBERT__CANONICAL_PIVOT_BOUNDARY_HOMOTOPY.md).
For active players `0,1,2`, with predecessor modulo three,

```text
r₀(S) = 1+1[2∈S] if 0∈S, and 3·1[2∈S] otherwise;
rᵢ(S) = 1[i−1∈S] if i∈S, and 3·1[i−1∈S]−1 otherwise (i=1,2);
r₃(S) = 0 if 3∈S, and 1 otherwise.
```

All Never pays zero. The own singleton vector is `(1,0,0,0)` and all
absolute rewards are bounded by three. Its successful infinite profile `σ`
has only owner `i` active at phase `i mod 3`, with hazard `1/2`, and dummy
Never. In particular `σ₀(0)=1/2`, `σ₀(1)=0`.

The second table, G, is the full table in
[`gpt/EXACT_EXAMPLE.md`](../archive/EXACT_EXAMPLE.md), frozen SHA-256
`f4f258367064525d0e890be3a0b66588eb8881eb553a50bda674cbdd378a8079`.
Its seven active-coalition rows are

```text
{0}: (1,7,7), {1}: (7,0,7), {2}: (7,7,0),
{0,1}: (6,8,7), {0,2}: (9,7,5), {1,2}: (7,5,8),
{0,1,2}: (7,6,6).
```

Adding player three does not change these active coordinates; a dummy-only
coalition gives them zero. The dummy receives minus one when it joins an
active coalition, one when it is absent and player one or two quits, and
zero otherwise. Its successful infinite profile `γ` has only the pivot
active, with geometric law `γ₀(t)=2^(−t−1)`, all other players Never.
The reward bound nine is valid. Thus `γ₀(0)=1/2`, `γ₀(1)=1/4`.

For product laws on these countable clocks write
`d(p,q)=Σᵢ TV(pᵢ,qᵢ)`. In particular every atom difference is bounded
by `d`. Bounded payoff coupling gives

```text
|fᵢ(t;p₋ᵢ)−fᵢ(t;q₋ᵢ)| ≤ 2M d(p,q),                       (TV)
```

uniformly over all pure dates, including Never. No weak-topology payoff
continuity is assumed.

The route was chosen in `docs/TOOLKIT.md` through the actual finite timing
menu declarations. `quittingFiniteDeadlineTimingGame`,
`quittingFiniteDeadlineTimingProfile`, and
`quittingTerminalPayoff_finiteDeadlineTimingProfile_eq_mixedEU` in
`UniformEquilibrium/Quitting/Terminal/FiniteDeadlineTimingGame.lean` were
inspected, as was `timingLawTail_isNash_of_isNash_of_positiveContinue` in
`UniformEquilibrium/Diagnostics/Quitting/FiniteDeadlineTimingRecursion.lean`.
The exact production barrier and the two stress-table proofs are compared
in the separate intake review
[`EXACT_EXAMPLE__BY_CODEX_FRECHET_CYCLE.md`](../feedback/EXACT_EXAMPLE__BY_CODEX_FRECHET_CYCLE.md).

A narrow search for entropy, logit, softmax, and Gibbs in conference notes,
questions, and the chosen source neighborhood found no whole-law theorem
covering the claims below. The relevant existing no-gos are different:

- `CODEX_CEDAR__DISCOUNTED_RADIAL_DEBIASING.md` computes the unrestricted
  refusal cost of repeating a discounted stationary Bellman root.
- `CODEX_SPINOZA__FIXED_PERIOD_SOFT_PHASE_SPLITTING_RIGIDITY.md` concerns
  fixed-period root-logit cycles in a vanishing-hazard positive-clearance
  regime. `CODEX_SPINOZA__GROWING_PERIOD_HAZARD_CLOCK_AND_REPLICATOR_BOUNDARY.md`
  extends that root/cyclic setting.
- `CODEX_SPINOZA__E2_FINITE_DEADLINE_APPROXIMATE_CHANNEL.md` records logit
  continuation as numerical discovery for a different table and a fixed
  rational error certificate, not this selection theorem.

No paper-priority claim is made. The proofs below are elementary properties
of the displayed tables and equations (L).

## 2. Exact exclusion near the periodic H witness

**Theorem H.** For every `N≥2` and `0<τ≤1/64`, no solution of (L) for H,
embedded as a complete finite-clock law, satisfies `d(p,σ)≤1/48`.

First, at the explicit profile `σ`,

```text
f₁(Never;σ₋₁)=1,       f₁(0;σ₋₁)=1/2,
f₃(Never;σ₋₃)=1,       f₃(0;σ₋₃)=0.                        (H1)
```

For the first Never calculation, after deleting player one each period has
owner-zero absorption mass `1/2`, owner-two mass `1/4`, and survival `1/4`.
The corresponding player-one rewards are two and minus one, giving
`[(1/2)·2+(1/4)·(−1)]/(1−1/4)=1`. Quit0 pays one exactly when the pivot
also quits, probability `1/2`. The dummy calculations follow because its
Never reward is one under almost-sure active absorption, while every
coalition including the dummy pays it zero.

If `d(p,σ)≤1/48`, (TV) with `M=3` shows that each difference between a
Never payoff and a Quit0 payoff changes by at most `12/48=1/4`. Therefore
both players one and three strictly lose at least `1/4` by Quit0 rather
than Never. Their exact logit odds imply

```text
p₁(0) ≤ exp(−1/(4τ)),       p₃(0) ≤ exp(−1/(4τ)).             (H2)
```

The following payoff inequality holds for every opponent product law,
without closeness or equilibrium assumptions:

```text
f₀(1;p₋₀)−f₀(0;p₋₀) ≥ −p₁(0)−p₃(0).                    (H3)
```

Indeed if the opponents first quit at date zero, waiting instead of joining
changes the pivot reward by `2·1[2 quits at zero]−1`. Its negative part
therefore requires player one or three to quit at zero. If opponents first
quit at date one, joining them instead of quitting alone at zero changes
the reward by `1[2 quits at one]`, which is nonnegative. If they first quit
later or never, the two pivot choices both pay one. This exhausts all cases.

Combine (L), (H2), and (H3):

```text
p₀(1)/p₀(0) ≥ exp(−2 exp(−1/(4τ))/τ).                      (H4)
```

The elementary inequality `exp(x)≥x²/2` gives
`exp(−1/(4τ))≤32τ²`. Thus for `τ≤1/64`, the ratio in (H4) is at least
`exp(−1)>1/3`. But total-variation proximity requires

```text
p₀(0) ≥ 1/2−1/48 = 23/48,       p₀(1) ≤ 1/48,
```

and hence the ratio is at most `1/23`. This is a contradiction.

The conclusion is uniform over menu size and every logit fixed point,
including any remote connected component. Since the three active tails of
the `3m`-date truncation each have mass `2^(−m)`, those known successful
approximate laws converge to `σ` in total marginal TV at rate `3·2^(−m)`.
No common-temperature logit sequence with `τ→0` can approximate this family
in that metric, irrespective of how `N` and `τ` are selected jointly.

This does not exclude some other family of logit equilibria with low full
regret and a different limiting strategy.

## 3. Exact exclusion near the geometric G witness

**Theorem G.** For every `N≥2` and `0<τ≤1/256`, no solution of (L) for G
satisfies `d(p,γ)≤1/144`.

At the explicit geometric profile,

```text
f₂(Never;γ₋₂)=7,        f₂(0;γ₋₂)=5/2,
f₃(Never;γ₋₃)=0,        f₃(0;γ₋₃)=−1/2.                    (G1)
```

With `M=9` and distance at most `1/144`, the payoff-gap perturbation is at
most `36/144=1/4`. Both gaps in (G1) therefore remain at least `1/4`, so
`p₂(0),p₃(0)≤exp(−1/(4τ))`.

The table gives, for arbitrary opponent laws,

```text
f₀(1;p₋₀)−f₀(0;p₋₀) ≥ −2p₂(0)−p₃(0).                    (G2)
```

When opponents first quit at zero, waiting rather than joining changes the
pivot payoff by one for active set `{1}`, minus two for `{2}`, zero for
`{1,2}`, and minus one for a dummy-only coalition. Adding a dummy to a
nonempty active set does not change these differences. When opponents first
quit at one, joining always pays the pivot at least its own singleton one.
The remaining cases give equal payoffs. This proves (G2).

The pivot's logit ratio is consequently at least
`exp(−3 exp(−1/(4τ))/τ)≥exp(−96τ)≥1−96τ≥5/8`.
Yet the assumed proximity gives

```text
p₀(1)/p₀(0) ≤ (1/4+1/144)/(1/2−1/144) = 37/71 < 5/8.
```

Again there is a contradiction. The known geometric approximate laws
therefore cannot be represented asymptotically by this regularizer either.
The negative conclusion concerns all nearby common-temperature logit
solutions, not merely a selected defective branch.

## 4. A uniform theorem for the nearest-exact logit selector

This secondary result explains the observed defective local family without
mistaking fixed-deadline cooling for joint selection.

Let `p^N` be the unique exact finite-menu law for H: only the last date and
Never are used, with active Quit probabilities `(1/3,1/4,1/2)` and dummy
Never. Its payoff is `(3/2,1/3,1/4,3/4)` and full defect is `3/8`.
Every earlier active action has payoff gap below Never at least `δ=1/4`;
every dummy finite action has gap `3/4`. These bounds do not depend on N.
At the retained last-date/Never support, the indifference Jacobian at this
equilibrium is

```text
J_H = [0    0     −2;
       −3/2 0      2/3;
        3/4 −4/3   0],             det J_H = −4.             (JH)
```

There are constants `C,r>0`, independent of N, such that whenever
`τ+4N exp(−1/(8τ))<r`, a logit fixed point `p` exists with

```text
d(p,p^N) ≤ C[τ+4N exp(−1/(8τ))].                            (B)
```

Here is the uniform construction, including why growing dimension does not
hide a constant. Use three variables `yᵢ` for the conditional last-date
probabilities within each active player's retained support. Let `z` contain
all earlier active atoms and all finite dummy atoms. For active player i,
put `pᵢ(last)=(1−Σzᵢ)yᵢ` and `pᵢ(Never)=(1−Σzᵢ)(1−yᵢ)`; the dummy's
Never mass is `1−Σz₃`.

The three supported logit equations are

```text
fᵢ(last)−fᵢ(Never) = τ log(yᵢ/(1−yᵢ)).
```

Near `(y*,z,τ)=(y*,0,0)`, their y-Jacobian is (JH). A uniform implicit
solution `y=y(z,τ)` exists and obeys `|y−y*|≤C(τ+||z||₁)`.
To justify uniformity directly, these payoffs are multilinear expectations
of a bounded table. On an ℓ¹ ball their first and second derivatives have
operator bounds depending only on the four players and the reward bound,
not on the number of actions. The above coordinate chart has the same
property. The map `y ↦ y−J_H⁻¹F(y,z,τ)` is thus a contraction on one fixed
small three-dimensional ball when `τ+||z||₁` is sufficiently small.
This proves both the implicit solution and its stated uniform estimate.

Take `η=4N exp(−1/(8τ))` and the compact convex set `z≥0`, `||z||₁≤η`.
If `τ+η` is small enough, every off-support payoff gap from Never is at
most `−δ/2=−1/8`. Let `Eᵢt=exp((fᵢ(t)−fᵢ(Never))/τ)`. Map each active
off-support block to

```text
Tᵢt(z) = (1−yᵢ)Eᵢt / [1+(1−yᵢ)Σ[u off support]Eᵢu],
```

and the dummy block to `T₃t=E₃t/(1+ΣE₃u)`. This continuous map has total
mass at most `4N exp(−1/(8τ))=η`, so Brouwer gives a fixed point. At that
point the normalization and the three supported odds equations give exactly
all the whole-law equations (L). Its distance bound is (B).

The same argument applies to G with its unique last-date exact equilibrium,
where

```text
J_G = [0 −2 1; 1 0 −2; −2 1 0],     det J_G = −7,
δ_G = 31/49,
d(p,p^N_G) ≤ C_G[τ+4N exp(−31/(98τ))].                       (BG)
```

The smallest off-support gap is the early dummy gap `31/49`; its last-date
gap is larger. The active earlier gaps are `24/7,19/7,34/7`.

Define the nearest-exact selector to minimize `d(p,p^N)` over all logit
fixed points for the chosen `N,τ`. The fixed-point set is nonempty and
compact, so a minimizer exists. Bounds (B)/(BG) apply to every such minimizer.
For every joint sequence `τ_k log(N_k+1)→0`, we have `τ_k→0` and
`N_k exp(−c/τ_k)→0` for each fixed `c>0`. Thus this genuinely approximate
selector has vanishing menu regret while its full defect tends to `3/8`
on H and `18/49` on G. The full-debt limit follows from uniform bounded-payoff
coupling to the exact law, before taking the maximum over pure deviations.

This rules out the specified nearest-exact selector under joint scaling.
It does not identify every connected component, and it does not prove that
continuation from high temperature always stays near this local family.

## 5. Experiment record and next mechanism

The numerical discovery script is
[`CODEX_FRECHET_CYCLE__LOGIT_STRESS_TEST.py`](CODEX_FRECHET_CYCLE__LOGIT_STRESS_TEST.py).
Reproduction commands are

```text
python notes/CODEX_FRECHET_CYCLE__LOGIT_STRESS_TEST.py --table hilbert --dates 1 2 4 8 16
python notes/CODEX_FRECHET_CYCLE__LOGIT_STRESS_TEST.py --table exact --dates 4 8 16
```

It uses NumPy Newton iteration on exact finite-menu payoff polynomials and
prints the full extra-date cap, Never atoms, and the logit residual. It
found the defective small-temperature family for the smaller deadlines.
At N=16 ordinary continuation failed its residual check near intermediate
temperature on both tables. That is inconclusive about remote components;
the script does not relabel a failed root solve as a fixed point. All
numerical values are discovery diagnostics. The theorems above are proved
independently and do not rely on these runs.

The next mechanism changed the regularization itself: the linked time-prior
note proves an actual positive weighted-logit selector for G. For H, an
explicit support-selection mechanism or another nonlocal approximate
optimization remains to be developed.
Theorems H and G identify the exact restriction such a replacement must
avoid: exponentially suppressed strict mistakes by opponents cannot generate
the finite odds between a player's equal-valued nearby stopping times.
No new actual-data producer for arbitrary canonical tables is claimed.
