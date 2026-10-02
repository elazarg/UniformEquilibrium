# Attained geometric MAX minima: response escape and the remaining joint test

Author: `CODEX_FRECHET_CYCLE`.

Status: bounded research checkpoint, paused at the user's request. The
one-coordinate response-escape statement below is proved. A contradiction
to finite-head/geometric-pivot attainment is **not** proved. No example
with positive unrestricted global minimum is constructed. No export,
commit, or Lean work is part of this checkpoint.

## 1. Exact question and hypotheses

Fix an arbitrary canonical Fin4 quitting table with own-singleton vector
`s=(1,0,0,0)` and bounded nonempty-coalition rewards. Players use independent
stopping laws on `ℕ∪{Never}`; the first finite stopping coalition receives
its reward, and all-Never pays zero. Every unilateral behavioral law is
allowed. Define prescribed payoffs U, full response caps B, nonnegative
debts `d_i=B_i−U_i`, and `E=max_i d_i`.

Let

```text
m=inf{E(p):p is any actual independent product stopping-law profile}.
```

The test supposes **both** that m>0 and that an actual profile p attains
it, with all three nonpivot laws supported on
`F_N={0,…,N−1,Never}` and a literal pivot law consisting of a finite head,
a geometric tail starting at N, and possibly Never. Its geometric tail
has positive hazard when its finite mass is positive; the relaxed
`α=0<λ` coordinates do not count as actual attainment.

The goal was to contradict these hypotheses by a genuinely joint calendar
enlargement, without supplying an equilibrium tail or replacing global
optimization by exact finite-menu Nash selection. This goal is still open.

An attained unrestricted minimum of this shape would satisfy `m_N=m`
for the complete geometric-repair minimum, and `m_L=m` for every L≥N.
The converse assertion is not assumed: an arbitrary positive m_N optimizer
need not be unrestricted-global, and a relaxed optimizer need not be an
actual law.

The strengthened MAX results imply at the hypothesized p that

```text
d_i(p)=m for every i,
U_i(p)−s_i≥m²/(64M)>0 for every i.
```

The full frozen all-coordinate tie proof was read independently at
SHA `42cf56a4a354823a3a17e379715dac61bd6c1ccd62aeb277bb32b99844a06166`;
the resulting explicit PASS is recorded in
[`feedback/CODEX_HILBERT__GLOBAL_MAXIMUM_MINIMUM_ALL_PLAYER_TIES__BY_CODEX_FRECHET_CYCLE.md`](../feedback/CODEX_HILBERT__GLOBAL_MAXIMUM_MINIMUM_ALL_PLAYER_TIES__BY_CODEX_FRECHET_CYCLE.md).
The strict-margin proof is the separately frozen owned note
`CODEX_FRECHET_CYCLE__GLOBAL_REPAIR_LOWERED_ROOT_MARGIN_TEST.md`.

## 2. Proved: every profitable one-law move leaves the global minimum

This fact only needs actual global attainment and the all-coordinate tie
theorem; it does not need the geometric shape or response attainment.

Fix player k and any replacement law τ_k whose payoff against p_-k
exceeds U_k(p) by some G>0. For `0<θ≤1`, change only that player's law to

```text
p^θ_k=(1−θ)p_k+θτ_k.
```

Its cap is unchanged, so its new debt is exactly

```text
d_k(p^θ)=m−θG<m.
```

If `E(p^θ)≤m`, global minimality would make p^θ another actual global
minimum. The all-coordinate tie theorem would then give
`d_k(p^θ)=m`, a contradiction. Therefore

```text
E(p^θ)>m for every θ>0.                                  (EXIT)
```

In particular, an exact full best reply has G=m and debt `(1−θ)m`, and
every partial mixture toward it strictly raises the maximum regret.
The error-free response endpoint has owner debt zero but is strictly
off minimum. This is not merely coordinate stationarity at an arbitrary
profile: the proof uses the unrestricted global value and the tie theorem
at every hypothetical global minimum.

Thus the failed implication is exact:

```text
actual global attainment + full-response attainment
    DOES NOT supply a same-minimum one-player purification chain.
```

Under the positive-minimum hypothesis, every profitable first step of that
proposed chain instead satisfies (EXIT). An off-minimum endpoint alone is
not a contradiction and is not an improving competitor.

## 3. Complete finite testers for a literal simultaneous response cube

For the actual geometric source, each full cap is attained in
`D_N={0,…,N,Never}`. The pivot's late finite payoff against finite
opponents is constant from N onward. A nonpivot's late geometric-response
payoffs are convex combinations of its Quit-N and Never payoffs. These
are the exact full-cap formulas already proved in the frozen repair note.

Select one pure complete best reply τ_i∈D_N for each player. The genuinely
simultaneous test is the product family

```text
p_i(x_i)=(1−x_i)p_i+x_iτ_i,       x_i∈[0,1],
p(x)=∏_i p_i(x_i).
```

All four private mixtures may change at once; there is no correlated
mixture of whole profiles and no two-player restriction inferred from
the number of maximal debts.

At every point x of this cube, all nonpivot laws are supported on
`{0,…,N,Never}`. The pivot's head may acquire date N; its tail strictly
after N remains a scaled copy of the original geometric tail. Therefore
the **same** finite pure tester set

```text
H_N={0,…,N+1,Never}
```

attains all four unrestricted caps at every x. This includes empty-tail
and zero-coordinate cases. The cube's full regret is consequently the
maximum of finitely many multiaffine fixed-response gain functions in x.
It is a genuine finite optimization with full, not menu-only, verification.

If the hypothesized source is globally minimal, its cube minimum equals
m because x=0 is available. Every other cube point reaching this value
must also have all four debts equal to m; every nontrivial coordinate
edge toward τ_i has larger value by (EXIT). No sign argument found here
forces an interior cube point below m. That missing implication is not
silently replaced by coordinate convexity or by a convex mixture of the
sixteen whole-profile corners.

## 4. Why finite Nashification does not close this test

One can form the finite game in which player i's two actions are its
original complete law p_i and its selected response τ_i. That finite
game has a mixed Nash equilibrium, but its allowed actions are not the
complete tester set H_N. At any such restricted equilibrium, unrestricted
global minimality still gives E≥m>0; some pure tester in H_N therefore
has gain at least m, although no allowed portfolio action is profitable.
This precisely identifies the unverified response comparison in the
finite-game shortcut.

Adding all pure testers to the portfolios is a lawful new experiment,
not a proof of closure. It can put nonpivot mass at the new frontier
N+1, after which the same shape calculation guarantees complete testers
only through N+2. The calculation does not assert that the newly allowed
date is always profitable; it says that a uniform response-closure proof
has not been obtained from source cap attainment alone. Repeating this
enrichment needs a genuine value decrement or a completeness argument.

The previously audited canonical H finite-menu examples already warn
against identifying finite Nash selection with small unrestricted regret.
They have unrestricted global infimum zero, so they are not counterexamples
to the positive-global-attainment hypothesis here. No known successful
periodic H tail is supplied to the present test.

## 5. Narrow source check and exact stopping point

The TOOLKIT finite-clock purification and pure-time response rows were
used to select the following source, not to survey the Lean tree:

`deadlineBoundedMinimum_purify_or_offMinimum_with_step_bound` in
`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/FiniteClockMinimumPurification.lean`.

Its imports, exact-cap replacement definition, minimum-fiber chain
definition, and complete named declaration/proof were inspected. It
assumes a minimum of **total** debt, and explicitly permits an off-minimum
target. It neither excludes actual minimum attainment nor supplies a
global MAX same-minimum purification. The complete conference note
`PAIRED_HULL_REVIEW__ARBITRARY_CLOCK_PURIFICATION_TO_OFF_MINIMUM_PORT.md`
was also read; it sends a retained SUM-minimum source to an off-minimum
paid port and expressly does not consume that port.

No mathematical content from the new user submission `gpt/ACTUAL.md`
was used. HILBERT performed its independent intake separately; his brief
message identified its SUM-versus-MAX distinction, not an attainment
resolution for this test.

Strongest rigorous checkpoint: (EXIT), the common unrestricted tester
alphabet for the simultaneous cube, and the exact failure of finite
Nashification to verify those testers. No coordinated improvement below
m, no impossibility of geometric attainment, and no positive-minimum
counterexample is claimed.

Next test, if research resumes: analyze a truly joint cube/portfolio
enlargement that controls every H_N response while permitting all four
laws to change, or establish a special geometric-tail condition that
forces one cube minimum below its global source value. It must provide
an actual product-law competitor, not another off-minimum response port.
This candidate is unproved and is left separate from the proved facts.
