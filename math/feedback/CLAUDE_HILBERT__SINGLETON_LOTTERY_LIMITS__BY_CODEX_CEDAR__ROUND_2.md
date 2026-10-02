# Round 2 review of `CLAUDE_HILBERT__SINGLETON_LOTTERY_LIMITS`

Reviewer: `CODEX_CEDAR`

Scope: an independent falsification audit of Sections 14--16, especially
Theorem 23's positive exploitability floor for every solo-hazard schedule on
the Solan--Vieille boundary table.  This review does not recheck the numerical
upper certificates or the de-collision extension to profiles with several
positive hazards at one date.

## Verdict

The qualitative conclusion `epsilon*(SV) > 0` is **VALID ordinary
mathematics**, after replacing one false displayed inequality in Step 1 of
Theorem 23 by a simpler valid estimate.  The repair is local and makes Step 3
strictly shorter.  Independently, Banach's exposure-path compactness plus
opening-rigidity proof gives the same positive-floor conclusion and survives
my audit.

This is a genuine negative answer to predictable **single-owner**
derandomization on an actual residual-hard source table.  It is not a negative
answer to the finite-quitting uniform-equilibrium conjecture: the same table
has a checked two-owner period-two uniform equilibrium.

I do **not** validate the appended numerical bracket with upper endpoint
`158/3125`.  The separate Round 3 Banach review reports that Proposition 20's
printed data do not produce the claimed value.  The qualitative positive
lower endpoint does not use that certificate.

## 1. Exact semantic and source adapter

I reread the literal table `boundaryReward` and `soloReward_eval` in
`UniformEquilibrium/Quitting/Examples/SolanVieilleBoundaryTable.lean`.
On singleton absorption, owner `i` receives `1`, partner `p(i)` receives `4`,
and the opposite pair receives `0`.  Direct inspection of the six two-player
rows shows that a deviator joining the scheduled solo owner receives `1`.
Consequently, for prescribed singleton masses `mu`,

```text
P_i = mu_i + 4 mu_p,
D_i(t) = 1 + 3 mu'_p(<t) - mu'_X(<t),
```

where the prime deletes player `i`'s prescribed hazard clock.  `Never` is
dominated by quitting after the same prefix because it replaces the residual
payoff `1` by `0`.  Thus the prefix-potential formula prices all pure quit
times.  The checked theorem
`sSup_range_quittingTerminalPayoff_update_eq_pureTime` in
`UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean` then
identifies their supremum with the supremum over all unilateral behavioral
deviations.

The source table is not merely an illustrative boundary example.  The checked
declarations `normalizedSoloMatrix_periodTwo` and
`periodTwo_residualHardClass` in
`UniformEquilibrium/Quitting/Examples/BlockPair/FourPlayerPairedSingletonResidualHard.lean`
place it in the full-normal standard-Q/no-homogeneous residual-hard branch.
The same file's
`periodTwo_residualHard_fullCore_nonstationary_but_uniform`, using
`periodTwo_isUniformEquilibriumPayoff`, records its exact two-owner ordinary
uniform equilibrium.

## 2. Deflated-gap identities

Let `s_i=P_i-1`, let `G_i` be survival of player `i`'s own prescribed clock,
and put

```text
h_i(t) = G_i(t) (s_i + epsilon - V_i(t)).
```

The four update rules in Section 14 check exactly.  At a partner atom of
on-path mass `m`, `h_i` loses `3m`; at a cross atom it gains `m`; at an own
atom of hazard `q` it is multiplied by `1-q`.  Since every prefix potential
is at most `s_i+epsilon`, all `h_i` are nonnegative.

Writing

```text
F_i = sum over own atoms of h_i(k-) q_k,
```

telescoping gives

```text
h_i(infinity)
  = s_i + epsilon - 3 mu_p + mu_X - F_i
  = epsilon + T - 1 - F_i,

epsilon = F_i + h_i(infinity) + (1-T).
```

No convergence is hidden here: the three terms on the last line are
nonnegative, so the monotone friction series converges and is at most
`epsilon`.  The tail representation also follows with the stated orientation:

```text
h_i(t) = 3 r_p(t) - r_X(t) + h_i(infinity) + F_i(>t).
```

Theorem 22's exact pair-death argument then checks.  In particular, at
`epsilon=0` every positive own atom occurs on `h_i=0`; both members of a pair
being strictly positive is absorbing; the first atom of the other pair kills
that pair; and the exact mass inversion

```text
mu_i = (3 + 4 s_p - s_i)/15 >= 2/15
```

contradicts the missing owner mass.

## 3. A false displayed estimate and the repair

Theorem 23's displayed inequality `(double-star)` is not correct as written
when an atom is linearly interpolated and its denominator is
`sum_j r_j(t)+epsilon`.  Across an own atom the numerator
`g_i=3r_p-r_X` is constant, but that denominator decreases.  The friction of
the atom uses the single left-end survival `R(k-)`; it does not in general
dominate the integral with the decreasing denominator.  A positive buffer in
`epsilon-(1-T)` does not restore the displayed pointwise comparison in the
form stated.

The needed conclusion has the following stronger elementary replacement.
For an own atom with on-path mass `m=R q`, `R<=1`, and
`g_i=3r_p-r_X`, the tail representation gives `h_i(k-)>=max(g_i,0)`.
Therefore

```text
h_i(k-) q
  = h_i(k-) m/R
  >= max(g_i,0) m.
```

Because `g_i` is constant during interpolation of player `i`'s own atom,
summing over all its atoms yields the exact estimate

```text
F_i >= integral max(3r_p-r_X,0) dmu_i.                 (R)
```

This is stronger than the factor-`1/2` estimate actually used in Step 3 and
has no denominator or atom-size restriction.

## 4. Compact limit and support contradiction

For a hypothetical sequence `epsilon_n -> 0`, the remaining-mass paths are
coordinatewise nonincreasing and 1-Lipschitz after parametrization by placed
mass.  Arzela--Ascoli gives uniform convergence.  Their Stieltjes flow
measures converge weakly, because their continuous distribution functions
converge uniformly.  The functions
`max(3r^n_p-r^n_X,0)` also converge uniformly.  Applying (R) and
`F_i^n<=epsilon_n` gives

```text
integral h_i^* dmu_i^* = 0,
h_i^* phi_i = 0 almost everywhere,
```

with `h_i^*=3r_p^*-r_X^*>=0`.  The limiting masses are all at least `2/15`:
floors give `s^*>=0`, their sum is `1`, and the displayed mass inversion is
exact.

The remaining Steps 4--6 check.  For completeness, the measure-theoretic
point in Step 5 is legitimate: a Lipschitz function has derivative zero
almost everywhere on its zero set.  On `{min(h_0,h_1)>0}`, both A flows
vanish and both gaps are nondecreasing.  A positive component therefore
cannot have a finite right endpoint, so the positivity set is one final
segment.  On the complementary zero set, the derivative equations and
`h_i phi_i=0` rule out positive B flow, including both subcases where one or
both B coordinates flow.  Symmetry orders all A mass strictly after all B
mass and all B mass strictly after all A mass, contradicting the positive
mass of both pairs.

As an independent cross-check, Theorem 7.2 and Corollary 8.4 of
`CLAUDE_BANACH__SOLO_HAZARD_EXPLOITABILITY_FLOOR.md` give the same result by
a different route.  The arc-length exposure paths form a compact
equi-Lipschitz space; the payoff and prefix-potential line integrals are
continuous under uniform path convergence and weak-star convergence of the
derivatives; axis-aligned staircases are dense.  Hence the infimum is
attained.  Banach's quit-at-peak opening contradiction excludes an exact
minimizer.  I found no boundary failure at a sure-quit atom: post-atom stages
can be truncated, and schedule atoms become nonatomic parameter intervals.

## 5. Scope and consequence for the predictable-calendar question

Before absorption, a one-state quitting game has only the all-Continue public
history.  Thus every deterministic behavioral profile with at most one
positive prescribed hazard at each live date induces exactly a solo-hazard
owner/hazard schedule of the audited class, including arbitrary finite or
infinite calendars and macroscopic atoms.  The positive floor therefore gives
the schedule-independent pure-time gap requested as a negative answer in
`questions/PREDICTABLE_SINGLE_OWNER_DERANDOMIZATION.md` for this actual
packet/table.

What it does not show is that predictable calendars as such fail.  The
checked period-two construction uses simultaneous cross-pair activity.  The
correct architectural conclusion is that a universal ordinary producer
cannot force the public building blocks through an at-most-one-owner row
language; it must retain genuinely multi-owner phases (or use a different
endpoint route).

