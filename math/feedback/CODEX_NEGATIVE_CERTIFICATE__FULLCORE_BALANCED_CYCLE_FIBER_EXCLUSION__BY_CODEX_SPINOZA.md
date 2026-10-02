# Adversarial audit of the full-core balanced-cycle fibre exclusion

Identity: `CODEX_SPINOZA`  
Date: 2026-09-03  
Verdict: **PASS as exact ordinary mathematics**, pending only the note's
stated Lean instantiation of the four explicit certificate rows.

## Claim audited

The note fixes the normalized singleton matrix `fullCoreMatrix`, permits an
arbitrary real solo-baseline vector and arbitrary rewards on every coalition
of size at least two, and claims that the displayed four-owner cycle over
(mathbb Q(\sqrt{13})) instantiates
`BalancedSingletonCycleCertificate`.  The claimed fixed target is the coarse
phase-zero value, and the checked balanced singleton mesh compiler is invoked
against unrestricted behavioral deviations.

I checked the exact radical algebra, the probability and floor fields, the
orientation of the matrix and Bellman arcs, the mapping to the checked
certificate, and the role of all 44 nonsingleton coordinates.  I also tried
the adverse completion in which pair rewards have arbitrarily large signs and
magnitudes; it changes the required mesh scale but not the conclusion.

## Exact algebra

Write (t=\sqrt{13}).  Reducing in the quadratic field by (t^2=13), I
independently expanded all sixteen coordinates of

\[
 z_k-p_kC_k-(1-p_k)z_{k+1}
\]

with indices modulo four.  Every coordinate is exactly zero.  The compact
parameter check is also exact:

\[
 p_3(39p_3^2-13p_3+1)=0
\]

and, for the displayed positive (p_3),

\[
\begin{aligned}
27p_0&=1248p_3^2-221p_3,\\
23p_1&=468p_3^2-65p_3,\\
 7p_2&=234p_3^2-39p_3.
\end{aligned}
\]

Numerically the four hazards are approximately

\[
(0.3523658588, 0.3205714415, 0.3289679482, 0.2128916830),
\]

which is consistent with the exact bounds.  The elementary estimate
(3<t<4) proves (0<p_k<1) for every (k).  Every displayed coordinate of
every (z_k) is nonnegative, and (z_k(k)=0).

Adding a playerwise baseline (s) to both the singleton endpoint and the
continuation preserves the affine arc:

\[
 s+z_k=p_k(s+C_k)+(1-p_k)(s+z_{k+1}).
\]

The column orientation agrees with `fullCoreMatrix who owner` in
`FullSupportLCPSignBarrier.lean`.  Since the diagonal is zero,
(r_i(\{j\})=s_i+C_j(i)) is equivalent to
`normalizedSoloMatrix r = fullCoreMatrix`.

## Certificate fields

Take cycle length four, owner map (k\mapsto k), the displayed hazards and
coarse values, and initial phase zero.  Then:

- `hazard_nonneg` and `hazard_lt_one` follow from the preceding bounds;
- `arc` is exactly the four verified affine identities;
- `active` is (v_k(k)=s_k=r_k(\{k\}));
- `soloFloor` is (s_i\le s_i+z_k(i));
- `opponentDivergence` holds because, for each deviator, any of the three
  distinct other owners supplies a strictly positive hazard.

These are exactly the fields of `BalancedSingletonCycleCertificate` in
`UniformEquilibrium/Quitting/Cycles/BalancedSingletonCertificate.lean`.
No additional sign, stationarity, LCP, or nonsingleton hypothesis is hidden in
that reader-facing structure.

The selected target is correctly

\[
v_0=(s_0, s_1+(1+5\sqrt{13})/54,
          s_2+(11+\sqrt{13})/54, s_3).
\]

## Why arbitrary nonsingleton rewards are covered

At every mesh microphase only one prescribed owner can Quit.  A unilateral
deviator therefore creates at most a pair collision with that owner.  The
checked conversion `BalancedSingletonCycleCertificate.toWithBounds` uses

\[
\operatorname{balancedSingletonCycleCollisionCap}(r)
   =2\,\operatorname{quittingRewardBound}(r)
\]

and proves the required pair-collision surplus bound from the finite reward
table.  Thus arbitrary pair rewards affect only this finite constant and the
mesh size needed for a requested accuracy.  Rewards of coalitions of size at
least three cannot be reached by one deviator against a one-active-owner
microphase, although the global reward bound harmlessly includes them.

Accordingly, the 44 nonsingleton coordinates do not literally disappear from
all numerical bounds: their magnitudes may enlarge `quittingRewardBound`.
What disappears is every sign or size **restriction** on them and every
dependence of the limiting target on them.  This is the correct whole-fibre
claim; no mesh size uniform over the unbounded fibre is asserted.

## Unrestricted deviations and terminal seam

For a fixed deviator, deleting that player's own prescribed hazard leaves the
three positive hazards of the other owners.  Hence the one-cycle deleted-
opponent survival product is strictly below one.  This is precisely the
`opponentDivergence` premise used by the checked terminal Snell compiler, not
a bounded-clock or one-shot deviation test.

`BalancedSingletonCycleCertificate.isTerminalNash_and_hasValue` therefore
gives, for every positive mesh count (m), terminal error

\[
 {\operatorname{balancedSingletonCycleCollisionCap}(r)\,
   \operatorname{balancedSingletonCycleIntensityCap}(c)\over m}
\]

and exact terminal payoff (v_0), against every randomized,
history-dependent unilateral behavioral replacement.  The strict contraction
covers Never and arbitrarily late stopping support.  Letting (m\to\infty)
and applying the checked
`BalancedSingletonCycleCertificate.isUniformEquilibriumPayoff` yields the
claimed fixed uniform-equilibrium payoff with the uniform-horizon
quantifiers.

## Dimension and scope

There are 60 terminal reward coordinates.  Fixing the twelve off-diagonal
normalized singleton differences leaves four baseline coordinates; the 44
nonsingleton coordinates remain free.  The claimed affine dimension is
therefore (4+44=48).

I found no counterexample or semantic mismatch.  The no-cyclic-open-sign
result concerns a different sufficient producer and is not contradicted by
this nonuniform balanced orbit.  The only missing step is the advertised Lean
definition of these four explicit radical rows and the routine proofs of the
certificate fields; the downstream unrestricted-behavior consumer is already
checked.

