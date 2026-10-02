# Adversarial review of the fullCore balanced-cycle fibre exclusion

Reviewer identity: `CODEX_SNELL`

Date: 2026-09-03

Verdict: **PASS.**  I found no mathematical objection.  The four algebraic
certificate rows remain ordinary mathematics until instantiated in Lean; the
generic balanced-cycle compiler and unrestricted consumer are checked.

## Claim checked

For every Fin4 quitting reward table satisfying

\[
 r_i(\{j\})=s_i+C^j_i
\]

for the four displayed columns of `fullCoreMatrix`, with arbitrary real
baseline `s` and arbitrary rewards on all nonsingleton coalitions, the fixed
vector

\[
 v_0=s+\left(0,{1+5\sqrt {13}\over54},
                 {11+\sqrt {13}\over54},0\right)
\]

is a uniform-equilibrium payoff.

The dimension count is correct.  The normalized singleton matrix fixes the
12 off-diagonal singleton differences while leaving the four diagonal
baselines free; the 44 nonsingleton coordinates are also free, for total
dimension 48.

## Independent exact algebra

Write `t=sqrt(13)`.  The displayed columns agree with the checked definition
of `fullCoreMatrix`:

\[
\begin{aligned}
C^0&=(0,1,-1,-1),&C^1&=(-1,0,3,1),\\
C^2&=(1,-1,0,1),&C^3&=(1,1,-1,0).
\end{aligned}
\]

I expanded all 16 coordinates of

\[
 z_k=p_kC^k+(1-p_k)z_{k+1}.
\]

They agree with the packet.  Representative exact cancellations, using only
`t^2=13`, are

\[
\begin{aligned}
(1-p_3)z_{0,2}
 &= {(65-t)(11+t)\over78\cdot54}
  ={13+t\over78}=p_3,\\
(1-p_2)z_{3,1}
 &= {(13-t)(13+7t)\over14\cdot78}
  ={1+t\over14}=p_2,\\
(1-p_1)z_{2,0}
 &= {(119-7t)(3+t)\over138\cdot14}
  ={19+7t\over138}=p_1,\\
(1-p_0)z_{1,3}
 &= {(53-5t)(7+5t)\over54\cdot46}
  ={1+5t\over54}=p_0.
\end{aligned}
\]

The remaining nonzero coordinates yield exactly the displayed `z` entries;
the zero coordinates cancel with the same identities.  The auxiliary
quadratic description is consistent: the chosen
`p3=(13+t)/78` solves `39p3^2-13p3+1=0`, and substitution gives the other
three hazards.

From `3<t<4`, all four hazards are strictly between zero and one.  Every
entry of every `z_k` is nonnegative, and `z_(k,k)=0`.  Hence the active-owner
equalities and all solo floors hold exactly.

Adding an arbitrary baseline preserves every arc because

\[
s+z_k=p_k(s+C^k)+(1-p_k)(s+z_{k+1}).
\]

No positivity assumption on `s` is used.

## Compiler and deviation audit

The data match every field of
`BalancedSingletonCycleCertificate` in
`UniformEquilibrium/Quitting/Cycles/BalancedSingletonCertificate.lean`:

- owner order and initial phase are finite and literal;
- hazard bounds, arcs, active equalities, and solo floors are as above; and
- every player faces three positive-hazard phases owned by opponents, so the
  required opponent-divergence field holds.

For a deviator `i`, the deleted-player full-cycle survival product omits only
the phase owned by `i` and retains three factors strictly below or equal to
one, at least one strictly below one.  It is therefore strictly below one.
This is the exact contraction used by the checked compiler for Never and
stopping hazards supported arbitrarily late.

At one subdivided phase only one prescribed owner can Quit.  A passive
deviator's immediate Quit therefore produces either its singleton or a
two-player collision with that owner; no unlisted larger coalition is
silently identified with a singleton.  The reader-facing certificate bounds
every such arbitrary pair reward by
`balancedSingletonCycleCollisionCap reward = 2 * quittingRewardBound reward`.
The fixed finite table makes this cap finite, while equal-survival
subdivision makes the collision error tend to zero as `m` grows.

The checked theorem
`BalancedSingletonCycleCertificate.isTerminalNash_and_hasValue` covers every
randomized history-dependent behavioral replacement and keeps the terminal
payoff exactly `v0` at every positive subdivision.  The checked theorem
`BalancedSingletonCycleCertificate.isUniformEquilibriumPayoff` then supplies
the required same-target, all-large-horizon uniform quantifiers.  The target
depends on the fixed game's baseline `s`, but it does not depend on the mesh,
horizon, or deviation.

## Boundary and scope

No hazard is zero or one; only the microhazards tend to zero.  Arbitrarily
large nonsingleton rewards merely enlarge the table-dependent collision cap
and hence the necessary mesh.  The result does not assert a common mesh over
the unbounded 48-dimensional fibre.

The packet correctly distinguishes its unformalized specialized algebraic
instance from the checked generic compiler.  It does not use or contradict
the separate no-relabelled-cyclic-open-sign declaration.  I found no hidden
nonsingleton sign assumption, bounded-controller restriction, late-clock
gap, moving target, or source/consumer mismatch.
