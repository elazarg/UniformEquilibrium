# Review of the universal positive-phantom reduction

Reviewer: `CODEX_GAUSS`

Reviewed claim: Proposition 27 in
[`../notes/CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION.md`](../notes/CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION.md),
the universal consequence of bounded charge on the selected punishment-floor
forward orbit.  This is an independent mathematical audit, not a Lean check.

## Verdict

**Valid ordinary mathematics.**  I found no orientation, compactness, or
limit-Nash error.  The conclusion is exactly a universal residual under the
assumption that the game has no uniform-equilibrium payoff: the canonical
selected predecessor orbit has finite total absorption and converges to a
positive all-Continue Nash *tail annotation*.  It does not itself construct a
behavioral equilibrium, a chronological path, or a positive return.

## Checks

1. The disjunction is used in the correct direction.
   `quittingGame_uniformPayoff_or_punishmentFloorForwardChargeBound`
   (`UniformEquilibrium/Quitting/Bellman/Finite/PunishmentFloorForward.lean`)
   says that either the high-charge packet consumer already gives a uniform
   payoff or one fixed real number strictly bounds every partial sum of the
   nonnegative absorption masses.  Under the hypothesis of Proposition 27,
   the first arm is impossible.  Monotonicity of the partial sums therefore
   gives a finite series and `alpha_t -> 0`.

2. The Bellman orientation is correct.  The checked identity is

   `V_(t+1) = quittingRootSuccessorPayoff reward V_t P_t`.

   Thus the stored edge has current endpoint `V_(t+1)` and tail `V_t`; it is a
   forward predecessor orbit, not roots already ordered for chronological
   execution.  Proposition 27 does not reverse this orientation silently.

3. The total-variation estimate is literal.  Both `V_t` and `V_(t+1)` lie in
   the canonical reward box.  Applying
   `abs_quittingRootSuccessorPayoff_sub_tail_le_two_mul_absorptionMass`
   (`UniformEquilibrium/Quitting/Debt/Marked/TimeAdvance.lean`) to the policy
   identity gives, coordinatewise,

   `|V_(t+1)(i)-V_t(i)| <= 2 M alpha_t`.

   Summability of the right side makes every coordinate Cauchy and of finite
   total variation.  Finiteness of the player type then gives one payoff
   vector `b`; closedness of the coordinate box retains `b` in that box.

4. Root convergence follows from an exact named inequality, not only a union
   heuristic.  For every player,

   `(P_t i true).toReal <= alpha_t`

   is `quitProbability_le_quittingRootAbsorptionMass`
   (`UniformEquilibrium/Quitting/Debt/Dynamic/PunishmentFloorViolation.lean`).
   Hence every Quit marginal tends to zero and the finite Boolean product root
   tends coordinatewise to all-Continue.

5. Exact Nash passes to the limit.  The statements
   `quittingPunishmentFloorForward_isZeroNash` have tails `V_t` and roots
   `P_t`.  Root expected payoffs and both unilateral endpoints are finite
   polynomials in the Boolean marginals and affine in the tail.  With
   `V_t -> b` and `P_t -> all-Continue`, their inequalities pass to the
   limit.  At all-Continue, a pure Continue endpoint is `b_i` and a pure Quit
   endpoint is the own singleton reward, so exact Nash gives

   `r({i})_i <= b_i`.

6. The punishment-floor inequality has the right endpoint:
   `quittingPunishmentFloor_le_forwardValue` holds at every `t`, so its closed
   coordinatewise limit is `quittingPunishmentValue reward i <= b_i`.

7. Positivity uses exactly the necessary zero-solo disjunct.  If all own
   singleton rewards were nonpositive,
   `exists_uniformEquilibriumPayoff_of_zeroSolo`
   (`UniformEquilibrium/Quitting/Punishment/ZeroSoloDisjunct.lean`) would
   contradict the standing no-uniform-payoff hypothesis.  Thus some own solo
   is positive, and item 5 places the corresponding coordinate of `b` above
   it.

## Scope and remaining obstruction

The word “phantom” is essential.  The all-Continue root is Nash against the
declared continuation `b`, but literal eternal continuation pays zero, not
`b`.  Finite total charge also prevents direct use of the high-charge packet
consumer.  A conjecture-closing continuation must still manufacture a
source-matched positive return, prove a restart theorem at this boundary, or
show that the boundary data are themselves impossible.  Proposition 27
correctly claims none of those missing steps.
