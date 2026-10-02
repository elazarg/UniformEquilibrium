# Review of fixed-period soft phase-splitting rigidity

Reviewer: `CODEX_NEGATIVE_CERTIFICATE`

Reviewed note:
[`../notes/CODEX_SPINOZA__FIXED_PERIOD_SOFT_PHASE_SPLITTING_RIGIDITY.md`](../notes/CODEX_SPINOZA__FIXED_PERIOD_SOFT_PHASE_SPLITTING_RIGIDITY.md)

Reviewed SHA-256:
`35a5b21cc83c6e6391c05dec0b5887c018130c2ed473829dac68078a88fba72a`

## Verdict

**PASS.**  I found no mathematical counterexample to the fixed-period
positive-clearance no-go.  The (2M) Bellman-motion bound, the (10M)
endpoint-margin bound, the exponential hazard estimate, phase-flatness, the
first-order Bellman cancellation, and (E_n/h_n\to\kappa) are all valid under
the stated hypotheses.  The conclusion is ordinary mathematics, not a new
Lean-checked theorem.

There is one nonblocking exposition improvement: the proof should display the
short telescoping derivation of

\[
v=\sum_i\lambda_i r(\{i\}),
\]

which is invoked in (3.3) as the "terminal singleton law."  This identity is
indeed forced by the assumptions, so this is not a missing hypothesis or a
change to the result.

## Reconstruction of the quantitative bounds

Write (p_{n,t}=\sum_i x_{n,t,i}).  One exact Bellman row is a convex
combination of its tail value and bounded terminal rewards.  Consequently

\[
\lvert v_{n,t,i}-v_{n,t+1,i}\rvert\le 2M p_{n,t}.
\]

Summing over an arc of the fixed cycle gives (2.1), since
(\sum_t p_{n,t}=h_n).  Forcing player (i) to Quit changes the singleton
payoff only on opponent absorption, and forcing (i) to Continue changes the
tail only on opponent absorption.  At each phase both errors are at most
(2Mh_n).  Comparing two Quit endpoints costs (4Mh_n); comparing two
Continue endpoints costs those two endpoint errors plus the (2Mh_n) tail
motion, hence (6Mh_n).  Their difference is therefore bounded by
(10Mh_n), exactly as in (2.2).

The relevant checked estimates and exact cyclic telescope are consistent
with this calculation:

- `abs_quittingRootSuccessorPayoff_sub_tail_le_sum_quitRates`,
  `abs_quittingRootEndpointDifference_sub_solo_sub_tail_le_sum_quitRates`,
  `QuittingReturnedProductBlock.sum_value_sub_next`, and
  `QuittingReturnedProductBlock.abs_sum_singletonLinearization_le` in
  `UniformEquilibrium/Quitting/Stationary/ReturnedBlockTangentObstruction.lean`;
- `quittingRootEndpointDifference` in
  `UniformEquilibrium/Quitting/Root/SuccessorCertificate.lean`, whose sign is
  Quit minus Continue.  Thus the note's (d=C-Q) is the negative of the
  checked endpoint difference.

Because all phases converge to (v), the endpoint margins converge uniformly
to (m_i=v_i-s_i\ge\kappa).  For large (n), the common-temperature odds
equation therefore gives

\[
x_{n,t,i}\le e^{-\kappa/(2\theta_n)},\qquad
{h_n\over\theta_n}\le {|I|H\over\theta_n}
e^{-\kappa/(2\theta_n)}\longrightarrow0.
\]

Combining this with the (10Mh_n) phase-margin bound makes the logarithm of
the same-player phase odds ratio tend to zero.  Since every hazard tends to
zero, the hazards themselves have ratio tending to one.  This verifies
(2.7)--(2.9).

## The two requested stress points

### Replacing (v_{n,t+1}) by (v)

There is no uniformity gap here.  Fixed (H), (2.1), and
(v_{n,0}\to v) imply

\[
\max_t\lVert v_{n,t}-v\rVert_\infty=o(1).
\]

In a singleton linearization, this replacement is multiplied by the row
hazard (p_{n,t}\).  Its row error is therefore
(p_{n,t}o(1)), and the sum over the fixed phase set is (h_no(1)=o(h_n)).
The collision remainder is bounded by a constant times
(\sum_t p_{n,t}^2\le h_n^2=o(h_n)).  Hence (3.2) is uniform at the claimed
scale.

For completeness, summing (3.2) around the cycle telescopes its left side to
zero.  Dividing by (h_n) and using the cumulative normalized masses gives,
coordinatewise,

\[
0=\sum_i\lambda_i(r_i(\{i\})-v_i)
 =\sum_i\lambda_i r_i(\{i\})-v_i,
\]

because (\sum_i\lambda_i=1\).  This proves the singleton law used in (3.3).
Phase-flatness then makes the same first-order expression occur with the
factor (1/H) at every row, so every normalized adjacent phase drift tends
to zero.

### Coordinates with λ_i=0

No positive-mass assumption is needed for these coordinates.  All soft
hazards are strictly positive, so (X_{n,i}>0), and (2.8) applies to every
player.  If (\lambda_i=0), then

\[
{x_{n,t,i}\over h_n}
= {x_{n,t,i}\over X_{n,i}}{X_{n,i}\over h_n}
\longrightarrow {1\over H}\,0=0.
\]

Thus the zero-weight terms disappear correctly in (3.3) and (4.1).  There is
no hidden division by (\lambda_i).

## Endpoint-regret orientation and limit

For large (n), every (d_{n,t,i}=C-Q) is positive.  In the checked
`QuittingReturnedProductBlock.endpointRegret`, the endpoint difference is
(Q-C=-d).  Its Continue-regret summand is then zero and its Quit-regret
summand is exactly (x_{n,t,i}d_{n,t,i}).  Hence

\[
{E_n\over h_n}
=\sum_i {X_{n,i}\over h_n}\,m_i+o(1)
\longrightarrow\sum_i\lambda_i m_i=\kappa,
\]

where simplex normalization and the support-complementarity condition give
the last equality.  This is a local endpoint-regret density statement; it
does not claim that terminal exploitability itself equals (E_n).

## Boundary and falsification checks

- If (\kappa=0), the exponential separation from temperature disappears,
  so phase splitting is not excluded.  The note states this boundary.
- If (H=H_n\to\infty), the factor (H_n) can compete with the exponential
  scale.  The note correctly makes no moving-period claim.
- If (h_n\not\to0), phase values can move macroscopically, so the proof does
  not apply.
- The common-temperature logit equation is essential for phase-flatness.  An
  arbitrary approximate selector can allocate a small cumulative hazard
  unevenly across phases; the note explicitly excludes that inference.
- Taking a player with (\lambda_i=0), taking (H=1), or allowing unequal
  phase hazards does not produce a counterexample: the odds-ratio argument
  handles the first and third cases, while (H=1) is tautological.

The theorem therefore gives a genuine no-go for local phase-split
bifurcations attached to a fixed-period, diffuse, positive-clearance soft
end.  It does not exclude a disconnected macroscopic-hazard branch, a
growing-period branch, or a non-logit construction.
