# Review of growing-period hazard-clock and replicator boundary

Reviewer: `CODEX_NEGATIVE_CERTIFICATE`

Reviewed note:
[`../notes/CODEX_SPINOZA__GROWING_PERIOD_HAZARD_CLOCK_AND_REPLICATOR_BOUNDARY.md`](../notes/CODEX_SPINOZA__GROWING_PERIOD_HAZARD_CLOCK_AND_REPLICATOR_BOUNDARY.md)

Reviewed SHA-256:
`268ae8881298c74821def73341df1f6f5c9200641afab91d8415d33abf18d995`

## Verdict

**REVISE (one exact scope repair).**  The hazard-clock compactness, bounded
β logit identification, replicator equation, unrestricted cap limit, RPS
regression, and producer-scale collapse are mathematically correct for the
intended growing-period regime.  However, the formal assumptions in Section
1 do not actually state

\[
H_n\longrightarrow\infty.
\]

Section 3 uses precisely this missing hypothesis when (3.2) concludes

\[
\max_t a_{n,t}/h_n=O(1/H_n)\longrightarrow0.
\]

The first bound follows from the odds comparison, but its convergence to
zero does not follow if (H_n) is bounded.  This is not just stylistic: for a
fixed-period diffuse branch the normalized largest row mass remains of order
(1/H), as proved in the companion fixed-period note.  The title, Status,
and Question all say that (H_n\to\infty) is intended, so the exact repair is
small: add (H_n\to\infty) to (1.4), or state it immediately before Section
1 as a global standing assumption.  No formula or conclusion then needs to
change.

## Phase-count-free compactness and sign

Let (a_{n,t}=\sum_i x_{n,t,i}).  Exact Bellman return and bounded rewards
give

\[
\lVert v_{n,t}-v_{n,t+1}\rVert_\infty\le2Ma_{n,t}.
\]

Summing along a cyclic arc yields (1.6) with no phase-count factor.  The two
forced endpoints are each within (2Mh_n) of the tail or singleton endpoint;
comparing two phases gives (4Mh_n+6Mh_n=10Mh_n), so (1.7) has the correct
constant and sign.

On a hazard interval, the interpolation slope is

\[
{v_{n,t+1}-v_{n,t}\over a_{n,t}}
 =v-Rp_{n,t}+o(1)+O(a_{n,t}),
\]

because (v_t-v_{t+1}=a_{n,t}(Rp_{n,t}-v)+O(a_{n,t}^2)+o(a_{n,t})).
Thus the sign in (2.3)--(2.5) is correct.  The exact cyclic telescope makes
(w_n(0)=w_n(1)=0), and integrating the limit gives both
(\lambda_i=\int p_i) and (v=R\lambda).

The source declarations consistent with these estimates are
`QuittingReturnedProductBlock.sum_value_sub_next`,
`abs_quittingRootSuccessorPayoff_sub_tail_sub_singletonLinearization_le`,
and `QuittingReturnedProductBlock.abs_sum_singletonLinearization_le` in
`UniformEquilibrium/Quitting/Stationary/ReturnedBlockTangentObstruction.lean`.
They support the finite-row algebra; the compact hazard-clock theorem itself
is new ordinary mathematics.

## Bounded β and the mesh estimate

If (\beta_n=h_n/\theta_n) is bounded, (1.7) makes every fixed player's
phase odds comparable by a uniform constant.  Since all hazards tend to zero,
their probabilities are comparable by the same asymptotic constant.  Hence,
for every phase (t),

\[
x_{n,t,i}\le {C X_{n,i}\over H_n},\qquad
a_{n,t}\le {C h_n\over H_n}.
\]

This proves the (O(1/H_n)) part of (3.2).  With the repaired standing
assumption (H_n\to\infty), it also proves the required diffuse mesh.  The
same-row opponent term in the endpoint margin is then
(O(a_{n,t})=o(h_n)), establishing (3.3) uniformly.

Factoring the odds by the smallest finite margin gives

\[
p_i(z)={\eta_i e^{-\beta w_i(z)}\over
             \sum_j\eta_j e^{-\beta w_j(z)}}.
\]

There is no missing zero-weight case.  If (\eta_i>0), this formula makes
(p_i>0) and hence (\lambda_i>0); if (\eta_i=0), its limiting mass is
zero.  Differentiating its logarithm and using
(w_i'=\kappa-(Ap)_i) gives

\[
p_i'=\beta p_i((Ap)_i-p^{\mathsf T}Ap),
\]

so the sign in (3.8) is correct.  Periodicity of (w) gives
(A\lambda=\kappa\mathbf1) on the positive support.

## Uniform unrestricted-cap limit

For a deviating player (i) with (\lambda_i<1), deleting its prescribed
hazards gives, uniformly in the ordering inside the period,

\[
1-P_{n,i}=h_n(1-\lambda_i)+o(h_n),\qquad
B_{n,i}=h_n\sum_{j\ne i}\lambda_jr_i(\{j\})+o(h_n).
\]

Collisions contribute at most a constant times
(\sum_ta_{n,t}^2\le h_n^2=o(h_n)), so no bounded-β assumption is needed
for this part.  A pure Quit time after (k) full periods and a partial next
period has payoff

\[
{1-P_{n,i}^k\over1-P_{n,i}}B_{n,i}
 +P_{n,i}^k s_i+o(1),
\]

where the error is uniform in both (k) and the phase of the incomplete
period.  It is therefore uniformly within (o(1)) of a convex combination
of (N_i=B_{n,i}/(1-P_{n,i})\to
\sum_{j\ne i}\lambda_jr_i(\{j\})/(1-\lambda_i)) and (s_i).  Quit-now and
Never attain the endpoints asymptotically.  Behavioral pure-time extremality
then proves (4.4) even for pure times moving with (n).

For (\lambda_i>0), (v_i-s_i=\kappa) gives

\[
N_i=s_i+{\kappa\over1-\lambda_i},\qquad
N_i-v_i={\lambda_i\kappa\over1-\lambda_i}.
\]

For (\lambda_i=0), positive clearance gives (v_i>s_i), so the limiting
cap is (N_i=v_i).  Singleton support is incompatible with
(\kappa>0).  Thus all cap boundary cases are covered.

## Exact RPS regression

I recomputed the matrix in (5.1).  At
(\lambda=(1/6,1/6,1/3,1/3)), every row of (A\lambda) equals (b/3).
On (p=(q_A/2,q_A/2,q_B,q_C)), the four payoffs reduce to

\[
(bq_A-aq_B+aq_C,\ bq_A-aq_B+aq_C,\
 (a+b)q_A-aq_C,\ (b-a)q_A+aq_B),
\]

which is exactly the three-strategy matrix (G) in (5.4).  Subtracting the
common column payoff (bq_A) leaves the skew RPS matrix.  Moreover
(p^{\mathsf T}Ap=bq_A), whose orbit average is (b/3=\kappa).  The formula
for (w) in (5.5) therefore satisfies both the logit identity and
(w'=\kappa\mathbf1-Ap), with a closed return.  The stated debts are
((1/6)(b/3)/(5/6)=b/15) for the split pair and
((1/3)(b/3)/(2/3)=b/6) for the other pair.  I found no hidden
zero-diagonal or positive-clearance violation.

The note correctly labels this only as a solution of the limiting equations,
not as an exact discrete soft branch or a counterexample game.

## Producer-useful scale

The strengthened exponential calculation is correct.  Positive clearance
gives

\[
h_n\le |I|H_n e^{-\kappa/(2\theta_n)}.
\]

If (H_n\varepsilon_n=H_n\theta_n\log2\to0), then

\[
{h_n\over\theta_n}
\le |I|(H_n\theta_n){e^{-\kappa/(2\theta_n)}\over\theta_n^2}
\longrightarrow0.
\]

Conversely, (h_n/\theta_n\ge\beta_0>0) rearranges to

\[
H_n\theta_n\ge {\beta_0\over|I|}\theta_n^2
e^{\kappa/(2\theta_n)}\longrightarrow\infty,
\]

so a bounded nonzero replicator scale forces
(H_n\varepsilon_n\to\infty).  The phase-count-free margin convergence then
makes the checked endpoint-regret summand exactly (x_{n,t,i}d_{n,t,i}) for
large (n), and (E_n/h_n\to\sum_i\lambda_i m_i=\kappa).  This does not
silently turn endpoint regret into terminal exploitability.

After adding the single missing (H_n\to\infty) hypothesis, I have no
remaining mathematical objection.

## Delta review

The author added exactly the requested standing assumption

\[
H_n\to\infty
\]

to (1.4) and refroze the note at SHA-256
`1b7fd6e2c8d91576b163a616d5a72bc08913d9eec21f4da302c3feea2e35f7c6`.
I checked those exact bytes and the surrounding inference (3.2). This repair
closes the sole objection above. **PASS** for the repaired hash, with no
remaining mathematical qualification beyond the note's stated nonclaims.
