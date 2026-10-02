# Period-one soft roots force a two-Never tropical escape in Fin4

Authors: `CODEX_SPINOZA`

Independent reviews:
[CODEX_SNELL](../feedback/CODEX_SPINOZA__SOFT_CYCLE_TROPICAL_LCP_AND_TWO_NEVER_ESCAPE__BY_CODEX_SNELL.md),
[CODEX_NEGATIVE_CERTIFICATE](../feedback/CODEX_SPINOZA__SOFT_CYCLE_TROPICAL_LCP_AND_TWO_NEVER_ESCAPE__BY_CODEX_NEGATIVE_CERTIFICATE.md)

## Exact statement

Let \(I=\operatorname{Fin}4\), and let

\[
 r:\{S\subseteq I:S\ne\varnothing\}\longrightarrow\mathbb R^I
\]

be a finite quitting reward table. Never pays zero. Behavioral
randomizations are independent across players and dates conditional on public
survival. A unilateral deviator may replace its whole behavioral strategy,
including by any finite pure quitting time or by Never.

Choose \(M\ge0\) such that \(|r_i(S)|\le M\) for every player \(i\) and
nonempty coalition \(S\).

Assume that the quitting game has no ordinary uniform-equilibrium payoff.
Equivalently, there is \(\Gamma>0\) such that every actual behavioral profile
has an unrestricted unilateral terminal gain at least \(\Gamma\).

Let \(\varepsilon_n>0\) tend to zero. For each \(n\), apply the unconditional
producer in
[`ENDOGENOUS_SOFT_CYCLIC_BLOCK_ESCAPE.md`](ENDOGENOUS_SOFT_CYCLIC_BLOCK_ESCAPE.md)
with the fixed period \(H=1\). Thus it gives

\[
 x_n=(x_{n,i})_{i\in I}\in(0,1)^I,\qquad v_n\in[-M,M]^I,
\]

such that:

1. \(v_n=F(x_n,v_n)\), the exact one-row Bellman return;
2. \(x_n\) is an \(\varepsilon_n\)-endpoint-Nash root against \(v_n\);
3. repeating \(x_n\) forever is an actual almost-surely absorbing stationary
   behavioral profile \(\sigma_n\) with terminal payoff \(v_n\); and
4. for every player \(i\), with

   \[
   A^-_{n,i}=1-\prod_{j\ne i}(1-x_{n,j}),
   \]

   its complete unrestricted terminal debt satisfies

   \[
   d_i(\sigma_n)\le {\varepsilon_n\over A^-_{n,i}}.   \tag{1}
   \]

After passage to a subsequence, all hazards tend to zero:

\[
 h_n:=\sum_i x_{n,i}\longrightarrow0.                \tag{2}
\]

Put \(\lambda_{n,i}=x_{n,i}/h_n\). After a further subsequence,
\(\lambda_n\to\lambda\) in the player simplex and \(v_n\to v\). Define

\[
 s_i=r_i(\{i\}),\qquad A_{ik}=r_i(\{k\})-s_i.
\]

Then

\[
 v=\sum_k\lambda_k r(\{k\}),                         \tag{3}
\]

and, with

\[
 m_i=v_i-s_i=(A\lambda)_i,\qquad \kappa=\min_i m_i,
\]

one has

\[
 \kappa>0,\qquad m_i\ge\kappa,\qquad
 \lambda_i>0\Longrightarrow m_i=\kappa.             \tag{4}
\]

If \(E_n\) is the aggregate endpoint regret of the returned row, then

\[
 {E_n\over h_n}\longrightarrow\kappa.                \tag{5}
\]

The support of \(\lambda\) has cardinality \(2\), \(3\), or \(4\). For every
support owner \(i\), define

\[
 N_i={\sum_{k\ne i}\lambda_k r_i(\{k\})\over1-\lambda_i}.
\]

Its unrestricted terminal cap \(W_{n,i}\) satisfies

\[
 W_{n,i}\longrightarrow N_i,\qquad
 W_{n,i}-v_{n,i}\longrightarrow
 {\lambda_i\kappa\over1-\lambda_i}>0.                \tag{6}
\]

The lower-bound witness in (6) is the literal Never deviation. Consequently
there are two fixed distinct support owners \(i,j\) and \(\gamma_0>0\) such
that, for all sufficiently large \(n\), both literal Never deviations gain
at least \(\gamma_0\) at the same actual source profile \(\sigma_n\).

For every outsider \(d\) with \(\lambda_d=0\),

\[
 W_{n,d}-v_{n,d}\longrightarrow0.                    \tag{7}
\]

Thus a hypothetical Fin4 counterexample admits one literal stationary
exact-return source sequence with vanishing total hazard, positive
first-order endpoint-regret density, and at least two fixed source-coherent
Never debtors. The only remaining support-cardinality cases are \(2,3,4\).

## Conjecture-facing change

The prior soft-cycle producer left a macroscopic isolated-owner arm and a
vanishing-total-hazard arm. This result consumes the first arm by choosing
the available fixed period \(H=1\). A positive limiting owner hazard would
give a positive-rate solo endpoint Nash root, and the checked Fin4 normality
and punishment compiler would produce a uniform-equilibrium payoff,
contradicting the assumed gap.

Therefore every hypothetical Fin4 counterexample reaches the second arm, and
that arm becomes the explicit system (3)--(7), with at least two literal
Never deviations attached to one actual source sequence.

This strictly narrows
[`FIN4_APPROXIMATE_FORWARD_PACKET_OR_CAPACITY_BARRIER.md`](../archive/FIN4_APPROXIMATE_FORWARD_PACKET_OR_CAPACITY_BARRIER.md)
and
[`FIN4_TWO_PERSISTENT_EXACT_SPINE_SELECTION.md`](../questions/FIN4_TWO_PERSISTENT_EXACT_SPINE_SELECTION.md).
The remaining consumer must treat support cardinality \(2\), \(3\), or \(4\)
without losing the common source.

## Definitions and assumptions

For a product root \(x\) and continuation \(w\), write \(Q_i(x_{-i})\) for
player \(i\)'s payoff from Quit and \(C_i(x_{-i},w)\) for its payoff from
Continue. The producer uses temperature

\[
 \theta_n={\varepsilon_n\over\log2}
\]

and the exact logit relation

\[
 {x_{n,i}\over1-x_{n,i}}
 =\exp\!\left({Q_i(x_{n,-i})-C_i(x_{n,-i},v_n)\over\theta_n}\right). \tag{8}
\]

The endpoint-Nash condition is the pair of non-strict weighted endpoint
inequalities. If

\[
 \Delta_{n,i}=C_i(x_{n,-i},v_n)-Q_i(x_{n,-i}),
\]

then its regret contribution is

\[
 \max\{x_{n,i}\Delta_{n,i},
       -(1-x_{n,i})\Delta_{n,i},0\}\le\varepsilon_n.
\]

The terminal cap \(W_{n,i}\) is the supremum over all complete unilateral
behavioral deviations against \(\sigma_{n,-i}\). Pure-time extremality makes
it the supremum over deterministic quitting times
\(\mathbb N\cup\{\infty\}\), where \(\infty\) is literal Never. No
stationary or bounded-clock restriction is placed on the deviator.

All convergence statements allow subsequences. The two Never labels are
fixed after the subsequence and do not vary with \(n\).

## Source correspondence

The arbitrary-table producer, exact Bellman return, actual repeated profile,
and complete debt bound (1) are the reviewed result
[`ENDOGENOUS_SOFT_CYCLIC_BLOCK_ESCAPE.md`](ENDOGENOUS_SOFT_CYCLIC_BLOCK_ESCAPE.md).
The new argument specializes it to \(H=1\), consumes its singleton arm, and
computes the complete zero-temperature limit and cap.

The no-uniform-payoff/positive-terminal-gap equivalence is
`not_exists_uniformEquilibriumPayoff_iff_exists_terminalExploitabilityGap` in
`UniformEquilibrium/Quitting/Terminal/ExploitabilityGap.lean`.

Joint endpoint closedness is
`isClosed_isεQuittingRootEndpointNash_simplex` in
`UniformEquilibrium/Quitting/Bellman/Finite/EndpointNashClosed.lean`.

The checked Fin4 classification gives full recursively stabilized normal
core through
`normalCore_eq_univ_of_fourPlayer_not_exists_uniformEquilibriumPayoff` in
`UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/AmbientCarrierElimination.lean`.
The recursive core is not definitionally the punishment-normal set. The
separate bridge is `all_punishmentNormal_of_normalCore_eq_univ` in
`UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/NormalCorePunishmentNormal.lean`.

The positive solo endpoint is consumed by
`isUniformEquilibriumPayoff_soloReward_of_endpointNash_of_punishmentIR` in
`UniformEquilibrium/Quitting/Punishment/SoloCycleCompletion.lean`.

The homogeneous branch is excluded by
`standardQMatrixSide_of_not_exists_uniformEquilibriumPayoff` in
`UniformEquilibrium/Quitting/Classification/LCP/CounterexampleNecessary.lean`.
The matrix definitions `HasHomogeneousSimplexSolution` and
`StandardLCPSolution` are in
`UniformEquilibrium/Quitting/Classification/LCP/MatrixClasses.lean`.

The cap calculation matches
`refusal_sub_mixture_eq_mass_div_mul_surplus` in
`UniformEquilibrium/Quitting/Classification/SingletonPacketRefusal.lean`.
Behavioral pure-time completeness is
`sSup_range_quittingTerminalPayoff_update_eq_pureTime` in
`UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean`.

No inspected declaration already proves the period-one singleton-arm
elimination or attaches the positive-level LCP system and the two Never
deviations to the actual soft profiles.

## Proof

### The period-one singleton arm is impossible

The positive terminal gap gives, at every \(\sigma_n\), some player with debt
at least \(\Gamma\). After a subsequence it is one fixed \(i\). Equation (1)
gives

\[
 A^-_{n,i}\le{\varepsilon_n\over\Gamma}\longrightarrow0. \tag{9}
\]

Since

\[
 A^-_{n,i}=1-\prod_{j\ne i}(1-x_{n,j}),
\]

and every factor is in \([0,1]\), (9) implies

\[
 x_{n,j}\longrightarrow0\qquad(j\ne i).              \tag{10}
\]

Pass to \(x_{n,i}\to p\in[0,1]\). Suppose \(p>0\). The actual terminal
coalition law converges to the point mass on \(\{i\}\), so

\[
 v_n\longrightarrow r(\{i\}).                        \tag{11}
\]

The roots converge to the solo stationary root owned by \(i\) with hazard
\(p\). Since the endpoint errors tend to zero, joint closedness gives exact
endpoint Nash of this root against \(r(\{i\})\).

The Fin4 hypothesis gives full recursive normal core. The separate checked
normal-core/punishment bridge yields

\[
 \operatorname{quittingPunishmentValue}_i\le r_i(\{i\}). \tag{12}
\]

Exact endpoint Nash, (12), and \(p>0\) meet every hypothesis of
`isUniformEquilibriumPayoff_soloReward_of_endpointNash_of_punishmentIR`.
It produces the uniform-equilibrium payoff \(r(\{i\})\), a contradiction.
Thus \(p=0\). Together with (10), this proves (2).

### Singleton first-order law and complementarity

In one row, the probability of two or more Quit actions is \(O(h_n^2)\), the
absorption probability is \(h_n+O(h_n^2)\), and the singleton-\(k\) atom has
raw probability \(x_{n,k}+O(h_n^2)\). Infinite stationary repetition
normalizes this one-row absorbing law, so its terminal law converges to the
singleton lottery \(\lambda\), proving (3).

Uniformly in \(i\),

\[
 Q_i(x_{n,-i})=s_i+O(Mh_n),\qquad
 C_i(x_{n,-i},v_n)=v_{n,i}+O(Mh_n).                  \tag{13}
\]

Thus the Continue-minus-Quit margin tends to
\(m_i=v_i-s_i=(A\lambda)_i\). Since every \(x_{n,i}\to0\), (8) makes these
margins nonnegative in the limit. Let \(\kappa=\min_i m_i\). If
\(m_k\ge m_\ell+\delta\), (8) and (13) give

\[
 {x_{n,k}\over x_{n,\ell}}
 \le2\exp\!\left(-{\delta\over2\theta_n}\right)\longrightarrow0. \tag{14}
\]

Hence positive \(\lambda_k\) is possible only at a minimum margin. For all
large \(n\), every margin is positive, and the aggregate endpoint regret is

\[
 E_n=\sum_i x_{n,i}
 \bigl(C_i(x_{n,-i},v_n)-Q_i(x_{n,-i})\bigr).
\]

Dividing by \(h_n\) and using (13) gives

\[
 {E_n\over h_n}\longrightarrow\sum_i\lambda_i m_i=\kappa, \tag{15}
\]

which proves (5).

If \(\kappa=0\), then \(\lambda\ge0\), \(\sum_i\lambda_i=1\),
\(A\lambda\ge0\), and \(\lambda_i(A\lambda)_i=0\). This is a homogeneous
simplex solution, which the checked counterexample classification excludes.
Therefore \(\kappa>0\).

If \(\lambda\) were supported only at \(i\), then
\(\kappa=(A\lambda)_i=A_{ii}=0\), because the normalized solo matrix has zero
diagonal. Thus the support has size \(2\), \(3\), or \(4\).

### Complete cap and two literal Never gains

Fix \(i\) with \(\lambda_i<1\). After deleting its prescribed hazard, the
opponents' one-row absorption probability is

\[
 h_n(1-\lambda_i)+o(h_n),
\]

and its conditional first quitter is singleton \(k\ne i\) with probability
\(\lambda_k/(1-\lambda_i)+o(1)\). Therefore literal Never tends to

\[
 N_i={\sum_{k\ne i}\lambda_k r_i(\{k\})\over1-\lambda_i}. \tag{16}
\]

A deterministic Quit time receives \(N_i+o(1)\) if opponents absorb first
and \(s_i+o(1)\) if they survive to that time; the collision error at the
chosen row is \(O(h_n)\). The estimate is uniform over all finite times and
Never. Pure-time extremality gives

\[
 W_{n,i}\longrightarrow\max\{s_i,N_i\}.              \tag{17}
\]

The singleton mixture identity

\[
 v_i=\lambda_i s_i+(1-\lambda_i)N_i
\]

and \(v_i-s_i=\kappa>0\) for a support owner yield

\[
 N_i-v_i
 ={\lambda_i\over1-\lambda_i}(v_i-s_i)
 ={\lambda_i\kappa\over1-\lambda_i}>0.              \tag{18}
\]

This proves (6), including attainment by literal Never. If \(\lambda_i=0\),
then \(N_i=v_i\) and \(s_i\le v_i\), proving (7).

Choose two distinct support owners. Their two limits in (18) are positive.
Taking \(\gamma_0\) below half their minimum gives the two fixed Never gains
on the same profiles \(\sigma_n\).

## Boundary tests

### Fixed period is essential

The producer's moving-period test has one owner using hazard \(1/H\) at each
of \(H\) phases, a collision premium \(\Gamma\), and punishment normality,
yet every outsider's pure-time gain is at most \(\Gamma/H\). Owner absorption
stays bounded below while collision is diffuse. It does not challenge this
theorem: \(H=1\) is chosen before \(\varepsilon_n\to0\), so a positive owner
hazard becomes a literal positive-rate solo endpoint consumed above.

### Singleton support cannot survive positive clearance

The diagonal identity \(A_{ii}=0\) shows that \(\lambda=e_i\) forces
\(\kappa=0\). Thus support size two is the sharp lower bound after exclusion
of the homogeneous branch.

### Positive clearance is not itself a contradiction

For the checked paired-singleton matrix

\[
 A=\begin{pmatrix}
 0&3&-1&-1\\
 3&0&-1&-1\\
 -1&-1&0&3\\
 -1&-1&3&0
 \end{pmatrix},
\]

the exact choice \(\lambda=(1,1,1,1)/4\), \(\kappa=1/4\) satisfies
\(A\lambda=\kappa\mathbf1\), and each debt in (18) is \(1/12\). The matrix is
checked full-core, standard-Q, and homogeneous-infeasible. Its maintained
completions include one with no stationary exact terminal Nash but an exact
period-two equilibrium. Thus positive clearance and full support require a
new consumer rather than an algebraic contradiction.

### Outsider-zero debt is source-specific

At support size two or three, (7) holds at the soft source but need not hold
at the lift of an arbitrary equilibrium of the support game. Exact
four-player regressions in
[`CODEX_SPINOZA__POSITIVE_REFUSAL_SUPPORT_CARDINALITY_AND_OUTSIDER_LIFT_BOUNDARY.md`](../notes/CODEX_SPINOZA__POSITIVE_REFUSAL_SUPPORT_CARDINALITY_AND_OUTSIDER_LIFT_BOUNDARY.md)
have an outsider with zero debt along the diffuse source but gain one by
joining the sure quitter at a lifted exact small-player equilibrium.

## Adapter and consumer

The actual-data adapter is unconditional. Given any Fin4 table and any
\(\varepsilon_n\downarrow0\), invoke the exported producer at \(H=1\). Under
the counterexample hypothesis, the fixed terminal gap and (1) select the
fixed-debtor subsequence above. No root, LCP solution, source minimum, or
passport is supplied as input.

The positive-hazard arm has a checked consumer: endpoint closedness, the
full-core-to-punishment-normal bridge, and the solo-cycle compiler produce an
actual uniform-equilibrium payoff. This proves that arm absent under the
counterexample hypothesis.

The surviving output is (2)--(7). Its remaining consumer is:

- at support size two, the checked two-player theorem solves the owners but
  two lifted outsider cap inequalities remain;
- at support size three, the checked three-player theorem solves the owners
  but the unique lifted outsider cap remains; and
- at support size four, there is no deletion and one needs a full-support
  chronological or cyclic consumer using nonsingleton rewards.

Small-player existence alone does not preserve (7) after changing profiles.
The next theorem must be source-preserving selection, controlled two-source
gluing, or a direct full-support chronological consumer.

## Lean handoff

A narrow formalization should expose the actual stationary profiles,
normalized hazard weights, and literal Never strategies. A suggested
headline is:

`exists_periodOne_tropical_twoNever_escape_of_finFour_counterexample`.

Likely dependencies are the formalized soft producer and:

- `isClosed_isεQuittingRootEndpointNash_simplex`;
- `normalCore_eq_univ_of_fourPlayer_not_exists_uniformEquilibriumPayoff`;
- `all_punishmentNormal_of_normalCore_eq_univ`;
- `isUniformEquilibriumPayoff_soloReward_of_endpointNash_of_punishmentIR`;
- `standardQMatrixSide_of_not_exists_uniformEquilibriumPayoff`;
- `sSup_range_quittingTerminalPayoff_update_eq_pureTime`; and
- the singleton refusal identities.

Useful finite lemmas are:

1. opponent absorption tending to zero forces every opponent hazard to zero;
2. the first-order singleton-law calculation;
3. logit support selection at fixed period one;
4. uniform pure-time cap convergence to \(\max\{s_i,N_i\}\); and
5. extraction of two fixed support labels from positive clearance and zero
   diagonal.

## Scope and nonclaims

- This is reviewed ordinary mathematics, not yet a Lean theorem.
- The no-uniform-payoff hypothesis derives a counterexample-facing reduction;
  it does not assume that a counterexample exists.
- The root comes from the unconditional producer at period one. The result
  does not classify every approximate root outside that produced class.
- Endpoint inequalities are approximate before the limit and exact only in
  the hypothetical positive-hazard solo limit.
- Arbitrary unilateral behavioral deviations are covered through terminal
  caps and pure-time extremality.
- The result does not turn the two Never deviations into a Nash--Bellman
  chronology, exact spine, or uniform equilibrium.
- It does not claim that support restriction preserves outsider caps.
- It does not claim that full-support LCP data determine a cyclic equilibrium;
  nonsingleton reward coordinates remain essential.
