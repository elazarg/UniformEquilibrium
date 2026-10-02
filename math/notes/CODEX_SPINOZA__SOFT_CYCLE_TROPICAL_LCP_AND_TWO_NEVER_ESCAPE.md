# Zero-temperature soft cycles produce a source-attached two-Never escape

Author: `CODEX_SPINOZA`

## Status

**Proof draft, ordinary mathematics, not checked in Lean.**  This note starts
from the vanishing-total-hazard arm of the independently reviewed soft cyclic
producer in
`CODEX_SPINOZA__ENDOGENOUS_SOFT_CYCLIC_BLOCK_ESCAPE.md`; it does not modify
that frozen packet.

The main theorem identifies the complete first-order limit.  Normalized
owner hazards solve a common-clearance singleton complementarity system, the
aggregate endpoint regret divided by total hazard converges to that
clearance, and every unrestricted terminal cap has an explicit limit unless
one owner carries all normalized mass.  Under the Fin4 no-uniform-payoff
hypothesis, the clearance is strictly positive and the normalized law has at
least two owners.  Hence the same literal periodic profiles have at least two
fixed players with positive Never debt.  This is a source-attached global
escape object, not a paid port.

The theorem does not yet compile the two Never debtors into a uniform
equilibrium.  Its matrix equation is the familiar standard LCP with
right-hand side \(-\mathbf 1\); the new content is its attachment to one
sequence of actual exact-return soft cycles and the unrestricted cap limit.

## Sources inspected

- `UniformEquilibrium/Quitting/Stationary/ReturnedBlockTangentObstruction.lean`:
  `QuittingReturnedProductBlock.endpointRegret` and
  `hasHomogeneousSimplexSolution_of_vanishing_returnedBlocks`.
- `UniformEquilibrium/Diagnostics/Quitting/FourPlayerReturnedBlockGap.lean`:
  `hasAmbientReturnedBlockRelativeErrorGap_of_fourPlayer_counterexample`.
- `UniformEquilibrium/Quitting/Punishment/SoloCycleCompletion.lean`:
  `isUniformEquilibriumPayoff_soloReward_of_endpointNash_of_punishmentIR`.
- `UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/AmbientCarrierElimination.lean`:
  `normalCore_eq_univ_of_fourPlayer_not_exists_uniformEquilibriumPayoff`.
- `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/NormalCorePunishmentNormal.lean`:
  `all_punishmentNormal_of_normalCore_eq_univ`, which converts full
  recursively stabilized normal core into playerwise punishment normality;
  the two notions are not identified.
- `UniformEquilibrium/Quitting/Bellman/Finite/EndpointNashClosed.lean`:
  `isClosed_isεQuittingRootEndpointNash_simplex`.
- `UniformEquilibrium/Quitting/Classification/LCP/MatrixClasses.lean`:
  `StandardLCPSolution`, `HasHomogeneousSimplexSolution`, and the use of the
  constant right-hand side \(-1\).
- `UniformEquilibrium/Quitting/Classification/SingletonPacketRefusal.lean`:
  `singletonMixture_eq_mass_mul_add_refusal` and
  `refusal_sub_mixture_eq_mass_div_mul_surplus`.
- `UniformEquilibrium/Quitting/Terminal/BehaviorPureTimeExtremality.lean`:
  `sSup_range_quittingTerminalPayoff_update_eq_pureTime`.
- `CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION.md`, Proposition 13, and
  `CLAUDE_HILBERT__SINGLETON_LOTTERY_LIMITS.md`: rare-renewal singleton
  mixtures and refusal amplification.  Those notes already explain why
  strict free-rider singleton schedules need nonvanishing order structure.

## 1. Data and notation

Let \(I=\operatorname{Fin}4\), let \(|r_i(S)|\le M\), and put

\[
 s_i=r_i(\{i\}),\qquad
 A_{ik}=r_i(\{k\})-s_i.                                \tag{1}
\]

Thus \(A\) is the checked `normalizedSoloMatrix` convention and
\(A_{ii}=0\).

For each \(n\), take a period \(H_n\), a tolerance \(\varepsilon_n>0\), and
one soft fixed point from the producer.  Write

\[
 \theta_n={\varepsilon_n\over\log2},\qquad
 x_{n,t,i}\in(0,1),\qquad v_{n,t}\in[-M,M]^I,           \tag{2}
\]

where phase indices are cyclic.  The exact Bellman equations hold and

\[
 {x_{n,t,i}\over1-x_{n,t,i}}
   =\exp\!\left({Q_{n,t,i}-C_{n,t,i}\over\theta_n}\right). \tag{3}
\]

Assume

\[
 H_n\varepsilon_n\longrightarrow0,qquad
 h_n:=\sum_{t<H_n}\sum_i x_{n,t,i}\longrightarrow0.    \tag{4}
\]

Define the cumulative owner masses and their normalization by

\[
 X_{n,i}=\sum_{t<H_n}x_{n,t,i},\qquad
 \lambda_{n,i}=X_{n,i}/h_n.                            \tag{5}
\]

After a subsequence, let \(\lambda_n\to\lambda\) and
\(v_{n,0}\to v\).

## 2. First-order law and tropical complementarity

### Theorem 2.1 (common-clearance limit)

Under (1)--(5),

\[
 v=\sum_k\lambda_k r(\{k\}).                           \tag{6}
\]

Put

\[
 m_i=v_i-s_i=(A\lambda)_i,qquad
 \kappa=\min_i m_i.                                    \tag{7}
\]

Then

\[
 \kappa\ge0,qquad m_i\ge\kappa\quad(i\in I),qquad
 \lambda_i>0\Longrightarrow m_i=\kappa.               \tag{8}
\]

If \(E_n\) denotes the checked aggregate `endpointRegret` of the returned
soft word, then

\[
 {E_n\over h_n}\longrightarrow\kappa.                  \tag{9}
\]

#### Proof

At one phase the Bellman equation changes a coordinate by at most twice the
reward bound times that phase's absorption probability.  Hence

\[
 \max_{t,i}|v_{n,t,i}-v_{n,0,i}|\le 2Mh_n\to0.         \tag{10}
\]

The probability of two or more Quit actions during one traversal is
\(O(h_n^2)\), uniformly in the number of phases.  Likewise, survival factors
before a singleton \(k\)-atom change its raw mass by a total
\(O(h_n^2)\).  The one-period absorption probability is
\(h_n+O(h_n^2)\).  Repetition normalizes the one-period absorbing law, so its
terminal law converges to the singleton lottery \(\lambda\).  The actual
payoff is \(v_{n,0}\), proving (6).

Uniformly in phase,

\[
 Q_{n,t,i}=s_i+O(Mh_n),\qquad
 C_{n,t,i}=v_{n,t+1,i}+O(Mh_n).                        \tag{11}
\]

Consequently the Continue-minus-Quit margins

\[
 d_{n,t,i}:=C_{n,t,i}-Q_{n,t,i}
\]

converge uniformly in \(t\) to \(m_i\).  Since
\(\max_{t,i}x_{n,t,i}\le h_n\to0\), (3) makes every \(d_{n,t,i}\)
positive eventually.  Thus every \(m_i\ge0\), and in particular
\(\kappa\ge0\).

It remains to identify the support.  If \(m_k\ge m_\ell+\delta\), uniform
convergence of the margins and (3) give, for all phases \(t,u\) and all
large \(n\),

\[
 {x_{n,t,k}\over x_{n,u,\ell}}
 \le 2\exp\!\left(-{\delta\over2\theta_n}\right).      \tag{12}
\]

Therefore

\[
 {X_{n,k}\over X_{n,\ell}}
 \le 2H_n\exp\!\left(-{\delta\over2\theta_n}\right)
 \longrightarrow0.                                    \tag{13}
\]

Indeed \(\theta_n\log H_n\le
H_n\varepsilon_n/\log2\to0\).  Taking \(\ell\) minimizing \(m\) proves
that positive \(\lambda_k\) is possible only at a minimizer, which is (8).

Finally, eventual positivity of \(d_{n,t,i}\) makes the exact endpoint
regret summand

\[
 x_{n,t,i}d_{n,t,i}.                                   \tag{14}
\]

Divide its sum by \(h_n\).  Uniform margin convergence and
\(X_{n,i}/h_n\to\lambda_i\) give

\[
 {E_n\over h_n}\to\sum_i\lambda_i m_i=\kappa,
\]

where the last equality uses (8). \(\square\)

### Corollary 2.2 (exact LCP identification)

If \(\kappa=0\), then \(\lambda\) is a homogeneous simplex solution for
\(A\).  If \(\kappa>0\), put \(z=\lambda/\kappa\).  Then

\[
 z\ge0,\qquad -\mathbf1+Az\ge0,qquad
 z_i(-1+(Az)_i)=0,                                     \tag{15}
\]

so \(z\) is a `StandardLCPSolution` for the constant right-hand side
\(-\mathbf1\).

This is immediate from (8).  It also explains why (9) is exactly the
checked returned-block relative-error boundary: zero clearance is the
homogeneous branch, while positive clearance is the standard-LCP branch.

## 3. Uniform unrestricted cap limit

For \(i\) with \(\lambda_i<1\), define its refusal value against the limiting
singleton lottery by

\[
 N_i={\sum_{k\ne i}\lambda_k r_i(\{k\})\over1-\lambda_i}. \tag{16}
\]

Let \(W_{n,i}\) be player \(i\)'s unrestricted terminal cap against the
actual repeated periodic opponents.

### Theorem 3.1 (pure-time envelope limit)

For every \(i\) with \(\lambda_i<1\),

\[
 W_{n,i}\longrightarrow\max\{s_i,N_i\}.                \tag{17}
\]

This convergence is uniform over the deviator's deterministic Quit time;
by pure-time extremality it therefore covers every behavioral deviation,
including Never and clocks escaping through arbitrarily many periods.

#### Proof

Delete player \(i\)'s prescribed hazards.  Its opponents' absorption
probability in one period is

\[
 b_{n,i}=h_n(1-\lambda_i)+o(h_n),                       \tag{18}
\]

and, conditional on that absorption, the first quitter is singleton \(k\ne
i\) with probability

\[
 {\lambda_k\over1-\lambda_i}+o(1).                     \tag{19}
\]

Both statements follow from the same union and collision estimates used in
Theorem 2.1.  They are valid because \(1-\lambda_i>0\).

Write a pure Quit time as \(qH_n+t\).  Absorption in one of the \(q\)
complete opponent periods pays the conditional value in (19), while survival
to the chosen time followed by a solo Quit pays \(s_i\).  Absorption in the
last partial period and a tie at the chosen phase have total probability
\(O(h_n)\), uniformly in \(q,t\).  Thus every pure-time payoff differs by
\(o(1)\), uniformly in the chosen time, from a convex combination of
\(N_i\) and \(s_i\).  This gives the upper bound in (17).  Quitting at time
zero tends to \(s_i\), while Never pays the complete opponent-period value
and tends to \(N_i\); these two deviations give the matching lower bound.
Pure-time extremality finishes the behavioral statement. \(\square\)

### Corollary 3.2 (explicit debt limits)

If \(0<\lambda_i<1\), then

\[
 N_i-v_i={\lambda_i\over1-\lambda_i}(v_i-s_i)
          ={\lambda_i\kappa\over1-\lambda_i},           \tag{20}
\]

and hence

\[
 W_{n,i}-v_{n,0,i}\longrightarrow
 {\lambda_i\kappa\over1-\lambda_i}.                   \tag{21}
\]

If \(\lambda_i=0\), then \(N_i=v_i\) and \(s_i\le v_i\), so that player's
debt tends to zero.  Thus, whenever \(\max_i\lambda_i<1\), all limiting debt
is carried exactly by the positive-mass owners, and it is refusal/Never debt.

Equation (20) is just the affine split
\(v_i=\lambda_i s_i+(1-\lambda_i)N_i\), together with (8).

## 4. Fin4 no-UE consequence: two named Never debtors

Assume now that the four-player table has no uniform-equilibrium payoff.
The checked counterexample classification used by
`hasAmbientReturnedBlockRelativeErrorGap_of_fourPlayer_counterexample`
excludes a homogeneous simplex solution for \(A\).  Corollary 2.2 therefore
forces

\[
 \kappa>0.                                              \tag{22}
\]

A singleton support would have \(\kappa=(A\lambda)_i=A_{ii}=0\), so
\(\operatorname{supp}\lambda\) contains at least two players.  For every
support owner \(i\), (21) is strictly positive and its lower-bound witness is
the literal Never deviation against the same periodic source.  Since the
support is finite, there are distinct fixed players \(i,j\) and a constant
\(\gamma_0>0\) such that, for all sufficiently large \(n\), both players'
Never gains at the actual soft profile are at least \(\gamma_0\).

This sharpens the diffuse boundary of the soft producer to

\[
 \boxed{
 \text{one literal exact-return cyclic source sequence}
 \; + \;
 \text{two fixed source-coherent Never debtors}
 \; + \;
 E_n/h_n\to\kappa>0.}
 \tag{23}
\]

It is not merely the abstract existence of a standard LCP solution.  The
weights, fixed payoff target, endpoint-regret cost, and two unrestricted
deviations all come from the same actual profile sequence.

### Theorem 4.1 (the period-one singleton arm is already consumed)

For every \(\varepsilon_n\downarrow0\), choose the soft producer with the
fixed period

\[
 H_n=1.                                                \tag{24}
\]

If the Fin4 table has no uniform-equilibrium payoff, then every root hazard
in this sequence tends to zero after passage to the fixed-debtor
subsequence.  Consequently Theorems 2.1 and 3.1 apply, and their limit has
\(\kappa>0\), at least two support owners, and at least two fixed positive
Never debts.

#### Proof

The no-uniform-payoff hypothesis supplies a fixed positive terminal gap.
The reviewed soft-cycle debt bound therefore selects a fixed debtor \(i\)
such that the one-row opponent absorption tends to zero.  Hence

\[
 x_{n,j}\longrightarrow0\qquad(j\ne i).               \tag{25}
\]

Pass to a subsequence with \(x_{n,i}\to p\).  Suppose \(p>0\).  The terminal
law of the actual stationary profile then converges to singleton \(\{i\}\),
so

\[
 v_n\longrightarrow r(\{i\}).                         \tag{26}
\]

The product roots converge to the positive-rate solo root owned by \(i\)
with hazard \(p\).  Endpoint Nash defect is at most \(\varepsilon_n\), so
closedness and continuity give exact endpoint Nash of this solo root against
the continuation \(r(\{i\})\).

The checked Fin4 counterexample classification first gives full recursively
stabilized normal core.  The separate checked theorem
`all_punishmentNormal_of_normalCore_eq_univ` then makes every player
punishment-normal; it does not identify those two notions.  In particular,

\[
 \operatorname{punishmentValue}_i\le r_i(\{i\}).       \tag{27}
\]

Now
`isUniformEquilibriumPayoff_soloReward_of_endpointNash_of_punishmentIR`
applies to the positive-rate solo root and produces the uniform-equilibrium
payoff \(r(\{i\})\), a contradiction.  Therefore \(p=0\).  Together with
(25), this makes the total one-row hazard tend to zero.  Section 4 already
shows that the resulting clearance is positive and has nonsingleton support,
and Corollary 3.2 supplies the two Never debts. \(\square\)

The moving-period singleton-diffusion regression in the reviewed producer
does not contradict this argument: its periods tend to infinity.  Fixing
\(H=1\) is an available choice in the unconditional producer and removes the
temporal diffusion which hid the collision endpoint from the solo-cycle
compiler.

## Scope and exact next question

- The general classification in Sections 2--3 applies only to the
  vanishing-total-hazard branch.  Theorem 4.1 separately consumes the
  macroscopic singleton arm for the deliberately chosen period-one producer.
- Simultaneous quitting and nonsingleton outcomes are allowed in every soft
  root; their normalized mass vanishes automatically at first order.
- No stationary, bounded-clock, or fixed-period restriction is imposed on a
  deviator.
- The periods may diverge, but \(H_n\varepsilon_n\to0\) is used critically in
  the support-selection estimate (13).
- The result does not claim that the standard LCP certificate alone produces
  a uniform equilibrium.

The precise next question is whether two fixed Never debtors on one
exact-return vanishing-hazard source sequence can be converted, without
changing that source, into either a two-cut chronological packet or a
nonvanishing-order singleton schedule.  The old paid-port waist has only one
selected response and does not contain the simultaneous source-coherent
information in (23).
