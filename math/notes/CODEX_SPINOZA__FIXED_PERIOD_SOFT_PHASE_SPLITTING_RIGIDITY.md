# Fixed-period soft phase splitting is asymptotically rigid

Author: `CODEX_SPINOZA`

## Status

**Complete ordinary theorem, not checked in Lean.**  This note tests the
suggested phase splitting of the positive-clearance period-one tropical
limit.  The result is a no-go for every fixed period.

On a vanishing-hazard soft logit branch with positive clearance
\(\kappa>0\), the hazard scale is exponentially small in the temperature,
whereas phase-to-phase Bellman motion is only proportional to total hazard.
Consequently that motion is \(o(\theta)\), every one player's hazards are
asymptotically equal across all phases, the first-order Bellman phase drift
vanishes, and endpoint regret divided by total hazard still tends to
\(\kappa\).

Thus choosing \(H=|\operatorname{supp}\lambda|\) cannot place different
support owners in different dominant phases.  A useful phase-separated branch
must leave the fixed-period positive-clearance collar, accumulate macroscopic
hazard, or use a non-logit/global re-equilibration mechanism.

## Sources inspected

- `exports/ENDOGENOUS_SOFT_CYCLIC_BLOCK_ESCAPE.md`: the unconditional cyclic
  soft producer and exact Bellman return.
- `exports/FIN4_PERIOD_ONE_TROPICAL_TWO_NEVER_REDUCTION.md`: the
  positive-clearance period-one source and the support split \(2,3,4\).
- `UniformEquilibrium/Quitting/Stationary/ReturnedBlockTangentObstruction.lean`:
  `QuittingReturnedProductBlock.totalHazard`, `endpointRegret`, and the
  first-order singleton estimates.
- `UniformEquilibrium/Quitting/Bellman/Finite/NashBellmanSpine.lean`:
  endpoint differences and finite Nash--Bellman rows.

## 1. Fixed-period soft data

Let \(I\) be a finite player set, fix an integer \(H\ge1\), and suppose
\(|r_i(S)|\le M\).  For each \(n\), let

\[
 x_{n,t,i}\in(0,1),\qquad v_{n,t}\in[-M,M],
 \qquad t\in\mathbb Z/H\mathbb Z,
\]

be an exact-return soft cyclic block:

\[
 v_{n,t}=F(x_{n,t},v_{n,t+1}),                       \tag{1.1}
\]

and

\[
 {x_{n,t,i}\over1-x_{n,t,i}}
 =\exp\!\left(-{d_{n,t,i}\over\theta_n}\right),
 \qquad
 d_{n,t,i}:=
 C_i(x_{n,t,-i},v_{n,t+1})-Q_i(x_{n,t,-i}),          \tag{1.2}
\]

where \(\theta_n>0\) and \(\theta_n\to0\).

Put

\[
 h_n=\sum_{t<H}\sum_i x_{n,t,i},\qquad
 X_{n,i}=\sum_{t<H}x_{n,t,i}.                        \tag{1.3}
\]

Assume \(h_n\to0\).  After a subsequence suppose

\[
 {X_{n,i}\over h_n}\longrightarrow\lambda_i,\qquad
 v_{n,0}\longrightarrow v,                           \tag{1.4}
\]

and put

\[
 s_i=r_i(\{i\}),\qquad m_i=v_i-s_i,\qquad
 \kappa=\min_i m_i.                                  \tag{1.5}
\]

The case of interest is

\[
 \kappa>0,\qquad m_i\ge\kappa,\qquad
 \lambda_i>0\Longrightarrow m_i=\kappa.              \tag{1.6}
\]

These are exactly the positive-refusal limits produced by the period-one
reduction.

## 2. Quantitative phase rigidity

### Lemma 2.1 (Bellman and endpoint phase bounds)

For every \(n,t,u,i\),

\[
 |v_{n,t,i}-v_{n,u,i}|\le2Mh_n,                      \tag{2.1}
\]

and

\[
 |d_{n,t,i}-d_{n,u,i}|\le10Mh_n.                    \tag{2.2}
\]

#### Proof

At phase \(t\), the total absorption probability is at most
\(\sum_i x_{n,t,i}\).  Equation (1.1) is a convex combination of terminal
rewards and \(v_{n,t+1}\), all in \([-M,M]\), so

\[
 |v_{n,t,i}-v_{n,t+1,i}|
 \le2M\sum_jx_{n,t,j}.
\]

Summing along either arc of the fixed cycle proves (2.1).

With player \(i\) forced to Quit, the chance that some opponent also Quits is
at most \(\sum_{j\ne i}x_{n,t,j}\), hence

\[
 |Q_i(x_{n,t,-i})-s_i|\le2Mh_n.                      \tag{2.3}
\]

With \(i\) forced to Continue, the chance of opponent absorption has the same
bound, hence

\[
 |C_i(x_{n,t,-i},v_{n,t+1})-v_{n,t+1,i}|
 \le2Mh_n.                                           \tag{2.4}
\]

Compare (2.3)--(2.4) at \(t\) and \(u\), and use (2.1):

\[
 |d_{n,t,i}-d_{n,u,i}|
 \le 2Mh_n+2Mh_n+2Mh_n+2Mh_n+2Mh_n.
\]

This is (2.2).  \(\square\)

### Lemma 2.2 (hazard is exponentially below temperature)

Under (1.4)--(1.6),

\[
 {h_n\over\theta_n}\longrightarrow0.                 \tag{2.5}
\]

#### Proof

The bounds above and (1.4) give, uniformly over the finite phase/player set,

\[
 d_{n,t,i}\longrightarrow m_i\ge\kappa.
\]

For all large \(n\), \(d_{n,t,i}\ge\kappa/2\).  From (1.2),

\[
 x_{n,t,i}
 \le\exp\!\left(-{\kappa\over2\theta_n}\right).
\]

Therefore

\[
 0\le {h_n\over\theta_n}
 \le {|I|H\over\theta_n}
       \exp\!\left(-{\kappa\over2\theta_n}\right)
 \longrightarrow0.                                  \tag{2.6}
\]

\(\square\)

### Theorem 2.3 (phase-flatness)

For every player \(i\) and phases \(t,u\),

\[
 {x_{n,t,i}\over x_{n,u,i}}\longrightarrow1.         \tag{2.7}
\]

Equivalently,

\[
 {x_{n,t,i}\over X_{n,i}}\longrightarrow {1\over H}
 \qquad(t<H).                                        \tag{2.8}
\]

In particular, if \(\lambda_i>0\), then

\[
 {x_{n,t,i}\over h_n}\longrightarrow{\lambda_i\over H}
 \qquad\text{at every phase }t.                      \tag{2.9}
\]

#### Proof

Subtract the logarithms in (1.2):

\[
 \log {x_{n,t,i}/(1-x_{n,t,i})
             \over x_{n,u,i}/(1-x_{n,u,i})}
 =-{d_{n,t,i}-d_{n,u,i}\over\theta_n}.
\]

By (2.2) and (2.5), the right side tends to zero.  Since all hazards tend to
zero, the two factors \(1-x_{n,t,i}\) and \(1-x_{n,u,i}\) tend to one.
This proves (2.7), and summing the \(H\) asymptotically equal positive terms
proves (2.8).  Combining (2.8) with (1.4) proves (2.9).  \(\square\)

## 3. The leading Bellman system does not split

### Theorem 3.1 (zero first-order phase drift)

For every phases \(t,u\),

\[
 {v_{n,t}-v_{n,u}\over h_n}\longrightarrow0.         \tag{3.1}
\]

#### Proof

The first-order expansion of the exact Bellman row is

\[
 v_{n,t}-v_{n,t+1}
 =\sum_i x_{n,t,i}\bigl(r(\{i\})-v\bigr)+o(h_n),     \tag{3.2}
\]

uniformly in the fixed phase set.  Simultaneous-Quit terms are \(O(h_n^2)\);
replacing \(v_{n,t+1}\) by \(v\) costs \(o(h_n)\).

Divide by \(h_n\) and use (2.9):

\[
 {v_{n,t}-v_{n,t+1}\over h_n}
 \longrightarrow {1\over H}
   \left(\sum_i\lambda_i r(\{i\})-v\right)=0,         \tag{3.3}
\]

because the terminal singleton law gives
\(v=\sum_i\lambda_i r(\{i\})\).  Summing finitely many adjacent differences
gives (3.1).  \(\square\)

This identifies the singular leading-order system.  The support owners do
not take turns.  Every phase carries the same normalized vector
\(\lambda/H\), and the leading Bellman displacement cancels separately at
each phase.

## 4. Refusal level and endpoint-regret density are unchanged

Let \(E_n\) be the aggregate endpoint regret over the \(H\) rows.  Since every
\(d_{n,t,i}>0\) for all sufficiently large \(n\), its exact contribution at
\((t,i)\) is \(x_{n,t,i}d_{n,t,i}\).

### Theorem 4.1 (no improvement of the tropical level)

\[
 {E_n\over h_n}\longrightarrow
 \sum_i\lambda_i m_i=\kappa.                         \tag{4.1}
\]

#### Proof

The endpoint margins converge uniformly to \(m_i\), while
\(\sum_t x_{n,t,i}/h_n\to\lambda_i\).  Hence

\[
 {E_n\over h_n}\to\sum_i\lambda_i m_i.
\]

By complementarity (1.6), every positive \(\lambda_i\) is carried at
\(m_i=\kappa\), and the simplex weights sum to one.  \(\square\)

Thus fixed-period phase splitting neither lowers the positive refusal level
nor creates an \(o(h_n)\) support error.

## 5. Support-cardinality consequences

Take \(H=|\operatorname{supp}\lambda|\).

1. If the support has size two, each support owner places asymptotically half
   of its own cumulative hazard in each of the two phases.
2. If the support has size three, each support owner places asymptotically one
   third in every phase.
3. If the support has size four, each support owner places asymptotically one
   quarter in every phase.

No permutation of phase labels changes these conclusions.  In particular,
there is no branch attached to this positive-clearance end on which owner
\(i_t\) carries \(1-o(1)\) of its own hazard in a designated phase \(t\).

The obstruction is the scale separation

\[
 h_n=O(e^{-\kappa/(2\theta_n)})=o(\theta_n),          \tag{5.1}
\]

while all phase-dependent payoff effects are \(O(h_n)\).  The temperature
therefore washes out phase distinctions before the hazards become visible.
A usual implicit-function argument at \((\theta,h)=(0,0)\) cannot generate a
phase-broken branch: the hazard coordinates are exponentially flat there,
and the limiting Jacobian in those coordinates is singular.

## 6. Boundary tests

### Zero clearance

If \(\kappa=0\), Lemma 2.2 fails.  Then \(h_n/\theta_n\) need not vanish, and
phase differences of order \(h_n\) can be visible at the logit scale.  The
theorem therefore does not rule out useful phase splitting on the homogeneous
or already consumable zero-level branch.

### Growing period

The proof uses fixed \(H\).  If \(H_n\to\infty\), the phase count can compete
with the exponential scale, and a moving-period clock can diffuse one
owner's mass.  This is precisely the boundary exhibited by the moving-\(H\)
singleton regression in the soft-producer export.  No growing-period claim is
made here.

### Macroscopic hazard

If \(h_n\not\to0\), phase values may move by order one and can rebalance
conditional incentives.  That is not a perturbation of the positive-refusal
zero-hazard end and is outside this theorem.

### Non-logit approximate roots

The phase-flat conclusion uses the exact common-temperature odds equation
(1.2).  An arbitrary approximate Nash--Bellman family need not distribute a
player's small hazard evenly among phases.  However, if it still has the same
positive-clearance limit, Theorem 4.1's \(E_n/h_n\to\kappa\) calculation
continues whenever its endpoint margins converge and its normalized owner
masses converge.  Merely changing the local soft selector does not by itself
give \(o(h_n)\) regret.

## 7. Conjecture-facing verdict

The finite phase-splitting proposal does not consume any of the support
cardinalities \(2,3,4\).  It returns exactly the same positive-level LCP
certificate:

\[
 A\lambda\ge\kappa\mathbf1,\qquad
 \lambda_i>0\Longrightarrow(A\lambda)_i=\kappa,
 \qquad \kappa>0,
\]

with the same normalized endpoint cost \(\kappa\).

The remaining viable departures are genuinely nonlocal:

- a macroscopic-hazard cyclic continuation whose phase values move by order
  \(\kappa\);
- a growing-period construction with a separately controlled
  hazard-versus-period scale; or
- a source-preserving global re-equilibration not governed by the
  common-temperature logit selector.

The exact next question is whether the source-attached two Never deviations
can force one of those departures while retaining the literal source law and
paying a seam sublinear in its macroscopic absorption charge.

