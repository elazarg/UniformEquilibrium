# Growing-period soft cycles: hazard-clock compactness and the replicator boundary

Author: `CODEX_SPINOZA`

## Status

**Complete ordinary-mathematics reduction, not checked in Lean.**  This note
continues the fixed-period phase-rigidity theorem at periods
\(H_n\to\infty\).  It proves three statements.

1. Every vanishing-total-hazard exact soft cyclic branch has a compact
   first-order Bellman limit on the cumulative-hazard circle.  For bounded
   \(\beta_n=h_n/\theta_n\), the normalized row mesh is diffuse and the limit
   is an autonomous logit flow.  On the positive-clearance support its hazard
   shares obey the replicator equation for the singleton-surplus matrix.
2. The actual unrestricted terminal cap also has a limit.  It forgets the
   within-period orbit and is exactly the conditional singleton-refusal value.
   Every positive-mass owner has limiting debt
   \(\lambda_i\kappa/(1-\lambda_i)\).
3. Positive clearance alone does **not** forbid nonconstant hazard-clock
   orbits: an explicit four-player zero-diagonal singleton matrix contains an
   invariant rock--paper--scissors circle with \(\kappa>0\).  This is a
   continuum limiting-equation regression, not a claimed exact discrete soft
   branch or a counterexample game.

There is nevertheless a strong conjecture-facing no-go.  On the scale used by
the checked soft-cycle escape theorem,

\[
 H_n\varepsilon_n\to0,
 \qquad \varepsilon_n=\theta_n\log 2,
\]

positive clearance forces \(h_n/\theta_n\to0\).  The entire growing-period
cycle is then phase-flat, its hazard-clock orbit is constant, and aggregate
endpoint regret divided by hazard still tends to \(\kappa\).  Thus growing
period does not evade the period-one tropical/two-Never residual at the only
scale where the present unrestricted-deviation estimate is useful.

## Question

Can \(H_n\to\infty\) split a positive-clearance period-one soft branch into a
source-attached cyclic Nash--Bellman packet whose support error is
little-o of its absorption charge?

No for the common-temperature soft producer under its required scale
\(H_n\varepsilon_n\to0\).  More generally, bounded nonzero
\(h_n/\theta_n\) has a nontrivial replicator limit, but its relative endpoint
cost remains \(\kappa\), and its actual terminal cap is the already known
positive singleton-refusal cap.  A new consumer would therefore have to use
more than nonconstant first-order phase motion.

## Sources inspected

- `exports/ENDOGENOUS_SOFT_CYCLIC_BLOCK_ESCAPE.md`: exact cyclic Bellman
  producer, common-temperature logit roots, and unrestricted periodic cap
  estimate.
- `exports/FIN4_PERIOD_ONE_TROPICAL_TWO_NEVER_REDUCTION.md`: the
  positive-clearance singleton LCP, fixed support labels, and two literal
  Never debts.
- `notes/CODEX_SPINOZA__FIXED_PERIOD_SOFT_PHASE_SPLITTING_RIGIDITY.md`:
  fixed-period phase flatness and endpoint-regret density.
- `UniformEquilibrium/Quitting/Stationary/ReturnedBlockTangentObstruction.lean`:
  `QuittingReturnedProductBlock.totalHazard`, `endpointRegret`, and the
  phase-count-free first-order returned-block obstruction.
- `UniformEquilibrium/Quitting/Classification/SingletonPacketRefusal.lean`:
  `QuittingNormalizedSingletonSourcePacket.refusal_sub_mixture_eq_mass_div_mul_surplus`.
- `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/Defect.lean`:
  `QuittingTerminalExploitabilityWitness.exists_pos_uniform_normalizedSingletonPacketRefusal`.
- `UniformEquilibrium/Quitting/Paths/VanishingNashRootSequenceFamily.lean` and
  `UniformEquilibrium/Quitting/AbsorptionPath/RootSequenceAbsorbingCompletionChronologicalPositiveSingletonRate.lean`:
  the global unrestricted-Nash source field required by the checked positive
  singleton-rate chronological contradiction.
- `notes/CODEX_RIEMANN__BALLISTIC_NORMALIZED_FLOW_OMEGA_CHAIN.md` and
  `notes/GATE_STRENGTHENER__BALLISTIC_WEIGHTED_COCYCLE_COLLAPSE.md`: the older
  tail-normalized ballistic relation, its aperiodic selected-chain
  regression, and its exact loss of absolute payoff/root data.
- `notes/CLAUDE_HILBERT__SINGLETON_LOTTERY_LIMITS.md`, Proposition 31 and
  Proposition 33: survival-normalized affine tail dynamics and the stationary
  fluid calculation for one specific singleton table.

## 1. Exact soft cyclic data

Let \(I\) be finite and write

\[
 R^i=r(\{i\})\in\mathbb R^I,
 \qquad s_i=R^i_i,
 \qquad |r_i(S)|\le M.
\]

For every \(n\), let \(H_n\ge1\), \(\theta_n>0\), and let

\[
 x_{n,t,i}\in(0,1),\qquad v_{n,t}\in[-M,M]^I,
 \qquad t\in\mathbb Z/H_n\mathbb Z,
\]

satisfy the exact cyclic Bellman and logit equations

\[
 v_{n,t}=F(x_{n,t},v_{n,t+1}),                                      \tag{1.1}
\]

\[
 {x_{n,t,i}\over1-x_{n,t,i}}
 =\exp\!\left(-{d_{n,t,i}\over\theta_n}\right),
 \qquad
 d_{n,t,i}=C_i(x_{n,t,-i},v_{n,t+1})-Q_i(x_{n,t,-i}).                \tag{1.2}
\]

Put

\[
 a_{n,t}=\sum_i x_{n,t,i},\qquad
 h_n=\sum_{t<H_n}a_{n,t},\qquad
 X_{n,i}=\sum_{t<H_n}x_{n,t,i}.                                    \tag{1.3}
\]

Assume, after passage to a subsequence,

\[
 H_n\to\infty,\qquad \theta_n\to0,\qquad h_n\to0,\qquad
 v_{n,0}\to v,\qquad {X_{n,i}\over h_n}\to\lambda_i.              \tag{1.4}
\]

Let

\[
 m_i=v_i-s_i,qquad \kappa=\min_i m_i,
\]

and assume the positive-clearance singleton complementarity

\[
 \kappa>0,qquad m_i\ge\kappa,qquad
 \lambda_i>0\Longrightarrow m_i=\kappa.                            \tag{1.5}
\]

The exact Bellman equations imply the phase-count-free estimates

\[
 \max_{t,u}\|v_{n,t}-v_{n,u}\|_\infty\le2Mh_n,                     \tag{1.6}
\]

\[
 \max_{t,u}|d_{n,t,i}-d_{n,u,i}|\le10Mh_n.                         \tag{1.7}
\]

These are the same telescoping estimates as in the fixed-period note; their
constants do not contain \(H_n\).  Consequently all endpoint margins are at
least \(\kappa/2\) for large \(n\).

## 2. The compact hazard clock

Define normalized cumulative-hazard cut points

\[
 z_{n,0}=0,\qquad
 z_{n,t+1}=z_{n,t}+{a_{n,t}\over h_n}.
\]

Thus \(z_{n,H_n}=1\).  On the interval
\([z_{n,t},z_{n,t+1})\), define the owner share

\[
 p_{n,i}(z)={x_{n,t,i}\over a_{n,t}}.                               \tag{2.1}
\]

All denominators are positive.  Interpolate

\[
 w_n(z_{n,t})={v_{n,t}-v_{n,0}\over h_n}                            \tag{2.2}
\]

affinely on every hazard interval.  Then \(w_n(0)=w_n(1)=0\), and
\(w_n\) is uniformly Lipschitz.  Indeed the exact row Bellman equation and
the small-hazard product expansion give, uniformly in \(t\),

\[
 {v_{n,t+1}-v_{n,t}\over a_{n,t}}
 =v-Rp_{n}(z)+O(h_n)+o(1),                                         \tag{2.3}
\]

where \(Rp=\sum_i p_iR^i\).  Simultaneous-Quit terms contribute
\(O(a_{n,t})\), and \(a_{n,t}\le h_n\).

Arzela--Ascoli and weak-star compactness therefore give, along a further
subsequence,

\[
 w_n\to w\quad\hbox{uniformly},qquad
 p_n\overset{*}{\rightharpoonup}p
 \quad\hbox{in }L^\infty([0,1];\Delta(I)),                         \tag{2.4}
\]

with the exact limiting Bellman system

\[
 \boxed{\quad w'(z)=v-\sum_i p_i(z)R^i\quad\text{a.e.},\qquad
 w(0)=w(1)=0.\quad}                                                 \tag{2.5}
\]

In particular

\[
 \lambda_i=\int_0^1p_i(z)\,dz,qquad
 \boxed{v=\sum_i\lambda_iR^i}.                                    \tag{2.6}
\]

This compactness statement does not use a fixed phase count.  The affine
interpolation only serializes first-order singleton mass inside one
vanishing absolute row; it does not claim that the row is an exact product
root at every interior point of the interpolating interval.

## 3. Bounded-temperature-scale identification

Assume now

\[
 \beta_n={h_n\over\theta_n}\longrightarrow\beta<\infty.            \tag{3.1}
\]

The odds equation and (1.7) compare every two phases by a factor bounded in
terms of \(\beta\).  Hence

\[
 \max_t{a_{n,t}\over h_n}=O(1/H_n)\longrightarrow0.                \tag{3.2}
\]

Thus the normalized row mesh is genuinely diffuse.  The one-row expansion
of the endpoint margin improves uniformly to

\[
 d_{n,t,i}
 =m_{n,i}+h_n w_{n,i}(z_{n,t+1})+o(h_n),
 \qquad m_{n,i}=(v_{n,0})_i-s_i.                                  \tag{3.3}
\]

The term involving an opponent quitting in the same row is
\(O(a_{n,t})=o(h_n)\); this is why no collision matrix is silently retained
in (3.3).

Put \(\kappa_n=\min_i m_{n,i}\) and pass to a subsequence on which

\[
 \eta_i=lim_n
 \exp\!\left(-{m_{n,i}-\kappa_n\over\theta_n}\right)\in[0,1]      \tag{3.4}
\]

exists for every \(i\).  At least one \(\eta_i\) equals one.  Equations
(1.2), (3.2), and (3.3) identify the weak-star limit strongly:

\[
 \boxed{
 p_i(z)={\eta_i e^{-\beta w_i(z)}
             \over\sum_j\eta_j e^{-\beta w_j(z)}}.}                \tag{3.5}
\]

If \(\eta_i>0\), then \(m_i=\kappa\).  Conversely a limiting binding
coordinate may have \(\eta_i=0\) if its finite margins approach the common
limit too slowly on the \(\theta_n\)-scale.

For \(\beta=0\), (3.5) is constant.  Periodicity in (2.5) then forces
\(p=\lambda\), \(v=R\lambda\), and

\[
 \boxed{w\equiv0.}                                                  \tag{3.6}
\]

For \(0<\beta<\infty\), let \(B=\{i:\eta_i>0\}\) and define the
singleton-surplus matrix

\[
 A_{ij}=r_i(\{j\})-s_i\qquad(i,j\in B).                             \tag{3.7}
\]

Every \(i\in B\) has \(v_i-s_i=\kappa\).  Differentiating (3.5) along
(2.5) yields the replicator equation

\[
 \boxed{
 p_i'=\beta p_i\bigl((Ap)_i-p^{\mathsf T}Ap\bigr),
 \qquad i\in B.}                                                   \tag{3.8}
\]

Thus a nonconstant growing-period clock is not an arbitrary motion: it is a
periodic orbit of the singleton replicator field, and its time average
\(\lambda\) satisfies

\[
 A\lambda=\kappa\mathbf1\quad\text{on }B.                          \tag{3.9}
\]

## 4. Actual unrestricted terminal caps survive the limit

Repeat the \(H_n\)-row word forever, as in the soft-cycle producer, and let
\(W_{n,i}\) be player \(i\)'s unrestricted terminal cap from phase zero.
Assume \(\lambda_i<1\).  Against player \(i\)'s literal Never strategy, one
period of the opponents has survival

\[
 P_{n,i}=1-h_n(1-\lambda_i)+o(h_n),                                 \tag{4.1}
\]

and its unnormalized absorbed payoff is

\[
 B_{n,i}=h_n\sum_{j\ne i}\lambda_jr_i(\{j\})+o(h_n).               \tag{4.2}
\]

Therefore the literal Never payoff converges to

\[
 N_i={\sum_{j\ne i}\lambda_jr_i(\{j\})\over1-\lambda_i}.          \tag{4.3}
\]

This calculation is independent of the order or the nonconstant orbit
inside a period.

More is true: pure-time extremality and the geometric decomposition into
complete periods give

\[
 \boxed{W_{n,i}\longrightarrow\max\{s_i,N_i\}.}                    \tag{4.4}
\]

Uniformly over a pure time, all completed periods contribute a geometric
prefix of (4.2), while the last incomplete period ends at immediate-Quit
value \(s_i+O(h_n)\).  Hence every pure-time payoff lies within \(o(1)\) of
a convex combination of \(N_i\) and \(s_i\); Never and Quit-now realize the
two endpoints.  The checked behavioral pure-time extremality theorem then
gives (4.4) for arbitrary behavioral deviations.

For a positive-clearance active owner \(i\), (2.6), (3.7), and
\(A\lambda= m\) give

\[
 N_i=s_i+{\kappa\over1-\lambda_i},
\]

so

\[
 \boxed{
 W_{n,i}-(v_{n,0})_i
 \longrightarrow {\lambda_i\kappa\over1-\lambda_i}>0.}            \tag{4.5}
\]

For \(\lambda_i=0\), (4.3) equals \(v_i\), so the limiting debt is zero.
Under \(\kappa>0\), singleton support \(\lambda_i=1\) is impossible because
\(A_{ii}=0\).  Thus (4.5) covers every active owner.

Formula (4.5) is exactly the semantic content of
`refusal_sub_mixture_eq_mass_div_mul_surplus`.  In a terminal-gap table,
`exists_pos_uniform_normalizedSingletonPacketRefusal` supplies a uniform
positive owner refusal.  These are exact debt diagnostics, not a theorem
turning refusal into a returned Nash--Bellman block.

The checked positive-singleton-rate chronological contradiction does not
consume this object.  Its source is a
`QuittingRootSequenceVanishingNashFamily`: the **complete repeated root
sequence** must have global unrestricted Nash error tending to zero.  A soft
cycle supplies only small one-row endpoint defects.  Formula (4.5) proves
that the corresponding repeated sequences have a fixed positive global
Never debt.  This is the exact missing hypothesis, not merely an absent
clock parametrization or derivative estimate.

## 5. Positive clearance permits a nonconstant continuum orbit

The following four-player matrix falsifies the claim that
\(\kappa>0\) alone makes every solution of (2.5), (3.5) constant.

Fix \(a>b>0\) and take \(s_i=0\) and singleton-surplus matrix

\[
 A=
 \begin{pmatrix}
 0&2b&-a&a\\
 2b&0&-a&a\\
 a+b&a+b&0&-a\\
 b-a&b-a&a&0
 \end{pmatrix}.                                                     \tag{5.1}
\]

Put

\[
 \lambda=(1/6,1/6,1/3,1/3),\qquad \kappa=b/3.
\]

Direct multiplication gives

\[
 A\lambda=(b/3)\mathbf1.                                          \tag{5.2}
\]

The diagonal is zero, as required of a quitting singleton-surplus matrix,
and every row has a negative entry when \(a>b\).

The plane

\[
 p=(q_A/2,q_A/2,q_B,q_C),qquad q_A+q_B+q_C=1,                     \tag{5.3}
\]

is invariant under (3.8).  On it the effective three-strategy matrix is

\[
 G=
 \begin{pmatrix}
 b&-a&a\\
 a+b&0&-a\\
 b-a&a&0
 \end{pmatrix}
 =
 \begin{pmatrix}
 0&-a&a\\ a&0&-a\\ -a&a&0
 \end{pmatrix}
 +\mathbf1(b,0,0).                                                  \tag{5.4}
\]

Adding the same column payoff to every row does not alter replicator
dynamics.  Hence (5.4) is the standard zero-sum rock--paper--scissors flow.
Every noncentral interior level of \(q_Aq_Bq_C\) is a nonconstant periodic
orbit.  Its time average is \((1/3,1/3,1/3)\), because integration of the
three logarithmic derivative equations gives \(K\bar q=0\).

Choose one such orbit and rescale \(\beta a\) so its period is one.  Given
its lift \(p(z)\), put \(\eta_i=p_i(0)\) up to one common positive factor and
define

\[
 w_i(z)=-{1\over\beta}\log{p_i(z)\over p_i(0)}+c(z),
 \qquad
 c'(z)=\kappa-p(z)^{\mathsf T}Ap(z),
 \qquad c(0)=0.                                                     \tag{5.5}
\]

Here \(p^{\mathsf T}Ap=bq_A\), whose period average is \(b/3=\kappa\).
Thus \(c(1)=0\), \(w(0)=w(1)=0\), (3.5) holds, and

\[
 w'=\kappa\mathbf1-Ap.                                             \tag{5.6}
\]

Taking \(R^j\) to be column \(j\) of \(A\) and
\(v=\kappa\mathbf1\), equations (2.5)--(3.9) all hold.  The orbit is
nonconstant and has positive clearance.

This is deliberately only a regression for the **limiting equations**.  No
implicit-function or degree argument is supplied which lifts this neutral
RPS family to exact finite-\(H\) Bellman/logit solutions with a prescribed
source.  It is also not asserted to have full recursive normal core or a
positive global terminal gap.  What it proves is that absolute payoff
retention plus positive clearance does not create a Lyapunov theorem for the
hazard-clock ODE.

Its terminal debts are nevertheless explicit.  The two split owners have
debt limit \(\kappa/5=b/15\), and the other two owners have debt limit
\(\kappa/2=b/6\).  Nonconstant phase motion has not reduced refusal.

## 6. The producer-useful scale collapses to the constant orbit

Suppose the roots come from the soft producer with

\[
 \varepsilon_n=\theta_n\log2,
 \qquad H_n\varepsilon_n\to0.                                     \tag{6.1}
\]

Since every endpoint margin is at least \(\kappa/2\), (1.2) gives

\[
 h_n\le |I|H_n\exp\!\left(-{\kappa\over2\theta_n}\right).
\]

Consequently

\[
 {h_n\over\theta_n}
 \le |I|(H_n\theta_n)
 {\exp(-\kappa/(2\theta_n))\over\theta_n^2}
 \longrightarrow0.                                                 \tag{6.2}
\]

Thus this branch lies in the \(\beta=0\) case of Section 3.  Uniformly over
all \(H_n\) phases, every one player's hazards are asymptotically equal,
the normalized mesh is flat, and \(w\equiv0\).

Let \(E_n\) be the aggregate endpoint regret of the returned block.  Since
all endpoint margins are positive for large \(n\), its exact contribution at
\((t,i)\) is \(x_{n,t,i}d_{n,t,i}\).  Uniform phase convergence gives

\[
 \boxed{{E_n\over h_n}\longrightarrow
 \sum_i\lambda_im_i=\kappa.}                                     \tag{6.3}
\]

Therefore any growing-period soft family satisfying the relative-error
condition \(E_n=o(h_n)\) must have

\[
 \boxed{\kappa=0.}                                                  \tag{6.4}
\]

Without that relative-error condition, one cannot conclude \(\kappa=0\):
the constant positive LCP/refusal state is exactly the surviving period-one
residual.  This distinction prevents a false branch elimination.

Conversely, suppose \(h_n/\theta_n\ge\beta_0>0\).  The same exponential
upper bound rearranges to

\[
 H_n\theta_n\ge {\beta_0\over |I|}\,
 \theta_n^2\exp\!\left({\kappa\over2\theta_n}\right)\longrightarrow\infty.
                                                                    \tag{6.5}
\]

Thus a bounded nonzero \(\beta\), and in particular the nonconstant smooth
orbit of Section 5, requires an exponentially large phase count and actually
forces \(H_n\varepsilon_n\to\infty\), not merely failure of convergence to
zero.  The existing periodic cap bound
\(H_n\varepsilon_n/A_{n,i}^-\) then has no terminal-equilibrium force.  This
is the precise price of the nonconstant continuum orbit.

## 7. Comparison with the older ballistic normalized no-go

The strict-ray ballistic state records only

\[
 (\lambda,\Lambda,\rho),\qquad
 \Lambda=\rho\lambda+(1-\rho)\Lambda^+,
\]

and the normalized work relation

\[
 M\Lambda+\rho J\lambda\le0,
 \qquad
 \lambda_i(M\Lambda+\rho J\lambda)_i=0.
\]

Its rational-rotation regression shows that a selected normalized chain can
be aperiodic.  But that state omits an absolute payoff, an absolute hazard
scale, a literal product root, and an actual terminal cap.

The present compactification does **not** make those omissions:

- \(v\) is the limit of the actual exact-return phase-zero payoffs;
- \(w\) is the first-order displacement of those same Bellman values around
  one literal cyclic word;
- \(p\) and \(\lambda\) come from the actual owner hazards of that word;
- (4.4) is the limit of the unrestricted behavioral cap of the repeated
  terminal profile; and
- \(\eta,\beta\) retain the logit chemical-potential and temperature scales.

The collision matrix \(J\) is absent only after the proved diffuse estimate
(3.2): same-row opponent effects are \(o(h_n)\) in the endpoint obstacle,
and simultaneous-coalition Bellman mass is \(o(h_n)\).  No absolute
collision state has been discarded silently.

Even this stronger state remains a first-order limit.  At positive clearance
every used finite root is soft and has endpoint cost of order its hazard;
there is no exact positive-absorption Nash root at the limit.  The RPS
regression therefore differs from the ballistic rational rotation, but it
reaches the same methodological warning: recurrence of a normalized motion
does not supply a source-reprojected exact Nash--Bellman return.

## 8. Singular scale and exact remaining question

If \(h_n/\theta_n\to\infty\), Section 2 still gives the compact Bellman path
(2.5) and Section 4 still gives the exact terminal-cap limit.  The simple
logit formula (3.5) need not survive: normalized row atoms can concentrate,
and the \(O(a_{n,t})\) same-row endpoint term can be visible after division
by \(\theta_n\).  A faithful state must then retain each atom's left value,
owner split, and full atom mass.  This is a hard tropical/atomic boundary,
not the continuous diffuse orbit treated above.

It cannot occur under (6.1) and positive clearance, by (6.2).  Thus it is not
an unexamined arm of the current soft-cycle counterexample reduction.

The exact remaining consumer is unchanged and sharply stated:

> Given the positive singleton packet
> \(A\lambda\ge\kappa\mathbf1\),
> \(\lambda_i>0\Rightarrow(A\lambda)_i=\kappa>0\), together with two or
> more literal Never debts (4.5) at one actual soft cyclic source, use the
> support cardinality \(2,3,4\) and full Fin4 hard data to produce a terminal
> approximate Nash profile or a source-reprojected charged Nash--Bellman
> block.

Growing-period logit phase splitting supplies no additional accepted field
at the producer-useful scale.

## Exact nonclaims

- No continuum orbit in Section 5 is claimed to lift to exact discrete soft
  cycles.
- No refusal debt is claimed to be a uniform-equilibrium consumer by itself.
- No deletion theorem is used; outsider caps are not silently preserved.
- No conclusion about arbitrary non-logit approximate roots is made.
- The \(h_n/\theta_n\to\infty\) atom-marked obstacle problem is not solved.
