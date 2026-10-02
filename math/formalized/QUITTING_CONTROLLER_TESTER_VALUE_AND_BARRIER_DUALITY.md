# Exact controller--tester value and barrier duality

Authors: Math conference synthesis

Independent reviews:
[ledger audit](../feedback/CONTROLLER_VS_TESTER__BY_LEDGER_AUDIT.md),
[uniform-horizon audit](../feedback/CONTROLLER_VS_TESTER__BY_UNIFORM_AUDIT.md),
and [barrier falsification audit](../feedback/CONTROLLER_VS_TESTER__BY_BARRIER_AUDIT.md).
The two statement repairs from the later
[formalizer audit](../feedback/META_EXPORTS__BY_FORMALIZER.md) are incorporated
below.

## Exact statement

Let \(I\) be a finite nonempty player set and \(r\) a bounded quitting reward
table. Let

\[
R=\max_{\varnothing\ne S\subseteq I}\max_{i\in I}|r_i(S)|.
\]

There is an exact finite-dimensional forward ledger with \(4|I|+1\)
coordinates which, for every prescribed product-root chronology, determines:

1. its prescribed terminal payoff;
2. every player's payoff from every pure finite stopping time;
3. every player's Never payoff; and
4. the supremum over every unilateral behavioral replacement.

For Fin4 the ledger dimension is \(17\).

The tester also has an exact infinite occupation-flow primal and a bounded
Bellman dual with a Never-sensitive transversality condition.

Let \(\mathcal K_r\) be the compact carrier of terminal semantic pairs
\((u,b)\), where \(u\) is prescribed payoff and \(b\) is the vector of
unrestricted behavioral caps, and put

\[
\mathcal Z_R=[-R,R]^I\times[-R,R]^I.
\]

For a fixed target \(v\in[-R,R]^I\), the decreasing finite-word controller
value converges to

\[
W_r(v)
=
\min_{(u,b)\in\mathcal K_r}
\max\left\{
\|u-v\|_\infty,\,
\max_i(b_i-u_i)
\right\}.
\tag{1}
\]

This is exactly the original offline uniform-horizon controller--tester value:
the controller selects one behavioral profile, while the tester may select
any sufficiently late horizon, any player, and any complete behavioral
replacement depending on that horizon.

After optimizing the target,

\[
\boxed{
\eta(r)
=
\min_{(u,b)\in\mathcal K_r}\max_i(b_i-u_i)}
\tag{2}
\]

and

\[
\boxed{
\eta(r)=0
\quad\Longleftrightarrow\quad
r\text{ has a uniform-equilibrium payoff}.}
\tag{3}
\]

The values \(W_r(v)\) and \(\eta(r)\) have exact greatest
upper-semicontinuous Bellman-barrier duals. The target-free value also has the
closed invariant-set dual

\[
\eta(r)
=
\max\left\{
\gamma:
\begin{array}{l}
e_\infty\in C\subseteq\mathcal Z_R,\ C\text{ closed},\\
T_x(C)\subseteq C\quad\forall x,\\
\max_i(b_i-u_i)\ge\gamma\quad\forall (u,b)\in C
\end{array}
\right\}.
\tag{4}
\]

The canonical carrier \(\mathcal K_r\) attains (4). A positive certified floor
\(\Gamma\) yields an actual all-behavior exploitability gap at every
\(0<\gamma<\Gamma\); attainment at exactly \(\Gamma\) is not asserted.

## Conjecture-facing change

This gives a sound and complete recursive tester representation, exact
finite-window controller approximation, exact identification with the
uniform-horizon quantifiers, and a complete negative barrier language.

It answers the controller--tester formulation problem. The remaining question
is only the sign or effective certification problem:

\[
\eta(r)=0\text{ for every Fin4 table,}
\]

or one concrete table with an independently checkable positive barrier. That
question is stated in
`questions/QUITTING_CONTROLLER_TESTER_DUALITY.md`.

The theorem is an offline controller value. It does not construct an online
feedback policy reacting to observed tester choices.

## Root data

Let \(X=[0,1]^I\) be the product-root space and define

\[
p_x(S)=\prod_{j\in S}x_j\prod_{j\notin S}(1-x_j),
\qquad
c(x)=p_x(\varnothing).
\]

For each player \(i\), let

\[
p_x^{-i}(A)=
\prod_{j\in A}x_j
\prod_{\substack{j\notin A\\j\ne i}}(1-x_j),
\qquad
\chi_i(x)=p_x^{-i}(\varnothing).
\]

Define

\[
g_k(x)=
\sum_{\varnothing\ne S\subseteq I}p_x(S)r_k(S),
\tag{5}
\]

\[
q_i(x)=
\sum_{A\subseteq I\setminus\{i\}}
p_x^{-i}(A)r_i(A\cup\{i\}),
\tag{6}
\]

\[
a_i(x)=
\sum_{\varnothing\ne A\subseteq I\setminus\{i\}}
p_x^{-i}(A)r_i(A).
\tag{7}
\]

Thus \(g_k\) is the prescribed absorbing contribution, \(q_i\) is player
\(i\)'s payoff from Quitting at the current root, and
\(a_i(x)+\chi_i(x)w\) is its payoff from Continuing into value \(w\).

## The forward ledger

For a prescribed chronology \(x^0,x^1,\ldots\), initialize

\[
Y_0=0,\quad S_0=1,\quad
P_{i,0}=0,\quad L_{i,0}=1,\quad M_{i,0}=-R
\]

and update under root \(x\) by

\[
\begin{aligned}
Y'_k&=Y_k+Sg_k(x),&
S'&=Sc(x),\\
P'_i&=P_i+L_i a_i(x),&
L'_i&=L_i\chi_i(x),\\
M'_i&=\max\{M_i,P_i+L_iq_i(x)\}.
\end{aligned}
\tag{8}
\]

The exact coordinate formulas are

\[
S_t=\prod_{s<t}c(x^s),
\qquad
Y_{k,t}=\sum_{s<t}S_sg_k(x^s),
\tag{9}
\]

\[
L_{i,t}=\prod_{s<t}\chi_i(x^s),
\qquad
P_{i,t}=\sum_{s<t}L_{i,s}a_i(x^s).
\tag{10}
\]

The bounds

\[
|g_k(x)|\le R(1-c(x)),
\qquad
|a_i(x)|\le R(1-\chi_i(x))
\]

telescope to

\[
|Y_{k,t}|\le R(1-S_t),
\qquad
|P_{i,t}|\le R(1-L_{i,t}),
\tag{11}
\]

and every candidate stopping payoff lies in \([-R,R]\). Hence the reachable
ledger closure is compact and the update is continuous.

The prescribed payoff is

\[
U_k(\sigma)=Y_{k,\infty}.
\tag{12}
\]

First Quitting at date \(t\) gives

\[
V_i(t)=P_{i,t}+L_{i,t}q_i(x^t),
\]

and Never gives \(V_i(\infty)=P_{i,\infty}\). Therefore

\[
\boxed{
B_i(\sigma)
=
\max\left\{
\sup_{t\in\mathbb N}
\bigl(P_{i,t}+L_{i,t}q_i(x^t)\bigr),
P_{i,\infty}
\right\}
=
\max\{M_{i,\infty},P_{i,\infty}\}.}
\tag{13}
\]

Every behavioral response induces a law on finite stopping times and Never,
and its payoff is the corresponding mixture of these values. Conversely,
conditional hazards realize every such law. Thus (13) covers unrestricted,
calendar-dependent behavioral deviations, not merely stationary deviations.

## Exact tester flow and Bellman dual

Fix player \(i\) and abbreviate the opponent data at date \(t\) by
\(q_t,a_t,\chi_t\). A feasible tester flow is a nonnegative sequence
\((y_t,s_t,k_t)\) satisfying

\[
y_0=1,\qquad
s_t+k_t=y_t,\qquad
y_{t+1}=\chi_tk_t.
\tag{14}
\]

Its payoff is

\[
\mathcal P_i(y,s,k)
=
\sum_{t\ge0}(s_tq_t+k_ta_t).
\tag{15}
\]

Every behavioral hazard induces this flow. Conversely,
\(h_t=s_t/y_t\) when \(y_t>0\), with arbitrary value after extinction,
purifies every feasible flow exactly.

Let \(L_t=\prod_{s<t}\chi_s\). A bounded Bellman sequence is feasible when

\[
w_t\ge q_t,
\qquad
w_t\ge a_t+\chi_tw_{t+1},
\qquad
\liminf_{t\to\infty}L_tw_t\ge0.
\tag{16}
\]

Then

\[
\boxed{
B_i(\sigma)
=
\sup_{\text{flows satisfying (14)}}\mathcal P_i
=
\inf_{\text{sequences satisfying (16)}}w_0.}
\tag{17}
\]

For weak duality, multiply (16) by the split flow and telescope:

\[
y_tw_t
\ge s_tq_t+k_ta_t+y_{t+1}w_{t+1}.
\]

Since \(0\le y_t\le L_t\), transversality removes the terminal boundary term.

For the reverse inequality, the true best-response tail values are bounded,
obey the Bellman equality, and satisfy transversality. If \(L_t\to0\), this
follows from boundedness. If \(L_t\to L_\infty>0\), the conditional
probability of later opponent absorption under Never tends to zero, so the
tail Never payoff tends to zero. Finally, each pure finite stopping time and
Never is itself a feasible flow. Equation (13) therefore supplies the reverse
inequality without assuming a maximizing infinite greedy policy.

## Finite controller windows and semantic density

After a finite controller word, prescribe all players to Continue forever.
At ledger endpoint \(\ell=(Y,S,P,L,M)\), the exact semantic pair is

\[
\widehat U_i(\ell)=Y_i,
\qquad
\widehat B_i(\ell)
=
\max\{M_i,P_i+L_i\max(r_i(\{i\}),0)\}.
\tag{18}
\]

The first cap term records all elapsed finite stopping times; the second
records every later solo Quit and Never. Therefore minimizing a continuous
objective over a finite word controls the complete behavioral tester.

For a fixed target \(v\), define

\[
V_m(v)=
\min_{w\in X^m}
\max\left\{
\|u_w-v\|_\infty,\,
\max_i(b_{w,i}-u_{w,i})
\right\},
\]

where \((u_w,b_w)\) is the semantic pair of the word \(w\) followed by all
Continue. Compactness gives attainment. Appending an all-Continue root changes
no semantic pair, so \(V_m(v)\) is nonincreasing.

On semantic pairs \(z=(u,b)\), exact prefixing is

\[
T_x(u,b)_i
=
\left(
g_i(x)+c(x)u_i,\,
\max\{q_i(x),a_i(x)+\chi_i(x)b_i\}
\right).
\tag{19}
\]

Let

\[
e_\infty=(0,(\max\{r_i(\{i\}),0\})_{i\in I})
\]

be the all-Continue boundary. Then

\[
\boxed{
\mathcal K_r
=
\overline{\{T_we_\infty:w\text{ a finite product-root word}\}}.}
\tag{20}
\]

To prove density, truncate any actual chronology after \(m\) rows and append
all Continue. Prescribed payoffs converge absolutely. For player \(i\), write

\[
Q_t=P_t+L_tq_i(x^t).
\]

The original cap is

\[
\max\{\sup_tQ_t,P_\infty\},
\]

whereas the truncated cap is

\[
\max\left\{
\max_{t<m}Q_t,\,
P_m+L_m\max(r_i(\{i\}),0)
\right\}.
\tag{21}
\]

The only delicate case has \(L_\infty>0\) and positive solo reward. Then
positivity of the opponent-survival infinite product gives
\(\chi_i(x^t)\to1\), and

\[
|q_i(x^t)-r_i(\{i\})|
\le2R(1-\chi_i(x^t))\longrightarrow0.
\]

Thus the apparent terminal solo value in (21) is already the limit of genuine
finite stopping-date values and is dominated by \(\sup_tQ_t\). This proves
semantic convergence and hence (20).

## Uniform-horizon identification

For a fixed behavioral profile \(\sigma\), define

\[
E_H(\sigma)
=
\max_i\sup_{\tau_i}
\left[
U_i^H(\sigma[i\leftarrow\tau_i])-U_i^H(\sigma)
\right]
\tag{22}
\]

and terminal exploitability

\[
d(\sigma)=\max_i(B_i(\sigma)-U_i(\sigma)).
\]

Then

\[
\boxed{E_H(\sigma)\longrightarrow d(\sigma).}
\tag{23}
\]

For the lower bound, fix one player attaining \(d(\sigma)\) and one
behavioral replacement within \(\delta\) of its cap, then use
finite-average convergence for the two fixed profiles. For the upper bound,
\(\sigma\) is a terminal \((d(\sigma)+\delta)\)-Nash profile. The strict
terminal-to-uniform theorem gives one threshold after which every player and
every complete behavioral replacement has gain at most
\(d(\sigma)+2\delta\). This controls replacements selected separately for
each horizon. Let \(\delta\downarrow0\).

For a fixed target \(v\), define

\[
\begin{aligned}
W_r(v)=\inf_\sigma\inf_N\sup_{H\ge N}
\max\Bigl\{
&\|U^H(\sigma)-v\|_\infty,\\
&E_H(\sigma)
\Bigr\}.
\end{aligned}
\tag{24}
\]

Equation (23), payoff convergence, semantic density, and compactness prove
(1). For each fixed \((u,b)\), the delivery term is nonnegative and becomes
zero at the admissible target \(v=u\in[-R,R]^I\). Therefore

\[
\inf_{v\in[-R,R]^I}
\max\{\|u-v\|_\infty,\max_i(b_i-u_i)\}
=
\max_i(b_i-u_i)
\]

pointwise in \((u,b)\). Taking the carrier minimum proves (2). No
compactness assertion about \(\mathcal K_r\times\mathbb R^I\) is used.

If \(\eta(r)=0\), a carrier minimizer has \(b=u\). Finite-word profiles
converging to this point have terminal errors tending to zero and payoffs
converging to the one fixed target \(u\); terminal uniform-payoff selection
gives a uniform-equilibrium payoff. Conversely, every uniform-equilibrium
payoff yields terminal approximate Nash profiles at every accuracy. This
proves (3).

## Bellman and barrier duality

The semantic prefix maps \(T_x\) preserve the compact reward box
\(\mathcal Z_R\). Every
function barrier below is defined on \(\mathcal Z_R\), not on an unbounded
ambient payoff-pair space.

For fixed target \(v\in[-R,R]^I\), put

\[
\ell_v(u,b)
=
\max\{\|u-v\|_\infty,\max_i(b_i-u_i)\}
\]

and

\[
Q_v(z)=\inf_{w\in X^{<\omega}}\ell_v(T_wz),
\tag{25}
\]

including the empty word. Splitting a nonempty word at its first root gives

\[
Q_v(z)
=
\min\left\{
\ell_v(z),\,
\inf_{x\in X}Q_v(T_xz)
\right\}.
\tag{26}
\]

As an infimum of continuous finite-word functions, \(Q_v\) is bounded and
upper semicontinuous. It is the greatest bounded upper-semicontinuous
function satisfying

\[
q\le\ell_v,
\qquad
q(z)\le q(T_xz)
\quad(x\in X).
\tag{27}
\]

Indeed, iteration makes every feasible \(q\) bounded above by every
\(\ell_v(T_wz)\), while (26) proves that \(Q_v\) is feasible. Therefore

\[
W_r(v)=Q_v(e_\infty)=\max_q q(e_\infty).
\tag{28}
\]

For an arbitrary behavioral profile, finite Never-tail truncations converge
semantically. Monotonicity followed by upper semicontinuity transfers every
barrier inequality from finite words to that profile.

Replacing \(\ell_v\) by

\[
d(u,b)=\max_i(b_i-u_i)
\]

gives the target-free greatest barrier and value \(\eta(r)\).

Finally, (20) says that \(\mathcal K_r\) is the smallest closed
forward-invariant set containing \(e_\infty\). Every closed invariant set in
(4) therefore contains \(\mathcal K_r\), and the pair
\((\eta(r),\mathcal K_r)\) attains (4).

If a barrier or invariant set proves \(d\ge\Gamma>0\) on every actual
semantic pair, some player has cap debt at least \(\Gamma\). For every
\(0<\gamma<\Gamma\), the definition of the cap supplies an actual behavioral
deviation with gain at least \(\gamma\). The supremum need not be attained at
\(\Gamma\).

## Boundary tests

- The cap formula includes Never and arbitrarily late stopping.
- The flow formulation is exactly purified by hazards; it is not a relaxed
  correlated occupation measure.
- The transversality condition prevents the Bellman recursion from discarding
  unresolved Never mass.
- Strong duality does not assume a maximizing infinite greedy policy.
- The upper bound in (23) is uniform over horizon-dependent deviations.
- One carrier minimizer supplies one fixed target before
  accuracy-dependent profiles are selected.
- The Bellman inner operation in (26) is an infimum; upper semicontinuity does
  not guarantee a minimizing root.
- A positive cap floor \(\Gamma\) yields actual deviations for every smaller
  margin, not necessarily at the exact supremum.
- The canonical carrier and greatest barrier may be non-effective; logical
  completeness is not a finite-certificate theorem.

## Source correspondence

Existing checked foundations include:

- `quittingTerminalPayoff_update_eq_expect_stoppingLaw_pureTime` in
  `UniformEquilibrium/Quitting/Paths/BehaviorStoppingPayoff.lean`;
- `sSup_range_quittingTerminalPayoff_update_eq_pureTime` in
  `UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean`;
- `continuous_quittingTerminalSemanticPrefix` and
  `quittingTerminalSemanticPrefix_mem_carrier` in
  `UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`;
- `terminalSemanticCarrier_eq_closure_neverGeneratedSemanticReachable` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticGlobalDebtBarrierCertificate.lean`;
- `tendsto_finiteAveragePayoff_quittingGame` in
  `UniformEquilibrium/ProofView/Concepts/Stochastic/Models/Quitting/Asymptotic.lean`;
- `quittingGame_isUniformεEquilibrium_of_terminalNash` in
  `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformization.lean`;
- `quittingGame_isUniformEquilibriumPayoff_of_terminalTargetAcceptance` and
  `quittingGame_terminalNash_all_errors_of_isUniformEquilibriumPayoff` in
  `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`; and
- `not_exists_uniformEquilibriumPayoff_iff_exists_terminalExploitabilityGap`
  in `UniformEquilibrium/Quitting/Terminal/ExploitabilityGap.lean`.

The unified ledger, exact tester-flow duality, uniform-horizon value
identification, and function-barrier presentation are ordinary mathematics
not claimed here as already Lean-checked.

## Lean handoff

The implementation can be staged without introducing the full controller
package at once:

1. first prove the standalone fixed-profile theorem
   \(E_H(\sigma)\to\max_i(B_i(\sigma)-U_i(\sigma))\), using the checked
   terminal-to-uniform theorem for the uniform upper bound;
2. define the root polynomials and ledger update;
3. prove the closed forms, boundedness, and exact cap formula;
4. define tester flows, prove hazard purification, weak duality,
   transversality, and the pure-time/Never reverse inequality;
5. connect ledger endpoints to the existing semantic prefix operation;
6. reuse the checked finite-word carrier-density theorem;
7. define \(W_r\) and \(\eta\), and prove equations (1)--(3) using pointwise
   target elimination;
8. formalize barriers on the compact invariant box \(\mathcal Z_R\) and the
   smallest-invariant-set dual; and
9. expose the positive-gap decoder with the strict inequality
   \(0<\gamma<\Gamma\).

Do not encode a maximizing pure stopping time or minimizing semantic root:
neither need be attained.

## Scope and nonclaims

The packet gives an exact complete value and certificate language. It neither
proves \(\eta(r)=0\) for every Fin4 table nor constructs a concrete table with
\(\eta(r)>0\). It is not an online feedback-game theorem, and it does not
claim that a finite or semialgebraic barrier class is complete.
