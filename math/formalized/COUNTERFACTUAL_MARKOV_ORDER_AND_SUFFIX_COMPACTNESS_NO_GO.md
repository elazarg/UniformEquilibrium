# Counterfactual Markov order and the suffix-compactness obstruction

Authors: Math conference synthesis

Independent reviews:
[architecture review](../feedback/SUFFICIENT_STATE__BY_ARCHITECTURE.md),
[collision audit](../feedback/SUFFICIENT_STATE__BY_COLLISION_AUDIT.md), and
[compactness audit](../feedback/SUFFICIENT_STATE__BY_COMPACTNESS_AUDIT.md).
The later [formalizer audit](../feedback/META_EXPORTS__BY_FORMALIZER.md)
confirmed the theorem with the displayed scope qualifications.

## Exact statement

Let \(I\) be a finite player set of cardinality \(n\ge2\). A behavioral
profile in a quitting game determines independent first-stopping laws

\[
\mu_i\in\Delta(\overline{\mathbb N}),
\qquad
\overline{\mathbb N}=\mathbb N\cup\{\infty\},
\]

where \(\infty\) means Never. Let \(\Omega\) record Never and the labelled
terminal quitting coalition, optionally together with the terminal date.

For \(A\subseteq I\) and \(t_A\in\overline{\mathbb N}^{A}\), let
\(K_\sigma(A,t_A)\) be the terminal-outcome law after fixing each player in
\(A\) to the displayed pure stopping time and leaving every other player's
strategy unchanged. Let \(\mathcal K_k(\sigma)\) collect these laws for
\(|A|\le k\).

The following hold.

### A. Exact replacement order

1. \(\mathcal K_{k+1}(\sigma)\), together with the new stopping law
   \(\nu_i\), determines
   \(\mathcal K_k(\sigma[i\leftarrow\nu_i])\) by an explicit affine formula.
2. \(\mathcal K_{n-1}\) is closed under every succession of unilateral
   behavioral replacements.
3. For every \(0\le k\le n-2\), \(\mathcal K_k\) is not closed under one
   unilateral replacement: two deterministic finite-clock profiles can have
   equal order-\(k\) states and unequal order-\(k\) successor states.
4. Hence, within this labelled pure-intervention hierarchy, the least
   replacement-closed order is exactly

   \[
   k_{\min}=n-1.
   \]

   In particular, the Fin4 order is \(3\).
5. On actual profiles, \(\mathcal K_{n-1}\) is losslessly equivalent to the
   labelled tuple of marginal stopping laws \((\mu_i)_{i\in I}\).
6. Order \(1\) already determines current prescribed payoffs and unrestricted
   unilateral behavioral caps.
7. In the operational total-variation metric, common replacement is
   nonexpansive, and changing both the source state and replacement law obeys
   the corresponding additive stability bound.

These statements concern labelled coalition-outcome laws. They need not hold
for laws of reward vectors when distinct coalitions have the same reward.

### B. Current payoff-response data do not determine literal suffixes

There is a rational four-player reward table and two positive-reach behavioral
profiles whose terminal payoff-vector laws agree after every current
unilateral behavioral replacement, including Never and arbitrarily late
stopping, but whose one-step literal suffixes have different prescribed
payoffs.

Consequently no state factoring through those current payoff-response laws
can simultaneously:

1. determine prescribed payoff;
2. give a congruent state transition for the labelled one-step literal
   suffix; and
3. realize the successor by the actual literal suffix.

### C. No compact state with one all-depth suffix modulus

There is a bounded rational Fin4 table for which no sequentially compact
metric state of actual profiles can satisfy one continuity estimate,
with a common modulus, for every labelled operation

\[
\text{suffix at depth }m
\quad\text{then one fixed pure-time replacement}.
\]

The failure persists when all tested suffix histories have reach probability
bounded uniformly away from zero. It also rules out a finite global
approximation net at any sufficiently small fixed accuracy for all such
suffix probes simultaneously.

This does not rule out continuity for each fixed depth, a modulus selected
after fixing a finite program, or sourcewise finite-clock approximation.

## Conjecture-facing change

Part A answers the exact finite counterfactual replacement-order problem.
Parts B and C rule out the original proposal of one compact recursively
congruent state with a depth-independent modulus for every calendar suffix.

The remaining open state problem is narrower: construct a finite-program,
two-tier, projective, or otherwise program-dependent architecture with an
executable diagonal synthesis theorem. It is stated in
`questions/QUITTING_COMPOSITIONALLY_SUFFICIENT_STATE.md`.

These results do not prove a uniform equilibrium and do not construct a
positive-gap table.

## Definitions and assumptions

Let

\[
\Phi:\overline{\mathbb N}^{I}\to\Omega
\]

be the deterministic map sending a vector of stopping times to Never or to
the earliest-time quitting coalition. Then

\[
K_\sigma(A,t_A)
=
\Phi_\#
\left(
\bigotimes_{j\in A}\delta_{t_j}
\otimes
\bigotimes_{j\notin A}\mu_j
\right).
\tag{1}
\]

Behavioral randomization is private and independent across players. Before
absorption there is one public live history at each date, so every behavioral
strategy induces a first-stopping law. Conversely, every law on
\(\overline{\mathbb N}\) is realized by its conditional hazards.

For a fully pure vector \(t_I\), define

\[
\Gamma(t_I)=\delta_{\Phi(t_I)}.
\tag{2}
\]

This law is universal and independent of the source profile.

## Proof of A

### Replacement formula

Replace player \(i\) by a behavioral strategy with stopping law \(\nu_i\).
For every \(A\subseteq I\),

\[
K_{\sigma[i\leftarrow\nu_i]}(A,t_A)
=
\begin{cases}
K_\sigma(A,t_A),&i\in A,\\[1.5ex]
\displaystyle
\int_{\overline{\mathbb N}}
K_\sigma^+
\bigl(A\cup\{i\},t_A\oplus(i\mapsto s)\bigr)
\,d\nu_i(s),&i\notin A,
\end{cases}
\tag{3}
\]

where \(K_\sigma^+\) agrees with \(K_\sigma\) below full order and equals
\(\Gamma\) at full order. This is disintegration in the new independent
stopping-time coordinate.

Thus order \(k+1\) determines the successor order \(k\). At order \(n-1\),
the only apparently missing order-\(n\) query fixes every player and therefore
equals the universal law (2). Hence \(\mathcal K_{n-1}\) is closed under one
replacement, and iteration gives closure under every finite succession.

### Lower-order separation

Fix \(0\le k\le n-2\). Choose a hidden player \(h\), a blocker set

\[
B\subseteq I\setminus\{h\},
\qquad |B|=k+1,
\]

and dates \(a<b<c\). Put \(R=I\setminus(B\cup\{h\})\). Define deterministic
profiles by

\[
T_h^\sigma=b,\qquad T_h^{\sigma'}=c,
\]

\[
T_j^\sigma=T_j^{\sigma'}=a\quad(j\in B),
\qquad
T_j^\sigma=T_j^{\sigma'}=c\quad(j\in R).
\tag{4}
\]

For an intervention on at most \(k\) players, either \(h\) is overwritten or
some blocker remains at the earlier date \(a\). Therefore

\[
\mathcal K_k(\sigma)=\mathcal K_k(\sigma').
\tag{5}
\]

Choose \(b_0\in B\), replace \(b_0\) by pure time \(c\), and query the
successor after fixing every player in \(B\setminus\{b_0\}\) to \(c\). Under
\(\sigma\), player \(h\) Quits alone at \(b\). Under \(\sigma'\), every player
Quits at \(c\). The successor order-\(k\) laws differ even if terminal dates
are omitted. This proves failure of closure at every lower order.

### Marginal-law equivalence

Equation (1) reconstructs every counterfactual law from the marginals.
Conversely, fix \(i\) and choose an anchor \(a\ne i\). To recover
\(\mu_i(\{t\})\), fix the anchor at \(t\), fix every other player except
\(i\) to Never, and inspect the probability of terminal coalition
\(\{i,a\}\). To recover \(\mu_i(\{\infty\})\), fix every opponent to Never
and inspect the probability of the Never outcome. Hence
\(\mathcal K_{n-1}\) recovers every marginal law.

On marginal tuples, replacement is coordinate overwrite.

### Payoffs, caps, and stability

For a bounded reward function \(\bar r_\ell:\Omega\to\mathbb R\),

\[
U_\ell(K)=\int_\Omega\bar r_\ell\,dK(\varnothing).
\tag{6}
\]

Player \(i\)'s pure-time payoff menu and cap are

\[
G_i^K(s)=\int_\Omega\bar r_i\,dK(\{i\},s),
\qquad
B_i(K)=\sup_{s\in\overline{\mathbb N}}G_i^K(s).
\tag{7}
\]

An arbitrary behavioral response is a probability mixture of pure stopping
times and Never, so the supremum in (7) is the complete behavioral cap.

Define

\[
d_k(K,L)
=
\sup_{|A|\le k,\,t_A}
\|K(A,t_A)-L(A,t_A)\|_{\mathrm{TV}}.
\]

Convexity in (3) gives

\[
d_{n-1}(U_i^\nu K,U_i^\nu L)\le d_{n-1}(K,L)
\tag{8}
\]

and

\[
d_{n-1}(U_i^\nu K,U_i^{\nu'}L)
\le d_{n-1}(K,L)+\|\nu-\nu'\|_{\mathrm{TV}}.
\tag{9}
\]

## Proof of B

Use players \(I=\{1,2,3,4\}\) and

\[
r^\star(S)=
\left(1,\mathbf 1_{\{2,3\}\subseteq S},0,0\right)
\qquad(\varnothing\ne S\subseteq I),
\tag{10}
\]

with payoff zero at Never.

Let \(x_i^m\) denote player \(i\)'s Quit hazard at live date \(m\), and let
\(S_m\sigma\) be the literal suffix after \(m\) all-Continue outcomes. If
player \(3\) is replaced by sure Quit at the first suffix date, then immediate
absorption is certain and player \(2\)'s payoff is one exactly when player
\(2\) also Quits. Therefore

\[
U_2((S_m\sigma)[3\leftarrow Q_3^0])=x_2^m.
\tag{11}
\]

Fix \(a\in(0,1)\). In profile \(\sigma\), player \(1\) has its only positive
Quit hazard, of size \(a\), at date \(0\). In profile \(\rho\), the same
hazard occurs at date \(1\). Players \(2,3,4\) always Continue.

Every absorbing outcome reachable after at most one current unilateral
replacement has payoff vector \(e_1=(1,0,0,0)\). If player \(1\) is replaced,
the displaced clock disappears. If another player is replaced, at most one
of players \(2,3\) can be active, so the second payoff coordinate remains
zero. If \(\alpha(\tau_i)\) is the replacement's eventual Quit probability,
the Never probability is

\[
(1-a)(1-\alpha(\tau_i))
\]

for both sources. Hence the complete current payoff-vector law is equal for
the prescribed profiles and after every unilateral behavioral replacement.

After one all-Continue outcome,

\[
U(S_1\sigma)=0,
\qquad
U(S_1\rho)=ae_1.
\tag{12}
\]

The suffix histories have positive reach \(1-a\) and \(1\). Equal current
response states would therefore force equal realized suffix states, while
payoff observability and (12) force them to differ.

## Proof of C

Use the same table (10). Suppose a metric state map \(\Psi\) and a function
\(\omega(\delta)\to0\) as \(\delta\downarrow0\) satisfy, for every pair of
actual profiles and every date \(m\),

\[
\left|
U_2((S_m\sigma)[3\leftarrow Q_3^0])
-
U_2((S_m\rho)[3\leftarrow Q_3^0])
\right|
\le
\omega(d(\Psi(\sigma),\Psi(\rho))).
\tag{13}
\]

Fix \(p\in(0,1)\). For each \(m\), let \(\sigma^m\) have the single hazard
\(x_2^m=p\), with every other hazard zero. Every finite live history has reach
at least \(1-p\). For \(m\ne\ell\), equation (11), probed at depth \(m\),
gives payoff difference \(p\). Choose \(\delta>0\) such that
\(\omega(d)<p\) whenever \(d<\delta\). Equation (13) implies

\[
d(\Psi(\sigma^m),\Psi(\sigma^\ell))\ge\delta.
\tag{14}
\]

The state image therefore contains an infinite uniformly separated family.
It is not totally bounded and cannot have sequentially compact closure.

For the finite-net statement, choose \(N\) binary hazards
\(x_2^t=pa_t\), \(a\in\{0,1\}^N\). Distinct binary words differ at a depth
detected by (11), so their images are pairwise \(\delta\)-separated. A global
net of radius below \(\delta/2\) would require at least \(2^N\) points for
every \(N\), which is impossible for one finite net.

## Boundary tests

- The lower-order separation uses deterministic finite clocks, so it does not
  rely on compact limits, nonbehavioral correlation, or payoff aliases.
- Coalition labels are essential for the exact order theorem. If only reward
  vectors are observed, two coalitions with the same reward may be
  indistinguishable.
- The suffix collision uses positive-reach histories.
- The compactness obstruction requires one modulus independent of the
  labelled depth. In the product topology, every fixed depth remains
  continuous.
- Every actual profile has sourcewise rational finite-clock approximations
  uniform over static pure interventions. The no-go concerns one finite global
  net controlling all moving-depth suffix probes.
- At a zero-survival history, marginal stopping laws do not determine the
  literal off-path policy. No arbitrary off-path suffix closure is claimed.

## Source correspondence

The behavioral stopping-law reduction and pure-time extremality correspond to:

- `quittingTerminalPayoff_update_eq_expect_stoppingLaw_pureTime` in
  `UniformEquilibrium/Quitting/Paths/BehaviorStoppingPayoff.lean`;
- `sSup_range_quittingTerminalPayoff_update_eq_pureTime` and
  `quittingProfileLiveRoot_update_eq_rootSequenceUpdate` in
  `UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean`; and
- `StoppingLaw.stoppingLaw_toScalarHazard` in
  `MathUE/Probability/StoppingLawReconstruction.lean`.

The law-valued counterfactual hierarchy, exact minimal-order theorem, payoff
response collision, and all-depth compactness obstruction are new ordinary
mathematics. They are not claimed to be Lean-checked.

## Lean handoff

The narrow implementation order is:

1. define the labelled terminal map on independent stopping laws and the
   order-\(k\) pure-intervention kernel;
2. prove the replacement integral formula;
3. prove closure at order \(n-1\) and the deterministic blocker separation;
4. prove recovery of marginal stopping laws;
5. expose payoff and cap evaluation plus total-variation nonexpansiveness;
6. encode the rational Fin4 probe table and payoff-response collision; and
7. formalize the isolated-spike packing theorem as a general metric lemma,
   then instantiate it with the probe identity.

The topology theorem should quantify explicitly over one common modulus and
the same labelled depth on both sources. It should not be generalized to
fixed-depth continuity.

## Scope and nonclaims

This packet does not construct a compositionally sufficient synthesis state,
an executable boundary transition, a uniform-equilibrium payoff, or a
positive-gap counterexample. Its exact contribution is the replacement-order
classification and a decisive obstruction to one stronger compact-state
specification.

## Lean formalization record

Pre-formalization packet SHA-256:
`cd8d29a90c51a6e2bc0fb8f3f1eefd95d767f632948dd2b9a05c5f299a9e4d6d`.
The earlier source-correspondence sentence saying that the new mathematics was
not claimed Lean-checked is superseded by this record.

The hierarchy and total-variation layer landed in commit
`eda3edaff8bed4a0146b16fbcb06eb13ff963763`; production integration and the
terminal-outcome lowering landed in
`289dfd1ee56bf170ad535f63302be798defd7a1a`; the compactness no-go landed in
`4bddd9d716dc42794272482fa3509bc79032a207`.

The checked owners are
`UniformEquilibrium/Quitting/Paths/CounterfactualStoppingLaw.lean`,
`MathUE/Topology/UniformProbeCompactness.lean`, and
`UniformEquilibrium/Diagnostics/Quitting/CounterfactualSuffixCompactnessNoGo.lean`.
The principal declarations are
`quittingCounterfactualReplacementDetermining_iff`,
`quittingCounterfactualReplacementDetermining_sharp`,
`quittingBehaviorStoppingLaws_update`,
`quittingTerminalPayoff_update_eq_expect_behaviorStoppingLaws`,
`quittingBehaviorDeviationPayoffCap_eq_pureTime`,
`pmfTV_quittingCounterfactualOutcomeLaw_update_le`,
`no_currentResponseQuotient_suffixTransition_payoffObservable`,
`not_isSeqCompact_of_commonAllDepthSpikeState`, and
`exists_no_finite_net_of_commonAllDepthSpikeState`.

Evidence seals are `M` and `L`; the behavioral replacement bridge and the
explicit Fin4 regressions have source `A`.  There is no equilibrium or
recursive-closure `C`.  The no-go does not construct a sufficient synthesis
state, executable suffix transition, uniform-equilibrium payoff, or
positive-gap counterexample, and it does not exclude fixed-depth continuity,
depth-dependent moduli, or finite programs.
