# Componentwise weighted potentials for affine membership gains

Author: `CHATGPT_EXTERNAL`

Status: `TWO INDEPENDENT REVIEWS PASS; EXPORT PACKET PREPARED`

First review:
[`CODEX_EULER`](../feedback/CHATGPT_EXTERNAL__COMPONENTWISE_WEIGHTED_POTENTIAL_QUITTING__BY_CODEX_EULER.md).
The review's four required repairs are incorporated below.

Second review:
[`CODEX_MINER`](../feedback/CHATGPT_EXTERNAL__COMPONENTWISE_WEIGHTED_POTENTIAL_QUITTING__BY_CODEX_MINER.md).
Its source-bridge clarification is incorporated below.

## Result

Let `I` be a finite player set and let `r` be a quitting reward table. Extend
the reward to the empty coalition by nonabsorption payoff zero and write

\[
w_i(S):=\operatorname{quittingSetReward}(r,S,i).
\]

Assume there are numbers \(a_i\in\mathbb R\) and \(c_{ij}\in\mathbb R\) for
distinct players such that, whenever \(i\notin S\),

\[
w_i(S\cup\{i\})-w_i(S)
=a_i+\sum_{j\in S}c_{ij}. \tag{1}
\]

Let \(G_c\) have a directed edge \(j\to i\) exactly when \(c_{ij}\ne0\).
Suppose that for every strongly connected component \(C\) of \(G_c\) there
are positive numbers \(\lambda_i^C\), \(i\in C\), such that

\[
\lambda_i^C c_{ij}=\lambda_j^C c_{ji}
\qquad(i,j\in C,\ i\ne j). \tag{2}
\]

Then the table has a quitting sure-exit set. Consequently its stationary pure
profile is an exact terminal Nash profile against every unilateral behavioral
deviation, and its reward is a uniform-equilibrium payoff.

This is ordinary mathematics, not yet checked in Lean.

## Quadratic-table corollary

Suppose, for each player \(i\),

\[
r_i(S)=\sum_{j\in S}a_{ij}
 +\sum_{\{j,k\}\subseteq S}b_{i,jk}
\qquad(S\ne\varnothing), \tag{3}
\]

where the second sum is over unordered pairs. Then (1) holds with

\[
a_i=a_{ii},\qquad c_{ij}=b_{i,ij}. \tag{4}
\]

Thus (2), component by component, suffices for a pure exact terminal Nash
profile. In particular the reciprocal symmetry condition

\[
b_{i,ij}=b_{j,ij}\qquad(i\ne j) \tag{5}
\]

is sufficient, with all passive coefficients \(a_{ij}\), \(j\ne i\), and
\(b_{i,jk}\), \(i\notin\{j,k\}\), unrestricted.

## Proof

Topologically order the SCCs of \(G_c\) as \(C_1,\ldots,C_m\), so every edge
between different components points from an earlier component to a later one.
Inductively suppose choices have been fixed on the earlier components, and
write their union as \(S_{<k}\). For \(i\in C_k\), put

\[
\theta_i=a_i+\sum_{j\in S_{<k}}c_{ij}. \tag{6}
\]

No later component influences \(i\), because such an influence would be a
backward edge in the condensation order.

For an unordered pair \(\{i,j\}\subseteq C_k\), define

\[
\psi_{\{i,j\}}:=\lambda_i^{C_k}c_{ij}
=\lambda_j^{C_k}c_{ji}. \tag{7}
\]

On subsets \(T\subseteq C_k\), define

\[
\Phi_k(T)=
\sum_{i\in T}\lambda_i^{C_k}\theta_i
+\sum_{\{i,j\}\subseteq T}\psi_{\{i,j\}}. \tag{8}
\]

Choose a maximizer \(T_k\). If \(i\notin T_k\), maximality under insertion
gives

\[
0\ge \Phi_k(T_k\cup\{i\})-\Phi_k(T_k)
=\lambda_i^{C_k}\left(\theta_i+\sum_{j\in T_k}c_{ij}\right),
\]

so

\[
\theta_i+\sum_{j\in T_k}c_{ij}\le0. \tag{9}
\]

If \(i\in T_k\), maximality under deletion gives

\[
\theta_i+\sum_{j\in T_k\setminus\{i\}}c_{ij}\ge0. \tag{10}
\]

Set \(S^*=\bigcup_kT_k\). Later choices cannot alter an earlier player's
membership gain. By (1), (9), and (10),

\[
\begin{aligned}
i\in S^*&\Longrightarrow w_i(S^*\setminus\{i\})\le w_i(S^*),\\
i\notin S^*&\Longrightarrow w_i(S^*\cup\{i\})\le w_i(S^*).
\end{aligned} \tag{11}
\]

These are exactly `IsQuittingSureExitSet r S*`. The checked theorem
`isεAsymptoticNash_pureSetRoot_iff_isQuittingSureExitSet` identifies the pure
stationary profile as exact terminal Nash against the complete behavioral
strategy class. The checked theorem
`isUniformEquilibriumPayoff_setReward_of_isQuittingSureExitSet` then supplies
the uniform-equilibrium payoff \(w(S^*)\).

Equation (4) follows from (3) because every term not involving the toggled
player cancels in the membership difference. This proves the quadratic
corollary.

## Boundary and strictness tests

### Negative reciprocal triangle

Take three players and set

\[
c_{12}=c_{21}=c_{23}=c_{32}=c_{31}=c_{13}=-1,
\]

with every other membership influence zero. Every \(\lambda_i=1\) works.
The directed triangle has negative sign product, so it is outside the checked
positive-cycle signed-influence theorem, but the present theorem supplies a
sure-exit set for every choice of the passive reward coefficients.

### Weighted asymmetric magnitudes

The theorem is strictly broader than reciprocal equality. For example, on a
three-player SCC choose positive \(\lambda=(1,2,3)\), select undirected
interaction weights \(\psi_{ij}\) whose nonzero support is connected, and put
\(c_{ij}=\psi_{ij}/\lambda_i\). Then (2) holds although the reciprocal
magnitudes generally differ.

### Failure of symmetrizability is not failure of existence

The condition is sufficient, not necessary. For two active players, the
quadratic table

\[
r_1(S)=-\mathbf1_{1\in S}+2\mathbf1_{\{1,2\}\subseteq S},\qquad
r_2(S)= \mathbf1_{2\in S}-2\mathbf1_{\{1,2\}\subseteq S}
\]

has opposite reciprocal influences and no stable pure coalition, yet the
stationary profile with both quit probabilities \(1/2\) is exact terminal
Nash with payoff zero. Extra players with payoff
\(-\mathbf1_{i\in S}\) may be added as passive continuers. Hence the theorem
does not classify all quadratic tables.

### Rank-one corollary

If \(c_{ij}=x_i y_j\) and \(x_i y_i\) has one common nonzero sign on a
nontrivial SCC, then

\[
\lambda_i=\left|\frac{y_i}{x_i}\right|
\]

satisfies (2). Trivial singleton SCCs require no pair equation and may use any
positive weight. The nonzero qualification is necessary to make the displayed
weights well-defined; strong connectivity already forces the relevant edge
factors to be nonzero in a nontrivial rank-one SCC.

## Source and novelty audit

The downstream semantic consumer is already checked in
`UniformEquilibrium/Quitting/Paths/SureExitSet.lean`:

* `IsQuittingSureExitSet`;
* `isεAsymptoticNash_pureSetRoot_iff_isQuittingSureExitSet`; and
* `isUniformEquilibriumPayoff_setReward_of_isQuittingSureExitSet`.

The closest checked producer is
`quittingGame_exists_uniformPayoff_of_cycleBalancedSignConsistentInfluence` in
`UniformEquilibrium/Quitting/Stationary/SignedInfluenceCycleBalance.lean`.
It permits background-dependent influences but requires fixed signs and
positive sign product on every directed simple cycle. The negative reciprocal
triangle above is deliberately outside that class.

The older conference Propositions 1--2 and their Section 3 specialization in
`notes/CODEX_GAUSS__CURL_FREE_TOGGLE_POTENTIAL.md` prove the global unweighted
special case \(c_{ij}=c_{ji}\). The present SCC-wise weighted theorem is a
strict extension: it permits positive reciprocal rescaling inside a component
and arbitrary one-way influences between components.

The generic weighted-potential definitions and mixed-extension lemmas are in
`UniformEquilibrium/ProofView/Core/GameProperties.lean` and
`UniformEquilibrium/ProofView/Concepts/Potential/MixedPotential.lean`. They do
not currently provide this SCC condensation adapter.

The existing `QuittingInfluenceBlockCertificate` is **not** the right direct
handoff for the full theorem: its within-block certificate is based on
increasing differences after one polarity switch. A sign-frustrated negative
triangle satisfying (2) cannot in general be switched into that chamber. A
Lean proof should instead formalize the finite SCC maximizer construction
(6)--(10) directly (or add a genuinely weighted-potential block theorem), then
assemble the resulting `IsQuittingSureExitSet`. Reusing the current signed
block certificate would silently lose the principal new examples.

There is also a checked downstream route through
`UniformEquilibrium/Quitting/Stationary/TogglePotential.lean`. On the full
coalition cube, associate to a coalition the vector of its SCC potentials,
ordered from earlier to later components and with each later component's
potential evaluated using the displayed earlier choices. A toggle by a player
in component \(C_k\) leaves every earlier coordinate unchanged, changes the
\(k\)-th coordinate with exactly the sign of that player's payoff change, and
may alter only later coordinates. Ranking the finitely many such vectors
lexicographically therefore gives `HasQuittingToggleOrdinalPotential`.
`quittingGame_exists_uniformPayoff_of_toggleOrdinalPotential` is an alternate
checked consumer. For formalization, the direct sequential construction of
the sure-exit set is still the shortest proof.

No paper theorem is needed for the proof. The within-component argument is
the standard finite weighted-potential maximizer argument; the new
quitting-facing content is the SCC condensation construction and sure-exit
consumer.

## Conjecture-facing change

This is a genuine positive special-case theorem for arbitrary finite player
count. It closes a sign-frustrated quadratic chamber not covered by the
checked positive-cycle influence theorem. It does not contract the universal
terminal-gap residual unless a separate producer shows that every remaining
quadratic or hard-residual table is symmetrizable.

## Review requests

Because the conclusion invokes unrestricted behavioral deviations, two
independent reviews are required before export:

1. falsify or verify the SCC orientation, the weighted-potential increments,
   and the quadratic coefficient adapter;
2. independently audit novelty against the checked signed-influence theorem,
   the older curl-free note, and the sure-exit consumer.
