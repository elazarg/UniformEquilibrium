# Componentwise weighted-potential quitting games

Authors: `CHATGPT_EXTERNAL`

Independent reviews:
[`CODEX_EULER`](../feedback/CHATGPT_EXTERNAL__COMPONENTWISE_WEIGHTED_POTENTIAL_QUITTING__BY_CODEX_EULER.md),
[`CODEX_MINER`](../feedback/CHATGPT_EXTERNAL__COMPONENTWISE_WEIGHTED_POTENTIAL_QUITTING__BY_CODEX_MINER.md)

## Exact statement

Let \(I\) be a finite player set and \(r\) a quitting reward table. Extend
the reward to the empty coalition by nonabsorption payoff zero and write

\[
w_i(S):=\operatorname{quittingSetReward}(r,S,i).
\]

Assume there are real numbers \(a_i\) and \(c_{ij}\), for distinct players,
such that whenever \(i\notin S\),

\[
w_i(S\cup\{i\})-w_i(S)=a_i+\sum_{j\in S}c_{ij}. \tag{1}
\]

Let \(G_c\) be the directed graph with edge \(j\to i\) exactly when
\(c_{ij}\ne0\). Suppose that for every strongly connected component \(C\)
of \(G_c\), there are positive numbers \(\lambda_i^C\), \(i\in C\), such
that

\[
\lambda_i^Cc_{ij}=\lambda_j^Cc_{ji}
\qquad(i,j\in C,\ i\ne j). \tag{2}
\]

Then \(r\) has a quitting sure-exit set. Its pure stationary profile is an
exact terminal Nash profile against every unilateral behavioral deviation,
and its reward is a uniform-equilibrium payoff.

### Quadratic corollary

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

Thus (2) suffices. In particular,

\[
b_{i,ij}=b_{j,ij}\qquad(i\ne j) \tag{5}
\]

is sufficient, with every passive coefficient \(a_{ij}\), \(j\ne i\), and
\(b_{i,jk}\), \(i\notin\{j,k\}\), unrestricted.

## Conjecture-facing change

The checked theorem
`quittingGame_exists_uniformPayoff_of_cycleBalancedSignConsistentInfluence`
solves fixed-sign influence tables when every directed simple influence cycle
has positive sign product. The theorem above strictly enlarges that solved
chamber: it consumes sign-frustrated reciprocal negative cycles, including an
odd all-negative triangle, whenever their magnitudes are positively
symmetrizable within each SCC. It applies at every finite player count and has
an actual coefficient/table adapter and the checked sure-exit consumer.

It does not solve every quadratic table or contract the universal hard
residual without an additional producer of the symmetrizability hypothesis.

## Definitions and assumptions

The game is the ordinary discrete-time quitting game. At each live history,
every player privately randomizes between Quit and Continue. The first
nonempty simultaneous quitting coalition absorbs and receives \(r(S)\); play
that Continues forever receives zero. A unilateral deviation replaces one
player's complete behavioral strategy.

Equation (1) concerns only the gain from toggling player \(i\)'s membership
in a terminal coalition. It places no restriction on reward changes between
coalitions both omitting \(i\), and hence leaves passive continuation rewards
free. Equation (2) is required only for distinct players in the same SCC.

## Source correspondence

The exact downstream interfaces are checked in
`UniformEquilibrium/Quitting/Paths/SureExitSet.lean`:

* `IsQuittingSureExitSet`;
* `isεAsymptoticNash_pureSetRoot_iff_isQuittingSureExitSet`; and
* `isUniformEquilibriumPayoff_setReward_of_isQuittingSureExitSet`.

The closest checked producer is
`quittingGame_exists_uniformPayoff_of_cycleBalancedSignConsistentInfluence` in
`UniformEquilibrium/Quitting/Stationary/SignedInfluenceCycleBalance.lean`.
It is incomparable in general because it permits background-dependent
membership influences, but it excludes the sign-frustrated examples newly
covered here.

The older conference Propositions 1--2 and their Section 3 specialization in
`notes/CODEX_GAUSS__CURL_FREE_TOGGLE_POTENTIAL.md` prove the global unweighted
case \(c_{ij}=c_{ji}\). The SCC-wise weighted theorem is a strict extension:
it permits positive reciprocal rescaling within components and arbitrary
one-way influence between components.

Generic weighted-potential infrastructure is checked in
`UniformEquilibrium/ProofView/Core/GameProperties.lean` and
`UniformEquilibrium/ProofView/Concepts/Potential/MixedPotential.lean`.
`UniformEquilibrium/Quitting/Stationary/TogglePotential.lean` provides an
alternate checked consumer after a finite lexicographic SCC ordinal potential
is built. None of these files currently contains the SCC actual-data adapter
proved here.

## Proof

Topologically order the SCCs of \(G_c\) as \(C_1,\ldots,C_m\), with every
intercomponent edge pointing from an earlier component to a later one.
Suppose choices have been fixed on the earlier components and let their union
be \(S_{<k}\). For \(i\in C_k\), put

\[
\theta_i=a_i+\sum_{j\in S_{<k}}c_{ij}. \tag{6}
\]

No later component influences \(i\), since that would be a backward edge in
the condensation order. For an unordered pair \(\{i,j\}\subseteq C_k\), put

\[
\psi_{\{i,j\}}:=\lambda_i^{C_k}c_{ij}
=\lambda_j^{C_k}c_{ji}. \tag{7}
\]

Define, for \(T\subseteq C_k\),

\[
\Phi_k(T)=\sum_{i\in T}\lambda_i^{C_k}\theta_i
+\sum_{\{i,j\}\subseteq T}\psi_{\{i,j\}}. \tag{8}
\]

Choose a maximizer \(T_k\). If \(i\notin T_k\), comparison with
\(T_k\cup\{i\}\) gives

\[
0\ge\Phi_k(T_k\cup\{i\})-\Phi_k(T_k)
=\lambda_i^{C_k}\left(\theta_i+\sum_{j\in T_k}c_{ij}\right),
\]

and therefore

\[
\theta_i+\sum_{j\in T_k}c_{ij}\le0. \tag{9}
\]

If \(i\in T_k\), comparison with \(T_k\setminus\{i\}\) gives

\[
\theta_i+\sum_{j\in T_k\setminus\{i\}}c_{ij}\ge0. \tag{10}
\]

Let \(S^*=\bigcup_kT_k\). Later component choices do not change earlier
players' membership gains. Equations (1), (9), and (10) give

\[
\begin{aligned}
i\in S^*&\Longrightarrow w_i(S^*\setminus\{i\})\le w_i(S^*),\\
i\notin S^*&\Longrightarrow w_i(S^*\cup\{i\})\le w_i(S^*).
\end{aligned} \tag{11}
\]

These are exactly `IsQuittingSureExitSet r S*`. The checked terminal-Nash
characterization covers all behavioral deviations, including the empty
all-Continue and singleton-exit boundaries. The checked uniform consumer then
supplies the payoff \(w(S^*)\).

For (3), every term not involving \(i\) cancels between \(S\cup\{i\}\) and
\(S\), leaving (4). This proves the quadratic corollary.

## Boundary tests

### Sign-frustrated negative triangle

Set

\[
c_{12}=c_{21}=c_{23}=c_{32}=c_{31}=c_{13}=-1
\]

and all other membership influences to zero. Weights \(\lambda_i=1\) satisfy
(2). A directed three-cycle has negative sign product, so the current checked
cycle-balanced theorem does not apply, while the theorem above does.

### Asymmetric reciprocal magnitudes

Choose positive weights \(\lambda_i\), choose undirected interaction weights
\(\psi_{ij}\) whose nonzero support is connected inside a desired SCC, and
put \(c_{ij}=\psi_{ij}/\lambda_i\). Equation (2) holds although reciprocal
magnitudes generally differ.

### Rank-one chamber

If \(c_{ij}=x_i y_j\) and \(x_i y_i\) has one common nonzero sign on each
nontrivial SCC, then

\[
\lambda_i=\left|\frac{y_i}{x_i}\right|
\]

satisfies (2). A singleton SCC may use any positive weight.

### Symmetrizability is not necessary

For two active players, let

\[
r_1(S)=-\mathbf1_{1\in S}+2\mathbf1_{\{1,2\}\subseteq S},\qquad
r_2(S)= \mathbf1_{2\in S}-2\mathbf1_{\{1,2\}\subseteq S}.
\]

The reciprocal influences have opposite signs and no pure terminal coalition
is stable. Nevertheless the stationary profile in which both quit with
probability \(1/2\) is exact terminal Nash with payoff zero. The new theorem
is sufficient, not a characterization of all quadratic games.

As an independent falsification attempt, the first review exhaustively tested
6,237 admissible three-player affine-membership instances with coefficients
in \(\{-1,0,1\}\) and found no counterexample to the SCC construction.

## Adapter and consumer

The actual-data adapter is (1)--(2): finite coefficients extracted from the
complete table produce the SCC order and the finite maximizers \(T_k\). Their
union is a literal sure-exit coalition for the same table. The checked
sure-exit theorem then produces exact unrestricted terminal Nash and a
uniform-equilibrium payoff. No selected strategy or equilibrium is assumed as
input.

## Lean handoff

Formalize a predicate expressing (1), the nonzero influence graph, and an SCC
weight assignment satisfying (2). The shortest proof should:

1. use the existing SCC/condensation machinery from
   `MathUE.DirectedTransport.SCC`;
2. define the finite potential (8) for each component under the already chosen
   earlier set;
3. choose a maximizing subset and prove (9)--(10);
4. assemble `IsQuittingSureExitSet`; and
5. invoke `isUniformEquilibriumPayoff_setReward_of_isQuittingSureExitSet`.

Do **not** route the proof through `QuittingInfluenceBlockCertificate`: that
certificate requires increasing differences after one polarity switch and
cannot represent the odd negative triangle. A separate quadratic-coefficient
corollary may then prove (1) by finite-sum cancellation.

## Checked Lean realization

The game-independent finite binary construction is checked in
`MathUE/FiniteBinaryWeightedPotential.lean`. Its complete public declaration
inventory is:

- `BinaryBlockWeightedPotentialCertificate`, the triangular block certificate
  with positive exact-potential weights;
- `BinaryBlockWeightedPotentialCertificate.exists_isBinaryGainStable`, which
  assembles block maximizers into a pure binary equilibrium;
- `binaryAffineBlockPotential` and
  `binaryAffineBlockPotential_insert`, the explicit affine weighted potential
  and its insertion identity;
- `BinaryAffineBlockWeightedCertificate`,
  `BinaryAffineBlockWeightedCertificate.toBlockWeightedPotentialCertificate`,
  and
  `BinaryAffineBlockWeightedCertificate.exists_isBinaryGainStable`, the raw
  affine-data adapter and finite pure-equilibrium consumer.

The quitting-game adapter and semantic consumers are checked in
`UniformEquilibrium/Quitting/Stationary/ComponentwiseWeightedPotential.lean`.
Its complete public declaration inventory is:

- `IsAffineQuittingMembershipGain`,
  `QuittingAffineInfluenceEdge`,
  `quittingAffineInfluenceGraph`, and
  `IsComponentwisePositiveSymmetrizable`, which state the exact actual-table
  hypotheses;
- `quittingAffineInfluencePredecessors` and
  `quittingAffineInfluenceLevel`, which implement the condensation order;
- `exists_isQuittingSureExitSet_of_componentwiseWeightedPotential`, which
  constructs the literal sure-exit coalition;
- `exists_pureStationary_exactTerminalNash_of_componentwiseWeightedPotential`,
  which gives exact terminal Nash against every unilateral behavioral
  deviation;
- `quittingGame_exists_uniformPayoff_of_componentwiseWeightedPotential`, which
  supplies the uniform-equilibrium payoff;
- `quittingQuadraticSetExpression` and `IsQuadraticQuittingReward`, the
  complete quadratic-table representation;
- `IsQuadraticQuittingReward.isAffineQuittingMembershipGain` and
  `IsQuadraticQuittingReward.componentwisePositiveSymmetrizable`, the checked
  quadratic coefficient adapters; and
- `exists_isQuittingSureExitSet_of_quadratic_componentwiseWeightedPotential`,
  `exists_pureStationary_exactTerminalNash_of_quadratic_componentwiseWeightedPotential`,
  and
  `quittingGame_exists_uniformPayoff_of_quadratic_componentwiseWeightedPotential`;
- `exists_isQuittingSureExitSet_of_quadratic_activePairSymmetry`,
  `exists_pureStationary_exactTerminalNash_of_quadratic_activePairSymmetry`,
  and
  `quittingGame_exists_uniformPayoff_of_quadratic_activePairSymmetry`, the
  unit-weight quadratic corollaries.

Frozen realization hashes:

- packet: `9daad9345bb691e6bc096843f3804e61f06502eaaeac54331bc080acac46b802`;
- generic module:
  `78a8984a49b94efb1aabf5aed9072c561569295fd44114e2a2598d2c7a41e297`;
- quitting adapter:
  `fc7dc486ed993602411eabe33ff6ef9deb277486cad4d6096663b946e38c8bd9`.

Evidence seals:

- `M`: two independent mathematical audits passed the SCC direction,
  weighted-potential increment, quadratic adapter, rank-one chamber, and
  boundary behavior;
- `L`: the declarations above are proved in Lean under their displayed
  imports;
- `A`: the affine and quadratic predicates are extracted from the complete
  quitting reward table, and the SCC levels and weights feed the finite binary
  certificate without assuming a profile or equilibrium; and
- `C`: the constructed literal sure-exit coalition reaches the checked exact
  terminal-Nash consumer for unrestricted behavioral deviations and the
  checked uniform-equilibrium-payoff consumer.

The four boundary tests and the 6,237-instance enumeration above are
illustrative mathematical regression evidence, not separate Lean
declarations. The result is a sufficient solved chamber, not a
characterization: it does not prove that nonsymmetrizable tables lack a
uniform payoff, cover every quadratic table, produce the hypotheses for an
arbitrary hard-residual table, or advance the universal finite-quitting
conjecture without such a producer.

## Scope and nonclaims

The theorem is not an all-quadratic existence theorem. Passive coefficients
are free only because a sure-exit coalition absorbs immediately; they remain
relevant in unresolved dynamic mixed-equilibrium chambers. No claim is made
that a hard residual satisfies (2), that every negative cycle is
symmetrizable, or that this special class closes the finite-quitting
conjecture.
