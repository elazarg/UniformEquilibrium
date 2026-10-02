# Review of componentwise weighted potentials for affine membership gains

Reviewer: `CODEX_EULER`

## Verdict

**REVISE for export; mathematical theorem PASS.**

The SCC-by-SCC maximizer proof is correct, the quadratic adapter is correct,
and the checked sure-exit consumer really does upgrade the constructed pure
profile against unrestricted behavioral deviations.  The negative reciprocal
triangle is a valid strict novelty witness against the checked positive-cycle
signed-influence theorem.

The draft is not yet export-ready because its source comparison misidentifies
the older proposition and its proposed `QuittingInfluenceBlockCertificate`
Lean handoff is false for the new chamber.  Both defects are local and do not
affect the mathematical statement.

## Claim audited

For a finite player set, suppose the own membership gains are affine,

\[
g_i(S)=w_i(S\cup\{i\})-w_i(S)
      =a_i+\sum_{j\in S}c_{ij},\qquad i\notin S,
\]

and, in each SCC of the directed graph with edge `j -> i` when `c_ij != 0`,
there are positive weights satisfying

\[
  \lambda_i c_{ij}=\lambda_j c_{ji}.
\]

Then a sure-exit coalition exists.  The associated pure stationary profile is
an exact terminal Nash profile against all unilateral behavioral deviations,
and its reward is a uniform-equilibrium payoff.

## Mathematical audit

### SCC orientation and induction — PASS

With the convention `j -> i` iff `c_ij != 0`, an earlier condensation
component may influence a later one.  Thus, when solving component `C_k`, the
already chosen set `S_<k` contributes exactly

\[
  \theta_i=a_i+\sum_{j\in S_{<k}}c_{ij}.
\]

A later component cannot influence `i in C_k`, because that would be a
backward condensation edge.  Conversely, after `C_k` is solved, later choices
cannot alter its players' gains.  This is the correct topological direction.

### Weighted potential increment — PASS

For distinct `i,j` in one component, put
`psi_{ij}=lambda_i c_ij=lambda_j c_ji`.  Then insertion of `i` into
`T subset C_k` changes

\[
\Phi_k(T)=\sum_{i\in T}\lambda_i\theta_i+
           \sum_{\{i,j\}\subseteq T}\psi_{ij}
\]

by

\[
  \lambda_i\left(\theta_i+\sum_{j\in T}c_{ij}\right).
\]

Positive `lambda_i` preserves the payoff-gain sign.  Insertion maximality for
an outsider gives gain at most zero; deletion maximality for a member gives
gain at least zero.  Combining the component maximizers therefore gives
exactly the two fields of `IsQuittingSureExitSet`.

I also exhaustively tested all three-player affine instances with
`a_i,c_ij in {-1,0,1}` that satisfy the stated positive SCC
symmetrizability equations: 6,237 instances passed, with a stable coalition in
every case.  This is corroboration, not part of the proof.

### Quadratic-table adapter — PASS

Toggling player `i` adds `a_ii` and exactly the pair terms `b_{i,ij}` for
`j in S`; every term not involving `i` cancels.  Hence
`a_i=a_ii` and `c_ij=b_{i,ij}` are exact, including the empty-background case
under the checked zero extension.  Reciprocal equality is the unweighted
special case.

### Rank-one corollary — PASS

On a nontrivial SCC, strong connectivity forces the relevant `x_i` and `y_i`
to be nonzero.  If every `x_i y_i` has the same nonzero sign, then
`lambda_i=|y_i/x_i|` gives both sides of the symmetry equation equal to the
same signed product `y_i y_j` up to that common sign.

### Probability and agency — PASS

The new proof only produces a pure coalition.  The unrestricted-strategy
conclusion is supplied by the checked declarations in
`UniformEquilibrium/Quitting/Paths/SureExitSet.lean`:

- `isεAsymptoticNash_pureSetRoot_iff_isQuittingSureExitSet`;
- `isUniformEquilibriumPayoff_setReward_of_isQuittingSureExitSet`.

These quantify arbitrary unilateral behavioral deviations, including the
empty and singleton exit-set boundary cases.  No stationary best-response
restriction is being smuggled into the new argument.

## Novelty audit

### Versus `SignedInfluenceCycleBalance.lean` — genuinely incomparable/new chamber

For affine gains, every `c_ij` has a fixed background-independent sign, so the
checked sign-consistency hypothesis is automatic.  But positive SCC
symmetrizability only forces each reciprocal pair to have the same sign; it
does not force the product around an odd directed cycle to be positive.

The reciprocal triangle with every `c_ij=-1` is therefore decisive.  It is
positively symmetrizable with all weights one, while its directed triangle has
sign product `-1`.  It is outside
`quittingGame_exists_uniformPayoff_of_cycleBalancedSignConsistentInfluence`
and inside the present theorem.  In the other direction, cycle balance permits
background-dependent magnitudes and polarity-switchable asymmetric signs not
covered by the affine weighted-potential hypothesis.  Neither theorem
subsumes the other.

### Versus the curl-free notebook — extension is real, citation needs repair

The current
`notes/CODEX_GAUSS__CURL_FREE_TOGGLE_POTENTIAL.md` does not have the claimed
curl-free statement as “Proposition 3.”  Proposition 1 is the square-curl
characterization, Proposition 2 is its sure-exit consumer, and Section 3 gives
the symmetric pair-interaction subclass.  The current Proposition 3 is the
different quit-complementarity theorem.

The weighted theorem does strictly extend the Section 3 symmetric affine
subclass: positive reciprocal rescaling need not have `c_ij=c_ji`, and the
SCC construction admits arbitrary one-way cross-component influences.  The
draft should cite the actual proposition/section rather than “older
Proposition 3.”

### Versus generic potential infrastructure — not a duplicate

`GameProperties.lean` defines `IsWeightedExactPotential`, and
`MixedPotential.lean` transports a supplied global weighted potential to a
mixed extension.  Those declarations do not construct the componentwise
triangular potential or a quitting sure-exit coalition from the raw
coefficients.  The new actual-table adapter is therefore not already present.

## Mandatory repairs

1. In (2), quantify **distinct** `i,j in C`, since `c_ii` was never defined.
2. Replace the source statement “older conference Proposition 3” by the exact
   current references: Proposition 1, Proposition 2, and Section 3 of
   `CODEX_GAUSS__CURL_FREE_TOGGLE_POTENTIAL.md`.
3. Delete the proposed handoff through
   `QuittingInfluenceBlockCertificate`.  That structure contains a
   `BinaryBlockTriangularCertificate`, whose `within` field requires
   increasing differences after a polarity switch.  The negative reciprocal
   triangle—the draft's own novelty witness—has an odd negative sign cycle and
   admits no such switch.  Hence it cannot be discharged by that certificate.

   The correct Lean handoff is a new direct finite theorem: topologically
   order the SCCs, choose a `Finset` maximizer of each displayed weighted
   quadratic potential, assemble their coalitions, prove
   `IsQuittingSureExitSet`, then invoke the checked consumer.  The generic
   weighted-potential definitions may help with local algebra but are not the
   producer.
4. In the weighted-asymmetric boundary example, replace “arbitrary undirected
   interaction weights” by weights whose nonzero support makes the announced
   three-player component connected (or state the construction separately on
   each SCC).  Zero/disconnected choices do not define a three-player SCC.

## Export-gate assessment

After these repairs and a second independent falsification review, this meets
the mathematical significance gate as a genuinely new arbitrary-player
special-case existence theorem:

- the source class is a finite, exact condition on the actual reward table;
- the negative reciprocal triangle proves strict novelty over the closest
  checked producer;
- the output reaches a named unrestricted-behavior semantic consumer; and
- the theorem closes the precisely defined sign-frustrated symmetrizable
  affine/quadratic chamber.

It does **not** narrow the universal terminal-gap residual, classify all
quadratic tables, or imply that nonsymmetrizable tables lack a uniform payoff.
Those nonclaims should remain explicit.
