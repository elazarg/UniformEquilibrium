# Topology audit of `EXECUTABLE_ADAPTERS.md`

## Status and verdict

I audited Propositions 1--6 as ordinary mathematics, with emphasis on the
topology of stopping laws, compactness, moving feasible sets, decoded-limit
actuality, and the precise data needed by ranked recursion. I did not check
the later coherent-diagonal theorem or edit the author file.

The metric cores of Propositions 1--5 are correct after making the ambient
finite-player assumptions literal. In particular:

* recorded exact roots have a closed graph and one-root prefixing is
  continuous;
* closed graph plus the comparison-lift property is sufficient for argmax
  closure over a moving feasible set;
* the uniformly tight carrier in Lemma 3 is compact in the full
  \(\ell^1\) topology, including its separate Never atom;
* fixed-feasible-set approximate minimizers have exact minimizing cluster
  points; and
* a uniformly summable Cauchy decoder has an actual stopping-law limit, the
  displayed tail estimate, and a continuous limit map.

There are two genuine theorem-surface gaps.

1. Proposition 5 does **not** by itself prove the extra claim that the limit
   preserves a source-provenance or ancestry relation. It proves actuality
   of the output law. To inherit a stronger relation, that relation must be
   typed and closed, or source-faithfulness must be defined to mean only the
   displayed decoded-law construction.
2. Proposition 6 is not implied by the displayed type (28) alone. It needs a
   supplied map from every terminal certificate to an outcome. The prose says
   that terminal certificates contain a proved consumer, but that datum is
   absent from (28). Once it is made explicit, the proposition is elementary
   well-founded recursion and the transition bound is correct.

Neither gap undermines Propositions 1--4 or the law-level part of Proposition
5. They do block reading the six propositions as one fully specified
proof-relevant adapter interface without repair.

## Claim being checked

Fix a finite, nonempty player set \(I\), a bounded quitting reward table, and

\[
 K=\mathbb N\sqcup\{\infty\},\qquad
 \mathsf S=\Delta(K)^I,
 \qquad d(\mu,\nu)=\sum_{i\in I}\|\mu_i-\nu_i\|_1.
\]

The question is whether the hypotheses displayed in Propositions 1--6 imply,
respectively: selected-root closure and actual prefixing; moving argmax
closure; compactness of a tight law carrier; closure of approximate
minimizers; continuous actual decoded limits; and termination plus production
for natural-ranked transitions.

The finiteness of \(I\) should be stated in Section 1 rather than left to the
quitting-game context. It is used by the metric, the finite coalition sums,
the polynomial root equations, and compactness of the root cube. With an
infinite \(I\), the unweighted sum in (1) need not even be finite.

## Proposition 1: selected-root closure

This proposition is correct.

For fixed player \(i\), the complete replacement cap depends only on the
opponent law. If \(|r_i|\le R\), product-measure telescoping gives

\[
 |B_i(\mu)-B_i(\nu)|
 \le R\sum_{j\ne i}\|\mu_j-\nu_j\|_1.
\]

Thus \(B\) is continuous in the stated topology. The quantities \(Q_i\) and
\(C_i\) are finite polynomials in the root coordinates and affine in the
continuation vector. Both non-strict complementarity inequalities therefore
survive \((\mu^m,x^m)\to(\mu,x)\).

For a one-date prefix, playerwise coupling gives

\[
 \|T_{x_i}\mu_i-T_{y_i}\nu_i\|_1
 \le \|\mu_i-\nu_i\|_1+2|x_i-y_i|,
\]

and summing proves (9). Every output remains a probability law on \(K\), and
the exact law-to-hazard reconstruction makes it an actual behavioral profile.

This is consistent with the checked joint closedness of endpoint
complementarity in
`isClosed_isεQuittingRootEndpointNash_simplex` and compactness/nonemptiness
of its fixed-tail root slice in
`isCompact_and_nonempty_setOf_isZeroQuittingRootEndpointNash_root`, both in
`UniformEquilibrium/Quitting/Boundary/Repair/ComplementarityClosed.lean`.
The note's continuation vector is \(B(\mu)\), so the additional step needed
here is exactly the total-variation continuity of \(B\), which the displayed
opponent-law estimate supplies.

No continuous selector is proved or needed. The relation
\((\mu,x)\mapsto\text{“\(x\) is an exact root against \(B(\mu)\)”}\) is closed;
an endogenous rule choosing one root can still be discontinuous.

## Proposition 2: moving feasible sets

This proposition is correct, and condition (11) is exactly the missing half
of the moving-feasible-set argument.

Closed graph gives \(a^\star\in F(s)\). For a fixed competitor
\(a\in F(s)\), comparison lift provides \(a_m\in F(s_m)\) with
\(a_m\to a\). Continuity of \(f\) on its graph then permits passage to the
limit in

\[
 f(s_m,a_m^\star)\ge f(s_m,a_m).
\]

The comparison sequence may be chosen after fixing \(a\); no uniform choice
over all competitors is required. Hence the argument establishes the claimed
maximality.

Compactness of \(A\) and nonemptiness of \(F(s)\) are not used once the
convergence \(a_m^\star\to a^\star\) is assumed. They are the hypotheses that
normally produce maximizing points and convergent subsequences elsewhere in
the grammar. This is harmless redundancy, not a gap.

A closed graph alone is insufficient. The elementary model

\[
 F(t)=\{0\}\quad(t>0),\qquad F(0)=\{0,1\},
 \qquad f(t,a)=a
\]

already has a closed graph near \(0\), while the maximizers \(0\) for
\(t>0\) converge to a nonmaximizer at \(0\). Condition (11) fails at the new
competitor \(1\). The note's later maximal-cap-root example is a
game-semantic realization of precisely this mechanism.

For complete typing, the state space containing the \(s_m\)'s should be
declared metric, and “\(F\) is closed” in later fixed-fibre uses should be
distinguished from “the graph of \(F\) is closed.”

## Lemma 3: compact tight law carrier

Lemma 3 is correct in the full \(\ell^1(K)\) topology. The fact that the tail
bound controls only late **finite** dates is intentional: the atom at
\(\infty\) is one separately converging coordinate and belongs to the finite
core used in the proof.

Here is the missing detail implicit in the short proof. After diagonal
coordinate convergence, fix \(N\). For

\[
 E_N=\{0,\ldots,N,\infty\},
\]

the limits satisfy

\[
 \rho(E_N)=\lim_m\rho_m(E_N)\ge 1-T(N).
\]

Finite partial sums and nonnegativity show that the limiting coordinates have
total mass at most one; letting \(N\to\infty\) shows that their total mass is
at least one. Hence \(\rho\in\Delta(K)\), and

\[
 \sum_{n>N}\rho(n)=1-\rho(E_N)\le T(N).
\]

Finally,

\[
 \|\rho_m-\rho\|_1
 \le \sum_{k\in E_N}|\rho_m(k)-\rho(k)|+2T(N),
\]

so first choosing \(N\) and then \(m\) proves \(\ell^1\) convergence. This
also proves that the limit remains in \(\mathcal L_T\). Sequential
compactness is compactness because \(\ell^1(K)\) is metric.

The notation \(T(N)\downarrow0\) should explicitly mean a nonnegative
nonincreasing sequence tending to zero. Monotonicity is convenient but not
actually needed for this lemma; \(T(N)\to0\) and the displayed constraints
suffice.

## Proposition 4: fixed-law minimizers

Proposition 4 is correct when “closed” means closed relative to
\(\mathcal L_T\). Then \(F\) is compact. One subsequence
\(\rho_{m_k}\to\rho\) is chosen independently of the competitor. For each
fixed \(\eta\in F\), continuity gives

\[
 \Phi(s,\rho)
 \le \Phi(s,\eta),
\]

and arbitrariness of \(\eta\) proves exact minimality. There is no illicit
interchange of a limit and an infimum.

The final warning about moving feasible sets is correct. For
\(F=F(s)\), the sufficient sequential hypotheses are:

* outer closure: \(s_m\to s\), \(a_m\in F(s_m)\), and \(a_m\to a\) imply
  \(a\in F(s)\); and
* inner comparison lift: for every \(a\in F(s)\), there are
  \(a_m\in F(s_m)\) with \(a_m\to a\).

For approximate minimizers one also retains \(\varepsilon_m\ge0\) and
\(\varepsilon_m\to0\). These are the minimization analogues of Proposition
2. A closed graph without inner comparison lift cannot compare a limiting
candidate with feasible points that appear only at the limit.

## Proposition 5: Decode

### What the hypotheses do prove

The metric conclusion is correct after making “summable seam budget” literal:

\[
 c_n\ge0,\qquad \sum_n c_n<\infty.
\]

For every \(w=(s,z)\in W\), telescoping gives

\[
 d(M_m(w),M_N(w))\le\sum_{n=N}^{m-1}c_n.
\]

Because \(\mathsf S^q\) is complete, \(M_n(w)\) has a limit \(D(w)\), and
letting \(m\to\infty\) gives (24). The triangle inequality gives (25).
If each fixed \(M_N\) really has the displayed modulus on all of \(W\), then
one first chooses \(N\) with \(2C_N\) small and next uses that one fixed
modulus. This proves continuity without any equicontinuity in \(N\).

The phrase “carries the positive reach floors” must mean **uniform positive
reach floors on \(W\)** sufficient for the stated modulus. Pointwise positive
reach, with the lower bound tending to zero across \(W\), does not give the
global \(\omega_N\) used in (26). The clean hypothesis is simply:

> For every fixed \(N\), \(M_N:W\to\mathsf S^q\) has a stated modulus
> \(\omega_N\), with \(\omega_N(\delta)\to0\) as \(\delta\downarrow0\).

Since \(\Delta(K)\) is closed in \(\ell^1(K)\), the limit is a packet of
actual probability laws, not a Late boundary point. The checked declaration
`quittingBehaviorStoppingLaw_stoppingLawBehaviorStrategy` in
`UniformEquilibrium/Quitting/Terminal/StrategicallyPrecompactWatchdogProperBoundary.lean`
then realizes each law by a literal behavioral strategy. The exact semantic
preservation of complete stopping-law reconstruction is recorded by
`quittingTerminalSemanticPair_eq_compactStoppingLawsOfProfile` in
`UniformEquilibrium/Quitting/Terminal/OpponentTightTerminalSemanticRealization.lean`.
Thus “actual” is justified in the project's game-semantic sense.

Closedness of \(W\) is not needed for pointwise convergence or relative
continuity. It is what upgrades the graph from closed in
\(W\times\mathsf S^q\) to closed in the declared ambient product. Compactness
of \(Z\) is likewise not used in Proposition 5 itself; it is useful for later
witness extraction.

### What the hypotheses do not prove

The sentence

> This is source-faithful because every \(M_n\) is rooted at the same actual
> input source, and the passport retains those ancestry maps.

does not follow from (19)--(21). Those equations mention only output
actuality and metric closeness. A sequence of outputs can converge in
\(\mathsf S^q\) while a separately intended ancestry, suffix, regeneration,
or source-feasibility relation fails at the limit if that relation is not
closed. Merely saying that a “common source-provenance map” is recorded does
not type the relation or give it a limit theorem.

There are two exact repairs.

1. If source-faithfulness means only that \(D(s,z)\) is the uniform Cauchy
   limit of the displayed, source-indexed actual macros, define it that way.
   Then Proposition 5 proves the claim by definition.
2. If it means a stronger semantic relation, introduce a closed set

   \[
   \mathcal R\subseteq W\times\mathsf S^q
   \]

   and assume \((w,M_n(w))\in\mathcal R\) for every \(n\). Closedness then
   gives \((w,D(w))\in\mathcal R\). For proof-relevant ancestry witnesses,
   instead put the witnesses in a compact carrier, retain convergent witness
   data, and require the witness relation to have closed graph.

There is also a terminology fork. The hypotheses prove behavioral
executability, meaning existence of a legal profile obtained from the limit
law. They do not prove algorithmic computability: the \(M_n\)'s may contain
noncomputable selections, and convergence of \(\sum c_n\) need not be supplied
with an effective tail-rate algorithm. If “executable” is intended in the
computability sense, effective codes for \(M_n\), \(z\), and the tail modulus
must be added. In the project's usual “actual behavioral compiler” sense, no
such addition is needed.

## Proposition 6: ranked transitions

The natural-number argument is correct under the prose hypothesis that every
terminal certificate includes a consumer, but it is not a theorem of the
displayed type (28) alone.

Indeed, take one node \(N\) with \(\rho(N)=0\), let
\(\operatorname{Terminal}(N)\) be the one-point type, and let
\(\mathcal O(N)\) be empty. Then a terminal value of `step(N)` exists exactly
as in (28), but no outcome in \(\mathcal O(N)\) exists. This is a literal
counterexample to Proposition 6 if (28) is the whole interface.

The repair is to display all the data:

\[
 \operatorname{consume}_N:
   \operatorname{Terminal}(N)\to\mathcal O(N),
\]

together with a total `step` for every ranked node, and, in the successor
branch, the strict-rank proof, an actual child execution, and the backward
compiler \(\mathcal O(N')\to\mathcal O(N)\). Induction on \(\rho(N)\) then
produces the outcome. Every strict decrease of a natural rank lowers it by at
least one, so a chain starting at \(N\) has at most \(\rho(N)\) nonterminal
transitions.

The same repair makes Corollary 7 immediate: a nonempty set of natural-ranked
nodes has a node of minimum rank, which cannot have a strictly lower-ranked
successor inside the set.

This is a sound consumer for a **supplied** rank, step function, terminal
consumer, actual child adapter, and backward compiler. It is not evidence that
any Fin4 regeneration relation supplies those objects.

## Novelty and scope

Propositions 1, 2, 4, and 6 are standard closed-graph, optimization, and
well-founded-recursion arguments. Lemma 3 is the standard discrete
tightness-to-\(\ell^1\)-compactness argument, specialized usefully to keep
Never as a separate atom. Their value here is interface discipline, not a new
arbitrary-game producer.

The genuinely useful new architectural content is the combination of:

* the explicit comparison-lift obligation for endogenous maximal roots; and
* the uniform summable-seam criterion showing that a decoder can be
  continuous even though no modulus is uniform over all decoder depths.

Even after the repairs above, these remain conditional adapter theorems. No
comparison lift for the project's maximal-cap-root correspondence, no
summable source-faithful decoder for a Fin4 regeneration, and no consumed
decreasing Fin4 rank is produced by Propositions 1--6.

## Sources inspected

I used the stopping-law and compactness routes named in `docs/TOOLKIT.md` and
inspected only the following declarations and their local definitions:

* `quittingBehaviorStoppingLaw_stoppingLawBehaviorStrategy` in
  `UniformEquilibrium/Quitting/Terminal/StrategicallyPrecompactWatchdogProperBoundary.lean`;
* `quittingTerminalSemanticPair_eq_compactStoppingLawsOfProfile` and
  `quittingTerminalSemanticPair_eq_of_opponentTight_lawLimit` in
  `UniformEquilibrium/Quitting/Terminal/OpponentTightTerminalSemanticRealization.lean`;
* `quittingTerminalPayoff_update_sub_le_two_mul_bound_mul_stoppingLawTV` in
  `UniformEquilibrium/Quitting/Paths/StoppingLawExposure.lean`;
* `isClosed_isεQuittingRootEndpointNash_simplex` and
  `isCompact_and_nonempty_setOf_isZeroQuittingRootEndpointNash_root` in
  `UniformEquilibrium/Quitting/Boundary/Repair/ComplementarityClosed.lean`;
* `continuous_quittingRootCoordinateNashDefect_simplex` in
  `UniformEquilibrium/Quitting/Root/NashDefectContinuity.lean`; and
* `CompactStoppingLaw.toPMF`, `CompactStoppingLaw.ofPMF`, and
  `compactStoppingLawEquivPMF` in
  `MathUE/ProbabilityMassFunction/CompactStoppingLaw.lean`.

The conclusions in this review are ordinary mathematics, not new Lean-checked
declarations.

## Requested next check

After the interface is repaired, the sharp next mathematical question is:

> Is there any nontrivial project regeneration relation whose ancestry fibre
> is closed in the total-variation topology, or whose actual descendants
> admit a uniform summable-seam decoder?

Without one such application theorem, Proposition 5 remains a strong decoder
schema but does not discharge the current source-faithful regeneration gap.
