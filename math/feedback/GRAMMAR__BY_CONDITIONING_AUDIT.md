# Conditioning audit of `GRAMMAR.md`

## Scope and verdict

This review checks Sections 1, 3, and 5: the conditioning modulus, the
provenance interface, and the proposed `CSR_1` obstruction.

The quantitative conditioning calculation and every displayed calculation in
the two-law witness are correct under the standard half-`L^1` convention for
total variation.  The witness proves a sharp law-level fact: closing the graph
of positive-reach conditional suffixing adds arbitrary successors over a
zero-reach source, so the closed relation cannot itself be interpreted as the
graph of legal positive-reach suffixing.

The current conclusion is nevertheless too broad in three ways.

1. The abstract `CW` syntax as written accepts any named closed relation, so
   `CSR_1` formally *is* a `CW` edge unless `CW` is separately required to
   certify the intended legal transition semantics.
2. The self-loop rules out a rank determined only by the stopping-law state
   and decreasing on every `CSR_1` pair.  It does not rule out an external
   occurrence budget or another enlarged-state rank of the form allowed by
   `RD`.
3. The fixed tester has discrepancy one at the *conditional target*, but its
   gain at the original source is only the vanishing reach `p_n`.  Thus the
   example is not a no-go for an unconditional controller payoff, for a
   reach-weighted consumer, or for the uniform-equilibrium conjecture.

After those scope repairs, the `CSR_1` example is a correct and useful no-go
for exact, unweighted, law-level, source-attached conditional regeneration.

## Sources inspected

The project source most directly supporting the provenance discussion is
`Research/Quitting/SourceFaithfulMinimumLawCausalization.lean`.  The structure
`QuittingSourceFaithfulMinimumCausalization` is indexed by the supplied
`profiles` and `mark` families; `nonempty_sourceFaithfulMinimumCausalization`
selects only the new cutoffs and root words.  This really does prevent hidden
profile or mark reselection.

The Fin4 specialization is
`Research/Quitting/FinFourProducerAtlas/SourceFaithfulThreeRoleRegeneration.lean`.
The definitions `sourceFaithfulTargetProfile` and
`sourceFaithfulTargetMark`, the structure
`FinFourSourceFaithfulMinimumTargetRegeneration`, and the declarations
`chronology_profile_eq` and `chronology_mark_eq` retain the literal incoming
families.  These declarations justify the final paragraph of Section 1, but
they are richer than a bare stopping-law ancestry tag.

For the distinction between stopping laws and complete behavioral strategies,
I inspected `StoppingLaw.toScalarHazard` and
`StoppingLaw.stoppingLaw_toScalarHazard` in
`MathUE/Probability/StoppingLawReconstruction.lean`, together with
`quittingStoppingLawBehaviorStrategy` and
`quittingBehaviorStoppingLaw_stoppingLawBehaviorStrategy` in
`UniformEquilibrium/Quitting/Terminal/StrategicallyPrecompactWatchdogProperBoundary.lean`.
The canonical hazard is set to zero once survival is zero.  Consequently a
stopping law does not remember arbitrary behavioral choices after a
zero-probability history.

## 1. Conditioning modulus

Let

$$
A=\{d,d+1,\ldots,\infty\},\qquad
a=\mu(A),\qquad b=\nu(A),\qquad
\Delta=d_{\mathrm{TV}}(\mu,\nu).
$$

For a shifted event `B`, write `C` for its unshifted preimage in `A`.  Then

$$
\begin{aligned}
\left|\frac{\mu(C)}a-\frac{\nu(C)}b\right|
&\le \frac{|\mu(C)-\nu(C)|}{a}
  +\nu(C)\frac{|a-b|}{ab} \\
&\le \frac{\Delta}{a}+\frac{|a-b|}{a} \\
&\le \frac{2\Delta}{\rho}
\end{aligned}
$$

whenever `a,b >= rho`.  Taking the supremum over events proves (1).  The
shift is a measurable bijection between `A` and the shifted stopping space,
so it preserves TV exactly.  A joint-survival lower bound also bounds every
marginal survival from below because the joint-survival event is contained in
each marginal-survival event.  Thus the finite-player sentence is correct
and does not require independence.

The phrase “positive reach floor is the exact boundary” should be narrowed.
What is proved is:

* `S_d` is locally Lipschitz on every domain `q_d >= rho > 0`;
* there is no uniform continuity modulus on the whole positive-reach domain
  that remains informative as the reach tends to zero; and
* the unrestricted graph closure has nonfunctional fibres at zero reach.

Some restricted families can still have a unique continuous extension at a
zero-reach boundary, and reach-weighted quantities such as
`q_d(mu) Phi(S_d mu)` can remain continuous.  Therefore positive reach is the
exact boundary for the unrestricted *unweighted conditional-law map*, not
for every suffix-derived semantic observable.

There is also a minor presentation point: Section 1 defines profile distance
as the maximum of marginal TV distances.  The one-coordinate proof above
then applies coordinatewise without another factor.  If a later program uses
a sum metric, the stated composed modulus must be converted to that metric.

## 2. Exact characterization of `CSR_1`

At depth one, `q_1(mu)=0` forces `mu=delta_0`.  For every stopping law `tau`,
let `L_1 tau` be its one-date delay and set

$$
\mu_p=(1-p)\delta_0+pL_1\tau.
$$

Then

$$
d_{\mathrm{TV}}(\mu_p,\delta_0)=p,
\qquad q_1(\mu_p)=p,
\qquad S_1\mu_p=\tau.
$$

Conversely, if `mu_n -> mu`, all `q_1(mu_n)>0`, and `q_1(mu)>0`, the
conditioning estimate on an eventual positive floor forces
`S_1 mu_n -> S_1 mu`.  Hence the closure has the exact description

$$
\operatorname{CSR}_1
=
\{(\mu,S_1\mu):q_1(\mu)>0\}
\;\cup\;
\bigl(\{\delta_0\}\times\mathcal P(\overline{\mathbb N})\bigr).
$$

This is stronger and cleaner than recording only the two pairs in (8): at
the vanished-reach source, closure has forgotten the conditional successor
completely.

The displayed special sequences are correct:

$$
d_{\mathrm{TV}}(\mu_n^Q,\delta_0)
=d_{\mathrm{TV}}(\mu_n^N,\delta_0)=p_n,
$$

their reaches are `p_n`, and their suffixes are respectively `delta_0` and
`delta_infty`.  “Their finite supports are contained in `{0,1}`” is correct
only if “finite support” means support on finite dates; the full support of
`mu_n^N` also contains `infty`.  Writing “their finite-date supports” removes
the ambiguity.

## 3. The one-player payoff and tester

For reward one on quitting and payoff zero on Never,

$$
U(\mu)=1-\mu(\infty),\qquad B(\mu)=1,
\qquad B(\mu)-U(\mu)=\mu(\infty).
$$

These identities are exact.  Pure quitting at date zero is one fixed complete
behavioral deviation attaining the cap.  For every law `nu` with zero Never
mass, its deviation gain is zero, whereas at `delta_infty` its deviation gain
is one.  Equations (11) and (12) are also correct for the stated *law algebra*:
finite prefixing, finite concatenation, and positive-reach conditioning of
almost-surely finite laws preserve zero Never mass.

However, this is a discrepancy of the post-edge conditional functional.  At
the original approximating source `mu_n^N`, the same quit-now deviation has
gain

$$
1-U(\mu_n^N)=p_n\longrightarrow0.
$$

Equivalently, multiplying the conditional discrepancy one by the reach
`p_n` removes it.  The phrases “surviving strategic discrepancy is 1” and
“fixed strategic obstruction” should therefore say explicitly “unweighted
post-suffix discrepancy.”  The example does not obstruct consumers whose
estimates retain the reach factor, and the one-player game itself has an
exact equilibrium.

## 4. Law provenance is not full behavioral provenance

Section 1 calls an element of
`prod_i P(overline N)` an “actual behavioral source.”  It is actualizable, but
it is not a complete behavioral strategy: induced stopping laws identify
strategies that differ after a zero-probability survival history.  This matters
at exactly the boundary used by the counterexample.

For example, a behavioral strategy can quit surely at date zero and prescribe
Never after the counterfactual all-Continue history.  Its induced law is
`delta_0`, while its literal off-path behavioral tail is Never.  The canonical
realizer in the inspected Lean source does precisely choose zero hazard after
survival has become zero.  Thus the target `delta_infty` is recoverable as a
literal off-path behavioral continuation of a strategy whose induced source
law is `delta_0`; it is merely not a *conditional law* `S_1 delta_0`, because
that expression is undefined.

Accordingly, (11) must not be asserted for arbitrary operations on complete
behavior profiles.  It holds only when:

1. ports are induced stopping laws rather than complete strategies;
2. suffixing means measure-theoretic conditioning and requires positive
   reach; and
3. source-faithful programs are restricted to the listed law operations,
   with no separately stored off-path continuation.

The provenance DAG should record typed equalities for every internal node,
not just node labels.  In particular, each protected target coordinate should
carry an ancestry path to the designated protected input coordinate, every
suffix node should store its date and positive reach witness, and every
prefix/concatenation node should store the exact operands and output-law
equation.  Merely saying that a protected coordinate “may not acquire a
replacement node” is not yet a mathematical definition of source fidelity.

## 5. What the three adapter failures actually prove

### Closed witness

The pair `(delta_0,delta_infty)` is not a legal positive-reach suffix from its
limiting source.  This proves that graph closure does not preserve that legal
transition semantics.  But `CSR_1` is closed by definition, so it satisfies
the literal formal condition imposed on `CW` in Section 2.  To say that the
`CW` adapter fails, add an ambient semantic requirement such as:

> A `CW(a,w)` relation must be a closed subrelation of the graph of the named
> actual operation, not merely a closed relation between actual endpoint
> objects.

Under that repaired definition, `CSR_1` fails because its zero-reach fibre is
not contained in the graph of legal suffixing.

### Reconstruction

The source estimate (9) is correct and already proves that no reconstruction
near `delta_0` can retain a common positive reach floor.  Under the stricter
`RC` rule from Section 2, which fixes the initial source exactly and forbids
replacing it by a nearby source, no suffix call from `delta_0` is legal at all.
The varying `widehat mu_k` discussion should be presented as the failure of a
tempting *relaxation* of `RC`, not as an execution permitted by the stated
`RC` constructor.

The zero-Never induction adds a separate exact obstruction to approximating
the target law by the restricted law program.  It should retain the law-level
scope stated above.

### Rank

The self-loop `(delta_infty,delta_infty)` is exact and proves that there is no
function

$$
R:\mathcal P(\overline{\mathbb N})\to\mathbb N
$$

strictly decreasing on every `CSR_1` pair.  This is the strongest conclusion
available from (13).  The grammar's `RD` state is `(x,m)`, however, so an
external finite-use counter can permit a transition
`(delta_infty,m) -> (delta_infty,m-1)`.  Therefore the text should say
“no law-intrinsic rank adapter for unrestricted iteration of `CSR_1`,” not
“no rank adapter.”

## Recommended corrected no-go statement

The following statement is fully supported by the calculations:

> On the TV space of complete stopping laws, the positive-reach depth-one
> conditional-suffix map has no single-valued continuous extension at
> `delta_0`.  Its graph closure has the entire fibre
> `{delta_0} x P(overline N)`.  Hence that closure cannot be used as an exact
> legal positive-reach suffix edge, nor reconstructed from the exact protected
> law `delta_0` by finite prefixing, concatenation, and positive-reach
> conditioning with vanishing law error while retaining a common positive
> reach floor.  No natural-number rank depending only on the law can decrease
> along every edge of the closure.

Add immediately:

> This does not rule out a restricted family with a prescribed boundary
> successor, an off-path continuation carried by a complete behavioral
> strategy, a reach-weighted semantic consumer, or an enlarged-state rank with
> an external finite-use budget.

With these qualifications, Sections 1, 3, and 5 can be retained.  Without
them, the headline claim that `CSR_1` has “none of the three permitted
adapters” is false under the grammar's own literal `CW` and `RD` definitions,
and the strategic wording overstates a conditional law-level obstruction.
