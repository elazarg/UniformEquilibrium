# Failure of weighted surplus gives a sparse coordinatewise-improving law, not a product strategy

Identity: `CODEX_SOCIAL_DUAL`  
Date: 2026-08-31  
Status: **ordinary mathematics proved below.**  Failure of the weighted
aggregate-surplus chamber has an exact sparse terminal-law interpretation.  In
Fin4 the law needs at most four outcomes, and this bound is sharp.  The law is
a correlated reward-moment certificate; it need not be an outcome law of any
behavioral profile, a product root, an LCP solution, or an equilibrium.
Throughout, “coordinatewise-improving over \(s\)” means exactly
\(u\geq s\) and \(u\ne s\); no convention-dependent Pareto terminology is
used in theorem statements.

## 1. Question

For a finite quitting game let

\[
 s_i=r_i(\{i\}),\qquad
 \Omega=\{\infty\}\cup\{S\subseteq I:S\ne\varnothing\},
\]

and put \(r(\infty)=0\).  The weighted chamber from
`CODEX_SOCIAL__WEIGHTED_AGGREGATE_SURPLUS_CHAMBER.md` closes the game if some
strictly positive vector \(\theta\) satisfies

\[
 \theta\cdot r(\omega)\leq\theta\cdot s
 \quad(\omega\in\Omega).
\tag{1.1}
\]

What exact finite reward-table object is forced when no such \(\theta\)
exists?  Does that object enter a stationary, LCP, or finite-block consumer?

## 2. Exact coordinatewise order alternative

Let

\[
 \mathcal F=\operatorname{conv}\{r(\omega):\omega\in\Omega\}
\]

be the correlated terminal reward-moment polytope.

### Theorem 2.1

Exactly one of the following holds.

1. There is \(\theta\in\mathbb R^I_{>0}\) satisfying (1.1).
2. There are a probability law \(\mu\in\Delta(\Omega)\) and its reward moment

   \[
   u=\sum_{\omega\in\Omega}\mu(\omega)r(\omega)
   \]

   such that

   \[
   \boxed{u\geq s\text{ coordinatewise},\qquad u\ne s.}
   \tag{2.1}
   \]

Thus failure of every positive weighted chamber is exactly the assertion that
the synthetic singleton vector \(s\) is **not** maximal for the strict
coordinatewise order on the terminal reward polytope: there is
\(u\in\mathcal F\) with \(u\geq s\) and \(u\ne s\).

### Proof

Use the generator set

\[
 G=\{r(\omega)-s:\omega\in\Omega\}
   =\{-s\}\cup\{r(S)-s:S\ne\varnothing\}.
\]

The strict Gordan--Stiemke alternative in the preceding note says that either
there is \(\theta>0\) nonpositive on every generator, or

\[
 0\ne v=\sum_{\omega}\lambda_\omega(r(\omega)-s)
       \in\mathbb R^I_{\geq0}
\tag{2.2}
\]

for nonnegative coefficients \(\lambda_\omega\).  Put

\[
 \Lambda=\sum_\omega\lambda_\omega>0,
 \qquad \mu(\omega)=\lambda_\omega/\Lambda.
\]

Then

\[
 u-s=v/\Lambda\in\mathbb R^I_{\geq0}\setminus\{0\},
\]

which is (2.1).  Conversely, a law satisfying (2.1), with
\(\lambda_\omega=\mu(\omega)\), gives a nonzero vector (2.2).

The two arms cannot coexist: (1.1) gives

\[
 \theta\cdot(u-s)\leq 0,
\]

whereas \(\theta>0\) and (2.1) give
\(\theta\cdot(u-s)>0\).  `QED`

The normalization is the important point.  The coefficient of the generator
\(-s\) becomes the probability of Never.  The conic certificate is therefore
not merely a formal linear combination: it canonically produces a correlated
terminal law.  It still does not produce an ordinary strategy profile.

### A different, source-attached law at a positive ordinary minimum

The abstract sparse law is not the only coordinatewise-improving law in the
counterexample branch.  Let \(z_*=(U,B)\) be a positive ordinary global
minimum of total debt, write

\[
 d_i=B_i-U_i,\qquad D_*=\sum_i d_i>0,
\]

and put \(s_i=r_i(\{i\})\).  The checked singleton margin gives

\[
 D_*\leq B_i-s_i.
\]

Therefore

\[
 U_i-s_i\geq D_*-d_i=\sum_{k\ne i}d_k\geq0.
\tag{2.3}
\]

When \(|I|\geq2\),

\[
 \sum_i(U_i-s_i)\geq(|I|-1)D_*>0.
\tag{2.4}
\]

Thus \(U\geq s\) and \(U\ne s\) directly.  The checked declarations
`exists_terminalSemanticLawCarrier_lift` and
`terminalSemanticLawCarrier_rewardMoment` supply a joint-carrier law
\(\mu_*\) whose literal reward moment is this same \(U\).  It is a
subsequential limit of actual behavioral outcome laws and retains that source
provenance.  It need not itself be attained by one behavioral profile, and it
need not be sparse.

Conic Caratheodory may now be applied using only the generators in
\(\operatorname{supp}\mu_*\).  It selects at most \(|I|\) positive
\(\mu_*\)-atoms and reweights them to another law \(\nu\) satisfying

\[
 \mathbb E_\nu r\geq s,\qquad
 \mathbb E_\nu r\ne s.
\tag{2.5}
\]

This retains provenance of the **selected outcomes**, but generally not of
the **selected law**: the new weights need not be their relative
\(\mu_*\)-weights, its reward moment need not equal \(U\), and no cap or
chronology is transported to \(\nu\).

### Quantitative literal-law mass times surplus

The ordinary global-minimum costate inequality in
`CODEX_WEIGHT_GLOBAL__NONNEGATIVE_WEIGHT_SOCIAL_CHAMBER.md` also gives a
source-attached quantitative atom.  Let \(\theta\geq0\) have at least two
positive coordinates and put

\[
 T_\theta=\sum_i\theta_i,\qquad
 M_\theta=\max_i\theta_i,\qquad
 c=T_\theta-M_\theta>0.
\]

For a supplied joint minimum point \((U,B,\mu_*)\), define

\[
 a_\omega=\theta\cdot(r(\omega)-s).
\]

Then

\[
 \sum_{\omega\in\Omega}\mu_*(\omega)a_\omega
 =\theta\cdot(U-s)\geq cD_*.
\tag{2.6}
\]

Writing \(K=|\Omega|\), at least one literal outcome satisfies

\[
 \boxed{\mu_*(\omega)a_\omega\geq\frac{cD_*}{K}>0.}
\tag{2.7}
\]

Indeed, the left side of (2.6) is the sum of the \(K\) displayed products,
so one is at least their arithmetic average.  This co-realizes positive
source-law mass and positive weighted surplus at one outcome.  It is distinct
from the sharper surplus-only common-outcome bound in the global-weight note:
(2.7) also controls the mass--surplus product.

Suppose all finite reward coordinates have absolute value at most \(R>0\).
If \(A_\theta=\theta\cdot s\geq0\), Never has surplus
\(-A_\theta\leq0\), so the outcome in (2.7) is finite.  Since

\[
 a_\omega\leq2RT_\theta,
\]

equation (2.7) gives

\[
 \mu_*(\omega)\geq
 \frac{cD_*}{2KRT_\theta},
 \qquad
 a_\omega\geq\frac{cD_*}{K}.
\tag{2.8}
\]

These last constants assume \(R>0\), which may always be arranged when
choosing a positive bound.  The estimate still gives no same-date Nash or
adjacent-toggle inequality.

## 3. Sharp Fin4 support bound

### Theorem 3.1

If \(|I|=4\), Alternative 2 of Theorem 2.1 has a witness supported on at most
four terminal outcomes.  More precisely:

- if Never belongs to the support of the selected compressed witness, the
  rest of that support contains at most three nonempty coalitions;
- if Never does not belong to that selected support, it contains at most four
  nonempty coalitions.

### Proof

Apply conic Caratheodory in \(\mathbb R^4\) to the nonzero vector \(v\) in
(2.2).  It is a conic combination of at most four generators from \(G\).
Normalize the sum of those new coefficients exactly as in Theorem 2.1.  Each
selected generator is one terminal outcome, including \(-s\) as Never.
`QED`

This does **not** say that compression preserves Never from an arbitrary
initial witness having positive Never mass.  It is only the conditional count
for the support produced by conic Caratheodory.  A Never-preserving
compression would require an additional argument.

For \(n\) players the identical argument gives support at most \(n\), not the
generic affine Caratheodory bound \(n+1\).

### Sharpness in Fin4

Let \(I=\{0,1,2,3\}\), and set every own singleton reward to zero, so
\(s=0\).  Choose four pair coalitions

\[
 T_0=\{0,1\},\quad T_1=\{0,2\},\quad
 T_2=\{0,3\},\quad T_3=\{1,2\}.
\]

For \(k=0,1,2,3\), define

\[
 r_i(T_k)=
 \begin{cases}
 4,&i=k,\\
 -1,&i\ne k.
 \end{cases}
\tag{3.1}
\]

At a singleton \(\{i\}\), set coordinate \(i\) to zero and all other
coordinates to \(-1\).  Give every remaining nonempty coalition reward vector
\((-1,-1,-1,-1)\).

The uniform law on \(T_0,T_1,T_2,T_3\) has moment

\[
 u=(1/4,1/4,1/4,1/4)>s.
\tag{3.2}
\]

No law supported on at most three outcomes weakly dominates \(s\) with one
strict coordinate.  Indeed, such a law omits some \(T_\ell\).  At coordinate
\(\ell\), every included displayed pair has reward \(-1\), and every
nondisplayed outcome has reward at most zero.  If a displayed pair has
positive mass, the \(\ell\)-coordinate is negative; if none has positive
mass, no coordinate can be strictly positive.  Hence support four is sharp.

Equivalently, for every \(\theta>0\), summing the four desired inequalities
\(\theta\cdot r(T_k)\leq 0\) would give

\[
 \theta\cdot\sum_k r(T_k)
 =\theta\cdot(1,1,1,1)>0,
\]

so the weighted chamber necessarily fails.

## 4. The sparse law need not be a product or behavioral law

### One-root product support

For a product root \(q\), let

\[
 K=\{i:q_i=1\},\qquad A=\{i:0<q_i<1\}.
\]

If \(K\ne\varnothing\), the support of its absorbing coalition law is the
Boolean interval

\[
 \{K\cup B:B\subseteq A\}.
\tag{4.1}
\]

If \(K=\varnothing\), its nonempty support is

\[
 \{B\subseteq A:B\ne\varnothing\}.
\tag{4.2}
\]

Thus an arbitrary four-outcome certificate is not a stationary product law.
For the sharp example, the four pair coalitions have empty common
intersection.  They cannot have the form (4.1); and support size four cannot
have the form (4.2), whose possible nonzero sizes in Fin4 are
\(1,3,7,15\).

### An exact all-behavioral nonrealizability test

There is an even stronger obstruction for the law in (3.2).

**Lemma 4.1.**  Suppose an ordinary behavioral profile has zero Never mass,
zero mass on every singleton terminal, and total absorption probability one.
Then all coalitions in its terminal-law support contain one fixed pair of
players.

**Proof.**  Before absorption there is one public live history at each date.
Choose the first date having positive unconditional absorption.  Earlier
roots are all Continue.  At the selected product root every singleton root
probability is zero, since all stage contributions to the terminal singleton
masses are nonnegative.

If no player Quits surely, then every opponent-Continue factor is positive;
any positive Quit probability would create a positive singleton probability.
Thus the root would have zero absorption, a contradiction.  If exactly one
player Quits surely, that player's singleton probability is positive.  Hence
at least two players Quit surely.  Absorption is then certain at this date,
and every coalition in the resulting support contains those two players.
`QED`

The four pairs \(T_0,T_1,T_2,T_3\) have empty intersection.  Therefore their
uniform law is not the terminal law of **any** ordinary behavioral profile,
not merely not the law of a stationary root.

This exact example is sufficient to rule out a general realization adapter
from the sparse dual certificate.  It does not assert the stronger topological
statement that this law is outside the closure of all behavioral outcome
laws; a quantitative stability lemma would be needed for that claim.

## 5. Even a realizable certificate need not be strategic

For two players, take

\[
 r(\{1\})=(1,3),\qquad
 r(\{2\})=(3,1),\qquad
 r(\{1,2\})=(2,2).
\tag{5.1}
\]

Then \(s=(1,1)\), and the pure terminal law on \(\{1,2\}\) has payoff
\((2,2)>s\).  It is an actual one-row product law.  Nevertheless, at the pure
pair row player 1 gains by Continuing and receiving \(r_1(\{2\})=3\), and
player 2 has the symmetric gain.  Thus the certificate is not a Nash root.

If one formally uses \(u=(2,2)\) as a continuation value, all Continue is a
strict exact root because \(u_i>s_i\).  Repeating all Continue, however,
produces the actual Never payoff zero, not \(u\).  The fixed-point payoff and
carrier realization are missing.  This is precisely the inert all-Continue
boundary, not a stationary equilibrium.

The certificate also contains no adjacent-toggle comparisons such as
\(r_i(S)\) versus \(r_i(S\setminus\{i\})\) or
\(r_i(S\cup\{i\})\).  Those comparisons can be changed while leaving the
coordinatewise-improving law intact.  Therefore no LCP/complementarity consumer follows from
Theorem 3.1 alone.

## 6. What the two law objects provide

For a hypothetical Fin4 counterexample, there are two distinct
coordinatewise-improving law objects.

First, the joint-carrier lift of the actual positive minimum supplies a
source-attached limiting law \(\mu_*\) with

\[
 \mathbb E_{\mu_*}r=U\geq s,\qquad U\ne s.
\tag{6.1}
\]

This law is the limit of actual behavioral laws along one realizing
subsequence.  It need not be sparse or attained by one profile.

Second, failure of every weighted chamber, or conic compression inside
\(\operatorname{supp}\mu_*\), supplies a reweighted law \(\nu\) with

\[
 |\operatorname{supp}\nu|\leq4,\qquad
 \mathbb E_\nu r\geq s,\qquad
 \mathbb E_\nu r\ne s.
\tag{6.2}
\]

This is a genuine exact reward-table restriction and an efficient LP screen.
For rational tables, a rational conic certificate and hence a rational sparse
law can be chosen.  It is also a natural feasible individually-rational
candidate whenever the relevant punishment levels lie below the singleton
vector.

The sparse law \(\nu\) does **not** by itself give:

- membership of \((\mathbb E_\nu r,B)\) in the terminal semantic carrier
  for any cap \(B\);
- a product realization of \(\nu\);
- incentive compatibility of a pure or correlated recommendation;
- a finite chronological block without public correlation;
- an absorbing exact root or LCP solution; or
- terminal approximate Nash profiles.

With an external public lottery, one could sample \(\omega\sim\nu\) and
implement its terminal coalition.  Such a lottery is absent from the ordinary
quitting game, and even with it the deviation inequalities in Section 5 do not
follow.  The object is therefore best understood as a **sparse correlated
feasibility witness**, not an equilibrium or chronology.  Selecting its
outcomes from \(\operatorname{supp}\mu_*\) retains atom identities but does
not repair this: the reweighted law is generally not the literal source law.

## 7. Conjecture-facing boundary

The weighted chamber and its dual give the exact static dichotomy

\[
 \boxed{
 \text{positive welfare separator closing the game}
 \quad\lor\quad
 \text{a coordinatewise-improving law on at most four outcomes}.}
\]

The second arm does not match a current stationary, LCP, or finite-block
consumer.  A useful next theorem would need extra structure, for example one
of:

1. the sparse support is a product Boolean interval and its adjacent toggle
   inequalities are Nash-compatible;
2. the law is realized by an actual source profile with cap equal to its
   reward moment; or
3. the four-outcome public mixture can be derandomized by a source-attached
   finite chronology while preserving every player's unrestricted cap.

Without one of these additions, the conic certificate is a sharp table-level
normal form but not a route from weighted-chamber failure to ordinary uniform
equilibrium.

## 8. Overlap and distinct content

The foundational Gordan alternative and the \(n\)-outcome conic support bound
overlap the fixed-support result in
`CODEX_WEIGHT_GLOBAL__NONNEGATIVE_WEIGHT_SOCIAL_CHAMBER.md`.  The pair
specialization, including two-outcome compression inside one minimum law's
positive support, is developed in
`CODEX_SOCIAL_PAIR__SOURCE_SUPPORTED_TWO_OUTCOME_CERTIFICATES.md`.

The distinct content of this note is:

1. the exact Fin4 table proving the four-outcome bound sharp;
2. the all-behavior fixed-pair-support obstruction in Lemma 4.1;
3. the separation of correlated feasibility from product-root geometry and
   Nash compatibility; and
4. the explicit distinction between the source-attached minimum law and its
   sparse reweighting, including (2.7)--(2.8).

These results should be consolidated with the global-weight theorem for a
future export rather than exported as a duplicate foundational packet.

## Sources inspected

- `notes/CODEX_SOCIAL__WEIGHTED_AGGREGATE_SURPLUS_CHAMBER.md`;
- `notes/CODEX_WEIGHT_GLOBAL__NONNEGATIVE_WEIGHT_SOCIAL_CHAMBER.md`;
- `notes/CODEX_SOCIAL_PAIR__SOURCE_SUPPORTED_TWO_OUTCOME_CERTIFICATES.md`;
- `minimumTerminalSemantic_weightedSingletonMargin` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticWeightedAuxiliaryNashBudget.lean`;
- `minimumTerminalSemantic_singletonMargin` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticAuxiliaryNashBudget.lean`;
- `minimumTerminalSemantic_subset_singletonSurplus` and
  `exists_terminalOutcome_subset_singletonSurplus_ge_minimumDebt` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticMinimumAggregateSurplus.lean`;
- `exists_terminalSemanticLawCarrier_lift` and
  `terminalSemanticLawCarrier_rewardMoment` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticResetIncidenceReturn.lean`;
- `quittingTerminalSemanticCarrier_prescribed_mem_rewardMomentSet` in
  `UniformEquilibrium/Quitting/Root/TerminalSemanticMoment.lean`;
- `QuittingMarkedPairDecoratedFamily` and its exact common-prefix scaling
  declarations in
  `Research/Quitting/NormalizedPassportPrefixOrbit.lean`; and
- `Literature/SolanAndSolan2020.lean`, consulted only to distinguish a public
  sunspot law from an ordinary behavioral profile.  No literature theorem is
  used in the proofs above.
