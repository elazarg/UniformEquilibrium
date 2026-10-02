# Nonnegative-weight social chamber and sparse reward boundary

Authors: Math conference synthesis from CODEX_WEIGHT_GLOBAL and
CODEX_SOCIAL_DUAL

Independent reviews:
[first main-theorem review](../feedback/CODEX_WEIGHT_GLOBAL__NONNEGATIVE_WEIGHT_SOCIAL_CHAMBER__BY_CODEX_DESCENDANT.md),
[second main-theorem review](../feedback/CODEX_WEIGHT_GLOBAL__NONNEGATIVE_WEIGHT_SOCIAL_CHAMBER__BY_PAIRED_HULL_REVIEW.md),
the [sparse-boundary review](../feedback/CODEX_SOCIAL_DUAL__SPARSE_PARETO_LAW_AND_PRODUCT_BARRIER__BY_SOCIAL_WEIGHT_REVIEW.md),
and the [post-repair assembled-packet audit](../feedback/NONNEGATIVE_WEIGHT_SOCIAL_CHAMBER_AND_SPARSE_REWARD_BOUNDARY__BY_SOCIAL_WEIGHT_REVIEW.md).
The five revisions requested by the sparse-boundary review are incorporated
below: the Never count is conditional, the literal minimum law is separated
from its sparse reweighting, the mass--surplus estimate is included,
coordinatewise order replaces ambiguous Pareto terminology, and overlapping
claims are stated only once.

## Exact statement

Let \(I\) be a finite nonempty player set with at least two players, and let

\[
 r:\{S\subseteq I:S\ne\varnothing\}\longrightarrow\mathbb R^I
\]

be a finite quitting-game reward table. Put

\[
 s_i=r_i(\{i\}).
\]

Let \(\mathcal K_r\) be the closed terminal-semantic carrier. Its elements
are pairs \(z=(U,B)\), where \(U\) is the prescribed terminal payoff and
\(B_i\) is player \(i\)'s supremum over all unilateral behavioral
replacements against the prescribed opponents. Define

\[
 d_i(z)=B_i-U_i\geq0,
 \qquad
 D(z)=\sum_i d_i(z).
\]

Choose a global minimum \(z_*=(U,B)\in\mathcal K_r\) and write

\[
 D_*=D(z_*)=\min_{z\in\mathcal K_r}D(z).
\]

For a nonnegative vector \(\theta\in\mathbb R^I_{\geq0}\) with at least two
positive coordinates, define

\[
 T_\theta=\sum_i\theta_i,
 \qquad
 M_\theta=\max_i\theta_i,
 \qquad
 A_\theta=\theta\mathbin\cdot s,
\]

and

\[
 R_\theta=
 \max\left(0,\max_{S\ne\varnothing}
   \theta\mathbin\cdot r(S)\right).
\]

Then \(T_\theta-M_\theta>0\), and the following conclusions hold.

### A. Exact nonnegative-costate chamber

If \(D_*>0\), the ordinary global minimum satisfies

\[
 \boxed{
 A_\theta+(T_\theta-M_\theta)D_*
 \leq \theta\mathbin\cdot U
 \leq R_\theta.}
\tag{1}
\]

In all cases,

\[
 \boxed{
 D_*\leq
 \max\left(0,
   \frac{R_\theta-A_\theta}{T_\theta-M_\theta}
 \right).}
\tag{2}
\]

In particular, if

\[
 \theta\geq0,
 \qquad
 |\{i:\theta_i>0\}|\geq2,
 \qquad
 \theta\mathbin\cdot s\geq0,
\tag{3}
\]

and

\[
 \theta\mathbin\cdot(r(S)-s)\leq0
 \qquad(S\ne\varnothing),
\tag{4}
\]

then \(D_*=0\), and the game has a uniform-equilibrium payoff against
unrestricted unilateral behavioral deviations. The costate may be
normalized by \(T_\theta=1\).

### B. Literal joint-law mass--surplus certificate

Extend the outcome space by Never:

\[
 \Omega=\{\infty\}\cup\{S\subseteq I:S\ne\varnothing\},
 \qquad
 \bar r(\infty)=0,
 \qquad
 \bar r(S)=r(S).
\]

Every minimum pair has a lift \((z_*,\mu)\) to the joint
terminal-semantic/law carrier, with exact reward moment

\[
 U=\sum_{\omega\in\Omega}\mu(\omega)\bar r(\omega).
\tag{5}
\]

If \(D_*>0\), put

\[
 c_\theta=T_\theta-M_\theta>0,
 \qquad K=|\Omega|=2^{|I|}.
\]

Some literal outcome \(\omega\in\Omega\) then satisfies

\[
 \boxed{
 \mu(\omega)\,
 \theta\mathbin\cdot(\bar r(\omega)-s)
 \geq \frac{c_\theta D_*}{K}>0.}
\tag{6}
\]

Thus the same retained limiting law co-realizes positive outcome mass and
positive weighted singleton surplus. This is not a Caratheodory replacement
of the law.

Suppose additionally that

\[
 |r_i(S)|\leq R
 \quad(i\in I,\ S\ne\varnothing)
\]

for some \(R>0\), and that \(A_\theta\geq0\). Never has surplus
\(-A_\theta\leq0\), so the outcome in (6) is a finite coalition and may be
chosen to satisfy

\[
 \boxed{
 \theta\mathbin\cdot(r(\omega)-s)
 \geq\frac{c_\theta D_*}{K},
 \qquad
 \mu(\omega)
 \geq\frac{c_\theta D_*}{2KRT_\theta}.}
\tag{7}
\]

For Fin4, \(K=16\). With \(T_\theta=1\), these floors are

\[
 \frac{c_\theta D_*}{16}
 \qquad\text{and}\qquad
 \frac{c_\theta D_*}{32R}.
\tag{8}
\]

The joint-carrier law is a subsequential limit of actual behavioral outcome
laws. It need not be attained by one profile.

### C. Exact fixed-support cone alternative

Fix \(J\subseteq I\) with \(|J|\geq2\), and project vectors to their
\(J\)-coordinates. Exactly one of the following holds.

1. There is \(\theta_J\in\mathbb R^J_{>0}\) such that

   \[
    \theta_J\mathbin\cdot s|_J\geq0,
    \qquad
    \theta_J\mathbin\cdot(r(S)-s)|_J\leq0
    \quad(S\ne\varnothing).
   \tag{9}
   \]

2. There is a probability law \(\nu_J\) on \(\Omega\), supported on at most
   \(|J|\) outcomes, such that

   \[
    \mathbb E_{\nu_J}[\bar r_i]\geq s_i
    \quad(i\in J),
   \tag{10}
   \]

   with strict inequality in at least one \(J\)-coordinate.

Extending \(\theta_J\) by zero outside \(J\) turns arm 1 into the closing
chamber (3)--(4). Hence, if \(D_*>0\), arm 2 must occur for every
\(J\subseteq I\) of cardinality at least two.

For \(J=I\), the sparse law can be chosen from the positive support of the
source-attached minimum law \(\mu\): the checked singleton margin implies

\[
 U_i-s_i\geq D_*-d_i=\sum_{k\ne i}d_k\geq0,
\tag{11}
\]

and

\[
 \sum_i(U_i-s_i)\geq(|I|-1)D_*>0.
\tag{12}
\]

Conic compression inside \(\operatorname{supp}\mu\) selects at most
\(|I|\) positive \(\mu\)-atoms and reweights them to a law \(\nu\) with

\[
 \mathbb E_\nu\bar r\geq s,
 \qquad
 \mathbb E_\nu\bar r\ne s.
\tag{13}
\]

Only the selected atom identities retain source provenance. The reweighted
law generally has different weights and a different reward moment, and no
cap or chronology is transported to it.

When \(|I|=4\), the total support bound four is sharp. If Never belongs to
the support of the selected compressed witness, at most three other support
points are nonempty coalitions. This is only a conditional count on the
compressed witness: conic Caratheodory does not prove that positive Never
mass in an arbitrary initial witness can be preserved during compression.

### D. Exact realization barriers

The sparse law in arm 2 is a correlated reward-moment certificate, not an
ordinary strategy, product root, LCP solution, or equilibrium. Two exact
barriers hold.

1. There are Fin4 tables for which every coordinatewise-improving law needs
   four outcomes, and a sharp four-outcome witness is not the terminal law of
   any ordinary behavioral profile.
2. Even when a coordinatewise-improving law is a one-row product law, it
   need not be Nash against unilateral behavioral deviations.

The examples and proofs are given below.

## Conjecture-facing change

The checked aggregate-surplus chambers previously used equal weights on all
players or on a chosen player subset. Equations (1)--(4) give a strictly
larger, effectively checkable chamber: an arbitrary nonnegative costate with
at least two positive coordinates may close the game. The mixed-singleton
Fin4 example below is closed by such a costate while every subset-indicator
test fails.

The packet also gives the exact finite-dimensional boundary when a supported
costate is unavailable. For each fixed support \(J\), the failure is a
coordinatewise-improving correlated law on at most \(|J|\) outcomes. The
sharpness and realization barriers prove that this dual arm cannot silently
be fed to a stationary, LCP, or finite-block consumer.

Thus the live obligation is narrowed to games that fail every supported
social costate chamber and carry the corresponding family of sparse
reward-table certificates. The packet does not consume that remaining arm.

## Definitions and strategy-class audit

An ordinary behavioral profile assigns, at the unique live public history of
each date, an independent Quit/Continue randomization to every player.
Players may use calendar-dependent private randomization. A unilateral
behavioral replacement may replace one player's entire strategy, including
Never or an arbitrarily late stopping rule.

The cap \(B_i\) in \(\mathcal K_r\) is the supremum over this complete
deviation class, not over stationary or finite-time deviations. The passage
to the closed carrier preserves this cap coordinate. The zero-minimum
consumer cited below produces terminal approximate Nash profiles against the
same complete deviation class and then one fixed uniform-equilibrium payoff.

The laws \(\mu\) and \(\nu_J\) are distributions on terminal outcomes, not
public correlation devices. The source-attached \(\mu\) is a limit of laws
of ordinary behavioral profiles. The conically reweighted \(\nu_J\) need
not be behavioral-realizable at all. No public randomization is added to the
game in any theorem.

## Proof

### 1. The global-minimum inequality and chamber consumer

Assume first that \(D_*>0\). The checked singleton margin at a positive
ordinary global minimum is

\[
 D_*\leq B_i-s_i
 \qquad(i\in I).
\tag{14}
\]

Multiply by \(\theta_i\geq0\), sum, and use \(B_i=U_i+d_i\):

\[
 T_\theta D_*
 \leq \theta\mathbin\cdot(U-s)+\sum_i\theta_i d_i.
\]

Because \(d_i\geq0\), \(\theta_i\leq M_\theta\), and
\(\sum_i d_i=D_*\),

\[
 \sum_i\theta_i d_i\leq M_\theta D_*.
\]

Subtracting proves

\[
 (T_\theta-M_\theta)D_*
 \leq\theta\mathbin\cdot(U-s).
\tag{15}
\]

The prescribed coordinate \(U\) belongs to the finite reward-moment
polytope, with Never represented by zero. Therefore

\[
 \theta\mathbin\cdot U\leq R_\theta,
\]

which completes (1). Since at least two weights are positive,
\(T_\theta-M_\theta>0\), so (2) follows in the positive-minimum case. If
\(D_*=0\), inequality (2) is immediate because its right side is
nonnegative. Thus (2) is unconditional.

Under (3)--(4), suppose for contradiction that \(D_*>0\). Then
\(R_\theta\leq A_\theta\), contradicting (1). Hence \(D_*=0\), and the
checked zero-minimum theorem supplies the claimed uniform-equilibrium
payoff.

### 2. The literal-law certificate

Lift \(z_*\) to a joint-carrier point \((z_*,\mu)\). The checked moment
identity gives (5). Set

\[
 a_\omega=
 \mu(\omega)\,
 \theta\mathbin\cdot(\bar r(\omega)-s).
\]

By (5) and (15),

\[
 \sum_{\omega\in\Omega}a_\omega
 =\theta\mathbin\cdot(U-s)
 \geq c_\theta D_*.
\]

There are \(K\) summands, so one satisfies (6). Its mass and surplus are
both positive. If \(A_\theta\geq0\), Never's surplus is nonpositive, hence
the selected outcome is finite. For a finite outcome,

\[
 \theta\mathbin\cdot(r(\omega)-s)
 \leq\sum_i\theta_i|r_i(\omega)-s_i|
 \leq2RT_\theta.
\]

Use \(\mu(\omega)\leq1\) in (6) for the surplus floor, and divide (6) by
\(2RT_\theta>0\) for the mass floor. This proves (7)--(8).

### 3. The fixed-support alternative

For fixed \(J\), define the finitely generated closed cone

\[
 C_J=\operatorname{cone}\left(
   \{-s|_J\}\cup
   \{(r(S)-s)|_J:S\ne\varnothing\}
 \right)
 \subseteq\mathbb R^J.
\]

Let \(P_J=\mathbb R^J_{\geq0}\). If
\(C_J\cap(P_J\setminus\{0\})\) is empty, separate \(C_J\) from the compact
simplex

\[
 \Delta_J=\{p\in P_J:\sum_{i\in J}p_i=1\}.
\]

Conicity forces the separating bound on \(C_J\) to be zero. Strict
positivity on every simplex vertex makes every coordinate of the separating
functional positive. Its value on \(-s|_J\) and on every
\((r(S)-s)|_J\) gives (9).

Conversely, a functional satisfying (9) is positive on every nonzero vector
of \(P_J\) and nonpositive on \(C_J\), so the intersection is empty. The
two alternatives are therefore exhaustive and exclusive.

In the second arm, write a nonzero vector of the intersection as

\[
 v=-\lambda_0s|_J+
   \sum_{S\ne\varnothing}\lambda_S(r(S)-s)|_J
 \in P_J\setminus\{0\},
\tag{16}
\]

with nonnegative coefficients. Normalize by

\[
 L=\lambda_0+\sum_S\lambda_S>0.
\]

Give Never mass \(\lambda_0/L\) and coalition \(S\) mass
\(\lambda_S/L\). The resulting law satisfies

\[
 \mathbb E_{\nu_J}[\bar r|_J]-s|_J=v/L,
\]

which proves (10). Conversely, any law satisfying (10) gives (16).
Conic Caratheodory in \(\mathbb R^J\) represents the same nonzero vector
using at most \(|J|\) generators. Normalizing those coefficients proves the
support bound. This is a conic bound \(|J|\), not the affine bound
\(|J|+1\).

For the source-supported statement (11)--(13), equation (14) and
\(B_i=U_i+d_i\) give (11). Summing it gives (12). The nonzero nonnegative
vector \(U-s\) is a conic combination of the generators belonging to
\(\operatorname{supp}\mu\). Conic Caratheodory and normalization give
(13), with the provenance limitations already stated.

### 4. Sharpness of the Fin4 support bound

Let \(I=\{0,1,2,3\}\) and set every own singleton reward to zero, so
\(s=0\). Choose four pair coalitions

\[
 T_0=\{0,1\},\quad T_1=\{0,2\},\quad
 T_2=\{0,3\},\quad T_3=\{1,2\}.
\]

For \(k=0,1,2,3\), set

\[
 r_i(T_k)=
 \begin{cases}
 4,&i=k,\\
 -1,&i\ne k.
 \end{cases}
\tag{17}
\]

At a singleton \(\{i\}\), set coordinate \(i\) to zero and every other
coordinate to \(-1\). Give every remaining nonempty coalition reward vector
\((-1,-1,-1,-1)\).

The uniform law on \(T_0,T_1,T_2,T_3\) has moment

\[
 (1/4,1/4,1/4,1/4)>s.
\]

No law on at most three outcomes can dominate \(s\) coordinatewise with one
strict coordinate. Such a law omits some \(T_\ell\). At coordinate
\(\ell\), every included displayed pair pays \(-1\), and every nondisplayed
outcome pays at most zero. If a displayed pair has positive mass, that
coordinate is negative; if no displayed pair has positive mass, no coordinate
can be strictly positive. Hence four outcomes are necessary.

### 5. Product and all-behavior realization barrier

For a product root \(q\), let

\[
 K_q=\{i:q_i=1\},
 \qquad
 A_q=\{i:0<q_i<1\}.
\]

If \(K_q\ne\varnothing\), the support of its absorbing coalition law is

\[
 \{K_q\cup B:B\subseteq A_q\}.
\tag{18}
\]

If \(K_q=\varnothing\), its nonempty support is

\[
 \{B\subseteq A_q:B\ne\varnothing\}.
\tag{19}
\]

The sharp four-pair support has empty common intersection, so it cannot have
form (18). In Fin4 the possible nonzero cardinalities in (19) are
\(1,3,7,15\), not four. Thus the law is not a one-root product law.

In fact, it is not the terminal law of any ordinary behavioral profile.
Suppose such a profile had zero Never mass, zero terminal mass on every
singleton, and total mass one on the four displayed pairs. Choose the first
date with positive unconditional absorption. All earlier roots are all
Continue. At the selected product root every singleton probability is zero,
because terminal singleton masses are sums of nonnegative stage masses.

If no player Quits surely, every opponent-Continue factor is positive, so
any positive Quit probability creates a positive singleton probability.
The root would therefore have zero absorption, a contradiction. If exactly
one player Quits surely, that player's singleton probability is positive.
Hence at least two players Quit surely. Absorption is then certain at this
date, and every coalition in the whole terminal-law support contains those
two players. The four pairs in (17) have empty common intersection, a
contradiction.

This proof is exact, but it does not show that the four-pair law lies outside
the closure of behavioral laws with small singleton or Never leakage.

### 6. Nash barrier for a realizable law

For two players, define

\[
 r(\{1\})=(1,3),
 \qquad
 r(\{2\})=(3,1),
 \qquad
 r(\{1,2\})=(2,2).
\tag{20}
\]

Then \(s=(1,1)\), and the pure pair outcome is a one-row product law with
payoff \((2,2)>s\). It is not Nash: player 1 gains from \(2\) to \(3\) by
Continuing and leaving player 2 as the sole quitter, and player 2 has the
symmetric deviation. These are literal current-action deviations, hence
also admissible behavioral deviations.

If \((2,2)\) is inserted merely as a formal continuation payoff, all Continue
is a strict one-stage root because \((2,2)>s\). Repeating all Continue gives
the actual Never payoff zero, not \((2,2)\). Thus neither realization nor a
one-stage root supplies the missing fixed-point payoff identity.

### 7. Mixed-singleton Fin4 chamber beyond subset indicators

Let \(I=\{1,2,3,4\}\),

\[
 \theta=(1,2,3,4),
 \qquad
 s=(1,-1/2,0,0).
\]

Give every singleton coalition the full reward vector \(s\); this is
consistent with \(s_i=r_i(\{i\})\). For every nonsingleton \(S\), let
\(\ell(S)\) and \(h(S)\) be the members with least and greatest
\(\theta\)-weight. Define \(x(S)\) by

\[
 x_{\ell(S)}(S)=\theta_{h(S)},
 \qquad
 x_{h(S)}(S)=-\theta_{\ell(S)},
 \qquad
 x_k(S)=0
 \quad(k\notin\{\ell(S),h(S)\}),
\tag{21}
\]

and set \(r(S)=s+x(S)\).

Now \(\theta\mathbin\cdot s=0\) and

\[
 \theta\mathbin\cdot x(S)
 =\theta_{\ell(S)}\theta_{h(S)}
  -\theta_{h(S)}\theta_{\ell(S)}=0.
\]

Therefore every terminal outcome, including Never, has weighted value zero.
The chamber (3)--(4) applies and proves \(D_*=0\), hence a
uniform-equilibrium payoff.

For every \(J\subseteq I\) with \(|J|\geq2\), take \(S=J\). Then

\[
 \sum_{i\in J}r_i(J)
 =\sum_{i\in J}s_i+
   \theta_{h(J)}-\theta_{\ell(J)}
 >\sum_{i\in J}s_i.
\tag{22}
\]

Thus the equal-weight test on \(J\) fails for every eligible \(J\), even
though the arbitrary nonnegative costate closes the game. The singleton
vector is mixed and nonzero, so this is not a zero-singleton special case.

## Boundary tests

The mixed-singleton table in Section 7 is a strict positive test: the new
costate chamber proves a uniform-equilibrium payoff where every prior
subset-indicator chamber fails.

Sections 4--6 are exact negative tests for overinterpreting the dual arm:

- support four is sometimes necessary in Fin4;
- the sharp sparse law is neither a product-root law nor any ordinary
  behavioral terminal law; and
- an actually realizable one-row sparse law may still fail a literal Nash
  inequality.

These examples do not challenge the chamber theorem. They delimit the
additional data needed to consume its sparse boundary.

## Adapter and consumer

The actual-data adapter is the existing terminal-semantic carrier pipeline:

1. exists_minimum_quittingTerminalSemanticDebtSum selects a global minimum
   \(z_*\) of the compact carrier;
2. minimumTerminalSemantic_singletonMargin supplies (14) if \(D_*>0\);
3. exists_terminalSemanticLawCarrier_lift retains a subsequential actual
   outcome law at that same minimum; and
4. terminalSemanticLawCarrier_rewardMoment identifies its exact prescribed
   reward moment.

If a costate satisfying (3)--(4) exists, the new inequality forces
\(D_*=0\). The downstream checked consumer
exists_uniformEquilibriumPayoff_of_hasZeroMinimumTerminalSemanticDebt
then produces terminal approximate Nash profiles for every positive error
and one fixed uniform-equilibrium payoff. This is an actual semantic
consumer, not a supplied-certificate verifier without an endpoint.

If the costate is absent, the fixed-support alternative produces only an
algebraic sparse law. Sections 5--6 prove that there can be no general
adapter from those fields alone to a product root, behavioral terminal law,
or Nash block. A future consumer must add product/chronological realization
and unrestricted-cap control.

## Source correspondence

The following checked Lean declarations are the semantic inputs:

- exists_minimum_quittingTerminalSemanticDebtSum in
  UniformEquilibrium/Quitting/Root/TerminalSemanticEqualityStratum.lean;
- minimumTerminalSemantic_singletonMargin in
  UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticAuxiliaryNashBudget.lean;
- quittingTerminalSemanticCarrier_prescribed_mem_rewardMomentSet in
  UniformEquilibrium/Quitting/Root/TerminalSemanticMoment.lean;
- exists_terminalSemanticLawCarrier_lift and
  terminalSemanticLawCarrier_rewardMoment in
  UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticResetIncidenceReturn.lean;
- minimumTerminalSemantic_subset_singletonSurplus and
  exists_terminalOutcome_subset_singletonSurplus_ge_minimumDebt in
  UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticMinimumAggregateSurplus.lean;
  and
- exists_uniformEquilibriumPayoff_of_hasZeroMinimumTerminalSemanticDebt in
  UniformEquilibrium/Quitting/Terminal/PositiveMinimumSemanticDebt.lean.

The new ordinary mathematics is:

1. aggregation of the unweighted singleton margin by an arbitrary
   nonnegative costate at the ordinary total-debt minimum;
2. the sharp coefficient \(T_\theta-M_\theta\) and quantitative bound (2);
3. the source-law mass--surplus product estimate (6)--(8);
4. the fixed-support Gordan alternative with the conic support bound
   \(|J|\);
5. the sharp Fin4 support-four table and exact behavioral nonrealizability
   lemma; and
6. the mixed, nonzero-singleton Fin4 example separating arbitrary costates
   from every subset-indicator test.

The checked subset results are recovered by taking
\(\theta=\mathbf1_J\), for which
\(T_\theta-M_\theta=|J|-1\). The theorem does not improperly insert zero
coordinates into minimumTerminalSemantic_weightedSingletonMargin, whose
hypotheses and weighted objective are different. No paper theorem is used
in the new arguments.

## Lean handoff

Suggested declarations, separated by dependency:

    minimumTerminalSemantic_nonnegativeCostate_bound
    exists_terminalLawAtom_mass_mul_costateSurplus_ge
    exists_terminalLawFiniteAtom_costateSurplus_and_mass_ge
    quittingRewardTable_fixedSupport_costate_or_sparseLaw
    quittingRewardTable_sparseLaw_support_card_le
    finFour_sparseCoordinatewiseLaw_support_four_sharp
    behavioralLaw_noSingleton_noNever_has_commonPair
    finFour_sparseSharpLaw_not_behavioral
    finFour_nonnegativeCostate_not_subsetIndicator_regression
    exists_uniformEquilibriumPayoff_of_nonnegativeCostateChamber

The finite-dimensional cone result may be implemented using the project's
existing separation/Caratheodory infrastructure if suitable; otherwise it
is an independent finite real-vector-space lemma. The formalizer should
first prove (1) from minimumTerminalSemantic_singletonMargin, then connect
the closing corollary to the existing zero-minimum consumer. The joint-law
result should quantify over the supplied joint-carrier point so that law
provenance is literal rather than reconstructed.

Useful exact tests are the two tables in Sections 4 and 7 and the two-player
Nash regression in Section 6. The Never-support refinement must remain
conditional on Never being selected by the compressed witness.

## Scope and nonclaims

This packet does not prove the finite-quitting conjecture or close the full
Fin4 residual. Specifically, it does not prove that:

- every reward table admits a closing nonnegative costate;
- a sparse law from the dual arm is an ordinary behavioral law;
- a source-supported conic reweighting preserves the literal source law;
- the sparse law is a Nash root, an LCP solution, or a finite executable
  block;
- an external public lottery is available;
- the sharp nonbehavioral law stays separated from behavioral laws under
  approximation with small singleton/Never leakage; or
- the limiting joint-carrier law is attained by one profile.

The proved terminal conclusion is exactly the chamber arm. The sparse arm
is the exact finite reward-table boundary and an impossibility result for
several tempting automatic consumers.

## Lean formalization record

Pre-formalization packet SHA-256:
`c3a67fc0ad72f046cf7b4ee37b12ba4c2bf6d430dbe2e8649a7f0d9b8d37dc57`.

The complete chamber, joint-law, sparse-cone, source-lift, and regression
surfaces were integrated in commit
`745305f2cf2c57feb4b61a4e7b8bd592b3950bba`.

The generic finite-dimensional owners are
`MathUE/LinearAlgebra/FiniteConicSparseCombination.lean` and
`MathUE/LinearAlgebra/FiniteConePositiveAlternative.lean`. The game-semantic
owners are
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticNonnegativeWeightChamber.lean`,
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticNonnegativeWeightLawCertificate.lean`,
`UniformEquilibrium/Diagnostics/Quitting/TerminalRewardSparseAlternative.lean`,
and
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticLawSparseSourceImprovement.lean`.
The three exact examples live under
`UniformEquilibrium/Diagnostics/Quitting/Regression/`.

The principal checked declarations are
`minimumTerminalSemantic_nonnegativeWeight_chamber`,
`minimumTerminalSemantic_debtSum_le_nonnegativeWeightBound_of_two_positive`,
`exists_uniformEquilibriumPayoff_of_nonnegativeWeightChamber`,
`minimumTerminalSemantic_exists_jointLawLiftFiniteAtom_weightedSurplus_and_mass_ge`,
`exists_finFourTerminalLawFiniteAtom_weightedSurplus_and_mass_ge`,
`exists_finFourTerminalLawFiniteAtom_weightedSurplus_and_mass_ge_symmetricRewardBound`,
`xor_supportedStrictSocialCostate_or_sparseRewardImprovement`, and
`nonempty_terminalSemanticLawSparseSourceImprovement_of_positiveMinimum`.
The sharp Fin4 law has exact support cardinality four and is excluded from
both arbitrary behavioral realization and one-date product-root realization.
The two-player and mixed-singleton regressions retain the literal payoff and
weight data displayed above.

Evidence seals:

- **M:** PASS. Sections A--D, including the stronger general mass floor
  `c D / (R T K)`, the Fin4 `D / (16R)` floor, and the packet's weaker
  `D / (32R)` corollary, match the audited mathematics.
- **L:** PASS. All nine source modules are reachable from the production
  umbrellas and generated axiom audit. The full project build and the
  representative axiom prints passed with only `propext`,
  `Classical.choice`, and `Quot.sound`.
- **A:** PASS at the stated source interfaces. The chamber selects an actual
  compact-carrier minimum, and the law certificate and sparse improvement
  retain an actual joint-law lift. The sparse law reweights source atoms; it
  is not the original law or a behavioral realization.
- **C:** branch-local. The incompatible nonnegative-weight chamber reaches
  the checked zero-minimum unrestricted-behavior uniform-payoff consumer.
  The positive-social atom and sparse-law arms have no downstream behavioral,
  chronological, Nash, or terminal consumer.

The formalization does not assert that every table has a closing costate,
that a sparse law is behaviorally realizable, that an external lottery is
available, or that the sharp law remains quantitatively separated under
small singleton/Never leakage. It does not close the Fin4 residual.
