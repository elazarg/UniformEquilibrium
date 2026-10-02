# Zero-singleton behavioral-law closure and complete semantic realization

Authors: CODEX_SOCIAL_SOURCE, CODEX_SOCIAL_RANK  
Independent reviews:
[CODEX_DESCENDANT](../feedback/CODEX_SOCIAL_SOURCE__CLOSED_BEHAVIORAL_LAW_PRODUCT_BASE__BY_CODEX_DESCENDANT.md),
[SOCIAL_WEIGHT_REVIEW](../feedback/CODEX_SOCIAL_SOURCE__CLOSED_BEHAVIORAL_LAW_PRODUCT_BASE__BY_SOCIAL_WEIGHT_REVIEW.md)

## Exact statements

Let \(I\) be a finite player set with at least two players. At every live
date, the players independently choose Quit or Continue using ordinary
private behavioral randomization. There is no public correlating device.
The terminal outcome is the first nonempty quitting coalition, or Never.

### A. Closed-law product-base theorem

Let \(\mu_n\) be terminal laws of ordinary behavioral profiles and suppose
\(\mu_n\to\mu\) coordinatewise. If

\[
 \mu(\mathrm{Never})=0,
 \qquad
 \mu(\{i\})=0
 \quad(i\in I),
\tag{A1}
\]

then there is \(q^*\in[0,1]^I\) and distinct \(i,j\in I\) such that

\[
 q_i^*=q_j^*=1
\tag{A2}
\]

and

\[
 \mu(S)=
 \prod_{k\in S}q_k^*
 \prod_{k\notin S}(1-q_k^*)
 \quad(S\ne\varnothing).
\tag{A3}
\]

Thus \(\mu\) is exactly one product-root law with a sure-quitter core of
cardinality at least two. In Fin4 its support has cardinality \(1\), \(2\),
or \(4\), and every supported coalition contains one fixed pair.

The outcome space is finite. Hence coordinatewise, weak, and total-variation
convergence are the same topology here.

### B. Complete semantic-pair realization

Let \(\sigma_n\) be the profiles above, and suppose their prescribed payoff
and unrestricted behavioral cap pairs converge to

\[
 \operatorname{Sem}(\sigma_n)\longrightarrow z=(U,B).
\]

Write \(s_i=r_i(\{i\})\). If

\[
 B_i\geq s_i
 \quad(i\in I),
\tag{B1}
\]

then \(z\) is attained by one literal finite profile: play one all-Continue
padding row, then the product root \(q^*\) from A, and then Never. This
profile has law \(\mu\), prescribed payoff \(U\), and the same complete
unrestricted cap vector \(B\).

If the inequalities are strict,

\[
 B_i>s_i\quad(i\in I),
\tag{B1s}
\]

then the padding row is unnecessary: the product root \(q^*\), followed by
Never, already attains \(z\). Stationary repetition of \(q^*\) is
semantically equivalent. The sure-quitter core has cardinality at least two,
so prescribed play absorbs at the first root, and after any one player's
behavioral replacement at least one opponent still Quits surely at that same
root.

At every positive global minimum of terminal semantic debt, the checked
singleton margin gives

\[
 B_i-s_i\geq D_*>0,
\tag{B2}
\]

so B applies automatically.
In fact (B2) supplies (B1s), so the unpadded and stationary realizations apply
at every positive global minimum.

### C. Superseded sure-core descent route

The former renewable sure-core-softening route is no longer an active
formalization target. Once A--B realize the supplied positive global minimum
by a literal root-then-Never product profile, that profile is finite-clock.
The checked reduction recorded in
[`PURE_FINITE_CLOCK_MINIMUM_DEADLINE_RANK_TO_PAID_PORT.md`](../formalized/PURE_FINITE_CLOCK_MINIMUM_DEADLINE_RANK_TO_PAID_PORT.md)
therefore reaches an actual off-minimum paid port directly, without the
full-debt hypothesis, the sure-core rank, or a positive-singleton
intermediate.

Sections A--B remain the useful content of this live packet. Section C is not
claimed formalized by PURE: its stronger root-softening geometry is simply
unnecessary for the active finite-clock-to-paid-port reduction.

## Proof of A

For a product root \(q\in[0,1]^I\), put

\[
 p_q(S)=\prod_{i\in S}q_i\prod_{j\notin S}(1-q_j),
\]

\[
 a(q)=1-p_q(\varnothing),
 \qquad
 b(q)=\sum_i p_q(\{i\}).
\]

For one behavioral profile, let \(q_t\) be its product root at the unique
live history at date \(t\), and let

\[
 L_t=\prod_{s<t}p_{q_s}(\varnothing).
\]

Its total singleton and Never masses are

\[
 \sigma=\sum_tL_tb(q_t),
 \qquad
 \zeta=\lim_tL_t,
\tag{1}
\]

and

\[
 1-\zeta=\sum_tL_ta(q_t).
\tag{2}
\]

### Local concentration

Suppose \(q^n\) satisfies \(a(q^n)>0\) and

\[
 \frac{b(q^n)}{a(q^n)}\longrightarrow0.
\tag{3}
\]

Then

\[
 \max_{i\ne j}q_i^nq_j^n\longrightarrow1.
\tag{4}
\]

Indeed, the event that at least two players Quit is contained in the union of
the pair events, and \(q_i\leq a(q)\). Therefore, with \(N=|I|\),

\[
 a(q)-b(q)
 \leq\sum_{i<j}q_iq_j
 \leq {N\choose2}a(q)^2.
\tag{5}
\]

Equations (3) and (5) exclude \(a(q^n)\to0\). If (4) failed, pass to a
convergent subsequence \(q^n\to q\) on which every pair product stays below
\(1-\varepsilon\). Then \(a(q)>0\) and \(b(q)=0\). If no coordinate of
\(q\) equals one, every positive coordinate creates positive singleton mass.
If exactly one coordinate equals one, that coordinate has positive singleton
mass. Thus at least two coordinates equal one, contradicting the pair-product
bound.

### First efficient root

For profile \(n\), let \(\sigma_n\) and \(\zeta_n\) be its singleton and Never
masses. Hypothesis (A1) gives

\[
 \sigma_n\to0,
 \qquad
 \zeta_n\to0.
\]

Choose \(\delta_n\downarrow0\) with

\[
 \sigma_n/\delta_n\to0.
\tag{6}
\]

Let \(t_n\) be the first positive-absorption date satisfying

\[
 b(q_{n,t_n})\leq\delta_na(q_{n,t_n}).
\tag{7}
\]

Such a date exists eventually. Otherwise (1)--(2) would give
\(1-\zeta_n\leq\sigma_n/\delta_n\to0\), contrary to \(\zeta_n\to0\).
Every earlier positive-absorption date violates (7), so the probability
\(E_n\) of absorption before \(t_n\) satisfies

\[
 E_n\leq\sigma_n/\delta_n\to0.
\tag{8}
\]

By local concentration, some pair has product tending to one at the selected
root. Pass to a subsequence on which the pair \(P=\{i,j\}\) is fixed and
\(q^n:=q_{n,t_n}\to q^*\). Then \(q_i^*=q_j^*=1\).

Let \(\nu_n\) be the one-root law of \(q^n\), followed by Never on all
Continue. Couple the source and one-root profiles. Count every absorption
before \(t_n\) as disagreement. Conditional on source survival to \(t_n\),
use the same product draw \(q^n\). If both members of \(P\) Quit, both
profiles terminate at the same coalition. Every tail outcome, including
Never, is counted as disagreement when the selected pair fails. Hence

\[
 \|\mu_n-\nu_n\|_{\rm TV}
 \leq E_n+1-q_i^nq_j^n\longrightarrow0.
\tag{9}
\]

Product laws depend polynomially on \(q\). Thus \(\nu_n\) converges to the
product law of \(q^*\), while it also converges to \(\mu\). This proves A.

## Proof of B

For a root \(q\), let \(\rho(q)\) play \(q\) at date zero and Never after all
Continue. Let \(\widehat\rho(q)\) add one all-Continue row before \(\rho(q)\).
Both have prescribed payoff

\[
 U_i(q)=\sum_{S\ne\varnothing}p_q(S)r_i(S).
\tag{10}
\]

Against opponents \(q_{-i}\), define

\[
 Q_i(q_{-i})
 =\sum_{A\subseteq I\setminus\{i\}}
 p_{q_{-i}}(A)r_i(A\cup\{i\}),
\tag{11}
\]

and

\[
 C_i(q_{-i})
 =\sum_{\varnothing\ne A\subseteq I\setminus\{i\}}
 p_{q_{-i}}(A)r_i(A)
 +p_{q_{-i}}(\varnothing)\max\{0,s_i\}.
\tag{12}
\]

The second term includes both Never and an arbitrarily late singleton Quit
after all opponents Continue. Arbitrary calendar-dependent and privately
randomized behavior gives no value beyond the root endpoints and this
post-root choice. Therefore

\[
 B_i^{\rho(q)}=\max\{Q_i,C_i\},
 \qquad
 B_i^{\widehat\rho(q)}=\max\{s_i,Q_i,C_i\}.
\tag{13}
\]

Use the selected dates and roots from A. For fixed \(i\), let \(H_{n,i}\) be
the probability that all opponents of \(i\) survive strictly before \(t_n\).
Since joint survival is \(1-E_n\),

\[
 H_{n,i}\geq1-E_n\longrightarrow1.
\tag{14}
\]

After deleting \(i\), one member of the almost-sure pair \(P\) remains among
its opponents. Hence

\[
 h_{n,i}:=\prod_{j\ne i}(1-q_j^n)\longrightarrow0.
\tag{15}
\]

Compare the original opponents with opponents who Continue before \(t_n\),
play \(q^n_{-i}\) there, and Never afterward. Under the same arbitrary
behavioral replacement by \(i\), the two outcomes can differ only if an
original opponent stops before \(t_n\), or every opponent Continues at the
selected root. With rewards bounded by \(R\), every replacement payoff
therefore differs by at most

\[
 2R(1-H_{n,i}+h_{n,i})\longrightarrow0.
\tag{16}
\]

The estimate is uniform over the complete unilateral behavioral class, so it
survives taking suprema. If \(t_n=0\), it identifies the limiting cap with
\(B_i^{\rho(q^*)}\). If \(t_n>0\), every pre-root Quit gives \(s_i\), so it
identifies the cap with \(B_i^{\widehat\rho(q^*)}\). Pass to a subsequence on
which one calendar case is constant. In the zero-date case, (B1) shows that
adding the singleton option does not enlarge the cap. Thus in both cases

\[
 B_i=B_i^{\widehat\rho(q^*)}.
\]

This holds for every player. Equation (9) transports the prescribed payoff
and ordinary law, proving B.

If (B1s) holds, then in the positive-date case

\[
 B_i=\max\{s_i,Q_i,C_i\}>s_i
\]

forces \(B_i=\max\{Q_i,C_i\}=B_i^{\rho(q^*)}\). Hence the unpadded profile
already realizes the complete pair. Because \(q^*\) has at least two sure
quitters, prescribed play under stationary repetition absorbs at date zero;
after any unilateral behavioral replacement, one unchanged sure-quitting
opponent still absorbs at date zero. Therefore stationary repetition has the
same prescribed payoff, law, and complete cap as \(\rho(q^*)\).

## Exact calendar and counterfactual boundary

The cap proof is one-deviator-at-a-time. It covers unrestricted behavioral
deviations, including Never and arbitrarily late stopping, because (16) is
uniform before taking the supremum.

It does not preserve the law of the same labeled calendar-dependent
intervention when the selected root is compressed from date \(t_n\) to date
one. For example, let the source Continue for \(n\geq2\) dates and then play
the pure pair \(\{0,1\}\), while the fixed realization plays that pair at date
one. If player \(2\) is replaced by Quit-exactly-at-date-one, the source
terminates at \(\{2\}\), while the fixed realization terminates at
\(\{0,1,2\}\). Their intervention laws have total-variation distance one.

Two stronger law statements are valid:

1. keeping the root at its moving original date \(t_n\), the coupling is
   uniform under interventions that leave at least one member of \(P\)
   unchanged; and
2. every one-player-deleted law converges to the deleted law of the fixed
   padded product profile, because the deleted player is Never at every date
   and is invariant under calendar compression.

No simultaneous fixed-padding intervention kernel is claimed.

## Conjecture-facing change

Previously, a sparse reward-improving law could be an unrealizable correlated
object, while law convergence alone did not transport unrestricted caps.
A--B show that the literal zero-Never, zero-singleton source law is much more
rigid: its full limiting semantic point is a finite persistent-base product
profile.

At a positive global minimum, B supplies the strict unpadded realization, so
the exact same semantic pair and law are attained by an actual finite-clock
profile. The checked PURE reduction then reaches an actual off-minimum paid
port. This composition bypasses the superseded sure-core descent, but A--B
remain the missing production source adapter.

## Source correspondence

Existing checked inputs:

- terminalSemanticLawCarrier_rewardMoment and
  exists_terminalSemanticLawCarrier_lift in
  UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticResetIncidenceReturn.lean;
- quittingTerminalOutcomeMass and quittingTerminalRewardMoment in
  UniformEquilibrium/Quitting/Root/TerminalSemanticMoment.lean;
- minimumTerminalSemantic_singletonMargin in
  UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticAuxiliaryNashBudget.lean
  for (B2);
- exists_positive_finiteLawAtom_of_finFourHardResidual_minimum in
  UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinFourMinimumLawFiniteAtom.lean;
- the persistent-base finite-game and all-behavior consumer interfaces under
  UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/.

New ordinary mathematics:

- the first-efficient-root closure theorem A;
- the complete scalar-cap realization B; and
- the stationary-repetition semantic equivalence in the strict-margin case.

## Boundary tests

1. A pure pair law satisfies A exactly, but arbitrary rewards may make a pair
   member profit by leaving; product realization is not Nash.
2. The uniform law on
   \(\{0,1\},\{0,2\},\{0,3\},\{1,2\}\) has zero Never and singleton mass but
   no common pair. A excludes even approximation by ordinary behavioral
   laws, although a public lottery realizes it.
3. Condition (B1) is necessary for the padded conclusion. At the pure pair
   \(\{0,1\}\), set
   \(r_0(\{0\})=10\) and
   \(r_0(\{0,1\})=r_0(\{1\})=0\). The unpadded cap of player \(0\) is zero,
   while one padding row adds the singleton option of value \(10\).
4. The retired sure-core route used softening rather than deletion to retain
   positive mover debt. The active A--B theorem does not assert either
   operation or any debt descent.

## Adapter and consumer

Given a source-attached joint global-minimum point, inspect its literal law.
Positive Never or singleton mass remains in the corresponding established
atlas arm. If both vanish, A constructs \(q^*\), and B uses the checked
minimum singleton margin to realize the exact same semantic pair and law by
the root-then-Never product profile (and, at the entrance, its stationary
repetition). This is an actual finite-clock profile. The checked PURE theorem
then supplies the off-minimum paid-port reduction. The two components are now
separately checked in production Lean; no declaration in this record claims
their end-to-end composition.

## Formalization record

Sections A--B were integrated in production Lean by commit
`fc81addfa5ff98f12a82735bce03e29cbe92fce4`.

- `zeroSingletonProductBase_zeroNever_zeroSingleton_law_productBase`
  (`UniformEquilibrium/Diagnostics/Quitting/ZeroSingletonProductBaseLaw.lean`)
  is the checked closed-law product-base theorem.
- `exists_twoSureProductRoot_realizing_law_of_mem_terminalSemanticLawCarrier`
  (`UniformEquilibrium/Diagnostics/Quitting/ZeroSingletonBehavioralLawProductBase.lean`)
  supplies the literal joint-carrier source adapter, the fixed sure pair, the
  exact complete law, and common-pair support.
- `exists_twoSureProductRoot_realizing_jointCarrierPoint_of_strictMargin` and
  `exists_twoSurePaddedProductRoot_realizing_jointCarrierPoint_of_margin`
  check the strict root-then-Never/stationary and nonstrict one-row-padded
  complete semantic/law realizations.
- `quittingProductRootCoalitionSupport_card_eq_one_or_two_or_four`
  (`UniformEquilibrium/Diagnostics/Quitting/ProductRootLawSupport.lean`)
  states the Fin4 support-cardinality alternatives literally.

Thus Sections A--B have `M`, `L`, and branch-local actual-source `A` from the
supplied joint terminal semantic/law carrier point. They have no downstream
`C`.

## Scope and nonclaims

Sections A--B do not prove Fin4 UE, consume the off-minimum paid target
returned by PURE, or preserve a common law for arbitrary simultaneous
calendar-dependent interventions after fixed padding compression. The former
Section C root-softening descent is superseded by the already formalized PURE
finite-clock reduction. It is not claimed formalized by this record.
