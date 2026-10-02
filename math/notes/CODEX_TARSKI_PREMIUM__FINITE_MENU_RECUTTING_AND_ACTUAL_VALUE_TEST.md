# Deadline recutting does not reduce original finite-menu exploitability

Author: CODEX_TARSKI_PREMIUM.

Status: bounded positive attempt stopped at its actual missing inequality.
No general selector, all-menu obstruction, or counterexample to the current
question is proved. The exact small test below has an immediate successful
finite selector. The recutting calculation explains why decreasing one
auxiliary tail coordinate supplies no decrease of the original objective.
The tested second operation is already an existing cap-prefix theorem;
no new conditional architecture or constants refinement is proposed.

## 1. The actual question and the optional bonus method

The CURRENT question
[FIN4_SINGLE_PIVOT_FINITE_MENU_SELECTION](../questions/FIN4_SINGLE_PIVOT_FINITE_MENU_SELECTION.md)
has four independent behavioral quitting players, Never payoff zero, and
own singletons s=(1,0,0,0), with arbitrary other finite real rewards. For
every ε>0 it asks for one N≥1 and product law p on
F_N={0,…,N−1,Never} such that

    E_N(p)≤ε,       L_0(p)=W_0(p)+D_0(p)−U_0(p)≤ε.

Its unrestricted exploitability is exactly E(p)=max(E_N(p),L_0(p)).
Neither exact finite-menu Nash nor any bonus best-response equation is a
premise. Deadlines and laws may vary freely and independently across errors.

Positive planned-Never bonuses are one optional synthesis method. In that
method nonpivots have finite laws, the pivot globally minimizes the original
full-cap objective over its complete behavioral choices through the compact
repair LP, and nonpivots best respond to compensation plus bonus. The added
bonus ceiling η is strictly positive. A failure inside this method would
not, by itself, refute the question. This distinction was clarified with
ROOT before the test was concluded.

The two requested stopped-test notes were read to avoid importing an
invariant low-value set, exactification of fixed finite support, or a
favorable head/tail cap comparison:

- [RENY: positive-bonus approximate completeness](CODEX_RENY__POSITIVE_BONUS_APPROXIMATE_COMPLETENESS_TEST.md);
- [HILBERT: joint Never-arm release](CODEX_HILBERT__GLOBAL_MAXIMUM_JOINT_NEVER_RELEASE_BOUNDARY.md).

## 2. Exact small positive test with two very different selections

Use this complete four-player table, with |r_i(S)|≤1:

    r_0(S)=1 if 0∈S, and 0 otherwise;
    r_j(S)=−1 if 0∈S and j∉S, and 0 otherwise, j=1,2,3.

Every coalition containing a nonpivot pays that participating player zero.
Thus s=(1,0,0,0), exactly as in the question.

Take the three nonpivots to Never surely. If the pivot's total finite
stopping mass is f, then its prescribed payoff is f and its full cap is 1.
Each nonpivot's prescribed payoff is −f and its full cap is 0, attained by
Quit at date zero. For EVERY actual pivot law,

    E=max(1−f,f)≥1/2.

Equality holds at f=1/2. This is the GLOBAL PIVOT optimum against these
three particular laws, not a global minimum over all four laws.

For a literal finite realization, let the pivot quit at date 1 with
probability 1/2 and Never otherwise. In the original repair description
with nonpivot cutoff N=1, its head is empty and

    λ=α=ν=1/2,       D=D_j=1,
    a_j=r_j({0})=−1,       b_j=r_j({0,j})=0.

The nonpivot Never payoff is W_j=−1/2, its first late endpoint is C_j=0,
and its compensation is Δ_j=1/2. Set extra bonuses β_j=0. Every old
finite action and compensated Never pays zero, so the selected nonpivot
Never laws are exact auxiliary best responses. The pivot is globally
optimal, and the ORIGINAL full objective is 1/2.

Now change only the description's cutoff to N=2. The same actual pivot
date-1 mass is part of the head; its new late mass is λ'=0. Both finite
nonpivot options 0 and 1 still pay zero. Its Never payoff remains −1/2,
its compensation becomes Δ'_j=0, and extra bonus β'_j=1/2 preserves the
same auxiliary objective and best responses. The same pivot remains
globally optimal. The entire actual product law is unchanged.

Thus the positive ceiling η=1/2 permits the recutting, while

    old λD=1/2,       new λ'D=0,
    old E=new E=1/2,
    new E_N=new L_0=1/2.

The sharper compensated residual is exactly conserved:

    β'_j z_j+D[b_jα'−a_jλ']_+=1/2.

This is an exact accounting test, not a negative answer: on the SAME table,
the law under which all four players Quit at date zero is exact full
terminal Nash. Player 0 loses 1 by leaving the coalition; every nonpivot
loses 1 by leaving it. Any unilateral behavioral replacement still faces
three sure first-date quitters, so these endpoint comparisons cover its
complete deviation class. Consequently this table admits

    N=1,       E_N=0,       L_0=−1

at EVERY positive accuracy. The test explicitly preserves the question's
freedom to choose unrelated actual laws and another deadline.

## 3. The short general accounting identity

For a literal geometric repair tail at cutoff N, let finite mass λ>0,
first atom α>0, Never mass ν, and r=1−α/λ∈[0,1). Its atom at N+k
is αr^k. Keep ALL actual stopping laws fixed but move the description's
cutoff to N+k by exposing those first k atoms as finite head. Then

    λ_k=λr^k,       α_k=αr^k,       ν_k=ν.

With a_j,b_j,D_j as above, the full nonpivot Never payoff W_j is unchanged.
The old and new first-late endpoints satisfy

    C_j−W_j=D_j(b_jα−a_jλ),
    C_(j,k)−W_j=r^k D_j(b_jα−a_jλ).

Hence endogenous compensation changes by

    Δ_(j,k)=r^kΔ_j.

Keeping the same total Never subsidy uses

    β_(j,k)=β_j+(1−r^k)Δ_j.

This can exceed a prescribed small positive bonus ceiling. Even when it
stays within that ceiling, the weighted term in the residual is unchanged:

    z_j[β_(j,k)+Δ_(j,k)]=z_j[β_j+Δ_j].

Most importantly, the original U_i and every unrestricted response cap
are unchanged because the actual laws are unchanged. Thus full E is
unchanged independently of any auxiliary response equations. Apparent
decay λ_kD→0 has transferred compensation into the option bonus; it has
not supplied an original-game gain.

The face α=0<λ is not an actual geometric law and is not used for this
argument or assigned a fictitious tail. The explicit small test above has
α=λ>0 and is finite throughout, so no limiting or realization issue is
needed to establish the failure of the proposed decrease inference.

## 4. Tested actual-law change and exact stopping point

A second operation that really changes all four laws is to prepend a new
independent product root q to an actual continuation profile p. Write U_i
and B_i for that profile's prescribed value and FULL behavioral cap. If
q is exact Nash in the one-shot continuation game with continuation B,
then its literal prefixed debt satisfies

    B'_i−U'_i=c(q)(B_i−U_i),       E'=c(q)E.

This follows because B'_i=max(Q_i(q),C_i(q,B))=F_i(q,B), while
U'_i=F_i(q,U). On the small table, q=all-Quit gives c(q)=0 and the
successful finite selector already displayed. It is an actual law change,
unlike recutting.

A narrow source search found this exact identity already in
`quittingTerminalDeviationDebt_rootThenContinuation_eq_continueMass_mul_of_capNash`
and its finite-stack version
`quittingTerminalDeviationDebt_capNashRootStack_eq`
(UniformEquilibrium/Quitting/Root/CapNashRootStack.lean).
`exists_maximalAbsorption_isZeroQuittingRootNash`
(UniformEquilibrium/Quitting/Root/MaximalAbsorptionNash.lean) already selects
the most absorbing exact root at each supplied cap.

These declarations do not force positive absorption or vanishing cumulative
survival for arbitrary actual caps. Imposing exact cap-Nash at every new
prefix would narrow the current question, which permits arbitrary finite
law changes and approximate menu Nash. Therefore the existing identity is
not repackaged here as a new architecture or universal source.

The missing inequality for a useful continuation of THIS attempt is a
table-derived change of the actual laws with controlled NEW full caps that
reduces their original maximum debt. Neither recutting, a bonus parameter,
nor the availability of a cap-Nash root supplies the required value drop.
No fixed continuation region, invariant low-value set, or local Nash
condition is adopted as an unstated premise. The method is stopped here.

## 5. Narrow source record and outcome

The route was chosen through the finite-menu and pivot-repair entries of
docs/TOOLKIT.md. Exact source declarations inspected:

- `singlePivot_fullExploitability_eq_max_menuExploitability_scalar` in
  UniformEquilibrium/Quitting/Terminal/SinglePivotFiniteMenuSource.lean;
- `exists_objective_minimizer_eq_behavioral_infimum` in
  UniformEquilibrium/Quitting/Terminal/PivotRepairBehavioralInfimum.lean;
- `HasQuittingSmallPivotRepairValue` and
  `exists_pivotRepairMass_objective_le_finiteMenu_exploitability` in
  UniformEquilibrium/Quitting/Terminal/PivotRepairSmallValueSource.lean;
- `otherNeverProduct`, `responderNeverEndpoint`, `responderFirstEndpoint`,
  and `objective` in
  UniformEquilibrium/Quitting/Terminal/PivotRepairFiniteLP.lean;
- the two literal cap-prefix/stack debt identities and maximal-absorption
  root source named in Section 4.

The compensation notation and existing residual were read in
[RENY's original compensated selector](CODEX_RENY__LATE_CAP_COMPENSATED_NEVER_SELECTOR.md).
They are ordinary research-source statements, kept separate from the named
production declarations above. No Lean build or new Lean implementation
was performed.

What survives is an exact accounting lemma and an exact small positive
test that rejects a false decrease inference while leaving successful
reselection available. Neither constitutes an arbitrary-table all-accuracy
selector or a negative answer to the question. No frozen export changed.

Next concrete research question: find an actual joint-law operation whose
upper bound on NEW unrestricted caps yields a positive original-value drop
at a true positive global minimum, without assuming an absorbing cap-Nash
prefix or a favorable head/tail cap comparison. Recutting alone is retired.
