# Auxiliary cap descent: finite full-response selectors and exact limits

## Status and scope

This note gives an ordinary-mathematics construction. It has not been formalized in Lean or independently reviewed. The finite example and all its unrestricted response caps were checked separately in exact rational arithmetic.

The construction proves two results.

1. A uniform deficit below the own-singleton vector forces an explicit, geometrically convergent sequence of actual finite stopping laws. No joining-gain condition is required. If all own singletons are nonnegative, it also produces an exact terminal Nash equilibrium at every suffix, with a uniform joint-absorption bound.
2. The entire non-strict two-pair payoff-exclusion class in the uploaded note admits an explicit finite selector with total complete regret O(1/N), without the extra hypotheses used there for its geometric finite-menu producer.

The auxiliary-prefix debt inequality is existing mathematics in the repository. The contributions here are the margin-to-absorption argument, its adaptive use in an actual prefix algorithm, the rational approximate-root version, the resulting quantitative selectors, and the exact all-suffix limit under nonnegative singletons.

These results do not solve arbitrary Fin4. They strengthen the construction and, in the strict nonnegative-singleton case, the equilibrium conclusion on classes already known to have UE from the supplied payoff-exclusion argument. No enlargement of that note's qualitative Theorem 1 existence class is claimed merely from making its producer quantitative.

## 1. Model and complete semantics

Let I be a finite nonempty player set, n=|I|, and let r(S) be the reward at each nonempty quitting coalition. Never pays zero. Assume |r_i(S)|<=M, with M>0, and put s_i=r_i({i}).

A player independently samples a stopping time in the nonnegative integers together with Never. For an actual product profile p define

    U_i(p) = prescribed expected terminal reward,
    B_i(p) = sup over all replacement stopping laws of U_i(replacement,p_-i),
    d_i(p) = B_i(p)-U_i(p),
    D(p)   = sum_i d_i(p).

All finite pure times, arbitrarily late dates, Never, and private randomization are included in B_i. A randomized replacement cannot exceed the supremum of the pure-time and Never values.

For a root q in [0,1]^I, define

    c(q)    = product_i (1-q_i),
    a(q)    = 1-c(q),
    beta_i  = product_(j!=i) (1-q_j),
    pi_i(q) = q_i beta_i = Pr_q(terminal coalition {i}).

Let Q_i(q) denote the current Quit endpoint. Write the Continue endpoint against an annotation v as

    C_i(q;v_i) = H_i(q) + beta_i v_i,

where H_i is the absorbing contribution when i Continues. Prefixing the actual old profile, not the annotation, gives the exact unrestricted identities

    U'_i = q_i Q_i + (1-q_i) C_i(q;U_i),
    B'_i = max(Q_i, H_i + beta_i B_i).                 (1)

No cap attainment is needed for the second formula.

For a finite word followed by all-Never, these quantities are finite calculations. Initialize

    U^0_i=0,     B^0_i=max(s_i,0).

Then apply (1) once for every prefixed row. Equivalently, for a profile on N dates plus Never, the unrestricted cap is a maximum over the N displayed dates, one additional finite date after the cutoff, and Never. All later finite dates are outcome-equivalent against those opponents.

## 2. The complete-debt prefix ledger

Choose a scalar h>=0 and an auxiliary annotation

    v=B-h*1.

Let the ordinary mixed root regret against v be

    g_i=max(Q_i,C_i(q;v_i))
          -[q_i Q_i+(1-q_i)C_i(q;v_i)].

The root need not be Nash against the actual prescribed continuation U. Nevertheless, when it is literally prefixed to the old actual profile,

    d'_i <= c d_i + pi_i h + g_i.                      (2)

Indeed, if w_i is the mixed root payoff against v, then

    B'_i <= w_i+g_i+beta_i h,
    U'_i  = w_i+c(h-d_i).

Subtract and use beta_i-c=pi_i. Summing gives

    D' <= cD+h sum_i pi_i+sum_i g_i
       <= D-a(D-h)+sum_i g_i.                         (3)

More precisely, there is an additional favorable collision term:

    D-D' >= a(D-h)+h Pr_q(at least two quitters)-sum_i g_i.  (4)

Thus the construction does not assume that the individual debts decrease. Previously zero debts can increase. Their aggregate, including the complete caps after the actual prefix, is what (3) controls.

For exact auxiliary Nash roots, g_i=0, and (2) is the existing declaration
`quittingTerminalSemanticDebt_prefix_le_auxiliaryNash`
in `UniformEquilibrium/Quitting/Terminal/AuxiliaryNashDebt.lean`.
The error term in (2) follows from the displayed calculation.

## 3. A below-singleton auxiliary coordinate forces absorption

Suppose for some i and delta>0 that

    v_i <= s_i-delta.

Let a_i=1-beta_i be its opponents' absorption probability. Conditioning on whether any opponent Quits gives

    Q_i-C_i(q;v_i)
      >= beta_i delta-2M a_i
      >= delta-(2M+delta)a(q).                        (5)

This estimate does not require an absolute bound on the auxiliary coordinate v_i.

### Exact-root version

Every exact root Nash profile against v satisfies

    a(q) >= delta/(2M+delta).                         (6)

Otherwise (5) makes Quit strictly better for i. Exact Nash forces q_i=1, contradicting the assumed small joint absorption.

### Approximate-root version

If every root regret is at most delta/4, then

    a(q) >= delta/[2(2M+delta)].                      (7)

If absorption were smaller, (5) would give Q_i-C_i>delta/2, while q_i<=a(q)<1/2. The mixed regret of i would exceed delta/4.

## 4. Uniform payoff deficit: a geometric actual-law producer

Assume there is kappa>0 such that every actual profile satisfies

    min_i [U_i(p)-s_i] <= -kappa.                     (PD)

The condition is on payoffs of all actual profiles. It is not a claim that a single low-payoff realization has small caps. For the construction it suffices that (PD) holds for finite-word profiles.

Start from all-Never and recursively calculate the complete U^m,B^m,D_m. Set

    t_m = min(D_m,kappa/2),
    h_m = D_m-t_m,
    v^m = B^m-h_m*1.                                 (8)

Choose any exact Nash root of the finite Boolean game with continuation v^m, and literally prefix that root to p^m:

    p^(m+1)=q^m::p^m.                                (9)

The resulting p^N is a product of laws on N finite dates plus Never.

### The forcing argument

Choose i with U_i^m<=s_i-kappa. Since d_i^m<=D_m,

    v_i^m = U_i^m+d_i^m-D_m+t_m
          <= s_i-kappa+t_m
          <= s_i-kappa/2.                            (10)

Put

    A = kappa/(4M+kappa).                            (11)

Equations (6), (10) give a(q^m)>=A. Equation (3) therefore gives

    D_(m+1) <= D_m-A min(D_m,kappa/2).                (12)

This is a decrease of the actual complete debt, with no horizontal cap installation or reconstruction seam.

Let

    D_0=sum_i max(s_i,0).

Applying (PD) to all-Never shows D_0>=kappa, so in particular D_0>0. The sequence is decreasing, and

    min(D_m,kappa/2) >= [kappa/(2D_0)]D_m.

Consequently

    D_N <= D_0 (1-kappa^2/[2D_0(4M+kappa)])^N.        (13)

A sharper two-regime estimate follows directly from (12): above kappa/2 there is a fixed additive decrease A*kappa/2; below it, debt contracts by 1-A at every step.

No sign condition on the individual singleton rewards, no punishment equality, and no joining-gain condition enters this finite-profile theorem.

### Rational approximate-root producer

For rational input data one need not trust numerical exact Nash roots. At a step with D_m>0 use the same (8), but find a rational root satisfying

    max_i g_i <= eta_m := A*t_m/(4n).                 (14)

Since eta_m<=kappa/8, (7) gives a(q^m)>=A/2. Equations (3), (14) then give

    D_(m+1) <= D_m-(A/4)min(D_m,kappa/2),
    D_N <= D_0 (1-kappa^2/[8D_0(4M+kappa)])^N.        (15)

Stop when the target debt is reached; if D_m=0, the current finite profile is already exact terminal Nash.

Existence of an accepted rational root is effective. If R bounds the absolute Boolean-game payoffs, every ordinary root-regret function is 4Rn-Lipschitz in the sup norm of the hazard vector. An exact Nash root exists by finite-game Nash existence. A grid of mesh at most eta_m/(4Rn) therefore contains a rational root satisfying (14). Exhaustive grid search terminates. This is not an efficient-complexity claim.

## 5. Uniform finite-horizon delivery

For a fixed N-date profile followed by Never, prescribed absorption is before the cutoff or does not occur. Thus its H-stage average payoff, for H sufficiently large, differs from U by at most

    M(N+1)/H.

Uniformly over deviations, the average payoff is at most

    B_i + M(N+1)/H.                                  (16)

To see the only sign-sensitive point, a deviation after the opponents' final finite date meets either an earlier opponent absorption or all-Never opponents. In the latter case its only possible terminal reward is s_i. If s_i>=0, delaying this reward cannot increase its finite-average payoff above its terminal payoff. If s_i<0, compare instead with the complete deviation that replaces these late quitting outcomes by Never; that comparison removes a nonpositive contribution. Early absorptions account for the displayed error in either case.

Therefore the finite-horizon regret is at most

    D_N + 2M(N+1)/H.                                 (17)

Choose a cluster point of the bounded vectors U(p^N), then select N along that cluster sequence and H large. This yields one fixed uniform-equilibrium payoff. The finite profile and the horizon threshold may depend on accuracy. This is also an instance of the repository's existing terminal-all-errors/fixed-uniform-target selection principle.

## 6. Stronger conclusion: exact equilibrium at every suffix

Add the assumption s_i>=0 for every player, and retain the strict payoff-deficit condition (PD).

**Theorem.** There is an actual infinite behavioral profile whose every suffix is exact terminal Nash. Every row has joint absorption probability at least A from (11). The same profile delivers its initial terminal payoff as a uniform-equilibrium payoff.

### Diagonal construction

Use the exact-root sequence (9). If debt becomes zero, keep selecting exact roots against its actual cap/payoff vector. Exact prefixing preserves zero debt, and (PD) still forces positive absorption, so the sequence can be continued indefinitely.

Chronologically, p^N has rows

    q^(N-1), q^(N-2), ..., q^0, then all-Never.

Compactness of [0,1]^I and a diagonal subsequence give q-bar_t such that, for each fixed t,

    q^(N_k-1-t) -> q-bar_t.

Every limit row has absorption at least A. Hence survival through L further rows from any suffix is at most (1-A)^L. Finite-prefix convergence and the uniformly vanishing payoff tail imply

    U(p^(N_k-t)) -> U(q-bar^t)                        (18)

for every fixed suffix t. The relevant old suffix is literally p^(N_k-t); it is not a separately selected profile.

### All finite deviations, then Never

For any fixed finite pure response date ell, its payoff depends on only finitely many opponent rows. Pass its inequality

    response payoff at p^(N_k-t)
      <= U_i(p^(N_k-t))+D_(N_k-t)

to the limit using (18) and D_m->0. Every finite pure response at q-bar^t is bounded by its prescribed payoff.

For fixed opponent laws, if L_i(ell) denotes the payoff from pure Quit at ell, then

    lim_(ell->infinity) L_i(ell)
      = U_i(Never,opponents)+s_i Pr(all opponents Never).  (19)

Since s_i>=0, the Never payoff is no greater than this limit of finite-response values. Therefore Never is also bounded. Averaging covers every privately randomized complete stopping law. This proves exact Nash separately at every suffix.

The argument does not assume that deviations inherit the prescribed joint-absorption bound. It uses (19) to handle precisely the possible positive opponent-deleted survival mass.

### The same profile is uniform

Prescribed expected absorption time is at most 1/A. Fix player i and let O_i be the first opponent quitting date, with O_i=Never allowed. Set

    e_(H,i)=E[1_{O_i finite} min((O_i+1)/H,1)].

Then e_(H,i)->0. Uniformly over own deviations, an average payoff can exceed its terminal payoff only through negative rewards. A negative reward from a sole own quit is impossible because s_i>=0. All remaining such rewards occur at the opponent clock O_i. Thus the average payoff of every deviation is at most B_i+M e_(H,i). The prescribed average payoff differs from U_i by at most M/(AH). Its horizon-H regret is therefore at most

    M e_(H,i)+M/(AH) -> 0.

No explicit rate for the deleted clock is asserted.

## 7. Non-strict group exclusion: an O(1/N) selector

There is also a finite-law producer without a uniform strict deficit.

Let a collection of probability weights w on I have a common coordinate bound

    max_i w_i <= beta < 1.

Assume every actual profile admits a weight in this collection satisfying

    sum_i w_i(U_i-s_i) <= 0.                          (GE)

Put rho=1-beta>0. At a source with total debt D>0 choose

    t=rho*D/2,
    h=D-t,
    v=B-h*1.                                         (20)

For a weight witnessing (GE),

    sum_i w_i(v_i-s_i)
      <= beta D-h = -rho D/2=-t.

Some coordinate is therefore below its singleton by at least t. An exact auxiliary Nash root has a>=t/(2M+t), and the actual complete-debt ledger gives

    D' <= D-rho^2 D^2/(8M+2rho D).                    (21)

With

    C=[8M+(2rho-rho^2)D_0]/rho^2,

reciprocal iteration yields

    D_N <= C D_0/(C+N D_0).                           (22)

If D_0=0, all-Never is already exact Nash.

For rational roots choose

    max_i g_i <= t^2/[4n(2M+t)].

The same argument with (7) gives

    D' <= D-rho^2 D^2/(32M+8rho D).

Thus (22) holds with the larger rational-producer constant

    C_rat=[32M+(8rho-rho^2)D_0]/rho^2.                (23)

### Application to the uploaded two-pair theorem

The two weights are the uniform measures on {0,1} and {2,3}, so beta=1/2. The uploaded clock argument and row inequalities establish (GE), including its Never term, for its entire Theorem 1 class. Consequently

    C=32M+3D_0,       C_rat=128M+15D_0.               (24)

For canonical singletons, D_0=1. The three nonpivot laws in p^N are therefore actual selected laws with optimal full-regret pivot-repair LP value at most

    (32M+3)/(32M+3+N)

for the exact-root construction, or

    (128M+15)/(128M+15+N)

for the rational approximate-root construction.

This does not require exact finite-menu Nash profiles and does not claim that an arbitrary own-payoff best-response repair preserves regret. The prescribed pivot law itself is a feasible competitor for the full-regret repair optimization.

Unlike the strict-deficit theorem, (GE) alone does not provide a positive absorption floor independent of accuracy. The exact-equilibrium diagonal conclusion of Section 6 is not asserted here.

## 8. Explicit negative-joining Fin4 fixture

Start from the complete rational table in the uploaded two-pair note and change just

    r_3({0,3}): 1/4 -> -1/4.

The complete resulting table is:

| Coalition | r_0 | r_1 | r_2 | r_3 |
|---|---:|---:|---:|---:|
| {0} | 1 | -2 | -15/4 | 0 |
| {1} | -5/2 | 0 | 1 | -3 |
| {2} | -7/4 | -5/4 | 0 | -5/2 |
| {3} | -2 | -3/4 | -4 | 0 |
| {0,1} | 2 | 1 | -3/4 | -3/4 |
| {0,2} | -3 | 1/2 | 1/2 | -13/4 |
| {0,3} | -7/4 | 1/2 | -9/4 | -1/4 |
| {1,2} | -3/2 | -3/2 | -2 | -3/2 |
| {1,3} | 1/2 | -2 | 1/2 | -15/4 |
| {2,3} | 1/4 | -3/4 | 1 | 1 |
| {0,1,2} | 0 | -3 | 7/4 | -17/4 |
| {0,1,3} | 5/4 | -9/4 | 0 | -4 |
| {0,2,3} | -1/2 | -5/2 | 3/2 | -15/4 |
| {1,2,3} | -3/4 | -1/4 | -1/2 | -9/4 |
| {0,1,2,3} | -1 | -7/4 | -7/2 | 3/2 |

Its canonical singleton vector is (1,0,0,0), and M=17/4. All the strict two-pair row bounds used for kappa=3/8 remain valid: the only changed group mean decreased. But

    (g_1,g_2,g_3)=(3,17/4,-1/4),

so the earlier all-nonnegative-joining hypothesis fails. Product-low still fails at q=(1,1,0,0). The correlated half-half lottery over {0,1} and {2,3} is still s+(1/8,1/8,1/8,1/8); hence the nonlinear payoff exclusion is not a nonnegative linear separation of the full convex hull.

For completeness, the kappa bound can be reconstructed from the clock inequality. Let x,y,n be the probabilities of the two target coalitions and Never, and let z=1-x-y-n. Put p=sqrt(x), q=sqrt(y), t=sqrt(n). Then p+q+t<=1. The row bounds give

    G_A(U)<=2p^2+(1/4)q^2+(1/2)t^2-1,
    G_B(U)<=(1/4)p^2+2q^2+t^2-1.

For p<=1/2 the first is at most 2p^2+(1/2)(1-p)^2-1<=-3/8. For p>=1/2 the second is at most (1/4)p^2+2(1-p)^2-1<=-7/16. At least one coordinate in the low pair is no greater than its mean. Thus (PD) holds with kappa=3/8 for every actual profile.

### Three rational prefixes

Use the following roots in **construction order**; the final profile plays them in reverse chronological order.

| Prefix | q_0 | q_1 | q_2 | q_3 |
|---|---|---|---|---|
| 1 | 2386017/76096933 | 80356906/99365033 | 70243795/97732973 | 47300903/49023997 |
| 2 | 1301064/76252885 | 80642351/99011632 | 64515646/90051035 | 76346577/78824219 |
| 3 | 1200151/75057758 | 4958849/6085172 | 59882048/83601291 | 74463212/76862663 |

All three satisfy the rational auxiliary-root acceptance inequality (14), verified exactly. The total complete debts are approximately

    1,
    0.05283329265560565,
    0.00008587633673792239,
    0.0000001388106540718527.

At the final profile,

    max_i d_i = approximately 1.0732213908978837e-7 < 1.1e-7,
    sum_i d_i < 1.4e-7.

The final prescribed payoff is approximately

    (-0.4350905821780818, -0.7748810394134403,
     -0.30116234673109626, -2.02397250305808).

These decimal displays are not the certificates. The checker evaluates all quantities as exact fractions and verifies the strict rational bounds.

If q^0,q^1,q^2 denote the listed construction rows, player i's actual law is

    Pr(T_i=0)     = q^2_i,
    Pr(T_i=1)     = (1-q^2_i)q^1_i,
    Pr(T_i=2)     = (1-q^2_i)(1-q^1_i)q^0_i,
    Pr(T_i=Never) = (1-q^2_i)(1-q^1_i)(1-q^0_i).

The checker independently enumerates the joint stopping laws and each player's five response classes: dates 0,1,2, one date after the cutoff, and Never. Its caps agree exactly with the recursive caps. This includes all unbounded and privately randomized deviations.

The first prefix creates debt in all three initially debt-free coordinates. It is not a coordinatewise-monotone repair. The total-debt ledger is essential.

## 9. Boundary check: why the exact-limit theorem needs its sign condition

For 0<delta<1, consider the two-player zero-sum table, displayed as player 0's reward:

    r_0({0})=1,    r_0({1})=1-delta,    r_0({0,1})=-1,
    r_1=-r_0,     Never=0.

Here s=(1,delta-1), and every payoff satisfies

    min_i(U_i-s_i)<=-delta/2.

Thus the finite geometric producer applies, but there is no exact terminal Nash equilibrium.

To verify this last claim, player 1's stationary hazard delta/2 makes every response of player 0 pay exactly V=1-delta. If player 0 uses constant positive hazard p, every player-1 response has payoff at most -V+(2-delta)p. Hence the value is V.

At an exact equilibrium let p_t be player 0's mass at date t, and S_t=Pr(T_0>=t), including Never. Player 1's pure Quit-at-t payoff is

    -1+delta S_t+(2-delta)p_t.

It must be at most -V=-1+delta. At t=0 this forces p_0=0; induction forces every p_t=0. Player 0 must therefore play Never, but then player 1 can also play Never and receive 0>-V, a contradiction.

This is not a UE counterexample. It confirms that passing only finite-deviation inequalities to a limit would be invalid for signed singletons. The nonnegative term in (19) is a substantive hypothesis, not a dispensable technicality.

## 10. Provenance and remaining arbitrary-Fin4 obstruction

Repository read-only reference: `elazarg/UniformEquilibrium` at
`88709a1034da3738fcb35ca10fc2cea45bad808d`, verified on 6 September 2026.

Relevant sources read directly:

- `AGENTS.md` and `docs/FRONTIER.md`;
- `UniformEquilibrium/Quitting/Terminal/AuxiliaryNashDebt.lean`, particularly `quittingTerminalSemanticDebt_prefix_le_auxiliaryNash`;
- `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticAuxiliaryNashBudget.lean`, particularly `minimumTerminalSemantic_singletonMargin`;
- `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticDebtHomotopySelection.lean`;
- `UniformEquilibrium/Quitting/Terminal/PivotRepairBehavioralInfimum.lean`;
- `Research/Quitting/EscapeAwareQuantileClockHierarchy.lean`.

The attached `TWO_PAIR_PAYOFF_EXCLUSION_AND_GEOMETRIC_FINITE_MENU_SELECTION(1).md` supplies the independent-clock payoff exclusion, its kappa=3/8 specialization, and the original rational fixture. Their proofs were read; the strict bound is also reconstructed above. The pair-clock inequality and the original exact auxiliary-prefix budget are not claimed as new.

No source was committed or modified in the repository, no branch or PR was created, and no Lean build or theorem-level axiom audit was run. The included Python checker ran successfully with exact Fraction arithmetic.

For arbitrary Fin4, neither (PD) nor (GE) has been established. At a hypothetical positive minimum, the existing margin theorem gives

    B_i-s_i >= D_*    for every i.

Then every scalar h<D_* leaves B-h*1 above the singleton vector, and the below-singleton forcing argument cannot start. In fact, the existing minimum auxiliary-Nash theorem says all these exact roots are all-Continue. This note does not eliminate that region, the supplied cap-installation collar, or the shifted-cap/negative-holonomy residuals.

The verified advance is a total-complete-debt chronological producer on the stated payoff-exclusion classes, and the stronger exact all-suffix conclusion under a strict deficit and nonnegative singletons. It is not an arbitrary-table proof or a counterexample.
