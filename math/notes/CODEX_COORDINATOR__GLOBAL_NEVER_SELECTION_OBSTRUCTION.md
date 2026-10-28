# Global observer-Never maximization can fail at every finite horizon

Ordinary mathematics; not checked in Lean. The complete proof has an
[independent review](../feedback/GLOBAL_NEVER_SELECTION_OBSTRUCTION__BY_REVIEW.md).
This is a counterexample to a global selection rule, not to Fin4.

For every singleton matrix satisfying the conditions below, and every fixed
continuous score uniquely maximized when all three observers choose Never,
there is a reward completion such that EVERY global score maximizer among
approximate finite-menu Nash profiles has full regret greater than1/2,
at every horizon and every sufficiently small menu error. The singleton
matrix stays fixed, and failure persists on an open set of higher rewards.
The rational control below also has an explicit absorbing Nash equilibrium.

## Data and the sixty rewards

Fix a real zero-diagonal invertible 4 by 4 matrix Gamma, a pivot p, and

    v = inverse(Gamma) e_p > 0.

Assume Gamma[j,p] = -c < 0 for one observer j. Let O be the three observers.
Choose a > 0 with a < 1 and a v_i < 1 for all four players. For independent
Bernoulli observer coins with probabilities a v_i, put

    Dstar = product_(i in O)(1-a v_i), A = 1-Dstar,
    P2 = probability(at least two observer coins succeed),
    H = (2-A-a)/P2 > 0, d = Dstar/A > 0.

All denominators are positive. For every nonempty observer subset D define

    V(D) = 1 + sum_(l in D) Gamma[p,l] + H 1_(|D|>=2).

Define every nonempty-coalition reward by:

    r_p({p}) = 1;
    r_p(D) = V(D)                      if empty != D subset O;
    r_p({p} union D) = V(D)-d          if empty != D subset O;
    r_i(S) = 0                        if i in S, i in O;
    r_i(S) = sum_(l in S) Gamma[i,l]   if i notin S, i in O.

Literal AllNever and live play pay zero. Own singleton rewards are
(s_p,s_O)=(1,0,0,0). The singleton difference matrix is EXACTLY Gamma:

    r_i({l}) - s_i = Gamma[i,l]        for i != l.

The H bonus never changes singleton rewards. If Gamma and a are rational,
the entire reward table is rational.

## Exact high-Never menu equilibrium at every horizon

For the menu F_N={0,...,N-1,Never}, N>=1, all players continue before N-1.
At N-1 player i quits independently with probability a v_i, else Never.

An observer's final Quit payoff is zero. Its final Never payoff is

    sum_(l != i) Gamma[i,l] a v_l = a (Gamma v)_i = 0.

Earlier solitary quit also pays zero. Thus all observer responses in the
menu have payoff zero. The pivot's Never payoff is

    W_p = A + a sum_(l in O) Gamma[p,l] v_l + H P2
        = A + a + H P2 = 2.

Its final Quit payoff is Dstar + W_p - d A = 2. Earlier solitary quit pays1.
Hence this is an exact menu Nash law, with every observer Never probability
n_i=1-a v_i. Its full omitted-response gain is Dstar, since quitting after
the entire menu pays W_p+Dstar while U_p=W_p.

The positive H bonus prices the earlier pivot responses as well as the
last-date indifference; without it W_p=A+a<1 for small a.

## A uniform full-response bound on every approximate menu equilibrium

For any independent product law on F_N write

    n_i = probability(player i chooses Never), D=product_(i in O)n_i,
    f_p=1-n_p, U_i=prescribed payoff, W_p=pivot Never payoff,
    L_p=W_p+D-U_p.

Let M be the maximum of zero and every subset sum of the j-th Gamma row
over players other than j. Let

    K = max(0, max_(empty != S subset O)(-sum_(l in S) Gamma[p,l])),
    C = M/c + K.

These constants depend only on Gamma, and not on a, H, d or N.

If the law is epsilon-Nash for the menu, observer j can quit at date0 for
zero, so U_j>=-epsilon. On the event that p is finite and every observer is
Never, the j-payoff is -c. On its complement, positive j-payoff requires
some observer to be finite and is at most M. Independence therefore gives

    U_j <= -c f_p D + M(1-D),
    f_p D <= (M/c)(1-D) + epsilon/c.                 (1)

Compare the pivot's prescribed pure clock with Never, holding its opponent
clocks fixed. If all observers Never, finite pivot quit gains1. Otherwise,
let S be the first observer coalition. Quitting before it gains 1-V(S)<=K,
joining it gains -d<0, and quitting after it changes nothing. The positive
H bonus can only decrease the first gain. Averaging gives

    U_p-W_p <= f_p D + K(1-D).

Combining with (1), every approximate menu equilibrium satisfies

    L_p >= (1+C)D-C-epsilon/c.                       (2)

The full behavioral exploitability equals max(menu exploitability,L_p):
all omitted observer finite dates equal Never, while all omitted pivot
finite dates pay W_p+D. Thus (2) bounds an actual available deviation.

## Every global max-Never selector fails, with Gamma held fixed

The set M_N(epsilon) of all epsilon-menu Nash laws is nonempty and compact.
It contains the exact high-Never comparison above. Put S=sum_(i in O)v_i.

Every global maximizer of sum_(i in O)n_i therefore has sum(1-n_i)<=aS,
and D>=1-aS. Consequently

    L_p >= 1-(1+C)aS-epsilon/c.                      (3)

Every global maximizer of D, equivalently of sum log n_i, satisfies

    L_p >= (1+C)Dstar-C-epsilon/c.                   (4)

For sufficiently small fixed a both floors remain positive as epsilon->0,
uniformly at EVERY horizon N.

More generally fix any continuous Phi:[0,1]^3->R whose unique global
maximum is at (1,1,1). Choose delta=1/(4(1+C)). The compact set
{n: product n_i<=1-delta} has strictly smaller maximum Phi. For sufficiently
small a, Phi((1-a v_i)_(i in O)) exceeds that maximum. Every global Phi
maximizer over every M_N(epsilon) has D>1-delta, hence

    L_p > 3/4-epsilon/c.                            (5)

The same statements hold over any smaller candidate set containing the
displayed exact equilibrium, conditional on a maximizer existing. In
particular one may jointly optimize over bounded action-payoff perturbations
and their Nash laws if zero perturbation is allowed and original menu regret
is bounded by epsilon.

This is a failure of global selection even on completions preserving any
fixed matrix Gamma satisfying the displayed assumptions. It is not a no-UE
construction, and does not prove any new class admits UE. Minimizing D and
minimizing actual full exploitability remain entirely unrefuted.

## Robustness with the singleton rewards fixed

Fix Gamma and the continuous score Phi as above. The obstruction holds on a
nonempty open set of all44 higher-coalition coordinates, with all sixteen
singleton rewards fixed.

First choose a in the construction above so the high-Never comparison beats
Phi on {D<=1-delta} strictly, with delta chosen using slightly enlarged
uniform constants Mbar and Kbar in place of M and K (for example Mbar=M+1,
Kbar=K+1). At the original last-date interior root q=av, the four mixing
indifference equations have nonsingular Jacobian: the three observer rows
are Gamma's observer rows and have common kernel span(v); the pivot row
is zero at p and strictly negative at every observer, so its product with
v is negative.

Now add eta>0 to every observer's participating reward in coalitions of
size at least two, leaving every other reward fixed. The observer mixing
equations become

    sum_l Gamma[i,l] q_l - eta(1-product_(l != i)(1-q_l)) = 0,

and the pivot equation stays D(q_O)-d(1-D(q_O))=0. The implicit function
theorem gives an interior root q(eta) near av for all sufficiently small
eta. Each observer's common final-date payoff is

    eta(1-product_(l != i)(1-q_l(eta))) > 0,

while the pivot's common final-date payoff stays near2. Every earlier
solitary response pays the fixed own singleton, zero or1 respectively,
so this profile is an exact menu equilibrium at every horizon. Its Phi
value still strictly beats the excluded compact set by continuity.

At one fixed sufficiently small eta>0, take a sufficiently small open ball
in all44 higher-coalition coordinates. Nonsingularity, the interior root,
strict final-value margins over earlier solitary responses, and the strict
Phi comparison persist. All observer participating rewards in coalitions
of size at least two stay positive, while each own singleton stays zero.
Thus every observer can quit at date0 for a nonnegative payoff. The pivot
joining penalty r_p(S union {p})-r_p(S) stays strictly negative for every
nonempty observer S, and its preemption gain stays at most Kbar. Every
reward of the selected negative-column observer stays at most Mbar off
the pivot-alone event. Hence the universal proof above remains valid,

    L_p >= (1+Cbar)D-Cbar-epsilon/c,
    Cbar=Mbar/c+Kbar,

uniformly throughout that neighborhood. Choosing delta=1/[4(1+Cbar)]
therefore makes every global Phi maximizer have L_p>3/4-epsilon/c at
every horizon. The same conclusion applies to sum and product scores.
This open-completion statement adds robustness, not a new solved UE class.

## Exact residual-matrix control and absorbing escape

Use the residual matrix audited in Section6 of the
[chronological exclusion theorem](../exports/CHRONOLOGICAL_TWO_OWNER_TAIL_EXCLUSION.md):

    Gamma=[0,1,4,-5; 1,0,-2,-1; -1,1,0,3; 2,-1,-4,0],
    p=0, v=(1,2/5,2/5,1/5), a=1/100.

Its determinant is10; every column has a negative entry; the inverse's
column0 is positive, every inverse entry is nonzero, and pair13 is mutually
negative. The cited existing audit verifies the remaining native matrix
conditions. The new completion changes no singleton entry.

For the construction above, exact rational
arithmetic gives

    Dstar=30938499/31250000,
    P2=499/15625000,
    H=61875999/998,
    d=30938499/311501.

Choose observer j=2, so c=1, M=4, K=5 and C=9. Every epsilon-menu Nash law
satisfies L0>=10D-9-epsilon. Every global observer-Never sum maximizer has

    L0>=9/10-epsilon,

and every global observer-Never product maximizer has

    L0>=2813499/3125000-epsilon.

These bounds hold at every finite horizon.

Nevertheless coalition{1,3} quitting surely at date0, with0 and2 Never,
is an exact absorbing equilibrium. Owners1 and3 each get0; waiting instead
gives-1 and every later response is equivalent. Observer2 gets4 by waiting
and0 by joining. Pivot0 gets V({1,3})=H-3 by waiting and H-3-d by joining.
All comparisons are strict at date0. Thus this control is an actual failure
of the selector, with full equilibrium available and matrix obstructions
unchanged. Its absorbing equilibrium persists under sufficiently small
higher-coalition reward perturbations, including the eta repair above.

## Source correspondence and remaining task

The existing declarations singlePivot_pivot_fullCap_eq_max_menu_never_add_deletedNever
and singlePivot_fullExploitability_eq_max_menuExploitability_scalar in
UniformEquilibrium/Quitting/Terminal/SinglePivotFiniteMenuSource.lean give
the full-response identity used here. The proof above also derives it directly.
No Lean implementation of the new matrix-preserving counterexample is claimed.

The conclusion concerns the actual selected profiles' full regret, even when
menu errors vanish and horizons grow. It is stronger than failure to force
an auxiliary Never product to zero. It does not refute minimizing that product,
minimizing full exploitability, or global selection rules whose objective is
not maximized at the all-Never observer vector. A successful selector still
has to control the full late-response term on its own selected profile.
