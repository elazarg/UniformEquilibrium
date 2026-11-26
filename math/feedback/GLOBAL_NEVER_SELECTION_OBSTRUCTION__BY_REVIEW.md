# Independent review: singleton-preserving global Never selection obstruction

Reviewer: GLOBAL_SELECTION_REVIEW. Ordinary mathematics; no Lean command.

Final artifact reviewed:
`math/notes/CODEX_COORDINATOR__GLOBAL_NEVER_SELECTION_OBSTRUCTION.md`, SHA256
`423198968d45a39266bcec5a7ad7c1736c9053188fc644b3c30f7f2a749c92ec`.
This review covers the whole final artifact: the matrix-preserving construction,
the all-horizon actual-output bound, the open44-coordinate completion claim,
and the exact residual-matrix control with an absorbing equilibrium.

**Verdict: mathematical PASS.** No unresolved mathematical objection remains.
This is a counterexample to the stated global selector family. It is not a
positive-gap counterexample to Fin4 and supplies no new UE-class exclusion.

## Construction and exact menu source

For v=Gamma^-1 e_p>0, a<1 and av_i<1, the observer probabilities are strictly
between zero and one. Hence 0<Dstar<1, A>0 and P2>0. Since A<1 and a<1,
H=(2-A-a)/P2 is positive. The reward rule specifies all sixty cells. Its
own singleton vector is (1,0,0,0); subtracting that vector from each
singleton column gives exactly Gamma. The H correction affects no singleton.

I reconstructed the final-date equilibrium independently. An observer's
Never payoff is the expectation of an additive row, namely a(Gamma v)_i=0;
its Quit payoff and every earlier solitary response are also zero. The
pivot's Never value is A+a+H P2=2. Its final Quit value is
Dstar+2-dA=2, whereas an earlier solitary quit gives1. This prices the
entire menu for every N>=1, not only the final simultaneous move. Without
H the earlier pivot response can indeed invalidate the construction; the
final artifact explicitly supplies the correction.

The complete response identity is also correct. Every omitted observer
finite deadline is equivalent to Never because its own singleton is zero.
Every omitted pivot finite deadline pays W_p+D because its own singleton is
one. All complete behavioral replacements are mixtures of these stopping
responses. Thus the full exploitability is max(menu exploitability,L_p).

## Universal inequality and global selection

For the selected observer j with Gamma[j,p]=-c, date-zero quitting guarantees
zero in the unperturbed table. Any epsilon-menu Nash profile therefore has
U_j>=-epsilon. The event that p is finite and all observers Never has
probability f_p D and gives j exactly -c. Off that event, positive j-payoff
requires some observer to be finite and is bounded by the raw constant M.
The all-Never event pays zero. Consequently

    U_j<=-c f_p D+M(1-D),
    f_p D<=(M/c)(1-D)+epsilon/c.

This uses independent laws explicitly and covers arbitrary occupied dates
and ties. It is not a calculation restricted to the witness equilibrium.

The pivot comparison holds pointwise on pure opponent-clock realizations.
If some observer first quits in coalition S, pivot Never receives V(S).
Preempting changes this to1 and gains at most K; joining gains -d<0; waiting
changes nothing. The positive H term cannot increase the preemption gain.
If all observers Never, finite pivot quit gains1. Averaging gives
U_p-W_p<=f_pD+K(1-D), hence

    L_p>=(1+M/c+K)D-(M/c+K)-epsilon/c.

Both constants M and K are independent of a,H,d,N. This uniformity makes the
subsequent selection argument valid even though H grows as a decreases.

The feasible final-date source forces every sum maximizer to have total
observer finite mass at most a sum_O v_i. The product inequality D>=1-F
therefore proves the printed sum bound. Every product maximizer has product
at least Dstar>0, so the product bound and the sum-log equivalence follow.
For a fixed continuous score uniquely maximized at(1,1,1), compactness gives
strict score separation from D<=1-delta. A sufficiently small a supplies a
feasible score beating that entire set, uniformly over N and epsilon. This
proves the lower bound for EVERY global maximizer. Smaller candidate sets
inherit it if they contain that source and possess a maximizer; no existence
is incorrectly asserted for arbitrary noncompact subsets.

## Open completion audit

The regularity argument alone would not give an open family because the
unperturbed observer values tie their earlier solitary responses. The final
artifact addresses exactly that issue.

The observer indifference rows at q=av are Gamma's three observer rows.
Their common kernel is span(v). The pivot indifference equation is
(1+d)D(q_O)-d=0; its derivative is zero in its own coordinate and strictly
negative in every observer coordinate. Its scalar product with v is negative,
so the full four-equation Jacobian is nonsingular.

Adding eta to every observer participating reward at coalitions of size>=2
changes its indifference equation to

    sum_l Gamma[i,l]q_l-eta(1-product_(l!=i)(1-q_l))=0.

The implicit function theorem supplies an interior root for sufficiently
small eta>0. Each observer's common final value is strictly positive; the
pivot's stays above1. Hence all earlier-date response inequalities now have
strict margins, independent of the horizon. A further sufficiently small
open ball in all44 higher-coalition reward coordinates preserves the root,
these margins, and the strict score comparison.

The universal inequality is stable in the same ball. Observer participants
continue to receive nonnegative payoffs, so quitting at date0 still guarantees
at least zero. The pivot-alone observer payoff remains exactly -c because
singletons are fixed. All other observer rewards have a common upper bound
Mbar. The pivot joining penalties remain negative and its preemption gain is
bounded by Kbar. Choosing these enlarged constants before choosing a removes
any circular dependence. Thus the stated regret floor holds throughout a
nonempty open set of all44 free coordinates, for every finite horizon.

## Exact control and adversarial checks

I independently computed all sixty rewards and coin expectations in exact
rational arithmetic for the printed residual Gamma, v and a=1/100. The
results are

    det Gamma=10, Gamma v=e_0,
    Dstar=30938499/31250000, P2=499/15625000,
    H=61875999/998, d=30938499/311501,
    W=Q=(2,0,0,0), M=4, K=5,
    determinant of the indifference Jacobian=-310503000/311501.

The sum and product floors are respectively9/10-epsilon and
2813499/3125000-epsilon. I checked preservation of every singleton cell,
N=1, the earlier-date pivot comparison for larger N, arbitrary large errors
(where a floor may be vacuous), and positive product/log attainment.

For the absorbing pair{1,3}, the prescribed reward is(H-3,0,4,0).
Either participant waiting receives-1; observer2 joining receives0; the
pivot joining receivesH-3-d. Thus all date-zero action comparisons are
strict and all later responses are equivalent to waiting. This is full
terminal Nash, not only menu Nash. The strict inequalities persist under a
sufficiently small higher-reward perturbation, including the eta repair.

## Source and retained scope

I inspected `singlePivot_nonpivot_fullCap_eq_menuCap`,
`singlePivot_pivot_fullCap_eq_max_menu_never_add_deletedNever`, and
`singlePivot_fullExploitability_eq_max_menuExploitability_scalar` in
`UniformEquilibrium/Quitting/Terminal/SinglePivotFiniteMenuSource.lean`.
The new mathematics is not asserted to have a Lean implementation.

The prior bonus-box example only defeated the surrogate requirement that a
Never product tend to zero; its selected outputs were already equilibria.
This result proves positive actual full regret at every selected output,
allows vanishing menu errors and unbounded horizons, and preserves any
singleton matrix satisfying the stated hypotheses. The explicit solved
control makes clear why this is a selector obstruction rather than a game
counterexample. Minimizing deleted Never, actual late gain, or full regret
remains outside the theorem's scope.
