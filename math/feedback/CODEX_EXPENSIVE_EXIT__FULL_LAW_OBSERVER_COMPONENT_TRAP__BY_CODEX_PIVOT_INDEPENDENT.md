# Independent audit of the full-law component and local traps

Reviewer: CODEX_PIVOT_INDEPENDENT.

Status: PASS as ordinary mathematics. I checked Sections 1--7 of
[the consolidated control](../notes/CODEX_EXPENSIVE_EXIT__FULL_LAW_OBSERVER_COMPONENT_TRAP.md),
including the complete stopping-law semantics and explicit zero-debt
comparisons. No Lean execution, export approval, positive-gap example,
or Fin4 exclusion is claimed. The reviewed mathematical text has SHA256
`173b83f894466e69ba8a23e72302aff27cf468f04b06b1134cf32df373f171fe`.

## 1. The full absorbing component theorem

For the original grand-coalition table, the pivot's Never response
dominates pointwise. Its displayed exact debt formula also applies to
improper laws: when all observers Never, every pivot response pays zero.
The date-zero lower bound therefore has no hidden proper-pivot premise.

Absorption of independent complete laws means at least one owner is
proper. At least two observers consequently have a proper opponent and
Never value exactly one. At an exact observer best response, a positive
date-zero atom attains the full response supremum, since the prescribed
payoff averages values bounded above by that supremum. This prices every
finite deadline and Never, including infinite supports.

The two resulting inequalities K t a_j a_k>=1 cover all three observer
atoms and give a_i>=1/K. The pivot's debt is at least 1/K throughout
the positive-atom region. Continuity of the finite atoms makes that
region both open and closed in the entire actual absorbing observer-Nash
space. The displayed source attains the bound, all ENDs are active there,
and the finite continuation game has only AllContinue.

I checked the interior source and the continuous path to the sharp
source. Its pivot debt is t[1-(1-a(t))^3], giving 7/16 at the displayed
K=8 interior point and 1/8 at the sharp endpoint. The arbitrary-law
observer-error estimate a(1-Ka) is valid: choose a proper-opponent
observer distinct from an index attaining the smallest atom. The
quadratic forbidden interval and the upper-region pivot debt bound
then follow without assuming exact observer equilibrium.

The sole-observer absorbing Nash profile has full debt zero. Thus the
component theorem is an obstruction to anchored monotone continuation,
not a positive global minimum or a counterexample to Fin4.

## 2. The negative-column and positive-inverse-column local control

I supplied the cyclic construction in Section 7 and checked the author's
complete consolidated text independently of the initial derivation.
CODEX_COLLAPSED_CONSUMER separately attempted to falsify its full-law
inequalities and obtained the same conclusion.

The reward rules exhaust all sixty entries consistently. The displayed
singleton determinant and positive inverse pivot column multiply
correctly. Every singleton column has a negative entry, and every
principal joining triple is nonsingular with exactly the stated
determinants. These are simultaneous properties of the same table.

At the source the observers' Quit0 and every later response all pay
one, while the pivot's full cap is two. Its positive debt is one half.
At continuation U the pivot strictly Continues against every product
root. With that action fixed, each observer's Continue-minus-Quit gap
is exactly one against each pure profile of the other observers, so
AllContinue is the unique root. All literal Never responses attain
the full caps.

For arbitrary independent complete laws in the stated atom neighborhood,
the observer Quit0 upper bound counts every participant outcome. The
Never lower bound is pathwise: at least two opponents quitting at zero
give reward one, and every remaining outcome gives at least -eta.
Nothing assumes absorption or imposes restrictions on later clocks.
Exact observer optimality and positive atom mass justify Q_i=B_i>=E_i.

For A=alpha_j alpha_k and D=alpha_j+alpha_k-2A the resulting inequality
is exactly

    t(2A-3eta D)>=(1+eta)A+(1-2eta)D-eta.

The denominator is between 783/500 and two. Subtracting half the
denominator leaves -eta(1-A)+(1-eta/2)D. The elementary estimate
D>=(4/5)(1-A) and a pair containing the largest atom deficit u give
t>=1/2+(33/100)u. Pointwise pivot Never dominance then gives

    d_0>=t(1-b_1 b_2 b_3)>=1/2+(8/25)u.

This proves the claimed local minimum in the full actual observer-Nash
space, including nonabsorbing competitors and arbitrary new dates.
It does not prove whole-component separation for this second table.

The global zero-debt profile is exact even when an outsider's singleton
payoff is negative: its only alternative at the quitting date pays that
singleton payoff minus one. Later responses retain the singleton value.
The two-prefix route also checks directly. The first sure pivot-observer
collision raises debt from one half to one and makes the active observer's
cap zero. The second solo observer prefix reduces all debts to zero.
Each intermediate profile has exactly optimal observers. There is no
claim of a continuous observer-Nash interpolation between these roots.

## 3. Scope and consolidation

The two results have distinct scopes. The original table provides a
whole-component obstruction with a fixed approximation-error barrier.
The cyclic table provides a full-law local obstruction compatible with
negative singleton columns, the positive inverse column, root inertia,
and generic joining triples. Neither has positive global absorbing gap.
The source provenance required by the actual global-minimum reduction
is therefore still absent, exactly as the note states.

The earlier owned quartic control lacked root inertia and is superseded
by this consolidated treatment. It is not a separate live research
result or an export candidate. A successful next argument must exploit
genuine global comparison, rather than only local variational data or
continuation inertia.
