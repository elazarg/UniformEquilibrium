# Availability homotopy: actual full-objective improvement and its boundary

Author: CODEX_NOETHER_SUPPORT.

Status: bounded ordinary-mathematics test, not an export or a general
selector. On the canonical H table, an explicitly identified LOCAL
constrained-equilibrium component through a genuine finite global auxiliary
minimum lowers ORIGINAL full exploitability. A separate global comparison
retains H's already known good branch at vanishing availability. No global
component-continuation theorem or new equilibrium class is claimed.

## 1. The actual optimization problem

For canonical Fin4 rewards, zero Never, and independent stopping laws,
extend F_N={0,...,N−1,Never} by the new date N. For α∈[0,1], restrict
each player's mixed law by

    p_i(N)≤α.

Keep the original terminal rewards and only private planned-Never bonuses
ξ∈[0,δ]^4. For this paragraph, equilibrium means exact Nash under those
mixed-strategy availability constraints. The individual domains are compact
convex polytopes and own payoffs are affine, so constrained Nash laws exist.
For fixed N,δ,α the union over the compact bonus box is closed and compact.
Define C_(N,δ)(α) to be its minimum ORIGINAL full exploitability E, with
every unrestricted behavioral response retained in the evaluator.

At α=0 this is A(N,δ); at α=1 it is A(N+1,δ). For intermediate α, the
selected laws are actual finite clocks but need not be unconstrained
auxiliary Nash. Global optimality over the exact auxiliary family therefore
does not lower-bound their full E. No action reward is changed in this
homotopy; only the synthesis feasible sets are restricted.

## 2. An explicitly identified component through the global source

Use the complete canonical H table, restated in the
[normalized-source test](CODEX_NOETHER_SUPPORT__NORMALIZED_SOURCE_BLOCK_LOCK_ON_H.md):

    r_0(S)=1+1_(2∈S) if 0∈S; otherwise 3·1_(2∈S);
    r_i(S)=1_(i−1∈S) if i∈S; otherwise 3·1_(i−1∈S)−1,
                                                     i=1,2;
    r_3(S)=0 if 3∈S; otherwise 1.

Take N=1 and δ=0. Its unique finite Nash law has active date-zero masses
(1/3,1/4,1/2), each otherwise Never, with player 3 Never. It is therefore
the actual global A(1,0) minimizer. Its original full E is 3/8. Uniqueness
and complete caps are the H calculation credited in the linked note; this
is not a selected nonglobal branch at this source.

For small α>0, prescribe each active player i a date-zero mass a_i(α),
a date-one mass α, and Never mass z_i(α)=1−a_i(α)−α. Player 3 remains
Never. Impose equality of the date-zero and Never payoffs for each active
player. Direct first-stopping-time evaluation gives exactly

    1−2a_2−3α(1−a_1)=0,
    a_2−a_0(1+a_2)−α(1+a_0−2a_2+α)=0,
    a_0−a_1(1+a_0)−α(1+a_1−2a_0+α)=0.                (1)

At α=0 their solution is a*=(1/3,1/4,1/2). The Jacobian with respect
to (a_0,a_1,a_2), evaluated at this solution, is

    J = [ 0       0       −2  ]
        [ −3/2    0        2/3]
        [ 3/4    −4/3      0  ],       det J=−4.

Thus the ordinary implicit function theorem supplies one smooth local
branch a(α) through THIS source. Positivity of all old finite and Never
masses persists for sufficiently small α. Differentiating (1) gives

    a'_0(0)=−13/18,   a'_1(0)=−27/32,   a'_2(0)=−9/8. (2)

This verifies local regularity of the actual reduced equations, rather
than assuming generic regularity of the structured timing game.

Let W_i be Never payoff and ℓ_i be date-one payoff minus W_i. The exact
new-action comparisons are

    ℓ_1=α(a_2−a_0−α),
    ℓ_2=α(a_0−a_1−α),
    ℓ_0=z_1z_2−α(a_2−a_1)−α².                        (3)

At zero, ℓ_0=3/8; the right derivatives of ℓ_1 and ℓ_2 are 1/6 and
1/12. Hence for every sufficiently small positive α all three ℓ_i are
positive. Each player strictly prefers the new action but uses its full
allowed mass α; on the remaining mass, date zero and Never tie by (1).
These verify ALL constrained best responses. Player 3 optimally chooses
Never, since joining an absorbing coalition replaces reward one by zero.
Thus the implicit branch consists of actual constrained Nash profiles.

Only local existence for 0≤α<α_* is proved. This does not assert that
the component reaches α=1, or that any arbitrary chosen equilibrium can
be continued by the same argument.

## 3. The full objective really decreases on this component

Retain the genuinely new COMPLETE tester date two. Its pivot payoff minus
date-one payoff is

    α(a_2−a_1)+α²>0

for small α>0. Thus the pivot's full cap is W_0+D_0, where D_0=z_1z_2;
its prescribed payoff is W_0+αℓ_0. The two nonpivot caps are their
date-one payoffs: later finite dates have the same payoff as Never since
their singleton rewards are zero. Therefore the exact debts are

    d_0=D_0−αℓ_0,
    d_1=(1−α)ℓ_1,
    d_2=(1−α)ℓ_2,
    d_3=0.                                             (4)

At zero, d_0=3/8 while all other debts vanish. The pivot remains the
unique maximum debtor for small α. From (2),

    z'_1(0)=−5/32,   z'_2(0)=1/8,
    D'_0(0)=(1/2)(−5/32)+(3/4)(1/8)=1/64.

Consequently

    E'(0+)=d'_0(0+)=1/64−3/8=−23/64<0.                (5)

This is strict improvement of the actual FULL maximum regret, not only
two marked gains or a menu-only objective. It follows that
C_(1,0)(α)<A(1,0)=3/8 for sufficiently small positive α. No assertion
that this local branch itself globally minimizes C is needed: it is an
actual admissible comparison for that global objective.

The branch is not unconstrained auxiliary Nash. Its newly admitted
pivot action has a substantial unpaid gain while its mass is capped.
In fact its original menu regret tends to 3/8 as α↓0. Hence (5) alone
is not a vanishing-menu-error selector or a renewable zero-limit descent.
At α=1, H's exact two-date zero-bonus Nash law is the delayed original
law and again has full error 3/8. This endpoint fact does not prove that
the locally identified component reaches it.

## 4. Global availability selection also retains the known good branch

HILBERT's
[active-Never-bonus construction](CODEX_HILBERT__ADAPTIVE_NEVER_BONUS_PORTFOLIO_ON_H.md)
provides the independent comparison here; no component ancestry is assumed.
For K≥1 it has last date T=3K, owners i=t modulo three, and hazards

    h_t=2^(T−t)/(2^(T−t+1)−1),        0≤t≤T.

Its only bonus is ξ_2=δ_K=A_0 A_1<4^(−K), where A_i is player i's
survival through its dates before T. Its ORIGINAL payoffs and full caps are

    U=(1,1+e_K,−e_K,1),   B=(1,1+e_K,0,1),
    e_K=1/(2^(3K+1)−1).

The full response proof in that source was read; these are ordinary
mathematical construction inputs, not newly formalized declarations.

Set N=T and expose its final date as the availability-limited new date.
Only the pivot has a positive mass there, namely

    α_K=A_0=∏_(m=1..K)(2^(3m)−1)/(2^(3m+1)−1)<2^(−K).

The good law is already unconstrained auxiliary Nash and is feasible under
availability α_K. It is therefore constrained Nash as well. It follows
directly, for the ACTUAL global constrained objective, that

    C_(3K,δ_K)(α_K)≤e_K→0.                            (6)

Every global minimizer on the left succeeds in original full regret, hence
also in original menu regret. Given a global A(3K,δ_K) source, either
its error is already ≤e_K or (6) supplies a strictly better actual law at
the new availability. The selected comparison need not lie on the component
of that particular source. Global selection can use it without a component
survival assertion. This is a test using an already proved H branch, not a
new table class or a table-free producer of such branches.

## 5. What this test adds and where it stops

The local calculation (1)–(5) establishes actual full-objective orientation
on one explicitly identified component through a genuine finite global
source. It verifies the required structured Jacobian and the added tester.
Existence of SOME strict actual-law descent at a unique maximum debtor was
already available by whole-law best-response repair; the extra point here
is membership in the explicitly checked constrained-equilibrium component.
The global comparison (6) shows that vanishing availability does not mean
small change of the old laws: the good source reorganizes the earlier
calendar and changes its continuation. It respects the earlier literal
appended-menu separation result rather than contradicting it.

The [installation ledger](CODEX_NOETHER_SUPPORT__LATE_ROW_INSTALLATION_AND_COLLAPSED_BONUS_BUDGET.md)
separates the H-specific payoff benefit from the collapsed-source cost.
In particular the required collapsed bonuses leave the SAME zero bonus
box, so A(1,0)-minimality must not be applied to that collapsed law.

Neither part supplies the missing arbitrary-table implication. Existence of
some connected equilibrium continuation does not say that the selected
source belongs to it, nor orient its actual full-regret values. No generic
component theorem, index argument, or new homotopy consumer is inferred.
The concrete H test is complete at this boundary; the next useful question
is a nonlocal all-law comparison that does not require a known good branch.
