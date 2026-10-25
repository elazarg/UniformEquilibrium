# Strict observer Never margins do not give local debt descent

Owner: CODEX_LAST_DATE.

**Complete ordinary-mathematical control.** Independent review is recorded
in the [canonical feedback](../feedback/CODEX_LAST_DATE__STRICT_NEVER_FULL_LAW_LOCAL_MINIMUM__BY_CODEX_UNIFORM_CORE_REVIEW.md).
This is an obstruction to a local proof step, not a global minimum,
counterexample to Fin4, new equilibrium class, export or Lean result.

An absorbing two-date profile can have all three observers strictly above
their Never offers and still locally minimize positive pivot debt among
profiles preserving exact observer optimality, under arbitrary changes of
ALL four complete stopping laws. The obstruction
persists on an open set of native tables. Thus exact finite-calendar
representation and strict Never margins do not supply local debt descent;
the genuine global-minimum hypothesis must do further work.

## 1. Complete table and literal law model

Players are I={0,1,2,3}, pivot0 and observers S={1,2,3}. Private stopping
laws on Nat plus Never are independent. The first finite quitting coalition
A pays Z(A). Own singletons, live play and AllNever pay zero. Deviations
replace the complete private law. Set a=1/10 and c=7/17.

The pivot row is

    Z0(A)=1                         if 0 is absent,
          0                         if A={0},
          1                         if 0 is present and 2<=|A|<=3,
          1-c=10/17                 if A=I.

For each observer i, let j be its next and k its previous observer in the
cycle1->2->3->1. On coalitions not containing0, put

    Zi({i})=0,  Zi({j})=1,  Zi({k})=-9/10,
    Zi({i,j})=19/10,  Zi({i,k})=-1,
    Zi({j,k})=-4/5,   Zi(S)=1/10.

On coalitions containing0 but not i, put

    Zi({0})=-1/10 for every observer i,
    Zi({0} union A)=1 for nonempty A contained in {j,k}.

For each A contained in {j,k}, complete the row by

    Zi({0,i} union A)=Zi({0} union A)+1_(j in A)-11/10.       (1)

These disjoint rules assign all sixty entries, with absolute values at
most21/10. Write U for prescribed payoffs, B for the full response caps,
e for literal Never offers and d=B-U.

## 2. The exact source and all response offers

Each observer chooses date0 or date1 with probability1/2 each. The pivot
chooses date0 with probability2/5 and Never with probability3/5. Every
observer is proper, and the profile absorbs by date1. Direct enumeration
gives the complete pure-response offers:

| Owner | Date0 | Date1 | Every date>=2 and Never |
| --- | --- | --- | --- |
| 0 | 14/17 | 129/136 | 1 |
| 1 | 1/5 | 1/5 | 13/200 |
| 2 | 1/5 | 1/5 | 13/200 |
| 3 | 1/5 | 1/5 | 13/200 |

Every later deadline is outcome-equivalent to Never: its owner faces
another observer quitting by date1. Affinity prices every randomized or
infinite complete response. Consequently

    U=(79/85,1/5,1/5,1/5),
    B=(1,1/5,1/5,1/5), d=(6/85,0,0,0),
    B_i-e_i=27/200 for every observer i.                    (2)

All payoffs are positive. Every observer mixes two maximizing dates and
strictly rejects Never and every later date.

## 3. Local exact-observer profiles really have only two dates

Consider a sufficiently small total-variation neighborhood of the four
source laws, allowing arbitrary finite or infinite supports and Never.
Every observer still has positive atoms at0 and1. Each pure response offer
changes uniformly by at most2M times the sum of the opponents' variation
distances, using independent maximal couplings and |Z|<=M. Thus the strict
gap in(2) ensures that every date>=2 and Never is still strictly below a
date0 offer. Exact observer optimality forces its entire law onto{0,1}.

This conclusion does not assume finite support in the varied profiles.
Every nearby exact-observer profile therefore absorbs by date1. Its pivot
law after date1 is outcome-equivalent to Never for all payoffs and all
response offers, because each possible deviator faces a bounded observer
clock. Let

    q_i=Pr(T_i=0), t=Pr(T_0=0),
    x=Pr(T_0=1)/(1-t)>=0.

Near the source, t is near2/5 and q_i near1/2. All remaining pivot mass can
be left arbitrary after date1 or at Never. It has no strategic effect here.

Exact observer optimality is now equivalent to its used date0/date1
indifference, together with the automatically preserved strict late gap.
The differences of those two offers, calculated from(1), are

    F_i=q_j-t-a-(4/5)(1-t)x(1-q_j)(1-q_k).                  (3)

At x=0 the Jacobian of(F_1,F_2,F_3) in(q_1,q_2,q_3) is a cyclic
permutation matrix. The implicit-function theorem gives a unique smooth
solution near the source for each(t,x). Cyclic symmetry of(3) makes it
q_1=q_2=q_3=q(t,x), where

    q-t-a-(4/5)(1-t)x(1-q)^2=0,
    q(t,0)=t+a, q_x(t,0)=(4/5)(1-t)(1-t-a)^2.              (4)

Thus(4) describes EVERY nearby full-law exact-observer profile, modulo the
irrelevant pivot tail. It is not merely a convenient subfamily.

## 4. A positive full-law local minimum

The pivot receives1 whenever absent and at most1 whenever present.
Since the observers are proper, Never attains its full cap1. Define

    C(q)=(1-q)^3+c q^3.

Its exact debt at the local profiles(4) is

    D(t,x)=t C(q(t,x))+(1-t)x c(1-q(t,x))^3.               (5)

The first term prices date0: loss1 if no observer stops, loss c if all
three stop, and zero otherwise. The second term prices a pivot stop at
date1 when all three observers waited. This accounts for the entire law.

At(t,x)=(2/5,0), equations(4)--(5) give

    D=6/85, D_t=0, D_tt=69/85>0, D_x=33/3400>0.           (6)

For explicit checks, at q=1/2 one has C=3/17, C'=-15/34,
C''=72/17 and q_x=3/25. Hence D_t=C+t C'=0,
D_tt=2C'+t C''=69/85, and

    D_x=t C' q_x+(1-t)c(1-q)^3=33/3400.

By continuity, D_x stays positive near the source. For x>=0 sufficiently
small, D(t,x)>=D(t,0), strictly when x>0. The positive second derivative
gives a strict minimum of D(t,0) at t=2/5. Therefore the source is a local
minimum of pivot debt over ALL actual absorbing exact-observer profiles.
It is strict in the effective variables(t,x); changing irrelevant pivot
tail dates can of course leave the semantic tuple unchanged.

## 5. Generic singleton screens and the global comparison

The singleton matrix is

    Gamma=[0,1,1,1; -1/10,0,1,-9/10;
           -1/10,-9/10,0,1; -1/10,1,-9/10,0].

Each column contains a negative entry. In lexicographic subset order its
principal determinants of orders2,3,4 are respectively

    (1/10,1/10,1/10,9/10,9/10,9/10),
    (-1/100,-1/100,-1/100,271/1000), (813/1000).

Thus Gamma is R0: support of size>=2 in a nonzero homogeneous LCP vector
would contradict an invertible principal block, and singleton support is
excluded by the negative column entry. Its pivot inverse column is

    Gamma^-1 e0=(1/3,1/3,1/3,1/3)>>0.

The LCP with offset -1 has the unique solution x=(0,10,10,10),
w=(29,0,0,0). Indeed x0>0 would force sum_S x_i=1, whereas summing
the three inequalities Gamma_i x>=1 would give
1/10-3x0/10>=3, impossible. With x0=0, a proper nonempty core support
has an active owner whose next coordinate is zero, contradicting its
positive target. The full core then gives the displayed solution. Its
support determinant is positive and all inactive inequalities strict, so
the support-index formula gives complementarity degree1.

This is not a no-passive-child matrix: Gamma_S^-1 is strictly positive
and its exterior inverse row is(10,10,10). The control passes the R0,
positive determinant, degree and strict inverse-column screens, while
deliberately retaining a solved child. No stronger matrix exclusion is claimed.

The control is nevertheless NOT a global minimum. Let pivot0 Quit0 surely
and every observer choose Never. The payoff is(0,-1/10,-1/10,-1/10). An observer's
date0 offer is exactly11/10 below its Never offer by(1); every later date
equals Never. The pivot obtains its singleton zero from every finite
deadline and zero from Never. This is an absorbing full Nash profile.
In particular the global partial-Nash debt minimum is zero.

The local obstruction persists on an open neighborhood in the56-dimensional
own-zero slice. The observer Jacobian, strict late gap, positive payoffs,
two strict pivot cap gaps, D_tt>0 and the one-sided D_x>0 all persist.
First solve the perturbed observer equalities by IFT, then solve D_t(t,0)=0
by IFT. The resulting nearby two-date source remains a positive local
minimum. Its cap stays the Never offer: dates0 and1 are strictly lower,
and every later date equals Never. The displayed singleton screens and
the explicit pivot-only absorbing equilibrium also persist, using their
strict inequalities and nonzero determinants.

The older [component trap](CODEX_EXPENSIVE_EXIT__FULL_LAW_OBSERVER_COMPONENT_TRAP.md)
has Never-active observers at its local minimum. This control keeps ALL
three Never margins strict and all observer laws proper. It makes no
claim that the whole observer-Nash component is trapped or that the root
game at U is inert. Both stronger hypotheses would need separate proofs.

The remaining question is global: can arbitrary-calendar comparisons exclude
a positive GLOBAL minimum with a finite-calendar realization? Equations
(3)--(6) show that a local variation theorem alone cannot do so.

Semantic declarations inspected were
`quittingContinuationBestResponseValue_rootThenContinuation_eq_max`
in `UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean` and
`quittingTerminalSemanticPair_rootThenContinuation`
in `UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`.
The complete source offers, polynomial(3), derivatives(6), singleton
determinants and displayed Nash comparison were checked by exact rational
enumeration and symbolic differentiation. The displayed formulas suffice
to reproduce those checks; no experiment script or Lean change is retained.
