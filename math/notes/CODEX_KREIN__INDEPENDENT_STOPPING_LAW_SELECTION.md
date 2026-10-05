# Independent stopping-law selection

Identity: CODEX_KREIN. Ordinary mathematics, not Lean-checked. The positive
selected-family theorem has independent review and is recorded in
`../exports/NONNEGATIVE_SINGLETON_FINITE_QUIET_LIFTS.md`. The separate exact
response-selector obstruction remains an internal proof draft. The
canonical finite-menu selection question remains open.

The joint-phase construction and its independent positive-harm enlargement
have two independent mathematical PASS reviews, including full behavioral
deviations and every proper-child F/J falsifier. Their bare existence scope
is ALREADY covered by `exists_uniformEquilibriumPayoff_of_productLowPremium`:
every own-Quit endpoint equals the corresponding singleton. Their exact
periodic rates, selected target, and separation from all proper-child F/J
families remain useful internal results, not new UE-class coverage. No
existence export is proposed for that covered family.

The live beyond-product-low candidate is **Positive mutual premiums at the
prescribed joint phase** below. Both participants receive strictly positive
singleton-relative premiums at the positive-probability coalition {0,1}.
This changes the actual Bellman equations and robustly violates product-low.
That additional raw-family theorem has a first independent PASS in
`../feedback/CODEX_KREIN__INDEPENDENT_STOPPING_LAW_SELECTION__BY_CODEX_BROUWER.md`.
Its central section is frozen while the broader candidate is assessed.

The appended **Proposed generalization: select the pivot equation first**
has independent PASS reviews from CODEX_BROUWER and CODEX_MORSE, recorded
in their feedback files for this notebook. A different scalar selection removes
the bound on the mutual premium and covers independent collision harms,
unequal pivot passive singletons, and arbitrary unused passive rewards.
Its exact new raw-table criterion and endpoint proof are written below;
both reviewers checked that stronger statement independently.

The separate **Further producer: diffuse only the solo phases** weakens
the reward criterion to six outsider caps at the actual joint phase and
has independent PASS reviews from CODEX_BROUWER and CODEX_MORSE. It supplies approximate
profiles with one fixed target using existing singleton-refinement and
exact-Continue supersolution methods. The self-contained mathematical packet
is frozen in `../exports/ONE_JOINT_PHASE_WITH_DIFFUSE_SOLO_EXITS.md`.
Further research below does not modify or inherit the export's review.

The section **Quadratic nonpivot selection and the complete R axis** has
independent mathematical PASS reviews from CODEX_MORSE and CODEX_BROUWER.
It replaces the sign-restricted pivot selector by a unique admissible root
of a quadratic nonpivot equation. On the same six-cap raw class, this
produces the entire residual interval between the existing singleton-degree
and passive-inverse exits whenever u≤1+xi and v<1. Consequently that raw
class has UE for every real R. Under the shared two-core participation
conditions stated there, the separate strict-leave theorem supplies u>1+xi,
giving one whole (u,R) plane rather than a chosen curve or bounded interval.
The new constructive part, source exits, and remaining table restrictions
are separated explicitly below. The independently reviewed self-contained
packet is frozen in `../exports/CYCLIC_CHILD_WITH_ONE_JOINT_PHASE.md`,
promoted byte-for-byte by the coordinator. The later **positive-gap obstruction to the
one-joint/two-solo-block architecture** is a separate unreviewed candidate,
including arbitrary solo subdivision and the all-zero-hazard limit. Its
beta=0 table has UE, so it is not a game counterexample. The subsequent
**Switched joint pair: two passive rewards above the pivot singleton**
has independent PASS reviews from CODEX_MORSE and CODEX_BROUWER in their
corresponding feedback files. It chooses a different joint pair and uses an actual positive
outsider continuation buffer to tolerate positive joining rewards. Its
full-core completion fails even the signed common-leaver criterion.
The next question is whether a second positive outsider buffer can remove
the remaining three zero caps, without merely supplying a strategy verifier.

The positive result in **Zero-singleton child selection** below removes the
strictly-positive-child-singleton requirement from EXISTENCE under the
original finite F/J quiet-extension criteria: one nonnegative child
singleton suffices. It selects actual child laws with both vanishing full
regret and vanishing joint Never, then uses the ORIGINAL table's exact
residual bound. Thus it covers the canonical pivot-deletion face where all
three remaining own singletons are zero. The same selected laws supply
small pivot-repair values. It does not extend every separately prescribed
child target, and does not assert that every table satisfies the finite
F/J inequalities. Its existence class is also a closure consequence of
the existing strict-positive class; the theorem supplies selected finite
original laws with both vanishing regret and vanishing joint Never.

The separate all-selector obstruction below excludes minimum-value
selection over all uncompensated exact-nonpivot-response / optimal-pivot
fixed points. This is an architecture exclusion on an already solved
table, not a new game without equilibrium.

## Question and exact source boundary

Four players independently choose stopping laws on the nonnegative integers
and Never. The first nonempty quitting coalition S pays r(S); all Never
pays zero. Before termination the public history consists only of
all-Continue. A deviation replaces one complete behavioral strategy,
equivalently its independent stopping law. Write U_i for prescribed
terminal payoff, B_i for the supremum over all such replacements, and
E=max_i(B_i-U_i). All probabilities below are unconditional unless a
surviving suffix is explicitly specified.

The positive question is: for every bounded table with own singletons
(1,0,0,0) and every error e>0, choose three actual finite nonpivot laws
whose optimal unrestricted pivot-repair value is below e. The outer laws,
not the inner repair, are missing.

Declarations inspected through `docs/TOOLKIT.md`:

- `singlePivot_fullExploitability_eq_max_menuExploitability_scalar`, in
  `UniformEquilibrium/Quitting/Terminal/SinglePivotFiniteMenuSource.lean`;
- `exists_objective_minimizer_eq_behavioral_infimum`, in
  `UniformEquilibrium/Quitting/Terminal/PivotRepairBehavioralInfimum.lean`;
- `smallPivotRepairValue_iff_exists_uniformEquilibriumPayoff`, in
  `UniformEquilibrium/Quitting/Terminal/PivotRepairUniformPayoffCharacterization.lean`;
- `HasQuittingSmallPivotRepairValue` and
  `exists_pivotRepairMass_objective_le_finiteMenu_exploitability`, in
  `UniformEquilibrium/Quitting/Terminal/PivotRepairSmallValueSource.lean`;
- `QuittingPivotRepairLPInput` and its payoff/endpoint definitions, in
  `UniformEquilibrium/Quitting/Terminal/PivotRepairFiniteLP.lean`.

These sources identify a finite LP with the behavioral repair infimum and
consume small values; they do not select the opponent laws. Source files
were inspected, not rebuilt. No outside theorem or literature claim is
needed for the new argument.

## All exact nonpivot replies are uniformly bad on VANISH

Index 1,2,3 cyclically. Define every nonempty coalition reward by

    r_0(S)=1 if 0 belongs to S, and 2 otherwise;
    r_j(S)=0 if j belongs to S;
           -1 if j does not belong to S but 0 does;
           2*1_(pred(j) belongs to S)-1_(succ(j) belongs to S) otherwise.

Fix ANY pivot law, allowing unbounded support and Never. Fix N>=1 and
nonpivot laws supported on F_N={0,...,N-1,Never}. Suppose that all three
are simultaneous exact best replies among laws on F_N to these SAME
opponents and pivot. Then

    U_1=U_2=U_3=0,     p_1=p_2=p_3,     E>=1/512.             (1)

Thus the infimum over all deadlines and all coupled fixed points which
globally minimize the original repair value in the pivot coordinate and
maximize original finite-menu payoffs in the three other coordinates is
positive. The statement covers all such fixed points, not merely a
selected branch, and is stronger than needed because pivot optimality is
absent from its hypotheses.

### The elementary three-player row

Suppose the pivot quits now with conditional probability h, and if nobody
quits the three nonpivots' common continuation value is -c, 0<=c<=1.
Their Quit payoff is zero. For h<1, divide Continue payoff by 1-h and set
k=h/(1-h). The three Continue comparisons are

    f_j=2q_pred(j)-q_succ(j)
          -c(1-q_pred(j))(1-q_succ(j))-k.                (2)

There is exactly one Nash row. It is symmetric. If k>=1, all q_j=1.
If k<1, all q_j=q, where the unique q in [0,1) solves

    q-c(1-q)^2=k.                                      (3)

In every case every player's value is zero. At h=1 the unique row is
also all Quit, with value zero.

Here is the boundary argument, including sure actions. If q_1=0, then
f_2=-q_3-c(1-q_3)-k<=0. Strict inequality forces q_2=1. Player 1's
Continue condition then gives 2q_3-1>=k, so q_3>0. If q_3<1, its
indifference gives k=2, impossible in that inequality; if q_3=1 its
Quit condition gives k>=2 while player 1 requires k<=1. Equality in
the first comparison instead forces q_3=c=k=0, and player 1 then
forces q_2=0. Hence a zero coordinate occurs only in the all-zero row.

With all coordinates positive, suppose q_1=1 and q_2<1 (rotate the
cycle to a transition from a sure coordinate to a nonsure one). Player
2's indifference gives q_3=2-k. If q_3<1, player 3's indifference gives
q_2=(1+k)/2>=1. If q_3=1 then k=1 and f_1=1-q_2>0. Both are
contradictions. Thus either all are one or all are interior. In the
interior, (2) gives q_pred(j)=phi(q_succ(j)), where

    phi(v)=[k+c+(1-c)v]/[2+c-cv],
    phi'(v)=[2-c+ck]/[2+c-cv]^2>0.

A strictly increasing map has no nonconstant three-cycle. Hence all
coordinates agree, and (3), whose left side is strictly increasing,
proves uniqueness. This also verifies the all-zero boundary c=k=0.

### Why unreachable suffixes do not invalidate the argument

At each positively reached row the conditional laws remain independent.
Changing one player's conditional suffix multiplies its conditional
payoff gain by the positive probability of reaching that row. Thus
conditional best-response comparisons are justified whenever the row is
reached.

First suppose a reached row before the final menu date absorbs surely.
If the pivot quits surely, all three nonpivots must Quit. Otherwise at
least one nonpivot quits surely. Each nonpivot may compare with Quit
now and with Continue now followed by Quit at the next menu date. The
latter has continuation value zero, including ties with the pivot. The
prescribed absorption is certain, so these comparisons imply exactly
the Nash inequalities of (2) with c=0. The row lemma therefore forces
all three nonpivots to Quit surely, and h>=1/2. Their values there are
zero and all three complete marginal laws end there. No arbitrary
off-path law has been used. Backward induction through its positively
reached prefix uses c=0 and proves equal earlier hazards.

If no earlier row absorbs surely, the final row is reached. Conditional
on everyone surviving it, each nonpivot is committed to Never and gets
-c, where c is the pivot's conditional probability of a later finite
quit. The common value lies in [-1,0], so the row lemma applies. If the
pivot has conditional survival zero, its h=1 case applies directly.
Every earlier reached row then has continuation value zero. Backward
induction proves the identical-law and zero-payoff conclusions of (1).

### A full-response lower bound independent of the deadline

Let s_t be one common nonpivot's survival probability before date t,
w_t the pivot's survival probability, and q_t,h_t their conditional
hazards. Write a for the common nonpivot Never mass and D=a^3. Write
lambda for the pivot's total finite mass at dates >=N and nu for its
Never mass. At every row before the final effective row, the row lemma
with zero continuation gives

    h_t=q_t/(1+q_t),  w_t>=s_t,
    x_t:=Pr(T_0=t)=w_t h_t >=(s_t-s_(t+1))/2.             (4)

For every pure finite pivot response t its payoff is 2-s_t^3. The
unrestricted pivot cap is therefore 2-D, attained after the nonpivot
menu. Direct averaging gives the exact pivot debt

    d_0=I+nu D,    I=sum_(t<N) x_t(s_t^3-D)>=0.           (5)

This retains simultaneous atoms: s_t is survival STRICTLY BEFORE t.

Let T be the last effective row and b=s_T. If b<=1/2, (4) on earlier
rows and D<=b^3 give

    I >= (1/2) integral_b^1 (u^3-b^3) du >=1/16.          (6)

If the last row is sure absorption, all three q_T=1 and h_T>=1/2.
Then D=0 and its contribution to I is at least b^4/2. Together with
(6), this gives E>=1/32. This includes h_T=1.

It remains to consider no sure absorption, with T=N-1, b>1/2, and
q=q_T<1. Put h=h_T and ell=lambda/w_T. The last row's indifference is

    (1-h)q-h-ell(1-q)^2=0.                             (7)

For q=0 this same equality follows from the all-zero row case.
Since ell<=1, if q>=1/2, (7) implies h>=1/8. The last row's
contribution to I is then at least

    w_T h b^3[1-(1-q)^3] >=7 b^4/64 >=7/1024.           (8)

If q<1/2 instead, a=b(1-q)>1/4. Equation (7) implies
h<=q/(1+q), hence the pivot's remaining mass lambda+nu is at least a.
The common Never action has positive probability and is an exact menu
best reply of value zero. Quitting at the first positive late pivot atom
(or any date >=N if lambda=0) improves that payoff by exactly lambda a^2:
the two other nonpivots must both choose Never, and joining the pivot
replaces reward -1 by zero. Thus

    E >= max(lambda a^2, nu a^3)
      >= (lambda+nu)a^3/2 >=a^4/2 >1/512.               (9)

The late test is legitimate for arbitrary pivot tails: their nonempty
finite support has a first atom. When lambda=0 it gives zero. Equations
(5)-(9) prove (1) without a compactness, cap-attainment, or symmetry
assumption on an infinite law.

## What fails, and what approximate play changes

The smallest failed implication is: minimize the original full repair
value over all simultaneous EXACT finite-menu nonpivot responses, then
increase the deadline, and obtain vanishing full regret. The quantifier
over all fixed points is now explicitly covered by (1).

This does not eliminate positive-error nonpivot response selection. On
the SAME table, the pivot Never and the laws

    p_j(3k+j-1)=2^(-k-1), 0<=k<K;
    p_j(Never)=2^(-K)

have full exploitability 8^(-K). Their only nonpivot debt is player 2's
8^(-K), whereas their three laws occupy distinct phases. An arbitrarily
small global nonpivot error therefore breaks the exact-symmetry
restriction by an order-one amount. Taking exact nonpivot best replies
before sending N to infinity loses these successful laws.

Nearby source comparison: the bad unweighted coupled branch and the
explicitly open minimum-over-all-fixed-points alternative are in
`CODEX_RENY__PIVOT_LP_AND_FINITE_NONPIVOT_BEST_REPLY_COUPLING.md`.
The different compensated beta=0 correspondence already has an
all-menu lower bound in
`CODEX_RENY__ZERO_BONUS_COMPENSATED_CONTINUATION_OBSTRUCTION.md`.
The unrestricted identical-law obstruction is in
`CODEX_RENY__SYMMETRY_PRESERVING_LOGIT_SELECTOR_OBSTRUCTION.md`.
The present proof derives equality of the nonpivot laws without imposing
it and does not rely on that note's separate lower-bound proof. The
successful finite laws and their complete caps are recorded in
`CODEX_RENY__CANONICAL_EXACT_FINITE_MENU_SEPARATION.md`.

## Zero-singleton child selection

### A self-contained finite reward-table theorem

Let I={0,1,2,3}, and let S be any nonempty proper subset. Let r be any
bounded real reward table, with zero Never payoff and independent private
stopping laws as above. Write s_i=r_i({i}). Suppose SOME j in S satisfies
s_j>=0. For each outsider k in I\S suppose there are fixed numbers
lambda_ki>=0 such that, for every nonempty A contained in S,

    s_k-r_k(A) <= sum_(i in S) lambda_ki [s_i-r_i(A)],       (F)
    r_k(A union {k})-r_k(A)
      <= sum_(i in S) lambda_ki [r_i(A union {i})-r_i(A)].  (J)

These are finite inequalities in the ORIGINAL table. There is NO
all-Never row requirement. In particular s_k need not be at most
sum_i lambda_ki s_i.

**Theorem.** For every e>0 there are a finite deadline and independent
laws on its finite-time/Never menu, with every outsider literally Never,
whose ORIGINAL full behavioral exploitability is below e. Consequently
there is one fixed uniform-equilibrium payoff, and its witnesses can be
selected from these actual quiet lifts.

The at-most-three-player child existence theorem is the only game
existence input. No favorable child payoff, stopping law, positive
absorption profile, inner-LP optimizer, or vanishing residual is assumed.

### Producing absorption while returning to the original child

For 0<delta<=1, let g^delta be the child reward table obtained from its
original restriction g by adding delta ONLY to player j's own-singleton
coordinate. Its new own singleton is s_j+delta>=delta. By the checked
at-most-three-player existence theorem, choose an actual child profile
p^delta with full exploitability at most delta^2 in g^delta.

For ANY independent profile p in ANY quitting table with positive own
singleton v for some player, its full debt is at least

    v * Q(p),        Q(p)=product_i p_i(Never).            (10)

Proof: keep that player's original finite atoms and move only its Never
atom to a deterministic date T. As T tends to infinity, its payoff gain
tends to v Q(p). The original finite atoms make identical contributions;
on the moved branch, finite opponent absorption before T is unchanged,
the probability of a finite opponent atom at/after T tends to zero, and
joint Never changes from zero to the own singleton v. Bounded rewards
justify this limit. Each replacement is legal and has gain bounded by
the full debt, so the limit does too. This is a supremum argument, with
no claim that the limit date is itself a finite action.

Applying (10) BEFORE changing the rewards back gives

    Q(p^delta) <= delta^2/(s_j+delta) <= delta.            (11)

For every original law and every unilateral replacement, the difference
between its g^delta and g payoffs is between zero and delta in coordinate
j and is zero elsewhere. Therefore the SAME selected profile satisfies

    E_g(p^delta) <= delta^2+delta,    Q(p^delta)<=delta.   (12)

The profile was selected using a perturbed child; all subsequent safety
comparisons use the original child and original parent table. In
particular (F) and (J) are NEVER required for g^delta and are NEVER
perturbed. Their equalities and zero weights cause no continuity issue.

### Original-table outsider safety on these selected laws

For each outsider set

    rho_k=max(s_k-sum_(i in S)lambda_ki s_i,0).

For every actual child law p, the exact original-table bound is

    d_k(quiet(p)) <= sum_i lambda_ki d_i(p)+rho_k Q(p),  (13)
    d_i(quiet(p))=d_i(p) for i in S.

Here is a direct proof. Compare an outsider's pure stopping date t with
the child private replacement T_i -> min(T_i,t), separately for each i.
If the child first absorbs before t, all gains are zero. If its first
coalition A occurs at t, (J) bounds the outsider join gain by these
child gains. If it occurs after t but finitely, (F) gives the bound.
On child joint Never the difference is at most rho_k; at outsider Never
all gains are zero. Integrate this pathwise inequality and bound each
child replacement by its full debt. Taking the outsider supremum proves
(13), and independence is preserved in every replacement. The common
proof coupling supplies no correlated strategy to the players.

Put C=max(1,max_k sum_i lambda_ki) and R=max_k rho_k. Equations
(12)-(13) give the ACTUAL parent profile bound

    E_r(quiet(p^delta)) <= C(delta+delta^2)+R delta ->0.   (14)

To obtain finite laws, move each child's finite mass after a sufficiently
large cutoff to Never. If the sum of moved marginal masses is tau, a
product coupling changes every prescribed payoff and every fixed pure
deviation payoff by at most 2M tau. Hence full regret grows by at most
4M tau, uniformly over ALL deviations. Joint Never grows by at most tau.
Choose delta and then tau so that (14)+4M tau<e. Outsiders stay Never.
This is an actual finite-law producer from the stated finite reward data.

The terminal payoff vectors of these selected profiles lie in a compact
cube. A convergent subsequence gives one fixed vector v before accuracy
is requested. The terminal-to-uniform family theorem retains the actual
selected profiles as witnesses. Thus no varying-target substitution or
uncontrolled horizon-dependent strategy is used.

### The full five-kind withdrawal consequence

The same argument applies unchanged to any of the five already checked
original F/J withdrawal systems: patient, deadline, evaluated security,
terminal security, or cancellation. For each outsider their actual raw
certificate supplies nonnegative debt coefficients c_ki and residual rho_k
with the SAME inequality (13), replacing lambda by c. Patient and
cancellation use the sum of the two operation weights; the other kinds
use their maximum. Their residual is the positive part of the omitted
original Never row, including the patient Never bonus. These are fixed
finite numbers computed from ORIGINAL rewards and certificate weights.
Use C=max(1,max_k sum_i c_ki) and the same R in (14). Different outsiders
may use different kinds. No perturbed security floor, perturbed
withdrawal condition, or certificate-stability hypothesis is needed.

This consequence extends the existing strict-positive-singleton Fin4
EXISTENCE consumer to a nonnegative child singleton. It does not extend
the stronger consumer promising to preserve ANY externally prescribed
child uniform target: the perturbed child profiles select their own
limiting payoff, which may differ from that target. The parent target
agrees with the child target selected by this construction.

For the canonical question, choose S={1,2,3}. All its own singletons are
zero, so the new source applies whenever the original pivot has one of
these F/J certificates. The finite quiet laws already have small E;
global minimization of the exact pivot LP against their three marginals
can only decrease E. Thus the output is exactly a small-inner-value
outer-law selection, without an assumed pivot-optimality compatibility.

### Source audit and boundary tests

- `QuittingThreePlayerStrategyClass.of_card_le_three`, in
  `UniformEquilibrium/Quitting/Classification/ThreePlayer/StationaryOrSmallHazardAllSigns.lean`,
  supplies actual unrestricted terminal approximate equilibria for the
  perturbed child. The exact strategy-class definition in
  `StationaryOrSmallHazard.lean` was inspected too.
- `WithdrawalFutureJoinRewardCertificate`, `neverExcess`, and `debtWeight`,
  in `UniformEquilibrium/Quitting/Classification/QuietExtension/WithdrawalFutureJoinRaw.lean`,
  specify original finite rewards/weights, not a selected strategy.
- `withdrawalFutureJoin_quietLift_outsideDebt_le_add_neverExcess`, in
  `UniformEquilibrium/Quitting/Classification/QuietExtension/WithdrawalFutureJoinDebt.lean`,
  gives (13) for every actual original child profile and all five kinds.
- `quittingGame_exists_uniformEquilibriumPayoff_of_finFour_withdrawalFutureJoinFamily`,
  in `UniformEquilibrium/Quitting/Classification/QuietExtension/WithdrawalFutureJoinFixedTarget.lean`,
  has the strict hypothesis `0 < reward (quittingSingletonTerminal pivot.1) pivot.1`.
  This is the exact producer boundary changed here, at existence level.
- `quittingTerminalExploitability_censored_le`, in
  `UniformEquilibrium/Quitting/Paths/LateFiniteStoppingLawCensor.lean`,
  gives the finite conversion. `quittingGame_uniformPayoffWitnesses_of_terminalNash_tendsto`
  and `quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`,
  in `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`,
  give the fixed uniform payoff conclusion and retained-family witnesses.

The checked `WithdrawalBoundaryExamples.neverResidual_outsideDebt_eq_residual_times_childJointNever`
in `UniformEquilibrium/Quitting/Examples/WithdrawalNeverBoundary.lean`
is NOT contradicted. Its one-child zero-reward all-Never profile has
Q=1, child debt zero, and outsider debt one. The theorem here selects
different laws: perturb the child's singleton positively, then let that
child Quit surely. In the original game that child's payoff/debt remain
zero and Q becomes zero, removing the outsider residual.

A particularly transparent full canonical subclass has
r_0(A)>=1 and r_0(A union {0})<=r_0(A) for every nonempty
A contained in {1,2,3}. All nonpivot rewards, except their zero own
singletons, are arbitrary. Taking all weights zero proves (F)-(J).
The original strict-positive-child wrapper cannot use this deletion;
the present actual-law producer does. No claim is made that none of
these tables can be solved by a different existing method.

The nonnegative-singleton hypothesis cannot be dropped for this quiet
source mechanism. With one child whose own payoff is -1, an outsider
whose reward is always 1, and child reward -1 on every coalition, zero
weights satisfy (F)-(J). In every quiet lift, child debt is its finite
quit probability and outsider debt is the child's Never probability;
full regret is at least 1/2. The parent itself has equilibrium with the
outsider quitting: the failure concerns the prescribed quiet class.

The independently reviewed scope of (10)-(14) is the selected-family
existence conclusion recorded in the frozen export named at the top.
The general single-pivot table still needs an arbitrary-table producer.

## A joint phase closes an asymmetric cyclic pivot family

Status: independently reviewed mathematical construction and F/J
separation. Bare UE existence is already covered by the product-low theorem;
the explicit profile is not claimed to enlarge that existence class.

### Raw table and parameter interval

Let a,b,c>0 and D=abc−1>0. Number the nonpivots cyclically 1,2,3,
with predecessor of 1 equal to 3. Put (a_1,a_2,a_3)=(a,b,c). For every
nonempty coalition S define

    r_0(S) = 1                         if 0 is in S,
             R * 1_(3 is in S)         otherwise;
    r_j(S) = 0                         if j is in S,
             −1                        if j is not in S and 0 is in S,
             a_j*1_(pred(j) is in S) − 1_(succ(j) is in S) otherwise.

The own singletons are exactly (1,0,0,0). Define

    R_low  = (ab+ac+a+bc+b+c+3)/(bc+b+1),
    R_high = ac+a+1.

Their difference is (c+2)D/(bc+b+1)>0. The theorem concerns every

    R_low < R < R_high.                                      (15)

All rewards are finite real data. All random choices below are private and
independent, both between players and between successive live dates. The
construction uses only the public date and whether absorption has occurred.

**Claim.** Every table (15) has an exact unrestricted-behavior terminal Nash
profile with a period-three product schedule. Its finite censored laws
produce arbitrarily small unrestricted exploitability and hence arbitrarily
small pivot-repair values. One explicit target precedes the accuracy.

### Selection of the four hazards

Set

    Y = D/[b(ac+a+1)] ∈ (0,1).

For 0<y<Y select the unique root k in

    0 < k < min(by, c−(c+1)y)

of

    f_y(k) = (k − a*w*(1−z) + z)*c*(1−y)*(1+by) = 0,
    z = (k+y)/[c(1−y)],
    w = (by−k)/(1+by).                                      (16)

This is an actual scalar selection, not an assumed equilibrium solution.
After substituting z,w, f_y is a quadratic with leading coefficient −a.
Its value at zero is

    y[b(ac+a+1)y−D] < 0.

At k=by, w=0, so f_y(k)>0. At k=c−(c+1)y, z=1, so again
f_y(k)>0. Both endpoints are positive: Y<c/(c+1). A strictly concave
quadratic negative at zero and positive at these two endpoints has exactly
one root below their minimum. This proves (16) and 0<z,w<1.

The smaller positive quadratic root is continuous in y and extends to
k(0)=k(Y)=0. Indeed the discriminant is strictly positive and the linear
coefficient is positive throughout [0,Y], as follows also from positivity
at k=by for y>0 and its explicit positive value ac+c+1 at y=0.

Define on 0<y≤Y

    R(y) = 1 + [1/((1−y)(1−z))−1]/w.                       (17)

It extends continuously to zero. To compute that endpoint, put

    v = (ac+c+1, ab+a+1, bc+b+1)/D.

The expansion of (16) at y=0 gives k/y→1/v_1, z/y→v_2/v_1,
w/y→v_3/v_1, and therefore R(0)=(v_1+v_2+v_3)/v_3=R_low.
At y=Y the exact endpoint rates are

    y = D/[b(ac+a+1)],
    z = D/[c(ab+b+1)],
    w = D/[a(bc+c+1)],

and substitution into (17) gives R(Y)=ac+a+1=R_high. The intermediate
value theorem supplies a y strictly between 0 and Y with R(y)=R for
every (15). No monotonicity of R(y) is needed. Finally set x=k/(1+k).
Thus x,y,z,w all belong to (0,1).

### Actual profile and complete response check

Repeat these three live rows forever:

| Phase | Player 0 | Player 1 | Player 2 | Player 3 |
| --- | ---: | ---: | ---: | ---: |
| A | x | y | 0 | 0 |
| B | 0 | 0 | z | 0 |
| C | 0 | 0 | 0 | w |

Entries are Quit probabilities; rows are product distributions, not public
mixtures of coalitions. Put k=x/(1−x). The continuation values at the three
phase entries are

    V_A = (1, 0, w/(1−w), 0),
    V_B = ((1−z)[1+(R−1)w], k, 0, c*z),
    V_C = (1+(R−1)w, a*w, 0, 0).                           (18)

Equation (17) says V_B,0=1/(1−y). Hence all pivot values are at least
one; all nonpivot values are nonnegative. The C and B recurrences follow
directly from their singleton rows. The A recurrences reduce exactly to

    (1−y)V_B,0 = 1,
    V_B,1 = k,
    (a_2*y−k)/(1+k) = w/(1−w),
    −k−y+c*z*(1−y) = 0.

The second equality is (16), and the others are respectively (17) and
the definitions of w,z. These are full vector Bellman equalities, including
the simultaneous coalition {0,1}, whose reward is (1,0,−1,−1).

Every nonpivot's Quit-now payoff is exactly zero at every phase, including
all ties and all multi-player coalitions. Whenever it mixes, its displayed
value is zero; whenever it Continues surely, its displayed value is
nonnegative. The Bellman equalities therefore give both pure-action Nash
inequalities at every phase. Player 0's Quit-now payoff is always one.
It mixes only at A, where its value is one, and Continues at B,C where
its values exceed one. Thus its two pure-action inequalities also hold.

These row comparisons control COMPLETE deviations. Fix a deviator. Every
opponent has a positive hazard in each three-date period, independently of
the deviator, so the probability that all opponents survive K periods
tends geometrically to zero. Iterating the two-action Bellman upper bounds
against an arbitrary history-dependent behavioral deviation, and bounding
the surviving remainder by the finite reward/value bound, proves that its
terminal payoff is at most the corresponding coordinate of (18). The same
contraction proves that the displayed vector recurrence equals the actual
prescribed terminal payoff. This establishes exact terminal Nash, not just
on-path or bounded-controller optimality.

The phase-A target is explicitly (1,0,w/(1−w),0). Censor the independent
laws after K periods by moving every later finite atom to Never. The sum
of changed marginal masses is

    tau_K = (1−x)^K + (1−y)^K + (1−z)^K + (1−w)^K → 0.

For a reward bound M, the prescribed payoff changes by at most 2M*tau_K
and every full regret by at most 4M*tau_K. These are actual finite laws
on a common menu. The exact pivot LP value against their three nonpivot
marginals is no larger than this profile's regret. This supplies the outer
laws required by the finite-menu question on the raw class (15). The same
fixed phase-A target is a uniform-equilibrium payoff by the terminal-family
consumer, or directly by the periodic-block consumer.

### Every proper-child F/J family fails on the same raw tables

Every one of the five F/J withdrawal kinds has the checked implication

    d_out ≤ sum_i c_i*d_child,i + rho*Q_child,               (19)

for every actual child profile, with finite nonnegative c_i,rho. Therefore
an exact child Nash profile with Q_child=0 and positive outside debt rules
out ALL choices of weights for ALL five labels at that child/outside pair.
The following cases exhaust every nonempty proper S⊂{0,1,2,3}.

1. If S⊂{1,2,3} and |S|≤2, let one child quit surely at date zero. For
   two children choose the owner giving the other its positive a_j reward;
   that is an exact child Nash profile. The missing third child, with
   prescribed payoff −1 gains one by joining at date zero. For a singleton
   child choose the missing player receiving −1. In both cases Q_child=0.
2. If S={1,2,3}, use the endpoint y=Y,z,w displayed above, with solo
   phases 1,2,3 and no pivot. Formula (18) without coordinate 0 and with
   k=0 proves exact child Nash and Q_child=0. Player 0's prescribed payoff
   is R/R_high, whereas quitting immediately gives one. Its debt is at
   least 1−R/R_high>0.
3. If 0∈S but 3∉S, make every member of S quit surely at date zero.
   The pivot gets one and loses by withdrawing; each retained nonpivot
   gets zero and gets −1 by withdrawing. This is exact child Nash.
   Any missing nonpivot gets −1 and gains one by joining; Q_child=0.
4. If {0,3}⊆S and 2∉S, player 3 alone quits surely at date zero.
   The pivot gets R>1 and any retained player 1 gets a>0, so this is exact
   child Nash. Missing player 2 gets −1 and gains one by joining.
5. The only remaining child is S={0,2,3}. At date zero, child 2 quits
   surely, pivot 0 quits with probability c/(1+c), and child 3 quits
   with probability 1/R; all surviving laws choose Never. Child 3's
   Continue payoff is zero, pivot 0's Continue payoff is one, and child
   2's Continue payoff is negative. Their Quit payoffs are respectively
   zero, one, zero. Thus this is exact child Nash with Q_child=0. Missing
   player 1 gets −1+a/[(1+c)R]<0 and can join for zero. The strict sign
   follows from R>R_low>a/(1+c).

These falsifiers exclude a complete F/J quiet-lift family at every proper
child, even if different outsiders may choose different kinds. They do not
claim that every quiet approximate profile is bad, nor that the union of
reward-table closures of all other producer classes is excluded.

### Transparent symmetric specialization and corpus boundary

For a=b=c=A>1 the interval is 3<R<1+A+A². One may choose a unique
y∈(0,(A−1)/A) by

    (1−y)^2[1+(R−1)y]=1,
    z=w=y,   k=y(A−1−Ay),   x=k/(1+k).

For A=2 this is exactly 3<R<7. At R=4,
y=(5−sqrt(13))/6. This is an exact algebraic test, not numerical evidence.

Named sources checked:

- `isUniformEquilibriumPayoff_of_isQuittingBlockCertificate`, in
  `UniformEquilibrium/Quitting/Cycles/BlockPeriodicProfile.lean`, is the
  existing unrestricted-behavior periodic consumer; it does not produce
  the present hazards from (15).
- `withdrawalFutureJoin_quietLift_outsideDebt_le_add_neverExcess`, in
  `UniformEquilibrium/Quitting/Classification/QuietExtension/WithdrawalFutureJoinDebt.lean`,
  supplies (19) uniformly in the five labels. Its exact `kind` quantifier
  and original-child-profile quantifier were inspected.
- `FullCoreDeadlock.jointBlock_isQuittingBlockCertificate` in
  `UniformEquilibrium/Quitting/Classification/LCP/FullCore/DeadlockJointBlockEquilibrium.lean`
  treats one different full-core singleton matrix and its zero-multicoalition
  completion. `IsDeadlockRationalJointBlockCompletion` in
  `DeadlockRationalPolyhedralBlock.lean` retains that same different matrix.
  The existence of those joint-block methods is not claimed new here.
- `exists_balancedCertificate_of_strictlyPositiveInverse_child` and
  `exists_uniformEquilibriumPayoff_of_strictInverse_passiveRows`, in
  `UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/StrictInversePassiveRowCycle.lean`,
  produce the known quiet three-child cycle when the outside inverse row
  is nonnegative. For the displayed asymmetric pivot row, (15) has the
  exact bad endpoint R/R_high<1; that passive-row test does not apply.
- The finite censor, pivot-LP comparison, and retained-family target sources
  are the exact declarations already listed above.

The decisive broader source is
`exists_uniformEquilibriumPayoff_of_productLowPremium`, in
`UniformEquilibrium/Quitting/Classification/Existence/ProductLowPremiumUniformPayoff.lean`.
Its hypothesis `HasProductLowQuittingPremium`, defined in
`UniformEquilibrium/Quitting/Classification/ProductLowQuittingPremium.lean`,
holds here because EVERY player's forced-Quit payoff equals its singleton
at EVERY product root. It proves bare existence for this family even
outside (15), and likewise for the positive-harm enlargement below. The
exact selected cycle and all-child F/J separation are stronger concrete
information, but do not establish new existence coverage.

## Proposed enlargement: independent positive pivot harm levels

Status: independently reviewed extension of the exact selected cycle and
all-child F/J separation. Its whole bare existence class is also already
product-low, as stated above. The previous central proof is unchanged.

Keep a,b,c>0 and D=abc−1>0, but choose arbitrary h_1,h_2,h_3>0.
Change only each nonpivot's reward when the pivot quits without it from
−1 to −h_j. Keep its own-quitting reward zero and its two cyclic passive
coefficients a_j and −1. Keep r_0(S)=1 for 0∈S and
r_0(S)=R*1_(3∈S) otherwise. Thus all finite coalition entries are again
specified explicitly, and the own singleton vector remains (1,0,0,0).

Let

    A = [[0,−1,a],[b,0,−1],[−1,c,0]],
    v = A^(-1) h
      = (ac*h_2+c*h_1+h_3,
         ab*h_3+a*h_2+h_1,
         bc*h_1+b*h_3+h_2)/D.

Every v_j is strictly positive. Set

    R_low(h) = (v_1+v_2+v_3)/v_3,
    R_high = ac+a+1.

The interval is always nonempty, since exact algebra gives

    R_high−R_low(h) = [(c+1)h_1+h_3]/v_3 > 0.             (20)

**Enlarged claim.** For every R strictly in this interval, the same
three-phase support pattern produces an exact unrestricted terminal Nash
profile, explicit fixed target, and finite outer laws with vanishing repair
value. Every proper-child F/J family is still excluded.

### Monotone scalar selection

Use the unchanged Y=D/[b(ac+a+1)]. For 0<y<Y and

    0≤k≤min(by/h_2, [c−(c+1)y]/h_3),

put

    z(k,y)=(h_3*k+y)/[c(1−y)],
    w(k,y)=(by−h_2*k)/[1+by+(1−h_2)k],
    G(k,y)=h_1*k+z−a*w*(1−z).                            (21)

The denominator of w equals 1+k+(by−h_2*k), hence is positive on this
whole interval. At its left endpoint,

    G(0,y) has the sign of y[b(ac+a+1)y−D],

which is negative. At its right endpoint, either w=0 or z=1, and G>0.
Inside the interval, z strictly increases in k and

    partial_k w = −(h_2+by)/[1+by+(1−h_2)k]^2 < 0.

Thus G is strictly increasing while 0<w,z<1. It has one unique root in
the interval's interior. This proves the selection without any assumption
on the sign of the cleared quadratic's leading coefficient.

The root k(y) is continuous and extends to k(0)=k(Y)=0. At zero this
follows from k≤by/h_2. At Y, every subsequential limit must be a root
of the strictly increasing endpoint function, whose unique root is zero.
Interior continuity follows either from strict monotonicity and compact
local brackets or from the positive k-derivative in (21).

As y tends to zero, all y,z,w,k are O(y). The three equations (21) give

    A*(y,z,w) = h*k + O(y²).

Consequently (y,z,w)=v*k+O(y²), so k/y→1/v_1, z/y→v_2/v_1,
w/y→v_3/v_1. The same function (17) therefore extends continuously with
R(0)=R_low(h). At y=Y the unchanged k=0 endpoint rates give
R(Y)=R_high. By (20) and the intermediate value theorem, every requested
R in the enlarged interval is attained at an interior y. Set x=k/(1+k).

### Full values, deviations, and certificate exclusion

The three actual root supports and all four independent hazards remain
as above. The only change in (18) is

    V_B,1 = h_1*k.

The A-row identities now read

    −h_1*x+(1−x)*V_B,1 = 0,
    (by−h_2*k)/(1+k) = w/(1−w),
    −h_3*k−y+c*z*(1−y) = 0.

They follow exactly from (21); the pivot equation is unchanged. Every
displayed nonpivot value is nonnegative, every pivot value is at least
one, and mixing occurs only at equality. Own-Quit endpoints are still
zero for nonpivots and one for the pivot. Positive opponent hazards every
period again give the unrestricted behavioral comparison and identify the
actual values. The finite censor and fixed phase-A target are unchanged.

The proper-child falsifiers above need only these two replacements:

- When 0∈S and 3∉S, the full sure-Quit child remains Nash; an omitted
  nonpivot j has debt h_j>0 instead of one.
- For S={0,2,3}, use pivot hazard c/(c+h_3), child-3 hazard 1/R, and
  child 2 surely quitting, all at date zero. Pivot and child 3 remain
  indifferent; child 2 strictly prefers quitting. Missing child 1 gets

      [−c*h_1+h_3*(a/R−1)]/(c+h_3).

  It is strictly negative because R>R_low(h)>a*h_3/(c*h_1+h_3).
  For the latter inequality use a*v_3−v_2=h_1 and c*v_2−v_1=h_3:

      (c*h_1+h_3)(v_1+v_2+v_3)−a*h_3*v_3
        = h_1[(c+1)v_1+c*v_3]+h_3(v_1+v_3) > 0.

All other child profiles use no pivot and are unchanged. They still have
zero child debt and Q_child=0; in the full three-child case the pivot's
positive debt is 1−R/R_high. Hence (19) again refutes every five-kind
F/J choice at at least one outsider of EVERY proper child.

Requested additional review: the interval identity (20), the unique
monotone selector (21) including its endpoint limits, and the two modified
child falsifiers. The original complete-deviation and finite-law arguments
apply literally after the displayed replacement V_B,1=h_1*k.

## Positive mutual premiums at the prescribed joint phase

Status: live proof draft beyond product-low and the proper-child F/J
families. This section is not covered by the reviews of the zero-premium
construction above. No export or Lean verification is asserted.

### Raw family and exact conclusion

Start with the positive-harm table above: a,b,c,h_1,h_2,h_3>0, abc>1,
and R_low(h)<R<R_high. Choose

    xi>0,                 0<eta≤a*min(h_2,1).

Change EXACTLY two reward entries, both on the coalition {0,1}:

    r_0({0,1})=1+xi,       r_1({0,1})=eta.                (22)

All other entries retain the preceding explicit table. In particular its
own singleton vector is still (1,0,0,0). These increases occur at a
prescribed coalition with strictly positive probability, not merely at an
unused full-coalition row.

**Claim.** Every such supplied raw table has a selected exact period-three
independent terminal Nash profile, a fixed uniform target, and actual
finite outer laws with pivot-repair values tending to zero. Every proper
child fails a full five-kind F/J family, and the table robustly fails
product-low quitting premiums.

### Selecting the hazards after the actual payoff change

Retain Y, the interval for k, and z,w from (21). Write

    d=1+by+(1−h_2)k,
    G_eta(k,y)=h_1*k+z−a*w*(1−z)
                 +eta*k[1−(1−z)(1−w)/(1+k)].             (23)

For 0<y<Y the value at k=0 is still strictly negative. At the upper
endpoint either w=0 or z=1; the old part is strictly positive and the
added part is nonnegative. Moreover 1−w=(1+k)/d. With z_k>0, direct
differentiation yields

    partial_k G_eta
      = h_1+eta + (1+a*w+eta*k/d)*z_k
          + (1−z)/d² * [a(h_2+by)−eta(1+by)] > 0.       (24)

The final bracket is nonnegative by the stated bound on eta. Thus there
is exactly one interior root k(y), again with all x=k/(1+k),y,z,w in
(0,1). It extends continuously to k(0)=k(Y)=0. The extra term in (23)
is O(y²) near zero, so the same endpoint ratios hold:

    k/y→1/v_1,          z/y→v_2/v_1,          w/y→v_3/v_1.

For this root define

    R_xi,eta(y)=(1+xi*y)
                    * [1+(1/((1−y)(1−z))−1)/w].         (25)

It extends continuously with

    R_xi,eta(0)=R_low(h),
    R_xi,eta(Y)=(1+xi*Y)R_high > R_high.

Every prescribed R_low(h)<R<R_high therefore has a selected interior y
with R_xi,eta(y)=R. Equations (23)-(25) select all hazards from the NEW
table. They do not reuse rates that were optimal before changing rewards.

### Complete-vector Bellman identities and all behavior deviations

Repeat the independent supports {0,1}, {2}, {3}, with rates x,y,z,w as
before. Put

    p=1+xi*y,       t=eta*x.

The three vectors are

    V_A=(p, t, w/(1−w), 0),
    V_C=((1−w)p+R*w, (1−w)t+a*w, 0, 0),
    V_B=((1−z)V_C,0, (1−z)V_C,1−z, 0, c*z).             (26)

In the last display the comma after a subscript separates coordinates:
explicitly V_B,0=(1−z)V_C,0 and V_B,1=(1−z)V_C,1−z.
The selector gives

    V_B,0=p/(1−y),       V_B,1=k(h_1+eta).                (27)

The second identity is exactly (23); the first is (25). The pivot's
Quit-now payoff is p at A and one at B,C. Its A Continue value is
(1−y)V_B,0=p. Both B,C values exceed one. Player 1's Quit-now payoff
is x*eta=t at A and zero at B,C, whereas its A Continue value is

    −h_1*x+(1−x)V_B,1 = eta*x=t.

Its values at B,C are positive. Players 2 and 3 retain Quit-now payoff
zero at every phase. Their A recurrences are unchanged, and their values
are nonnegative, with zero exactly at their prescribed mixing phases.
The prescribed pair {0,1} has vector (1+xi,eta,−h_2,−h_3), so these
checks include the changed actual collision payoff, not merely isolated
pure-action tests. The B,C singleton recurrences give the rest of (26).

Thus every pure action endpoint at every live phase is bounded by the
displayed value, with equality for every supported action. Every player
retains a positive-hazard opponent every period. Iterating these exact
inequalities against an arbitrary complete behavioral deviation kills the
geometrically bounded surviving remainder. The same iteration identifies
the actual prescribed values. Hence this is exact unrestricted terminal
Nash, with fixed target

    (1+xi*y, eta*x, w/(1−w), 0).

Censoring the four independent laws after K cycles again changes total
marginal mass by tau_K from the original construction and bounds full
exploitability by 4M*tau_K. The same finite nonpivot marginals therefore
have inner repair value at most 4M*tau_K. These are legal finite laws on
one common menu, with no public correlation. The fixed-target terminal
consumer, or the directly verified periodic-block consumer, gives the
uniform payoff. No fixed-target selection from unrelated approximants is
needed.

### Exact separation from product-low and all proper-child F/J

Take a product root supported on {0,1}, with both hazards one half.
Its only active players have own-Quit premiums xi/2 and eta/2, both
strictly positive. This is an inward absorbing root witnessing failure of
`HasProductLowQuittingPremium`. The strict witness survives all sufficiently
small reward perturbations, so the class is not a mere reward-closure
boundary of the product-low theorem.

The proper-child falsifiers in the positive-harm section survive. Two
points require an explicit check after (22):

- For S={0,1}, the full date-zero coalition now pays its members
  1+xi and eta. Withdrawing gives respectively zero and −h_1, so it
  remains exact child Nash with Q_child=0. Its omitted nonpivots still
  get −h_j and can join for zero. All other full-child coalitions in
  the case 0∈S,3∉S are unchanged and remain exact child Nash.
- For S={1,2,3}, the exact quiet cycle is unchanged. Pivot 0's payoff
  is R/R_high, while quitting at phase A gives 1+xi*Y. Its positive
  debt is at least 1+xi*Y−R/R_high. For the child S={0,2,3}, omitted
  player 1's joining response always includes sure-quitter 2, so it
  never realizes the altered pair {0,1}; its previously proved strict
  gain remains valid.

All remaining witnesses use unchanged coalition rows and comparisons.
Hence every proper child still has an outside player whose debt is
positive on an exact child Nash profile with joint Never zero. The single
slack implication (19) refutes ALL weights in EACH of the five labels.

### Early source-overlap check

The source definition of product-low was read directly, not inferred from
pointwise participant caps. It requires only ONE low-premium active player
at every absorbing product root, which is why BOTH entries in (22) are
raised. Raising player 1's pair reward alone would leave the original
product-low theorem applicable.

The singleton comparison matrix is unchanged by (22):

    M = [[0,−1,−1,R−1],
         [−h_1,0,−1,a],
         [−h_2,b,0,−1],
         [−h_3,−1,c,0]].

Every row has a strictly negative off-diagonal entry, so `normalCore` is
the full four-player set under the actual distinct-witness definition in
`UniformEquilibrium/Quitting/Classification/LCP/NormalCore.lean`.
There is no nonzero homogeneous LCP solution. If x_0>0, complementarity
and the successive rows 0,3,2 force all child coordinates positive; then
z=v*x_0 and the pivot residual is

    v_3*(R−R_low(h))*x_0 > 0,

a contradiction. If x_0=0, any nonzero child coordinate forces all three
positive by their cyclic equations, after which invertibility of A gives
a contradiction. Thus M is R0 and has no homogeneous simplex solution.

Its R0 degree is one, not a nonunit-degree exit. At the regular LCP offset
(1,−h_1,−h_2,−h_3), nonnegative child residuals force ALL child coordinates
positive. Hence z=(1+x_0)v. The pivot residual is
1+(1+x_0)v_3(R−R_low(h))>0, so x_0=0. This is the unique solution,
with strict inactive pivot residual and active determinant det A=D>0.
The exact root-sum theorem gives degree +1, and its nonzero-degree
consequence gives standard Q. The declarations inspected are
`exists_finset_r0Degree_eq_sum_sign_det` in
`MathUE/LinearProgramming/R0DegreeSum.lean` and
`isStandardQ_of_r0Degree_ne_zero` in
`MathUE/LinearProgramming/R0Degree.lean`.
Consequently the completed abnormal, homogeneous, ordinary non-Q and
nonunit-degree existence gates do not supply this class. The two-coordinate
principal {0,1} has both off-diagonal entries negative, so it is neither
standard Q nor homogeneous-feasible; the full table is not projective Q-bar.

The strict/weak three-child passive-row test also fails: the middle
coordinate of the pivot inverse row is (R−R_high)/D<0. Every other
three-player principal has a row with only negative off-diagonal entries,
which prevents an entrywise nonnegative inverse. The four-player positive
inverse criterion fails as well: the (0,2) entry of M^(-1) is positive
while its (0,1) entry is negative in this interval; equivalently the signed
pivot inverse row has both signs. Only the fact that at least one entry
is negative is needed for this exclusion.

The oriented-pair and paired-cylinder notes inspected have the reciprocal
positive singleton pairs 0↔1 and 2↔3. This family's singleton sign graph
has NO reciprocal positive pair, so no player relabeling or positive
playerwise affine transformation identifies those raw tables with these.
The integrated `PairedCycle.RawRegion` in
`UniformEquilibrium/Quitting/Cycles/PairedCycleSchedule.lean` requires two
positive nonpartner singleton comparisons in every four-player row through
`OwnBounds`/`PassiveBounds` from `MathUE/PairedAffineIntervalEstimates.lean`.
Here each row has exactly one positive off-diagonal comparison. The full-core
deadlock joint-block modules also fix a different singleton sign graph.
These are exact non-overlap checks for the named producer families, not a
claim to have exhausted every theorem in the repository.

### Rational stress test and next question

The literal parameters

    a=b=c=2,   h_1=h_2=h_3=1,
    xi=1,      eta=17/11,      R=1735/368

have selected hazards

    (x,y,z,w)=(1/11,1/4,7/30,4/15)

and target (5/4,17/121,4/11,0). Direct substitution gives G_eta=0 and
(25), with eta<2 and 3<R<7. This is an exact rational test of an ACTUAL
positive-premium collision and of the finite-law producer, not floating
point evidence or a reward chosen after assuming a strategy exists.

Next check: independently falsify (24), the changed complete-vector
recurrences, and the source overlap analysis before any gate decision.
The general arbitrary canonical table remains open.

## Proposed generalization: select the pivot equation first

Status: ordinary mathematics with independent CODEX_BROUWER and CODEX_MORSE
PASS reviews. This
section is separate from the frozen positive-mutual-premium review target
above. It removes the upper bound on the participant premium, changes the
actual collision rewards of the two outsiders independently, allows two
independent passive singleton rewards for the pivot, and leaves every
unused nonparticipant reward unrestricted. No Lean or export claim is made.

### Reward data and exact conclusion

Let a,b,c,h_1,h_2,h_3>0 and D=abc−1>0. Let u,v<1, xi>0,
eta>0, and q_2,q_3≤0. There is NO upper bound on eta. Prescribe the
four singleton vectors and the exceptional pair vector by

    r({0})   = (1, −h_1, −h_2, −h_3),
    r({1})   = (u, 0, b, −1),
    r({2})   = (v, −1, 0, c),
    r({3})   = (R, a, −1, 0),
    r({0,1}) = (1+xi, eta, q_2, q_3).                    (28)

For every other nonsingleton coalition T, require only

    r_i(T)≤s_i whenever i∈T,        s=(1,0,0,0).         (29)

Its nonparticipant rewards are arbitrary finite real numbers. Thus (28)
and (29) are a criterion on the raw reward table, not a requirement that
the game admit a particular strategy or continuation witness. In fact
many inequalities in (29) can be omitted because their coalitions are
unreachable even by one deviator; the uniform participant cap keeps the
statement simple.

Write s_1=1−u>0, s_2=1−v>0 and

    nu = (ac*h_2+c*h_1+h_3,
          ab*h_3+a*h_2+h_1,
          bc*h_1+b*h_3+h_2)/D,
    L = ac+a+1,
    R_low = 1+(s_1*nu_1+s_2*nu_2)/nu_3,
    R_high = 1+ac*s_1+a*s_2.

Assume R_low<R<R_high. This interval is always nonempty, since

    R_high−R_low
      = [(c*s_1+s_2)*h_1+s_1*h_3]/nu_3 > 0.            (30)

**Theorem draft.** Every such raw table admits an exact terminal Nash
profile against every complete behavioral deviation, using the period-three
independent supports {0,1}, {2}, {3}. The proof selects all four strictly
positive hazards from the table. Its phase-A payoff is a fixed uniform
equilibrium target. Finite censoring produces actual common-menu laws
with full exploitability and optimal pivot-repair value tending to zero.
Every table in this class strictly fails product-low premiums.

The statement does NOT exclude all proper-child F/J families for every
arbitrary completion (29). The previously proved all-child separation
survives on the original completion with u=v=0 and q_j=−h_j, even when
eta exceeds its former upper bound. A different arbitrary completion may
have an additional simpler producer.

The probability model is the original one: independent private action
randomization at each live date, public observation of the date and
survival, and no external public coin. A unilateral deviation replaces
one player's entire behavioral strategy. Terminal Never pays zero.

### A uniquely selected pivot branch

Put Y=D/(bL). Then 0<Y<c/(c+1)<1. For 0≤y≤Y define

    H_j(y)=h_j*(1−y)−q_j*y > 0,                 j=2,3.

For 0<y≤Y and

    0≤k<K(y)=min(by/H_2(y), [c−(c+1)y]/H_3(y)),

define

    z=(H_3(y)*k+y)/[c(1−y)],
    d=1+by+[1−H_2(y)]k,
    w=[by−H_2(y)k]/d,
    p=1+xi*y.

Here d=1+k+[by−H_2(y)k]>0, and 0<z,w<1. The pivot's
indifference equation is R=P(k,y), where

    P(k,y)=p+
      { (p−u)y/(1−y)+(p−v)z }/[(1−z)w].                (31)

For fixed y, z strictly increases in k and w strictly decreases, since

    z_k=H_3(y)/[c(1−y)]>0,
    w_k=−[H_2(y)+by]/d²<0.

Both p−u and p−v are positive. Consequently P strictly increases in k,
and P(k,y) tends to infinity as k increases to K(y): either w tends to
zero or z tends to one, while the numerator stays strictly positive.

At k=0, direct simplification gives

    P_0(y)=p+
      [(c+1)p−cu−v]*(1+by)/[b(c−(c+1)y)].              (32)

This is continuous and strictly increasing on [0,Y]. Indeed p increases,
the positive bracket increases, and the final positive rational factor
strictly increases. Its endpoints satisfy

    P_0(0)=1+[c*s_1+s_2]/(bc)<R_low,
    P_0(Y)=L*(1+xi*Y)−ac*u−a*v
          =R_high+xi*Y*L>R_high.                       (33)

For the first strict inequality use b*nu_1−nu_3=h_2 and
c*nu_2−nu_1=h_3, which give nu_1/nu_3>1/b and
nu_2/nu_3>1/(bc). For the second endpoint, substitution of Y gives
(1+bY)/[b(c−(c+1)Y)]=a.

Equations (32)-(33) uniquely select y_star∈(0,Y) with P_0(y_star)=R.
For each 0<y<y_star, strict monotonicity and the infinite upper endpoint
in (31) uniquely select k_R(y)∈(0,K(y)) with P(k_R(y),y)=R. Set
k_R(y_star)=0. This branch is continuous. At an interior y, strict
monotonicity provides fixed lower and upper brackets around the root,
which remain brackets for all nearby y. At y_star the same argument
uses a lower bracket of zero and any fixed positive upper bracket.
Also k_R(y)≤by/H_2(y)=O(y), so the branch extends with k_R(0)=0.
No monotonicity or uniqueness of the remaining nonpivot equation is used.

### Endpoint direction and closing the nonpivot equation

The limit tau=lim_(y→0) k_R(y)/y exists and is the unique number in
(0,b/h_2) satisfying

    R=F(tau),
    F(t)=1+[s_1+s_2*(1+h_3*t)/c]/(b−h_2*t).            (34)

To verify the limit, k_R(y)/y is bounded. Multiply (31) by
(1−z)w/y before taking a subsequential limit. Every such limit t solves

    (R−1)(b−h_2*t)=s_1+s_2*(1+h_3*t)/c.

The positive right side excludes t=b/h_2; this linear equation has the
unique solution

    tau=[b(R−1)−s_1−s_2/c]/[h_2(R−1)+s_2*h_3/c]>0.

Hence all subsequential limits coincide. F strictly increases on
[0,b/h_2), since its numerator increases and its positive denominator
decreases. The identities for nu give F(1/nu_1)=R_low. Therefore

    tau>1/nu_1.                                         (35)

Along this selected branch let

    G(y)=h_1*k+z−a*w*(1−z)
          +eta*k*[1−(1−z)(1−w)/(1+k)],    k=k_R(y).      (36)

This is continuous on (0,y_star]. Since k,z,w=O(y), the term multiplied
by eta is O(y²) for every fixed finite eta. Equations (34)-(35) yield

    lim_(y→0) G(y)/y
      =h_1*tau+(1+h_3*tau)/c−a*(b−h_2*tau)
      =(D/c)*(nu_1*tau−1)>0.                            (37)

At y=y_star, k=0, so G has the sign of

    y_star*[bL*y_star−D]<0,

because y_star<Y. The intermediate value theorem gives a selected
y∈(0,y_star) with G(y)=0. All of x=k/(1+k),y,z,w lie strictly between
zero and one. This proves selection for every eta>0. In particular, a
large eta can destroy monotonicity of G in k without affecting this
construction: k has already been selected uniquely from another equation.

### Complete payoff vectors and unrestricted deviations

Repeat rows (x,y,0,0), (0,0,z,0), (0,0,0,w). Put t=eta*x and

    V_A=(p,t,w/(1−w),0),
    V_C=((1−w)p+Rw, (1−w)t+aw, 0, 0),
    V_B=(v*z+(1−z)V_C,0, (1−z)V_C,1−z, 0, c*z).       (38)

Here V_C,0 and V_C,1 are coordinates; equivalently the first two B
coordinates are v*z+(1−z)*V_C,0 and (1−z)*V_C,1−z. The two selected
equations imply

    V_B,0=(p−uy)/(1−y),        V_B,1=k(h_1+eta).         (39)

At A, the pivot's Quit payoff is p and its Continue payoff is
uy+(1−y)V_B,0=p. Player 1's Quit payoff is t and its Continue payoff is
−h_1*x+(1−x)V_B,1=t. The actual A-row values for players 2 and 3 are

    [by−H_2(y)k]/(1+k)=w/(1−w),
    [−H_3(y)k−y+c*z*(1−y)]/(1+k)=0,

respectively. These expressions include the independent actual collision
rewards q_2 and q_3. The B and C recurrences in (38) follow from the
singleton vectors in (28).

At B and C, the pivot's forced-Quit payoff is at most one by (29).
Its two continuation values exceed one: (39) gives
V_B,0−1=(xi+1−u)y/(1−y)>0, and
V_C,0=(V_B,0−v*z)/(1−z)>1. Every nonpivot forced-Quit payoff outside
the exceptional pair is at most zero by (29). All displayed nonpivot
values are nonnegative, and each supported nonpivot Quit action has
value zero at its solo phase. Thus both action endpoints are bounded
above by the displayed value at every live phase, with equality for
every action in the prescribed support.

Fix an arbitrary deviator. Its opponents have positive hazards every
period regardless of its behavior. The chance of surviving K full
periods is at most rho_i^K, where

    rho_i=product_(j≠i)(1−q_j^*)<1,
    (q_0^*,q_1^*,q_2^*,q_3^*)=(x,y,z,w).

Iterating the endpoint inequalities against its complete behavioral
strategy and bounding the remainder by a finite reward/value bound
proves that its terminal payoff is at most V_A,i. Iterating the prescribed
equalities identifies (38) with the actual payoff vectors. This proves
exact terminal Nash and rules out late, history-dependent, and Never
deviations, not merely bounded or periodic deviations.

The fixed target is (p,t,w/(1−w),0), selected before any accuracy. If M
bounds all absolute table entries, moving each marginal's atoms after K
periods to Never changes total marginal mass by at most

    tau_K=(1−x)^K+(1−y)^K+(1−z)^K+(1−w)^K→0.

Product coupling bounds the prescribed-payoff change by 2M*tau_K and
every complete regret by 4M*tau_K. Hence these actual finite laws deliver
the fixed target and full approximate Nash simultaneously. The finite
pivot optimizer does no worse than the prescribed pivot marginal, so
the three finite outer laws have optimal repair value at most 4M*tau_K.
The named fixed-target terminal consumer already listed in this notebook
then yields a uniform equilibrium payoff. No strategic witness is assumed.

### Exact checks and the implementation boundary

The {0,1} product root with both hazards 1/2 gives positive premiums
xi/2 and eta/2 to both and only active players. Therefore (28)-(29)
strictly fail `HasProductLowQuittingPremium`, independently of every
other coalition entry. The exact definition and
`exists_uniformEquilibriumPayoff_of_productLowPremium` were reread in
`UniformEquilibrium/Quitting/Classification/ProductLowQuittingPremium.lean`
and `UniformEquilibrium/Quitting/Classification/Existence/ProductLowPremiumUniformPayoff.lean`.
The supplied-block consumer remains
`isUniformEquilibriumPayoff_of_isQuittingBlockCertificate` in
`UniformEquilibrium/Quitting/Cycles/BlockPeriodicProfile.lean`; it does
not select the branch (31). This is new ordinary source construction,
not a claim that the source consumer itself is new.

One rational test on the old completion has a=b=c=2, all h_j=1,
u=v=0, q_2=q_3=−1, xi=1 and

    eta=8027/101,       R=21845/6076,
    (x,y,z,w)=(1/101,1/4,13/75,49/150).

It has eta>2 and 3<R<7, outside the former premium hypothesis. The
all-child falsifiers from the preceding proof do not use an upper bound
on eta and still apply to this exact completion.

A second rational test changes genuinely independent actual rewards:
a=b=c=2, all h_j=1, u=1/2, v=−1/2, q_2=−2, q_3=−3, xi=1, and

    eta=62786/809,      R=321377/96330,
    (x,y,z,w)=(1/101,1/4,53/300,195/599),
    V_A=(5/4,62786/81709,195/404,0).

Here R_low=3<R<6=R_high. Give every other nonsingleton coalition its
participant cap s_i and give every nonparticipant payoff 37. Exhaustive
rational substitution checks all 24 pure-action inequalities and all
12 vector Bellman identities. Those large unused passive payoffs have
no effect on the equations. These are finite exact tests; the proof
above supplies every real table in the stated raw class.

Requested independent check: the pivot-branch continuity at both ends,
the sign comparison (34)-(37), and completeness of the cap argument
under the arbitrary reward freedom (29). The source-overlap claims
beyond product-low remain those explicitly established for the original
completion above; no exhaustive implementation audit is asserted for
every enlarged completion. The arbitrary canonical four-player game
remains open.

## Further question: a second rewarded pair changes the phase geometry

This is separate from the frozen pivot-first theorem. The question is
whether the same source geometry can handle arbitrary participant rewards,
which is the remaining obstruction to using that mechanism on general
canonical tables.

A minimal modification shows that merely repeating or reordering its row
types cannot do this. Take the original completion from the mutual-premium
construction, and change only r_2({2,3}) from zero to a number beta>0.
Leave every other own-quitting reward of player 2 zero, and every
own-quitting reward of player 3 zero. In particular both can always secure
zero by quitting, while player 2's Quit payoff against a pure player-3 row
of hazard w is beta*w>0.

Consider an exact periodic Bellman equilibrium whose allowed nonempty rows
are: a product row supported on {0,1}; a solo player-2 row; or a solo
player-3 row. Empty rows are allowed. Suppose some player-3 row has positive
hazard. Its player-3 value equals zero by supported-action equality. An
immediately preceding nonempty row cannot be supported on {0,1}: every
outcome of that row harms player 3 strictly, and its continuation value
at the player-3 row is zero, so its actual value is negative. Quitting
there guarantees zero, contradicting equilibrium. It cannot be a positive
player-2 row either: player 2's value at the ensuing player-3 row is at
least beta*w>0, while quitting alone at the player-2 row pays zero. Its
supported Quit action therefore loses to Continue. Empty rows between
these two rows merely copy the relevant value.

Thus a positive player-3 row can only follow another such row in the
cyclic list of nonempty rows. Finiteness forces every nonempty row to be
a player-3 row. That remaining profile gives player 2 terminal payoff
−1, while joining at the initial positive row gives a positive payoff,
so it is not Nash either. The whole row grammar is therefore impossible
for an exact periodic Bellman equilibrium in which player 3 ever quits.

This is an internal architecture boundary, not a game counterexample and
not a claim about all approximate profiles. It explains why arbitrary
positive participation rewards cannot be absorbed by more copies of the
same three row types. A next producer must permit additional simultaneous
owners or supply a different, possibly nonperiodic approximation mechanism.
No assertion is made here that such a larger producer is impossible.

Concrete next question: construct the additional simultaneous-owner
phase from this single changed pair reward, keeping a,b,c,h and the
singleton comparison matrix fixed. This changes actual strategic
interactions without replacing the source problem by an interval exercise.

## Further producer: diffuse only the solo phases

Status: ordinary mathematics with independent CODEX_BROUWER and CODEX_MORSE
PASS reviews, included in the frozen joint/solo export. It resolves the immediately
preceding added-pair problem by approximation. The limiting target stays
fixed. No extra simultaneous-owner phase is needed for this enlargement.

### A weaker raw-table criterion

Keep ALL numerical assumptions and the five prescribed vectors (28) of
the pivot-first construction. Replace the participant cap (29) by only
the following six inequalities:

    r_2({0,2})≤0,  r_2({1,2})≤0,  r_2({0,1,2})≤0,
    r_3({0,3})≤0,  r_3({1,3})≤0,  r_3({0,1,3})≤0.      (40)

Every other coordinate of every other nonsingleton coalition is arbitrary
and finite, including r_2({2,3}), r_3({2,3}), the pivot's participant
payoffs on {0,2} and {0,3}, player 1's participant payoffs on {1,2}
and {1,3}, and the entire four-player coalition vector.

**Theorem draft.** Every such table has one fixed uniform equilibrium
payoff and actual finite outer stopping laws with arbitrarily small full
regret and pivot-repair value. The theorem asserts arbitrarily accurate
terminal equilibria, rather than an exact finite periodic equilibrium.
The same {0,1} witness proves strict product-low failure throughout this
larger class. No class-wide F/J exclusion is claimed.

### Construction and preserved actual payoff

Equations (30)-(37) depend only on the five vectors (28). They therefore
select the same x,y,z,w and values V_A,V_B,V_C for this new table. More
formally, cap the otherwise unspecified participant rewards at s_i to
obtain an auxiliary table satisfying (29), apply that producer, and retain
its rates. The original and auxiliary tables agree at every prescribed
outcome {0}, {1}, {0,1}, {2}, {3}, so their actual vector recurrences
agree. No auxiliary-game incentive conclusion is transferred silently.

For a positive integer n put

    z_n=1−(1−z)^(1/n),       w_n=1−(1−w)^(1/n).

Repeat one {0,1} row with hazards x,y, then n solo player-2 rows of
hazard z_n, then n solo player-3 rows of hazard w_n. All choices remain
independent and use only the public date and survival. Each solo block
has exactly its original aggregate hazard, because

    (1−z_n)^n=1−z,           (1−w_n)^n=1−w.

Thus the distribution of the terminal coalition is unchanged for every n,
and the ACTUAL initial payoff is always the same vector

    V_A=(1+xi*y, eta*x, w/(1−w), 0).                     (41)

Within the player-2 block, if rho is the remaining aggregate hazard,
the value is rho*r({2})+(1−rho)*V_C, with 0≤rho≤z. It lies on the
line segment between V_B and V_C. Within the player-3 block the analogous
value lies on the segment between V_C and V_A. All these values retain
the coordinatewise floor s=(1,0,0,0). The owner has value zero throughout
its own solo block. The root policy and every player's pure-Continue
transport are exact at every refined date, including the joint row.

### One immediate-Quit error controls the whole deviation

Define the finite collision excess bound

    C=max({0} union
      { (r_i({i,j})−s_i)_+ : j∈{2,3}, i≠j }).          (42)

At a solo j-row of hazard delta, a different player's forced-Quit
payoff is exactly

    s_i+delta*(r_i({i,j})−s_i)
       ≤s_i+C*delta≤V_i+C*delta.

The solo owner has forced-Quit payoff equal to its value zero. At the
{0,1} row, the two supported players retain their exact action equalities.
Conditions (40), together with their zero singleton rewards, bound both
outsiders' forced-Quit payoffs by zero, hence by their displayed values.
Consequently every immediate-Quit endpoint is at most its value plus

    e_n=C*max(z_n,w_n)→0,                                (43)

while every pure-Continue endpoint equals its value exactly.

These local inequalities control one COMPLETE behavioral deviation with
error e_n, not a sum of errors over dates. One proof adds e_n to every
value. If Continue has immediate expected reward a and opponent survival
probability q≤1, exact transport says a+q*V_next=V, so
a+q*(V_next+e_n)≤V+e_n. Quit is also bounded by V+e_n. Thus V+e_n is
a Bellman supersolution for every deviating action. Iterating against
any behavioral strategy and letting the finite remainder vanish gives
terminal payoff at most V_A,i+e_n.

The remainder vanishes uniformly over that player's deviations because
its opponents still have the same per-period survival product as before:
the joint phase is unchanged, and each refined solo block has unchanged
aggregate survival. That product is strictly below one. All rewards and
values are bounded. Equivalently, the error is charged only when the
deviator first Quits while the game is live, an event occurring at most
once. There is no accumulation over repeated refined periods.

This proves full terminal e_n-Nash and exact delivery of (41) for every n.
The target is chosen before n or the requested accuracy.

### Finite laws and uniform horizons

For each n censor all four marginal laws after K refined periods. The
total changed marginal mass is still bounded by

    tau_K=(1−x)^K+(1−y)^K+(1−z)^K+(1−w)^K,

independently of n. If M bounds the absolute entries of the ORIGINAL
table, product coupling gives full terminal regret at most

    e_n+4M*tau_K,

and distance at most 2M*tau_K from the fixed target (41). Choose n first
and K second for the desired accuracy. These are actual finite laws on
one common finite menu; the optimal pivot repair is bounded above by the
same full regret. The fixed-target terminal consumer supplies one profile
and one threshold covering every sufficiently long horizon at that accuracy.
No common threshold across different accuracies is required or asserted.

### Source correspondence and exact boundary check

Singleton refinement and the one-error comparison are EXISTING methods,
not new principles. The sources read for this argument are:

- `exists_uniform_quittingMeshScale` in
  `UniformEquilibrium/Quitting/Terminal/TargetTail/InfiniteSingletonMesh.lean`;
- `singletonArcCycle_isTerminalNash_and_hasValue` in
  `UniformEquilibrium/Quitting/Cycles/SingletonArcCycle.lean`;
- `quittingRootSequenceHazardTerminalValue_le_add_of_quitError_exactContinue`,
  `QuittingInfinitePathQuitErrorCertificate.isεAsymptoticNash_and_delivers`,
  and `isUniformEquilibriumPayoff_of_arbitrarily_small_infinitePath_quitError`
  in `UniformEquilibrium/Quitting/Paths/InfinitePathSupersolution.lean`.

The last file's exact certificate retains root policy evaluation, exact
Continue transport, a uniform Quit cap, bounded values, and vanishing
opponent survival; all are produced explicitly above. The first two
files refine supplied singleton paths. They do not produce the present
mixed joint/solo path from the raw data (28),(30),(40). The contribution
here is the enlarged actual-data source using the pivot-first construction,
not a new supplied-path compiler.

For the concrete modification r_2({2,3})=beta>0 of the original completion,
all other formerly capped participant entries remain at their caps.
Then C=beta, and (43) gives e_n≤beta*max(z_n,w_n); the sharper bound
e_n=beta*w_n is immediate because only player 2's join at a player-3
microstage changes. The exact row-grammar impossibility in the preceding
section and these approximate profiles are consistent: each finite n
retains a positive local join gain, while its full gain is bounded by a
number tending to zero. This is an explicit repair of that failed exact
route, not numerical evidence.

Next independent check: verify that (40) lists every undiffused outsider
coalition, that the refined values retain exact Continue transport for
all four players, and that the terminal error is (43) rather than an
accumulated per-period error. Arbitrary participant rewards at the six
undiffused outsider coordinates remain outside this producer.

## Complementary pair/passive orderings with the two-core mechanism

Status: new ordinary proof draft, not independently reviewed and not part
of the frozen export. This tests the gap between the explicit joint/solo
producer and the two-core boundary-return mechanism in Section 10 of
`CODEX_MORSE__GLOBAL_QUITTING_OBSTRUCTION.md`.

The two mechanisms initially had different pivot comparisons at the same
pair {0,1}. The explicit producer assumed the passive singleton u<1,
while the two-core theorem applies when u>1+xi, the pivot's pair reward.
The intermediate ordering 1≤u≤1+xi is not by itself an obstruction to
the explicit rate selection. The precise repair below RETAINS the full
R interval; it does not prove coverage of every fixed-table middle slice.

### The actual selector only needs u≤1+xi

Keep the raw vectors, six outsider caps, v<1, positive a,b,c,h, D>0,
xi,eta>0, and q_2,q_3≤0 from the diffuse producer. Allow u to be any
real number with u≤1+xi. Define s_1=1−u, s_2=1−v and the SAME
R_low,R_high as before, and ASSUME R_low<R<R_high. This interval is
no longer automatically nonempty for arbitrary u.

The interval's strict ordering and identity (30) give

    (c*s_1+s_2)h_1+s_1*h_3>0.                           (44)

If s_1≥0 then c*s_1+s_2>0 immediately. If s_1<0, (44) gives
c*s_1+s_2>−s_1*h_3/h_1>0. Thus in both cases

    c*s_1+s_2>0.                                       (45)

This is the positivity actually needed for the pivot branch at k=0.
In particular P_0(y)−p has the positive bracket
c*s_1+s_2+(c+1)xi*y, so P_0 is still strictly increasing. Its zero
endpoint is strictly below R_low because exact subtraction yields

    R_low−P_0(0)
      =[h_2(c*s_1+s_2)+b*s_2*h_3]/(bc*nu_3)>0.         (46)

It is not enough to repeat the earlier claim p−u>0: that claim can now
be false. Instead put A0=(p−u)y/(1−y). For fixed y,

    d/dz [(A0+(p−v)z)/(1−z)]
      =(A0+p−v)/(1−z)²,
    A0+p−v
      =[s_2(1−y)+(1+xi−u)y]/(1−y)>0.                   (47)

The strict positivity follows from s_2>0, y<1, and u≤1+xi. Moreover
A0+(p−v)z is positive at k=0 by (45), and increases with z because
p−v>0. Since z increases and w decreases with k, (47) proves that
P(k,y) still strictly increases from P_0(y) to infinity. Thus y_star
and the continuous unique pivot branch are produced exactly as before.

The endpoint function F in (34) also remains strictly increasing: its
numerator at zero is (c*s_1+s_2)/c>0, its slope is positive, and its
positive denominator strictly decreases. Equation (46) gives tau>0,
and F(1/nu_1)=R_low still implies tau>1/nu_1. Hence the sign crossing
of G in (37) is unchanged for every eta>0.

Finally the pivot's continuation floor at B is now

    V_B,0−1=(1+xi−u)y/(1−y)≥0.                          (48)

Equality is harmless: the pivot can Continue at a value equal to its
singleton. At C its value is strictly above one since v<1 and z>0;
at A it is p>1. All nonpivot calculations are unchanged. The refined
values are still above their singleton floors, and the same one-error
supersolution proves full terminal approximate Nash and the same fixed
target. This completes the extension to u≤1+xi under the explicitly
retained interval assumption.

An exact intermediate fixture has

    a=b=c=2, all h_j=1, u=3/2, v=−3,
    xi=1, eta=17/11, q_2=q_3=−1, R=2095/368.

Then R_low=9/2<R<7=R_high. The exact rates are
(x,y,z,w)=(1/11,1/4,7/30,4/15), with the same nonpivot values as
the first positive-premium fixture, and pivot values

    V_A,0=5/4,       V_B,0=7/6,       V_C,0=56/23.

This has p−u=−1/4<0, so it tests the changed monotonicity argument
rather than accidentally staying in the former positive-numerator case.
For comparison, keeping a=b=c=2,h=1,v=0,R=4 forces u<3/4 from
R<R_high=7−4u. The theorem does NOT bridge that fixed slice's entire
middle ordering just by changing the displayed bound on u.

### One raw family on both sides of the pair reward

To compare the two mechanisms on the SAME reward data, additionally require
that players 2 and 3 have constant participant rewards zero, while players
0 and 1 have nonnegative participant premiums on every coalition. Leave
all nonparticipant rewards not fixed by the five vectors arbitrary.
These conditions imply the six undiffused outsider caps, and so the
explicit producer above applies for u≤1+xi WHEN R_low<R<R_high.
For u>1+xi, the two-core theorem applies directly with core {0,1} and
designated player 0, because

    r_0({0,1})=1+xi<u=r_0({1}).

That second branch needs no restriction on R. It consumes arbitrary core
participation premiums rather than an assumed selected child or root.
The precise covered union is therefore

    {u≤1+xi and R_low<R<R_high} union {u>1+xi},

under the shared table assumptions just stated. No claim is made for
u≤1+xi outside the interval, nor for arbitrary participant rewards in
the second branch. This is complementary coverage of concrete raw
regions, not an assertion that those regions exhaust all singleton data.

For a completely explicit connected test family, fix

    a=b=c=2, h_1=h_2=h_3=1, v=−3,
    xi=eta=1, q_2=q_3=−1,
    R=(19−5u)/2,                u arbitrary real.

Use the five vectors (28). On every other nonsingleton coalition use
the original cyclic completion: pivot reward one when it participates
and R*1_(3∈S) otherwise; each nonpivot has own-quitting reward zero,
reward −1 when the pivot quits without it, and cyclic outsider reward
2*1_(pred∈S)−1_(succ∈S) otherwise. The singleton overrides u and v
remain as specified in (28).

Here R_low=6−u and R_high=13−4u. For every u≤2,

    R−R_low=R_high−R=(7−3u)/2≥1/2>0,

so the extended explicit producer applies, including the whole interval
1≤u≤2. For every u>2, the two-core theorem applies. Thus this one
fully specified family has UE for every real u. The boundary u=2 is
handled directly by (48), with no reward-closure argument.

This is a test of how the two source mechanisms fit together, not a separate
parameter-range export. The slice v=0,R=4,1≤u≤2 lies outside both displayed
regions but is ALREADY consumed by the existing passive-inverse criterion:
its pivot row times the child inverse is

    ((2u+9)/7, (4u−3)/7, (u+1)/7),

which is entrywise positive throughout that slice. Thus it is not a live
existence gap. The fixture with v=−3,R=2095/368 above instead has a negative
middle inverse weight (R−7)/7. The next section identifies the whole actual
residual interval and constructs across it, without fixing R artificially.

## Quadratic nonpivot selection and the complete R axis

Status: ordinary proof with independent CODEX_MORSE and CODEX_BROUWER PASS
reviews, not Lean-checked. The older frozen export is unchanged. This section solves the
mutual-pair-preference residual of the same actual joint/solo table rather
than merely weakening an interval constant. The new producer is the
quadratic selector; two existing source criteria close its outer regions.

### Precise raw class and quantifiers

Take the four singleton vectors and the pair vector (28), with

    a,b,c,h_1,h_2,h_3>0,     D=abc−1>0,
    xi,eta>0,              q_2,q_3≤0,
    v<1,                   u≤1+xi,
    R arbitrary real.

Require only the SAME six undiffused outsider caps:

    r_2({0,2}), r_2({1,2}), r_2({0,1,2})≤0,
    r_3({0,3}), r_3({1,3}), r_3({0,1,3})≤0.             (49)

All entries not specified by (28) or (49) are arbitrary finite real
numbers. In particular, players 2 and 3 may have positive participant
premiums at their joint coalition, and players 0 and 1 may have arbitrary
participant rewards at the refined solo phases. The pair {0,1} has two
strictly positive participant premiums and can strictly harm both outsiders.

CLAIM: every table in this class has a uniform-equilibrium payoff against
all complete behavioral deviations in the original four-player game.
The constructive middle branch below has one fixed target, selected before
the accuracy. Its independent live-date hazards use only the public clock
and private independent action randomization. Refinement and censoring give
one profile and threshold for each accuracy; no extra public coin or
restriction on the deviator is imposed. The source exits give existence
on the other branches, not necessarily the same target or controller.

Retain nu,L,s_1=1−u,s_2=1−v and R_low from the preceding sections.
Now s_1 may be negative; no condition on c*s_1+s_2 is assumed.

### The three exact passive thresholds

For the child on players 1,2,3, the singleton matrix and its inverse are

    A = [[0,−1,a], [b,0,−1], [−1,c,0]],
    A^(-1) = [[c,ac,1], [1,a,ab], [bc,1,b]]/D.

Every inverse entry is strictly positive. Define

    T_1 = 1+(c*s_1+s_2)/(bc),
    T_2 = 1+ac*s_1+a*s_2 = R_high,
    T_3 = 1+(s_1+ab*s_2)/b,
    T_pass = max(T_2,T_3).

The pivot singleton-difference row multiplied by A^(-1) is exactly

    [bc*(R−T_1), R−T_2, b*(R−T_3)]/D.                (50)

Since s_2>0,

    T_3−T_1 = D*s_2/(bc)>0,
    T_2−T_3 = D*s_1/b.

Thus all three literal inverse weights are nonnegative exactly when
R≥T_pass. This includes equality; no strict outside weight is needed.

The lower threshold is strictly below T_pass. If s_1≥0, use

    T_2−R_low = [(c*s_1+s_2)h_1+s_1*h_3]/nu_3>0.

If s_1<0, instead use

    T_3−R_low = [s_2*h_1−s_1*h_2/b]/nu_3>0.          (51)

Finally define the actual upper endpoint of the explicit construction,

    R_top=P_0(Y)=T_2+xi*D/b,        Y=D/[b(ac+a+1)].

For s_1≥0, R_top>T_pass=T_2. For s_1<0,

    R_top−T_pass = D*(1+xi−u)/b≥0.                   (52)

Consequently R_low<T_pass≤R_top throughout the asserted raw class.

### Solve the nonpivot equation by its quadratic numerator

For 0<y<Y keep H_j,K,z,d,w from the pivot-first construction, but do
NOT select k from the pivot equation. Define G(k,y) by (36), now treating
k as free in [0,K(y)]. All denominators extend positively to this closed
interval: d=1+k+by−H_2*k≥1+k, and c(1−y)>0. At the right endpoint,
either w=0 or z=1. The variables satisfy 0≤z,w≤1 there.

Write

    C=c(1−y), E=c−(c+1)y,
    d_0=1+by, d_1=1−H_2(y),
    Q(k,y)=C*d*G(k,y)=alpha(y)k²+beta(y)k+gamma(y).

Exact expansion gives

    alpha = h_1*C*d_1+H_3*d_1−a*H_2*H_3
              +eta*(C*d_1+H_3),
    beta  = h_1*C*d_0+H_3*(d_0+ab*y)+y
              +H_2*(a*E−y)+eta*y*(Cb+1),
    gamma = y*(bL*y−D).                               (53)

There is no sign assumption on alpha, and alpha=0 is allowed. The
linear coefficient is strictly positive on the entire closed interval
0≤y≤Y, because every displayed term is nonnegative and

    a*E−y=ac−L*y≥ac−L*Y=1/b>0.

For 0<y<Y, Q(0,y)=gamma<0. At k=K(y), G is strictly positive:
its term −a*w*(1−z) vanishes, h_1*k+z>0, and
eta*k*[1−(1−z)(1−w)/(1+k)]≥0. Hence Q(K(y),y)>0.

A polynomial of degree at most two with these endpoint signs has exactly
one zero in (0,K(y)). Indeed, a linear polynomial has at most one; for a
quadratic, two distinct roots in that interval would make the signs at
the two endpoints equal, and a double root cannot change the sign. The
actual zero is simple. This argument covers a vanishing leading
coefficient and does not assert monotonicity of G away from its root.

The discriminant Delta=beta²−4*alpha*gamma is therefore strictly positive
for 0<y<Y. It is also positive at y=0,Y, where gamma=0 and beta>0.
The unique admissible zero has the expression

    k(y)=−2*gamma(y)/[beta(y)+sqrt(Delta(y))].           (54)

If alpha=0, this is just −gamma/beta. If alpha≠0, rationalization of
the quadratic formula gives the smaller positive root whenever two
positive roots exist; the endpoint signs put that root inside (0,K).
Formula (54) is continuous on [0,Y], has k(0)=k(Y)=0, and is strictly
inside the admissible interval at every interior y. Thus the required
continuous selector is produced from raw data, not supplied as a witness.

### Both endpoint limits and the pivot equation

At y=0,

    beta(0)=c*h_1+h_3+ac*h_2=D*nu_1,
    gamma(y)/y→−D.

Formula (54) therefore gives

    k(y)/y→1/nu_1,
    z(y)/y→nu_2/nu_1,
    w(y)/y→nu_3/nu_1>0.                               (55)

The last two follow directly from the formulas for z,w and
c*nu_2−nu_1=h_3, b*nu_1−nu_3=h_2. At the other endpoint, k(Y)=0,
and the limiting z,w are strictly between zero and one because
0<Y<c/(c+1).

For 0<y≤Y define R(y)=P(k(y),y) using (31). Its denominator is positive,
and it is continuous. Even if its numerator is negative, no sign or
monotonicity of P is used. Using (55) cancels the common order-y factor
and gives the removable endpoint value

    R(0)=1+(s_1*nu_1+s_2*nu_2)/nu_3=R_low.

At y=Y, equation (33), which is an algebraic identity without the former
sign assumptions, gives R(Y)=R_top. The intermediate value theorem now
selects an interior y for EVERY

    R_low<R<R_top.                                    (56)

No uniqueness or monotonicity of R(y) is asserted. Equations G=0 and
P=R are both exact at the selected point. Set x=k/(1+k); all four
hazards x,y,z,w lie strictly between zero and one. In particular, every
R in the residual interval (R_low,T_pass) is produced by (52).

### Payoff floors, all deviations, and the six-cap boundary

The value vectors remain precisely (38)-(39), with the unambiguous form

    V_A=(p,eta*x,w/(1−w),0),
    V_C=((1−w)p+Rw,(1−w)eta*x+aw,0,0),
    V_B=(v*z+(1−z)V_C,0, (1−z)V_C,1−z,0,c*z),
    p=1+xi*y.

Here the first two B coordinates mean v*z+(1−z)*(V_C)_0 and
(1−z)*(V_C)_1−z. The exact equations give

    (V_B)_0=(p−uy)/(1−y),
    (V_B)_1=k(h_1+eta).

All nonpivot displayed values are nonnegative. The pivot has

    (V_A)_0>1,
    (V_B)_0−1=(1+xi−u)y/(1−y)≥0,
    (V_C)_0=[(V_B)_0−v*z]/(1−z)>1,                    (57)

where the last strict inequality uses v<1 and z>0. These bounds do not
assume R>1, and equality at u=1+xi is harmless. The Bellman equations
and exact Continue endpoints are algebraic, so they remain valid even
when c*s_1+s_2≤0 or p−u<0.

At the undiffused joint row, the only outsider Quit coalitions are exactly
the six in (49), together with each outsider's singleton of value zero.
Their expectations are at most zero, bounded by the displayed values.
Both participating players are exactly indifferent there.

Refine each solo phase j=2,3 into n microstages as in (43), with
z_n=1−(1−z)^(1/n), w_n=1−(1−w)^(1/n). Intermediate vectors interpolate
between the corresponding endpoints, preserve all singleton floors, and
have exact Continue transport. Let

    C_join=max(0, r_i({i,j})−s_i : j∈{2,3}, i≠j),
    e_n=C_join*max(z_n,w_n),         s=(1,0,0,0).

Every pure-Quit payoff is at most its displayed value plus e_n, including
arbitrary participant premiums at the refined phases. Adding e_n to all
continuation coordinates is one global Bellman supersolution, because
an exact Continue transition with opponent survival q≤1 contributes only
q*e_n≤e_n. This charges a deviation once, not once per microstage. For
each deviator, the opponents' per-period survival product is the unchanged
strictly subunit product of their original factors (1−x),(1−y),(1−z),(1−w).
The bounded remainder thus vanishes against every complete behavioral
deviation. The full terminal regret is at most e_n→0, with the SAME exact
on-path target V_A for every n.

Censoring after K refined periods changes marginal mass by at most

    tau_K=(1−x)^K+(1−y)^K+(1−z)^K+(1−w)^K.

For an absolute reward bound M, full terminal regret is at most
e_n+4M*tau_K and target error at most 2M*tau_K. Choose n and then K at
the requested accuracy. The existing fixed-target terminal consumer gives
the asserted uniform-horizon conclusion. No new compiler is being claimed.

### Exact source exits on the entire complementary R region

The full singleton matrix is

    M_full = [[0,−s_1,−s_2,R−1],
              [−h_1,0,−1,a],
              [−h_2,b,0,−1],
              [−h_3,−1,c,0]].

For R≠R_low it is R0. To prove this, let (t,z) be a nonnegative homogeneous
LCP solution. If t>0, nonnegativity of the three child residuals forces
all three coordinates of z strictly positive, cyclically. Complementarity
then gives z=t*nu. The pivot residual is
t*nu_3*(R−R_low) and must be zero, impossible. If t=0 and z≠0, the cyclic
negative edges force all three child coordinates positive; complementarity
gives A*z=0, impossible since det A=D>0. Thus only the zero solution exists.

For R<R_low, put delta=nu_3*(R_low−R)>0 and choose q_0>delta. At the
test offset (q_0,−h_1,−h_2,−h_3), every LCP root has all child coordinates
positive and hence z=(1+t)*nu. Its pivot residual is

    q_0−delta*(1+t).

Exactly two roots exist: t=0, with strict inactive residual q_0−delta>0,
and t=q_0/delta−1>0, with all coordinates active. Their active principal
determinants are D>0 and

    det M_full = D*nu_3*(R−R_low)=−D*delta<0,

respectively. Both roots satisfy the precise strict-inactive and nonsingular
conditions of the standard LCP root-sum formula. Their signs sum to zero,
so the R0 degree is zero. The existing degree-not-one exit supplies UE,
independently of every nonsingleton completion.

For R=R_low, the strictly positive vector (1,nu) is a nonzero homogeneous
LCP solution. The existing four-player noUE implication forces the original
singleton matrix to be R0, so its contrapositive supplies UE at this
boundary. No limiting strategy or closure assertion is needed.

For R≥T_pass, equation (50) gives the exact nonnegative passive inverse
weights, while A^(-1) is strictly positive. The existing raw three-child
inverse theorem supplies UE, with arbitrary unused reward entries. Equality
R=T_pass is included literally by its weak outside-weight hypothesis.

These three source cases and the constructive middle case partition ALL
real R. The open endpoints in (56) leave no unhandled boundary. The new
math is the actual joint/solo producer on (R_low,T_pass); it is not a new
proof of the pre-existing exits.

The declarations and precise source files inspected for these exits are:

- `exists_finset_r0Degree_eq_sum_sign_det` in
  `MathUE/LinearProgramming/R0DegreeSum.lean`;
- `exists_uniformEquilibriumPayoff_of_r0Degree_ne_one` in
  `UniformEquilibrium/Quitting/Classification/LCP/SingletonDegreeCriterion.lean`;
- `finFour_singleton_r0Degree_eq_one_of_no_uniformPayoff` in
  `UniformEquilibrium/Diagnostics/Quitting/FinFourSingletonDegreeCriterion.lean`;
- `PassiveRowInverseCriterion.inverseWeight`, `factorization`, and
  `exists_uniformEquilibriumPayoff_of_raw_nonnegativeInverse_triple` in
  `UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/RawPassiveRowInverseCriterion.lean`.

The actual target/deviation consumer is the same terminal/mesh/supersolution
source already read and recorded in the diffuse section, not a stronger
equilibrium notion. These are static declaration checks, not new Lean builds.

### Exact stress tests outside the old interval

Take a=b=c=2, h_1=h_2=h_3=1, xi=1, eta=17/11, q_2=q_3=−1,
u=7/4, v=0 and R=685/368. Then

    c*s_1+s_2=−1/2,
    R_low=5/4 < R < 21/8=T_pass,
    R_high=T_2=0,       R_top=7/2.

Thus the old interval R_low<R<R_high is EMPTY, and even the preceding
intermediate sign argument is unavailable. The exact selected hazards
are nevertheless

    (x,y,z,w)=(1/11,1/4,7/30,4/15),
    V_A=(5/4,17/121,4/11,0),
    V_B=(13/12,14/55,0,7/15),
    V_C=(65/46,7/11,0,0).

At y=1/4, the quadratic coefficients are

    (alpha,beta,gamma)=(−5/11,387/44,−7/8),

and k=1/10 is its admissible root. This tests a negative leading
coefficient, not an accidentally monotone quadratic. A rational check on
the original cyclic completion verified all twelve exact Continue
identities and all twelve pure-Quit bounds. The same hazard and value
calculations with arbitrary (49)-admissible completions use refinement
where their unused participant premiums exceed the singleton floor.

The three passive weights in this fixture are exactly

    (363/644, 685/2576, −281/1288).

The negative last weight excludes the selected child inverse exit, rather
than merely lying outside our earlier proof range. Each other three-player
principal singleton matrix has a nonzero row with all entries nonpositive,
which rules out a nonnegative inverse. The full matrix is R0 of degree one
by the same unique-positive-child root calculation at offset (1,−1,−1,−1);
here R>R_low makes its pivot residual strictly positive, so only the
inactive-pivot root exists and its determinant is D>0. Its full inverse
has a negative entry because its pivot inverse row is −(50) divided by
the positive Schur complement nu_3*(R−R_low). Product-low fails at the
product root with only players 0 and 1 mixing, since both actual pair
premiums are strictly positive. This is a targeted source separation,
not a claim that every arbitrary completion fails every possible gate.

For an exact zero-leading-coefficient test, keep the same a,b,c,h,xi,u,v,q
but take eta=2. At y=1/4, alpha=0 and (beta,gamma)=(37/4,−7/8).
Formula (54) gives

    (x,y,z,w)=(7/81,1/4,17/74,10/37),
    R=12509/6840.

This is also strictly inside (R_low,T_pass). It tests the linear
degeneracy explicitly; the proof does not divide by alpha.

### One full parameter plane under the shared two-core assumptions

If additionally every participant reward of players 2 and 3 equals zero,
and every participant reward of players 0 and 1 is at least its singleton
(one and zero respectively), the six caps (49) hold automatically. All
other nonparticipant rewards remain arbitrary subject to (28).

Under these SHARED conditions and v<1, the present theorem handles
every u≤1+xi and every real R. For u>1+xi, the independently reviewed
two-core strict-leave theorem handles the SAME tables, with core {0,1}
and r_0({0,1})=1+xi<u=r_0({1}). It imposes no restriction on R.
Thus their union is the ENTIRE plane (u,R)∈R², for every fixed choice of
the remaining stated parameters and every admissible nonsingleton
completion. This is not a universal normalized-table result: the cyclic
three-child structure, negative core-to-child singleton entries, v<1,
and the shared participation assumptions remain genuine raw restrictions.

Next requested check: independently falsify the quadratic selector at both
endpoints and at alpha=0, the exact six-cap all-deviation adapter, and the
degree/passive source stitching. A broader constructive question is whether
arbitrary normal singleton sign geometries admit an analogous joint row
whose remaining balance equations have this one-root crossing structure.

## A positive-gap obstruction to the one-joint/two-solo-block architecture

Status: separate ordinary proof candidate, not independently reviewed. The
reviewed quadratic theorem above is unchanged. This is NOT a counterexample
to four-player UE. It is a strict expressiveness boundary for the entire
periodic architecture used by that producer, including all accuracy-dependent
hazards and arbitrarily fine solo blocks, not merely its exact period-three
Bellman equations.

### An explicit table and the precise restricted profile class

The table has singleton vectors

    r({0})=(1,−1,−1,−1),
    r({1})=(2,0,2,−1),
    r({2})=(2,−1,0,2),
    r({3})=(0,2,−1,0),
    r({0,1})=(2,1,−1,−1).                              (58)

Here is a full completion, with an optional parameter beta≥0. Set the
pivot payoff to one whenever it participates, except for its pair payoff
r_0({0,1})=2. When the pivot does not participate, set its reward to zero
except at the singleton coalitions {1} and {2}, where it is two.
For each nonpivot j, its participant reward is zero except
r_1({0,1})=1 and

    r_2({2,3})=r_3({2,3})=beta.

A nonparticipating nonpivot receives −1 if 0 participates; otherwise its
reward is 2*1_(pred(j) participates)−1_(succ(j) participates), with the
cycle 1→2→3→1. These rules specify all fifteen reward vectors and agree
with (58). All participant premiums are nonnegative.

For beta=0, the table has constant-participant outsiders 2,3 and the weak
leave equality r_0({0,1})=r_0({1})=2. It therefore has a fixed-target UE
by the independently reviewed two-core weak-leave theorem. For beta>0,
both disjoint pairs {0,1} and {2,3} are premium traps and their union is
the full greatest core; no existence conclusion for that variant is
being inferred from the core-size-two theorem.

The restricted profile class consists of infinite repetition of:

1. one simultaneous date at which only players 0 and 1 may Quit, with
   fixed hazards x,y;
2. a finite block containing only player-2 hazards, of arbitrary length
   and arbitrary date-dependent probabilities;
3. a finite block containing only player-3 hazards, likewise arbitrary.

The blocks and all hazards may be chosen separately for each requested
accuracy. Let z,w be the aggregate Quit probabilities of the two solo
blocks. Empty or zero blocks can be represented by an all-Continue date.
The full repeated profile uses private independent randomization and no
correlating device. A deviator is unrestricted; in particular it may wait
until a particular block, skip a whole block, or Never quit thereafter.

CLAIM: there is delta>0 such that EVERY profile in this class has full
terminal exploitability at least delta in the beta=0 table. The SAME
delta works for every beta≥0. Thus the architecture cannot produce terminal
approximate Nash profiles at all errors, even though the beta=0 game has UE.

The phase order is essential to the class being excluded. No claim here
excludes arbitrary periodic policies, several joint phases, nonperiodic
profiles, random phase entry, or every conceivable independent stopping law.

### Phase values and elementary deviation consequences

Let V_A,V_B,V_C be prescribed terminal values at entry to the joint date,
the player-2 block, and the player-3 block. On-path coalitions are only
{0},{1},{0,1},{2},{3}; in particular no on-path coalition contains both
2 and 3. The values depend only on x,y,z,w, not on the solo blocks'
lengths or subdivisions. If at least one aggregate hazard is positive,
absorption occurs almost surely under repetition, and these values are
the unique bounded solutions of the three aggregate Bellman equations.

At every phase the pivot can Quit for at least one, and every nonpivot
can Quit for at least zero. At A, players 2 and 3 get exactly zero by
forced Quit. At B, player 1 gets exactly zero by forced Quit. At C,
player 2 gets zero or beta by forced Quit, hence at least zero. The
deviator can follow the prescribed profile until reaching that phase and
then take this action. Thus whenever the phase-entry survival probability
is bounded away from zero, vanishing initial full regret forces the
limiting phase values to lie above the singleton vector s=(1,0,0,0).

A solo owner can instead Continue through its entire block and then
resume its prescribed behavior. For player 2 this changes its conditional
value from V_B,2=(1−z)V_C,2 to V_C,2. For player 3 it changes
V_C,3=(1−w)V_A,3 to V_A,3. These deviations are legal regardless of
how finely a block has been subdivided. They will recover the exact
owner equalities in a positive-hazard limit; no per-microstage error is
summed.

### No nonzero aggregate-hazard limit can have vanishing regret

Suppose toward a contradiction that restricted profiles have full terminal
regrets tending to zero. All-zero profiles have pivot deviation gain one,
so they can be omitted. By compactness, pass to a subsequence whose
aggregate hazards converge to (x,y,z,w). First suppose this limit is not
the zero vector. The aggregate absorption probability then has a positive
limit, so all three phase-value vectors converge by their explicit
Bellman formulas. Write the limits again as V_A,V_B,V_C.

If x=1 or y=1, phase A absorbs surely and player 3's value is −1,
whereas its immediate Quit payoff is zero. Hence x,y<1. Phase B is
therefore reached with limiting probability (1−x)(1−y)>0. If z=1,
player 1's B-value is −1, whereas immediate Quit there gives zero.
Thus z<1, and phase C also has positive limiting entry probability.
If w=1, player 2's C-value is −1, whereas immediate Quit there gives
at least zero. Thus w<1 as well. All phase-entry probabilities are now
bounded away from zero, and every limiting phase value is at least s.

Suppose x>0. The pivot's supported Quit and Continue actions at A must
be indifferent in the limit, since 0<x<1. Its Quit endpoint is 1+y,
and its Continue endpoint is 2y+(1−y)V_B,0. Since y<1, this forces

    V_B,0=1.

But the player-2 block gives

    V_B,0=2z+(1−z)V_C,0≥1+z.

Hence z=0. The player-3 coordinate of the remaining Bellman equations
then reads

    [1−(1−x)(1−y)(1−w)] V_A,3=−x−y+xy<0.

Its positive left coefficient forces V_A,3<0, a contradiction. Therefore
x=0 in every possible nonzero limit.

Only the cyclic singleton exits 1,2,3 remain. Their three hazards must
all be positive. If y=0 and w>0, player 2 receives a strictly negative
terminal payoff; if y=w=0 and z>0, player 1 does. Once y>0, absence of
z makes player 3 strictly negative; once z>0, absence of w makes player
1 strictly negative. These statements follow directly from the two
available singleton payoffs for the indicated receiver. None can hold
under the phase-value floors.

At A, player 1's positive interior hazard then forces
V_A,1=V_B,1=0. The block-skipping deviations and nonnegative floors
force V_C,2=V_B,2=0 and V_A,3=V_C,3=0. The aggregate Bellman equations
now give

    z=2w/(1+2w),       w=2y/(1+2y),       y=2z/(1+2z).

Composing the three fractional-linear maps gives y=8y/(1+14y), so the
unique positive solution is y=z=w=1/2. At these hazards the quiet pivot's
three phase values are exactly

    V_A,0=12/7,       V_B,0=10/7,       V_C,0=6/7.

The last is below its singleton one, contradicting the C-phase floor.
Thus no nonzero limiting aggregate-hazard vector is possible.

### The zero-hazard limit is excluded by an actual homogeneous LCP

It remains possible a priori that all four aggregate hazards tend to
zero. Put t=x+y+z+w for each profile and pass to a subsequence with

    (x,y,z,w)/t → lambda,       lambda≥0, sum lambda=1.

Per-period absorption probability is t+O(t²), while joint absorption
at {0,1} has mass xy=O(t²). The four singleton absorption masses are
their respective aggregate hazards plus O(t²). Hence the limiting common
phase value is

    W=sum_j lambda_j r({j}).                            (59)

The initial-phase forced-Quit inequalities imply W≥s. No basis vector
can equal lambda, since each singleton vector in (58) gives some other
player strictly less than its singleton. Therefore lambda_i<1 for every i.

For any i with lambda_i>0, let that player Never quit. The opponents'
aggregate hazard sum is (1−lambda_i)t+o(t), positive for sufficiently
large indices, so they still absorb almost surely. The deviating terminal
value converges to

    [W_i−lambda_i*s_i]/(1−lambda_i).

Its excess over W_i is lambda_i*(W_i−s_i)/(1−lambda_i). Vanishing
full regret makes this nonpositive; the already-proved floor makes it
nonnegative. Thus W_i=s_i whenever lambda_i>0. Consequently lambda is
a nonzero homogeneous LCP solution for the actual singleton matrix

    M=[[0,1,1,−1],
       [−1,0,−1,2],
       [−1,2,0,−1],
       [−1,−1,2,0]].                                  (60)

That matrix is R0, as follows directly. If its homogeneous solution has
positive pivot coordinate t_0, the three child feasibility inequalities
force all child coordinates positive. Their complementary equalities
give z=(t_0,t_0,t_0), and the pivot residual is t_0>0, impossible.
If t_0=0 but a child coordinate is positive, the cyclic negative edges
force all three positive; their equalities and the child determinant
seven then force them all zero, again impossible.

This contradiction excludes the zero limit as well. Therefore no sequence
of restricted profiles has exploitability tending to zero, proving the
strictly positive infimum delta. The reasoning uses full deviations to
derive the obstruction; it is not a finite collection of numerical tests.

### What the obstruction does and does not establish

Changing beta from zero to a positive number leaves every prescribed
profile's payoff unchanged, because {2,3} is never realized on path.
It only raises the deviation payoffs of players 2 and 3 at that coalition;
all other payoff coordinates are unchanged. Thus exploitability for each
restricted profile weakly increases with beta. The same positive delta
therefore holds throughout beta≥0, including the full-premium-core variants.

For beta=0 the game has UE by the reviewed weak-leave theorem, so the
obstruction proves that the one-joint/two-solo-block architecture cannot
be a complete UE producer even on that already resolved raw class. It
also explains why changing only the scalar selector cannot remove v<1
from the current construction. At u=1+xi and v>1, supported pivot Quit
would pin V_B,0 to one, while a positive player-2 block necessarily raises
it above one if the next phase respects the pivot's singleton floor.

There is no unrestricted positive exploitability gap asserted for the
game. In particular, the beta=0 table cannot be an equilibrium counterexample.
The next constructive mechanism must alter the chronological support
architecture, for example by more than one joint phase or a different
phase-entry structure, rather than retuning hazards within these blocks.

### Reversing just the two solo blocks still does not suffice

The same table also has a positive restricted exploitability gap when
the order is joint {0,1}, solo-3 block, solo-2 block. Here is the extra
nonzero-limit argument; the zero-limit LCP proof is unchanged.

The initial joint row still rules out x=1 or y=1 by player 3's negative
payoff. A sure player-3 block makes player 2 negative, and a sure
player-2 block makes player 1 negative. Thus all limiting hazards are
below one, every phase is reached with positive probability, and all
phase values retain the singleton floors. A nonzero limit must have
z>0: without any player-2 exit, joint {0,1} harms player 3 and is its
only nonzero-payoff exit; if the joint row is absent too, player 3 alone
harms player 2. With z>0, skipping the final player-2 block forces
V_A,2=V_C,2=0. The intervening player-3 block then gives V_B,2=−w,
so w=0. If x>0, pivot indifference at A again forces V_B,0=1, but
the remaining player-2 block has V_B,0=2z+(1−z)V_A,0>1. Hence x=0.
Only singleton exits 1,2 remain, and positive z makes player 1 strictly
negative. This is the final contradiction. Taking the smaller of the
two positive gaps therefore excludes BOTH solo orders with the fixed
joint pair {0,1}; arbitrary solo subdivision does not change either proof.

## Switched joint pair: two passive rewards above the pivot singleton

Status: complete ordinary proof with independent PASS reviews from
CODEX_MORSE and CODEX_BROUWER in their corresponding feedback files;
not Lean-checked or exported. The
central statement and proof are frozen for further review. This changes
the selected joint pair and its incentive geometry,
not the constants in the frozen positive-premium-pair theorem. The
selected joint pair now has ZERO own premiums; a positive outsider
continuation coordinate permits actual positive joining premiums elsewhere.

### New raw class

Let a,b,c,h_1,h_2,h_3>0, D=abc−1>0. Prescribe

    r({0})=(1,−h_1,−h_2,−h_3),
    r({1})=(U,0,b,−1),
    r({2})=(V,−1,0,c),
    r({3})=(R,a,−1,0),
    r({0,3})=(1,−h_1,−h_2,0),                          (61)

where U,V≥1 and R is ANY real number. Write nu for the positive
singleton vector defined in (28)–(30); equivalently A*nu=(h_1,h_2,h_3)
for A=[[0,−1,a],[b,0,−1],[−1,c,0]]. Require

    r_2({0,2}), r_2({2,3}), r_2({0,2,3})≤0,            (62)

and the single raw weighted condition

    J=max(0,r_1({0,1}),r_1({0,1,3})),
    J+nu_3*r_1({1,3})≤nu_2.                            (63)

All other reward coordinates are arbitrary finite real numbers. In
particular r_0({0,1}) is unrestricted, and (63) allows a strictly positive
participant premium for player 1 at {0,1}. Neither global product-low
premiums nor globally constant outsider payoffs are assumed.

CLAIM: every such original four-player table has a fixed-target UE
against all behavioral deviations, for EVERY R. The constructive branch
uses one joint {0,3} row, then refined solo blocks for players 1 and 2.

### Exact residual interval and the alternative pivot equation

Put d_1=U−1≥0, d_2=V−1≥0 and

    R_low=1−(d_1*nu_1+d_2*nu_2)/nu_3,
    T=1−(c*d_1+d_2)/(bc).

The pivot inverse weights on A are the same literal weights (50), now
with s_1=−d_1 and s_2=−d_2. Their largest threshold is T=T_1, because
T_3≤T_1 and T_2≤T_3. Thus R≥T is already covered by the passive
inverse source. R≤R_low is covered by the same degree-zero/homogeneous
source arguments; they impose no sign condition on the two passive
shortfalls. If U=V=1, then R_low=T=1 and these sources cover every R.
Otherwise

    T−R_low=[h_2(c*d_1+d_2)+b*d_2*h_3]/(bc*nu_3)>0.  (64)

It remains to construct on R_low<R<T.

Cyclically order the nonpivot players as (3,1,2). In the quadratic
construction this changes (a,b,c) to (c,a,b), (h_1,h_2,h_3) to
(h_3,h_1,h_2), and nu to (nu_3,nu_1,nu_2). Put

    Y'=D/[a(bc+c+1)].

Here the actual joint collision rewards in (61) make both corresponding
H functions CONSTANT, h_1 and h_2. The selected joint pair's premium
eta is zero. The cleared quadratic proof still applies verbatim at
eta=0: its linear coefficient remains strictly positive, its constant
coefficient is y*[a(bc+c+1)y−D], and its right-endpoint value is positive.
Thus for each 0<y<Y' it supplies a unique admissible k>0, continuously
in y, with

    z=(h_2*k+y)/[b(1−y)],
    w=(a*y−h_1*k)/[1+a*y+(1−h_1)k],
    h_3*k+z−c*w*(1−z)=0,                              (65)

and k(0)=k(Y')=0. All z,w lie strictly between zero and one; set
x=k/(1+k). The endpoint limits are

    k/y→1/nu_3,        z/y→nu_1/nu_3,
    w/y→nu_2/nu_3.                                    (66)

For these rates define

    V_C,0=1+(V−1)w,
    V_B,0=U*z+(1−z)V_C,0,
    R(y)=[1−(1−y)V_B,0]/y.                            (67)

Both displayed continuation values are at least one. Formula (66)
extends R(y) continuously with R(0)=R_low. At k=0,y=Y', direct
substitution gives R(Y')=T. For example this follows from

    V=(bc+c+1)−bc*R−c*U

at that endpoint, obtained by inserting the zero-k rates in (67).
Hence every R strictly between R_low and T has an interior selected y.
No monotonicity of R(y) or negative passive reward is assumed.

### The positive outsider buffer is selected from raw data

The key new estimate is

    k(y)<y/nu_3,                0<y<Y'.                (68)

To prove it, test the balance function in (65) at k_0=y/nu_3. If
k_0 is at least the admissible upper endpoint, (68) is immediate.
Otherwise all its z,w are admissible and identities (3) give

    z_0=nu_1*y/[nu_3(1−y)]>nu_1*y/nu_3,
    w_0=nu_2*y/[nu_3+(nu_2+1)y]<nu_2*y/nu_3.

Therefore

    h_3*k_0+z_0−c*w_0*(1−z_0)
       > (h_3+nu_1−c*nu_2)y/nu_3=0.

The function starts negative and has only one admissible root, so that
root is below k_0. This proves (68) without differentiating a root branch.

Let Q=r_1({1,3}) and J be as in (63). At the joint {0,3} phase,
outsider 1's forced-Quit payoff is

    [k(1−y)r_1({0,1})+yQ+ky*r_1({0,1,3})]/(1+k)
        ≤[kJ+yQ]/(1+k).

Its prescribed value is (a*y−h_1*k)/(1+k)=w/(1−w). By (63),

    a−Q≥(h_1+J)/nu_3,

since a*nu_3−h_1=nu_2. Inequality (68), with h_1+J>0, therefore
gives

    (a−Q)y−(h_1+J)k>0.                                (69)

Thus the actual positive joining premium is strictly bounded by the
selected positive continuation buffer. It is not replaced by a zero cap.
Outsider 2 has value zero, and all its forced-Quit coalitions are exactly
its singleton and the three in (62), so its Quit endpoint is at most zero.

### Values, refinement, and complete deviations

The full phase vectors, in the ORIGINAL player order (0,1,2,3), are

    V_A=(1,w/(1−w),0,0),
    V_C=(1+(V−1)w,0,0,c*w),
    V_B=(U*z+(1−z)(V_C)_0,0,b*z,h_3*k).               (70)

The pivot's two A endpoints are both one by (67); player 3's are both
zero by (65). For the two outsider coordinates, actual A policy
evaluation gives

    (a*y−h_1*k)/(1+k)=w/(1−w),
    [−h_2*k−y+b*z*(1−y)]/(1+k)=0.

All B and C equations are exactly the singleton recurrences from (61).
Every Continue endpoint equals its displayed value, every supported
action is indifferent, and (62),(69) check all outsider Quit actions at
the undiffused joint row. Every value is at least its singleton, because
U,V≥1 and the remaining displayed coordinates are nonnegative.

Refine only the player-1 and player-2 rows. Define C_join using all pair
participant surpluses r_i({i,j})−s_i with j∈{1,2}, i≠j, and zero.
The same interpolation gives exact Continue, singleton floors, and a
uniform Quit error C_join times the largest microhazard. One constant-error
Bellman supersolution bounds EVERY complete deviation, not a sum of
local errors. Opponent survival contracts every repeated period because
x,y,z,w are positive. Thus the actual fixed target V_A is terminal
approximate Nash at all errors and is a uniform-equilibrium payoff by
the same direct geometric-tail or finite-law argument as before.

The source cases and (64)–(70) prove the whole R axis for this new raw
class. It admits positive premiums at coalitions prohibited by the old
six-cap theorem and selects a different actual joint support. The old
export's v<1 restriction has not been silently deleted.

### The architecture obstruction is repaired by changing the joint pair

The beta=0 obstruction table (58) satisfies (61)–(63): a=b=c=2,
all h_j=1, U=V=2, R=0, nu=(1,1,1), J=1, and Q=0. Put

    y=(3−sqrt(5))/2,
    k=y(1−2y),          x=k/(1+k),          z=w=y.

Then 0<y<1/2 and all four hazards are positive. The exact vectors are

    V_A=(1,y/(1−y),0,0),
    V_B=(1/(1−y),0,2y,k),
    V_C=(1+y,0,0,2y).

All policy/Continue identities follow from y=(1−y)². At A, the only
positive outside Quit endpoint is player 1's x(1−y), strictly below
y/(1−y). At B the pivot's Quit endpoint is 1+y, below 1/(1−y).
Every other unrefined Quit bound follows from the displayed floors and
zero participant rewards. Hence THIS unrefined alternative-pair cycle
is already exact terminal Nash, in the SAME table on which both solo
orders with the prescribed joint pair {0,1} have a positive gap.

The structural theorem, not that one algebraic fixture, is the proposed
enlargement. To obtain a full greatest-premium-core example in its new
class, one may raise both participant rewards at {1,2} to 1/2 and raise
player 3's participant reward at {1,3} to 1/2, keeping player 1's reward
there zero. Conditions (62),(63) are unchanged. Every player then has
a positive participant witness inside the full set, whereas the positive
player-2 premium at {1,2} and player-3 premium at {1,3} violate the old
joint-{0,1} caps. These additions are handled at the refined solo phases,
not discarded. The actual target (70) stays fixed before accuracy.

CODEX_MORSE independently checked the switched-pair theorem's raw weighted
cap, strict estimate (68), all-R endpoint T, full behavioral refinement,
and source stitching. His review also gives exact signed-Q and zero-leading-
coefficient tests with arbitrary unused rewards. The preceding architecture
positive-gap proof was not included in that PASS and remains a separate
unreviewed result.

For an explicit common-leaver comparison, the full-core completion has
premium traps {0,1} and {1,2}. Hence any player present in every trap
would have to be player 1. That player fails even weak leave at {0,1}:
r_1({0,1})=1>−1=r_1({0}). Thus the example is outside the signed
common-leaver class, not merely outside its earlier nonnegative-premium
version. This is a comparison with that precise criterion, not a claim
that every other implemented source fails.

## Two outsider buffers from a repeated solo exit

Status: separate complete ordinary proof candidate, not independently
reviewed. It is not part of the frozen switched-pair theorem. The new
architecture is joint {0,3}, solo 1, solo 2, solo 3. Repeating player 3
after the other solo exits creates a positive value for outsider 2 at
the joint row; a positive premium for pivot 0 keeps its later values
above its own singleton. Both outsiders may now have positive joining
rewards at every nontrivial joint-row collision.

### Raw class and claimed conclusion

Keep a,b,c,h_1,h_2,h_3>0, D=abc−1>0 and the four singleton vectors
in (61), with U,V≥1 and arbitrary R. Define nu by A*nu=h as above,
and R_low,T as in (64). Choose a number theta satisfying

    0<theta<nu_2/h_1,
    xi≥theta(1−R_low).

Replace the prescribed joint reward in (61) by

    r({0,3})=(1+xi,−h_1,−h_2,0).                    (71)

Since R_low≤1, xi is nonnegative. Put

    J_1=max(0,r_1({0,1}),r_1({0,1,3})),
    Q_1=r_1({1,3}),
    J_2=max(0,r_2({0,2}),r_2({0,2,3})),
    Q_2=r_2({2,3}).

The new raw restrictions are only

    (1+theta)J_1+nu_3 Q_1≤nu_2−h_1 theta,
    (1+theta)J_2+nu_3 Q_2≤theta nu_3.                 (72)

All other reward coordinates are arbitrary finite numbers. Both Q_i
may be signed, and (72) permits all six displayed collision coordinates
to be strictly positive. The claim is fixed-target UE for every R,
with all behavioral deviations allowed. The sources already proved for
the same singleton matrix handle R≤R_low and R≥T, including equality.
Only R_low<R<T requires the construction. If U=V=1 this interval is
empty and no construction is needed.

### A strictly monotone balance, without a quadratic branch convention

Put

    L_theta=a(bc+c+1)+theta(1+a+ac),
    Y_theta=D/L_theta,
    t=theta*y/(1+theta*y),
    A_1=(a*y−h_1*k)/(1+k),
    z=[h_2*k+y+(1+k)theta*y]/[b(1−y)],
    d_1=a*t+(1−t)A_1,
    w=d_1/(1+d_1),
    G(k,y)=h_3*k+z−c*w*(1−z).                        (73)

Here t is the final solo-3 aggregate hazard, not the pivot hazard.
For 0<y<Y_theta work on

    0≤k≤K=min(a*y/h_1,
             [b−(b+1+theta)y]/[h_2+theta*y]).

Both bounds are positive: indeed

    b L_theta−D(b+1+theta)
       =(1+theta)(ab+b+1)>0.

On this interval, 0≤A_1, 0<z≤1, 0<d_1 and 0<w<1.
As k increases, z strictly increases, A_1 strictly decreases, hence
w strictly decreases. Therefore G is strictly increasing, with
derivative at least h_3>0 wherever the interval is nondegenerate.
At k=0, clearing the positive denominators gives the sign of

    −D+L_theta*y,

so G(0,y)<0. At the right endpoint, either z=1, giving G>0, or
k=a*y/h_1. In the latter case A_1=0 and w<a*theta*y, whereas

    z≥[1+theta+a*h_2/h_1]y/b.

Consequently

    G(K,y)>y*D*(nu_2−h_1 theta)/(b h_1)>0.

These inequalities give one and only one root k(y) in (0,K).
The derivative lower bound gives continuity in the interior. At zero,
K≤a*y/h_1 forces k→0; at Y_theta, continuity and strict monotonicity
force k→0 because G(0,Y_theta)=0. Thus the branch extends continuously
with k(0)=k(Y_theta)=0. Dividing (73) by y at zero gives

    k/y→(1+theta)/nu_3,
    z/y→(1+theta)nu_1/nu_3,
    w/y→(1+theta)nu_2/nu_3.                           (74)

To justify the division without assuming a derivative, k/y is bounded
by a/h_1. Every convergent subsequence solves the same linear limiting
balance, whose positive coefficient is
h_3+h_2/b+c*h_1=D*nu_3/b. Hence its limit is unique.

### The root allocates both positive outsider buffers

The strict estimate needed for (72) is

    k(y)<(1+theta)y/nu_3.                             (75)

Test k_0=(1+theta)y/nu_3. If it is outside the admissible interval,
the conclusion is immediate. Otherwise its z value is strictly greater
than (1+theta)nu_1*y/nu_3. Its w value has numerator

    (1+theta)y(nu_2+a*theta*y)/nu_3

and denominator

    1+[theta+(1+theta)(nu_2+1)/nu_3]y
      +theta(1+a)(1+theta)y²/nu_3.

It is strictly less than (1+theta)nu_2*y/nu_3. Indeed, after comparing
the first-order coefficients, the required positive difference, times
nu_3, is

    nu_2(nu_2+1)+theta(nu_2 nu_3+nu_2²−h_1)>nu_2²,

using theta*h_1<nu_2; the quadratic coefficient is positive too.
It follows that

    G(k_0,y)>(1+theta)y(h_3+nu_1−c*nu_2)/nu_3=0.

Strict increase proves (75).

Set x=k/(1+k). At the joint phase outsider i's forced-Quit payoff
is at most [k J_i+y Q_i]/(1+k). The first inequality in (72) and
(75) give a strict upper bound A_1=(a*y−h_1*k)/(1+k) for i=1,
exactly as in (69) but with the factor 1+theta retained. The second
inequality gives an upper bound theta*y/(1+k)<theta*y for i=2.
Thus BOTH actual outsider Quit endpoints are strictly below their
positive prescribed values A_1 and theta*y. No zero collision cap is
being silently retained.

### Pivot selector and all-R endpoint stitching

Put p=1+xi*y and define

    R(y)={p[1−(1−y)(1−z)(1−w)(1−t)]
           −(1−y)[U*z+(1−z)V*w]}
          /{y+(1−y)(1−z)(1−w)t}.                    (76)

Its denominator is strictly positive. Formula (74) shows that it extends
continuously with R(0)=R_low. Direct substitution at k=0,y=Y_theta
gives

    R(Y_theta)−T
       =D[ xi−theta(1−T) ]/(abc+theta).              (77)

Since R_low<T in the nonempty residual case and
xi≥theta(1−R_low), the right side is strictly positive. The
intermediate value theorem therefore selects an interior y for EVERY
R_low<R<T. Neither R(y) monotonicity nor uniqueness is needed.

For the selected R, let

    P_D=R*t+(1−t)p
       =1+y[xi+theta(R−1)]/(1+theta*y),
    P_C=V*w+(1−w)P_D,
    P_B=U*z+(1−z)P_C.

All three are at least one: R>R_low and the xi hypothesis give the
first floor, and U,V≥1 give the other two. Equation (76) is precisely
R*y+(1−y)P_B=p, the pivot's joint-row Continue equality.

The full vectors at the successive phases A,B,C,D are

    V_A=(p,A_1,theta*y,0),
    V_B=(P_B,0,b*z,h_3*k),
    V_C=(P_C,0,0,c*w),
    V_D=(P_D,d_1,0,0).                                (78)

The vectors in (78) are in the original player order (0,1,2,3).
At A, the pivot's Quit endpoint is p and player 3's is zero.
Player 3's Continue equality is (1−x)h_3*k−x*h_3=0.
The outsider policy equations are

    V_A,1=(a*y−h_1*k)/(1+k),
    V_A,2=[−h_2*k−y+(1−y)b*z]/(1+k)=theta*y.

The solo recurrences give V_C,1=−w+(1−w)d_1=0,
V_D,2=−t+(1−t)theta*y=0, and
V_B,3=−z+(1−z)c*w=h_3*k. Every coordinate has its singleton
floor; every Continue comparison is exact, and every supported Quit
action is indifferent. The two remaining A comparisons were proved
from (72), so these are all joint-row deviations.

### Solo refinement and full behavioral conclusion

Refine ALL THREE solo blocks, not only the first two. In particular,
a pivot deviation at the final solo-3 block can collect the positive
pair premium xi, so leaving that block coarse would not be justified.
For n≥1 replace each aggregate q∈{z,w,t} by n identical hazards
q_n=1−(1−q)^(1/n). The endpoint vectors remain (78); intermediate
vectors interpolate between the corresponding endpoints and retain
all singleton floors and exact Continue identities. Let

    C_join=max(0, r_i({i,j})−s_i : j∈{1,2,3}, i≠j),
    e_n=C_join*max(z_n,w_n,t_n).

An outsider's immediate-Quit payoff at a solo-j microstage is
s_i+q_n[r_i({i,j})−s_i], so it is at most its phase value plus e_n.
The unchanged A row has error zero. Adding e_n to every phase value
is a Bellman supersolution: Continue transports only an opponent
survival fraction of that added constant, and Quit already has the
same single cap. Hence no error accumulates across phases or periods.

All x,y,z,w,t are strictly between zero and one. Removing any player's
hazards leaves a per-period opponent survival rho_i<1; this bound is
unchanged by any complete unilateral behavior and by subdivision. The
supermartingale comparison can therefore pass to terminal payoff, and
the fixed target V_A is delivered exactly with regret at most e_n→0.
If M bounds all rewards, m_n=1+3n and
C_n=max_i m_n/(1−rho_i), absorption time under every deviation has
expectation at most C_n. Finite-horizon average payoff differs from
terminal payoff by at most 2M C_n/N. Thus choosing n first, then N,
proves the usual all-large-horizon inequalities around the SAME V_A.
Together with the original singleton degree and passive-inverse exits,
this proves the claimed entire R-axis raw class in ordinary mathematics.

The exact compiler inspected again is
`quittingRootSequenceHazardTerminalValue_le_add_of_quitError_exactContinue`
and `isUniformEquilibriumPayoff_of_arbitrarily_small_infinitePath_quitError`
in `UniformEquilibrium/Quitting/Paths/InfinitePathSupersolution.lean`.
No new compiler claim is made. A narrow source check also read
`SignedFourCycleSingletonData` in
`UniformEquilibrium/Quitting/Cycles/SignedFourCycleRewardAdapter.lean`:
that singleton-only four-cycle requires a strictly positive predecessor
comparison in every column. Here the pivot singleton harms all other
players, so no relabeling meets that requirement. This is only that
specific source comparison, not an exhaustive classification.

### Exact two-buffer test and non-common-leaver completion

Use a=b=c=2, h_1=h_2=1, h_3=11465/6552, U=V=2,
theta=1/4, xi=1, and

    x=1/11, y=1/4, z=67/240, w=86/273, t=1/17,
    R=4802/23743,
    nu=(50777,65516,55690)/45864,
    R_low=−60603/55690, T=1/4,
    J_1=1/2, Q_1=5077/11138,
    J_2=1/10, Q_2=16379/111380.

Both inequalities (72) bind, with all four J_i,Q_i strictly positive.
The rate k is 1/10, and xi>theta(1−R_low). The exact vectors are

    V_A=(5/4,4/11,1/16,0),
    V_B=(37971/23743,0,67/120,2293/13104),
    V_C=(34286/23743,0,0,172/273),
    V_D=(479662/403631,86/187,0,0).

Choose r_1(01)=r_1(013)=J_1, r_1(13)=Q_1,
r_2(02)=r_2(023)=J_2 and r_2(23)=Q_2. These are all SIX positive
outsider collision coordinates, which neither zero-cap construction
can simply ignore. Their A Quit gaps are respectively
52581/245036 and 97953/4900720. The literal (73), (76), and all
sixteen phase policy/Continue identities hold in exact rational arithmetic.

For a full table, give every unspecified participant its singleton and
every unspecified outsider reward zero, then set r_0(01)=r_0(02)=3
and r_3(13)=1/2. Preserve (71), all singletons, and the six specified
collision coordinates. Traps 01,02,13 have empty intersection, so there
is no common player in every premium trap at all, even before any
leave inequality is tested. Their union is the full four-player set.
This completion satisfies the raw conditions and has a full greatest
premium core, while invalidating the signed common-leaver criterion.
It does not claim separation from every conceivable existing producer.

Next check requested: independently falsify the global bound (75),
endpoint identity (77), pivot floor at the final solo-3 block, and the
claim that refinement of that third block preserves both buffers.
