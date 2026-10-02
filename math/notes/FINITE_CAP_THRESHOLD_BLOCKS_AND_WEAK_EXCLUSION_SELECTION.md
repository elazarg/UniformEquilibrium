# Finite cap-threshold blocks, a quadratic minimum collar, and finite selection

Authors: supplied GPT cap-threshold manuscript; independent reconstruction and
source audit by CODEX_FRECHET_CYCLE.
Independent reviews: [CODEX_FRECHET_CYCLE's source audit](../feedback/CAP_THRESHOLD_DEBT_DESCENT__BY_CODEX_FRECHET_CYCLE.md)
and [CODEX_NOETHER_SUPPORT's independent packet review](../feedback/CODEX_FRECHET_CYCLE__FINITE_CAP_THRESHOLD_DESCENT_PACKET_DRAFT__BY_CODEX_NOETHER_SUPPORT.md).

This packet proves a finite prefix construction with complete behavioral
deviation control, an explicit quadratic minimum margin, and a terminating
finite selector under weak payoff exclusion. All new results are ordinary
mathematics; no Lean implementation is asserted. The residual for arbitrary
Fin4 is renewed access to a usable cap margin. The argument proves that
access under weak payoff exclusion, not for arbitrary reward tables.

## Self-contained question and answer

Fix n>=2 players I, terminal rewards r(S) in R^I for every nonempty coalition
S, and M>0 with `|r_i(S)|<=M`. Before absorption the only public history is
all Continue. Players privately randomize independently. The first nonempty
coalition quits and receives r(S); infinite all Continue receives zero.
Write `s_i=r_i({i})`.

A behavioral profile is equivalently a product of laws on
`N union {Never}`. For an actual profile p define

    U_i(p) = expected terminal reward,
    B_i(p) = sup over all complete replacement laws of U_i(replacement,p_-i),
    d_i(p) = B_i(p)-U_i(p),
    D(p)   = sum_i d_i(p),
    L_i(p) = B_i(p)-s_i.

The supremum includes every deterministic finite date, arbitrarily late
finite dates, Never, and all private randomization. The prescribed own law
is feasible, so all d_i are nonnegative. All U_i and B_i lie in [-M,M].

An owner i is preempted if some j!=i satisfies
`ell=s_j-r_j({i})>0`. Given an arbitrary actual source with D>0 and a
preempted owner, can one produce a finite literal prefix controlling the
**total** complete deviation debt without replacing the source?

Yes. Put

    C=max(D,L_i),        k(C)=3C^2/(32M+6C).

There is a finite word w of independent product rows, followed by the exact
old source p, with

    D(w::p)<=C-k(C),
    length(w)<=1+ceil([32(M+C)/C] log(4M/ell)).       (T1)

The empty word is allowed. If `L_i<=D`, this is a strict debt decrease from D.
For rational reward and finite-source data, an exhaustive finite rational
root search produces instead

    D(w::p)<=C-3C^2/(128M+24C)                     (T1q)

with the same row bound. The real-source assertion does not claim an
algorithm that computes arbitrary infinite-profile cap suprema.

Let K be the closure of all actual semantic pairs `(U(p),B(p))` and let
`d=min_K D`. If d>0, then at every minimizing pair and every preempted owner,

    B_i-s_i>=d+d^2/(8M),
    U_i-s_i>=d-d_i+d^2/(8M)>=d^2/(8M).             (T2)

The same conclusion applies to every player with `s_i>=0`: absence of a
preemptor would imply d=0. For four players it applies to every player of an
arbitrary signed table, using the existing no-UE singleton-blocker theorem.

Finally assume all s_i>=0 and

    for every actual finite-word profile p,
        min_i(U_i(p)-s_i)<=0.                      (WE)

Every rational table satisfying WE has a terminating construction of an
actual finite profile with `D<=epsilon` for every rational epsilon>0. If all
owners are preempted, let

    D_0=sum_i s_i,
    C_0=(128M+24D_0)/3,
    ell=min_i max_(j!=i)(s_j-r_j({i}))>0.

For `0<epsilon<D_0`, the constructed number of dates is at most

    ceil(C_0/epsilon)
      * [1+ceil([32(M+D_0)/epsilon] log(4M/ell))].  (T3)

This is a date bound of order epsilon^(-2) for a fixed table, not a bound on
arithmetic bit complexity. The same payoff-exclusion hypothesis for a real
table gives finite real-law approximants using exact Nash roots.

## Exact semantics of prefixing

A product root q specifies independent current-date Quit probabilities q_i.
Let

    c=product_i(1-q_i),     a=1-c,
    beta_i=product_(j!=i)(1-q_j),
    pi_i=q_i beta_i.

Let mu_i(T) be the product probability that precisely T of the opponents
quit. Define

    Q_i=sum_(T subset I\{i}) mu_i(T) r_i(T union {i}),
    H_i=sum_(nonempty T subset I\{i}) mu_i(T) r_i(T).

Prefixing q to the actual profile gives

    U'_i=q_i Q_i+(1-q_i)(H_i+beta_i U_i),
    B'_i=max(Q_i,H_i+beta_i B_i).                   (1)

For the cap identity, a complete deviation first chooses Quit or Continue.
Quit gives Q_i. Continue leaves exactly the old opponent profile after the
common all-Continue event and permits every old replacement law. Its
supremum is `H_i+beta_i B_i`. Taking the larger branch gives (1), also when
the old supremum is not attained or beta_i=0. Randomizing between the two
branches cannot improve their maximum.

The finite-dimensional set K is nonempty, closed, and bounded, hence compact.
Equation (1) is continuous in `(U,B)` for a fixed root. Prefixing actual
profiles gives actual profiles, so this map preserves K. All finite algebra
below therefore holds for carrier points too. No carrier point is claimed
to have an actual full-pair realization merely because it lies in K.

## Credited auxiliary input, with its short proof

Fix h>=0 and set `v=B-h*1`. The current finite Boolean game uses r on
nonempty quitting coalitions and v on all Continue. Let

    w_i=q_i Q_i+(1-q_i)(H_i+beta_i v_i),
    g_i=max(Q_i,H_i+beta_i v_i)-w_i.

Then

    B'_i<=w_i+g_i+beta_i h,
    U'_i=w_i+c(h-d_i).

Since `beta_i-c=pi_i`, subtraction and summation give

    d'_i<=c d_i+pi_i h+g_i,
    D'<=D-a(D-h)+sum_i g_i.                         (2)

For an exact Nash root all g_i vanish. This exact coordinate budget is
already implemented by `quittingTerminalSemanticDebt_prefix_le_auxiliaryNash`
(`UniformEquilibrium/Quitting/Terminal/AuxiliaryNashDebt.lean`).

If `v_j<=s_j-delta` with delta>0, endpoint subtraction gives

    Q_j-(H_j+beta_j v_j)
       >=beta_j delta-2M(1-beta_j)
       >=delta-(2M+delta)a.                         (3)

Each nonempty-opponent contribution is a joining difference bounded below
by -2M. This calculation needs no absolute bound on v. An exact Nash root
therefore has

    a>=delta/(2M+delta).                            (4)

Otherwise j strictly prefers Quit, forcing q_j=1 and hence a=1, a
contradiction. If `max_i g_i<=delta/4`, the valid approximate version is

    a>=delta/[2(2M+delta)].                         (5)

Indeed, failure of this bound makes j's endpoint gain greater than delta/2,
while `q_j<=a<1/2`; its mixed regret would exceed delta/4.

The approximate-root and absorption calculations are credited to the supplied
GPT manuscript “Auxiliary cap descent: finite full-response selectors and
exact limits.” Their complete proofs are given above. Its exact infinite-limit
conclusion is not used here.

## Proof of the finite first-threshold block

Choose

    theta=C/[32(M+C)],      rho=1-theta,
    z=4M theta<=C/8,        h=C/2.

Here theta is positive and below 1/32, and `0<k(C)<C/2`. If `D<=h`, keep
the source. If some initial margin `B_j-s_j<=z`, proceed directly to the
auxiliary row below. Otherwise every initial margin exceeds z.

Repeatedly prefix only owner i with Quit probability theta. At each step,
all outsiders have Quit probability zero. For j!=i write `a_j=r_j({i})`.
The outsider's Quit endpoint satisfies

    Q_j=rho s_j+theta r_j({i,j})<=s_j+2M theta.

Whenever the old outsider cap satisfies `B_j>s_j+4M theta`, its Continue
endpoint obeys

    rho B_j+theta a_j>=B_j-2M theta
       >s_j+2M theta>=Q_j.                          (6)

Consequently Continue is strictly selected at every step up to and
including the first threshold crossing. The owner's cap is constant because
its initial margin is positive and its row update is `max(s_i,B_i)`.

For every m up to that first crossing, exact iteration of (1) gives

    U_i(m)=s_i+rho^m(U_i-s_i),       B_i(m)=B_i,
    U_j(m)=a_j+rho^m(U_j-a_j),
    B_j(m)=a_j+rho^m(B_j-a_j)              (j!=i).

Therefore

    D_m=rho^m D+(1-rho^m)L_i<=C.                    (7)

This identity accounts for all debts, including a possible increase in the
owner's debt. It is valid only through the chosen first crossing.

For the fixed strict preemptor j, `a_j=s_j-ell`. If no crossing has yet
occurred at m, its affine cap formula gives

    B_j(m)-s_j<=-ell+2M rho^m.

Since `rho^m<=exp(-theta m)`, by
`m=ceil(theta^(-1) log(4M/ell))` this is at most `-ell/2<0`. Thus a first
crossing occurs no later than this finite index. A crossing cap satisfies

    2M theta<B_j(m)-s_j<=4M theta.                  (8)

The strict lower bound follows from (6) on the crossing step.

If `D_m<=h`, stop. Otherwise prefix any exact Nash root of the finite game
at `v=B(m)-h*1`. A crossing cap, or an initially low cap in the skipped-block
case, gives `v_j<=s_j-3C/8`. Equation (4) gives
`a>=a_0=3C/(16M+3C)`. Since `D_m>h`, equation (2) gives

    D_final<=D_m-a_0(D_m-h)
            <=C-a_0(C-h)
             =C-3C^2/(32M+6C).

The second inequality uses `1-a_0>=0` and `D_m<=C`. This proves T1 and its
row count. Every root is prefixed to the preceding complete source.

For T1q, require `max_i g_i<=k(C)/(4n)`. Since this is below `(3C/8)/4`,
(5) gives `a>=a_0/2`. Equation (2) then yields

    D_final<=C-(a_0/2)(C-h)+k(C)/4=C-k(C)/4.

The early-stop branches also satisfy this weaker bound. For rational source
data the solo rows and threshold tests are rational. If the Boolean-game
payoffs are bounded by R in absolute value, each root-regret function is
`4Rn`-Lipschitz in the sup norm: couple the product actions one coordinate
at a time to bound each expected payoff difference by `2Rn` times the
hazard distance, and add the corresponding bound for the endpoint maximum.
An exact finite-game Nash root has a rational grid neighbor with regret at
most the chosen tolerance on a grid of mesh at most tolerance/(4Rn).
Exhaustively testing that finite grid therefore terminates.

## Positive-minimum consequence

First recall the minimum singleton-margin fact, which also has a short proof
from (2). At a global minimum d>0, choose any `0<=h<d` and an exact root at
`B-h*1`. Global minimality and (2) force a=0. The all-Continue root is Nash
only if `B_i-h>=s_i` for every i. Letting h increase to d gives

    L_i>=d for every i.                             (9)

Fix a preempted owner i at any minimizing pair. Choose positive hazards
theta tending to zero with `4M theta<d`. Apply only the first-threshold
solo block, using that hazard and threshold `4M theta`. The proof of (6)--(8)
works for these hazards independently of the quantitative choice used in T1.
The resulting carrier points Y_theta have

    d<=D(Y_theta)<=L_i.

Compactness and finiteness of the outsiders give a subsequence with a fixed
crossing j and a limit Y in K satisfying

    B_j(Y)=s_j,       d<=D(Y)<=L_i.                 (10)

Prefix Y with an exact Nash root at `B(Y)-d*1/2`. By (4),
`a>=d/(4M+d)`. Since `D(Y)>=d>d/2`, global minimality and (2) imply

    d<=D(prefix Y)
      <=[4M/(4M+d)]D(Y)+[d/(4M+d)]d/2.

Multiplication and rearrangement give
`D(Y)>=d+d^2/(8M)`. Combine with (10) to prove the first part of T2, then
subtract `d_i<=d` to prove its payoff statement.

If `s_i>=0` and owner i has no preemptor, let only i quit at a stationary
hazard t>0. Its payoff and complete cap are s_i. For j!=i put
`a_j=r_j({i})>=s_j` and `J_j=(1-t)s_j+t r_j({i,j})`. Its prescribed payoff
is a_j. A pure quit at date k gives

    [1-(1-t)^k]a_j+(1-t)^k J_j,

while Never gives a_j. Hence its full cap is `max(a_j,J_j)` and its regret
is at most `2Mt`. Let t decrease to zero. Thus infimum total debt is zero,
contradicting d>0. This proves the nonnegative-owner clause of T2.

For arbitrary signed Fin4, positivity of the semantic minimum implies
absence of a uniform-equilibrium payoff by the existing semantic
equivalence. The already proved
`exists_singletonColumnBlockerCertificate_of_fourPlayer_noUniform`
(`UniformEquilibrium/Quitting/Classification/LCP/FourPlayerSingletonColumnBlockers.lean`)
supplies a preemptor for each owner with one uniform positive gap. Its
hypotheses impose no singleton signs. Applying the preempted-owner form of
T2 proves the signed Fin4 clause without altering terminal rewards.

The quadratic consequence for payoffs can be recorded without an additional
construction. If all owners satisfy the T2 hypotheses and

    rho_pay=max(0,sup_(actual p) min_i(U_i(p)-s_i)),

then continuity of the minimum-coordinate payoff functional on the
semantic carrier implies `d<=sqrt(8M rho_pay)`. When d=0 this is immediate;
when d>0 apply T2 at a minimizer. This bounds the infimum of total debt, not
the cap of an arbitrary payoff realizer.

## Construction under weak exclusion

Assume now that all singleton rewards are nonnegative. If an owner is not
preempted, the preceding solo construction has a finite implementation.
Use K dates of its hazard t followed by all-Never. The owner's regret is
at most `M(1-t)^K`. For an outsider, `a_j>=s_j>=0`, the cap is at most
`a_j+2Mt`, and its prescribed payoff is `[1-(1-t)^K]a_j`. Thus every
coordinate regret is at most

    2Mt+M(1-t)^K.

Choose rational `t=min(1/2,epsilon/(4nM))` and the least K with
`M(1-t)^K<=epsilon/(2n)`. This is finite and yields total debt at most
epsilon. No WE assumption is needed for this unblocked branch.

Otherwise all owners are preempted, with uniform ell>0 as in T3. Start from
all-Never, with `U=0`, `B=s`, and debt D_0. If D_0 is zero or already at
most epsilon, stop. At every other finite source, WE supplies an owner with
`U_i<=s_i`. Since

    L_i=B_i-s_i<=B_i-U_i=d_i<=D,

T1q applies with C=D and produces another actual finite source satisfying

    D_next<=D-3D^2/(128M+24D)
           <=D-D^2/C_0.                            (11)

This source is the entire previous word with a new finite word prefixed.
It satisfies WE again by hypothesis. Thus the source is renewed with no
semantic replacement seam. If debt is positive, (11) implies

    1/D_next>=1/D+1/C_0,
    D_k<=C_0 D_0/(C_0+kD_0).

The inequality is unnecessary when a step produces zero debt. At most
`ceil(C_0/epsilon)` phases therefore suffice. During each nonterminal phase
`epsilon<D<=D_0`; the row bound from T1q is bounded by the second factor
in T3. Concatenating the literal prefixes proves its date count.

All finite-source values are computed by (1), initialized at `(0,s)`.
Equivalently, the complete cap is a finite maximum over the displayed dates,
one finite date after the last displayed date, and Never. Every later finite
date faces only all-Never opponents and has the same terminal reward as the
first post-cutoff date. Randomized complete deviations are mixtures of these
pure payoff values. At an auxiliary step `R=M+D_0` bounds all Boolean-game
payoffs, so the finite rational grid search specified above is executable.

For real data, use T1 in the same recursion and replace C_0 by
`(32M+6D_0)/3`. This proves existence of finite approximants even though no
effective exact comparison procedure for arbitrary real inputs is claimed.

## Fin4 finite-menu adapter and uniform-payoff consumer

In the canonical four-player case `s=(1,0,0,0)`, the actual profile from T3
has each complete gain at most epsilon. On its N-date menu, every restricted
deviation is complete, so `E_N<=epsilon`. The pivot's extra post-cutoff
deviation is also complete, so `L_0<=epsilon` for this very same product law.
This supplies a finite-menu selector on WE tables. No separate pivot
replacement or cap-preserving payoff-realization theorem is assumed.

For an N-date finite profile, every prescribed terminal absorption is at a
displayed date; the discrepancy from the H-stage average payoff is at most
`M(N+1)/H`. For any complete deviation, early absorption has the same bound.
After the opponents' cutoff, the only possible later reward on their
all-Never event is that player's nonnegative singleton, whose delayed
average contribution is no larger than its terminal contribution. Uniformly
over deviations, finite-average gain is therefore at most

    D+2M(N+1)/H.

Choose errors tending to zero and a convergent subsequence of their bounded
prescribed payoff vectors, with limit u. For any positive target accuracy,
select one sufficiently late finite profile from this subsequence so that
its debt and payoff distance from u are small, then one H threshold making
the displayed error small. The same selected profile works at every larger
horizon. Thus u is one fixed uniform-equilibrium payoff. This is the existing
consumer `quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
(`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`).

## Boundary tests and scope

For a positive finite regression, take four players with s=(1,0,0,0).
At every coalition use the own singleton for participants and -1 for
outsiders, except `r({1,2})=(1,1,1,1)` and
`r({0,1,2})=(2,-1,-1,-1)`. This completely specifies an M=2 table. The
pure `{1,2}` source has `U=(1,1,1,1)`, `B=(2,1,1,1)`, and D=1.
Owner 0 has L_0=1, so T1 uses theta=1/96 and z=1/12. The first outsider
cap crossing occurs at m=59, with `B_j=-1+2(95/96)^59` and total debt
exactly one. The all-Quit auxiliary root at B-1/2 has zero root regret
and produces zero terminal debt. The guaranteed decrease is only 3/70.
This table already has a pure all-Quit equilibrium.

For a negative test of replacing C by D, take three players with
s=(-1,0,0). Use the same default rule, except `r({1,2})=(1,1,1)` and
`r({0,1,2})=(2,-1,-1)`. The pure `{1,2}` source has U=(1,1,1),
B=(2,1,1), D=1, and owner-0 margin L_0=3. Owner 0 has preemptor 1.
T1 uses C=3, theta=3/160, and z=3/20. Its first hit is m=30, and up to
that hit

    B_j(m)=-1+2(157/160)^m   (j=1,2),
    D_m=3-2(157/160)^m>1    (m>0).

The crossing cap lies in `(3/40,3/20]`. Thus even the total debt can
increase during the block when L_i>D; the theorem's use of C is necessary.
Continuing the same solo recurrence indefinitely would predict negative
outsider caps. The actual Quit endpoint is zero, so the affine cap formula
eventually fails. The first-hit restriction prevents this failure.

For a below-singleton cap test, take two players and the complete table

    r({0})=(1,1),  r({1})=(-1,1),  r({0,1})=(-1,-1).

The pure joint-quit source has U=(-1,-1), B=(-1,1), and D=2. Owner 1
is preempted by player 0, but `B_0=-1<s_0=1`. The initial low-cap branch
therefore skips the solo block. Its auxiliary game at B-1 has the exact
root q=(1,0), whose actual prefix has U=B=(1,1) and zero debt. This
shows why owner-cap constancy is asserted only after the all-margins-positive
test, never at an arbitrary source.

These examples are exact calculations, not evidence that a positive-minimum
game exists. The supplied finite checker additionally passed 300 rational
auxiliary-ledger cases, 30 signed first-hit blocks, and 16 collar-algebra
cases, as recorded in the source review; those tests do not replace a proof.

The proved local block is stronger than a supplied-root verifier: it selects
a finite word from an arbitrary actual source and a preempted owner. The
finite selector is a construction from a precisely stated reward class,
with complete deviations controlled throughout. Its qualitative UE class
was already covered by minimum-margin and singleton-tight arguments; the
new point is explicit actual finite selection and its quantitative budget.

The current production surface already has qualitative singleton-margin
and minimum-fiber separation. Specifically,
`minimumTerminalSemantic_singletonMargin`
(`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticAuxiliaryNashBudget.lean`)
gives L_i>=d, while
`exists_pos_uniformSingletonGap_minimumFiber_of_punishmentNormal`
(`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinFourMinimumFiberIsolation.lean`)
gives a uniform but unspecified positive payoff gap on the minimum fiber.
`exists_offMinimum_collar_on_completeCap_singletonSlab`
(`UniformEquilibrium/Diagnostics/Quitting/CompleteCapSingletonSlabCollar.lean`)
already gives a qualitative off-minimum cap slab. T2 supplies an explicit
quadratic constant through the new arbitrary-source finite block; it does
not claim these qualitative conclusions anew. The exact local
cap-Continue accounting is also present in
`quittingTerminalSemanticDebt_prefix_eq_of_capContinue`
(`Research/Quitting/TerminalSemanticWeightedDebtAxisInsertion.lean`), under
its branch hypothesis. T1 proves finite threshold selection and sums the
complete debt on arbitrary sources.

The newly integrated
`eventually_capResponseSegment_debtSum_ge_min_add`
(`UniformEquilibrium/Diagnostics/Quitting/CapResponseSegmentCollar.lean`)
uniformizes a qualitative collar over supplied response-installation
segments. Its companion
`eventually_capResponseSegment_exactRoot_debtDrop_and_absorption`
(`UniformEquilibrium/Diagnostics/Quitting/CapResponseSegmentExactRootExpenditure.lean`)
assumes supplied cap-attaining responses, a positive owner-debt floor, and
convergence of that owner's cap to its singleton. Neither theorem produces
the first-threshold block at an arbitrary source or the weak-exclusion
finite selector above. No attainment hypothesis is used in T1 or T2.

The complete bounded source inventory is in the first linked review. No
original-paper result is needed beyond classical finite-game Nash existence,
and no literature-wide novelty claim is made.

For arbitrary canonical Fin4 the named open finite-menu obligation remains:
the next source can have every `B_i-s_i>D`, and WE is not known for every
table. The bound in T1 is then `C-k(C)`, with C possibly larger than D.
Neither this bound nor the compact limit Y gives a renewable debt decrease
in that region. T2 quantifies the margin of a hypothetical positive minimum
inside this residual; it does not exclude that residual.

## Lean handoff

The source types and continuous finite-prefix maps are already defined in
`UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`. An external
formalization could first add a finite solo-block theorem whose inputs are
an actual semantic source (or carrier membership), a preempted owner, and
the reward bound, and whose output is a finite list of product roots with
the exact first-hit ledger and row count. Existence of that list must be
proved, not stored as an assumed structure field. Then compose the existing
auxiliary budget, the quadratic carrier-limit corollary, and finally the
finite-law recursion. The exact-root and rational approximate-root theorem
shapes should remain distinct.

