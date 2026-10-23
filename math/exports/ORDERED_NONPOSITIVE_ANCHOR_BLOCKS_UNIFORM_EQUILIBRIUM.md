# Ordered nonpositive anchor blocks admit uniform equilibrium

## 1. A finite raw equilibrium class

Let I be any finite nonempty player set. Native rewards Z_i(A), for every
nonempty coalition A, are finite real numbers with Z_i({i})=0; live and
Never rewards are zero. Strategies use independent private randomness;
complete unilateral behavioral replacements are permitted.

Choose a nonempty marked set C, an ordered partition (B1,...,Bm) of C into
nonempty blocks, and strictly positive weights lambda_i on each block. Set
D=I minus C. Assume the following finite raw inequalities:

* If Bk is the first block meeting a nonempty coalition A, then
  sum_(i in A intersect Bk) lambda_i Z_i(A)<=0.
* For every c in C and every nonempty A subset D, Z_c(A)<=0.

Every unlisted reward is arbitrary. In particular, no sign condition on
any reward recipient in D is imposed. These conditions use weak reward
inequalities and finite-dimensional raw weights, with no strategic input.
The subset, block order and weights may be produced by finite enumeration
and linear programming: enumerate all nonempty subsets and ordered
partitions, normalize sum_(i in Bk)lambda_i=1 for each block, and maximize t
subject to all displayed linear inequalities, lambda_i>=t, and t>=0. The feasible
set is compact. A positive optimum is equivalent to strictly positive
admissible block weights and supplies them. An infeasible program or optimum
zero simply rejects that ordered partition. Blocks may be rescaled
independently, so the normalization loses no admissible raw table.

**Theorem.** The infimum A_Z of complete native total Nash debt over
prescribed independent laws that absorb surely is zero. Consequently every
original reward table r_i(A)=Z_i(A)+s_i with s_i>=0 has one fixed
uniform-equilibrium payoff. The target is fixed before accuracy; at each
positive accuracy, one behavioral profile and a horizon threshold work for
every larger finite horizon and every complete unilateral replacement.
This is a restricted raw class, not a solution of the full Fin4 conjecture.

Singleton blocks give a useful explicit corollary. If C=(c1,...,cm) is
ordered, it suffices that Z_ck(A)<=0 whenever ck is the first C member of A,
together with the same passive inequalities on nonempty subsets of D.
For Fin4 with C=(0,1), D={2,3}, the entire corollary premise is

    Z0(A)<=0 whenever 0 in A;
    Z1(A)<=0 whenever 1 in A and 0 notin A;
    Z0(A),Z1(A)<=0 for nonempty A subset{2,3}.         (R)

Own zeros make two listed inequalities automatic, leaving sixteen caps.
There is no assumption on Gamma01,Gamma10, any entry received by2 or3,
or any pair joining product. No singleton sign pattern is imposed.

## 2. Exact maps and the closed marked cone

For q in[0,1]^I write a=product_i(1-q_i) and H_i=product_(j!=i)(1-q_j).
Let P_i be the passive absorption contribution and Q_i the forced-Quit
value against the product opponent quitter set. For arbitrary virtual
payoff/cap annotations (u,b), the exact prefix maps are

    u'_i=a u_i+E_i(q),
    b'_i=max(Q_i(q),P_i(q)+H_i b_i),

where E is the expected nonempty-coalition reward. These maps are continuous,
preserve b>=u, and are coordinatewise 1-Lipschitz in their terminal annotation.
At a root Nash against u, equality b=u is preserved. A full cap includes
every finite deadline and literal Never; taking its supremum commutes with
the nonnegative H_i. Finite Nash existence holds for every real u.


For precision, if B is the independently sampled opponent quitter set,

    Q_i(q)=E[Z_i(B union{i})],
    P_i(q)=E[Z_i(B) 1_(B nonempty)],
    E(q)=sum_(A nonempty) Pr_q(A)Z(A).

Before absorption the only live public history is elapsed time. An arbitrary
complete behavioral strategy therefore induces a law for its first Quit time
in N union{Never}. A replacement law is a mixture of finite deadlines and
Never. Thus the cap recurrence above includes every unilateral behavioral
replacement, with no restriction to Markov or periodic deviations. The
prescribed stopping laws use only independent private randomness.

A finite word means an arbitrary finite list of hazard vectors. Its dates
need not be Nash at intermediate annotations unless this is explicitly
required. Prefixing reverses the construction order to obtain the physical
calendar. The cap and prescribed maps are separately coordinatewise
1-Lipschitz in their terminal annotation because a,H_i lie in[0,1] and taking
a maximum preserves the bound. These estimates are independent of word
length, and apply equally to virtual annotations and actual laws.

Let K_C={u:min_(c in C)u_c<=0}. The following property is enough for the
proof; the raw class above will supply it:

    u in K_C and q a proper Nash root against u
             imply its output u' lies in K_C.        (NI)

Proper means all q_i<1. For the raw ordered-block class, (NI) holds
for all roots. If some C owner is active, let B be the first block with an
active owner. Every earlier block has all hazards zero. Independence gives
the exact identity

    sum_(i in B) lambda_i q_i Q_i(q)
       = E_q[sum_(i in A intersect B) lambda_i Z_i(A)].   (B)

The summand is zero when A misses B. Every positive-probability coalition
meeting B has B as its first intersected block, so the raw condition makes
the right side nonpositive. Because all weights are positive and some
q_i>0 in B, at least one active i in B satisfies Q_i<=0. At a Nash root its
Quit action is supported, so its output equals Q_i, whether its hazard is
mixed or one. Thus the output belongs to K_C. This argument averages only
inside the first active block; no sign is required of later block totals.

If no C owner is active, every absorbing coalition lies in D. The passive
condition gives E_c<=0 for every c in C. Then u'_c=a u_c+E_c preserves a
nonpositive marked coordinate. This proves (NI), including every zero wall.
Singleton blocks recover the first-active-owner proof of corollary(R).

## 3. Budgeted local escape under (NI)

Fix a table satisfying (NI) for a fixed nonempty marked set C. Suppose
v>=0, min_C v=0, and AllContinue is the UNIQUE whole-game Nash root at v.
Let S={i:v_i=0}; it is nonempty and meets C.

**Local lemma.** For every d>0 and eta>0 there exist c>0 and finite words
W_k supported on S, with hazard coordinates at most d, whose output from
(v,v), denoted (u_k,b_k), and survival h_k satisfy

    1-eta <= h_k <= 1-c,
    sum_i(b_(k,i)-u_(k,i)) -> 0,
    limsup_k min_C u_k <= 0.                          (1)

All coordinates outside S retain strictly positive limiting payoffs.
There is no participant-pair sign premise in this lemma. We prove it by
induction on |S| while keeping the AMBIENT game and marked set C fixed.
The words need not be Nash at every intermediate annotation.

Choose M>=1 bounding the rewards, v and nearby seeds. Unrolling any word
with terminal seed z and survival p gives

    ||u-v||_infinity <= ||z-v||_infinity+2M(1-p).     (2)

Both payoff and cap annotations stay in the bounded reward/seed interval.
Decrease eta, if necessary, so eta<1 and 2M eta is less than one quarter
of every positive coordinate of v. Decreasing a requested budget is allowed.

### 3.1. Nonnegative kernel and the induction base

Let Gamma_ij=Z_i({j}) with zero diagonal. If Gamma_SS x=0 for nonzero x>=0,
normalize sum x=1. Repeat q=epsilon x on S for floor(t/epsilon) dates, with
t>0 fixed so 1-eta<exp(-t)<1. Core passive contributions are O(epsilon^2),
forced-Quit values O(epsilon), and prescribed stopping contributions
O(epsilon^2). From zero core input, payoffs are O(m epsilon^2) and complete
caps have a nonnegative upper bound O(epsilon+m epsilon^2). Thus all core
debt tends to zero. This includes rows outside the support of x.

Positive outsiders retain their buffer by (2). Their forced-Quit values
are O(epsilon), while Continue stays strictly positive. They Continue
optimally throughout and have exactly zero debt. Survival tends to exp(-t),
and all core payoffs tend to zero. Since S meets C, the marked minimum has
limit zero. Hazards tend to zero, so (1) follows after discarding finitely
many terms and decreasing c. This proves the base |S|=1 as Gamma_SS=0.

### 3.2. Signed progress and existence of a marked seed

Otherwise the convex hull of Gamma_SS's columns avoids zero. Its nearest
point w, interpreted as a row on S, satisfies

    w Gamma_SS >= ||w||^2 1^T >> 0.                 (3)

For all sufficiently small hazard vectors supported on S, the singleton expansion
therefore gives

    w E_S(q) >= gamma sum_i q_i, gamma>0.           (4)

Higher terms are bounded by a small maximum hazard times the total hazard.
No positivity of w and no sign of any J entry is used.

There are arbitrarily small seeds z_S with w z_S>0 and min_(C intersect S)
z<0. If C intersect S has at least two elements, the union of its negative
coordinate halfspaces intersects every nonzero positive linear halfspace:
otherwise w would have to be supported on each distinct marked coordinate,
forcing w=0. If C intersect S={i}, w cannot be supported on i alone, since
(w Gamma_SS)_i would then equal zero, contrary to (3). Varying a different
nonzero-weight coordinate gives w z_S>0 while z_i<0. Set z_out=v_out.

### 3.3. The bounded-prefix minimum

Choose delta>0 with delta<=d, delta<eta/(4|I|), and (4) valid. Also take it
small enough for outsiders' strict Continue gaps near (v,0). Unique root
at v and compactness of the whole root cube then supply epsilon0>0 such
that every Nash root for ||u-v||<epsilon0 has max q_i<delta and all outsiders
inactive. Fix c0=min(eta/4,epsilon0/(8M),1/4), before choosing z, and take
the preceding seeds with ||z-v||<epsilon0/4.

Let K_z be the closure of all outputs (u,b,p) of finite words starting at
(z,z), supported on S, with every root coordinate at most delta and total
survival p>=1-eta. Include the empty word. It is compact. A fixed permitted
finite prefix acts on this closure whenever the resulting survival has
STRICT slack above 1-eta: append it to defining approximants and use that
slack to retain the budget before taking their limit.

Minimize p on the nonempty closed subset

    F_z={b=u, min_C u<=0, w u_S>=p w z_S}.           (5)

The empty word belongs to F_z. Let Y=(u,u,p) be a minimum. If p>1-c0,
(2) places u in the epsilon0 neighborhood. All its whole-game roots are
small, proper and supported on S. Any nonzero Nash root preserves equality
of cap/payoff, the marked cone by (NI), and the weighted constraint by (4).
It also leaves strict budget slack:

    a(q)p >= (1-|I|delta)p > 1-|I|delta-c0 > 1-eta/2.

It would belong to the SAME F_z with smaller p, a contradiction. Thus
AllContinue is the unique whole-game root at u. Hence u>=0; its core is
nonzero by w u_S>=p w z_S>0, even for signed w. Its zero set T is nonempty,
properly contained in S, and still meets C, by min_C u<=0. Every coordinate
outside T is positive.

### 3.4. Induction retains the original marked cone and original weight

Apply the induction hypothesis at u with zero set T and the SAME marked
set C. Property (NI) is unchanged since the ambient table and C are fixed.
Choose the new total absorption budget eta' with p(1-eta')>1-eta and request
root hazards at most delta. The resulting finite words V_k have survival
h_k in[1-eta',1-c'] for some c'>0, full debt tending to zero, and limiting
marked minimum nonpositive.

Each endpoint from Y lies in the original K_z by strict-slack stability.
Every new hazard vector is supported on T subset S and below delta, so (4) gives

    w U_S(V_kY) >= h_k w u_S >= ph_k w z_S.         (6)

This inequality concerns the ORIGINAL w, independently of any different
separator used inside the inductive construction. It holds for arbitrary
small hazard vectors, without a Nash premise on their intermediate inputs. A compact
endpoint subsequence has zero full debt, min_C<=0 by (1), the original
weighted constraint by (6), and survival at most p(1-c')<p. It belongs to
the SAME F_z and contradicts its minimum. Thus min_F_z p<=1-c0.

The inner c' may depend on Y and the seed; only its strict positivity is
needed at this exact minimum. The outer c0 was fixed independently of z.

### 3.5. Remove the virtual seed

For seeds z_k tending to v, approximate the corresponding F minima by finite
defining words, with virtual debt tending to zero, survival at most 1-c0/2,
and marked minimum with limsup<=0. Every word already obeys the hazard and
survival budget. Apply the identical words to (v,v). Full-cap and payoff
nonexpansiveness change total debt by at most 2 sum_i|z_(k,i)-v_i| and the
marked minimum by at most ||z_k-v||. Survival is unchanged, and outsiders
stay positive by (2). This proves (1), with c=c0/2, and closes induction.

## 4. An actual marked-fiber minimum proves absorbing debt zero

For actual independent stopping laws let H be the compact closure of
(U,B,N), retaining each ORIGINAL Never mass N_i. Finite prefixes act
continuously on H, including non-Nash prefixes, and multiply their Never
product by the word's joint survival. Define

    E_C={X in H: B=U and min_C U<=0}.

It is compact and contains AllNever. Moving the smallest Never mass to one
finite date gives an absorbing law. For n=|I| and absolute reward bound M,

    A_Z <= D+(4n-2)M (product_i N_i)^(1/n).         (7)

There are n changed prescribed payoff coordinates and n-1 changed caps,
each bounded by twice M times that mass; the changed owner's cap is unchanged.
The inequality extends to H. If A_Z>0, the minimum m of the original Never
product over E_C is therefore positive. Let X attain it, with payoff v.

If any nonzero Nash root exists against v, it preserves zero debt. An
absorbing root would give a point of H with zero debt and zero Never,
contradicting (7). A proper nonzero root stays in E_C by (NI) and lowers
the original product below m. Hence only AllContinue is Nash at v, forcing
v>=0. Since X is in E_C, min_C v=0.

Apply the local lemma to v, and apply its identical finite words to X.
Their cap/payoff annotations are exactly those of the lemma, because X
has annotations (v,v). A compact endpoint subsequence has zero debt,
marked minimum<=0, and Never product at most m(1-c)<m. It lies in the SAME
E_C, contradicting its minimum. Therefore A_Z=0.

This minimum is neither a global minimum over all payoffs nor a minimum
of a conditional tail. Its closed marked-cone constraint is preserved at
every exact root and every local escape limit. No payoff equality beyond
cap=payoff is needed, and no virtual seed is asserted realizable.

## 5. Original rewards and one fixed target

For s_i>=0, every absorbing prescribed law has U_i^r=U_i^Z+s_i. Every finite
deadline receives the same shift s_i; Never receives at most s_i. Hence
B_i^r<=B_i^Z+s_i and D_r<=D_Z. The produced absorbing approximate profiles
give terminal Nash at every accuracy for r. The exact fixed-target endpoint
is `quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
in `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`.
It selects one payoff before accuracy and controls complete behavioral
deviations over every sufficiently long horizon. Negative own offsets are
not included by this argument.

The prefix and full-cap source interfaces are
`quittingTerminalSemanticDebt_prefix_eq_continueMass_mul_of_capNash` in
`UniformEquilibrium/Quitting/Root/CapNashRootStack.lean`,
`quittingFiniteRootWordCap_sub_le_opponentSurvival_mul_posPart` in
`UniformEquilibrium/Quitting/Root/CommonPrefixCapStability.lean`, and
`exists_isZeroQuittingRootNash` in
`UniformEquilibrium/Quitting/Root/NashExistence.lean`.
The ordinary formulas used here are proved directly above. No new Lean
implementation, generic root selector, degree, or perturbation is claimed.


## 6. Complete raw calibration and coverage

### 6.1. Complete unbounded native family

Let original own-singletons be one and r_i(A)=1+Z_i(A) for nonempty A,
with live and Never zero. For arbitrary T>=0 define all sixty entries by

| A | Z(A) |
|---|---|
| 0 | (0,3,-1,-1) |
| 1 | (3,0,-1,-1) |
| 2 | (-1,-1,0,3) |
| 3 | (-1,-1,3,0) |
| 01 | (-1,-1,-T,0) |
| 02 | (-1/10,3,-2,0) |
| 03 | (-2,3,0,-1/10) |
| 12 | (3,-2,-1/10,0) |
| 13 | (4,-1/10,0,-2) |
| 23 | (-1/10,-1/10,4,1) |
| 012 | (-1/10,-2,-1/10-T,-1) |
| 013 | (-1,-1/10,5,-1/10) |
| 023 | (-1/5,5,0,-11/10) |
| 123 | (4,-1/5,19/10,-3) |
| 0123 | (-1/10,9/10,59/10,-31/10) |

The singleton and joining matrices are independent of T:

    Gamma = [ 0  3 -1 -1 ]
            [ 3  0 -1 -1 ]
            [-1 -1  0  3 ]
            [-1 -1  3  0 ],

    L = [ 0  -4   9/10 -1   ]
        [-4   0  -1     9/10]
        [-1   9/10 0    1   ]
        [ 9/10 -1 -2    0   ],       J=Gamma+L.

The table has the exact additive insertion identity

    Z_i(B union{i})-Z_i(B)=sum_(j in B)Lij              (1)

for every opponent set B, with Z_i(empty)=0. Thus its actual zero-input
joining field is Delta(q)=Lq. The two growing coordinates are paired
precisely so that (1) is unchanged for every T.

In particular the two-anchor raw premise(R) holds. As additional controls,
all matching singleton signs and all cross J signs are strict, and J01=-1.
The seven entries Z0(012),Z0(013),Z0(023),Z0(0123),Z1(123),Z0(23),Z1(23) equal

    (-1/10,-1,-1/5,-1/10,-1/5,-1/10,-1/10).           (2)

But for EVERY nonzero a>=0,

    a Z(012)=-(a0/10)-2a1-(1/10+T)a2-a3<0.           (3)

This defeats every global or proper-coalition nonnegative weighted floor,
including weights with zero coordinates. It strictly separates this full
family from a global nonnegative weighted-coalition hypothesis. The singleton
row condition alone still happens to hold with weights one; no separation
from that intermediate condition is claimed for this calibration.

### 6.2. Actual zero-root inertia and all sure-owner families

Every reciprocal sum Lij+Lji is strictly negative and every column has a
positive entry. At any zero-input root, qi(Lq)i>=0 for supported Quit.
Their sum is strictly negative if two owners move, a contradiction. A lone
mover fails a positive outsider joining inequality. Therefore AllContinue
is the unique actual zero-input root on the entire cube.

Fix one owner i at Quit and solve the complementary three-player induced
game. The continuation disappears from every opponent difference. Its
entire Nash correspondence, in full player coordinates, is:

| Forced owner | Entire complementary Nash family | Forced-owner joining gap |
|---|---|---|
| 0 | (1,0,t,1), 0<=t<=9/20 | -1+(9/10)t<=-119/200 |
| 1 | (0,1,1,0) | -1 |
| 2 | (1,0,1,0) | -1 |
| 3 | (0,0,1,1) | -2 |

Here is an analytic elimination, including boundary indifferences.
For forced0, owner1 has gap -4-q2+(9/10)q3<0, hence q1=0.
Owner2 then has gap -1+q3. If q3<1 it forces q2=0, which makes
owner3's gap 9/10>0 and forces q3=1, a contradiction. Thus q3=1,
owner2 is indifferent, and owner3's supported-Quit inequality gives
q2<=9/20. For forced1, owner0's gap is strictly negative, hence q0=0;
owner2's gap 9/10+q3>0 forces q2=1, and then q3=0. For forced2,
owner3's gap (9/10)q0-q1-2<0 forces q3=0; owner1's gap
-4q0-1<0 forces q1=0; owner0 then strictly quits. For forced3,
owner0's gap -4q1+(9/10)q2-1<0 forces q0=0; owner2's gap
(9/10)q1+1>0 forces q2=1; owner1's gap -1+9/10<0 forces q1=0.

The exact program also enumerates all 27 closed pure/mixed face patterns
for each induced game. It checks every vertex of every rational bounded
solution polytope by adjoining zero through three active inequalities to
the existing equalities, so equality-fixed interior vertices, singular
faces and continua are included. An exact interior-point sanity check
guards this enumeration. The first family is the whole interval, not
merely two tested points.

Every family has ANOTHER sure opponent. Thus the owner's Continue payoff
has zero coefficient on EVERY supplied punishment tail. The positive
Continue-minus-Quit gain in the last column is independent of that tail.
No owner and no induced Nash selection can satisfy the actual owner floor.
This excludes singleton bases, all sure-owner roots and owner chambers.
For a base with at least two sure owners, all base leave and outsider tests
would together give a full sure-owner root, already excluded. Additional
fixed Continue outsiders that satisfy their own no-join tests merely
extend to a point of the full complementary induced correspondence above.

The checked interfaces being compared are
`quittingSingletonBaseOwnerFloorExcess_nonpos_iff` and
`nonempty_quittingSingletonBaseCertificate_of_inducedNash` in
`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseConcreteGap.lean`;
`nonempty_quittingPersistentBaseCertificate_of_inducedNash` and
`exists_uniformPayoff_of_persistentBase_inducedNash_signs` in
`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseNashSemanticAdapter.lean`;
and `QuittingInducedOwnerChamber`, `QuittingInducedOwnerNeverChamber` in
`UniformEquilibrium/Diagnostics/Quitting/InducedOwnerChambers.lean`.
The latter Never chamber also fails its nonpositive original-own guard.

### 6.3. Every quiet child

For child C and outsider o the necessary capped-clock rows are

    F(A): sum_C beta_i[-Z_i(A)] >= -Z_o(A),
    K(A): sum_C beta_i[Z_i(A union{i})-Z_i(A)]
                                  >= Z_o(A union{o})-Z_o(A),

with beta>=0. For the following thirteen children, the singleton joining
row K({j}) has every child coefficient nonpositive and RHS9/10:

    (C,o,j)=
    (0,3,0),(1,2,1),(2,0,2),(3,1,3),
    (01,3,0),(02,3,0),(03,1,3),(12,0,2),(13,2,1),(23,0,2),
    (012,3,0),(013,2,1),(123,0,2).

For child023 and outsider1, F({2})+F({3})+2K({3}) has child
coefficients(0,-1,-3) and RHS19/5>0. Every child therefore fails the
entire weight LP. These literal singleton rows are unchanged throughout
the T family.
The nonnegative-singleton quiet relaxation changes only its Never row,
so it fails as well. No broader withdrawal grammar is inferred excluded.

### 6.4. Traps, weights and raw phase comparisons

The only premium trap is23. Owner0 has no positive participant premium,
and owner1 has none inside123; every remaining pair except23 has negative
participant rewards. J23=4,J32=1 supply its two positive witnesses.
The greatest premium core is thus23, not the set of all owners who have
some positive premium involving outside players.

Pure product support23 defeats ProductLow and every nonzero nonnegative
supportwise upper-average certificate. A pair cannot use the boxed-charge
branch of the mixed upper/charge theorem. The mixed-premium-trap producer
requires nonnegative reciprocal joining product on every pair trap, while
L23 L32=-2. The weighted-floor-return test for23 fails on the GLOBAL
inserted singleton {0}, giving -2lambda2-lambda3/10<0 for every positive
trap weight. Summing the global inserted rows at{0},{1} gives
(-1,-1,-21/10,-21/10), defeating every nonzero nonnegative global floor
weight. Summing the native singleton columns gives(1,1,1,1), defeating
every nonzero nonnegative global upper weight. Equation(3) now additionally
defeats every proper passive-ledger weight, independently of the proper
trap obstruction to all proper-flat two-ledger classes.

Every owner has a negative cross participant premium. Thus the protected
set is empty and common/support-specific protected-leaver admissions fail.
The greatest-core-at-most-two theorem assumes all participant premiums
nonnegative and fails that premise. The mixed-sign triple-core theorem
requires greatest core size three and fails that premise.


The exact weight and participant predicates being compared are
`HasProductLowQuittingPremium` in
`UniformEquilibrium/Quitting/Classification/ProductLowQuittingPremium.lean`,
`HasGlobalQuittingWeightedFloor` and `HasWeightedQuittingTrapLeavers` in
`UniformEquilibrium/Quitting/Classification/WeightedQuittingTrapLeavers.lean`,
and `HasProtectedParticipantPremiums`, `HasSupportSpecificQuittingLeavers`
in `UniformEquilibrium/Quitting/Classification/SupportSpecificQuittingPremiumLeavers.lean`.

#### Complete singleton, pair and finite calendar comparisons


Every reciprocal singleton product is positive. There is no directed
escort edge Gamma_ij<=0<=Gamma_ji between distinct players, including in
every principal restriction. This excludes the exact
`BalancedSingletonCycleCertificate.exists_escortCycle` admission in
`UniformEquilibrium/Quitting/Cycles/CyclicSingletonEscort.lean` and the
strict/weak nonpositive-reciprocal-product class. Mutual negative cross
pairs exclude the no-mutually-negative-pair class. The positive singleton
graph consists only of two disjoint two-cycles, so raw classes requiring
a positive Hamiltonian singleton cycle or a directed positive triple do
not admit any relabeling.

The cross principal [[0,-1],[-1,0]] is not standard Q: at offset
(-1,-1) every residual is strictly negative. It has no nonzero homogeneous
solution either, because x>=0 and (-x1,-x0)>=0 force x=0. Thus it is not
projective Q, and the full matrix is not projective Q-bar. This uses both
branches of `isProjectiveQMatrix_iff_standard_or_homogeneous` and
`IsProjectiveQBarMatrix` in
`UniformEquilibrium/Quitting/Classification/LCP/MatrixClasses.lean`.
The full determinant is45>0 and the inverse is strictly positive; this
is not the old negative-determinant inverse entrance. Every proper triple
has an unmatched row with both offdiagonal entries negative, precluding
that triple from mapping any nonnegative vector to a strictly positive
one; hence no proper positive-inverse child occurs.

For EVERY unordered pair ij, at least one of Lij,Lji is strictly negative.
Thus every pair partition fails the necessary scheduled-owner comparison
in the two-pair joining-cap, crossed-matching, signed-inverse-column,
nonmatching-positive-passive and bounded-inverse-corners producers.
The signed inverse-column signs are necessarily all positive here, so
they cannot reverse that failed comparison. Neither favorite pair has
BOTH positive joining increments, excluding every negative-pair-funded
boundary and global asymmetric favorite-pair choice. Every cross pair
has opposite joining signs, so no cross pair meets the both-below
negative-pair or below-singleton joint-phase premise; nor can an
opposite-sign two-pair schedule select one whole below/below pair.

The low-passive alternating-friendly class fixes a common normalized
participant value on all four favorite coordinates. Here those values
are -1,-1,4,1, while the singleton rows fix identical positive scales;
no relabeling meets that equality. The four-joint-phase and rectangular
families require the two favorite rows to have both participants above
their passive favorite singleton; that already fails. The literal
four-singleton-phase bound at a favorite pair is original reward at most
(5+sqrt(5))/2<4. Owner2 at23 receives5, which fails under either pair
orientation. A triple collision-box premise requiring all six joining
increments in one triple positive also fails. These comparisons concern
the displayed raw families, not every possible periodic strategy or an
unspecified perturbation neighborhood of an older reference table.

The one-negative-pair joint/two-solo families and their arbitrary-premium
extensions require reciprocal-opposite singleton pairs; the present
matrix has none. The three-owner positive-passive-triple producer likewise
requires a reciprocal-opposite pair in its literal singleton subpattern.
The exact passive-cap table families fix different participant pair
values (negative native favorite participants), so the positive23 row
prevents every matching relabeling. No unrestricted table-level Nash
checker is treated as an older raw existence producer.

### 6.5. Passive-pole census and family-level caveat

All24 old three-passive-pole endpoint assignments are checked. Exactly two
pass, unchanged because the joining field is unchanged:

    (0,1,3,2),    (0,3,1,2).

Their respective c values are9/10 and9/40. The six remaining guard values
(a2,b2,l0,l1,f0,f1) are

    (-2,-11/10,-19/100,-419/100,27/50,-1/10),
    (-1,-5,-89/40,-53/40,3519/16000,-319/400).

No isolated-table threshold exclusion is inferred from passing or failing
only part of an asymptotic theorem. In the first passing role the two
designated negative passive poles are fixed original rewards4 and1; its
designated nonnegative passive pole is r2(01)=1-T and tends to negative
infinity. In the second role the two negative poles are fixed rewards1
and9/10 and the third pole is fixed reward1; both growing coordinates of
our ray lie in its supposedly bounded background. Thus the whole T ray
is not a fixed-background tail of either admitted negative-pole family.
More generally the linked unbounded
passive and participant entries prevent this ray from being a tail of the
old participant-jackpot schemas with bounded passive completions or the
old passive-coalition schemas with bounded participant completions.
Letting a completion bound vary with T supplies no diagonal theorem;
no converse or isolated-threshold nonmembership is asserted.

The new theorem handles all payoff strata directly. Earlier full-zero
source exclusions, including matching anchor/index results that may apply
to these same Gamma,J, are not substituted for a direct global UE producer.
The present exact table is not asserted to have positive absorbing debt.

### 6.6. Reproduction scope

Appendix A contains all data and reruns the full60 adapter,
seven strict caps, impossible coalition weight, all14 quiet certificates,
entire four induced Nash families, all trap/weight tests, all24 pole roles,
and matrix/pair sign screens. It also verifies that the negative T-ray
preserves every insertion identity and avoids every constrained cap.

The corresponding existing row interfaces are
`rawChild_future_delta`, `rawChild_future_base`, `rawChild_joining_delta`
and `rawChild_joining_base` in
`UniformEquilibrium/Quitting/Classification/QuietExtension/CappedClockOriginalCoalitionRows.lean`,
with feasibility given by `nonempty_cappedClockParentRewardCertificate_iff`
in `UniformEquilibrium/Quitting/Classification/QuietExtension/CappedClockExactLPAlternative.lean`.
All finite data and necessary comparisons are included here and in the
embedded standalone checker.

### 6.7. The entire homogeneous pencil, including its singular value

Let A(p)=Gamma-pJ, 0<=p<=1. Every column has an offdiagonal entry
-1+p/10<0, excluding every singleton homogeneous complementarity support.
The favorite pair determinants are -(p+3)^2 and -(p-3)(4p-3); the four
cross-pair determinants are -(p-10)(2p-1)/10. At each pair singularity in
[0,1], one reciprocal offdiagonal is zero and the other is nonzero, so
no kernel vector is strictly positive on both pair coordinates.

The two triple determinants for012,013 are

    (p+3)(401p^2-420p+200)/100.

For023 and123 they are respectively

    -(404p^3-1683p^2+1760p-600)/100,
    -(1601p^3-2823p^2+1760p-600)/100.

Exact polynomial root counts show none vanishes on[0,1]. The full determinant
is

    -3(33067p^4-73080p^3+314800p^2-42000p-150000)/10000.

It has exactly one zero in[0,1], lying in(81/100,82/100). This zero cannot be
ignored. On its entire isolating interval, the first two entries of adj(A)'s
column0 have opposite signs:

    adj(A)_00=-(1601p^3-2823p^2+1760p-600)/100>0,
    adj(A)_10=(50p^3-147p^2-184p+210)/10<0.

The first polynomial has no zero on[0,1]; the second has no zero on the
isolating interval and is negative at81/100. The nonzero first cofactor gives
rank three. The adjugate column spans a mixed-sign one-dimensional kernel,
so no full nonnegative homogeneous support exists. The exact program below
checks every stated root count. Thus the WHOLE pencil is R0, rather than only
its endpoints or nonsingular parameter values. This excludes a homogeneous
pencil exit, not a general UE producer.

At offset -ones, the original Gamma has the unique complementarity solution
x=ones: singleton supports cannot cancel their -1 active row; crossing pairs
and every triple have a negative active row; a favorite-pair solution violates
both outsider inequalities. Full invertibility leaves x=ones, with local
orientation detGamma=45>0. Thus its R0 degree is one. This is a control with the
usual Q/degree source guards intact, not a bypass through a missing guard.

## 7. Exact absorbing profile and branch boundary tests

At T=0, Appendix B supplies an explicit rational word of87 dates, followed by
one sure-quit date. The word was found by numerical root continuation and then
rounded to denominator10^12. It is not claimed to consist of exact Nash roots.
Its validity is checked instead by exact rational evaluation of the actual
prescribed payoff and complete dynamic cap recurrence of Section2, with the true zero Never tail.

The87-date word has joint Never probability below10^(-35). Replacing the
smallest original Never mass by a sure quit at the last date makes the profile
absorbing. The exact88-date profile has total native full debt below10^(-7);
the same bound holds for original own levels one. Its original payoff is
approximately

    (0.330450890753, 2.658770713784, 1.352504491857, 0.974837874629).

Every finite deadline and Never is included in the cap recursion. All proof
checks use rational arithmetic, regardless of the floating-point provenance
of the word. It proves one finite-accuracy comparison, not A_Z=0 by itself and
not stationary nonexistence. Sections1--5 separately give all accuracies for
every raw table in the theorem. The complete table has actual zero-root
inertia, so this comparison uses nonzero continuation values.

Appendix C tests the local alternatives in Section3. Its balanced matching
matrix has favorite entries2 and crossing entries-1, with kernel vector
ones/4. Arbitrary signed higher rewards are included, and the actual
stationary finite-deadline and Never caps are evaluated exactly at four
shrinking rational hazards. A separate singleton-supported kernel tests the
deleted-opponent case d_i=0, where the true endpoint is zero rather than a
quotient with zero denominator. Finally, a matching matrix with favorite1
and crossing-1 has Gamma*ones=-ones, so no nonzero nonnegative row can have
wGamma>=0. Nevertheless w=-ones satisfies wGamma=ones, and the seed
(-3,-3,1,1) has wu>0 and a negative anchor coordinate. The main calibration
has matching singleton signs; the raw theorem itself does not require them. These are mechanism
and boundary tests, not additional coverage witnesses.

For an explicit nonmatching scope test, take the complete T=0 table in
Section6.1 and change only Z2({0}) to7 and Z3({2}) to-4. These are rewards
received by D owners, so every ordered-anchor inequality is unchanged.
The only mutual nonnegative singleton pair is01; there is no partition into
two such pairs, and no relabeling has the weak matching sign pattern.
Appendix D specifies all sixty modified rewards and checks all24 labelings.
This shows that the raw adapter contains no hidden matching gate. It is not
claimed as a separate novelty witness or as an independent numerical proof
of equilibrium for the modified table; the general theorem supplies UE.

The weighted-block premise is also strictly broader than the singleton-block
premise. From the original T=0 calibration, change only
Z0(01)=1/20, Z1(023)=83/20, and Z1(0123)=1/20. The one marked block
C={0,1} with weights(1,1) passes: the sums for both-marked coalitions
01,012,013,0123 are respectively -19/20,-21/10,-11/10,-1/20; coalitions
with exactly one marked participant retain that participant's nonpositive
reward, and the passive C-on-D caps are unchanged. Every player now has
a positive participant reward somewhere, so none can be first in an ordered
singleton-anchor set. Appendix D checks all64 nonempty ordered singleton
choices and all weighted-block inequalities exactly. This is a raw-scope
test, not an additional whole-selection novelty claim; Section6 remains
the complete coverage calibration for the theorem.

## 8. Source correspondence, strategic inputs, and Lean handoff

Finite root existence is
`exists_isZeroQuittingRootNash` in
`UniformEquilibrium/Quitting/Root/NashExistence.lean`.
Complete independent stopping laws realize actual behavioral profiles through
`quittingTerminalPayoff_stoppingLawProfile_eq_expectedPayoff` and
`quittingStoppingLawCap_eq_continuationBestResponseValue_stoppingLawProfile`
in `UniformEquilibrium/Quitting/Paths/StoppingLawOperationalDistance.lean`.
The latter identifies the law cap with the full behavioral best-response value.
The finite-prefix formulas and their nonexpansiveness are proved in Section2;
the local induction and actual compact-fiber consumer are Sections3--4.

The fixed-target endpoint is
`quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
in `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`.
For an arbitrary alleged four-player counterexample, the separate declaration
`nonempty_finFourSinglePivotNormalization_of_no_uniformPayoff` in
`UniformEquilibrium/Diagnostics/Quitting/FinFourSinglePivotNormalization.lean`
produces a no-UE table with one own level one and the other three zero.
Its native table cannot satisfy the ordered-block conditions for ANY
nonempty marked set and positive-weight ordered partition, because those
own levels are nonnegative and the
present theorem would produce UE. The normalization is not asserted to
supply the raw conditions. Their failure is a necessary restriction on a
surviving normalized counterexample.

The full-pencil degree comparison in Section6.7 agrees with
`exists_finset_r0Degree_eq_sum_sign_det` in
`MathUE/LinearProgramming/R0DegreeSum.lean` and
`isStandardQ_of_r0Degree_ne_zero` in
`MathUE/LinearProgramming/R0Degree.lean`.
The projective-Q dictionary is specified in Section6.4. These are calibration
comparisons only. No degree, genericity, matrix inverse, or participant
determinant is assumed or used by the new existence proof.

All strategic objects are produced. The subset and ordered partition are
finite raw data, and their positive block weights are supplied by the finite
linear program in Section1. Identity(B) proves the root invariant directly.
Under the temporary
positive-debt contradiction, compactness produces an actual marked-fiber
minimum and forces its unique AllContinue root. On each zero face the finite
singleton table produces either a nonnegative kernel direction or a signed
separating row. The local seed is produced in a proved nonempty open cone.
Finite Nash existence supplies a root at every required intermediate input.
The budgeted prefix closure and its minimum produce finite words, and
induction on the strictly smaller zero set handles every possible stall.
No continuation value, root word, equilibrium, selector, minimum, survival
drop, punishment, or payoff target is an unproduced strategic hypothesis.

A formalization can separate the exact cap recursion, the
(4n-2)M absorbing-repair inequality, compact marked-fiber minimum, marked
seed separator lemma, and budgeted local escape by zero-face induction.
The key induction conclusion must retain an arbitrary requested hazard bound,
an arbitrarily small total absorption budget, a strictly positive survival
loss uniform along the approximating sequence, complete-cap debt tending to
zero, and the SAME marked set. It must not replace the original signed row
by the smaller face's row in the outer minimum constraint. The remaining
steps are the actual compact return and nonnegative original own-level
adapter. All reward inequalities are weak from the outset; no perturbation
or uniform-constant passage through nearby tables is needed.

The theorem closes this finite raw reward class directly at every payoff
stratum, for any finite player set. It does not assert that every game
admits ordered blocks and positive weights satisfying the inequalities, or that a supplied
invariant is itself an arbitrary-game producer. The raw adapter is the
ordered-block condition in Section1. Negative original own offsets are
outside the proved adapter. The full four-player conjecture remains open.
The exact finite-selector exclusions and family-level asymptotic comparisons
in Section6 have their displayed scope; no isolated unknown-threshold
nonmembership or failure of every older strategy grammar is claimed.
The new proof is ordinary mathematics, not a checked Lean implementation.

## Appendix A. Exact full-table and selection verifier

This standalone Python/SymPy program checks all sixty rewards, the entire
T>=0 insertion identity, all fourteen quiet children, every sure-owner
induced correspondence including its interval, every listed trap and weight
blocker, and all twenty-four passive-pole role assignments. The two passing
endpoint roles are retained; no unknown-threshold claim is made.

```python
"""Exact full-table audit for the global anchor theorem without weights.

Run with Python/SymPy. No floating point, root sampling, or Lean claim.
The program verifies raw guards and explicitly named older admission tests;
it does not prove failure of every equilibrium architecture.
"""
from itertools import combinations, permutations, product
import sympy as s

R = s.Rational
I = tuple(range(4))
COAL = tuple(A for n in range(1, 5) for A in combinations(I, n))
G = s.Matrix([[0, 3, -1, -1], [3, 0, -1, -1],
              [-1, -1, 0, 3], [-1, -1, 3, 0]])
L = s.Matrix([[0, -4, R(9, 10), -1], [-4, 0, -1, R(9, 10)],
              [-1, R(9, 10), 0, 1], [R(9, 10), -1, -2, 0]])
J = G+L
PASSIVE = {
    (0, (1, 2)): 3, (0, (1, 3)): 4, (0, (2, 3)): -R(1, 10),
    (1, (0, 2)): 3, (1, (0, 3)): 3, (1, (2, 3)): -R(1, 10),
    (2, (0, 1)): 0, (2, (0, 3)): 0, (2, (1, 3)): 0,
    (3, (0, 1)): 0, (3, (0, 2)): 0, (3, (1, 2)): 0,
    (0, (1, 2, 3)): 4, (1, (0, 2, 3)): 5,
    (2, (0, 1, 3)): 5, (3, (0, 1, 2)): -1}


def native(i, A):
    A = tuple(sorted(set(A)))
    B = tuple(j for j in A if j != i)
    if not B:
        value = s.S.Zero
    elif len(B) == 1:
        value = G[i, B[0]]
    else:
        value = s.sympify(PASSIVE[i, B])
    return value+(sum(L[i, j] for j in B) if i in A else 0)


def joining(i, A):
    return native(i, set(A) | {i})-native(i, A)


TABLE = {A: tuple(native(i, A) for i in I) for A in COAL}
assert len(TABLE)*4 == 60
assert all(native(i, [i]) == 0 for i in I)
FAVORITES = ((0, 1), (2, 3))
CROSS = [(i, j) for i in I for j in I if i//2 != j//2]
assert all(G[i, j] > 0 and G[j, i] > 0 for i, j in FAVORITES)
assert all(G[i, j] < 0 and J[i, j] < 0 for i, j in CROSS)
assert J[0, 1] < 0
CAPS = [(0, (0, 1, 2)), (0, (0, 1, 3)), (0, (0, 2, 3)),
        (0, I), (1, (1, 2, 3)), (0, (2, 3)), (1, (2, 3))]
assert [native(i, A) for i, A in CAPS] == [
    -R(1, 10), -1, -R(1, 5), -R(1, 10), -R(1, 5),
    -R(1, 10), -R(1, 10)]
assert TABLE[(0, 1, 2)] == (-R(1, 10), -2, -R(1, 10), -1)
assert max(TABLE[(0, 1, 2)]) < 0  # Every nonzero nonnegative ledger weight fails.
assert TABLE[I] == (-R(1, 10), R(9, 10), R(59, 10), -R(31, 10))

q = s.symbols('q0:4')
for i in I:
    opponents = tuple(j for j in I if j != i)
    derived = 0
    for bits in product((0, 1), repeat=3):
        A = tuple(j for j, bit in zip(opponents, bits) if bit)
        probability = s.prod(q[j] if bit else 1-q[j]
                             for j, bit in zip(opponents, bits))
        derived += probability*joining(i, A)
    assert s.expand(derived-sum(L[i, j]*q[j] for j in I)) == 0

# Actual zero-continuation inertia, including all sure-root boundaries.
# At any Nash root q_i*(Lq)_i >=0. Its sum is strictly negative if two
# owners move. Every one-owner support has a strict positive outsider.
assert all(L[i, j]+L[j, i] < 0 for i, j in combinations(I, 2))
assert all(any(L[i, j] > 0 for i in I) for j in I)

# Every proper quiet child fails literal passive/joining singleton rows.
# A feasible quiet-child weight vector beta>=0 would have
# sum_{i in C} beta_i L_ij >= L_oj, but lhs<=0 and rhs>0 here.
QUIET = []
for C in COAL:
    if len(C) == 4:
        continue
    if C == (0, 2, 3):
        o = 1
        terms = [('F', 2, 1), ('F', 3, 1), ('J', 3, 2)]
    else:
        j, o = next((j, o) for j in C for o in I if o not in C
                    and L[o, j] > 0 and max(L[i, j] for i in C) <= 0)
        terms = [('J', j, 1)]
    coefficients = tuple(sum(w*(-G[i, j] if kind == 'F' else L[i, j])
                             for kind, j, w in terms) for i in C)
    rhs = sum(w*(-G[o, j] if kind == 'F' else L[o, j])
              for kind, j, w in terms)
    assert max(coefficients) <= 0 and rhs > 0
    QUIET.append((C, o, terms, coefficients, rhs))
assert len(QUIET) == 14


def vertices(equalities, inequalities, variables):
    """All vertices of a rational bounded polytope, including singular faces.

    Each inequality is expression>=0. The caller includes cube bounds.
    Every nonempty bounded polytope has a vertex, so this is also an exact
    feasibility test; no nonsingularity of the original equalities is used.
    """
    ans = set()
    for count in range(len(variables)+1):
        for active in combinations(inequalities, count):
            A, b = s.linear_eq_to_matrix(equalities+list(active), variables)
            if A.rank() != len(variables) or A.row_join(b).rank() != A.rank():
                continue
            sol = tuple(A.gauss_jordan_solve(b)[0])
            sub = dict(zip(variables, sol))
            if all(s.expand(f.subs(sub)) >= 0 for f in inequalities):
                ans.add(sol)
    return ans


# An equality-fixed interior vertex has NO active cube inequality. This
# checks the case missed if one insists on exactly three active inequalities.
assert vertices([q[i]-R(1, 2) for i in range(3)],
                list(q[:3])+[1-v for v in q[:3]], q[:3]) == {(R(1, 2),)*3}


# Exhaust all27 states of the complementary three-player induced game.
# State -1=Continue, 0=mix (closed face), 1=Quit. Closure permits repeated
# vertices but loses no roots, including whole positive-dimensional fibers.
SURE_VERTICES = []
for owner in I:
    others = tuple(i for i in I if i != owner)
    variables = tuple(q[i] for i in others)
    gaps = (L*s.Matrix(q)).subs(q[owner], 1)
    all_vertices = set()
    for states in product((-1, 0, 1), repeat=3):
        equations = []
        inequalities = [v for v in variables]+[1-v for v in variables]
        for i, state in zip(others, states):
            if state == 0:
                equations.append(gaps[i])
            else:
                equations.append(q[i]-int(state == 1))
                inequalities.append(state*gaps[i])
        for v in vertices(equations, inequalities, variables):
            full = tuple(1 if i == owner else v[others.index(i)] for i in I)
            all_vertices.add(full)
    SURE_VERTICES.append(all_vertices)
assert SURE_VERTICES == [
    {(1, 0, 0, 1), (1, 0, R(9, 20), 1)},
    {(0, 1, 1, 0)}, {(1, 0, 1, 0)}, {(0, 0, 1, 1)}]
for owner, vv in enumerate(SURE_VERTICES):
    for v in vv:
        assert any(v[j] == 1 for j in I if j != owner)
        assert (L*s.Matrix(v))[owner] <= -R(119, 200)
# The only nontrivial face is precisely the whole stated interval.
t = s.symbols('t', real=True)
assert L*s.Matrix([1, 0, t, 1]) == s.Matrix([
    R(9, 10)*t-1, -R(31, 10)-t, 0, R(9, 10)-2*t])

TRAPS = [A for A in COAL if all(any(i in B and set(B) <= set(A)
         and native(i, B) > 0 for B in COAL) for i in A)]
assert TRAPS == [(2, 3)]
assert J[2, 3] == 4 and J[3, 2] == 1
assert L[2, 3]*L[3, 2] == -2
# Any positive trap-floor weights fail at the GLOBAL inserted set {0}.
assert J[2, 0] < 0 and J[3, 0] < 0
# Indeed every nonzero globally nonnegative floor weight fails: the sum
# of the two singleton inserted rows is strictly negative coordinatewise.
FLOOR_DUAL = tuple(native(i, {0, i})+native(i, {1, i}) for i in I)
assert max(FLOOR_DUAL) < 0
# All nonnegative weighted upper rows fail on some singleton, since their
# sum is (1,1,1,1). Nonnegative participant-premium hypotheses fail too.
assert G*s.ones(4, 1) == s.ones(4, 1)
assert all(any(J[i, j] < 0 for j in I if j != i) for i in I)

# Complete role census of the older passive-pole endpoint guards. Passing
# endpoint guards are NOT asserted to give membership in its eventual ray.
POLES = []
POLE_DETAILS = []
for i, j, k, l in permutations(I):
    a, b = joining(i, [l]), joining(i, [k, l])
    if not (a > 0 and b < 0):
        continue
    c = a/(a-b)
    a2, b2 = joining(k, [l]), joining(k, [i, l])
    l0 = (1-c)*joining(j, [l])+c*joining(j, [k, l])
    l1 = (1-c)*joining(j, [i, l])+c*joining(j, [i, k, l])
    f0 = c*((1-c)*(1+native(l, [l]))
            +c*(1+native(l, [k, l]))-(1+native(l, [k])))
    f1 = (1-c)*joining(l, [i])+c*joining(l, [i, k])
    guards = (a2, b2, l0, l1, f0, f1)
    passed = a2 < 0 and b2 < 0 and l0 < 0 and l1 < 0 and f0 > 0 and f1 < 0
    POLE_DETAILS.append(((i, j, k, l), c, guards, passed))
    if passed:
        POLES.append((i, j, k, l))
assert POLES == [(0, 1, 3, 2), (0, 3, 1, 2)]

# The whole T>=0 ray subtracts T at passive (2,01) and participant
# (2,012). Their paired insertion preserves every joining row. Neither
# coordinate is capped, and coalition012 stays strictly negative.
RAY = {(2, (0, 1)): -1, (2, (0, 1, 2)): -1}
assert all((i, A) not in RAY for i, A in CAPS)
for i in I:
    for A in ((),)+COAL:
        if i not in A:
            assert RAY.get((i, tuple(sorted(set(A) | {i}))), 0) == RAY.get((i, A), 0)

# Every pair has at least one negative joining increment: this blocks
# pair schedules requiring BOTH participants above their passive singleton.
assert all(min(L[i, j], L[j, i]) < 0 for i, j in combinations(I, 2))
# Every cross pair has opposite joining signs: neither a below/below nor
# an above/above cross-pair scheduled phase is available.
assert all(L[i, j]*L[j, i] < 0 for i, j in combinations(I, 2)
           if i//2 != j//2)
# Same-sign reciprocal singleton matrix: no directed escort edge; every
# proper triple has its unmatched negative row, excluding a positive child.
assert all(G[i, j]*G[j, i] > 0 for i, j in combinations(I, 2))
for A in combinations(I, 3):
    assert any(all(G[i, j] < 0 for j in A if j != i) for i in A)
assert G.det() == 45 and min(G.inv()) > 0

if __name__ == '__main__':
    print('PASS: all60, seven strict caps, and every nonnegative global coalition weight excluded.')
    print('PASS: exact additive joining, actual AllContinue uniqueness, all14 quiet rows.')
    print('PASS: entire four sure-owner fibers; every punishment has owner-leave excess.')
    print('PASS: sole trap23, opposite pair index, every floor/upper weight and ProductLow screen.')
    print('Table:', TABLE)
    print('Quiet rows:', QUIET)
    print('Sure-owner fiber vertices:', SURE_VERTICES)
    print('Pole guard passing roles:', POLES)
    print('Pole first-two-guard details:', POLE_DETAILS)
```

## Appendix B. Whole-pencil and complete finite-word verifier

This standalone Python/SymPy program includes the entire rational word and
rechecks the full homogeneous pencil and every actual finite/Never cap.
The physical calendar is the reverse of the construction-order WORD followed
by the sure-quit tail. Save the block as a Python file and run it directly.

```python
"""Exact finite-word stress test for the global anchor raw class.

The rational word was obtained by rounding a numerical positive-index walk.
Its provenance is not a proof premise: this program verifies its complete
actual terminal caps directly. It tests a single accuracy, not A_Z=0.
Run with Python/SymPy.
"""
from fractions import Fraction as F
from functools import reduce
from operator import mul
from itertools import combinations
import sympy as sp

I=range(4)
def prod(xs): return reduce(mul,xs,F(1))
G=[[0,3,-1,-1],[3,0,-1,-1],[-1,-1,0,3],[-1,-1,3,0]]
L=[[0,-4,F(9,10),-1],[-4,0,-1,F(9,10)],
   [-1,F(9,10),0,1],[F(9,10),-1,-2,0]]
passive=[{6:3,10:4,12:F(-1,10),14:4},
         {5:3,9:3,12:F(-1,10),13:5},
         {3:0,9:0,10:0,11:5}, {3:0,5:0,6:0,7:-1}]
Z={}
for i in I:
    for mask in range(1,16):
        t=mask&~(1<<i)
        value=F(0)
        if t:
            value=F(G[i][t.bit_length()-1]) if t.bit_count()==1 else F(passive[i][t])
        if mask>>i&1:
            value+=sum((L[i][j] for j in I if t>>j&1),F(0))
        Z[i,mask]=value
assert len(Z)==60
assert all(Z[i,7]<0 for i in I)  # No positive global coalition weight row exists.
assert all(Z[i,m]<0 for i,m in [(0,7),(0,11),(0,13),(0,15),
                               (1,14),(0,12),(1,12)])
assert Z[2,12]==4 and Z[3,12]==1
assert L[2][3]*L[3][2]==-2
# Strictly negative reciprocal sums exclude every multiowner root at u=0.
assert all(L[i][j]+L[j][i]<0 for i in I for j in I if i<j)
assert all(any(L[i][j]>0 for i in I) for j in I)

# Entire homogeneous pencil, including its genuine full determinant zero.
x=sp.symbols('x')
GM=sp.Matrix(G); LM=sp.Matrix(L); JM=GM+LM
A=GM-x*JM
for j in I:
    assert any(max(A[i,j].subs(x,0),A[i,j].subs(x,1))<0 for i in I)
for i,j in combinations(I,2):
    f=sp.Poly(A[i,j],x);g=sp.Poly(A[j,i],x)
    assert sp.gcd(f,g).count_roots(0,1)==0
for S in combinations(I,3):
    d=sp.Poly(A.extract(S,S).det(),x)
    assert d.count_roots(0,1)==0
d=sp.Poly(A.det(),x)
lo,hi=sp.Rational(81,100),sp.Rational(82,100)
assert d.count_roots(0,1)==1 and d.count_roots(lo,hi)==1
adj=A.adjugate()
assert sp.Poly(adj[0,0],x).count_roots(0,1)==0
assert adj[0,0].subs(x,0)>0
assert sp.Poly(adj[1,0],x).count_roots(lo,hi)==0
assert adj[1,0].subs(x,lo)<0
# At the full zero, adjugate column0 is nonzero and mixed, so rank3 and
# a mixed one-dimensional kernel. No nonnegative full support is possible.
assert GM.det()==45 and min(GM.inv())>0
assert GM*sp.ones(4,1)==sp.ones(4,1)

# Construction order: q[0] is nearest the terminal tail, not the first date.
DEN=10**12
NUMERATORS=[[234389493, 0, 0, 100989800],
 [0, 0, 11719337, 271390815],
 [35446930, 20183552, 0, 404086542],
 [0, 2484533773, 75835509, 0],
 [248391664, 0, 7227094002, 0],
 [20829455976, 0, 0, 722187468],
 [34461948771, 0, 16496869615, 16244653627],
 [52163002852, 0, 17928479912, 47590746960],
 [15509393119, 0, 1651227388, 88278154583],
 [1920644759, 1679687783, 0, 144054435763],
 [0, 437465763544, 15795896110, 0],
 [41913025006, 0, 559544340423, 0],
 [611825407169, 0, 0, 52989439921],
 [475757825287, 0, 226495887902, 264166336764],
 [445448771189, 0, 208483230690, 396518347027],
 [313550230297, 0, 147476107107, 444039660143],
 [25593068069, 0, 0, 437698378844],
 [39035005662, 37498684921, 0, 375874778927],
 [0, 690237995732, 58336265562, 0],
 [64567130873, 0, 670408046382, 0],
 [649747141973, 0, 0, 62828716903],
 [493691024744, 0, 234748311044, 280463769729],
 [452911050426, 0, 213790427423, 406670613079],
 [315378795801, 0, 149246660665, 448473913427],
 [25520868763, 0, 0, 439681534644],
 [39360085566, 37783083142, 0, 376464641718],
 [0, 690734840548, 58547844954, 0],
 [64610604495, 0, 670590069985, 0],
 [649806037248, 0, 0, 62844703581],
 [493718992718, 0, 234761131334, 280489298500],
 [452922664235, 0, 213798727124, 406686132800],
 [315381942958, 0, 149249574904, 448480624006],
 [25520680868, 0, 0, 439684462719],
 [39360536783, 37783469813, 0, 376465592267],
 [0, 690735583939, 58548145412, 0],
 [64610669539, 0, 670590338208, 0],
 [649806123245, 0, 0, 62844727138],
 [493719033875, 0, 234761150187, 280489336088],
 [452922681316, 0, 213798739334, 406686155649],
 [315381947565, 0, 149249579181, 448480633883],
 [25520680597, 0, 0, 439684467031],
 [39360537449, 37783470384, 0, 376465593662],
 [0, 690735585033, 58548145855, 0],
 [64610669634, 0, 670590338603, 0],
 [649806123372, 0, 0, 62844727173],
 [493719033936, 0, 234761150215, 280489336143],
 [452922681341, 0, 213798739352, 406686155683],
 [315381947572, 0, 149249579187, 448480633898],
 [25520680596, 0, 0, 439684467038],
 [39360537450, 37783470385, 0, 376465593664],
 [0, 690735585035, 58548145856, 0],
 [64610669635, 0, 670590338603, 0],
 [649806123372, 0, 0, 62844727173],
 [493719033936, 0, 234761150215, 280489336143],
 [452922681341, 0, 213798739352, 406686155683],
 [315381947572, 0, 149249579187, 448480633898],
 [25520680596, 0, 0, 439684467038],
 [39360537450, 37783470385, 0, 376465593664],
 [0, 690735585035, 58548145856, 0],
 [64610669635, 0, 670590338603, 0],
 [649806123372, 0, 0, 62844727173],
 [493719033936, 0, 234761150215, 280489336143],
 [452922681341, 0, 213798739352, 406686155683],
 [315381947572, 0, 149249579187, 448480633898],
 [25520680596, 0, 0, 439684467038],
 [39360537450, 37783470385, 0, 376465593664],
 [0, 690735585035, 58548145856, 0],
 [64610669635, 0, 670590338603, 0],
 [649806123372, 0, 0, 62844727173],
 [493719033936, 0, 234761150215, 280489336143],
 [452922681341, 0, 213798739352, 406686155683],
 [315381947572, 0, 149249579187, 448480633898],
 [25520680596, 0, 0, 439684467038],
 [39360537450, 37783470385, 0, 376465593664],
 [0, 690735585035, 58548145856, 0],
 [64610669635, 0, 670590338603, 0],
 [649806123372, 0, 0, 62844727173],
 [493719033936, 0, 234761150215, 280489336143],
 [452922681341, 0, 213798739352, 406686155683],
 [315381947572, 0, 149249579187, 448480633898],
 [25520680596, 0, 0, 439684467038],
 [39360537450, 37783470385, 0, 376465593664],
 [0, 690735585035, 58548145856, 0],
 [64610669635, 0, 670590338603, 0],
 [649806123372, 0, 0, 62844727173],
 [493719033936, 0, 234761150215, 280489336143],
 [452922681341, 0, 213798739352, 406686155683]]
WORD=[[F(x,DEN) for x in row] for row in NUMERATORS]
assert len(WORD)==87
assert all(0<=x<1 for q in WORD for x in q)

def endpoints(q,i):
    Q=P=F(0)
    for t in range(16):
        if t>>i&1: continue
        mass=prod(q[j] if t>>j&1 else 1-q[j] for j in I if j!=i)
        Q+=mass*Z[i,t|(1<<i)]
        if t: P+=mass*Z[i,t]
    h=prod(1-q[j] for j in I if j!=i)
    return Q,P,h

def apply(word,U,b):
    U=list(U);b=list(b)
    for q in word:
        un=[];bn=[]
        for i in I:
            Q,P,h=endpoints(q,i)
            un.append(q[i]*Q+(1-q[i])*(P+h*U[i]))
            bn.append(max(Q,P+h*b[i]))
        U,b=un,bn
    assert all(b[i]>=U[i] for i in I)
    return U,b

N=[prod(1-q[i] for q in WORD) for i in I]
P=prod(N)
assert P<F(1,10**35)
assert min(N)<F(1,10**10)
U,b=apply(WORD,[F(0)]*4,[F(0)]*4)
D=sum(b[i]-U[i] for i in I)
assert D<F(1,10**7)
# Put a sure quit by the owner with smallest Never mass after the whole word.
# The actual chronological word is reversed(WORD), followed by this last date.
j=min(I,key=lambda i:N[i])
tail_q=[F(int(i==j)) for i in I]
V,c=apply([tail_q]+WORD,[F(0)]*4,[F(0)]*4)
completed_debt=sum(c[i]-V[i] for i in I)
assert completed_debt<F(1,10**7)
assert all(abs(V[i]-U[i])<=2*max(abs(z) for z in Z.values())*N[j] for i in I)
# Full caps above are exact maxima over every deadline, and include Never.
# For original r_i(A)=Z_i(A)+1, absorption shifts U by1 and every deadline
# payoff by1; Never has a weakly smaller shift. Its debt is no larger.
print('PASS: all60 no-weight raw guards, unique zero-input AllContinue, and rational87-date word')
print('PASS: whole homogeneous pencilR0, including its mixed full singular kernel')
print('PASS: actual88-date absorbing profile has full native/original debt < 1e-7')
print('minimum Never owner:',j,'native debt:',float(D),'completed debt:',float(completed_debt))
print('original prescribed payoff:',[float(v+1) for v in V])
```

## Appendix C. Kernel and signed-separator boundary controls

This standalone Python/SymPy program checks the stationary kernel caps,
the single-owner kernel exception, and a strictly signed separator example.

```python
"""Exact controls for kernel and signed-separator branches, not novelty witnesses.

Run with Python/SymPy. Complete stationary deadline/Never caps are evaluated,
including the single-active-owner deleted-opponent exception.
"""
from fractions import Fraction as F
from functools import reduce
from operator import mul
import sympy as sp

I=range(4)
def prod(xs): return reduce(mul,xs,F(1))

def table(G):
    Z={}
    for i in I:
        for mask in range(1,16):
            if mask.bit_count()==1:
                Z[i,mask]=F(G[i][mask.bit_length()-1])
            else:
                # Signed higher data, including positive participant rewards.
                Z[i,mask]=F(((7*i+11*mask)%35)-17)
    return Z

def stationary(Z,q):
    a=prod(1-t for t in q)
    assert a<1
    E=[sum((prod(q[j] if mask>>j&1 else 1-q[j] for j in I)*Z[i,mask]
           for mask in range(1,16)),F(0)) for i in I]
    U=[x/(1-a) for x in E]; caps=[]
    for i in I:
        Q=P=F(0)
        for t in range(16):
            if t>>i&1: continue
            mass=prod(q[j] if t>>j&1 else 1-q[j] for j in I if j!=i)
            Q+=mass*Z[i,t|(1<<i)]
            if t: P+=mass*Z[i,t]
        h=prod(1-q[j] for j in I if j!=i)
        if h==1:
            assert P==Q==0
            cap=F(0)
        else:
            never=P/(1-h)
            cap=max(Q,never)
            # Every finite deadline n is h^n Q+(1-h^n)never.
            for n in (0,1,2,19):
                assert h**n*Q+(1-h**n)*never<=cap
        caps.append(cap)
    assert all(caps[i]>=U[i] for i in I)
    return U,caps

G=sp.Matrix([[0,2,-1,-1],[2,0,-1,-1],[-1,-1,0,2],[-1,-1,2,0]])
x=[F(1,4)]*4
assert G*sp.Matrix(x)==sp.zeros(4,1)
Z=table(G.tolist());M=max(abs(v) for v in Z.values())
previous=None
for epsilon in (F(1,10),F(1,100),F(1,1000),F(1,10000)):
    U,b=stationary(Z,[epsilon*v for v in x]);D=sum(b[i]-U[i] for i in I)
    assert D<=200*M*epsilon
    if previous is not None: assert D<previous
    previous=D

# A kernel supported on one owner: its deleted-opponent absorption is zero.
Gsingle=sp.Matrix([[0,3,-2,1],[0,0,4,-1],[0,-2,0,3],[0,1,-4,0]])
xsingle=[F(1),F(0),F(0),F(0)]
assert Gsingle*sp.Matrix(xsingle)==sp.zeros(4,1)
Zsingle=table(Gsingle.tolist());Msingle=max(abs(v) for v in Zsingle.values())
for epsilon in (F(1,10),F(1,1000)):
    U,b=stationary(Zsingle,[epsilon*v for v in xsingle])
    assert U==[0,0,0,0]
    assert sum(b[i]-U[i] for i in I)<=3*Msingle*epsilon

# A genuinely signed separator; no positive row can satisfy wGamma>=0.
Gsigned=sp.Matrix([[0,1,-1,-1],[1,0,-1,-1],[-1,-1,0,1],[-1,-1,1,0]])
ones=sp.ones(4,1);w=-ones.T
assert Gsigned.det()!=0
assert Gsigned*ones==-ones
assert w*Gsigned==ones.T
seed=sp.Matrix([-3,-3,1,1])
assert (w*seed)[0]>0 and min(seed[0],seed[1])<0
print('PASS: balanced kernel full caps, sole-owner kernel exception, signed separator seed')
```

## Appendix D. Nonmatching and weighted-block scope controls

This standalone Python program checks the literal raw premises on all sixty
modified rewards and excludes every weak matching relabeling. Its second
complete table passes the weighted-block premise while all64 ordered
singleton-anchor choices fail. These are premise tests; the complete
coverage audit is the family in Section6.

```python
"""Exact raw-scope tests for nonmatching and weighted-block ordered anchors.

This is a premise test, not a novelty separation or an equilibrium computation.
All sixty native rewards are specified; original own levels may all equal one.
"""
from fractions import Fraction as F
from itertools import permutations

I = tuple(range(4))
TABLE = {
    1: (0, 3, 7, -1),
    2: (3, 0, -1, -1),
    4: (-1, -1, 0, -4),
    8: (-1, -1, 3, 0),
    3: (-1, -1, 0, 0),
    5: (F(-1, 10), 3, -2, 0),
    9: (-2, 3, 0, F(-1, 10)),
    6: (3, -2, F(-1, 10), 0),
    10: (4, F(-1, 10), 0, -2),
    12: (F(-1, 10), F(-1, 10), 4, 1),
    7: (F(-1, 10), -2, F(-1, 10), -1),
    11: (-1, F(-1, 10), 5, F(-1, 10)),
    13: (F(-1, 5), 5, 0, F(-11, 10)),
    14: (4, F(-1, 5), F(19, 10), -3),
    15: (F(-1, 10), F(9, 10), F(59, 10), F(-31, 10)),
}
assert len(TABLE)*len(I) == 60
assert all(TABLE[1 << i][i] == 0 for i in I)
C = (0, 1)
D = {2, 3}
for mask, values in TABLE.items():
    A = {i for i in I if mask & (1 << i)}
    active = [c for c in C if c in A]
    if active:
        assert values[active[0]] <= 0
    if A <= D:
        assert all(values[c] <= 0 for c in C)


def matching_order(order):
    a, b, c, d = order
    pairs = ({a, b}, {c, d})
    for i in I:
        for j in I:
            if i == j:
                continue
            same = any({i, j} <= pair for pair in pairs)
            if same and TABLE[1 << j][i] < 0:
                return False
            if not same and TABLE[1 << j][i] > 0:
                return False
    return True


assert TABLE[1][2] == 7 and TABLE[4][3] == -4
assert not any(matching_order(order) for order in permutations(I))
print('PASS: all60 ordered-anchor inequalities; no weak matching labeling exists')

# Restore the original T=0 calibration, then change three displayed entries.
BASE = dict(TABLE)
BASE[1] = (0, 3, -1, -1)
BASE[4] = (-1, -1, 0, 3)
WEIGHTED = dict(BASE)
WEIGHTED[3] = (F(1, 20), -1, 0, 0)
WEIGHTED[13] = (F(-1, 5), F(83, 20), 0, F(-11, 10))
WEIGHTED[15] = (F(-1, 10), F(1, 20), F(59, 10), F(-31, 10))
assert len(WEIGHTED)*4 == 60
assert all(WEIGHTED[1 << i][i] == 0 for i in I)
for mask, values in WEIGHTED.items():
    A = {i for i in I if mask & (1 << i)}
    active = set(C) & A
    if active:
        assert sum(values[i] for i in active) <= 0  # Positive block weights (1,1).
    else:
        assert all(values[i] <= 0 for i in C)
assert [WEIGHTED[m][0]+WEIGHTED[m][1] for m in (3, 7, 11, 15)] == [
    F(-19, 20), F(-21, 10), F(-11, 10), F(-1, 20)]


def singleton_order(order):
    for mask, values in WEIGHTED.items():
        A = {i for i in I if mask & (1 << i)}
        active = [i for i in order if i in A]
        if active and values[active[0]] > 0:
            return False
        if not active and any(values[i] > 0 for i in order):
            return False
    return True


orders = [order for size in range(1, 5) for order in permutations(I, size)]
assert len(orders) == 64
assert not any(singleton_order(order) for order in orders)
assert all(any(values[i] > 0 for mask, values in WEIGHTED.items()
               if mask & (1 << i)) for i in I)
print('PASS: positive weighted block01; every ordered singleton-anchor choice fails')
```
