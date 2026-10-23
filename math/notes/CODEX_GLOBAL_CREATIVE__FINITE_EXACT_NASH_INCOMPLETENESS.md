# Exact finite timing Nash selection can miss every absorbing equilibrium

Identity: CODEX_GLOBAL_CREATIVE.
Status: complete ordinary argument and exact checked control; internal,
not independently reviewed or exported. This is a limitation of a global
research operation, not a new class exclusion or a Fin4 counterexample.
No Lean source was edited or built.

## 1. Question and exact answer

Can the incoming mixed-root predecessor of a strictly positive inert native
source be followed through exact finite timing Nash profiles until it reaches
absorption? Does solving the complete finite timing game again at arbitrarily
large horizons repair the limitation of an exact Nash root stack?

The following rational four-player table gives a negative answer to both
proposals. Own singletons and AllNever pay zero. All sixty rewards are
specified below. Complete stopping laws are private and independent, and
all unilateral finite-date and literal Never replacements are included.

For this SAME table:

1. Every full exact Nash profile with finite finite-date support is either
   literal AllNever, or has exactly one occupied date at which players
   0,1,2 independently Quit with probability 1/2; player 3 always Continues.
   The latter profiles have

       U=B=(3/4,3/4,3/4,7/8), N=(1/2,1/2,1/2,1), nu=1/8.       (1)

2. The auxiliary root game at the positive payoff in (1) has uniquely
   AllContinue Nash. Its incoming half-hazard root is the unique nontrivial
   Nash root at AllNever, hence globally maximizes absorption over that
   entire root Nash set. This incoming root is isolated.

3. No exact full Nash profile with finite finite-date support absorbs almost
   surely. Even the closure of ALL such finite exact Nash semantic tuples
   contains only the two tuples just described. Re-solving unrestricted
   finite timing menus, selecting arbitrary equilibria, moving the occupied
   date and letting the horizon grow cannot lower their Never below 1/8.

4. Nevertheless the stationary law with hazards (1/2,1/2,0,0) at EVERY
   natural date is an absorbing exact full Nash profile, with payoff

       (2,-1,1,1).                                         (2)

   Its K-date truncation followed by AllNever has exact full SUM debt
   2^(-K)+4^(-K), and original joint Never 4^(-K).

5. These finite-exact-Nash and stationary-absorber properties persist on an
   OPEN neighborhood in the 56-dimensional own-zero reward slice.

6. The full singleton matrix is R0, has all eleven nontrivial principal
   minors nonzero, a strictly positive image of a positive vector, and
   degree one, hence is standard Q. The example is not explained by failure
   of these elementary global singleton screens.

The strictly positive source (1) is NOT globally least Never: the minimum is
zero by (2). It is a counterexample to extracting an absorbing comparison
from incoming roots or arbitrary finite EXACT Nash reselection alone. The
non-Nash finite truncations in item 4 do supply that comparison.

## 2. The complete four-player table

Let T={0,1,2}, with next(i)=i+1 and prev(i)=i-1 modulo 3. Player 3 is the
observer. For each nonempty coalition S, define every reward as follows.

For i in T, if 3 belongs to S, put

    Z_i(S)=1 if i belongs to S, and -1 otherwise.           (3)

If 3 does not belong to S and i does not belong to S, put

    Z_i({next(i)})=2,
    Z_i({prev(i)})=-1,
    Z_i({next(i),prev(i)})=2.                              (4)

If 3 does not belong to S and i belongs to S, put

    Z_i({i})=0,
    Z_i({i,next(i)})=4,
    Z_i({i,prev(i)})=-2,
    Z_i(T)=1.                                             (5)

For the observer, put

    Z_3(S)=1 if S meets T and 3 does not belong to S,
           1/2 if S meets T and 3 belongs to S,
           0 if S={3}.                                  (6)

These disjoint cases assign all sixty entries, with |Z|<=4. In particular
all own singletons vanish. Observer rewards are always nonnegative, so
its actual full cap is nonnegative at every continuation profile.

Write P_i(q) for the passive current reward from nonempty opposing quitter
coalitions, Q_i(q) for forced-current Quit reward, and
H_i(q)=product_(j!=i)(1-q_j). At continuation vector v, let

    F_i(q;v)=Q_i(q)-P_i(q)-H_i(q)v_i.                      (7)

Root Nash means F_i<=0 when q_i=0, F_i=0 when 0<q_i<1,
and F_i>=0 when q_i=1. Equivalently, positive q_i requires F_i>=0
and q_i<1 requires F_i<=0.

When q_3=0, direct enumeration of (4)--(5) gives

    F_i(q;v)=2q_next-q_prev-2q_next q_prev
                  -v_i(1-q_next)(1-q_prev), i in T.       (8)

For arbitrary q, (6) gives

    F_3(q;v)=-(1/2)(1-H_3(q))-H_3(q)v_3.                      (9)

These are full root comparisons; no own hazard appears in its own row.

## 3. Complete Nash-root census at continuation zero

If v=0 and q_3>0 is Nash, (9) forces H_3=1, so every core hazard is zero.
Then (3) gives F_i=2q_3>0 for every core owner. They must all Quit surely,
a contradiction. Thus every Nash root at zero has q_3=0.

There can be no sure core quitter. If q_i=1, then (8) gives

    F_next(i)=-1, hence q_next(i)=0;
    F_prev(i)=2, hence q_prev(i)=1;
    F_i=-1, contradicting q_i=1.                         (10)

This argument actually works for every continuation v once q_3=0: each
comparison used in (10) has an opposing sure quitter, so its continuation
coefficient is zero.

At v=0, if q_i=0 and q_next(i)>0, then F_prev(i)=-q_next(i)<0,
so q_prev(i)=0. But F_i=2q_next(i)>0 contradicts q_i=0. If instead
q_next(i)=0 and q_prev(i)>0, then F_next(i)=2q_prev(i)>0 contradicts
q_next(i)=0. Thus a nonzero Nash root has all three core hazards interior.

Put x_i=q_i/(1-q_i)>0. Dividing (8) by the positive H_i gives

    x_prev=2x_next/(1+x_next).                            (11)

The map f(x)=2x/(1+x) is strictly increasing on positive reals. A strictly
increasing map has no nonconstant finite cycle: starting at a value with
f(x)>x forces every subsequent iterate to increase, and f(x)<x forces them
to decrease. The three equations therefore give x_0=x_1=x_2. Their common
positive solution is x=1, hence q_0=q_1=q_2=1/2.

Both this root and AllContinue satisfy all Nash inequalities. They are the
ENTIRE root Nash set at v=0. The nontrivial point is isolated, has survival
1/8, and is the unique root minimizing survival. Its complete successor
payoff and cap are (1): each core row has P_i=Q_i=3/4, and the observer
gets the probability 7/8 that some core player quits.

## 4. The positive successor is inert; the explicit root fold

Let u be the payoff in (1). Since u_3>0, (9) is strictly negative at every
root, forcing q_3=0. Equation (10) again excludes sure core quitters.

If a core hazard q_i=0, then

    F_prev(i)=-q_next(i)-u_prev(i)(1-q_next(i))<0.

Thus q_prev(i)=0. Its predecessor is then forced to zero by the same
argument. Consequently a nonzero root would have all core hazards interior.
In odds coordinates its equations are

    x_prev=(2x_next-3/4)/(1+x_next).                      (12)

The right side is strictly increasing wherever it is evaluated, because
its derivative is (2+3/4)/(1+x)^2. The no-cycle argument again makes all
three odds equal. Their equation is

    x^2-x+3/4=0,

which has negative discriminant. Therefore AllContinue is the unique Nash
root at u.

More generally use the common continuation v=(t,t,t,t), t>=0. The same
boundary arguments apply; when t=0 use Section 3 to remove the observer.
For t>0, (9) removes it immediately. All nonzero roots are interior on T
and satisfy x^2-x+t=0. Thus the COMPLETE root correspondence is:

- t=0: AllContinue and the core half-hazard root;
- 0<t<1/4: AllContinue and two core-diagonal roots with
  x=(1+sqrt(1-4t))/2 or x=(1-sqrt(1-4t))/2, q=x/(1+x);
- t=1/4: AllContinue and the coalesced core root q_i=1/3;
- t>1/4: only AllContinue.

This is an explicit finite-game fold. The isolated incoming half-hazard
branch does not persist to arbitrary positive continuation values. No
external homotopy of continuation vectors is asserted to consist of actual
zero-debt source payoffs.

## 5. No root can absorb against an actual continuation cap

Let v be any actual full continuation cap, so v_3>=0. Suppose a root Nash
q has some sure quitter.

If q_3>0, (9) and root Nash force H_3=1 and v_3=0. Thus all core hazards
are zero, and the sure quitter must be player 3. At q_3=1, each core owner
has F_i=2 by (3), contradicting those zero core hazards.

Hence q_3=0. A sure core quitter is impossible by (10), independently of
the other continuation coordinates, including negative ones. This proves
that no such Nash root has zero joint Continue probability.

The premise v_3>=0 matters in this step. It is supplied by the actual
reward table, not by a false assertion that all occupied conditional Nash
tails have nonnegative payoff.

## 6. Classification of every finite exact full Nash law

Every finite-support complete product law has a finite chronological root
word followed by AllNever; empty calendar dates may be retained or removed.
For any root and actual continuation pair (a,b), the exact formulas are

    a_i'=q_i Q_i+(1-q_i)(P_i+H_i a_i),
    b_i'=max(Q_i,P_i+H_i b_i).

Writing D=sum_i(b_i-a_i), h=product_i(1-q_i), and

    r=sum_i[max(Q_i,P_i+H_i b_i)
          -q_i Q_i-(1-q_i)(P_i+H_i b_i)]>=0,

subtraction gives

    D'=r+hD.                                             (13)

If a finite word is full exact Nash, its first root has r=0 and hence is
Nash against the actual continuation cap. Section 5 makes h>0. Therefore
its suffix also has zero debt by (13). Induction shows that EVERY root is
Nash against its exact full Nash suffix.

Now run through the word in construction order, starting at AllNever.
Section 3 allows only an empty root or the half-hazard core root. Empty
roots leave the zero source unchanged. Once a half-hazard root is used,
the suffix payoff becomes u, and Section 4 permits only empty roots.
Hence there is at most one occupied date, and it has exactly the laws (1).
Conversely those laws and AllNever are exact full Nash, proving the census.

For the complete finite menu 0,...,K-1 plus Never, a Nash equilibrium in
that timing game is already full Nash here: the only omitted queries are
later dates, and their payoffs equal Never because the own singleton is
zero. For arbitrary sparse menus, enlarge to the whole finite calendar
before making this unrestricted claim. The exact-law census above already
tests ALL intervening queries and does not assume sparse-menu Nash is
sufficient.

Thus re-solving complete finite timing games at any horizon, selecting
arbitrary exact equilibria, and taking semantic limits cannot reach an
absorbing point. The exact finite Nash semantic tuples are exactly two
points and their closure has minimum original joint Never 1/8.

## 7. An explicit actual absorbing full Nash profile

At every natural date let players 0 and 1 independently Quit with probability
1/2; players 2 and 3 always Continue. Joint per-date survival is 1/4, so
prescribed play absorbs almost surely. The proposed continuation payoff is

    V=(2,-1,1,1).

The exact root endpoints, in player order, are

    (P_i,Q_i,H_i) = (1,2,1/2),
                     (-1/2,-1,1/2),
                     (3/4,3/4,1/4),
                     (3/4,3/8,1/4).                       (14)

Consequently max(Q_i,P_i+H_i V_i)=V_i in every row, and each prescribed
root mixture attains that value. Bounded Bellman iteration gives the actual
payoffs V: its prescribed survival remainder tends to zero.

For the complete deviation cap, iterate the Continue inequality to any
finite forced date. Each owner's deleted-owner survival has ratio 1/2 or
1/4, hence its bounded continuation remainder tends to zero. This also
prices literal Never. Any randomized complete replacement averages those
pure responses. Thus all deviations are bounded by V, and prescribed play
attains V: this is exact full behavioral Nash.

The negative payoff V_1=-1 is legitimate. There is no date before date zero;
player 1's forced Quit at date zero already gives -1. Its pure Never payoff
is also -1 because player 0 eventually quits alone when player 1 Never.
No inserted empty preemption date is claimed safe for this profile.

For a fully finite check, repeat the same root K>=1 times and then use
literal AllNever. Put e=2^(-K), f=4^(-K). Recursing the complete max formula
gives exactly

    U=(2(1-f), -1+f, 1-f, 1-f),
    B=(2,      -1+e, 1-f, 1-f),
    N=(e,e,1,1),
    D=e+f, nu=f.                                        (15)

The displayed cap includes every finite date after the block and literal
Never, starting from terminal cap zero. Equations (14)--(15) provide both
an actual absorbing equilibrium and explicit finite approximate equilibria.
They show exactly why imposing zero debt at every finite horizon loses the
necessary operation on this table.

## 8. Full singleton screens and overlap

The full singleton matrix is

    Gamma=[ 0  2 -1 -1 ]
          [-1  0  2 -1 ]
          [ 2 -1  0 -1 ]
          [ 1  1  1  0 ].                               (16)

Its principal determinants are 2 for each core pair, 1 for each
core-observer pair, 7 for the core triple, -1 for each other triple, and
21 for the full matrix. Every column has a negative exterior entry. Thus a
nonzero homogeneous LCP solution cannot have singleton support, and any
larger support would contradict the corresponding nonzero principal minor.
Gamma is R0. Also Gamma*(2,2,2,1)=(1,1,1,6)>>0.

For the LCP with offset -1, the only solution is

    x=(1,1,1,0), w=Gamma*x-1=(0,0,0,2).                 (17)

Indeed any nonempty proper core support contains an active i whose next
coordinate is absent. Its equality would be -x_prev-x_3=1, impossible.
If x_3>0, its equality gives sum_T x=1; all core owners must be active by
the preceding observation, and summing their equalities gives
sum_T x=3+3x_3, also impossible. Thus x_3=0 and all core coordinates
are active, giving (17). The active determinant is 7>0 and the inactive
residual is strict. The usual finite-support degree formula gives degree
one, and nonzero R0 degree gives standard Q.

The proper core inverse is

    Gamma_T^(-1)=(1/7)*[2 1 4; 4 2 1; 1 4 2]>>0,

and the outside inverse row is (1,1,1). Therefore this is also deliberately
inside the OLD passive-child existence criterion. It is a solved game used
to test a proposed global mechanism, not a new hard raw-table class.

The present table classifies EVERY exact finite-support full Nash
profile across every calendar, excludes every finite absorbing exact Nash,
and supplies an actual absorbing infinite Nash with finite approximate
truncations. It also gives a complete explicit root-continuation fold.

In this example the predecessor of (1) is AllNever, and
the incoming root already globally minimizes survival over that whole root
Nash set. There is no outgoing nontrivial root at the positive successor.

## 9. Openness and why small root errors matter

The preceding incompleteness is robust under all sufficiently small changes
of the 56 non-own reward coordinates, with the four own singletons kept
zero. Here are the exact compactness and nondegeneracy inputs.

Every non-own observer reward in (6) is strictly positive, and adding the
observer to any nonempty core coalition strictly lowers its reward. These
properties persist on an open neighborhood. Thus actual observer caps stay
nonnegative; at any Nash root with q_3>0 the observer's comparison forces
all core hazards zero and observer continuation cap zero. A sure observer
quitter then gives every core player a strict joining gain, impossible.

With q_3=0, the no-sure-core argument (10) also persists. For a sure owner i,
owner next(i)'s joining increments against {i} and against {i,prev(i)}
are both -1 at the displayed table. Their convex combination remains
strictly negative under perturbation, forcing next(i) to Continue. Owner
prev(i) then has strict joining increment +2 against i and Quits surely;
owner i has strict joining increment -1 against prev(i), a contradiction.
Continuation values drop out of all these comparisons. Thus no root against
ANY actual continuation cap can absorb throughout this open neighborhood.

Let L_ij=Z_i({i,j})-Z_i({j}), L_ii=0, so F(q;0)=Lq+O(||q||^2). Here

    L=[ 0    2   -1    2 ]
      [-1    0    2    2 ]
      [ 2   -1    0    2 ]
      [-1/2 -1/2 -1/2  0 ].                            (18)

L has the same nontrivial principal determinants as Gamma, and each column
of -L has a strictly negative entry. Therefore -L is R0 by the homogeneous
support argument in Section 8. This gives UNIFORM isolation of AllContinue
for nearby tables: otherwise nonzero Nash roots q_n tending to zero for
tables tending to this one, divided by ||q_n||, would yield x>=0, ||x||=1,
-Lx>=0, and x_i(Lx)_i=0, contradicting R0.

At the other root q*=(1/2,1/2,1/2,0), the observer inequality is strict.
The core Jacobian of F at continuation zero is the matrix with next entries
1 and prev entries -2. Its determinant is -7. The implicit function theorem
therefore produces a unique nearby root q*(Z), with all three core hazards
interior and observer hazard zero. Compactness excludes any additional
roots away from neighborhoods of zero and q*: a sequence of such roots for
tables tending to this one would limit to an omitted root of the complete
census in Section 3.

The successor u(Z) stays strictly positive. Its unique AllContinue root is
also stable: small hazards have a uniform strict Continue margin, while
compactness handles hazards bounded away from zero, exactly as in the
positive inert-ball estimate. Therefore all finite exact full Nash profiles
for every table in a sufficiently small open neighborhood again have just
zero or one occupied cohort, the latter q*(Z). Their original joint Never
is bounded below, for example by 1/16 after shrinking the neighborhood.

Finally the absorbing stationary pair persists independently. Its hazards
are explicitly

    q_1=Z_0({1})/Z_0({0,1}),
    q_0=Z_1({0})/Z_1({0,1}), q_2=q_3=0.                (19)

Both ratios stay in (0,1). The active players' stationary values are their
passive singleton rewards Z_0({1}), Z_1({0}). Substitution gives exact
Quit/Continue equality. The inactive players' stationary values are their
passive current rewards divided by 1-(1-q_0)(1-q_1); their strict Continue
margins in (14) persist by continuity. Opponent survival tends to zero for
every player, so the complete finite/Never cap proof from Section 7 applies.
This is an actual absorbing exact Nash producer throughout the open family.
The singleton R0, nonzero-minor, positive-image and degree-one properties
also persist, using the strict finite support census and R0 neighborhood.

This robust failure does NOT survive allowing vanishing finite root errors.
At the displayed table let B^(k) be the cap after k pair roots are prepended
to AllNever, and let r_k be the next root's defect in (13). Directly from
(14)--(15),

    r_0=3/4,       r_k=2^(-k-2) for k>=1,       h=1/4.

Thus the terminal construction starts with a fixed positive error. Its
contribution to the final K-root word is attenuated by 4^(-(K-1)); the
subsequent root errors themselves tend to zero. Their exact weighted sum is

    sum_(k=0)^(K-1) r_k 4^(-(K-1-k))=2^(-K)+4^(-K).     (20)

There is no uniform finite-exact-Nash correction preserving absorption:
(20) approaches zero with nu=4^(-K), while every exact finite Nash has
nu>=1/8. A proposed global obstruction must price root errors AFTER all
later construction-order survival factors, rather than requiring each
finite intermediate word to be exactly Nash or bounding its unweighted
sum of errors. The positive-survival prefix barrier is consistent with
this example because the attenuation here has survival tending to zero.

## 10. Checked code, source correspondence, and remaining question

The durable exact program is
[CODEX_GLOBAL_CREATIVE__FINITE_EXACT_NASH_INCOMPLETENESS_CHECK.py](../experiments/CODEX_GLOBAL_CREATIVE__FINITE_EXACT_NASH_INCOMPLETENESS_CHECK.py).
Run it with Python and SymPy installed. It independently constructs all
sixty entries, derives the symbolic root equations, checks the principal
minor and LCP census, evaluates the actual positive source and absorbing
stationary endpoints, and verifies (15) by full cap recursion for K=1,...,32.
The arbitrary root and calendar classifications are proved above; the
bounded program is not used as a completeness oracle.

The semantic correspondence was inspected in
`quittingTerminalSemanticDebt_prefix_eq_continueMass_mul_of_capNash`
and `quittingTerminalSemanticPrefix_envelope_eq_rootSuccessorPayoff_of_capNash`
(`UniformEquilibrium/Quitting/Root/CapNashRootStack.lean`). Equation (13)
retains the nonnegative root defect rather than imposing cap-Nash as a
hypothesis. `QuittingFiniteDeadlineNashProfile.debt_eq_zero_of_solo_nonpos`
(`UniformEquilibrium/Diagnostics/Quitting/FiniteDeadlineTimingNashDebt.lean`)
confirms why native finite-deadline Nash has no missing late-query debt.
The complete law/behavior bridge remains
`quittingStoppingLawCap_eq_continuationBestResponseValue_stoppingLawProfile`
(`UniformEquilibrium/Quitting/Paths/StoppingLawOperationalDistance.lean`).

The degree steps use the inspected statements
`r0Degree_eq_sum_admissible_inverse_supports`
(`MathUE/LinearProgramming/FiniteSupportDegree.lean`) and
`isStandardQ_of_r0Degree_ne_zero`
(`MathUE/LinearProgramming/R0Degree.lean`), with their nonzero-minor,
positive-image, negative-column and strict inactive-residual inputs supplied
above. No new Lean declaration or build is claimed.

The remaining question is a global approximate-law deformation allowing
terminal debt that vanishes only after a long survival product. Exact finite
Nash correction is not a harmless intermediate step: on this table it
removes EVERY sequence that approaches absorption. The positive selected
source is not least, so a theorem exploiting genuine least-Never minimality
beyond its incoming-root structure could still succeed.
