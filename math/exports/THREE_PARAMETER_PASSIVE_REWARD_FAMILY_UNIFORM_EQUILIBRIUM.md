# Complete closure of a three-parameter passive-reward family

## Exact statement

Let the players be `I={0,1,2,3}`. The live reward is zero. Upon the first
nonempty quitting coalition `S`, player `i` receives `r_i(S)` forever.
All randomizations below are private and independent. A unilateral deviation
may replace the player's complete behavioral strategy, with no horizon,
support, or stopping-time bound.

Define the zero-diagonal matrices

```text
A=[[0,1,-7/10,-1/20],
   [1,0,-1/20,-7/10],
   [-1/20,-7/10,0,1],
   [-7/10,-1/20,1,0]],

Gamma=[[0,2,-69/100,-1/25],
       [3,0,-1/25,-69/100],
       [-1/25,-69/100,0,4],
       [-69/100,-1/25,5,0]].
```

For each player `i` and opponent coalition `T subset I\{i}`, put
`delta_i(empty)=0`, `delta_i({j})=-A_ij`, and
`delta_i(I\{i})=-1`. For the opponent pairs in the order
`01,02,03,12,13,23`, give the smaller outsider contact
`(-1,-1,+1,+1,-1,-1)` and the larger outsider its negative.
This specifies every contact without a strategic input.

Let `L,M,P>=0` be arbitrary finite real numbers, independently
unbounded. Define

```text
F_i(empty)=0,             F_i({j})=Gamma_ij,
F_0({1,2})=-L,           F_1({0,2,3})=-M,       F_3({0,1,2})=-P,
F_i(T)=0 for every other opponent coalition with |T|>=2.
```

For arbitrary finite signed numbers `s_0,s_1,s_2,s_3`, specify all sixty
absorbing rewards by

```text
r_i(S)=s_i+F_i(S\{i})+1_(i in S) delta_i(S\{i}),  S nonempty.   (1)
```

**Theorem.** Every table (1) has an independent periodic profile of period
at most four which is exact terminal Nash against every unilateral behavioral
replacement. For `L>=40` the construction can be chosen proper, stationary,
and with full support.
After deleting any one player's prescribed quitting, absorption still occurs
almost surely. The actual terminal payoff of the constructed profile is one
fixed uniform-equilibrium payoff target. The same profile works for every
positive accuracy and every sufficiently long finite horizon.

**Full reward-tube corollary.** Put `delta_star=10^(-1000)`. For every
`L,M,P>=0`, every signed row offset vector s, and sixty independently chosen
real numbers `xi_i(S)` with `|xi_i(S)|<=delta_star`, the same conclusions
hold for the perturbed raw table

```text
r_i(S)=s_i+Z_i(L,M,P,S)+xi_i(S),
Z_i(L,M,P,S)=F_i(S\{i})+1_(i in S) delta_i(S\{i}).
```

The construction may depend on this actual table, while its profile and
actual payoff are fixed before any equilibrium accuracy or horizon is
requested. The tube width is uniform over the entire unbounded orthant;
no contact-preserving restriction is imposed on the sixty perturbations.

**Unbounded reward-tube corollary for the stationary region.** For
`L>=40,M,P>=0`, put `t=2/[L+sqrt(L^2+4(M+P))]`. The exact stationary
and fixed-target conclusions also hold when the independent raw errors
obey the larger bounds

```text
|xi_i(S)|<=delta_star*t^(-max(|S\{i}|-1,0)).
```

Thus every exterior pair reward and triple-participant reward has allowance
`delta_star/t`, while every exterior triple reward and grand-coalition
reward has allowance `delta_star/t^2`. All remaining coordinates retain
allowance `delta_star`. This entire enlarged region uses the stationary
branch, including `40<=L<=50`.

For `0<=L<=50`, the periodic terminal-Nash, opponent-absorption and
fixed-target conclusions also allow arbitrary finite signed `M,P`,
both for the exact family and its ordinary absolute-width reward tube.
The stationary assertions above retain `M,P>=0`.

**Positive recipient rescaling.** Every stated conclusion also holds for
arbitrary finite `c_i>0` after replacing the native rewards by `c_i Z_i`
and multiplying each applicable coordinatewise error allowance by `c_i`;
the signed offsets `s_i` remain arbitrary. Normalize the absorbing rewards
to `(r_i-s_i)/c_i` and use the same profile: opponent-only absorption is
unchanged, every terminal deviation gain is multiplied by `c_i`, and the
finite-horizon bounds use the actual rescaled reward bound. The variables
`c_i>0` simply enter the finite algebraic raw membership conditions.

The three independent unbounded parameters are part of the raw reward table;
no stationary root, continuation, return word, or rate is assumed.

## Conjecture-facing change and strategic inputs

The theorem closes the explicitly defined three-parameter family. Its
conjecture-facing increment is the remaining region where the pair and
triple penalties have intermediate relative sizes, after accounting for
the applicable earlier producers. The bounded-L periodic branches extend
earlier constructions through coordinates absent from their complete
action-endpoint menus. The sure-owner punishment construction already
covers M>=27/20, and earlier explicit dominance tests cover further
large-scale subregions. These known parts are retained to state one
complete family theorem; they are not counted as separate new exclusions.

The concrete comparison below uses L=100, M=1/10000, P=10000. In particular
P/L^2=1, so this witness is not a small added passive coordinate near the
old pair-penalty ray. It falls outside the named complete earlier raw
criteria, including their allowed role and positive recipient-scale
choices. The whole-prism certificate supplies the missing root production
uniformly across this joint-scale region and joins the known regions into
a complete closure. The ordinary and weighted reward tubes record
robustness of this construction; their dimension and unbounded allowances
are not used as separate claims of counterexample-class reduction.

All three penalties retain their contact-preserving participant
coordinates, including the grand-coalition rewards
`r_1(0123)=s_1-M-1` and `r_3(0123)=s_3-P-1`.

The construction is selected by the following overlapping raw intervals:

| Parameter region | Chronological prescription |
| --- | --- |
| `0<=L<=10`, every `M,P>=0` | repeat `03,02,12,13` |
| `8<=L<=50`, every `M,P>=0` | repeat `12,123,013` |
| `L>=40`, every `M,P>=0` | full-support stationary |

For example choose the first branch for `L<=10`, the second for
`10<L<=50`, and the third for `L>50`. The first two branches construct
all hazards by finite rational contraction certificates at `M=P=0`; their
complete action-endpoint menus then give invariance for every finite `M,P`.
The third branch constructs a positive scale `t`, three compact parameters,
a positive root of a literal stationary endpoint field, and proper hazards.
A finite exact arithmetic certificate produces this root for the entire
compact triangular prism, including its limiting faces. No subsequent
strategic witness remains to be supplied.

The all-behavior conclusion means that the produced profile passes the
complete unilateral-deviation test. The theorem does not assert that
stationary profiles alone cover this orthant or all four-player games.

## Source correspondence

The semantic target is `quittingUniformEquilibriumPayoffConjecture`
(`UniformEquilibrium/Quitting/Conjecture/Basic.lean`). The positive endpoint
`quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
(`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`)
turns terminal approximate Nash existence at every positive error into a
fixed uniform-equilibrium payoff. Here a stronger explicit conclusion is
proved directly: one exact terminal Nash profile has a geometric survival
bound uniform over unilateral replacements, so its actual payoff itself is
one fixed target.

The new mathematics is the reward-to-root producer for (1), including the
whole-prism exact certificate. The semantic endpoint is an existing Lean
declaration. The new producer and its finite certificate are ordinary
computer-assisted mathematics; no Lean check of them is claimed here.

The periodic declarations
`isZeroAsymptoticNash_quittingCyclicBehaviorProfile_of_certificate` and
`isUniformEquilibriumPayoff_quittingCyclicTerminalValue_of_certificate`
(`UniformEquilibrium/Quitting/Cycles/PeriodicCompiler.lean`) consume finite
phase policy identities, root Nash inequalities and opponent-cycle
contraction. The stationary declarations
`isZeroAsymptoticNash_stationary_of_fixedPoint_endpointNash_contracts` and
`isUniformEquilibriumPayoff_of_stationaryEndpointCertificate_contracts`
(`UniformEquilibrium/Quitting/Stationary/EndpointCompiler.lean`) consume the
period-one versions. Parts A--C produce every input to those existing
consumers, and also prove their behavioral conclusions directly.

For the exact unperturbed family (1), the finite membership selector is explicit:
recover `s_i=r_i({i})`, `L=s_0-r_0(12)`, `M=s_1-r_1(023)`, and `P=s_3-r_3(012)`, check `L,M,P>=0`
and all sixty identities (1), and choose a branch by `L`. These
operations require no game-theoretic witness. For the reward tube, membership
is the finite linear feasibility problem given by `L,M,P>=0` and all sixty
inequalities `|r_i(S)-s_i-Z_i(L,M,P,S)|<=delta_star`. Any feasible raw
parameter tuple supplies the algebraic inputs; it does not assume a
strategic certificate. For the bounded-L signed enlargement, drop the
two sign restrictions on M,P and impose L<=50. The enlarged stationary
tail has the finite polynomial membership criterion stated in T9; every
table using its larger allowance is sent directly to the stationary branch.
In the perturbed class, the branch is chosen by a
feasible base parameter L, not by the effective difference of two perturbed
rewards. In particular a perturbation near L=0 need not preserve the sign of
that difference.

## The periodic branches and exact invisibility of both triple penalties

Parts A and B below give complete proofs at `M=P=0`. Changing `M,P` in (1)
affects exactly four native coordinates:

```text
Z_1(023)=-M,         Z_1(0123)=-M-1,
Z_3(012)=-P,         Z_3(0123)=-P-1.                       (8)
```

At a phase with prescribed active set `C`, the tester `i`'s Continue
endpoint uses only rewards `(i,T)` with nonempty `T subset C\{i}`. Its
Quit endpoint uses only `(i,T union {i})` with `T subset C\{i}`. Neither
periodic word above ever presents tester `1` with all of `0,2,3`, or tester
`3` with all of `0,1,2`, simultaneously. Thus none of the coordinates (8)
occurs in any action endpoint,
including endpoints used only by a unilateral deviation. Every policy
recursion, cap equation, root equation, and inactive inequality is therefore
identical to its value at `M=P=0`.

The tail program independently enumerates every such subset for every
phase and every tester and checks this complete-menu invisibility. It
follows that the produced periodic profiles, values and opponent-deleted
absorption bounds below hold for every finite `M,P>=0`. In the two bounded-L intervals the same proof even
permits arbitrary signed finite M,P, since menu invisibility uses no sign.
Only the absolute
reward bound in a finite-horizon estimate changes with `M,P`.

In the local proofs A and B, `Z(L,S)` denotes the `M=P=0` native table
specified in (1). The symbols `p_i,d_i` denote respectively its passive
and contact coordinates, so `p_i=F_i` at `M=P=0` and `d_i=delta_i`.
Equation numbering is local to each part. The symbol `(R)` denotes the
unperturbed base table plus arbitrary signed row offsets. In Part B only,
`delta=1/100000000` is an auxiliary scalar and `(T)` denotes the sixty-entry
perturbed base class `Z_i(L,S)+s_i+xi_i(S)`, `|xi_i(S)|<=delta`.
The exact core theorem uses `xi=0`; the full reward-tube corollary also
uses this perturbation allowance. The exact certificate verifies these stronger
bounds. 
For either periodic branch, write `R=max_(i,S)|r_i(S)|` for the literal
original rewards. Its bounds `(U)` are

```text
|prescribed expected N-stage average_i-u_i| <= K R/N,
deviating expected N-stage average_i <= u_i+K R/N,
actual unilateral N-stage gain_i <= 2K R/N,
```

with `K=21` in Part A and `K=20` in Part B. These quantities may instead
be doubled to absorb either initial live-stage convention without changing
the fixed-target conclusion. The endpoint proofs and geometric estimates
below are independent of that harmless indexing choice.

## Part A. Four-pair construction on [0,10]

## A2. Reduced fields and exact phase values

Index prefix phases by k modulo four in reverse physical order, with

    w=(1,2,0,3), v=(3,1,2,0), S_k={w_k,v_k}.

Thus the physical order k=3,2,1,0 gives the chronological word03,02,12,13, and the physical successor
of phase k is k-1. Use four strong hazards x_k, and define weak hazards

    y_k=x_(k-1)/(5+x_(k-1)),
    C_k=(1-x_k)(1-y_k),    a_k=y_(k+1)/100.

Only w_k and v_k quit in phase k, with hazards y_k and x_k respectively.
For t=k+2 and t=k+3 define successively

    e_k=(w_k+2)y_t(1-x_t)-(1/25)x_t(1-y_t)
                       +p_(w_k)(S_t)x_t y_t+C_t a_k,      t=k+2,
    b_k=-(69/100)y_t(1-x_t)+(w_k+2)x_t(1-y_t)
                       +p_(w_k)(S_t)x_t y_t+C_t e_k,      t=k+3.

The four reduced active fields and eight inactive Continue-minus-Quit
gaps are

    f_k=(1-x_k)b_k-(7/10)x_k,
    I_k=y_k-x_k(1-y_k)/20+C_k a_(k+2),
    O_k=-(7/10)y_k(1-x_k)+x_k-2x_k y_k+C_k e_(k+1).        (4)

For owner w_j assign native phase caps

    V_(w_j)^j=x_j/100, V_(w_j)^(j+1)=a_j,
    V_(w_j)^(j+2)=e_j, V_(w_j)^(j+3)=b_j.                (5)

These assignments cover every owner at every phase. Write P_i^k and Q_i^k
for its literal passive absorption expectation and forced-Quit expectation,
computed from the complete native table Z=r-s, and h_i^k for its opponent
Continue probability. Then the actual endpoint gap at continuation
V_i^(k-1) is

    g_i^k=Q_i^k-P_i^k-h_i^k V_i^(k-1).

Direct finite-coalition expansion gives the following identities:

- g_(w_k)^k=-f_k and g_(v_k)^k=0;
- g_(w_(k+2))^k=-I_k and g_(w_(k+1))^k=-O_k;
- the policy residual V_i^k-q_i^k Q_i^k-(1-q_i^k)P_i^k-C_k V_i^(k-1)
  equals -(1-y_k)f_k for i=w_k and equals zero for the other three owners.

For example, the strong owner's gap is
(1/20)y_k-(1-y_k)x_(k-1)/100=0, exactly by the chosen formula for y_k.
The weak owner's gap is (7/10)x_k-(1-x_k)b_k. The other identities
are one- and two-step passive recursions. The checker reconstructs all
sixty rewards and verifies all sixteen policy identities, all eight active
identities, and all eight inactive identities symbolically.

Consequently a proper root f=0 with I,O>=0 gives every local Bellman
comparison and the prescribed policy recursion. The product of the four
survival factors C_k is strictly below one. Iterating the policy recursion
through a complete cycle therefore identifies V with the actual cyclic
terminal value, rather than an assumed continuation target.

## A3. An exact certificate for every parameter in the interval

The complete checker is Appendix A. It requires Python 3 and SymPy.

Multiply each field and inactive gap in (4) by the positive factor

    B(x)=100 product_k(5+x_k).

The resulting polynomials are denoted F and G respectively. F is affine
in L. The parameter cells are the 256 closed intervals

    [10j/256,10(j+1)/256],   j=0,...,255.                 (6)

They cover [0,10] without gaps. On each cell the checker constructs a
rational center c and preconditioner M, then verifies the following bounds
on the closed state box X={x: ||x-c||_infinity<=rho}, rho=1/400,
and the entire closed parameter cell:

    1/4 < x_k < 9/10 for all x in X,
    lambda=sup ||Id-M D_x F(x,L)||_infinity <1/2,
    sup_L ||M F(c,L)||_infinity/rho+lambda <1,
    every G_j(x,L)>0.                                  (7)

All interval endpoints, coefficients, matrix operations, sums and
comparisons in (7) are exact fractions. Natural monomial interval evaluation
is valid because every coordinate is nonnegative, including the L=0 face.
Coefficient signs determine which endpoint product is lower. Since F is
affine in L, its center residual over a cell is bounded exactly by

    |(M F(c,mid))_i|+|(M partial_L F(c,mid))_i|*(hi-lo)/2.

This retains cancellation through M before taking absolute values.
The derivative bound covers both all state coordinates and all parameters
in that cell. No parameter sample replaces its interval quantifier.

For definiteness, candidate generation starts with
c=(.753,.787,.66,.8), treating those decimals as exact rationals. At each
cell midpoint it forms the inverse center Jacobian, rounds it to denominator
10^15, and performs exactly six updates c<-Round_(10^15)(c-M F(c,mid)).
It then recomputes and rounds M at that final center. The final center is
the next cell's initial seed. No convergence theorem is assumed for this
algorithm: only its posterior inequalities (7) are used. All inverses and
roundings are rational operations and are specified completely in the
standalone checker.

For each fixed L in a cell, x->x-M F(x,L) is a strict contraction of X
into itself by (7). Banach gives a fixed point. The norm bound makes
M D_x F invertible, hence the square matrix M invertible, so that fixed
point satisfies F=0. Positivity of B gives f=0 and I,O>0. This proves a
root for EVERY L in [0,10], including all cell boundaries.

The tested strict inequalities are the proof bounds. Rounded diagnostic
outputs, approximately .07849 for the largest contraction bound and .53254
for the largest self-map ratio, are not proof inputs. The checker does not
depend on stored numerical root data or an untracked discovery file.

The strong hazard bound x_k>1/4 and the formula for y give y_k>1/21.
The upper bounds ensure both hazards are strictly below one. Thus every
produced phase has two distinct players quitting with probability >1/21.

## A4. Complete original-game consumer

At a root, (5) gives bounded actual terminal values and all sixteen endpoint
inequalities. Conditional on any surviving history under any unilateral
complete replacement, a distinct opponent in the current phase still quits
with probability >1/21. Opponent-only survival is therefore at most
(20/21)^t after t dates, regardless of private randomization, horizon
dependence, or the identity of the opponent supplying this bound.

Iterating the Bellman inequalities against an arbitrary behavioral
replacement bounds its expected native terminal reward by the initial cap,
up to a bounded continuation remainder tending to zero geometrically.
The prescribed policy recursion is equality, so its payoff equals that cap.
This proves terminal Nash, including literal Never. Opponent-only absorption
is almost sure under every such comparison; hence every terminal
expectation receives the same absorbing row shift s_i. This justifies (R)
for arbitrary signed s_i without shifting live or Never rewards.

The expected number of zero-paying live dates through the absorbing decision
is at most 21 under every replacement. If the absorption delay is T, the
pathwise difference between terminal reward and its N-stage average is
at most R min(T,N)/N. Taking expectations proves each 21R/N estimate in
(U); comparing prescribed and deviating averages gives 42R/N. One produced
profile and its actual original terminal payoff are chosen for the fixed
table before accuracy, as required.

The inspected semantic consumers are
`isZeroAsymptoticNash_quittingCyclicBehaviorProfile_of_certificate` and
`isUniformEquilibriumPayoff_quittingCyclicTerminalValue_of_certificate`
in `UniformEquilibrium/Quitting/Cycles/PeriodicCompiler.lean`.
The identities and bounds above supply the corresponding policy, root-Nash
and playerwise contraction data. This is ordinary mathematics; no Lean
command or new checked declaration is claimed.

## Part B. Three-phase construction on [8,50] and its reward tube

## B2. Literal endpoints and the two-phase inactive recursion

Use the native perturbed table g_i(S)=Z_i(L,S)+xi_i(S), with g_i(empty)=0.
Restore s only in Section B6. Write the active hazards in increasing owner
order at each phase as

    x=(q_1^0,q_2^0,q_1^1,q_2^1,q_3^1,q_0^2,q_1^2,q_3^2).

Every other hazard is zero. For each owner i and phase k, let mu_i^k be
the independent product law of the opponents' prescribed hazards, and put

    h_i^k=product_(j!=i)(1-q_j^k),
    P_i^k=sum_(B subset I minus{i}, B nonempty) mu_i^k(B) g_i(B),
    Q_i^k=sum_(B subset I minus{i}) mu_i^k(B) g_i(B union{i}). (6)

All caps and endpoints below are literal finite expressions in these raw
rewards. At an active owner-phase pair set V_i^k=Q_i^k. At an inactive pair
recurse forward until the owner's next active phase:

    V_i^k=P_i^k+h_i^k V_i^(k+1).                           (7)

Indices are modulo three. In particular the complete recursion for owner 0
is

    V_0^2=Q_0^2,
    V_0^1=P_0^1+h_0^1 Q_0^2,
    V_0^0=P_0^0+h_0^0(P_0^1+h_0^1 Q_0^2).                 (8)

Owner 3 is inactive only at phase 0, owner 2 only at phase 2, and owner 1
is active at all phases. Hence every V is defined without solving an
infinite continuation equation.

For the eight active owner-phase pairs, in the variable order above, put

    F_i^k(x;L,xi)=Q_i^k-P_i^k-h_i^k V_i^(k+1).             (9)

For the four inactive pairs use the same expression and call it G_i^k.
Our finite certificate is F=0 and all four G<0. At an active root both
actual endpoints equal V=Q. At an inactive pair Continue equals V by (7),
and Quit is at most V. The prescribed policy therefore attains V exactly
and every one-stage action is bounded by V.

For completeness, define

    alpha_k=product_i(1-q_i^k),
    E_i^k=q_i^k Q_i^k+(1-q_i^k)P_i^k,
    W_i^k=V_i^k-E_i^k-alpha_k V_i^(k+1),
    D=1-alpha_0 alpha_1 alpha_2,
    N_i^k=E_i^k+alpha_k E_i^(k+1)
                    +alpha_k alpha_(k+1) E_i^(k+2).       (10)

Then W=0 at inactive pairs and W=(1-q_i^k)F_i^k at active pairs. Direct
telescoping gives

    D V_i^k-N_i^k=W_i^k+alpha_k W_i^(k+1)
                           +alpha_k alpha_(k+1)W_i^(k+2). (11)

At a root, D>0 and V=N/D, the actual prescribed cyclic terminal values.
The checker verifies all twelve policy identities and all twelve versions
of (11), symbolically in L at the center table. Their derivation above is
valid for arbitrary g, hence also for every perturbation in (T).

## B3. Uniform perturbation bounds from finite terminal protocols

Every cap V_i^k is the terminal expected reward in the following finite
protocol: owner i continues through its inactive phases, then quits surely
at its next active phase; the opponents use the prescribed hazards.
Termination is certain by that last phase. Therefore V is a convex average
of native terminal rewards. Its change when all rewards change by at most
delta is at most delta.

Likewise Q_i^k is the terminal average under immediate forced Quit, while
C_i^k=P_i^k+h_i^k V_i^(k+1) is the terminal average under forced Continue
now and forced Quit at the next active phase. Thus, uniformly on [0,1]^8,

    |F(x;L,xi)-F(x;L,0)|_infinity<=2delta,
    |G_i^k(x;L,xi)-G_i^k(x;L,0)|<=2delta.                 (12)

There is also the uniform derivative bound

    |partial_(x_j)F_a(x;L,xi)
                  -partial_(x_j)F_a(x;L,0)|<=6delta       (13)

for every active equation a and every variable j. To prove it, first
temporarily give each chronological Bernoulli trial its own independent
parameter. Differentiating an expectation of a reward perturbation in
[-delta,delta] in one such parameter gives the difference of two conditional
averages, of absolute value at most 2delta. A given hazard variable occurs
at most once in the immediate-Quit protocol and at most twice in the
Continue-to-next-active protocol. The latter maximum occurs for owner 0:
its current phase 2 reappears as the forced-Quit phase one period later.
The chain rule after identifying repeated parameters proves (13).
The checker also enumerates these occurrences for every owner-phase pair.

These arguments handle arbitrary perturbations of all sixty entries,
including own-singleton rewards and entries encountered only after a
unilateral Quit. They do not assume any contact identity is preserved.

## B4. Finite rational root production on 190 parameter cells

Write F^0(x,L)=F(x;L,0) and G^0=G(x;L,0). The total degrees of the eight
polynomials F^0 in (x,L) are

    3,3,4,6,4,9,3,6,

and their nonzero monomial counts are

    7,7,15,63,15,323,7,63.

Every equation is affine in L. All their coefficients have denominators
dividing 100. The checker constructs them from the literal native table,
including the two occurrences of owner 0's current phase.

Use these 190 closed parameter cells, in increasing order:

| Parameter interval | Cell length | Number of cells |
| --- | ---: | ---: |
| [8,10] | 1/20 | 40 |
| [10,15] | 1/10 | 50 |
| [15,25] | 1/5 | 50 |
| [25,50] | 1/2 | 50 |

Endpoints overlap, and there are no omitted parameters. At a shared
endpoint choose the first cell containing L. For each cell [a,b], let
m=(a+b)/2 and h=(b-a)/2. The following finite algorithm constructs a
rational center c, preconditioner M, and positive coordinate radii r.

Let Round_D(z)=floor(D*z+1/2)/D, coordinatewise. The initial center is the
exact rational vector represented by the finite decimal strings

    (.5643795381862795, .19016981154675858,
     .505782937996143, .015790579292830696,
     .4547022016511442, .3514733480515821,
     .04286172661525797, .3045435045232077).                (14)

For each successive cell:

1. Start from the preceding cell's final center, using (14) for the first
   cell, and set M=Round_(10^15)([D_x F^0(c,m)]^(-1)).
2. Perform sixteen updates on the first cell and eight on every later cell:
   c <- Round_(10^18)(c-M F^0(c,m)).
3. Recompute M=Round_(10^15)([D_x F^0(c,m)]^(-1)). Put
   v=M partial_L F^0(c,m) and set

       r_i=ceil(10^12*(2|v_i|h+10^(-7)))/10^12.           (15)

All inversions and updates use exact rational arithmetic; the checker
verifies their successful completion. The decimal seed is not asserted to
be a root, and no convergence theorem for these updates is used. Existence
comes entirely from the posterior bounds on the closed box

    B_c={x: |x_i-c_i|<=r_i for all i}.                    (16)

For A=diag(r_0,...,r_7), use the weighted norm
||z||_r=||A^(-1)z||_infinity. Let

    lambda0=sup_(x in B_c,L in[a,b])
                    ||A^(-1)(Id-M D_x F^0(x,L))A||_infinity,
    b0=max_(L=a,b)||A^(-1)M F^0(c,L)||_infinity,
    t_i=sum_j |M_ij|,
    eta=max_i 2delta*t_i/r_i,
    theta=max_i 6delta*t_i*(sum_j r_j)/r_i.               (17)

The two endpoint values suffice for b0 since F^0(c,L) is affine in L.
By (12)-(13), b=b0+eta bounds the perturbed center displacement, and
lambda=lambda0+theta bounds the perturbed weighted Lipschitz constant.
On every one of the 190 cells, the exact checker proves

    B_c subset (1/500,3/5)^8,
    at least two hazards >1/20 at every phase throughout B_c,
    lambda<2/5,  b<3/5,  lambda+b<99/100,
    sup_(x in B_c,L in[a,b])G^0_i^k(x,L)+2delta<-1/100
                                        at all four inactive pairs. (18)

Thus for every fixed L in the cell and every independent perturbation xi,

    T_(L,xi)(x)=x-M F(x;L,xi)                             (19)

is a contraction of B_c into itself. Indeed its distance from c in the
weighted norm is at most b+lambda<99/100 on the unit weighted box.
Banach's fixed-point theorem gives a unique fixed point of (19) in B_c.
The preconditioner M is invertible: at c the matrix
Id-M D_x F(c;L,xi) has weighted norm less than one, so M D_x F(c;L,xi),
and hence its square factor M, is invertible. Therefore the fixed point
satisfies F=0. All inactive inequalities are strict by (18).

This produces an actual profile for each original table. No continuity of
the selected roots across cell boundaries is required. One may alternatively
define the root as the limit of iterating (19) from c; its selection depends
only on L and xi, and never on an accuracy or horizon.

### Exact arithmetic behind the finite verification

The complete standalone checker is Appendix B. All candidate generation
and acceptance decisions use integers or rational numbers. For interval
evaluation, each endpoint has denominator 10^18. Each polynomial coefficient
has denominator dividing 100. Homogenizing every monomial to a common total
degree gives one integer denominator for each of F^0, its Jacobian, and
G^0. Every variable, including L, is positive on each tested box, so the
monomial interval is obtained by substituting lower endpoints for a positive
coefficient and upper endpoints for a negative coefficient, and conversely
for its upper bound. Summing these integer intervals is an enclosure even
when monomials share variables.

The matrix interval products, weighted row sums, endpoint displacements,
and perturbation corrections in (17) are then compared as exact rationals.
The final floating-point diagnostic line is informational only and is not
used by any acceptance assertion. For orientation its largest certified
image bound is about 0.824913, its largest inactive upper bound is below
-0.0231529, and its smallest hazard lower bound is above 0.0025488.

## B5. Complete behavioral deviations and deleted-opponent absorption

Fix the root just produced. At every phase at least two distinct players
quit with probability greater than 1/20. Deleting any one player's hazard
therefore leaves at least one opponent hazard greater than 1/20 at that
date. Conditional on any live history under any complete replacement of
that player, its prescribed opponents jointly continue with probability
at most 19/20. Consequently

    Pr(survive t dates)<=(19/20)^t,
    expected number of dates up to absorption<=20.        (20)

This bound also holds for the prescribed profile. It uses only opponents'
prescribed private randomization and permits arbitrary history-dependent
or randomized behavior by the replacing player.

The endpoint inequalities from Section B2 hold after every live history.
Iterate them for t dates under a deviation: the expected payoff already
absorbed by that time plus the surviving phase cap is bounded by V_i^0.
All twelve caps are finite, so (20) makes the remaining cap term tend to
zero. The terminal payoff of every complete deviation is at most V_i^0.
For the prescribed profile every one-step inequality is an equality, so
its terminal payoff is exactly V_i^0. This proves terminal Nash against
the full behavioral strategy space, including the strategy that always
continues. Literal Never has probability zero even after that replacement,
because the opponents alone absorb almost surely.

## B6. Signed shifts and the uniform finite-horizon target

Now restore the signed offsets s_i in (T). For each native endpoint,

    Q_i^k -> Q_i^k+s_i,
    P_i^k -> P_i^k+(1-h_i^k)s_i,
    V_i^k -> V_i^k+s_i.                                  (21)

The cap statement follows by induction along (7), starting from an active
cap; in particular it remains valid across both inactive phases of owner
0. Formula (21) cancels in F and G, so the original reward table has the
same policy and Nash inequalities with shifted caps. Nothing shifts the
live or literal Never reward. Such a shift is legitimate here because
(20) proves almost-sure absorption under every relevant full replacement.

Select once and for all

    u_i=V_i^0+s_i.                                       (22)

For any prescribed or unilaterally deviating play, compare its terminal
reward with its N-stage average in the absorbing game. The preabsorption
stages have reward zero. The absolute pathwise discrepancy is bounded by
R times the number of preabsorption dates, truncated at N, divided by N.
Using the harmless convention-independent bound of 20 on the expected
delay from (20) gives discrepancy at most 20R/N. The prescribed terminal
value equals u and the deviating terminal value is at most u, proving all
three inequalities in (U) above.

For every epsilon>0, the same profile and target work for all positive
integers N sufficiently large that 40R/N<=epsilon. If R=0 the claim is
immediate. This explicitly fixes the target before the requested accuracy.

## Part C. Stationary construction for the unbounded region

## Stationary endpoint identity

Write `Z_i(S)=r_i(S)-s_i`. Native own-quitting rewards are zero. For positive
stationary odds `x_i=q_i/(1-q_i)`, set

```text
Pi_i(x)=product_(j!=i)(1+x_j),       h_i=1/Pi_i(x),
D_i(x)=sum_(T subset I\{i}) delta_i(T) product_(j in T)x_j,
E_i(x)=[Pi_i(x)-1] D_i(x).
```

Let `P_i` be the immediate native absorption expectation when player `i`
Continues, with the all-Continue event contributing zero. Let `Q_i` be its
native expected payoff from Quitting now. Independent coalition averaging
gives

```text
P_i=h_i[(Gamma x)_i-L 1_(i=0)x_1x_2-M 1_(i=1)x_0x_2x_3
                                      -P 1_(i=3)x_0x_1x_2],
Q_i=P_i+h_i D_i(x).
```

Consequently the exact stationary endpoint residual is

```text
[(1-h_i)Q_i-P_i]/h_i^2
 =-(Gamma x)_i+L 1_(i=0)x_1x_2
                    +M 1_(i=1)x_0x_2x_3+P 1_(i=3)x_0x_1x_2+E_i(x). (2)
```

This identity includes all simultaneous quitting coalitions. The program
below independently enumerates the literal table (1), both action endpoints,
and the polynomial expression (2), and checks their equality symbolically.
No limiting approximation is used in (2).

## Compactification of the three unbounded penalties

For the stationary branch with finite `L>=40,M,P>=0`, put

```text
t=2/[L+sqrt(L^2+4(M+P))],    alpha=L t,    tau=40t,
b=M/(M+P) if M+P>0, and b=0 otherwise.
```

Then `t>0`, `0<tau<=alpha<=1`, `0<=b<=1`, and

```text
L t+(M+P)t^2=1,      M t^2=(1-alpha)b,
P t^2=(1-alpha)(1-b),       t=tau/40<=1/40.
```

These formulas include `M=P=0`, where `t=1/L` and `alpha=1`; in that
case the choice of `b` is immaterial. Set `x=t z`. Dividing (2) by the
strictly positive `t` yields

```text
H(z,alpha,b,tau)=-Gamma z+alpha e_0 z_1z_2
              +(1-alpha)b e_1 z_0z_2z_3
              +(1-alpha)(1-b)e_3 z_0z_1z_2
              +E((tau/40)z)/(tau/40).                       (3)
```

Every monomial of `E` has degree between two and six, so the final term
extends polynomially to `tau=0`. The exact certificate proves:

**Compact root lemma.** For every point of the closed triangular prism

```text
K={(alpha,b,tau):0<=tau<=alpha<=1, 0<=b<=1},
```

the polynomial field (3) has a root satisfying

```text
1/4 < z_i < 200 for all i.                                  (4)
```

The prism includes the entire projective edge where `(M+P)/L^2` becomes
arbitrarily large, together with every possible relative weight of `M` and
`P`. At `alpha=tau=0` the pair term vanishes and the leading field retains
both triple terms with weights `b` and `1-b`. Points with `tau=0` are
auxiliary polynomial limits, not games with infinite rewards. Every finite
raw table in the stationary region maps to `t>0`, so its certified root
reconstructs the literal stationary equation (2) without a limiting passage.

## Proof of the compact root lemma from the finite certificate

Rescale the state as `z=(40y_0,160y_1,8y_2,30y_3)`. Denote the rescaled
field by `G(y,alpha,b,tau)`. It is a polynomial with rational coefficients.
The verifier clears all coefficients with one positive integer denominator
`C` and uses the dyadic grid denominator `N=2^40`.

The ambient parameter cube is recursively partitioned into closed dyadic
rectangles. For an attempted rectangle `B`, numerical calculations propose
a rational state center `c`, positive rational radii `r_i`, and a rational
matrix `V`, all on the denominator-`N` grid. The proposals are accepted only
if exact integer arithmetic proves, on the entire state box
`X={|y_i-c_i|<=r_i}` and entire parameter rectangle `B`,

```text
1/4 < scale_i y_i < 200,
lambda_i=sum_j sup_(X x B)|(Id-V D_y G)_ij| r_j/r_i <1,
sup_B |(V G(c,alpha,b,tau))_i|/r_i+lambda_i <1.                (5)
```

For each fixed parameter point in `B`, the map
`y -> y-V G(y,alpha,b,tau)` sends `X` into itself and contracts its weighted
maximum norm. Banach's fixed-point theorem supplies a fixed point. The first
Jacobian inequality in (5) implies that `V D_y G` is invertible at the
center; hence `V` is invertible. The fixed point therefore solves `G=0`.
The first inequality gives (4). No uniqueness or compatibility between the
roots chosen in different rectangles is needed.

Here is why each bound in (5) is exact. For the Jacobian, first combine the
four polynomial rows with `V`; this retains all coefficient cancellations.
Evaluate the combined polynomial exactly at the box midpoint, then bound
its change by its seven partial derivatives on the full box: four state and
three parameter variables. All variables have nonnegative interval endpoints,
so each monomial has the elementary lower and upper bounds obtained by
substituting respectively those endpoints. Signed polynomial bounds then
follow by separating positive and negative coefficients. Integer
homogenization with powers of `N` implements these rational operations.

The verifier sharpens the derivative enclosure near `alpha=1` by
grouping the two parameters `alpha,b` exactly. Every derivative polynomial
being bounded is multiaffine in these two variables; its degree in each
is at most one, checked explicitly. For fixed remaining variables, its
value at any point of their rectangle is a convex combination of its four
corner values. The program first substitutes each of those four exact
parameter corners, combining the resulting polynomial coefficients, and
then bounds the five remaining variables by signed monomial intervals.
The minimum of the four lower bounds and maximum of the four upper bounds
therefore enclose the derivative on the entire seven-variable box.
This retains cancellations in factors such as `1-alpha`. The program uses
this rule when `alpha_low>1/2` or `b_low>1/2`, and the preceding signed monomial bound
elsewhere; either bound is valid independently. No numerical assertion
selects whether a proposed box is accepted.

For the center defect, substitute the exact rational state center, combine
through `V`, and expand the trivariate parameter polynomial about the exact
parameter midpoint. The sum of each coefficient's absolute value times the
corresponding half-width powers bounds its absolute value on the whole
rectangle. This also uses only integer arithmetic.

More specifically, let `D` be the largest total degree of a state-Jacobian
entry and let `DY,DP` be respectively the largest state degree and parameter
degree of a field monomial. The program uses

```text
LDEN=C N^(D+2),          DDEN=C N^(DY+1+DP).
```

With radius numerators `R_i=N r_i`, the computed integers `lnums[i]` and
`dnums[i]` satisfy

```text
lambda_i <= lnums[i]/(LDEN R_i),
sup_B |(V G(c,alpha,b,tau))_i|/r_i <= dnums[i]/(DDEN R_i).
```

The two acceptance comparisons are thus exactly the strict inequalities
in (5), with positive denominators cleared. Floats appear only in proposals
and printed diagnostics. They cannot turn a failed rational inequality into
an acceptance.

Every attempted rectangle must have even positive grid widths, checked
explicitly before computing its integer midpoint and half-width. Thus no
half-grid interval is silently rounded down. A failed rectangle is bisected
in one coordinate; a numerical sensitivity heuristic chooses only which
coordinate to split. All root and acceptance conclusions remain exact.

A rectangle with `tau_low>=alpha_high` is discarded: it contains no point
of the ordinary interior of the prism `K`. Every other rectangle is
certified or split. A depth or grid failure aborts without a theorem claim.
For a grid rectangle `[a0,a1] x [b0,b1] x [t0,t1]`, set

```text
u=max(a0,t0),       v=min(a1,t1),
D=(v-t0)^2-(u-t0)^2 if u<v, otherwise 0,
R=2 max(0,a1-max(a0,t1))(t1-t0),
W=(D+R)(b1-b0).
```

The integer `W` is twice the exact volume of its intersection with `K`,
in grid units. This follows by integrating the length
`max(0,min(t1,alpha)-t0)` over the alpha interval, then multiplying by
the b interval length. The verifier checks that `W` is additive at every
binary cut, is zero on every discarded rectangle, and is `N^3` on the
initial cube. Completion requires the accepted sum to be exactly `N^3`.

Boundary coverage does not rest on a volume assertion alone. Every interior
point of `K` belongs to a child after each finite subdivision and can never
belong to a discarded rectangle. When the finite run ends, every such point
therefore lies in an accepted rectangle. The union of the finitely many
accepted closed rectangles is closed, and `K` is the closure of its interior.
Hence every boundary face is covered too, including the entire edge
`alpha=tau=0` and both b endpoints. The contraction test is performed on
all of each accepted rectangle, even its portion outside `K`. Thus it
supplies roots at every boundary point covered by that rectangle.

A successful run is consequently a finite certificate for the complete
parameter quantifier in the compact root lemma, not a sample of roots.

The complete execution of Appendix C accepts 67,171 closed boxes after
138,012 attempts, with maximum subdivision depth22 and total accepted
integer weight `N^3=2^120`. Every acceptance and coverage comparison is exact;
rounded diagnostic values are not proof inputs.

## Behavioral and fixed-target consumer

For an actual table (1) in the stationary region, choose a root from the compact root lemma and set
`x=t z`, `q_i=x_i/(1+x_i)`. All four hazards are strictly between zero and
one. Equation (2) gives `(1-h_i)Q_i=P_i`, so `V_i=Q_i` satisfies both exact
native endpoints

```text
Quit payoff = V_i,        Continue payoff = P_i+h_i V_i=V_i.  (6)
```

Prescribe the same independent hazards at every live date. Opponents have
no time-dependent internal state. Against any complete behavioral
replacement by player `i`, conditional on any surviving history each of its
two actions satisfies (6). Iterating (6) through a finite number of dates
leaves a bounded remainder multiplied by the probability all opponents
survive. That probability tends geometrically to zero. This proves equality
of the prescribed terminal payoff and every unilateral terminal payoff,
including Never and unbounded stopping laws. In particular, no replacement
has a positive terminal gain. The same recursion identifies `V` as the
actual native terminal value, not an assumed continuation.

From (4) and `t<=1/40` one obtains

```text
q_i > (t/4)/(1+200t) >= t/24,       q_i<5/6.                 (7)
```

Deleting any one player's quitting therefore leaves a per-date absorption
probability exceeding `t/24`; one surviving opponent already suffices.
After `k` dates its survival probability is at most `(1-t/24)^k`, uniformly
over all actions and behavioral histories of the deviator. Thus absorption
occurs almost surely under the prescription and every unilateral replacement,
with expected waiting time at most `24/t`.

For the original rewards, adding the same row offset `s_i` to every
absorbing outcome adds exactly `s_i` to every prescribed and deviating
terminal payoff. The almost-sure absorption just proved is essential to
this statement, because the live and Never rewards remain zero. Hence (6)
transfers to an exact terminal Nash profile for the literal original game.
Its actual payoff is `v_i=s_i+V_i`.

Let `R=max_(i,S)|r_i(S)|`. Truncating the absorbing terminal reward to the
first `n` stage rewards costs at most `48R/(t n)` in expectation, uniformly
over unilateral replacements. This bound allows one initial live-stage
convention by bounding the number of unpaid initial stages by the absorption
waiting time plus one. Therefore unilateral finite-horizon gain is at most
`96R/(t n)`, and the prescribed expected average payoff approaches `v`
with the same uniform bound. Given any positive accuracy, choose one large
enough horizon threshold. The same profile then works at every larger
horizon, and `v` was fixed before the accuracy. This is precisely the
uniform-equilibrium-payoff quantifier order.

## Boundary checks and scope

The verifier reconstructs all sixty raw coordinates and proves (2) by exact
symbolic identity. It checks that `Gamma` is nonsingular with strictly
positive inverse. As analytical boundary controls, let `b_j=Gamma^(-1)e_j`.
At `(alpha,tau)=(1,0)`, the vector
`z=b_0/[(b_0)_1(b_0)_2]` is a positive zero of the leading field,
independently of the parameter b. At `(alpha,tau,b)=(0,0,1)`, the vector
`z=b_1/sqrt((b_1)_0(b_1)_2(b_1)_3)` is a positive leading zero. At
`(alpha,tau,b)=(0,0,0)`, the vector
`z=b_3/sqrt((b_3)_0(b_3)_1(b_3)_2)` is another. The finite certificate
treats the complete prism between and beyond these controls, including
`tau=alpha`, which corresponds to the finite boundary `L=40`.

The face `M=P=0` is a valid finite-game boundary, not a division-by-zero case.
As `M+P` grows with `L` fixed, `t` tends to zero but remains positive for each
finite game; the necessary horizon threshold may increase. The theorem
requires no horizon threshold uniform over unbounded reward parameters.
Signed row offsets are unrestricted because the deleted-opponent absorption
bound is proved before translating them.

This result does not decide the unrestricted Fin4 conjecture. In particular,
it does not assert that the independent nonpositive values of all sixteen
higher passive coordinates admit such stationary roots.

## A uniform full-dimensional reward tube

### T2. Normalize the actual own singleton

Replace s_i by s_i'=r_i({i}). The actual normalized table is

    Z_i'=Z_i+xi_i(S)-xi_i({i}),

so its own singleton is exactly zero and its raw native perturbation has
absolute value at most 2 epsilon if the original perturbation is at most
epsilon. Every nonempty passive coefficient changes by at most 2 epsilon;
every nonempty participation contact changes by at most 4 epsilon.
The empty contact remains exactly zero.

All constructions below absorb even after deleting one owner's prescription.
Adding the signed s_i' back therefore adds exactly s_i' to prescribed and
deviating terminal payoffs. No change of live or literal Never payoff is
made or needed.

### T3. Exact four-pair elimination survives general perturbations

Use reverse-chronological phase indices modulo four, with

    w=(1,2,0,3),       v=(3,1,2,0),       S_k={w_k,v_k}.

Notice v_k=w_(k-1). At phase k the strong owner v_k uses hazard x_k and
the weak owner w_k uses hazard y_k. Every other owner Continues. Define
from the ACTUAL normalized table

    c_k=Z'_(w_k)(S_k),
    d_k=Z'_(v_k)(S_k)-Z'_(v_k)({w_k}),
    j_k=Z'_(w_k)(S_(k+1)).

Their unperturbed values are respectively 1/100, 1/20, 1/100. Put

    y_k = x_(k-1)c_(k-1)/(d_k+x_(k-1)c_(k-1)),          (1)
    C_k=(1-x_k)(1-y_k).

For epsilon<=10^(-4), these c and d are strictly positive throughout every
base state box, so (1) is well-defined and 0<y_k<1.

Assign player w_k the active phase values

    V_(w_k)^k=x_k c_k,
    V_(w_k)^(k+1)=a_k=y_(k+1)j_k.

For an inactive owner i at phase t, let R_i^t be its literal passive
absorption contribution from the two active players. Define successively

    e_k=R_(w_k)^(k+2)+C_(k+2)a_k,
    b_k=R_(w_k)^(k+3)+C_(k+3)e_k,
    V_(w_k)^(k+2)=e_k,        V_(w_k)^(k+3)=b_k.

These are exactly the base passive recursions, with all raw coefficients
and hazards changed to their actual values.

At phase k the strong owner's continuation is its weak-phase value
x_(k-1)c_(k-1). Its Quit-minus-Continue gap is exactly

    y_k d_k-(1-y_k)x_(k-1)c_(k-1)=0                  by (1).       (2)

Thus no eight-dimensional implicit-function theorem is required. The
remaining four active equations are

    f_k'=(1-x_k)b_k-x_k aweak_k=0,
    aweak_k=Z'_(w_k)(S_k)-Z'_(w_k)({v_k}).             (3)

The base value of aweak_k is 7/10. Equations (2)--(3) make each active
owner's two endpoints equal. The assigned active value is its forced-Quit
value; the inactive values satisfy the Continue recursion by construction.
At an inactive owner i, the exact Continue-minus-Quit gap is

    Graw_i^k=C_k V_i^(k-1)
       - E[actual contact delta_i(T) at the phase].               (4)

Strict positivity of these eight expressions is the remaining Nash test.
The prescribed policy equations then follow from equality of active
endpoints and the inactive Continue recursion.

The two unbounded triple penalties M,P never occur in these literal menus:
tester 1 never faces all of 023, and tester 3 never faces all of 012.
This includes forced Quit by inactive players. Thus all bounds in this
section are uniform in M,P. The perturbations on those unused coordinates
are harmless for the same reason.

### T4. Uniform elementary bounds for the four-pair perturbation

The base certificate uses x_k in (1/4,9/10) and the positive multiplier

    B(x)=100 product_k(5+x_k).

Keep this SAME multiplier for the perturbed rational fields:
F'=B f' and G'=B Graw'. It need not clear the new denominators; the
contraction proof requires differentiability and bounds, not polynomiality
of the perturbed field. All denominators in (1) stay uniformly positive.

Write Delta for perturbed minus base, at the SAME x and L. Uniformly for
epsilon<=10^(-4),

    |Delta y_k|<=60 epsilon,
    |Delta (d y_k/d x_(k-1))|<=64 epsilon,
    0<d y_k/d x_(k-1)<1.                              (5)

Here c lies in [.009,.011], d in [.049,.051], and x<=.9. For
y=xc/(d+xc),

    |partial_c y|<=x/d<19,
    |partial_d y|<=xc/d^2<5,
    |partial_c (partial_x y)|<=1/d<21,
    |partial_d (partial_x y)|<=c/d^2<5.

The raw changes |Delta c|<=2 epsilon and |Delta d|<=4 epsilon give
(5), using the straight parameter segment; its denominators satisfy the
same bounds. Every other x derivative of y_k is zero.

Consequently |Delta C_k|<=60 epsilon and each individual x derivative
changes by at most 64 epsilon. The base and perturbed C_k have absolute
value at most one and each individual derivative has absolute value at
most one.

All native reward entries actually used in this bounded-L endpoint menu
have absolute value at most 10 before perturbation and at most 11 after.
For an inactive owner,

    R=G_w y(1-x)+G_v x(1-y)+F_pair xy.

Coupling the two Bernoulli y draws and changing the reward coefficients
gives |Delta R|<1400 epsilon. The derivative with respect to x is
G_v(1-y)-G_w y+F_pair y; its change is at most
30*60 epsilon+6 epsilon<2000 epsilon. The derivative through y is
(partial_y R)y'; its change is at most
6 epsilon+30*64 epsilon<2000 epsilon. These exhaust its nonzero x
derivatives. Base and perturbed individual derivatives are bounded by 40.

The following conservative table now follows by the displayed recursions
and the ordinary product rule; each derivative bound is for one x variable:

| Quantity | Absolute change | Absolute derivative change |
| --- | --- | --- |
| a_k=y_(k+1)j_k | 3 epsilon | 3 epsilon |
| e_k=R+C a_k | 1500 epsilon | 2200 epsilon |
| b_k=R+C e_k | 4000 epsilon | 10000 epsilon |
| f_k' | 5000 epsilon | 15000 epsilon |

For clarity, one may use |a|,|partial a|<=1,
|e_base|<=11 and |partial e_base|<=42. Then the largest derivative
comparison, for b, is bounded by

    2000+64*11+1500+60*42+2200=8924<10000.

The f derivative adds at most 4000+4 to the b derivative. Also
B<130000 and every |partial B|<22000. Thus

    max_i |Delta F_i| <=650000000 epsilon,
    max_(i,j) |partial_j Delta F_i| <=3000000000 epsilon.          (6)

For (4), the contact expectation changes by less than 400 epsilon:
all contacts in these inactive two-player menus have absolute value at
most two, their coefficients change at most 4 epsilon, and (5) controls
the hazard change. Its continuation term changes at most
60*11 epsilon+1500 epsilon. Therefore

    |Delta Graw_i^k|<=3000 epsilon,
    |Delta G_i^k|<=400000000 epsilon.                (7)

These bounds are deliberately conservative. They control all sixty raw
perturbations simultaneously; no signs, contact-preserving constraints or
affine restrictions on the perturbation are assumed.

### T5. The finite left-interval certificate has enough margin

The exact 256-cell audit in Appendix A
reconstructs the base polynomial fields and boxes from Part A.
It uses the same radius rho=1/400 and verifies, in every
closed parameter cell,

    ||Id-V D_x F||_infinity<1/10,
    ||V F(center,L)||_infinity/rho+lambda<3/5,
    ||V||_infinity<1,
    every cleared inactive gap G>1.                  (8)

All comparisons in (8) are exact rational comparisons. All 256 cells passed;
no rounded diagnostic is a proof input. The preconditioner V and state
center remain those of the base certificate, not a numerical solve for a
perturbed table.

By (6), perturbing the contraction constant costs at most
4*3*10^9 epsilon, and perturbing the normalized center defect costs at
most 400*650000000 epsilon. Their sum is at most

    272000000000 epsilon.

At epsilon<=10^(-12), the perturbed self-map sum is strictly below
3/5+.272<1, and the derivative norm is below .1+.012<1. Equation (7)
keeps every inactive gap positive, since its loss is at most .0004.
The same closed box therefore contains a zero of F' by Banach, and the
same norm bound makes V invertible. This zero solves all four actual
equations (3).

The strong hazard exceeds 1/4. From c>.009, d<.051 and x<.9,

    y > (.25*.009)/(.051+.9*.011) > 1/30.

Thus every phase has a distinct prescribed opponent quitting with
probability greater than 1/30 after any one player's replacement. Full
behavioral endpoint iteration and geometric absorption prove exact terminal
Nash and a uniform-payoff target, with expected absorption delay at most 30.
The finite-horizon constants may be changed accordingly from the base
four-pair proof, replacing 21 by 30 for perturbed tables.

### T6. Uniform stationary perturbation on the entire compact prism

This section uses the accepted-box inequalities of Appendix C. It requires
no additional numerical guard.

For positive stationary odds x=t z, define, for each recipient i,

    Pi_i=product_(j!=i)(1+t z_j),
    P_i=sum_(nonempty T) F_i(T) t^|T| z_T,
    D_i=sum_(nonempty T) delta_i(T) t^|T| z_T,
    H_i=[(Pi_i-1)D_i-P_i]/t.                          (9)

Here H is the stationary field, not an opponent survival probability.
Own-singleton normalization makes the empty coefficients vanish, so (9)
extends polynomially across t=0. The base L,M,P coefficients are those
removed by the compactification in Part C.

On 0<=t<=1/40, 0<z_i<200, put x_j=t z_j<=5. Then

    Pi_i-1<=215,
    sum_(nonempty T)t^(|T|-1)z_T <=600+3000+5000=8600.

Using the raw changes from Section T2 gives

    |Delta(P_i/t)|<=17200 epsilon,
    |Delta(D_i/t)|<=34400 epsilon,
    |Delta H_i|<=7413200 epsilon<7500000 epsilon.     (10)

For an opponent coordinate z_j,

    |partial_(z_j) Delta(P_i/t)|<=72 epsilon,
    |partial_(z_j) Delta(D_i/t)|<=144 epsilon,
    |partial_(z_j) Pi_i|<=36/40.

Hence

    |partial_(z_j) Delta H_i|
      <=72 epsilon+(36/40)*34400 epsilon+215*144 epsilon
      =61992 epsilon.

The state scales are z=(40y_0,160y_1,8y_2,30y_3), so

    max_(i,j)|partial_(y_j) Delta H_i|
      <=9918720 epsilon<10000000 epsilon.             (11)

These estimates are independent of L,M,P. Unbounded passive penalties
cancel from the differences because the stationary field is linear in all
reward entries. The triple contact-preserving companions of the base
family are not imposed on the perturbation.

### T7. Integer slack supplies an explicit preconditioner bound

The stationary verifier uses N=2^40. Its rational state centers,
preconditioners and radii are N-grid quantities. The base field has common
coefficient denominator C=200; the total degree of its y-Jacobian is 10.
For every accepted cell:

- its entire state box has 1/4<z_i<200;
- its weighted Jacobian error lambda_i is strictly below one;
- its weighted center-defect-plus-error is strictly below one;
- both integer denominators LDEN and DDEN equal 200 N^12.

Let J be the center Jacobian and V the rational preconditioner. Since each
J entry has denominator dividing Q=200 N^10, nonsingularity implies

    |det J|>=Q^(-4).

Nonsingularity follows from ||Id-VJ||_r<1, not from a floating-point
matrix inversion. On the full unit parameter rectangle and 0<z<200,
every Jacobian entry has absolute value below K=10^10. For example its
four possible contributions are bounded respectively by 800, 32000,
6400000 and 2476800; the last is the contact term in (9). This bound also
holds on parts of a certified rectangle outside the triangular prism.
For the contact contribution, every base contact coefficient has absolute
value at most one. Consequently |D_i/t|<=8600,
|partial_(z_j)(D_i/t)|<=36 and |partial_(z_j)Pi_i|<=36/40. Its y-derivative
is bounded by 160*((36/40)*8600+215*36)=2476800, as asserted.

Each 3-by-3 cofactor has absolute value at most 6K^3, so

    ||J^(-1)||_infinity<=24K^3 Q^4.

Write real state radii as r_i=R_i/N with positive integers R_i. The smallest
state scale is eight, so each entire y-interval lies in
(0,25). Thus r_max<25, r_min>=1/N and R_i<200N. With E=Id-VJ,

    ||Id-E||_infinity<=1+||E||_infinity<1+25N<200N,
    ||V||_infinity=||(Id-E)J^(-1)||_infinity
                  <=4800 N K^3 Q^4 <10^577.           (12)

The last strict inequality follows directly from N<10^13, K=10^10,
Q=200N^10. It is intentionally very loose.

Since LDEN=DDEN, the accepted row's self-map sum is

    (integer lnum_i+integer dnum_i)/(200 N^12 R_i)<1.

Its distance below one is therefore at least

    1/(200 N^12 R_i)>1/(40000 N^13)>10^(-174).         (13)

This conclusion uses only exact integer acceptance and the state-box bounds.
It does not read or trust a rounded maximum of diagnostic residuals.

By (10)--(12), the perturbation to the weighted derivative norm is less
than 10^600 epsilon, and that to the weighted center defect is less than
10^597 epsilon. Their sum is below 10^601 epsilon. At
epsilon<=10^(-1000), this is below 10^(-399), hence below the exact slack
(13). The base box still maps strictly into itself. Because the unperturbed
center defect is nonnegative, the same self-map slack (13) also bounds
the distance of its derivative norm below one. The new derivative norm
is consequently less than one. Banach supplies a root of the perturbed field.
Invertibility of V is unchanged.

For an actual finite L,M,P in the tail region, t>0. The resulting positive
z gives proper full-support hazards x/(1+x), and the literal stationary
endpoint equations hold for Z'. The same state box keeps z>1/4 and z<200.
The same geometric opponent-absorption argument therefore applies with its
current lower bound t/24. No projective boundary point is executed as a
finite game.


### T8. Covering the absolute-width tube and fixing the target

Take any representation of a table in the full reward tube with base
parameters L,M,P>=0. For L<=50 the same argument permits arbitrary signed
M,P. Normalize its own singleton as in T2. This changes
neither the base parameters nor the two complete-menu invisibility
identities. It gives a native perturbation bounded by 2 delta_star.

For 0<=L<=10, T3--T5 apply directly to the actual raw perturbations with
epsilon=delta_star<10^(-12). The two arbitrary base triple penalties are
invisible to every endpoint of the four-pair construction, including the
endpoints of a player who departs from the prescription. For 10<L<=50,
use Part B on the normalized native table: its perturbation size is at most
2 delta_star<10^(-8), and the same complete-menu argument removes both
base triple penalties. For L>50, T6--T7 apply using the original raw error
epsilon=delta_star and the positive compactification scale of that base
L,M,P. These three regions cover every allowed base representation.

Each branch produces exact endpoint identities or inequalities for the
actual table and absorption after deleting any one player's hazard, with
expected delay bounded respectively by 30, 20, or 24/t. The proofs of the
behavioral consumers in Parts A--C therefore apply to the actual perturbed
table. In particular, restoring the actual signed own-singleton offsets is
valid because opponents cause absorption almost surely against every
deviation. The prescribed profile's actual terminal expectation is one
fixed payoff vector. The same finite-horizon truncation estimate, with the
actual finite reward bound, shows that this one profile approaches that
vector and has vanishing unilateral gain on all sufficiently long
horizons. No choice made here depends on the requested equilibrium
accuracy or on a horizon.

### T9. Unbounded weighted reward tube in the stationary tail

Apply the stationary construction for L>=40. Fix arbitrary finite
L>=40 and M,P>=0, and put

    t=2/(L+sqrt(L^2+4(M+P))).

Then t>0, Lt+(M+P)t^2=1 and t<=1/40. Set eta=10^(-1000).
For arbitrary signed row offsets s_i and all sixty independent raw
perturbations satisfying

    r_i(S)=s_i+Z_i(L,M,P,S)+xi_i(S),
    |xi_i(S)|<=eta*t^(-max(|S\{i}|-1,0)),            (14)

the game has an exact stationary terminal Nash profile against every
complete unilateral behavioral replacement, with almost-sure opponent-only
absorption. Its actual payoff is one fixed uniform-equilibrium payoff
target.

Thus own singletons, exterior singletons and pair participants retain
absolute width eta. Exterior pair rewards and triple participants have
width eta/t; exterior triple rewards and grand-coalition participants have
width eta/t^2. All signs and all sixty coordinates remain independent.
This tail statement contains the ordinary absolute-width tube. Together
with the ordinary absolute-width result, it is one stronger reward-table
producer. Its entire range L>=40 uses the stationary branch, including
40<=L<=50; the larger allowances are not passed to the middle periodic
branch.

There is a finite algebraic criterion for membership in this added tail
class. Given a raw table r, seek real numbers s_i,L,M,P,t satisfying

    L>=40, M>=0, P>=0, t>0, Lt+(M+P)t^2=1,
    |r_i(S)-s_i-Z_i(L,M,P,S)|*t^max(|S\{i}|-1,0)<=eta
                  for every one of the sixty coordinates.

Each absolute-value inequality is two polynomial inequalities. These
reward-scale and row-offset variables are all the required inputs; no
hazards, continuation values or strategic witnesses are assumed.

To prove this, fix the actual positive t before considering perturbations.
For an opponent coalition T of size k>=1, own-singleton normalization
subtracts a number of absolute value at most eta. Since t<=1,

    |Delta F_i(T)|<=2 eta*t^(-(k-1)),
    |Delta delta_i(T)|<=4 eta*t^(-(k-1)).             (15)

The empty normalized coefficients are zero. The bounds in (15) are
conservative: subtraction of the own singleton cancels when forming a
contact, but no improvement is needed.

On every certified state box, 0<z_i<200. Define

    S_i=sum_(nonempty T subset I\{i}) z_T.

Then S_i<=3*200+3*200^2+200^3=8120600. The factors t^(k-1)
in P_i/t and D_i/t cancel the allowed growth in (15), giving

    |Delta(P_i/t)|<=2 eta*S_i,
    |Delta(D_i/t)|<=4 eta*S_i.

Because Pi_i-1<=215, the actual stationary field satisfies

    |Delta H_i|<=862*8120600 eta
                 =6999957200 eta<7*10^9 eta.         (16)

For an opponent coordinate z_j,

    sum_(T containing j) z_(T\{j})<=201^2=40401,
    |partial_(z_j)Pi_i|<=36/40.

Differentiate with the fixed t and fixed raw table. Equations (15)--(16)
give

    |partial_(z_j)Delta H_i|
      <=[2*40401+(36/40)*4*8120600+215*4*40401]eta
      =64059822 eta.

Multiplying by the largest state scale, 160, yields

    max_(i,j)|partial_(y_j)Delta H_i|
       <=10249571520 eta<11*10^9 eta.                (17)

Choose any accepted base parameter cell containing this actual finite
L,M,P compactification point, and use its state box and preconditioner.
No continuity of xi as a function of L,M,P is required: (16)--(17) hold
on the entire state box at the one fixed parameter point to which Banach
is applied. In particular no reward table with infinite entries at t=0
is introduced or executed.

By (12), the weighted derivative perturbation costs less than

    200 N*10^577*4*(11*10^9) eta<10^603 eta,

and the normalized center defect costs less than

    N*10^577*(7*10^9) eta<10^600 eta.

Their sum is less than 10^604 eta=10^(-396), which is smaller even
than the integer slack 10^(-174) in Section T7.
The same Banach box therefore supplies a zero of the actual perturbed
stationary field at this fixed parameter point.

The positive odds t z_i give proper stationary hazards

    q_i=t z_i/(1+t z_i)>t/24.

Thus after deleting any one owner's prescription, a prescribed opponent
quits each stage with probability greater than t/24. Opponent-only
absorption has finite expected delay at most 24/t. The exact stationary
endpoint equations and iteration against every behavioral deviation give
terminal Nash. Every individual table in (14) is finite because t>0,
so bounded-reward truncation and this geometric absorption bound give
the fixed-target uniform-payoff conclusion. The signed row offsets may
be restored because absorption is almost sure under every unilateral
replacement.


## Exact off-ray boundary and concrete raw-class comparisons

Take the table (1) at `L=20`, `M=1/10000`, `P=0`, and `s_i=1` for every owner.
All sixty rewards are fixed by (1). In particular the two row-zero rewards
at 12 and 012 are -19 and -18, and the two row-one rewards at 023 and
0123 are `9999/10000` and `-1/10000`. Call this table W. The distinctions
between native and original rewards are essential here.

The exact finite program below establishes that W has no stationary
terminal Nash profile on any support, and that it has no proper periodic
Nash profile using the chronological word 03,02,12,13. These are tests of
restricted architectures. The theorem above supplies W's equilibrium with
the different word 12,123,013.

### Every stationary support and a positive stationary regret gap

Let q be a stationary hazard vector. Write h_i for opponent Continue mass,
P_i for the immediate native Continue absorption expectation, Q_i for the
native forced-Quit expectation, and

    R_i(q)=(1-h_i)Q_i-P_i,    D_i(q)=Q_i-P_i.

For an owner with absorbing opponents the exact stationary comparisons
are R_i=0 at a proper hazard, R_i<=0 at zero hazard, and R_i>=0 at sure
hazard. The program reconstructs these polynomials from the complete raw
table. A rational tensor-Bernstein and interval-Newton subdivision proves

    {q in [0,1]^4 : R_i(q)=0 for all i}={0},
    {q in [0,1]^4 : q_m=0, R_i(q)=0 for i!=m}={0}

for each m. The full system uses251 subdivision nodes, and the four
omitted-coordinate systems use69,103,31,55. These statements concern
entire closed cubes, not sampled roots. Every accepted leaf is excluded
by a strict polynomial sign, a disjoint interval-Newton image, or contraction
uniqueness at the known origin. The complete rational programs are included.

On a proper two-owner support {i,j},

    R_i=q_j[-Gamma_ij+q_j J_ij].

Every J_ij is positive. Favorites have Gamma_ij=J_ij+1, while crossings
have Gamma_ij<0; consequently no proper pair can satisfy its active
indifference equations. All singleton and pair contacts are nonzero.
The exact contact identity

    sum_i(1-q_i)D_i(q)
      =-(1/4)sum_j q_j product_(k!=j)(1-q_k)
       -sum_i(1-q_i)product_(j!=i)q_j

excludes full support with both sure and proper owners. In that case every
proper owner faces a sure opponent and has D_i=0, whereas the right side
is strictly negative. The all-sure profile has joining contact -1.
With one sure and two proper owners, the proper owners' affine contact
equations leave only support012 with sure1 and support023 with sure2.
Their actual stationary residuals at the sure owner are respectively
`-265/578` and `-150/289`. With two sure owners, a remaining proper owner
faces a nonzero pair contact. The program also checks every pure support.

AllNever gains1 by immediate Quit. On a singleton active support j, any
crossing observer i receives `1+Gamma_ij` while immediate Quit gives
`1+q_j J_ij`, a strict improvement. These cases exhaust all stationary
profiles, including every sure face.

The infimum of complete behavioral terminal regret over stationary
profiles is positive. Otherwise choose stationary profiles with regret
tending to zero and take a convergent subsequence. A limit with at least
two active owners has contracting opponents for each owner; the prescribed,
immediate-Quit and Never values are continuous there and give an exact
stationary equilibrium. A one-active-owner limit has the same strict
crossing-observer improvement. At the remaining limit q=0, normalize
`z=q/sum_i q_i` and take a simplex limit. The fixed finite higher rewards
contribute only `O(sum_i q_i)` to normalized terminal values. Immediate
Quit and Never comparisons force

    Gamma z>=0,     z_i(Gamma z)_i=0,     sum_i z_i=1.

A simplex vertex has a negative crossing coordinate in Gamma z and is
already impossible. In every other case the displayed complementarity
follows from the prescribed versus Never comparison. Direct exact inversion
gives Gamma^-1 strictly positive. If Gamma z is zero, invertibility is a
contradiction; otherwise `z=Gamma^-1(Gamma z)` is strictly positive, which
forces Gamma z=0 by complementarity. This excludes the only discontinuous
limit. No numerical lower bound on the positive regret gap is asserted.

Thus every prior raw criterion whose conclusion here is an exact stationary
profile or stationary profiles of vanishing complete regret fails, including
all choices of auxiliary parameters and representations. This includes
stationary response quotients, guarded crossed-response criteria,
polynomial-row-weight and columnwise odds-order tests, passive and
participant pole/jackpot producers, contact-preserving positive/negative
bonus producers, and stationary domination tests. The own rewards are
positive and det Gamma is nonzero, so their negative-sole-owner and
singular exceptions cannot supply an alternative conclusion on W.

### Punishment, child, premium and payoff tests

The contact identity also permits a full sure-base punishment-root census.
The only possible sure-plus-two-proper roots are the two supports just
listed. Their sure owner's contact expectation is `-27/68` and opponent
survival is `5/17`. Every participant reward for owners1 and2 is at least
`-1/10000`; therefore immediate Quit guarantees at least that amount
against arbitrary opponent laws. At any admissible punishment continuation,
the sure owner's Quit-minus-Continue gap is at most

    -27/68+(5/17)(1+1/10000)<0.

This uses the changed grand reward rather than incorrectly retaining a
nonnegative punishment floor for owner1. Pure sure bases, one proper owner,
and the full-support sure faces fail by the contact census. Every sure-root
selection is consequently rejected, including mixed free-owner completions.
All-proper punishment roots remain a different supplied input.

Each of the14 nonempty proper child sets has a pure full-behavior child
Nash profile with zero child debt and zero joint Never, but a strict omitted
joining gain. For triple children012,013,023,123 use coalitions02,13,03,12,
respectively. Crossing pair children use both owners; favorite pair children
use a singleton; singleton children use their sole owner. The sign tests are
literal contacts and are checked for every child. Hence every universal
nonnegative weighted child-debt/joint-Never quiet-lift inequality fails for
every child selector and all its weights. This does not exclude a selected
favorable child law.

All twelve ordered participant-pair native premiums are strictly positive.
This defeats every proper premium-core/support-peeling choice, every first
marked block with positive weights, product-low pair tests and every
nonzero nonnegative supportwise upper average. The larger-charge option in
the mixed upper/charge criterion cannot apply to a pair. Positive crossing
contacts defeat all weak, strict and positively weighted trap-leaver
alternatives. Native grand rewards are negative in every row, also defeating
global participant-floor premises.

A finite common-hazard word gives a strict all-coordinate payoff witness.
Use hazard1/100 independently for100 dates and then Never. Its native
stationary value vector is

    (4176707,8889899,12809507,16730699)/15761596
       -(0, (1/10000)(1/100)^3/[1-(99/100)^4], 0, 0).

Every entry exceeds1/4 and `(99/100)^400<1/5`. Its actual finite-word
original payoff is therefore strictly above the own-one vector in every
coordinate. This rejects all universal strict-deficit, weak-subset,
nonconcentrated-weight and nonzero social-upper selectors, including all
their subset and weight choices.

### Complete concrete periodic and singleton selectors

The singleton invariants are unchanged:
`det Gamma=474131399/4000000>0`, Gamma^-1 is strictly positive, every
principal triple is nonsingular with a negative inverse diagonal, and the
positive singleton graph is exactly the two favorite two-cycles. The
homogeneous LCP has no nonzero solution; offset-1 forces full support and
its unique solution Gamma^-1*1 has positive index. These reject the non-Q,
non-R0, degree-not-one, nonnegative singleton column, negative-determinant
inverse and deleted-triple inverse exits. Opposite-sign reciprocal and
positive directed three/four-cycle selectors fail under every relabeling.
Favorite contacts are negative and each favorite J=Gamma-1, rejecting
negative-pair-funded, mixed-positive-pair and triple-collision-box tests.

All positive invariant-cone pair matrices fail their favorite joining cap:
for each crossing matching, one cap forces a row-ratio maximum R_ab<1
and the corresponding reverse cap forces R_ba<1, impossible for a positive
matrix. Bounded inverse corners satisfy `ell_i<=c_i/8<J_i,f(i)` and
fail as well. Nonpositive unscheduled participant caps fail in the
two-pair join-cap, crossed-matching and signed-inverse-column criteria.

The complete repeated-pair fixed-tube criterion leaves8 matching roles.
The exact scalar bracket test rejects3 by its raw M0 guard,3 by a wrong
left-face sign, and2 by a wrong right-face sign. These signs concern the
whole prescribed bracket, using exact monotonic scalar root enclosures;
they do not merely reject one approximate root.

For the flexible crossing-completion criterion, all8 roles fail a positive
transport test at `x=1,y=106/1000`, with value at most `-83/250`.
Singleton ratios and favorite increments leave only the identity
representation for the signed and compensated branches. The signed branch
has inactive output `-359623/1512000<0` at its stated box corner, while the
compensated branch requires the false inequality `-20>=-3`. The common
negative-passive tube has zero higher coordinates and fails its strict
negative upper bound. These tests are unchanged by the new row-one triple
coordinate. The canonical word is additionally excluded for every proper
hazard, by139 exact subdivision nodes; that stronger word exclusion is not
needed to reject its particular raw box criterion.

The former sparse ray and its radius10^(-8) full reward tube also fail.
At every candidate first parameter the row-one difference between changed
and unchanged coordinates has range1/10000, greater than twice the radius;
an additive row shift cannot remove it. The exact program checks all24
relabelings and positive recipient scales: singleton and participant-pair
intervals leave only the identity role with row scales arbitrarily close
to1 within explicit rational intervals, and the row-one grand comparison
then still fails by a strict margin. This also excludes the earlier
isolated radius10^(-8) sparse cube and the middle-interval tube.

The literal long-period and explicit local families are separated by the
same invariants: positive participant-pair premiums exclude families
requiring a negative designated pair; unequal negative singleton magnitudes
with ratio69/4 exclude the equal-crossing and E1 explicit cube/cylinder
families; favorite J/Gamma ratios `(1/2,2/3,3/4,4/5)` exclude the
thirty-three-phase, weak-crossing, Jordan and complex-spectrum literal
families. The older microscopic revisit cube is excluded by its native
grand-coordinate scale bound versus its favorite singleton. The general
cubic periodic producer requires six positive passive pair slopes and two
positive passive triples, whereas all higher passives of W are nonpositive.
All these comparisons include the whole displayed raw parameter sets and
positive row scalings, not just a printed center.

### Scope of the bounded-L comparison

The off-ray witness above is a useful exact boundary check, but its
periodic producer is an endpoint-menu extension of an earlier bounded-L
construction. It is not used as the substantive significance witness.
The later joint-scale comparison explicitly accounts for the known
punishment and dominance regions and places a new point at
`L=100,M=1/10000,P=10000` outside the named complete earlier raw classes.

No nonmembership claim is made for unspecified maximal qualitative
neighborhoods, arbitrary supplied cycles, arbitrary supplied stationary
root certificates, selected favorable child laws, all-proper punishment
roots or semantic source witnesses. The generic periodic and stationary
compilers are deliberately reused. Their ability to consume a newly
produced certificate is not prior production of this raw three-parameter orthant.

The full four-player conjecture and the sixteen-coordinate passive
completion orthant remain open.

### Tracked source correspondence for the comparison

The inspected implemented quotient consumers are
`exists_uniformEquilibriumPayoff_of_responseInvariant_noSingletonBlocks`
and `exists_uniformEquilibriumPayoff_of_responseInvariant_singletonSign`
(`UniformEquilibrium/Quitting/Stationary/ResponseInvariantQuotientStrategic.lean`).
They require the complete response-invariance polynomial identity, an R0
quotient, and quotient degree different from1; they do not require a supplied
stationary root. The own-positive witness satisfies their strategic sign
boundary, so the stationary exclusion is applicable to every partition.
The inspected crossed consumer
`exists_guardedCrossed_stationaryTerminalNash_uniformPayoff`
(`UniformEquilibrium/Quitting/Stationary/GuardedCrossedResponseStrategic.lean`)
requires both complete common-height face guards and produces an exact
stationary behavioral equilibrium with contracting opponents. Its raw
predicates `QuittingCrossedStrictLowerRanking` and
`QuittingCrossedStrictUnitJoining` are defined in
`UniformEquilibrium/Quitting/Stationary/GuardedCrossedResponseRawTests.lean`.

The inspected declaration
`exists_pureStationary_exactTerminalNash_of_componentwiseWeightedPotential`
(`UniformEquilibrium/Quitting/Stationary/ComponentwiseWeightedPotential.lean`)
produces a pure stationary terminal Nash profile, so the pure-support
census rules out every admissible affine coefficient and positive
symmetrizing-weight choice at W. Finally
`exists_uniformEquilibriumPayoff_of_finFour_rawPayoffExclusion`
(`UniformEquilibrium/Quitting/Paths/FinFourRawPayoffExclusionFiniteLaws.lean`)
consumes the strict, nonconcentrated-group or weak-subset finite-calendar
raw exclusion predicates. The explicit all-coordinate finite-word payoff
witness violates the corresponding semantic universal payoff bounds.
These are source-level inspections of existing declarations, not new Lean
checks or newly formalized claims. The concrete comparison with ordinary
mathematical reward producers is supplied by the explicit finite predicates
and calculations above and in the complete program.


## An auxiliary stationary-region comparison

The concrete point `L=100,M=1/10000,P=0,s_i=1` belongs to the stationary
region proved above and is outside the following earlier complete finite raw tests.
This comparison concerns their entire stated choice sets; it does not
exclude the stationary equilibrium produced here from a generic supplied-root
compiler.

First, every stationary equilibrium of this table has full proper support.
In fact the following proper-support exclusion holds for every L,M>=0.
The single-owner, proper-pair, pure, and sure-face arguments in the boundary
census use only singleton or contact data and still apply. For proper
triples013 and123, respectively owner3 and owner1 has two crossing opponents,
zero passive pair reward and pair contact+1. For opponent hazards x,y and
h=(1-x)(1-y), that owner's residual is

    (c1-h/100)x(1-y)+(c2-h/100)y(1-x)+(1-h)xy>0,

where c1,c2 are1/20 and7/10. Thus neither triple can be an active root.
On support012, owner1 has `D_1=-q0+(1/20)q2(1-q0)` and `Q_1>=-q0 q2`.
Consequently `R_1<=-3q0/4+1/20`; an active root forces q0<=1/15.
Owner2 then satisfies

    R_2 >=(1/25)q0+(69/100)q1-(173/100)q0 q1
         >=(1/25)q0+(431/750)q1>0.

On support023 the analogous estimate for owner2 forces q3<=1/15, and
owner0 has the corresponding strictly positive residual. No changed
passive triple belongs to one of these active-owner equations. This proves
the full proper-support exclusion without numerical roots.

The contact-preserving two-high-owner bonus producer must select a crossing
pair, because favorite contacts are negative. At each crossing pair its two
outsider contacts have opposite signs, so there is exactly one positive
maximizer at every positive slope choice. Its prescribed stationary support
therefore has exactly three owners. The three-weak-owner bonus producer also
has exactly three active owners. The preceding exclusion rejects every
selected pair/triple and every slope choice in both producer conclusions.
The sure-base punishment census still fails here, since M<7/20 and

    -27/68+(5/17)(1+M)<0.

The entire polynomial-row-weight/odds-order criterion also fails, with no
restriction on its positive odds or positive polynomial multipliers.
Such transformations fix binary hazard vertices and preserve residual
signs. At `q0=q1=1`, the two choices `(q2,q3)=(1,0),(0,1)` give
`(R0,R1)=(1,-1),(-1,1)`. At `q2=q3=1`, the choices
`(q0,q1)=(1,0),(0,1)` give `(R2,R3)=(-1,1),(1,-1)`.
Every single ordered favorite wall therefore fails at one vertex. If both
favorite pairs are ordered, choosing the outsider vertex admitted by the
other pair's order forces incompatible preferred orientations for the two
walls. The exact program checks all four joint orientations. This excludes
all64 positive multiaffine vertex weights and all positive odds choices,
including constant-row and columnwise predecessors, before Bernstein
sufficient conditions are considered.

Every guarded crossed-response common-height test fails as well. For each
favorite pair i,j there is an outsider k with both
`delta_i({k})>0` and `delta_i({j,k})>0`. Setting q_k=1, the remaining
outsider zero and q_j=h makes R_i a positive convex combination of these
two contacts for every h in(0,1]. It cannot satisfy the required upper
face sign. For any ordered pair, the weak asymmetric unit-face guard fails
at some binary outsider coalition with positive joining contact. The
three-passive-pole producer's eight strict guards fail for all24 role
choices by the finite exact census.

For stationary-response quotients, the derivative identity already
requires, inside every block, positive proportionality of the vectors
`(sum_(j in B)Gamma_ij)_B`, allowing arbitrary positive recipient scaling.
The exact enumeration of all15 set partitions leaves only the all-singleton
and one-block partitions. The former has degree+1, since the inverse is
positive and the determinant positive; the latter is a positive scalar and
also has degree+1. Thus neither has the required quotient degree different
from1. This rejects the complete partition and positive-row-scale choice set.

The existing explicit signed passive-dominance thresholds fail directly.
With `b=min Gamma^-1`, `B=max Gamma^-1`, `kappa=b/(16B)`,
`D=16`, and `R0=1/(1+32 B^2 D/b)`, exact arithmetic gives

    100 < 4BD/(b kappa^2)+1/(b kappa^2),
    4b[100 kappa^2 R0+(1/10000)kappa^3 R0^2] <2.

These failures persist under every positive recipient rescaling, not only
the displayed normalization. Write d_i>0 for the four scale factors.
The inverse matrix becomes `Gamma^-1 diag(1/d_i)`, so its extrema b',B'
satisfy `kappa'=b'/(16B')<=1/16` and
`b'd_i<=c_i=min_k(Gamma^-1)_(ki)`. The contact bound is
`D'=16 max_i d_i`, because every row has a contact of absolute value1.
Consequently the first threshold is at least
`4D'/(kappa')^2>=16384 max_i d_i>100d_0`. For the second, R0'<=1 gives

    4b'W' <=4[100c_0/16^2+(1/10000)c_1/16^3]
           =2583696145481/242755276288000 <2,

where `c_0=3229620/474131399` and `c_1=59380/9676151`.
Relabeling only permutes these quantities. Signed row offsets disappear
when the own singleton is subtracted.

Zeros in the other higher passive coordinates exclude the common negative
relative tube. The old sparse ray is violated by M>0; its old middle tube
fails independently in row1, and the bounded first-parameter interval also
misses L=100. The eight repeated-pair fixed-tube roles fail with the same
3 raw-guard,3 left-sign and2 right-sign census. Crossing transport failures
only become stronger as L increases from20 to100. All singleton, pair-sign,
fixed-family ratio and marked/trap-selector obstructions above are unchanged.
For the universal payoff exclusions, use hazard1/1000 for1000 dates and then
Never. Exact evaluation gives every native stationary value>1/4 and total
survival<(1/5), so the finite original payoff exceeds own in every coordinate.

There is also a representation-independent separation from the positive
participant-jackpot bounded-completion families. Any such completion box
containing this table also contains the stationary-free table at
`L=20,M=1/10000,P=0`. Only recipient0 at coalitions12 and012 changes. Its passive
12 coordinate is never a selected participant jackpot. Reducing L from100
to20 moves this raw coordinate toward the unchanged zero-native passive
coordinates, hence keeps it inside the same bounded completion interval.
If participant012 is selected, its prescribed positive jackpot center is
fixed; its shifted native reward moves upward toward the unchanged row
baseline. The lower residual bound improves and the upper bound holds
because that baseline is itself an unselected passive coordinate in the
box. If it is unselected, it remains between two bounded coordinates.
This argument survives arbitrary positive recipient scales, signed row
baselines and relabelings. The two tables have identical singleton data and
use identical scale, leading coefficients and completion bounds. Uniform
validity of the old producer on its whole box would therefore imply an
exact stationary equilibrium at the excluded L=20 table. The same argument
applies when the common completion radius is the stated scale-thick radius.
All inverse columns here have positive sign, so the signed single-column
producer cannot evade this argument with a negative participant pole.

For the explicit finite-coefficient rule in the signed passive producer
that selects one negative passive pole in every row, its threshold forces
each selected reward to be strictly below `-R`, where R bounds every
unselected nonsingleton reward. Indeed write its scale as t^-1, its degree
as k_i>=2, and its quantities as `m=a_min(ell kappa)^(n-1)` and C_E.
The selected residual coefficient contributes a monomial of absolute
coefficient1 to E, so `C_E>=max(1,R)u^(k_i)`, while m<=a_i and u>=2.
Its condition `t<m/(2C_E)` and t<=1 yields
`a_i t^(-(k_i-1))>2R`; adding a residual of absolute value<=R gives the
claimed strict bound. At the present table all higher passives in row2
(and also row3) equal the same own baseline. Whatever coalition is selected,
an unselected passive coordinate with exactly that same value remains and
already has absolute value<=R. This contradicts the required strict bound.
This last comparison concerns the supplied explicit threshold formula; it
does not identify the smallest possible threshold of an eventual theorem.

The point therefore supplies a direct comparison inside the new stationary
region against the named complete raw tests. Arbitrary supplied stationary
certificates, unspecified maximal continuation neighborhoods, and uncomputed
optimal thresholds of eventual families remain unclassified. No claim that
stationarity itself fails at this tail point is made.


## Exact overlap and the remaining family region

The new conclusion is complete closure of the specified three-parameter
family. Several conspicuous features of its statement were already available:
full sixty-coordinate neighborhoods, unbounded raw classes, and stationary
constructions with a positive singleton inverse. They are not separate
counterexample exclusions here.

There is substantial exact overlap. For L<=50, the two periodic menus used
above already supply the strategies after changing M and P: the full endpoint
menus never inspect either changed passive triple or its participant grand
companion. This is an immediate completion freedom of the earlier periodic
strategies, including arbitrarily large M and P.

A second overlap has a sharp boundary. For every L,M,P>=0 and arbitrary signed
own levels, an exact Nash root against the actual punishment vector with a
sure quitter exists if and only if M>=27/20. Here is a complete adapter to
`quittingPunishmentSureRootTarget_isUniformEquilibriumPayoff_and_floor`
(`UniformEquilibrium/Quitting/Classification/InstantPunishmentSureQuitterPayoff.lean`).
The contact census leaves only the following possible roots with a sure
quitter:

    q=(7/17,1,1/2,0),       q=(1/2,0,1,7/17).

The first has sure owner1; the second has sure owner2. In either case the
sure owner's expected joining contact is -27/68 and opponent survival is
5/17. Thus the sure-owner endpoint inequality against continuation chi_i is
exactly

    -27/68+(5/17)(s_i-chi_i)>=0,
    equivalently chi_i<=s_i-27/20.                    (O1)

The contact census also rejects every other sure support: the two proper
owners on a three-owner support force the displayed hazards, four-owner
sure faces containing proper players contradict the weighted contact identity, and pure and smaller
supports have a wrong-sign joining contact. This enumeration is independent
of L,M,P and of the own levels.

For completeness, a finite-table patient-response floor handles arbitrary
signed own levels without translating Never. If all passive native rewards
of owner i are at least -a and |delta_i|<=1, give that owner an independent
geometric first-Quit clock G with hazard epsilon. Against the opponents'
first-Quit clock T, Pr(G=T<infinity)<=epsilon. On G<T the owner receives s_i;
on T<G it receives at least s_i-a; on a simultaneous stop it receives at
least s_i-a-1. The clock G is finite almost surely, so there is no Never
term. This complete strategy guarantees at least s_i-a-epsilon uniformly
against all opponent laws. Taking epsilon to zero gives chi_i>=s_i-a.
Here a=max(M,69/100) for owner1 and a=69/100 for owner2. Consequently (O1)
is impossible for either candidate when M<27/20, and it is always impossible
for the second candidate. When M>=27/20, opponents023 quitting surely cap
owner1's best reply by s_1-M: Continue receives s_1-M and Quit receives
s_1-M-1. Hence chi_1<=s_1-M and the first root satisfies (O1). Its two proper
owners are indifferent and its inactive owner's contact is -19/68. The named
consumer therefore gives a uniform-equilibrium payoff for the entire region
M>=27/20. No symmetry between M and P is being assumed.

The earlier signed passive-dominance tests also cover the sufficiently large
ends. In the literal normalization put

    b=min Gamma^(-1), B=max Gamma^(-1), kappa=b/(16B),
    R0=1/(1+512 B^2/b),
    Cpair=4B*16/(b kappa^2)+1/(b kappa^2).

They apply whenever either

    L>=Cpair,
    4b[L kappa^2 R0+(M+P)kappa^3 R0^2]>=2.             (O2)

The pair threshold is exactly

    Cpair=28828074185243664003809280/2170791610991641,

approximately 1.328*10^10. The all-degrees test covers P alone above
2/(4b kappa^3 R0^2), approximately 1.673*10^20. These tests apply to the
entire compatible sixteen-coordinate passive orthant, a broader family than
ours, although with these large sufficient thresholds.

Relative to these earlier mechanisms, any remaining point of the present
family must satisfy

    50<L<Cpair, 0<=M<27/20,
    4b[L kappa^2 R0+(M+P)kappa^3 R0^2]<2.             (O3)

Thus the substantive addition is closure of a bounded region of intermediate
parameter values, with a complete compatible construction across its boundaries.
It is not a new assertion that sufficiently large nonpositive passive
rewards can yield equilibrium.

## A nonlocal point in the added stationary region

Take the complete raw table defined above at

    L=100, M=1/10000, P=10000, s_i=1.                 (V*)

The point belongs to the newly certified stationary region. It lies outside
the preceding periodic, sure-punishment and dominance regions. It is also far
from the old sparse ray in the stationary compactification:

    alpha=2L/[L+sqrt(L^2+4(M+P))]<(sqrt(5)-1)/2.

The old sparse ray has alpha=1. The separation is therefore not merely a
large raw perturbation whose normalized size tends to zero.

Here are the full-choice comparisons needed at this point. The proper-support
exclusion above holds for all P: on a three-owner support every active owner
faces at most two opponents, so a passive triple never enters its equation.
The complete sure-root exclusion follows from (O1). Accordingly the
contact-preserving two-high-owner and three-weak-owner bonus producers, whose
contact choices here force exactly three active owners, cannot produce this
table. The quotient tests, positive polynomial row weights and all hazard
orders, common-height crossed guards, and all24 three-passive-pole role guards
remain excluded by the same singleton and contact calculations. In particular
both changed triple penalties cancel from every difference used in those
role guards. The proper-child counterexamples use only singleton and pair
absorptions, so all14 child and all weight choices remain excluded.

For the two dominance tests the exclusion holds under every positive recipient
rescaling, not merely the displayed normalization. If the four scales are
d_i>0, the inverse becomes Gamma^(-1)diag(1/d_i). Its extrema b',B' obey
kappa'=b'/(16B')<=1/16 and b'd_i<=c_i, where

    c0=3229620/474131399,
    c1=59380/9676151,
    c3=2589620/474131399.

The contact constant is D'=16 max_i d_i. The pair threshold is therefore at
least16384 max_i d_i>100d_0, while the all-degrees left side satisfies

    4b'W'<=4[100c0/16^2+(c1/10000+10000c3)/16^3]
           =2218828020783/34679325184000<2.          (V1)

Relabeling only permutes the quantities, and signed row offsets disappear
from native comparisons.

The literal earlier periodic raw classes also miss (V*). The positive
participant-pair premiums, singleton ratios69/4, and favorite J/Gamma ratios
are unchanged, so their entire role and positive-scale exclusions apply.
For the old sparse tube, the singleton and participant-pair coordinates
force the identity role and a row0 scale whose reciprocal differs from1 by at most10^(-8). Its row0
passive12 comparison then cannot be within radius10^(-8) of any L<=50.
Every coordinate used in this separation belongs to the complete endpoint
menus, so freeing unused completion entries cannot repair it. The prior
isolated three-phase cube and the four-coordinate free cylinder likewise
fail their complete role/scale tests. The fixed crossing transport guards
fail at L=100 independently of M,P. Zero higher passives in row2 exclude both
the common strictly negative relative tube and the explicit finite threshold
of the producer requiring a negative passive pole in every row.

A representation-independent obstruction excludes all positive participant
jackpot bounded-completion families, including their scale-thick variants.
Any such completion box containing (V*) also contains the stationary-free
control table

    W: L=20, M=1/10000, P=0, s_i=1,

whose complete stationary gap was proved above. Move precisely row0 at12,012
and row3 at012,0123 upward to the W values. The passive entries can never be
selected participant poles. Each moves toward an unchanged zero-native
passive entry of its row, and hence stays in the same bounded completion
interval. If one of the changed participant entries is selected, its prescribed
positive pole center is fixed. Moving upward improves its lower residual
bound; its upper residual remains bounded because the new entry is at most
the unchanged row baseline, which is itself an unselected bounded passive
coordinate. If it is unselected, it stays between already bounded entries.
This reasoning survives all positive recipient scales, signed row baselines,
coalition choices and relabelings. The singleton data, pole scales, coefficients
and completion bounds are unchanged. Uniform correctness of the earlier
producer on that entire box would imply a stationary equilibrium at W,
contradicting its proved gap. All inverse columns here are positive, so a
negative signed participant pole is not an alternative selection.

Finally, the universal payoff-exclusion predicates remain false. Use common
hazard1/1000 for1000 dates and then Never. Its infinite-horizon native
stationary values are

    (4669243079/15976015996,
     45304275353/79880079980,
     13052851079/15976015996,
     17004863071/15976015996).

Each exceeds1/4 and the finite word has survival (999/1000)^4000<1/5.
Consequently its actual finite-word original payoff exceeds the own-one
vector in every coordinate. This defeats every nonzero nonnegative social
weight and every subset selector in the universal upper-payoff predicates.

These comparisons identify a concrete added raw-table region. They do not
exclude unspecified maximal qualitative neighborhoods, arbitrary supplied
stationary or periodic certificates, or unproduced all-proper punishment
continuations. Such supplied-object consumers are used by the new proof;
the new content is production throughout the stated bounded region of
intermediate parameter values. The general four-player conjecture and arbitrary sixteen-
coordinate passive completions remain open.

### An unbounded positive triple beyond both explicit dominance tests

The weighted tube also permits a passive coefficient of the opposite sign
from the two base triple penalties. Put eta=10^(-1000), M=P=0 and t=1/L.
Add eta L^2 to both row2 rewards at coalitions013 and0123, leaving every
other coordinate unchanged. This preserves every joining contact and
satisfies the weighted raw error bound exactly. The weighted theorem
therefore supplies an exact stationary equilibrium and fixed uniform target
for every L>=40, despite the unbounded positive passive triple F_2(013).

For L>=eta^(-1), both explicit signed passive-dominance mass tests fail
even after arbitrary positive recipient rescaling and relabeling. To see
this, let d_i>0 be the scales. The inverse singleton matrix becomes
A'=Gamma^(-1)diag(1/d_i), whose positive columns force every sign choice
to be positive. Write b'=min A', B'=max A', q=b'/B', r=d_0/d_2, and

    k=min_j(Gamma^(-1))_(j0)/max_j(Gamma^(-1))_(j2)
      =53827/1990800<1.

Then q<=1 and rq<=k, so rq^m<=k for every integer m>=1. The only
compatible higher coefficient is the pair Ld_0, whereas the incompatible
mass is eta L^2 d_2. Hence D'>=eta L^2d_2 and kappa'=q/16. The pair
threshold obeys

    [4B'D'/(b'kappa'^2)+1/(b'kappa'^2)]/(Ld_0)
       >=1024 eta L/(rq^3)>=1024 eta L/k>1.

For the all-degrees test,
R0'=1/(1+32B'^2D'/b')<=b'/(32B'^2D'), and consequently

    4b'W'=4b'Ld_0 kappa'^2R0'
         <=rq^4/(2048 eta L)<=k/(2048 eta L)<2.

Thus neither finite raw inequality can apply anywhere on this ray with
L>=eta^(-1). These comparisons concern the complete stated sign, scale
and relabeling choices of those two explicit tests. They do not assert
failure of arbitrary stationary certificates, other producers, or an
unspecified optimal threshold of a qualitative eventual theorem.


## Lean handoff and reproduction

A formalization can separate the two periodic contraction covers, their
complete-menu invariance under `M,P`, the literal stationary reward-to-polynomial
identity (2), the whole-prism compact root lemma, and the behavioral
consumers. Every finite cover consists of exact rational inequalities. The full reward-tube
corollary additionally uses the generalized four-pair elimination, the
uniform coefficient perturbation bounds, and the explicit integer-slack
argument proved above.
The raw-table theorem quantifies over finite real `L,M,P>=0` and arbitrary
real row offsets. Its conclusion is existence of the constructed periodic
profile and one fixed uniform-equilibrium payoff; it must not assume the
root or the Nash profile as an input field.

Appendices A and B give the complete programs for the periodic branches.
Appendix C reconstructs the three-parameter field and verifies every cell in
the compact prism using exact integers. It also checks the complete-menu
invisibility used above. Save each block as its own Python file and run it
normally. Appendices A, B, and D use Python and SymPy; Appendix C additionally
uses NumPy and SciPy only to propose rational data. Failure or an incomplete
run supplies no certificate.

## Appendix A. Four-pair left interval

```python
"""Exact stronger four-pair margins for a full-sixty raw reward tube.

All certificate decisions use Fraction arithmetic. Rational Newton updates
only construct candidates; each parameter cell is checked independently.
"""
from fractions import Fraction as Q
from itertools import combinations
from math import prod
import sympy as s

I=range(4)
x=s.symbols('x0:4');L=s.symbols('L');vars=x+(L,)
A=s.Matrix([[0,1,-s.Rational(7,10),-s.Rational(1,20)],
 [1,0,-s.Rational(1,20),-s.Rational(7,10)],
 [-s.Rational(1,20),-s.Rational(7,10),0,1],
 [-s.Rational(7,10),-s.Rational(1,20),1,0]])
J=(s.ones(4)-s.eye(4))/100
for i in I:J[i,i^1]=i+1
Gamma=A+J
contacts={}
for T,sign in zip(combinations(I,2),[-1,-1,1,1,-1,-1]):
 lo,hi=[i for i in I if i not in T]
 contacts[lo,T]=sign;contacts[hi,T]=-sign

def passive(i,T):
 if not T:return s.Integer(0)
 if len(T)==1:return Gamma[i,T[0]]
 return -L if i==0 and T==(1,2) else s.Integer(0)

def contact(i,T):
 if not T:return s.Integer(0)
 if len(T)==1:return -A[i,T[0]]
 if len(T)==2:return s.Integer(contacts[i,T])
 return s.Integer(-1)

table={}
for mask in range(1,16):
 S=frozenset(i for i in I if mask>>i&1)
 for i in I:
  T=tuple(sorted(S-{i}))
  table[i,S]=passive(i,T)+(contact(i,T) if i in S else 0)
assert len(table)==60

# Prefix order is the reverse of physical chronology03,02,12,13.
w=(1,2,0,3);v=(3,1,2,0)
pairs=[tuple(sorted((w[k],v[k]))) for k in I]
y=[x[(k-1)%4]/(5+x[(k-1)%4]) for k in I]
C=[(1-x[k])*(1-y[k]) for k in I]
a=[y[(k+1)%4]/100 for k in I]
e=[];b=[]
for k in I:
 t=(k+2)%4
 e.append((w[k]+2)*y[t]*(1-x[t])-s.Rational(1,25)*x[t]*(1-y[t])
          +passive(w[k],pairs[t])*x[t]*y[t]+C[t]*a[k])
for k in I:
 t=(k+3)%4
 b.append(-s.Rational(69,100)*y[t]*(1-x[t])+(w[k]+2)*x[t]*(1-y[t])
          +passive(w[k],pairs[t])*x[t]*y[t]+C[t]*e[k])
raw=[(1-x[k])*b[k]-s.Rational(7,10)*x[k] for k in I]
gaps=[y[k]-x[k]*(1-y[k])/20+C[k]*a[(k+2)%4] for k in I]
gaps += [-s.Rational(7,10)*y[k]*(1-x[k])+x[k]-2*x[k]*y[k]
         +C[k]*e[(k+1)%4] for k in I]

# Literal inactive Continue-minus-Quit identities.
for k in I:
 hazards={w[k]:y[k],v[k]:x[k]}
 for owner,continuation,expected in (
  (w[(k+2)%4],a[(k+2)%4],gaps[k]),
  (w[(k+1)%4],e[(k+1)%4],gaps[4+k])):
  Delta=0
  for size in range(3):
   for T in combinations(pairs[k],size):
    probability=s.prod(hazards[j] if j in T else 1-hazards[j] for j in pairs[k])
    Delta+=probability*contact(owner,T)
  assert s.cancel(expected+Delta-C[k]*continuation)==0

# All sixteen literal policy recursions and eight active endpoint identities.
caps={}
for j in I:
 for shift,value in enumerate((x[j]/100,a[j],e[j],b[j])):
  caps[w[j],(j+shift)%4]=value
for k in I:
 hazards={i:(y[k] if i==w[k] else x[k] if i==v[k] else 0) for i in I}
 for i in I:
  others=[j for j in I if j!=i]
  P=Quit=0
  for size in range(4):
   for T in combinations(others,size):
    S=frozenset(T)
    probability=s.prod(hazards[j] if j in S else 1-hazards[j] for j in others)
    P+=probability*(table[i,S] if S else 0)
    Quit+=probability*table[i,S|{i}]
  h=s.prod(1-hazards[j] for j in others)
  gap=Quit-P-h*caps[i,(k-1)%4]
  qi=hazards[i]
  residual=caps[i,k]-qi*Quit-(1-qi)*P-C[k]*caps[i,(k-1)%4]
  if i==w[k]:
   assert s.cancel(gap+raw[k])==0
   assert s.cancel(residual+(1-y[k])*raw[k])==0
  elif i==v[k]:
   assert s.cancel(gap)==0 and s.cancel(residual)==0
  else:
   expected=gaps[k] if i==w[(k+2)%4] else gaps[4+k]
   assert s.cancel(gap+expected)==0 and s.cancel(residual)==0

scale=100*s.prod(5+z for z in x)
fields=[s.Poly(s.cancel(scale*f),*vars).as_expr() for f in raw]
positive=[s.Poly(s.cancel(scale*f),*vars).as_expr() for f in gaps]

def frac(value):
 value=s.Rational(value);return Q(int(value.p),int(value.q))
def terms(value):return [(alpha,frac(c)) for alpha,c in s.Poly(value,*vars).terms()]
F=list(map(terms,fields));G=list(map(terms,positive))
DF=[[terms(s.diff(f,z)) for z in x] for f in fields]
FL=[terms(s.diff(f,L)) for f in fields]
assert all(s.diff(f,L,2)==0 for f in fields)

def evaluate(poly,point):
 return sum(c*prod(point[j]**k for j,k in enumerate(alpha)) for alpha,c in poly)
def interval(poly,box):
 lo=hi=Q(0)
 for alpha,c in poly:
  aa=prod(box[j][0]**k for j,k in enumerate(alpha))
  bb=prod(box[j][1]**k for j,k in enumerate(alpha))
  lo+=c*(aa if c>=0 else bb);hi+=c*(bb if c>=0 else aa)
 return lo,hi
def invert(matrix):
 out=[list(row)+[Q(i==j) for j in I] for i,row in enumerate(matrix)]
 for j in I:
  pivot=next(i for i in range(j,4) if out[i][j])
  out[j],out[pivot]=out[pivot],out[j]
  div=out[j][j];out[j]=[z/div for z in out[j]]
  for i in I:
   if i!=j:
    div=out[i][j];out[i]=[a-div*b for a,b in zip(out[i],out[j])]
 return [row[4:] for row in out]
def rounded(value,den=10**15):return Q((value*den+Q(1,2)).numerator//(value*den+Q(1,2)).denominator,den)
def matvec(M,v):return [sum(a*b for a,b in zip(row,v)) for row in M]

if __name__=='__main__':
 count=256
 radius=Q(1,400)
 center=list(map(Q,['.753','.787','.66','.8']))
 max_lip=max_image=Q(0);min_gap=None
 for cell in range(count):
  lo=Q(10*cell,count);hi=Q(10*(cell+1),count);mid=(lo+hi)/2
  # Exact bounded candidate generation, not an existence assumption.
  M=invert([[evaluate(poly,center+[mid]) for poly in row] for row in DF])
  M=[[rounded(a) for a in row] for row in M]
  for _ in range(6):
   correction=matvec(M,[evaluate(poly,center+[mid]) for poly in F])
   center=[rounded(a-b) for a,b in zip(center,correction)]
  M=invert([[evaluate(poly,center+[mid]) for poly in row] for row in DF])
  M=[[rounded(a) for a in row] for row in M]
  box=[(c-radius,c+radius) for c in center]+[(lo,hi)]
  assert all(Q(1,4)<a<b<Q(9,10) for a,b in box[:4]),(cell,'proper')
  bounds=[[interval(poly,box) for poly in row] for row in DF]
  lip=Q(0)
  for i in I:
   total=Q(0)
   for j in I:
    lower=upper=Q(i==j)
    for k in I:
     coeff=-M[i][k];aa,bb=bounds[k][j]
     lower+=coeff*(aa if coeff>=0 else bb)
     upper+=coeff*(bb if coeff>=0 else aa)
    total+=max(abs(lower),abs(upper))
   lip=max(lip,total)
  assert lip<Q(1,10),(cell,'contraction',float(lip))
  assert max(sum(abs(z) for z in row) for row in M)<1
  residual=matvec(M,[evaluate(poly,center+[mid]) for poly in F])
  slope=matvec(M,[evaluate(poly,center+[mid]) for poly in FL])
  defect=max(abs(a)+abs(b)*(hi-lo)/2 for a,b in zip(residual,slope))
  image=defect/radius+lip
  assert image<Q(3,5),(cell,'self-map',float(image))
  gap=min(interval(poly,box)[0] for poly in G)
  assert gap>1,(cell,'inactive',float(gap))
  max_lip=max(max_lip,lip);max_image=max(max_image,image)
  min_gap=gap if min_gap is None else min(min_gap,gap)
  if (cell+1)%64==0:print('PASS cells',cell+1,'of',count,flush=True)
 print('PASS: entire closed parameter interval 0<=L<=10,',count,'exact cells.')
 print('PASS: all active strong hazards>1/4; weak hazards>1/21; eight inactive gaps positive.')
 print('Diagnostic rounded bounds only:',float(max_lip),float(max_image),float(min_gap))

if __name__ == '__main__':
 # Conservative analytic perturbation constants, all exact rationals.
 eps=Q(1,10**12)
 dmin=Q(49,1000); cmax=Q(11,1000)
 assert Q(9,10)/dmin<19
 assert Q(9,10)*cmax/dmin**2<5
 assert 1/dmin<21 and cmax/dmin**2<5
 assert 2*19+4*5<60 and 2*21+4*5<64
 assert 2000+64*11+1500+60*42+2200<10000
 assert 130000*15000+22000*5000<3000000000
 assert Q(3,5)+272000000000*eps<1
 assert Q(1,10)+12000000000*eps<1
 assert 400000000*eps<1
 assert (Q(1,4)*Q(9,1000))/(Q(51,1000)+Q(9,10)*Q(11,1000))>Q(1,30)
 assert 215*4*8600+2*8600==7413200
 assert 72+Q(36,40)*34400+215*144==61992
 assert 61992*160==9918720
 # These constants supplement, and do not replace, a complete stationary
 # run with C<=10^10 and Jacobian degree at most 10. Accepted derivative
 # rows need only have weighted norm <1, not the stronger margin <1/2.
 N=2**40; K=10**10; Cmax=10**10; denominator=Cmax*N**10
 assert 1+25*N<200*N
 assert 800+64000+12800000+2476800<K
 assert 160*(Q(36,40)*8600+215*36)==2476800
 assert 4800*N*K**3*denominator**4<10**577
 assert Q(1,200*Cmax*N**13)>Q(1,10**174)
 assert Q(1,400*Cmax*N**15)>Q(1,10**208)
 for exponent in (14,16):
  assert (2*Cmax*N**exponent)%(Cmax*N**12)==0
  assert Q(1,400*Cmax*N**(exponent+1))>Q(1,10**234)
 assert 200*N*10**577*4*10**7<10**600
 assert N*10**577*7500000<10**597
 assert Q(10**601,10**1000)<Q(1,10**234)
 print('PASS: full-sixty perturbation constants and stationary integer-slack bounds')
 # Weighted tail: raw degree-k errors may grow by t^(-(k-1)).
 # These are pointwise state-C1 bounds at the actual positive t.
 weighted_sum=3*200+3*200**2+200**3
 assert weighted_sum==8120600
 assert 862*weighted_sum==6999957200<7*10**9
 weighted_derivative=2*201**2+Q(36,40)*4*weighted_sum+215*4*201**2
 assert weighted_derivative==64059822
 assert 160*weighted_derivative==10249571520<11*10**9
 assert 200*N*10**577*4*(11*10**9)<10**603
 assert N*10**577*(7*10**9)<10**600
 assert Q(10**604,10**1000)<Q(1,10**234)
 print('PASS: unbounded weighted full-sixty tail perturbation constants')
```

## Appendix B. Three-phase middle interval and full reward tube

```python
"""Exact finite-cell certificate for the middle sparse passive ray.

The raw class has F_0(12)=-L, all other higher passives zero, and 8<=L<=50.
The independent raw-reward perturbation radius is1/100000000.
The word is12,123,013. All candidate generation and all acceptance decisions
use rational/integer arithmetic. The finite decimal seed is only candidate
data; posterior complete-cell bounds provide every existence assertion.
"""
from fractions import Fraction as Fr
from itertools import combinations
import sympy as s

Q = s.Rational
I = range(4)
phases = [(1, 2), (1, 2, 3), (0, 1, 3)]
x = s.symbols('x0:8')
L = s.symbols('L')
hazards = {}
at = 0
for k, support in enumerate(phases):
    for i in support:
        hazards[k, i] = x[at]
        at += 1
A = s.Matrix([[0, 1, -Q(7, 10), -Q(1, 20)],
              [1, 0, -Q(1, 20), -Q(7, 10)],
              [-Q(1, 20), -Q(7, 10), 0, 1],
              [-Q(7, 10), -Q(1, 20), 1, 0]])
J = (s.ones(4)-s.eye(4))/100
for i in I:
    J[i, i ^ 1] = i+1
Gamma = A+J
contacts = {}
for B, sign in zip(combinations(I, 2), (-1, -1, 1, 1, -1, -1)):
    lo, hi = [i for i in I if i not in B]
    contacts[lo, B] = sign
    contacts[hi, B] = -sign
Z = {}
for mask in range(1, 16):
    coalition = frozenset(i for i in I if mask >> i & 1)
    for i in I:
        B = tuple(sorted(coalition-{i}))
        passive = (0 if not B else Gamma[i, B[0]] if len(B) == 1
                   else -L if i == 0 and B == (1, 2) else 0)
        contact = (0 if not B else -A[i, B[0]] if len(B) == 1
                   else contacts[i, B] if len(B) == 2 else -1)
        Z[i, coalition] = passive+(contact if i in coalition else 0)
assert len(Z) == 60
printed_table = [
    ((0,), (1, 4, Q(24, 25), Q(31, 100))),
    ((1,), (3, 1, Q(31, 100), Q(24, 25))),
    ((2,), (Q(31, 100), Q(24, 25), 1, 6)),
    ((3,), (Q(24, 25), Q(31, 100), 5, 1)),
    ((0, 1), (2, 3, 1, 1)),
    ((0, 2), (Q(101, 100), 1, Q(101, 100), 1)),
    ((0, 3), (Q(101, 100), 1, 1, Q(101, 100))),
    ((1, 2), (1-L, Q(101, 100), Q(101, 100), 1)),
    ((1, 3), (1, Q(101, 100), 1, Q(101, 100))),
    ((2, 3), (1, 1, 4, 5)),
    ((0, 1, 2), (2-L, 0, 0, 1)),
    ((0, 1, 3), (0, 2, 1, 2)),
    ((0, 2, 3), (0, 1, 0, 2)),
    ((1, 2, 3), (1, 2, 2, 0)),
    ((0, 1, 2, 3), (0, 0, 0, 0))]
assert all(s.expand(Z[i, frozenset(B)]+1-row[i]) == 0
           for B, row in printed_table for i in I)
P, Quit, h = {}, {}, {}
used = set()
for k, support in enumerate(phases):
    for i in I:
        opponents = tuple(j for j in support if j != i)
        P[k, i] = Quit[k, i] = 0
        for count in range(len(opponents)+1):
            for B in combinations(opponents, count):
                B = frozenset(B)
                mass = s.prod(hazards[k, j] if j in B else 1-hazards[k, j]
                              for j in opponents)
                if B:
                    P[k, i] += mass*Z[i, B]
                    used.add((i, B))
                Quit[k, i] += mass*Z[i, B | {i}]
                used.add((i, B | {i}))
        P[k, i] = s.expand(P[k, i])
        Quit[k, i] = s.expand(Quit[k, i])
        h[k, i] = s.prod(1-hazards[k, j] for j in opponents)
unused = set(Z)-used
assert unused == {(i, frozenset(B)) for i in (1, 3)
                  for B in ((0, 2), (0, 1, 2), (0, 2, 3), (0, 1, 2, 3))}

# Start at each owner's next active phase, including both inactive phases of0.
V = {(k, i): Quit[k, i] for k, support in enumerate(phases) for i in support}
for _ in range(3):
    for k in range(3):
        for i in I:
            if (k, i) not in V and ((k+1)%3, i) in V:
                V[k, i] = s.expand(P[k, i]+h[k, i]*V[(k+1)%3, i])
assert len(V) == 12
F, G, slots = [], [], []
for k, support in enumerate(phases):
    for i in I:
        gap = s.expand(Quit[k, i]-P[k, i]-h[k, i]*V[(k+1)%3, i])
        if i in support:
            F.append(gap)
            slots.append((k, i))
        else:
            G.append(gap)
assert slots == [(0, 1), (0, 2), (1, 1), (1, 2), (1, 3), (2, 0), (2, 1), (2, 3)]
F = s.Matrix(F)
Jac = F.jacobian(x)
assert [s.Poly(z, *x, L).total_degree() for z in F] == [3, 3, 4, 6, 4, 9, 3, 6]
assert [len(s.Poly(z, *x, L).terms()) for z in F] == [7, 7, 15, 63, 15, 323, 7, 63]
assert all(s.diff(z, L, 2) == 0 for z in F)

# A Continue endpoint follows the prescribed opponents until this owner's
# next active phase, then forces Quit. Each Bernoulli hazard is encountered
# at most twice, including the two occurrences of the initial phase for0.
for k in range(3):
    for i in I:
        distance = next(d for d in range(1, 4) if i in phases[(k+d)%3])
        occurrences = []
        for d in range(distance+1):
            phase = (k+d)%3
            occurrences.extend((phase, j) for j in phases[phase] if j != i)
        assert max((occurrences.count(slot) for slot in hazards), default=0) <= 2
        assert len(set((k, j) for j in phases[k] if j != i)) <= 3

# Exact policy recursions, as polynomial identities at every finite L.
alpha = [s.prod(1-hazards[k, i] for i in support) for k, support in enumerate(phases)]
stage, policy = {}, {}
at = 0
for k, support in enumerate(phases):
    for i in I:
        qi = hazards.get((k, i), 0)
        stage[k, i] = qi*Quit[k, i]+(1-qi)*P[k, i]
        policy[k, i] = V[k, i]-stage[k, i]-alpha[k]*V[(k+1)%3, i]
        if i in support:
            assert s.expand(policy[k, i]-(1-qi)*F[at]) == 0
            at += 1
        else:
            assert s.expand(policy[k, i]) == 0
Dcycle = 1-s.prod(alpha)
for k in range(3):
    for i in I:
        num = (stage[k, i]+alpha[k]*stage[(k+1)%3, i]
               +alpha[k]*alpha[(k+1)%3]*stage[(k+2)%3, i])
        rem = (policy[k, i]+alpha[k]*policy[(k+1)%3, i]
               +alpha[k]*alpha[(k+1)%3]*policy[(k+2)%3, i])
        assert s.expand(Dcycle*V[k, i]-num-rem) == 0

# All state endpoints have common denominator GRID. Every raw polynomial
# coefficient has denominator dividing100. Homogenization to a common total
# degree lets polynomial evaluation and interval enclosure use only integers.
GRID = 10**18
MDEN = 10**15

def compile_poly(expr, degree):
    out = []
    for powers, coefficient in s.Poly(expr, *x, L).terms():
        scaled = coefficient*100
        assert scaled.q == 1 and sum(powers) <= degree
        if scaled:
            out.append((int(scaled)*GRID**(degree-sum(powers)),
                        tuple((j, n) for j, n in enumerate(powers) if n)))
    return out

fpolys = [compile_poly(z, 9) for z in F]
jpolys = [[compile_poly(Jac[i, j], 8) for j in range(8)] for i in range(8)]
lpolys = [compile_poly(s.diff(z, L), 9) for z in F]
gpolys = [compile_poly(z, 7) for z in G]
FDEN, JDEN, GDEN = 100*GRID**9, 100*GRID**8, 100*GRID**7

def power_table(point):
    return [(1, z, z*z) for z in point]

def evaluate(poly, powers):
    total = 0
    for coefficient, monomial in poly:
        term = coefficient
        for j, n in monomial:
            term *= powers[j][n]
        total += term
    return total

def interval(poly, lower_powers, upper_powers):
    lower = upper = 0
    for coefficient, monomial in poly:
        a = b = coefficient
        for j, n in monomial:
            a *= (lower_powers if coefficient >= 0 else upper_powers)[j][n]
            b *= (upper_powers if coefficient >= 0 else lower_powers)[j][n]
        lower += a
        upper += b
    return lower, upper

def nearest_integer(numerator, denominator):
    return (2*numerator+denominator)//(2*denominator)

def inverse(matrix):
    a = [[Fr(z) for z in row]+[Fr(i == j) for j in range(8)]
         for i, row in enumerate(matrix)]
    for j in range(8):
        pivot = next(i for i in range(j, 8) if a[i][j])
        a[j], a[pivot] = a[pivot], a[j]
        divisor = a[j][j]
        a[j] = [z/divisor for z in a[j]]
        for i in range(8):
            if i != j:
                multiplier = a[i][j]
                a[i] = [z-multiplier*w for z, w in zip(a[i], a[j])]
    return [row[8:] for row in a]

def preconditioner(center, parameter):
    powers = power_table(center+[parameter])
    jac = [[Fr(evaluate(poly, powers), JDEN) for poly in row] for row in jpolys]
    inv = inverse(jac)
    return [[nearest_integer(z.numerator*MDEN, z.denominator) for z in row] for row in inv]

def multiply(matrix, vector):
    return [sum(a*b for a, b in zip(row, vector)) for row in matrix]

seed = ['.5643795381862795', '.19016981154675858', '.505782937996143',
        '.015790579292830696', '.4547022016511442', '.3514733480515821',
        '.04286172661525797', '.3045435045232077']
center = [int(Fr(z)*GRID) for z in seed]
cells = []
for start, step, count in [(Fr(8), Fr(1, 20), 40),
                           (Fr(10), Fr(1, 10), 50),
                           (Fr(15), Fr(1, 5), 50),
                           (Fr(25), Fr(1, 2), 50)]:
    cells.extend((start+j*step, start+(j+1)*step) for j in range(count))
assert cells[0][0] == 8 and cells[-1][1] == 50
assert all(cells[j][1] == cells[j+1][0] for j in range(len(cells)-1))
DELTA = Fr(1, 10**8)
worst_lip = worst_defect = worst_image = Fr(0)
worst_perturb_lip = worst_perturb_defect = Fr(0)
largest_gap = -Fr(100)
smallest_hazard = Fr(1)

for cell_index, (left, right) in enumerate(cells):
    middle, halfwidth = (left+right)/2, (right-left)/2
    parameter = int(middle*GRID)
    mm = preconditioner(center, parameter)
    for _ in range(16 if cell_index == 0 else 8):
        powers = power_table(center+[parameter])
        step = multiply(mm, [evaluate(poly, powers) for poly in fpolys])
        center = [nearest_integer(z*MDEN*FDEN-GRID*t, MDEN*FDEN)
                  for z, t in zip(center, step)]
    mm = preconditioner(center, parameter)
    powers = power_table(center+[parameter])
    slope = multiply(mm, [evaluate(poly, powers) for poly in lpolys])
    radii = []
    for z in slope:
        raw = 2*abs(Fr(z, MDEN*FDEN))*halfwidth+Fr(1, 10**7)
        scaled = raw*10**12
        rounded_up = -((-scaled.numerator)//scaled.denominator)
        radii.append(rounded_up*(GRID//10**12))
    low = [a-r for a, r in zip(center, radii)]+[int(left*GRID)]
    high = [a+r for a, r in zip(center, radii)]+[int(right*GRID)]
    assert all(GRID//500 < a < b < 3*GRID//5 for a, b in zip(low[:8], high[:8]))
    smallest_hazard = min(smallest_hazard, *(Fr(a, GRID) for a in low[:8]))
    cursor = 0
    for support in phases:
        assert sum(a > GRID//20 for a in low[cursor:cursor+len(support)]) >= 2
        cursor += len(support)
    lowpowers, highpowers = power_table(low), power_table(high)
    jb = [[interval(poly, lowpowers, highpowers) for poly in row] for row in jpolys]
    denominator = MDEN*JDEN
    lip = Fr(0)
    for i in range(8):
        row_sum = 0
        for j in range(8):
            lo = hi = denominator*int(i == j)
            for k in range(8):
                c = -mm[i][k]
                a, b = jb[k][j]
                lo += c*(a if c >= 0 else b)
                hi += c*(b if c >= 0 else a)
            row_sum += max(abs(lo), abs(hi))*radii[j]
        lip = max(lip, Fr(row_sum, denominator*radii[i]))
    defect = Fr(0)
    for endpoint in (left, right):
        pp = power_table(center+[int(endpoint*GRID)])
        residual = multiply(mm, [evaluate(poly, pp) for poly in fpolys])
        defect = max(defect, *(Fr(abs(z)*GRID, MDEN*FDEN*r)
                               for z, r in zip(residual, radii)))
    # A next-active cap is a convex average of terminal rewards. Hence
    # each reward-perturbed F or G changes by<=2delta. Each hazard appears
    # at most once in Quit, at most twice in the finite Continue protocol;
    # differentiating one Bernoulli occurrence costs at most2delta.
    # Thus every derivative entry changes by<=6delta.
    row_norms = [Fr(sum(abs(z) for z in row), MDEN) for row in mm]
    perturb_defect = max(2*DELTA*n*GRID/r for n, r in zip(row_norms, radii))
    perturb_lip = max(6*DELTA*n*sum(radii)/r for n, r in zip(row_norms, radii))
    worst_perturb_lip = max(worst_perturb_lip, perturb_lip)
    worst_perturb_defect = max(worst_perturb_defect, perturb_defect)
    lip += perturb_lip
    defect += perturb_defect
    assert lip < Fr(2, 5), (cell_index, 'Lipschitz', float(lip))
    assert defect < Fr(3, 5), (cell_index, 'center displacement', float(defect))
    assert lip+defect < Fr(99, 100), (cell_index, 'self map', float(lip+defect))
    for poly in gpolys:
        lo, hi = interval(poly, lowpowers, highpowers)
        assert Fr(hi, GDEN)+2*DELTA < -Fr(1, 100), (cell_index, 'inactive gap')
        largest_gap = max(largest_gap, Fr(hi, GDEN)+2*DELTA)
    worst_lip = max(worst_lip, lip)
    worst_defect = max(worst_defect, defect)
    worst_image = max(worst_image, lip+defect)
    if (cell_index+1) % 25 == 0:
        print('Certified cells', cell_index+1, 'through L=', str(right), flush=True)

print('PASS: exact190-cell cover[8,50]; every active hazard in(1/500,3/5).')
print('PASS: full60 tube radius1e-8; Lipschitz<2/5; displacement<3/5; image<99/100.')
print('PASS: all four inactive gaps<−1/100; two distinct hazards>1/20 at every phase.')
print('PASS: all12 policy/cyclic identities; eight inactive raw coordinates absent from every endpoint.')
print('Diagnostics only:', {'lip': float(worst_lip), 'defect': float(worst_defect),
                           'image': float(worst_image), 'gap': float(largest_gap),
                           'min_hazard': float(smallest_hazard),
                           'perturb_lip': float(worst_perturb_lip),
                           'perturb_defect': float(worst_perturb_defect)})
```

## Appendix C. Simultaneous unbounded pair and two-triple stationary region

```python
"""Exact stationary certificate for three independent passive penalties.

Run with Python, SymPy, NumPy, and SciPy. Floating point only proposes
rational centers and preconditioners; acceptance and coverage are exact.
Failure aborts without a theorem claim. This does not decide Fin4.
"""
from math import comb
from time import monotonic

from itertools import combinations
import numpy as np
import sympy as s
from scipy.optimize import root

Q=s.Rational
I=range(4)
A=s.Matrix([[0,1,-Q(7,10),-Q(1,20)],[1,0,-Q(1,20),-Q(7,10)],
            [-Q(1,20),-Q(7,10),0,1],[-Q(7,10),-Q(1,20),1,0]])
J=(s.ones(4)-s.eye(4))/100
for i in I: J[i,i^1]=i+1
G=A+J
B=G.inv()
contacts={}
for S,sign in zip(combinations(I,2),(-1,-1,1,1,-1,-1)):
    lo,hi=[i for i in I if i not in S]
    contacts[lo,S]=sign
    contacts[hi,S]=-sign
z=s.Matrix(s.symbols('z0:4'))
t,a,b=s.symbols('t a b')
E=[]
for i in I:
    others=tuple(j for j in I if j!=i)
    contact=sum(-A[i,j]*t*z[j] for j in others)
    contact+=sum(contacts[i,S]*t**2*s.prod(z[j] for j in S)
                 for S in combinations(others,2))
    contact-=t**3*s.prod(z[j] for j in others)
    E.append(s.cancel((s.prod(1+t*z[j] for j in others)-1)*contact/t))
H=-G*z+s.Matrix([a*z[1]*z[2],(1-a)*b*z[0]*z[2]*z[3],0,(1-a)*(1-b)*z[0]*z[1]*z[2]])+s.Matrix(E)
H=s.simplify(H)
fn=s.lambdify((z,a,b,t),H,'numpy')
jn=s.lambdify((z,a,b,t),H.jacobian(z),'numpy')


# Reconstruct all sixty raw coordinates, including both contact-preserving
# changes, and check the complete stationary endpoint field independently.
L,M,P=s.symbols('L M P')
odds=s.Matrix(s.symbols('x0:4'))
table={}
for mask in range(1,16):
    coalition=frozenset(i for i in I if mask>>i&1)
    for i in I:
        opponents=tuple(sorted(coalition-{i}))
        passive=(0 if not opponents else G[i,opponents[0]] if len(opponents)==1
                 else -L if i==0 and opponents==(1,2)
                 else -M if i==1 and opponents==(0,2,3)
                 else -P if i==3 and opponents==(0,1,2) else 0)
        contact=(0 if not opponents else -A[i,opponents[0]] if len(opponents)==1
                 else contacts[i,opponents] if len(opponents)==2 else -1)
        table[i,coalition]=passive+(contact if i in coalition else 0)
assert len(table)==60
changed={(i,S) for (i,S),value in table.items() if s.diff(value,M)!=0 or s.diff(value,P)!=0}
assert changed=={(1,frozenset((0,2,3))),(1,frozenset((0,1,2,3))),
                 (3,frozenset((0,1,2))),(3,frozenset((0,1,2,3)))}
for phases in (((0,3),(0,2),(1,2),(1,3)),((1,2),(1,2,3),(0,1,3))):
    used=set()
    for active in phases:
        for i in I:
            others=tuple(j for j in active if j!=i)
            for size in range(len(others)+1):
                for selected in combinations(others,size):
                    S=frozenset(selected)
                    if S: used.add((i,S))
                    used.add((i,S|{i}))
    assert not (used & changed)
for i in I:
    others=tuple(j for j in I if j!=i)
    denominator=s.prod(1+odds[j] for j in others)
    ppoly=qpoly=0
    for size in range(len(others)+1):
        for selected in combinations(others,size):
            S=frozenset(selected)
            monomial=s.prod(odds[j] for j in S)
            if S: ppoly+=table[i,S]*monomial
            qpoly+=table[i,S|{i}]*monomial
    # [(1-h)Q-P]/h^2 = (denominator-1)qpoly-denominator*ppoly.
    endpoint=s.expand((denominator-1)*qpoly-denominator*ppoly)
    pulled=s.cancel(endpoint.subs(dict(zip(odds,t*z))).subs({L:a/t,M:(1-a)*b/t**2,P:(1-a)*(1-b)/t**2})/t)
    assert s.expand(pulled-H[i])==0
assert G.det()!=0 and all(value>0 for value in G.inv())
print('PASS: full60, both periodic full endpoint menus ignore M,P, exact odds field')

SCALE = (40,160,8,30)
y=s.symbols('y0:4')
r=s.symbols('r')
state_substitution=dict(zip(z,[SCALE[i]*y[i] for i in range(4)]))
field=s.Matrix([s.expand(f.subs(t,r/40).subs(state_substitution)) for f in H])
variables=(*y,a,b,r)
polys=[s.Poly(f,*variables) for f in field]
C=s.ilcm(*[c.q for p in polys for c in p.coeffs()])
C=int(C)
terms=[{e:int(c*C) for e,c in p.terms()} for p in polys]
jterms=[[{tuple(e[k]-(k==j) for k in range(7)):c*e[j]
          for e,c in row.items() if e[j]} for j in range(4)] for row in terms]
fnum=s.lambdify((y,a,b,r),field,'numpy')
jnum=s.lambdify((y,a,b,r),field.jacobian(y),'numpy')
pnum=s.lambdify((y,a,b,r),field.jacobian((a,b,r)),'numpy')
hjnum=s.lambdify((y,a,b,r),[field.jacobian(y).diff(v) for v in variables],'numpy')
N=2**40
D=max(sum(e) for row in jterms for col in row for e in col)
NP=[N**k for k in range(40)]
LDEN=C*NP[D+2]
DY=max(sum(e[:4]) for row in terms for e in row)
DP=max(sum(e[4:]) for row in terms for e in row)
DDEN=C*NP[DY+1+DP]
assert (C,D,DY,DP)==(200,10,6,5)
assert LDEN==DDEN==200*N**12
jbase=set(e for row in jterms for col in row for e in col)|{(0,)*7}
jexps=sorted(jbase|{tuple(e[k]-(k==l) for k in range(7))
                   for e in jbase for l in range(7) if e[l]})
fexps=sorted(set(e for row in terms for e in row))
zero=(0,)*7


def roundgrid(value):
    return int(np.floor(float(value)*N+.5))


def certify(box, seed):
    assert all(box[2*j+1]-box[2*j]>=2 and (box[2*j+1]-box[2*j])%2==0 for j in range(3)), ("ODD GRID WIDTH",box)
    loA,hiA,loB,hiB,loR,hiR=box
    ma=(loA+hiA)//2; mb=(loB+hiB)//2; mr=(loR+hiR)//2
    ha=(hiA-loA)//2; hb=(hiB-loB)//2; hr=(hiR-loR)//2
    av,bv,rv=ma/N,mb/N,mr/N
    rr=root(lambda yy:fnum(yy,av,bv,rv).ravel(), seed,
            jac=lambda yy:jnum(yy,av,bv,rv),tol=1e-11)
    candidate=rr.x
    if not np.all(np.isfinite(candidate)) or min(candidate)<=1e-5:
        return False,seed,None
    center=[roundgrid(value) for value in candidate]
    cf=np.array(center,dtype=float)/N
    jac=jnum(cf,av,bv,rv)
    try: mfloat=np.linalg.inv(jac)
    except np.linalg.LinAlgError: return False,candidate,None
    m=[[roundgrid(mfloat[i,j]) for j in range(4)] for i in range(4)]
    sensitivity=np.abs(mfloat@pnum(cf,av,bv,rv))@np.array([ha/N,hb/N,hr/N])
    radii=[max(1,int(np.ceil(N*(2.2*sensitivity[i]+0.0001*(ha+hb+hr)/N+1e-8))))
           for i in range(4)]
    low=[center[i]-radii[i] for i in range(4)]+[loA,loB,loR]
    high=[center[i]+radii[i] for i in range(4)]+[hiA,hiB,hiR]
    if any(4*low[i]*SCALE[i]<=N or high[i]*SCALE[i]>=200*N for i in range(4)):
        return False,candidate,None
    maxpower=max(max(e) for e in jexps)
    lop=[[value**k for k in range(maxpower+1)] for value in low]
    hip=[[value**k for k in range(maxpower+1)] for value in high]
    bounds={};points={}
    mid=center+[ma,mb,mr]
    midp=[[value**k for k in range(maxpower+1)] for value in mid]
    for e in jexps:
        ll=hh=pp=NP[D-sum(e)]
        for k,ex in enumerate(e):
            ll*=lop[k][ex]; hh*=hip[k][ex]; pp*=midp[k][ex]
        bounds[e]=(ll,hh)
        points[e]=pp
    lnums=[]
    for i in range(4):
        rownum=0
        for j in range(4):
            p={}
            for k in range(4):
                for e,c in jterms[k][j].items(): p[e]=p.get(e,0)-m[i][k]*c
            if i==j: p[zero]=p.get(zero,0)+C*N
            variation=abs(sum(c*points[e] for e,c in p.items()))*N
            for l,width in enumerate(radii+[ha,hb,hr]):
                if 2*loA>N or 2*loB>N:
                    # Every derivative is multiaffine in (a,b). Evaluate its
                    # four exact parameter vertices before bounding state/r
                    # monomials; this retains cancellations near a=1.
                    corner_bounds=[]
                    for avalue in (loA,hiA):
                        for bvalue in (loB,hiB):
                            grouped={}
                            for e,c in p.items():
                                if not e[l]: continue
                                de=tuple(e[k]-(k==l) for k in range(7))
                                assert de[4]<=1 and de[5]<=1
                                rest=de[:4]+(de[6],)
                                dc=c*e[l]*avalue**de[4]*bvalue**de[5]*NP[D-sum(de)]
                                grouped[rest]=grouped.get(rest,0)+dc
                            lower=upper=0
                            for ex,dc in grouped.items():
                                mn=mx=1
                                for coordinate,power in zip((0,1,2,3,6),ex):
                                    mn*=lop[coordinate][power]
                                    mx*=hip[coordinate][power]
                                if dc>=0: lower+=dc*mn;upper+=dc*mx
                                else: lower+=dc*mx;upper+=dc*mn
                            corner_bounds.append((lower,upper))
                    ll=min(pair[0] for pair in corner_bounds)
                    hh=max(pair[1] for pair in corner_bounds)
                else:
                    ll=hh=0
                    for e,c in p.items():
                        if not e[l]: continue
                        de=tuple(e[k]-(k==l) for k in range(7))
                        dc=c*e[l]
                        mn,mx=bounds[de]
                        if dc>=0: ll+=dc*mn;hh+=dc*mx
                        else: ll+=dc*mx;hh+=dc*mn
                variation+=max(abs(ll),abs(hh))*width
            rownum+=variation*radii[j]
        if rownum>=LDEN*radii[i]: return False,candidate,None
        lnums.append(rownum)
    # Precondition at the fixed center, then Taylor-expand only the three
    # parameters. Integer homogenization retains the cancellations exactly.
    cp=[[value**k for k in range(DY+1)] for value in center]
    state_mono={}
    for e in fexps:
        value=NP[DY-sum(e[:4])]
        for k in range(4): value*=cp[k][e[k]]
        state_mono[e]=value
    dnums=[]
    for i in range(4):
        param={}
        for k in range(4):
            for e,c in terms[k].items():
                ex=e[4:]
                param[ex]=param.get(ex,0)+m[i][k]*c*state_mono[e]
        translated={}
        for (p,q,u),c in param.items():
            for j in range(p+1):
                for k in range(q+1):
                    for v in range(u+1):
                        cc=c*comb(p,j)*comb(q,k)*comb(u,v)*ma**(p-j)*mb**(q-k)*mr**(u-v)*NP[DP-p-q-u]
                        translated[j,k,v]=translated.get((j,k,v),0)+cc
        defect=sum(abs(c)*ha**j*hb**k*hr**v for (j,k,v),c in translated.items())
        dnum=defect*N
        if lnums[i]*DDEN+dnum*LDEN>=radii[i]*LDEN*DDEN:
            return False,candidate,None
        dnums.append(dnum)
    stats=(max(lnums[i]/(LDEN*radii[i]) for i in range(4)),
           max((lnums[i]/LDEN+dnums[i]/DDEN)/radii[i] for i in range(4)),
           min(low[i]*SCALE[i]/N for i in range(4)),
           max(high[i]*SCALE[i]/N for i in range(4)))
    return True,candidate,stats


def split_axis(box, seed):
    mid=[(box[2*j]+box[2*j+1])/(2*N) for j in range(3)]
    widths=np.array([(box[2*j+1]-box[2*j])/(2*N) for j in range(3)])
    try:
        jac=jnum(seed,*mid)
        sens=np.abs(np.linalg.solve(jac,pnum(seed,*mid)))
        weight=np.maximum(np.abs(seed),0.01)
        rawh=hjnum(seed,*mid)
        curvature=[]
        inverse=np.linalg.inv(jac)
        for second in rawh:
            weighted=np.abs(inverse@second)*weight[None,:]/weight[:,None]
            curvature.append(np.max(np.sum(weighted,axis=1)))
        curvature=np.array(curvature)
        scores=(curvature[4:]+curvature[:4]@sens)*widths
        scores+=np.max(sens/weight[:,None],axis=0)*widths
        # Positive width floor prevents insensitive axes from being ignored
        # indefinitely. The split decision is heuristic; acceptance is exact.
        scores+=0.03*widths
        if np.all(np.isfinite(scores)): return int(np.argmax(scores))
    except (ValueError,np.linalg.LinAlgError): pass
    return int(np.argmax(widths))


def wedge_volume2(box):
    al,ah,bl,bh,rl,rh=box
    u=max(al,rl);v=min(ah,rh)
    diagonal=(v-rl)**2-(u-rl)**2 if u<v else 0
    rectangle=2*max(0,ah-max(al,rh))*(rh-rl)
    return (diagonal+rectangle)*(bh-bl)


if __name__=='__main__':
    started=monotonic(); count=attempts=0; deepest=0; volume=0
    worst=[0,0,float('inf'),0]
    stack=[((0,N,0,N,0,N),np.array([20,10,4,2])/np.array(SCALE),0)]
    assert wedge_volume2(stack[0][0])==N**3
    while stack:
        box,seed,depth=stack.pop()
        if box[4]>=box[1]:
            assert wedge_volume2(box)==0
            continue
        attempts+=1
        ok,nextseed,stats=certify(box,seed)
        if ok:
            count+=1;deepest=max(deepest,depth)
            volume+=wedge_volume2(box)
            worst=[max(worst[0],stats[0]),max(worst[1],stats[1]),
                   min(worst[2],stats[2]),max(worst[3],stats[3])]
            if count%1000==0: print('accepted',count,'attempted',attempts,'depth',depth,
                                   'volume',volume/N**3,'seconds',round(monotonic()-started),flush=True)
        else:
            assert depth<55, ('DEPTH FAILURE',box,depth,nextseed)
            axis=split_axis(box,nextseed)
            lo,hi=box[2*axis:2*axis+2];mid=(lo+hi)//2
            assert lo<mid<hi, ('GRID EXHAUSTED',box,axis)
            left=list(box);left[2*axis+1]=mid
            right=list(box);right[2*axis]=mid
            assert wedge_volume2(box)==wedge_volume2(left)+wedge_volume2(right)
            stack.append((tuple(right),nextseed,depth+1))
            stack.append((tuple(left),nextseed,depth+1))
    assert volume==N*N*N
    print('PASS',count,'accepted',attempts,'attempts','depth',deepest,'stats',worst,
          'seconds',monotonic()-started,flush=True)
```

## Appendix D. Exact off-ray boundary and raw-class comparisons

```python
"""Exact obstruction to two equilibrium architectures for one passive completion.

All higher passives vanish except F_0({1,2})=-20 and F_1({0,2,3})=-1/10000.

The first certificates and finite support census exclude every stationary
equilibrium after own singleton levels +1; the second excludes the proper four-crossing-pair cycle 03,02,12,13. This is
not a uniform-equilibrium counterexample or an exclusion of other cycles.

Run with Python 3 and SymPy. All certificate decisions use exact rationals.
"""
from fractions import Fraction as F
from itertools import combinations, product
from math import comb
import sympy as sp

I=tuple(range(4)); q=sp.symbols('q0:4'); x=sp.symbols('x0:4')
A=sp.Matrix([[0,1,-sp.Rational(7,10),-sp.Rational(1,20)],
             [1,0,-sp.Rational(1,20),-sp.Rational(7,10)],
             [-sp.Rational(1,20),-sp.Rational(7,10),0,1],
             [-sp.Rational(7,10),-sp.Rational(1,20),1,0]])
J=(sp.ones(4)-sp.eye(4))/100
for i in I: J[i,i^1]=i+1
Gamma=A+J
contact={}
for B,sign in zip(combinations(I,2),[-1,-1,1,1,-1,-1]):
    lo,hi=[i for i in I if i not in B]
    contact[lo,B]=sign; contact[hi,B]=-sign

def passive(i,B):
    if not B:return sp.Integer(0)
    if len(B)==1:return Gamma[i,B[0]]
    if i==1 and B==(0,2,3): return -sp.Rational(1,10000)
    return sp.Integer(-20 if i==0 and B==(1,2) else 0)

def delta(i,B):
    if not B:return sp.Integer(0)
    if len(B)==1:return -A[i,B[0]]
    if len(B)==2:return sp.Integer(contact[i,B])
    return sp.Integer(-1)

# All sixty native entries are built before the endpoint equations.
table={}
for mask in range(1,16):
    S=frozenset(i for i in I if mask & (1<<i))
    for i in I:
        B=tuple(sorted(S-{i}))
        table[i,S]=passive(i,B)+(delta(i,B) if i in S else 0)
assert len(table)==60
stationary=[]; D=[]
for i in I:
    others=tuple(j for j in I if j!=i)
    P=Q=Di=0
    for size in range(4):
        for B in combinations(others,size):
            S=frozenset(B)
            prob=sp.prod(q[j] if j in S else 1-q[j] for j in others)
            P+=prob*(table[i,S] if S else 0)
            Q+=prob*table[i,S|{i}]
            Di+=prob*delta(i,B)
    h=sp.prod(1-q[j] for j in others)
    stationary.append(sp.expand((1-h)*Q-P));D.append(sp.expand(Di))
weighted=sp.expand(sum((1-q[i])*D[i] for i in I))
identity=-sum(q[j]*sp.prod(1-q[k] for k in I if k!=j) for j in I)/4
identity-=sum((1-q[i])*sp.prod(q[j] for j in I if j!=i) for i in I)
assert sp.expand(weighted-identity)==0

# Canonical prefix phases (chronology reverses these).
w=(1,2,0,3); v=(3,1,2,0)
S=tuple(tuple(sorted((w[k],v[k]))) for k in I)
y=tuple(x[(k-1)%4]/(5+x[(k-1)%4]) for k in I)
C=tuple((1-x[k])*(1-y[k]) for k in I)
a=tuple(y[(k+1)%4]/100 for k in I)
e=[];b=[]
for k in I:
    t=(k+2)%4;g=w[k]+2
    e.append(g*y[t]*(1-x[t])-sp.Rational(1,25)*x[t]*(1-y[t])
             +passive(w[k],S[t])*x[t]*y[t]+C[t]*a[k])
for k in I:
    t=(k+3)%4;g=w[k]+2
    b.append(-sp.Rational(69,100)*y[t]*(1-x[t])+g*x[t]*(1-y[t])
             +passive(w[k],S[t])*x[t]*y[t]+C[t]*e[k])
cycle=[(1-x[k])*b[k]-sp.Rational(7,10)*x[k] for k in I]
inactive=[y[k]-x[k]*(1-y[k])/20+C[k]*a[(k+2)%4] for k in I]
inactive += [-sp.Rational(7,10)*y[k]*(1-x[k])+x[k]-2*x[k]*y[k]
              +C[k]*e[(k+1)%4] for k in I]
# Independently reconstruct the literal endpoint gaps for both inactive owners.
for k in I:
    hazards={w[k]:y[k],v[k]:x[k]}
    for owner,continuation,expected in (
        (w[(k+2)%4],a[(k+2)%4],inactive[k]),
        (w[(k+1)%4],e[(k+1)%4],inactive[4+k])):
        Di=0
        for size in range(3):
            for B in combinations(S[k],size):
                prob=sp.prod(hazards[j] if j in B else 1-hazards[j] for j in S[k])
                Di+=prob*delta(owner,B)
        assert sp.cancel(expected+Di-C[k]*continuation)==0
scale=100*sp.prod(5+xx for xx in x)
cycle=[sp.Poly(sp.cancel(scale*r),*x).as_expr() for r in cycle]
inactive=[sp.Poly(sp.cancel(scale*r),*x).as_expr() for r in inactive]

def frac(c):
    c=sp.Rational(c);return F(int(c.p),int(c.q))

def inverse(matrix):
    aug=[list(row)+[F(i==j) for j in I] for i,row in enumerate(matrix)]
    for j in I:
        pivot=next((i for i in range(j,4) if aug[i][j]),None)
        if pivot is None:return None
        aug[j],aug[pivot]=aug[pivot],aug[j]
        c=aug[j][j];aug[j]=[t/c for t in aug[j]]
        for i in I:
            if i!=j:
                c=aug[i][j];aug[i]=[a-c*b for a,b in zip(aug[i],aug[j])]
    return [row[4:] for row in aug]

def bernstein(polys,variables):
    deg=tuple(max(sp.Poly(p,*variables).degree(v) for p in polys) for v in variables)
    indices=tuple(product(*(range(d+1) for d in deg)))
    values=[]
    for p in polys:
        terms=[(powers,frac(c)) for powers,c in sp.Poly(p,*variables).terms()]
        co={}
        for m in indices:
            val=F(0)
            for powers,c in terms:
                if all(powers[j]<=m[j] for j in I):
                    for j in I:c*=F(comb(m[j],powers[j]),comb(deg[j],powers[j]))
                    val+=c
            co[m]=val
        values.append(co)
    return deg,indices,values

def split(coeffs,deg,indices,axis):
    left=[{} for _ in coeffs];right=[{} for _ in coeffs]
    rest=[j for j in I if j!=axis]
    for fixed in product(*(range(deg[j]+1) for j in rest)):
        index=[0]*4
        for j,value in zip(rest,fixed):index[j]=value
        line=[]
        for m in range(deg[axis]+1):
            index[axis]=m;line.append(tuple(index))
        for n,co in enumerate(coeffs):
            arr=[co[m] for m in line]
            left[n][line[0]]=arr[0];right[n][line[-1]]=arr[-1]
            for step in range(deg[axis]):
                arr=[(a+b)/2 for a,b in zip(arr,arr[1:])]
                left[n][line[step+1]]=arr[0];right[n][line[-step-2]]=arr[-1]
    return left,right

def evaluate(terms,point):
    return sum(c*sp_prod(point[j]**e[j] for j in I) for e,c in terms)

def sp_prod(values):
    value=F(1)
    for v in values:value*=v
    return value

def exact_exclusion(equalities,inequalities,variables,label):
    deg,indices,coeffs=bernstein(equalities+inequalities,variables)
    terms=[[(e,frac(c)) for e,c in sp.Poly(p,*variables).terms()] for p in equalities]
    derivative=[[[ (e,frac(c)) for e,c in sp.Poly(sp.diff(p,v),*variables).terms()]
                  for v in variables] for p in equalities]
    assert all(evaluate(t,[F(0)]*4)==0 for t in terms)
    stack=[(coeffs,[F(0)]*4,[F(1)]*4,0)]
    counts={'sign':0,'Newton':0,'origin':0};nodes=0;maxdepth=0
    while stack:
        co,lo,hi,depth=stack.pop();nodes+=1;maxdepth=max(maxdepth,depth)
        minima=[min(c.values()) for c in co];maxima=[max(c.values()) for c in co]
        if (any(minima[i]>0 or maxima[i]<0 for i in I)
                or any(m<0 for m in maxima[4:])):
            counts['sign']+=1;continue
        center=[(a+b)/2 for a,b in zip(lo,hi)]
        midjac=[[evaluate(p,center) for p in row] for row in derivative]
        M=inverse(midjac)
        if M is not None:
            lower=[[F(0)]*4 for _ in I];upper=[[F(0)]*4 for _ in I]
            for i in I:
                for j in I:
                    differences=[]
                    for index in indices:
                        if index[j]<deg[j]:
                            nxt=list(index);nxt[j]+=1
                            differences.append(deg[j]*(co[i][tuple(nxt)]-co[i][index])/(hi[j]-lo[j]))
                    lower[i][j]=min(differences);upper[i][j]=max(differences)
            mid=[[ (lower[i][j]+upper[i][j])/2 for j in I] for i in I]
            rad=[[ (upper[i][j]-lower[i][j])/2 for j in I] for i in I]
            bound=[[abs(F(i==j)-sum(M[i][k]*mid[k][j] for k in I))
                    +sum(abs(M[i][k])*rad[k][j] for k in I) for j in I] for i in I]
            residual=[evaluate(p,center) for p in terms]
            newcenter=[center[i]-sum(M[i][k]*residual[k] for k in I) for i in I]
            newradius=[sum(bound[i][j]*(hi[j]-lo[j])/2 for j in I) for i in I]
            if any(newcenter[i]+newradius[i]<lo[i] or newcenter[i]-newradius[i]>hi[i] for i in I):
                counts['Newton']+=1;continue
            if not any(lo) and max(sum(row) for row in bound)<1:
                # The map Id-MF is a strict contraction on this convex box.
                # Its known zero at the origin is the only possible zero.
                counts['origin']+=1;continue
        assert depth<60,(label,'subdivision budget exhausted',lo,hi)
        axis=max(I,key=lambda j:hi[j]-lo[j])
        left,right=split(co,deg,indices,axis)
        mid=(lo[axis]+hi[axis])/2
        left_hi=hi[:];left_hi[axis]=mid
        right_lo=lo[:];right_lo[axis]=mid
        stack.append((right,right_lo,hi,depth+1))
        stack.append((left,lo,left_hi,depth+1))
    assert counts['origin']==1
    print('PASS:',label,'nodes',nodes,'max depth',maxdepth,'leaves',counts,flush=True)
    return nodes,counts

def support_census():
    assert all(value>0 for value in Gamma.inv())
    # With precisely two proper active hazards, each active equation is
    # q_j[-Gamma_ij+q_j J_ij]. Its bracket cannot vanish in (0,1).
    for i,j in combinations(I,2):
        for owner,other in ((i,j),(j,i)):
            reduced=stationary[owner].subs({q[k]:0 for k in I if k not in (i,j)})
            assert sp.expand(reduced-q[other]*(-Gamma[owner,other]+q[other]*J[owner,other]))==0
            assert J[owner,other]>0
            assert Gamma[owner,other]<0 or Gamma[owner,other]>J[owner,other]
    # Pure supports of size at least two: a wrong-sign actual endpoint gap.
    for size in (2,3,4):
        for active in combinations(I,size):
            point={q[i]:int(i in active) for i in I}
            values=[r.subs(point) for r in stationary]
            assert any(values[i]<0 if i in active else values[i]>0 for i in I)
    # One sure and two proper owners: the proper contacts uniquely force
    # hazards, independently of all higher passive values.
    survivors=[]
    for active in combinations(I,3):
        for sure in active:
            mixed=[i for i in active if i!=sure]
            values={q[sure]:sp.Integer(1),**{q[i]:sp.Integer(0) for i in I if i not in active}}
            valid=True
            for owner in mixed:
                partner=next(i for i in mixed if i!=owner)
                a0=delta(owner,(sure,));a1=delta(owner,tuple(sorted((sure,partner))))
                if a0==a1:
                    assert a0!=0
                    valid=False;break
                hazard=sp.cancel(a0/(a0-a1));values[q[partner]]=hazard
                if not 0<hazard<1:valid=False
            if valid:
                assert all(stationary[i].subs(values)==0 for i in mixed)
                gap=sp.factor(stationary[sure].subs(values))
                assert gap<0
                survivors.append((active,sure,gap))
    assert survivors==[((0,1,2),1,-sp.Rational(265,578)),
                       ((0,2,3),2,-sp.Rational(150,289))]
    # Remaining proper players facing one or two sure opponents have a
    # nonzero singleton or pair contact and cannot be indifferent.
    assert all(delta(i,(j,))!=0 for i in I for j in I if i!=j)
    assert all(v!=0 for v in contact.values())
    print('PASS: positive inverse, proper pairs, all pure supports, all sure faces.',flush=True)

if __name__=='__main__':
    print('PASS: literal reward reconstruction, fixed-contact identity, inactive gaps.',flush=True)
    exact_exclusion(stationary,[],q,'stationary equalities: origin is the only cube zero')
    for missing in I:
        face=[q[i] if i==missing else stationary[i].subs(q[missing],0) for i in I]
        exact_exclusion(face,[],q,'proper triple missing '+str(missing))
    support_census()
    exact_exclusion(cycle,inactive,x,'canonical cycle: origin is the only feasible cube point')


# Complete raw-selector comparisons for the same off-ray table.
from itertools import combinations, permutations, product
import sympy as s

Q = s.Rational
I = tuple(range(4))
U = frozenset(I)
A = s.Matrix([[0, 1, -Q(7, 10), -Q(1, 20)],
              [1, 0, -Q(1, 20), -Q(7, 10)],
              [-Q(1, 20), -Q(7, 10), 0, 1],
              [-Q(7, 10), -Q(1, 20), 1, 0]])
J = (s.ones(4)-s.eye(4))/100
for i in I:
    J[i, i ^ 1] = i+1
Gamma = A+J
contacts = {}
for B, sign in zip(combinations(I, 2), (-1, -1, 1, 1, -1, -1)):
    lo, hi = [i for i in I if i not in B]
    contacts[lo, frozenset(B)] = sign
    contacts[hi, frozenset(B)] = -sign

def subsets(S):
    return [frozenset(C) for k in range(len(S)+1) for C in combinations(sorted(S), k)]

L_audit=20
def passive(i, B):
    if not B:
        return s.S.Zero
    if len(B) == 1:
        return Gamma[i, next(iter(B))]
    if i == 1 and B == frozenset((0, 2, 3)):
        return -Q(1, 10000)
    return -s.Integer(L_audit) if i == 0 and B == frozenset((1, 2)) else s.S.Zero

def contact(i, B):
    if not B:
        return s.S.Zero
    if len(B) == 1:
        return -A[i, next(iter(B))]
    return contacts[i, B] if len(B) == 2 else -s.S.One

Z = {(i, S): passive(i, S-{i})+(contact(i, S-{i}) if i in S else 0)
     for S in subsets(U) if S for i in I}
assert len(Z) == 60
assert Z[0, frozenset((1, 2))] == -20
assert Z[0, frozenset((0, 1, 2))] == -19
assert all(Z[i, U] == -1-Q(i == 1, 10000) for i in I)
assert all(J[i, j] > 0 for i in I for j in I if i != j)
assert Gamma.det() == Q(474131399, 4000000)
assert min(Gamma.inv()) > 0
for S in combinations(I, 3):
    principal = Gamma.extract(S, S)
    assert principal.det() > 0
    assert any(principal.inv()[k, k] < 0 for k in range(3))
for i in I:
    assert sorted(-Gamma[i, j] for j in I if Gamma[i, j] < 0) == [Q(1, 25), Q(69, 100)]
    assert J[i, i ^ 1] == Gamma[i, i ^ 1]-1

# Every universal proper-child zero-debt lift has a strict counterexample.
child_witnesses = {}
triple_coalitions = {(0, 1, 2): (0, 2), (0, 1, 3): (1, 3),
                    (0, 2, 3): (0, 3), (1, 2, 3): (1, 2)}
for C in subsets(U):
    if not C or C == U:
        continue
    if len(C) == 1:
        S = C
    elif len(C) == 2:
        a, b = sorted(C)
        S = frozenset((a,)) if b == (a ^ 1) else C
    else:
        S = frozenset(triple_coalitions[tuple(sorted(C))])
    for i in C:
        if i in S:
            assert (1+Z[i, S] > 0 if len(S) == 1 else contact(i, S-{i}) > 0)
        else:
            assert contact(i, S) < 0
    omitted = [i for i in U-C if contact(i, S) > 0]
    assert omitted
    child_witnesses[tuple(sorted(C))] = (tuple(sorted(S)), omitted)
assert len(child_witnesses) == 14

# One finite profile defeats every universal own-payoff upper selector.
q = Q(1, 100)
survival = (1-q)**4
native_stage = [sum(Z[i, S]*q**len(S)*(1-q)**(4-len(S))
                    for S in subsets(U) if S) for i in I]
native_values = [z/(1-survival) for z in native_stage]
assert native_values == [Q(4176707, 15761596), Q(8889899, 15761596)-Q(1,10000)*q**3/(1-survival),
                         Q(12809507, 15761596), Q(16730699, 15761596)]
assert min(native_values) > Q(1, 4)
assert survival**100 < Q(1, 5)
assert all((1-survival**100)*(1+z) > 1 for z in native_values)

# Immediate Quit guarantees at least -1/10000 at owners1,2, including
# the changed participant grand entry for owner1.
assert all(1+Z[i, S] >= -Q(1,10000) for i in (1, 2) for S in subsets(U) if i in S)
assert -Q(27,68)+Q(5,17)*(1+Q(1,10000)) < 0

for L_audit in (20,100):
    # The entire previous repeated-pair fixed-tube criterion, all eight roles.
    mate = (3, 2, 1, 0)
    counts = {'M0': 0, 'left': 0, 'right': 0}
    for role in permutations(I):
        g = s.Matrix(4, 4, lambda i, j: Gamma[role[i], role[j]])
        if any((g[i, j] > 0) != (j == (i ^ 1)) for i in I for j in I if i != j):
            continue
        premiums = s.Matrix(4, 4, lambda i, j: J[role[i], role[j]])
        p = [premiums[i, mate[i]] for i in I]
        raw = [passive(role[i], frozenset(role[k] for k in I if k not in (i, mate[i]))) for i in I]
        beta = {i: (p[mate[i]]-g[mate[i], i])/p[mate[i]] for i in (0, 3)}
        d = {i: 1+beta[i] for i in (0, 3)}
        pp = p[:]
        pp[0] /= d[3]
        pp[3] /= d[0]
        c = [pp[i]-g[i, mate[i]] for i in I]
        P = raw[:]
        for i in (1, 2):
            P[i] = ((1+beta[0]*beta[3])*raw[i]+beta[3]*g[i, 0]+beta[0]*g[i, 3])/(d[0]*d[3])
        guards = [g[0, 1] >= pp[0], g[0, 2] <= P[0] <= g[0, 1],
                  g[3, 2] >= pp[3], g[3, 1] <= P[3] <= g[3, 2],
                  g[2, 0] <= P[2] <= g[2, 3], g[2, 3] >= pp[2]]
        if not all(guards):
            counts['M0'] += 1
            continue
        failures = []
        for side, y, t in [('left', Q(12, 25), Q(18563485, 10**8)),
                            ('right', Q(51, 100), Q(20364495, 10**8))]:
            h = (1-y)*(1-t)
            RR = {i: g[i, 1]*y*(1-t)+g[i, 2]*t*(1-y)+raw[i]*y*t for i in (0, 3)}
            assert min(RR.values()) > 0
            def bracket(i):
                lo, hi = s.S.Zero, s.S.One
                for _ in range(80):
                    mid = (lo+hi)/2
                    val = c[i]*mid/(1-mid)-pp[i]*h*mid-RR[i]
                    if val < 0:
                        lo = mid
                    else:
                        hi = mid
                return lo, hi
            r0, r3 = bracket(3), bracket(0)
            def G1(a, b):
                return (g[1, 0]*a*(1-b)+g[1, 3]*b*(1-a)+P[1]*a*b
                        +pp[1]*t*(1-a)*(1-b)-c[1]*t/(1-t))
            values = [G1(a, b) for a, b in product(r0, r3)]
            if side == 'left' and max(values) < 0:
                failures.append(side)
            if side == 'right' and min(values) > 0:
                failures.append(side)
        assert failures
        counts[failures[0]] += 1
    assert counts == {'M0': 3, 'left': 3, 'right': 2}

L_audit=20

# Flexible crossing guards, all matching roles, already fail at x=1,y=.106.
w0, v0 = (1, 2, 0, 3), (3, 1, 2, 0)
matching_roles = []
for role in permutations(I):
    w, v = [role[i] for i in w0], [role[i] for i in v0]
    if not all(contact(w[k], frozenset((v[k],))) > 0 and contact(v[k], frozenset((w[k],))) > 0 for k in I):
        continue
    matching_roles.append(role)
    t = [frozenset((w[k], v[k])) for k in I].index(frozenset((1, 2)))
    vertex = Gamma[0, v[t]]*Q(894, 1000)-20*Q(106, 1000)
    assert vertex <= -Q(83, 250) < 0
assert len(matching_roles) == 8

# Exact fixed singleton data admit only the identity representation, even with
# independent nonnegative favorite increments and positive row rescalings.
admitted = []
for role in permutations(I):
    scale = []
    okay = True
    for i in I:
        cross = [j for j in I if j not in (i, i ^ 1)]
        if any(Gamma[role[i], role[j]] >= 0 for j in cross):
            okay = False
            break
        ratios = [Gamma[i, j]/Gamma[role[i], role[j]] for j in cross]
        if ratios[0] != ratios[1]:
            okay = False
            break
        scale.append(ratios[0])
    if okay and all(scale[i]*J[role[i], role[i ^ 1]] >= J[i, i ^ 1] for i in I):
        admitted.append((role, scale))
assert admitted == [((0, 1, 2, 3), [1, 1, 1, 1])]
lo = list(map(Q, ('.60', '.65', '.40', '.60')))
yy = [lo[(k-1)%4]/(5+lo[(k-1)%4]) for k in I]
k = w0.index(0)
cap = yy[(k+1)%4]/100
for t in ((k+2)%4, (k+3)%4):
    xx, y = lo[t], yy[t]
    cap = (Gamma[0, w0[t]]*y*(1-xx)+Gamma[0, v0[t]]*xx*(1-y)
           +passive(0, frozenset((w0[t], v0[t])))*xx*y+(1-xx)*(1-y)*cap)
assert cap == -Q(359623, 1512000) < 0
assert -20 < -3

# Explicit older cube and literal-family exclusions, valid for the full new cube.
delta = Q(1, 10**8)
assert Q(1, 100)-2*delta > 0
favorite_ratio_lower = (1-2*delta)/(2+2*delta)
assert favorite_ratio_lower > Q(1, 11)
assert favorite_ratio_lower > Q(1, 101)
old_radius = Q(1, 10**9)
scale_upper = 2*old_radius/(1-2*delta)  # old revisit grand-native reward ~0
assert scale_upper*(5+2*delta) < Q(1001, 1000)-2*old_radius
old_e1 = Q(1, 50000000)
assert (Q(69, 100)-2*delta)/(Q(1, 25)+2*delta) > 17
assert (1+2*old_e1)/(1-2*old_e1) < 2

# The old ray and its full sixty-coordinate tube fail even after any
# relabeling, positive recipient scaling, and additive recipient offsets.
# Singleton and participant-pair native entries constrain the row scale.
delta=Q(1,10**8)
possible=[]
for role in permutations(I):
    intervals=[]
    for i in I:
        lower=Q(0); upper=s.oo
        valid=True
        for j in I:
            if i==j: continue
            for actual,base in ((Gamma[role[i],role[j]],Gamma[i,j]),
                                (J[role[i],role[j]],J[i,j])):
                if (actual>0)!=(base>0): valid=False;break
                aa,bb=abs(actual),abs(base)
                lower=max(lower,aa/(bb+2*delta))
                upper=min(upper,aa/(bb-2*delta))
            if not valid:break
        if not valid or lower>upper:break
        intervals.append((lower,upper))
    if len(intervals)==4:possible.append((role,intervals))
assert len(possible)==1 and possible[0][0]==(0,1,2,3)
lo_scale,hi_scale=possible[0][1][1]
assert max(abs(lo_scale-1),abs(hi_scale-1))+2*hi_scale*delta < Q(1,10000)
# Comparing row1 grand with its own coordinate therefore fails every tube
# representation. The exact sparse ray is a subset of the same row1 test.

# Full polynomial-row-weight/odds-order wall exclusion from literal contacts.
# Positive odds fix binary cube vertices and positive weights preserve signs.
wall01={2:(contact(0,frozenset((1,2))),contact(1,frozenset((0,2)))),
        3:(contact(0,frozenset((1,3))),contact(1,frozenset((0,3))))}
wall23={0:(contact(2,frozenset((3,0))),contact(3,frozenset((2,0)))),
        1:(contact(2,frozenset((3,1))),contact(3,frozenset((2,1))))}
assert wall01=={2:(1,-1),3:(-1,1)}
assert wall23=={0:(-1,1),1:(1,-1)}
for preferred in (0,1):
    assert any(values[preferred]<0<values[1-preferred] for values in wall01.values())
for preferred in (2,3):
    assert any(values[preferred-2]<0<values[3-preferred] for values in wall23.values())
for preferred01,preferred23 in product((0,1),(2,3)):
    g01=wall01[preferred23];g23=wall23[preferred01]
    assert (g01[preferred01]<0<g01[1-preferred01]
            or g23[preferred23-2]<0<g23[3-preferred23])

print('PASS: off-ray full60 invariants and all14 proper quiet-child witnesses.')
print('PASS: finite payoff witness and repaired punishment lower bound.')
print('PASS: all8 repeated-pair roles; flexible/signed/compensated crossing tests.')
print('PASS: exact old ray/tube exclusion under all roles, positive row scales, offsets.')
print('PASS: all positive polynomial row-weight/odds/order choices fail a binary wall.')
print('PASS: explicit older cubes and literal-family invariant separations.')
print('Unspecified qualitative neighborhoods and generic supplied certificates remain unclassified.')

# Complementary tail point (L,M)=(100,1/10000). These checks assert only
# the named raw tests, not absence of an arbitrary stationary certificate.
tail_L=Q(100); tail_M=Q(1,10000)
b=min(Gamma.inv()); bigB=max(Gamma.inv()); kappa=b/(16*bigB); D=Q(16)
R0=1/(1+32*bigB**2*D/b)
pair_threshold=4*bigB*D/(b*kappa**2)+4/(4*b*kappa**2)
assert tail_L<pair_threshold
assert 4*b*(tail_L*kappa**2*R0+tail_M*kappa**3*R0**2)<2
# Uniform exclusion under every positive recipient rescaling d_i:
# kappa'<=1/16, D'=16*max(d), and b'*d_i<=min_k Gamma^-1[k,i].
# Therefore the pair threshold exceeds 16384*max(d), and the all-degree
# left side has the following scale-independent rational upper bound.
column_min=[min(Gamma.inv()[:,j]) for j in I]
assert 4*16*16**2==16384>tail_L
scaled_mass_upper=4*(tail_L*column_min[0]/16**2+tail_M*column_min[1]/16**3)
assert column_min[0]==Q(3229620,474131399)
assert column_min[1]==Q(59380,9676151)
assert scaled_mass_upper==Q(2583696145481,242755276288000)<2
assert tail_M<Q(7,20)

# The full common-height crossed upper guard fails at a binary outsider,
# for every height h in (0,1], because both endpoint contacts are positive.
for owner in I:
    favorite=owner^1
    assert any(contact(owner,frozenset((outside,)))>0
               and contact(owner,frozenset((favorite,outside)))>0
               for outside in I if outside not in (owner,favorite))
# The asymmetric weak crossed criterion's unit upper guard fails for every
# ordered selected pair, before its other hypotheses matter.
for owner,partner in permutations(I,2):
    assert any(contact(owner,T|{partner})>0
               for T in subsets(U-{owner,partner}))

# Every nontrivial stationary-response block quotient fails already in its
# linear terms, even with arbitrary positive recipient rescalings.
def partitions(items):
    if not items:
        yield ();return
    first,*rest=items
    for partition in partitions(rest):
        yield ((first,),)+partition
        for at in range(len(partition)):
            yield partition[:at]+(tuple(sorted((first,)+partition[at])),)+partition[at+1:]
possible_partitions=[]
for blocks in partitions(list(I)):
    okay=True
    for block in blocks:
        vectors=[[sum(Gamma[i,j] for j in target) for target in blocks] for i in block]
        reference=vectors[0]
        pivot=next((j for j,v in enumerate(reference) if v),None)
        for vector in vectors[1:]:
            if pivot is None:
                if any(vector):okay=False
            elif vector[pivot]*reference[pivot]<=0 or any(
                    vector[j]*reference[pivot]!=reference[j]*vector[pivot]
                    for j in range(len(blocks))):okay=False
    if okay:possible_partitions.append(blocks)
assert {tuple(sorted(map(len,p))) for p in possible_partitions}=={(4,),(1,1,1,1)}
assert all(sum(Gamma[i,j] for j in I)>0 for i in I)
# The one-block quotient is a positive scalar (degree+1); the singleton
# partition is Gamma itself, already R0 of degree+1 by the exact invariants.

# The three-passive-pole producer's eight raw guards, all24 role choices.
for role in permutations(I):
    a0,a1,a2,a3=role
    AA0=contact(a0,frozenset((a3,)))
    BB0=contact(a0,frozenset((a2,a3)))
    if not (AA0>0 and BB0<0):continue
    cc=AA0/(AA0-BB0)
    AA2=contact(a2,frozenset((a3,)))
    BB2=contact(a2,frozenset((a0,a3)))
    LL0=(1-cc)*contact(a1,frozenset((a3,)))+cc*contact(a1,frozenset((a2,a3)))
    LL1=(1-cc)*contact(a1,frozenset((a0,a3)))+cc*contact(a1,frozenset((a0,a2,a3)))
    FF0=cc*(cc*J[a3,a2]-Gamma[a3,a2])
    FF1=(1-cc)*contact(a3,frozenset((a0,)))+cc*contact(a3,frozenset((a0,a2)))
    assert not (AA2<0 and BB2<0 and LL0<0 and LL1<0 and FF0>0 and FF1<0)

print('PASS: tail point fails both exact passive-dominance mass thresholds.')
print('PASS: all guarded crossed heights/roles; all response-quotient partitions and positive row scales.')
print('PASS: three-passive-pole full24 role census.')

# A finite all-coordinate payoff witness at the complementary tail point.
tailZ=dict(Z)
tailZ[0,frozenset((1,2))]-=80
tailZ[0,frozenset((0,1,2))]-=80
qq=Q(1,1000);aa=(1-qq)**4
tail_values=[sum(tailZ[i,S]*qq**len(S)*(1-qq)**(4-len(S))
                 for S in subsets(U) if S)/(1-aa) for i in I]
assert min(tail_values)>Q(1,4)
assert aa**1000<Q(1,5)
assert all((1-aa**1000)*(1+value)>1 for value in tail_values)
print('PASS: all8 repeated-pair roles and finite payoff witness also at L100,M1/10000.')
```
