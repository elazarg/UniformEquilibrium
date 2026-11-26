# A signed collision bridge produces a fixed uniform-equilibrium payoff

This is a complete existence theorem for an explicit family of four-player
quitting games with strongly signed participant rewards and nonadditive
passive rewards. Fin4 for arbitrary reward tables remains open. The proof is
ordinary mathematics; no new Lean-checked theorem is asserted.

## 1. Exact raw-table statement and strategic inputs

There are four players I={0,1,2,3}, one live state, and independent private
Continue/Quit choices at each live date. The first nonempty quitting
coalition D absorbs at its finite reward vector r(D). Live play and literal
AllNever pay zero. There is no public correlation. A unilateral deviation
may replace the player's entire behavioral law, including every finite
deadline and Never.

Set kappa_i=r_i({i}) and Z_i(D)=r_i(D)-kappa_i for nonempty D only. Require
precisely the following32 native entries:

| D | Z0 | Z1 | Z2 | Z3 |
| --- | ---: | ---: | ---: | ---: |
| 0 | 0 | 2 | 2 | -1 |
| 1 | 3 | 0 | -2 | -2 |
| 2 | -1 | 1 | 0 | 1 |
| 3 | 3 | -3 | -1 | 0 |
| 12 | -12 | -100 | 0 | -6 |
| 13 | 2 | -100 | -1 | 0 |
| 23 | -6 | 9 | 3 | -100 |
| 123 | -8 | 11 | 2 | 1 |

The remaining28 native coordinates satisfy only these conditions:

- The seven Z0(D) with 0 in D and |D|>=2 may be any nonpositive numbers.
- Z1({0,1}) and Z2({0,2}) may be any nonpositive numbers.
- Z3({0,3})=K may be any real number.
- For i=1,2,3, all six Z_i(D) with 0 in D and
  D not in {{0},{0,i}} may be arbitrary real numbers.

These sets are disjoint. The own levels kappa_i are arbitrary real numbers. Equivalently the original
absorbing rewards are r_i(D)=kappa_i+Z_i(D), with live play and AllNever
unchanged at zero. Every profile below, and every opponents-only
profile faced by a deviator, absorbs almost surely. Consequently the row
translation adds exactly kappa_i to prescribed and deviating terminal
payoffs; it does not translate literal AllNever.

None of these 28 variable native entries is used as a prescribed absorbing
reward by the construction. The algebraic macro states and parameters are
therefore unchanged. The seven row0 entries occur only in its joining
comparisons; their nonpositivity protects player0 at the solo2, pair12,
triple123 and solo3 roots, where its prescribed native value is nonnegative.
The other two nonpositive entries protect players1,2 at solo0 roots. The
only remaining variable comparison is player3's solo0 joining offer Kq.
The 18 unrestricted entries are never queried by a prescribed outcome or
unilateral deviation on these supports.

**Theorem.** Every table in this raw class has the fixed original
uniform-equilibrium payoff

    W=(kappa_0, kappa_1+A1, kappa_2+A2, kappa_3).             (1)

Here A1 and A2 are the uniquely produced algebraic numbers defined below;
numerically A1 is approximately0.8616124826 and A2 approximately0.6489455273.
For every epsilon>0, one finite periodic behavioral profile delivers W
exactly as terminal payoff, has every full terminal deviation gain below
epsilon, and satisfies the uniform finite-horizon inequalities at W for
all sufficiently long horizons. Only the profile and horizon depend on
accuracy. When K<=0 the construction even gives an exact absorbing
periodic terminal Nash profile.

Only the displayed reward tests are inputs. The proof produces the scalar
algebraic root, all continuation annotations, every finite block and the
complete periodic schedule. No equilibrium, tail, selected Nash row,
invariant graph or return witness is assumed. Negative native continuation
values occur inside the finite collision bridge and are explicitly priced.

## Conjecture-facing change and coverage

The construction crosses negative continuation coordinates using a finite
pair12/triple123 bridge and a finite solo3 repair. Its only approximate
comparison is one small initial joining opportunity for player3. The exact
periodic Bellman equation prices this opportunity against every behavioral
deviation, while the prescribed payoff target is independent of accuracy.
This is an actual-data existence class, not a verifier for a supplied cycle.

The fixed singleton matrix is

    Gamma=[0,3,-1,3;2,0,1,-3;2,-2,0,-1;-1,-2,1,0].

Its only principal triple with entrywise nonnegative inverse is023, with

    Gamma_023^(-1)=(1/5)[1,3,1;1,3,6;2,1,2].

The outside inverse row is Gamma_{1,023}Gamma_023^(-1)=(-3,6,2)/5,
which is not nonnegative. The inverses of012,013,123 have negative entries
-1/5,-1,-3/8 respectively. Thus no choice of a three-player child meets
the complete raw inverse/passive-row criterion. These signs are unchanged
by relabeling a selected child. The signed participant entries and the
seven nonadditive passive entries in Section1 also place this class outside
the positive-premium, additive-passive fixed-matrix classes: for example
Z1(12)=-100 and Z3(23)=-100, while Z0(12)=-12 differs from
Gamma01+Gamma02=2. The finite producer below handles these actual rewards.
There is also a complete obstruction to every ordered nonpositive-anchor
selection. Such a selection would choose nonempty C, ordered blocks of C,
and positive weights on each block, require Z_c({j})<=0 for c in C,j
outside C, and require a nonpositive weighted participant sum on the first
block meeting each coalition. The positive singleton graph, with edge
c->j whenever Gamma_cj>0, has edges

    0->1,3; 1->0,2; 2->0; 3->2.

It is strongly connected. The passive singleton condition therefore forces
C=I. But coalition123 meets some first block in a nonempty subset of
{1,2,3}, and its participant rewards (11,2,1) are strictly positive.
No positive weights can satisfy the required nonpositive sum. This rejects
every marked set, every order and every block-weight selection at once.
It remains a strict obstruction under sufficiently small perturbations.

The same coalition is a premium trap: each of its owners has a positive
own-containing premium inside it. Its singleton charge at{1} is
Z2(12)+Z3(13)=0, so a strictly negative singleton-charge premise fails.
Its joining charge at{1,2} is Z3(123)-Z3(12)=7>0, so the required negative
upper-face charge fails with a strict margin as well. A nonzero
nonnegative upper-average weight on this trap cannot work because its
participant vector at123 is strictly positive. These are complete
obstructions on the fixed data, independent of the28 freely varying entries.
The theorem does not assert an exhaustive census of every conceivable
sufficient equilibrium criterion.

## 2. One-root identities

For a product root q and a specified native successor value u, let Q_i be
the forced-Quit offer, P_i the passive contribution from a nonempty
opponent quitting coalition, and H_i=product_(j!=i)(1-q_j). Continuing at
this date and following the prescribed continuation offers

    C_i=P_i+H_i u_i.

The prescribed native value is

    v_i=q_i Q_i+(1-q_i)C_i.                               (2)

Every root used below has all q_i<1. A legal root has Q_i=C_i=v_i at each
active owner and Q_i<=C_i=v_i at every quiet owner. These are finite
algebraic comparisons against the specified successor values; actual full
response caps will be proved by a separate periodic argument.

## Produced algebraic macro and exact closure

All values in this subsection are native prescribed-value annotations for
the raw family of Section1. Fix `y=1/25`. Let `P(w)` be the polynomial below,
and let `w` be its unique positive root:

```
5925636804644733974727250 w^5
 +7838727530168235775250281 w^4
 +1337222696480289357993259 w^3
 +49232500736262112787450 w^2
 +279128064680059185038 w
 -1668726734798132632 = 0.
```

All nonconstant coefficients are positive, so the polynomial is strictly
increasing on the positive axis. Exact rational evaluation gives opposite
signs at `3544554/10^9` and `3544555/10^9`. Define

```
E0 = -3(2078141123214034 w^3 -649791530287147 w^2
         -10839225840795 w -118826118826)
      /[19336(w-1)(3171813530 w^2 +17299342307 w -87038467)],
z = 2y/(101-106y),
T1 = -100z-100w+211zw,
T2 = w(3-y),
T3 = -z(100-101y),
x = (101z+97w-200zw)/[(1-z)(1-w)],
E2 = (2y+4w-3yw)/[(1-y)(1-w)],
T0 = 3y-z+3w-14yz-4yw-8zw+13yzw
       +(1-y)(1-z)(1-w)E0.
```

The triple root with hazards `(0,y,z,w)` has prescribed values
`T=(T0,T1,T2,T3)` and continuation `E=(E0,-x,E2,0)`. Its three active
indifference equations hold by these definitions.

Set

```
c = T2/(2+T2),  d = -T1/(101-T1),
C0 = 3c-d-14cd+(1-c)(1-d)T0,
C1 = -100d,
C3 = -2c+d-5cd+(1-c)(1-d)T3,
b = C0/(1+C0),
B1 = b+(1-b)C1,  B3 = b+(1-b)C3,
a = B3/(1+B3),
A1 = 2a+(1-a)B1,  A2 = 2a.
```

The pair12 root with hazards `(0,c,d,0)` has values `C=(C0,C1,0,C3)`
and continuation `T`; both active indifferences hold. A solo2 block of
aggregate hazard `b` has values `B=(0,B1,0,B3)` and continuation `C`.
A solo0 block of aggregate hazard `a` has values `A=(0,A1,A2,0)` and
continuation `B`. These are payoff/active-indifference identities; the solo0
block is implemented with one small seam by the consumer lemma.

Define the wash endpoint and following solo3 aggregate by

```
R=1-x/3,
V0=(E0-x)/R,  V2=(E2+x/3)/R,
h=V0/3.
```

Then the two exact closure identities are

```
A1(1-h)=3h,
A2(1-h)=V2+h.
```

Consequently a solo3 block of aggregate hazard `h`, continued by `A`, has
values `V=(V0,0,V2,0)`. The negative1 wash takes `E` to `V`; its finite
implementation is supplied separately. Thus the macro returns to precisely
`A`, independent of the accuracy used for the solo0 seam.

The closure identities have the following direct polynomial certificate.
After substituting the displayed rational expression for `E0`, put

```
D(w)=(241494w-7049)
     (3171813530w^2+2287878149w-19696111)
     (3171813530w^2+17299342307w-87038467).
```

Direct expansion gives the identities of rational functions

```
A1(1-h)-3h = 9P(w)/(4D(w)),
A2(1-h)-V2-h = P(w)/D(w).
```

Every factor of `D(w)` is strictly negative throughout the stated rational
root interval, and all other denominators in the definitions are separated
from zero. Thus `P(w)=0` proves both closure identities without a numerical
root claim.

The same rational interval computation gives the following enclosures
(the displayed decimal endpoints can be widened to rational decimal bounds):

```
a       in (0.3244725,0.3244731)
b       in (0.5209621,0.5209628)
c       in (0.00521856,0.00521857)
d       in (0.00430334,0.00430335)
h       in (0.2231223,0.2231227)
x       in (0.4286135,0.4286137)
E0      in (1.0023473,1.0023482)
E2      in (0.0980066,0.0980067)
B1      in (0.3148158,0.3148167)
A1      in (0.8616116,0.8616135)
A2      in (0.6489450,0.6489461).
```

Every hazard is strictly between zero and one. The wash hypotheses
`0<x<3`, `E0>x`, and `E2>3x/100` have strict margins, as do `B1>0`, `T0>1`, `C0>1`,
`V2>7/25`, and `h<28/125`.
For the pair12 root, the quiet player3 gap is

    -100d+101cd-C3 < -0.3432.

The other quiet row is player0, whose forced-Quit offer is nonpositive
throughout the raw family, whereas C0>1. At the triple123 root, its only
quiet row is again player0, with nonpositive Quit offer and T0>1.
At the solo2 root, player0's joining offer is nonpositive and its prescribed
value is0; player1's and player3's gaps are respectively -100b-B1 and
-100b-B3, both negative. These comparisons cover every quiet row at the
three finite middle roots. All active identities use only the32 fixed
coordinates in Section1. The target is W from that section.

## 3. Fixed44-root repair of negative player1 values

The triple123 root ends at E=(E0,-x,E2,0). The macro certificate gives

    0<x<3,  E0>x,  E2>3x/100.

At a solo3 root of hazard q, forced-Quit offers are

    (Z0({0,3})q, -100q, 3q, 0),

where the first coordinate is nonpositive throughout the raw family.
For a current state (s,-v,t,0), the successor required by (2) is

    ((s-3q)/(1-q), (-v+3q)/(1-q), (t+q)/(1-q), 0).          (3)

If 0<=v<3, s>=v and t>=3v/100, choose q=v/100. Player3 is indifferent;
players0,1,2 respectively have nonnegative prescribed value, the equality
-v=-100q, and t>=3q. All root comparisons hold. The successor satisfies

    v'=97v/(100-v),
    t'=(t+v/100)/(1-v/100),
    s'-v'=(s-v)/(1-v/100).

Thus the same conditions persist, with v decreasing and t increasing.
Let r=97/100. After n such roots their cumulative survival and state are

    S_n=1-x/3+(x/3)r^n,
    v_n=x r^n/S_n,
    s_n=(E0-3+3S_n)/S_n,
    t_n=(E2+1-S_n)/S_n.

Use exactly43 regular roots, then the final hazard q_last=v_43/3. The
final root sends the player1 successor coordinate to zero. Its player2
comparison requires t_43>=v_43, equivalent to

    r^43 <= (3E2+x)/(4x).

The right side exceeds109/400, whereas exact rational arithmetic gives
(97/100)^43<109/400. Player0 remains nonnegative and player1's comparison
is automatic. Every hazard is below1. The total survival is exactly

    S_43(1-v_43/3)=1-x/3=R.

This fixed44-root legal block therefore has successor

    V=((E0-x)/R, 0, (E2+x/3)/R, 0).                       (4)

It is entirely finite. The all-Continue interpretation when x=0 is also
valid, although the concrete macro has x>0.

## 4. Finite exact realization of the final solo3 aggregate

The macro gives V=(V0,0,V2,0), h=V0/3 in(0,1), V2>0, and

    A1(1-h)=3h,  A2(1-h)=V2+h.

After cumulative solo3 quitting probability t in[0,h], the forward state is

    ((V0-3t)/(1-t), 3t/(1-t), (V2+t)/(1-t), 0).            (5)

All first three coordinates are nonnegative. The first two quiet joining
offers are nonpositive. Player2's joining offer is3q, while its state
coordinate is at least V2. Hence every solo3 hazard q<=V2/3 is legal.

Choose theta=min(1/2,V2/6)>0. Repeatedly use theta until the remaining
conditional hazard needed to attain aggregate h is at most theta, then
use exactly that remainder. This terminates in finitely many dates since
(1-theta)^n tends to zero. It reaches A exactly by the two closure identities.
Its length depends only on the fixed algebraic macro, not the requested
accuracy or any free native reward. No diffuse limit is needed here.

## 5. The solo0 block has one explicitly bounded seam

Let 0<delta<a. Its first solo0 root has hazard delta. Write t for the
cumulative conditional probability of player0 quitting so far in this
block. The forward state determined by the aggregate-a payoff identity is

    u(t)=(0,(A1-2t)/(1-t),(2a-2t)/(1-t),t/(1-t)),
                                                        0<=t<=a.       (6)

The player1 coordinate is positive because
A1=2a+(1-a)B1 and B1>0; player2's coordinate is nonnegative. The native
joining offers at a solo0 root of hazard q are

    (0, Z1({0,1})q, Z2({0,2})q, Kq).

Consequently all comparisons except possibly player3's are legal along(6).
At the first root the state is A and player3's joining gain is exactly
K delta. Put m=max(1,K). Once t>0, choose

    q = min(t/m, a-t)/(1-t).                              (7)

The next cumulative probability is t'=min((1+1/m)t,a), so the process
reaches a after finitely many dates. Every selected hazard is below1: in
the growth case t<=am/(m+1)<m/(m+1), and the final remainder is below1
because a<1. For K>0,

    Kq <= (K/m)t/(1-t) <= u_3(t).

For K<=0 the same comparison is automatic. Thus all later roots are legal.
The final state is exactly B, and the whole block's aggregate hazard is a.
For fixed K its length is O(1+log(1/delta)); for K=1 the cumulative
probability doubles at every growth step.

The sole possible local error in the entire cycle is therefore the first
solo0 root's quiet-player3 gain

    e=max(K,0)delta.                                      (8)

The specified continuation endpoint still gives its prescribed value A3=0
exactly. If K<=0, even this first root is legal.

## 6. One fixed target and the full behavioral response bound

Repeat the following finite word forever:

1. The solo0 block of Section5, with aggregate a.
2. The one solo2 root of hazard b.
3. The pair12 root with hazards c,d.
4. The triple123 root with hazards y,z,w.
5. The fixed44-root block of Section3.
6. The finite solo3 block of Section4, with aggregate h.

Every listed hazard is below1. The macro certificate gives all active
indifferences and all quiet comparisons for the three middle roots. They
continue to hold throughout the raw family by Section1. The finite blocks
satisfy the exact payoff identities (2), and their endpoints are

    A -> B -> C -> T -> E -> V -> A.

For every delta the resulting period therefore has the SAME cyclic value
annotations. Period absorption is certain in the infinite repetition. Each
player has a positive quitting probability per period: player0 through a,
player1 through c or y, player2 through b, and player3 through w or the
solo3 blocks. In particular each player faces proper opponents. If
rho=min(a,b)>0, every opponents-only period has survival at most1-rho:
use player2's solo root for a deviation by0, and player0's aggregate for
any other deviator. The all-player survival is also below1.

Iterating (2) around the period uniquely identifies its actual prescribed
native payoff as A. It follows that its original payoff is exactly W in(1),
independently of delta.

For completeness, reduce unrestricted deviations directly. Before
absorption the only public observation is continued survival. Any independent
behavioral replacement induces a distribution of a first quitting date,
possibly Never. Against the periodic opponents, every pure deadline or
Never payoff satisfies the one-step response recursion. The full cap is
therefore the unique bounded periodic solution

    B_i^k=max(Q_i^k, P_i^k+H_i^k B_i^(k+1)).               (9)

Existence follows from the actual supremum of this complete response menu;
uniqueness follows by contraction through one full period, whose deleted
survival is below1. Arbitrary randomized stopping rules cannot exceed the
pure-response supremum.

Let D_i^k=B_i^k-v_i^k>=0. Because every own hazard is below1, the active
indifferences and quiet payoff identities give C_i^k=v_i^k at EVERY root,
including the seam. Thus

    D_i^k=max(Q_i^k-v_i^k, H_i^k D_i^(k+1)).               (10)

For players0,1,2 all first arguments are nonpositive, so periodicity forces
D_i^k=0 everywhere. For player3 they are nonpositive except at the initial
seam, where the argument is K delta. Unrolling once around the period gives

    D_3^start=max(K delta, H_3^period D_3^start).

Since H_3^period<1 and D_3^start>=0, this is exactly

    (B-U)^start=(0,0,0,max(K,0)delta).                    (11)

This is a full terminal best-response statement. No finite-horizon response
menu or prescribed continuation restriction is substituted for arbitrary
behavioral deviation. In particular K<=0 gives an exact absorbing periodic
Nash profile; for any finite K, arbitrary positive terminal accuracy follows
by choosing delta sufficiently small.

## 7. Uniform finite-horizon conclusion with the same payoff

Here is a direct fixed-target consumer, without selecting a subsequential
payoff. For a requested error epsilon>0 choose

    0<delta<min(a,epsilon/[4 max(1,K)]).

Let L be this profile's finite period length. Against ANY unilateral
behavioral replacement, absorption occurs no later than the first opponent
quit. Its expectation is bounded by a constant depending only on L and
rho; for instance L/rho+1 suffices. The same bound holds under the prescribed
profile. Let M be a finite absolute bound on the original rewards, including
zero live play. The difference between a terminal payoff and an N-stage
average payoff is bounded in expectation by

    2M(L/rho+2)/N,

uniformly over all unilateral behavioral replacements. Thus, for all
sufficiently large N, prescribed average payoff is within epsilon/4 of W,
and every unilateral average payoff is at most W_i+epsilon/2. Comparison
with the prescribed average then bounds every deviation gain by epsilon.
The target W is fixed before epsilon; only the profile and horizon threshold
change. This proves the uniform-equilibrium payoff claim for the printed
table and the full raw family of Section1.

For any fixed finite raw table, M is finite even though the allowed family
has no common reward bound. No uniform horizon threshold over unbounded
raw variations is asserted. The proof uses ordinary finite probability and
algebra; no unrestricted Fin4 closure is claimed.

## 8. Boundary checks and scope

One concrete completion takes kappa_i=1 and fills the seven remaining
coalitions as follows:

| D | Z0 | Z1 | Z2 | Z3 |
| --- | ---: | ---: | ---: | ---: |
| 01 | 0 | -1 | -10 | -12 |
| 02 | 0 | 5 | -10 | 7 |
| 012 | -13 | 6 | -9 | 11 |
| 03 | -3 | 3 | -5 | 1 |
| 013 | -7 | 8 | 10 | -10 |
| 023 | -7 | -8 | -3 | 15/2 |
| 0123 | -5 | -9 | 8 | 21/2 |

Together with Section1 this specifies all60 original rewards. Its fixed
uniform-equilibrium payoff is approximately
`(1,1.8616124826,1.6489455273,1)`. The exact target is W, not this rounded
decimal vector.

This completion also rules out nonzero nonnegative payoff weights that
would make every proper-coalition reward nonnegative: its original vectors
satisfy

    10r(12)+10r(012)+r(23)=(-235,-910,-66,-29).

For another complete finite weight test, define native passive and joining
charges H_w(T)=sum_(i notin T)w_i Z_i(T) and
J_w(T)=sum_(i notin T)w_i[Z_i(T union{i})-Z_i(T)].
If w>=0 satisfies J_w(123)<=0 and H_w({1}),H_w({3})>=0, then
J_w(123)=3w0 forces w0=0; H_w({1})=-2w2-2w3 forces w2=w3=0;
and H_w({3})=-3w1 forces w1=0. Thus no nonzero weight passes even
these necessary inequalities. These failures are comparisons, not inputs
to the equilibrium construction.

The raw condition K<=0 removes the only positive seam and gives exact
terminal Nash; any finite positive K is handled by the adaptive finite
solo0 subdivision. Arbitrarily large values in the18 unqueried coordinates
and arbitrarily low permitted joining rewards do not change any prescribed
value or clock. They can change the reward bound and therefore the uniform
horizon threshold. There is no common threshold over this unbounded family.

The equality Z2(12)=0 is part of the raw class: it makes the pair12 output
coordinate2 zero, allowing the preceding solo2 block to be indifferent.
Changing that entry freely is not covered by this proof. All32 displayed
native coordinates remain fixed. Neither the free
coordinates nor arbitrary row translations amount to independent variation
of all60 rewards. The theorem imposes no nonnegativity of original rewards
or prescribed values at intermediate dates.

All strategy blocks are finite and use independent private randomization.
The only repeated operation is a finite periodic schedule. No continuation
after infinitely many dates is executed. All opponents-only laws absorb,
so no translation of the nonabsorbing payoff is hidden in the normalization.
The theorem establishes neither arbitrary-game existence nor a counterexample.

## 9. Source correspondence and formalization handoff

The semantic target is `quittingUniformEquilibriumPayoffConjecture`
in `UniformEquilibrium/Quitting/Conjecture/Basic.lean`.
The full-cap recursion corresponds to
`quittingContinuationBestResponseValue_rootThenContinuation_eq_max`
in `UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean`.
The existing endpoint
`quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
in `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`
also consumes the all-errors terminal conclusion. Section7 supplies a direct
fixed-target proof, so no independent choice of payoff across accuracies is
required. The raw child criterion compared above is
`PassiveRowInverseCriterion.exists_uniformEquilibriumPayoff_of_raw_nonnegativeInverse_triple`
in `UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/RawPassiveRowInverseCriterion.lean`.
These declarations identify existing interfaces; the signed bridge and its
algebraic parameters are new ordinary mathematics, not attributed to them.

A formalization can proceed through four concrete statements: existence
and uniqueness of the positive quintic root with the stated rational bounds;
the two exact algebraic closure identities and all root comparisons; the
finite44-root repair and finite solo0/solo3 schedules; and the periodic
full-cap identity with debt (0,0,0,max(K,0)delta). All witnesses are defined
from the raw table and accuracy. The final theorem returns W before
quantifying over accuracy, strategy and horizon. No structure field should
assume the desired return, physical root or equilibrium.
