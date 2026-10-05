# Mixed premium traps: negative pair indices and boxed Nash charges

## 1. Raw data and conclusions

Let I be a finite nonempty player set. At each live date of a quitting
game, players independently choose Quit or Continue. The first nonempty
quitting coalition S absorbs with reward r(S)∈ℝ^I, received thereafter.
Live dates and perpetual continuation pay zero. Past actions are public;
profiles and unilateral deviations may be arbitrary behavioral strategies
with independent private randomization. No public correlation is added.

Write s_i=r_i({i}) and M=max_(S≠∅,i)|r_i(S)|. A premium trap A is
nonempty and, for every i∈A, some coalition S⊆A containing i has
r_i(S)>s_i. Singletons are never traps. Traps are union-closed, since
their witnessing coalitions remain available in the union.

For each TWO-player trap A={i,j}, define its joining gaps

    d_i^A=r_i(A)−r_i({j}),
    d_j^A=r_j(A)−r_j({i}).                            (1)

Require d_i^A*d_j^A>0 for the strict theorem. Either common sign
is allowed, independently between pair traps. There may be several
pair traps; the larger-trap inequalities below force them to be disjoint.

For each trap A of size m≥3 and each nonempty proper T⊂A, put

    P_A(T)=sum_(i∈A\T)[r_i(T∪{i})−s_i],
    L_A(T)=sum_(i∈A\T)[r_i(T∪{i})−r_i(T)].

Require positive constants D_A,tau_A,G_A,L_Astar satisfying

    |T|=1:       P_A(T)≤−D_A,   L_A(T)≤−G_A;
    2≤|T|≤m−2:  P_A(T)≤0,      L_A(T)≤0;
    |T|=m−1:    P_A(T)≤tau_A,  L_A(T)≤−L_Astar,       (2)

and

    K_A=m*(D_A/tau_A)^(1/(m−2)),
    C_A=K_A*(G_A+L_Astar*D_A/tau_A)
                              >sum_A s_i+m*M.        (3)

Empty families and empty intermediate cardinality ranges impose no
condition. These are finite raw reward inequalities. No strategy, root,
annotation, potential, degree value, or controller is supplied as an input.
Participant premiums outside the stated inequalities may have either sign.

To verify the disjointness assertion, traps ij and ik with distinct
i,j,k would make ijk a trap, but
P_ijk({i})=[r_j(ij)−s_j]+[r_k(ik)−s_k]>0, contrary to (2).
In Fin4 there can consequently be at most two pair traps.

**Strict analytic theorem.** Under these hypotheses there is a number
M<B<M+2 such that no C¹ function on a neighborhood of [−B,B]^I has
unit absorption drift along every full exact Nash root in that box.

**Uniform-equilibrium theorem.** For I=Fin4 with s≥0, the original
game has a uniform-equilibrium payoff. The pair conditions can be weakened
to d_i^A*d_j^A≥0 for this strategic conclusion; (2)–(3) stay as stated.
More precisely, one vector u is fixed such that, for every epsilon>0,
there are a behavioral profile and a threshold which work for all larger
finite horizons: expected average payoff is within epsilon of u and
every complete unilateral deviation pays at most u_i+epsilon.

The proof selects one low-successor root at each below-floor source.
It does not assert that all exact roots return or that any bounded
strategy architecture is complete. The weak pair boundary is strategic
only, by reward closure. No opposite-strict-sign pair claim is made.

## 2. Exact roots and signed elementary bounds

For independent hazards q∈[0,1]^I, let mu_q be the product coalition
law, c(q)=mu_q(∅), and a(q)=1−c(q). At annotation v, the successor is

    w(v,q)=c(q)v+sum_(S≠∅)mu_q(S)r(S).               (4)

The actual forced action endpoints are

    Q_i(q)=sum_(T⊆I\{i})mu_(−i)(T)r_i(T∪{i}),
    C_i(v,q)=mu_(−i)(∅)v_i
                 +sum_(∅≠T⊆I\{i})mu_(−i)(T)r_i(T).

An exact root is Nash in the finite two-action game with continuation
v after all Continue. Equivalently, w_i=q_i Q_i+(1−q_i)C_i is at
least both Q_i and C_i. An active hazard gives w_i=Q_i≥C_i; an
interior hazard gives equality of both endpoints. Finite-game Nash
existence supplies an exact root at every v. The annotation need not
be a payoff realized by a strategy.

For any B>M and |v_i|≤B, the successor stays boxed, and

    norm(w−v)_infinity≤(M+B)a(q),
    Q_i≥s_i−2M*a_(−i)(q)≥s_i−2M*a(q).              (5)

The second inequality uses the singleton outcome on opponent
nonabsorption; any other outcome changes its reward by at most 2M.
No participant-premium sign assumption is used.

A full exact-root potential with unit absorption drift means

    H(w(v,q))+a(q)≤H(v)                             (6)

at every boxed annotation and every exact root, including inactive
players, simultaneous quitting and sure hazards.

If a nonempty active support A is not a trap, some k∈A has
r_k(S)≤s_k for every S⊆A containing k. All positive-probability
opponent coalitions lie inside A. Hence Q_k≤s_k and support
optimality gives w_k≤s_k. This signed upper bound does not imply
any other coordinate's floor.

## 3. Larger supports pay a boxed Nash charge

There are finitely many traps. The strict gaps in (3) allow one common
M<B<M+2 with

    C_A>sum_A s_i+|A|B                              (7)

for every trap of size at least three. If none exist, any such B works.

We prove that an absorbing exact root with successor w>s in every
coordinate must have support a pair trap. A nontrap support is already
excluded by Section 2. Suppose its support A is a trap of size m≥3.
Every active Q_i=w_i>s_i. The exact aggregate-gap identity is

    sum_(i∈A)(1−q_i)(Q_i−C_i)
       =c(q)*sum_A(s_i−v_i)
          +sum_(∅≠T⊊A)mu_q(T)L_A(T).               (8)

Multiplying the ith opponent law by 1−q_i gives the full product
law on coalitions omitting i. Grouping the empty term and then each
nonempty proper T proves (8) on the entire cube, without division.

If some but not all active hazards are sure, choose a nonsure active i.
The proper coalition A\{i} has positive probability and a strictly
negative L coefficient. Every other L coefficient is nonpositive and
c(q)=0. This contradicts the nonnegative left side of (8). If all
hazards are sure, (2) at A\{i} instead says r_i(A)<r_i(A\{i}),
a profitable withdrawal. Thus all active hazards are interior.

Put z_i=q_i/(1−q_i)>0, U=sum_A z_i, and
E=sum_(i∈A)product_(j∈A\{i})z_j. Divide each Q_i−s_i>0 by its
positive opponent Continue probability, and sum. The result is

    0<sum_(∅≠T⊊A)P_A(T)product_(j∈T)z_j
                                    ≤−D_A U+tau_A E.

Consequently D_A U<tau_A E. We also have

    E≤U^(m−1)/m^(m−2).                              (9)

For a proof, maximize E over nonnegative coordinates with fixed U>0.
The maximum is positive and has at least m−1 positive coordinates.
Holding all but two coordinates u,v fixed writes E as
uv*e_(m−3)(rest)+(u+v)*e_(m−2)(rest). At such a maximum the first
coefficient is positive, including e_0=1 for m=3. Averaging unequal
u,v strictly raises E. All coordinates must therefore equal U/m,
which gives (9); the zero-sum case is immediate.

It follows that U>K_A. Interior support indifference makes the left
side of (8) zero. Dividing by c(q)>0 and using (2) gives

    sum_A(s_i−v_i)≥G_A U+L_Astar E
        >(G_A+L_Astar D_A/tau_A)U>C_A.

This contradicts the boxed upper bound sum_A s_i+mB from (7).
Thus every all-high absorbing root has support a two-player trap.
No condition on outside players' joining rewards was used here.

## 4. One explicit generic source set for all pair traps

Fix a pair trap A={i,j}, abbreviate its gaps by d_i,d_j, and set
α_i=v_i−s_i+d_i, α_j=v_j−s_j+d_j. On its active pair face the
actual endpoint gaps are

    g_i=s_i−v_i+α_i q_j,
    g_j=s_j−v_j+α_j q_i.                            (10)

An interior pair root therefore has the unique possible coordinates

    p_i=(v_j−s_j)/α_j,
    p_j=(v_i−s_i)/α_i,
    p_k=0 for k∉A.                                  (11)

A zero denominator cannot solve an interior active equation because
the corresponding joining gap is nonzero.

For each outsider k and each nonempty T⊆A, put
Delta_k(T)=r_k(T∪{k})−r_k(T). Define the polynomial

    N_(A,k)(v)=d_i d_j(s_k−v_k)
        +d_i(v_j−s_j)Delta_k({i})
        +d_j(v_i−s_i)Delta_k({j})
        +(v_i−s_i)(v_j−s_j)Delta_k(A).              (12)

Whenever the denominators in (11) are nonzero, substitution in the
FULL outsider equation gives

    Q_k(p)−C_k(v,p)=N_(A,k)(v)/(α_i α_j).            (13)

Indeed the four opponent coalition probabilities have numerators
d_i d_j, d_i(v_j−s_j), d_j(v_i−s_i), and
(v_i−s_i)(v_j−s_j) over that common denominator. The simultaneous
joining reward r_k(A∪{k}) is included in the last term.

Since k∉A, the coefficient of v_k in N is the nonzero constant
−d_i d_j. Thus no polynomial N is identically zero. Exclude every
N=0 set and every α_i=0 hyperplane for every pair trap, simultaneously.
Their complement G is open and dense in source space. To see density,
a polynomial vanishing on an open box is zero by induction on its
variables; a finite union of zero sets is the zero set of the nonzero
product polynomial. The empty family gives all source space.

Only annotations are perturbed, never the reward table. This single
generic set is defined before any root is chosen, and its annotations
need not have strategic realizations.

## 5. Finite negative-index root count

If a pure pair is exact at any annotation, it is exact at every one:
every player faces at least one sure opponent quitter. At v=r(A) its
successor equals its source and a=1, directly contradicting (6). It
also gives an actual pure equilibrium in the original quitting game,
since any unilateral replacement still faces a sure quitter at the
first date. We may exclude this alternative in the remaining proof.

Fix v∈G∩[−B,B]^I below at least one singleton. All Continue is not
Nash, so every exact root absorbs. Suppose every root were bad, meaning
w>s. Section 3 leaves only pair traps. One sure and one interior pair
hazard is impossible, because the latter player's gap against the sure
opponent equals its nonzero joining gap. Two sure hazards are the case
already excluded. Thus each root is an interior candidate (11).

There are finitely many roots, at most one per pair trap. Distinct
supports give distinct roots. Finite-game Nash existence ensures at
least one root; if there are no pair traps the contradiction is already
immediate. Otherwise we count the full ambient indices of these roots.

Extend the full polynomial gaps g=Q−C to real hazards and define

    F_v(q)_k=min(1,max(0,q_k+g_k(q))).                (14)

This is a continuous map from ℝ^I into [0,1]^I. Its fixed points
are exactly all full exact Nash roots: the clipping conditions give
g_k≤0 at q_k=0, g_k≥0 at q_k=1, and g_k=0 in the interior.

At a candidate (11), every inactive gap is nonzero by (13) and
genericity; Nash makes it strictly negative. Its outside clipped rows
are therefore locally constant zero. The two core rows are locally
unclipped. Interiority implies that v_i−s_i and d_i have the same
strict sign, and likewise for j: 0<u/(u+d)<1 forces u,d to have
the same sign. Hence α_i α_j>0. Ordering the pair coordinates first,
the derivative of identity minus F_v has the full block form

    [[0,−α_i,*], [−α_j,0,*], [0,0,Id]],             (15)

with determinant −α_i α_j<0. The starred derivatives retain every
larger-coalition interaction; no restricted-face Jacobian has replaced
the full one.

Here are the degree details. On Ω=(−1,2)^I the homotopy from F_v
to the constant cube center stays inside [0,1]^I. Identity minus
that homotopy is nonzero on the boundary. Its total degree is +1.
At each root p, (15) is invertible. For its derivative J there is
mu>0 with norm(Ju)≥mu norm(u). On a sufficiently small sphere,
the remainder in p+u−F_v(p+u)−Ju is at most mu norm(u)/2.
Straight-line comparison to Ju is therefore nonzero on that sphere,
and the root's local degree is sign det J=−1.

The finitely many roots have disjoint such neighborhoods. Excision and
finite additivity identify the total degree with the sum of these local
degrees, namely −K for K≥1 roots, contradicting +1. All roots lie
inside Ω even when their outsider coordinates are zero, so no half-index
arises. This proves existence of a nonbad root at every generic source
under consideration. It does not assert return by every root.

## 6. Restoration of every source and strict analytic exclusion

Let v be ANY boxed source with v_h<s_h for some h. Approximate it
by generic sources v_n from the box interior, still with v_n,h<s_h.
Choose the low-successor roots just produced. Compactness of the unit
cube gives a convergent subsequence of hazards. The polynomial endpoint
inequalities are closed, so its limit q is exact Nash at v. The union
of the singleton sublevels is closed, so the limit successor also has
a low coordinate. Its absorption is positive because all Continue is
not Nash at v. We have proved selected return at EVERY original
below-floor source, including box-boundary sources, without a continuous
root selector.

Suppose H is C¹ near the box and satisfies (6). Minimize it on the
compact nonempty set

    D={v∈[−B,B]^I: some v_i≤s_i}.

If a minimum x has a strict singleton deficit, selected return gives
an absorbing root with successor in the SAME D, contradicting minimality
and drift. Thus x≥s and J={i:x_i=s_i} is nonempty.

### Signed singleton-face inequality

For any x≥s with x_j=s_j, a full potential satisfies

    grad H(x)·(x−r({j}))≥1.                         (16)

Set b_j=0; set b_i=0 at nonbinding coordinates, and otherwise set
b_i=max(0,r_i({i,j})−r_i({j})). At small t>0 use the source
x+t b/(1−t) and the sole hazard q_j=t. Its positive corrections
are only at singleton-binding coordinates strictly below B. Player j
is indifferent, while each inactive Continue-minus-Quit gap is

    (1−t)(x_i−s_i)+t[b_i+r_i({j})−r_i({i,j})]≥0

for all sufficiently small t. This includes upper faces, whose corrections
are zero. The root is exact, absorbs with probability t, and has successor
x+t(b+r({j})−x). Apply (6), divide by t and differentiate. The b
terms cancel, giving (16).

### Same-domain derivative contradiction

If J had only j, the j displacement in (16) would vanish. All other
interior partial derivatives would be zero, and upper-face partials
nonpositive because downward variations stay in D. Their displacements
B−r_i({j}) are positive. Thus the left side of (16) would be
nonpositive, a contradiction. Therefore |J|≥2. Increasing a binding
coordinate while keeping another binding proves grad_k H(x)≥0 for
every k∈J.

Fix k∈J and put v=x−epsilon e_k for small epsilon>0. Its selected
root has absorption a>0 and successor w∈D. Bounds (5) and Nash yield

    s_k−2Ma≤Q_k≤w_k≤s_k−epsilon+(M+B)a,
    epsilon≤(3M+B)a.

Minimality and drift give

    H(x−epsilon e_k)−H(x)≥a≥epsilon/(3M+B).

After division by epsilon, its left side tends to −grad_k H(x)≤0,
a contradiction. No protected coordinate, individual successor floor,
or convergence of roots near this minimum is needed. The selected
successors return to the identical domain D.

## 7. Original Fin4 UE and weak pair products

For Fin4 with nonnegative own singletons, every player is normal. If
some singleton is positive, absence of a uniform-equilibrium payoff
produces an actual rational polynomial potential for the full robust
relation on the box M+2. Restriction to exact roots and then to B
retains the same game and same polynomial. Section 6 contradicts its
unit drift. If all own singletons are zero, all Never is directly
an exact equilibrium at every horizon: a unilateral quitter earns zero.
The named source declarations for this semantic chain are in Section 9.

For the weak pair condition, perturb only passive singleton entries
r_i({j}) associated with zero pair gaps. If exactly one gap is zero,
give it the same strict sign as its partner; if both are zero, make
both positive. Ordered passive singleton entries affect distinct pair
comparisons, so all these changes can be simultaneous with sup-norm
at most delta. They change no participant reward or own singleton.
The COMPLETE trap list and every P coefficient are unchanged.

Only singleton-layer L coefficients of a larger trap can change, by
at most (m−1)delta. Replace G_A by G_A−(m−1)delta>0, retaining
the other constants. All higher-layer L inequalities remain unchanged.
The new reward bound is at most M+delta, and its charge is
C_A−K_A(m−1)delta. Thus the strict larger-trap margin persists if

    delta<G_A/(m−1),
    delta<[C_A−sum_A s_i−mM]/[K_A(m−1)+m]             (17)

for every larger trap. There are finitely many positive bounds, so
arbitrarily small perturbations satisfy all of them and all strict pair
conditions. This checks every larger trap, not just the selected pair.

The nearby games therefore have UE payoffs. Reward closure gives one
fixed target for the original game. Explicitly, take nearby targets in
one common compact reward box and pass to a convergent subsequence with
limit u. A uniform reward change of delta changes every prescribed or
deviating expected finite-horizon average by at most delta. For each
accuracy choose one nearby target close to u, then its profile and horizon
threshold. They work for the original game at all larger horizons. The
target u is chosen before accuracy. This proves only the weak strategic
boundary, not a weak analytic statement or opposite-sign pair coverage.

## 8. An exact mixed-trap table beyond the separate criteria

The following complete table has s=(1,0,0,0) and M=11:

| S | r(S) |
|---|---|
| 0 | (1,−1,−1,−1) |
| 1 | (2,0,2,−1) |
| 2 | (2,−1,0,2) |
| 3 | (0,2,−1,0) |
| 01 | (−9,−10,10,10) |
| 02 | (−9,10,−10,10) |
| 03 | (4,−11,10,3) |
| 12 | (−10,3,3,10) |
| 13 | (11,−10,10,−10) |
| 23 | (11,10,−10,−10) |
| 012 | (−9,−10,−10,10) |
| 013 | (−9,−10,10,−10) |
| 023 | (−9,10,−10,−10) |
| 123 | (11,−10,−10,−10) |
| 0123 | (11/10,1/10,1/10,1/10) |

### All raw tests

The only traps are 03,12,0123. The pair joining-gap vectors are
(4,4) and (4,1). Their participant premiums are three. All other
proper nonsingleton participant premiums are −10, while every grand
premium is 1/10. Thus no triple is a trap, and the union of the two
disjoint pair traps is the greatest core I.

For the larger trap I, the P coefficients by coalition cardinality
are −17 at each singleton, −20 at every pair, and 1/10 at every
triple. Its L singleton coefficients in order0,1,2,3 are
−14,−19,−19,−17. The L pair values are −19 at03,12 and −40
at the other four pairs; all triple values are −99/10. Choose

    D_I=10, tau_I=1, G_I=10, L_Istar=9.

Every raw coefficient bound has strict slack, and

    C_I=400 sqrt(10)>45=sum_i s_i+4M.                (18)

The two pair products are strictly positive too. These are robust
finite inequalities, not a strategically supplied witness. The displayed
point has three zero own singletons; a small increase in those three
entries retains every strict inequality and trap sign and gives positive
own singletons. Thus the raw region has nontrivial relative interior,
and nearby tables with all own singletons positive also satisfy the
strategic theorem. No general openness principle for UE is used.

### No pure exit

At singletons0,1,2,3 the profitable joining players3,2,1,0 gain
4,1,4,4 respectively. At cross pairs01,02,13,23, the withdrawing
players0,0,1,2 gain11,11,12,9. At03 player1 joins for gain1;
at12 player0 joins for gain1. At triples012,013,023,123, players
1,0,0,1 withdraw for gain20. Every grand participant gains99/10
by withdrawal. Each withdrawal retains another quitter. All Never
fails because player0 has positive singleton payoff.

### Fourteen exact full-behavior child witnesses

For each proper nonempty child, the following sure coalition quits at
the first date; all other child players choose Never. After nonabsorption
the prescribed future is Never. The last column is the immediate gain
of the listed omitted player in the actual quiet lift.

| Child | Sure coalition | Omitted player | Gain |
|---|---|---|---|
| 0 | 0 | 3 | 4 |
| 1 | 1 | 2 | 1 |
| 2 | 2 | 1 | 4 |
| 3 | 3 | 0 | 4 |
| 01 | 0 | 3 | 4 |
| 02 | 0 | 3 | 4 |
| 03 | 03 | 1 | 1 |
| 12 | 12 | 0 | 1 |
| 13 | 1 | 2 | 1 |
| 23 | 2 | 1 | 4 |
| 012 | 0 | 3 | 4 |
| 013 | 1 | 2 | 1 |
| 023 | 2 | 1 | 4 |
| 123 | 3 | 0 | 4 |

The only profitable join against a singleton is by its matched partner
in 03 or12, and that partner is omitted in every singleton row above.
The two sure pairs are internally Nash because both members strictly
prefer joining. A sole owner who prevents absorption faces Never
opponents and cannot improve on its nonnegative singleton by delaying.
These observations cover every complete behavioral deviation, not just
one-stage actions. Each child profile is exact terminal Nash and has
zero joint Never probability.

Hence, for EACH proper child, SOME omitted player defeats any proposed
universal bound by a fixed finite nonnegative weighted sum of child
deviation debts plus a fixed multiple of joint Never. The right side
vanishes on the displayed profile and the outside gain is positive.
This excludes the universal-profile bound, not every possible selected
quiet chronology.

### Bounded matrix and premium comparisons

The singleton-difference matrix, with receiver rows and owner columns,
is

    Gamma=[[0,1,1,−1],[−1,0,−1,2],
           [−1,2,0,−1],[−1,−1,2,0]].              (19)

Its child123 block has determinant7, inverse
[[2,4,1],[1,2,4],[4,1,2]]/7, and sends the all-one vector to
itself. A positive homogeneous pivot h forces all child coordinates
positive and equal h; the pivot residual then equals h>0. With zero
pivot, the cyclic child inequalities either propagate a zero to all
coordinates or make all coordinates positive, where invertibility forces
zero. Thus Gamma is R₀. At offset (1,−1,−1,−1), the child equals
(1+h)1 and the pivot residual is 2+h. The unique root is (0,1,1,1),
with inactive residual2 and active determinant7. Its degree is +1,
not a degree-not-one exit.

Only child123 has a nonnegative inverse, and its passive inverse row
is (−1/7,5/7,3/7). For child012 the first diagonal inverse entry
is −2; for child013 it is −2/3; for child023 its first-row second
entry is −2/3. These exact entries exclude the raw three-child
nonnegative-inverse/passive-weight criterion on every triple. At
q=(t,0,0,0), the candidate block0|123 has full response coordinates
t−10t²,t−10t²,t+3t², so it is not a literal response quotient.
No exhaustive classification of other response partitions is needed here.

A criterion requiring the greatest premium core to be a pair cannot
apply: the greatest core is full. A criterion forbidding pair traps
cannot apply either. This is genuinely a mixed configuration, not merely
a table in the union of those two classes.

Every player has a negative participant premium, so there is no protected
coordinate set with globally nonnegative premiums. Summing any putative
nonnegative weighted forced-Quit-floor inequalities over the four sure-
singleton product laws gives

    −17*sum_i lambda_i≥0.

Thus every nonnegative weight must vanish; even weights on all players
cannot produce a nonzero such global floor. At the sure law on03,
both active premiums equal3. Product-low and normalized nonpositive
supportwise participant-premium balance therefore fail.

The usual cyclic-child two-joint raw template with sole positive-singleton
pivot0 and joint03 requires r_2(03)≤0, whereas here r_2(03)=10.
Its other pivot pairs01,02 have negative participant premiums. This is
a bounded comparison with that raw template, not a proof that every
other periodic or stationary architecture fails. The example has a UE
by the theorem, not a uniform-equilibrium obstruction.

## 9. Tracked dependencies and implementation shape

The exact-root, analytic and semantic inputs are the following named
declarations under their current imports:

- `exists_isZeroQuittingRootNash` in
  `UniformEquilibrium/Quitting/Root/NashExistence.lean` gives a finite
  exact root at every annotation.
- `abs_quittingRootSuccessorPayoff_sub_tail_le_reward_add_source_mul_absorptionMass`
  in `UniformEquilibrium/Quitting/Root/BoundedSuccessorDisplacement.lean`
  gives the displacement estimate in (5).
- `IsQuittingFullExactRootPotential.singletonFace_drift` in
  `UniformEquilibrium/Quitting/Projective/FullExactRootPotentialFaceDrift.lean`
  is the signed probe conclusion (16), also proved directly here.
- `ambientDegree_homotopy` and
  `ambientDegree_affineRootField_eq_sign_det` in
  `MathUE/Topology/AmbientDegreeHomotopyNormalization.lean`, together with
  `ambientDegree_excision` and `ambientDegree_additive` in
  `MathUE/Topology/AmbientDegreeProperties.lean`, supply the full ambient
  degree comparison and finite local sum. The nonlinear local comparison
  and explicit source polynomials are proved in Sections 4–5.
- `isQuittingNormalPlayer_of_singleton_nonneg` in
  `UniformEquilibrium/Quitting/Classification/AbnormalPlayers.lean`
  gives normality without a global participant-premium sign condition.
- `quittingGame_not_exists_uniformEquilibriumPayoff_iff_noSureRoot_and_rationalPotential`
  in `UniformEquilibrium/Quitting/Projective/PolynomialForwardCertificateCharacterization.lean`
  produces the actual Fin4 polynomial obstruction at reward bound M.
- `isQuittingFullExactRootPotential_of_robustPotential` and
  `IsQuittingFullExactRootPotential.mono_box` in
  `UniformEquilibrium/Quitting/Projective/ExactRootPotentialRestriction.lean`
  restrict the same polynomial to the required exact source box.
- `exists_uniformEquilibriumPayoff_of_arbitrarily_close_reward_tables`
  in `UniformEquilibrium/Quitting/Terminal/TerminalExploitabilityRewardRobustness.lean`
  gives the weak strategic boundary with fixed target.

The matrix comparisons use
`exists_finset_r0Degree_eq_sum_sign_det` in
`MathUE/LinearProgramming/R0DegreeSum.lean`,
`exists_uniformEquilibriumPayoff_of_r0Degree_ne_one` in
`UniformEquilibrium/Quitting/Classification/LCP/SingletonDegreeCriterion.lean`,
and `PassiveRowInverseCriterion.exists_uniformEquilibriumPayoff_of_raw_nonnegativeInverse_triple`
in `UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/RawPassiveRowInverseCriterion.lean`.
The exact universal quiet-debt quantifier is that of
`withdrawalFutureJoin_quietLift_outsideDebt_le_add_neverExcess` in
`UniformEquilibrium/Quitting/Classification/QuietExtension/WithdrawalFutureJoinDebt.lean`.
Product-low and the supportwise certificate are defined in
`UniformEquilibrium/Quitting/Classification/ProductLowQuittingPremium.lean`
and `UniformEquilibrium/Quitting/Classification/SupportwiseQuittingPremiumBalanceAt.lean`.

The raw predicate to formalize contains only trap conditions, joining
gaps, positive coefficient bounds and (2)–(3). Its producer first excludes
all-high larger-support roots on one common box; explicit tie polynomials
and finite ambient index counting then produce low-successor roots at
generic below-floor sources. Compactness restores every such source.
The same-domain minimum and existing polynomial consumer yield Fin4 UE;
(17) and reward closure handle zero pair products. For Fin4, the larger-
trap powers are only the triple linear and quadruple square-root cases.
No potential, controller, favorable root selection or strategic target
belongs among the supplied fields. This is ordinary mathematics, not a
claim that the new theorem is already implemented or Lean checked.
