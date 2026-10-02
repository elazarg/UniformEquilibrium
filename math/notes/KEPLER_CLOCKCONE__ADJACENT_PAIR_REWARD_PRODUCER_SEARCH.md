# KEPLER_CLOCKCONE — adjacent-pair reward producer search

Author: `KEPLER_CLOCKCONE`

Status: **sharp three-clock triangle and four-clock star laws are proved; no
reward-table producer was found.**  Three exact rational inverse designs were falsified by full
behavioral terminal Nash profiles.  The strongest four-active candidate has no
pure sure-exit set and breaks all-`Never`, but the stationary half-hazard
profile is an exact terminal Nash with every player's value and both root
action values equal to one.  Sections 7--11 prove the stronger law, audit its
equality and arbitrary-clock boundary, and state its exact `K_4` triangle
consumer.  Sections 12--15 prove the genuine four-clock star law and give its
stronger six-edge consumer.  This is ordinary mathematics, not Lean-checked
and not exported.

This note continues the producer search requested after the separately
reviewed theorem in
`KEPLER_CLOCKCONE__OVERLAPPING_FIRST_QUITTER_LAW.md`.  It does not change that
frozen note, claim a counterexample, or enter the export queue.

## 1. Exact producer target

Let `A={0,1}` and `B={0,2}`.  For a four-player behavioral profile `sigma`,
write `a,b` for the probabilities that `A,B` are respectively the exact finite
first-quitter coalition and write

```text
E(sigma)=max_i (B_i(sigma)-U_i(sigma))
```

for terminal exploitability against complete unilateral behavioral
replacement.  The reviewed clock consumer would close a negative example if
one rational reward table supplied constants

```text
a >= alpha_A-L_A*E,
b >= alpha_B-L_B*E,
sqrt(alpha_A)+sqrt(alpha_B)>1.                     (1.1)
```

Pure-time extremality makes deterministic dates and `Never` a complete test
class, but it does not supply the lower bounds.

The search below starts with membership-toggle duals because exact coalition
indicators convert localized atoms into linear payoff accounts.  Every
candidate was checked against pure coalitions, all-`Never`, and stationary
behavior before any claim about (1.1).

## 2. Weighted adjacent square always has a mixed escape

The smallest design uses player `0` as a sure base quitter and player `3` as
an inert continuer.  At date zero, players `1,2` choose membership in the
absorbing coalition.  The four possible coalitions are

```text
D={0}, A={0,1}, B={0,2}, C={0,1,2}.
```

For positive rational `u,v,w,z`, give player `1` rewards

```text
r_1(A)=u, r_1(B)=v, r_1(D)=r_1(C)=0,
```

and player `2` rewards

```text
r_2(D)=w, r_2(C)=z, r_2(A)=r_2(B)=0.
```

Set the coordinates of players `0,3` to zero.  Player `1` wants the two
off-diagonal corners while player `2` wants the diagonal corners.  Their
unique fully mixed membership equilibrium has

```text
x=P(1 quits at date 0)=w/(w+z),
y=P(2 quits at date 0)=u/(u+v).
```

Because player `0` quits surely, a time after zero is exactly the Continue
membership action and there is no untested later deviation.  Thus this is a
full terminal Nash profile, not merely a one-stage equilibrium.  Its target
masses are

```text
a = w*v/((w+z)(u+v)),
b = z*u/((w+z)(u+v)).                              (2.1)
```

The desired square-root violation is impossible already in this exact dual:

```text
sqrt(a)+sqrt(b)
 = (sqrt(w*v)+sqrt(z*u))/sqrt((w+z)(u+v))
 <= 1                                               (2.2)
```

by Cauchy--Schwarz.  Equality holds exactly when `w*u=z*v`, which is the
same-date equality condition for the overlapping clock theorem.

Thus arbitrary rational weighting of the shortest adjacent toggle square
does not force a forbidden lower rectangle.  Its mixed Nash law automatically
moves onto or below the sharp clock boundary.

## 3. An adjacent compensated table with no pure or `Never` sink

I next adapted the strong deletion ledger to overlapping targets and then
added the shortest join premiums that break the two target-pair sinks.  The
following complete rational table is conveniently specified by rules.  Put
`C={0,1,2}`.  For every nonempty coalition `S`, define

```text
r_i(S)=1                 if i is not in S,
r_i({i})=1               for i=0,1,2,
r_3({3})=-2,
r_i(A)=2                 for i in A,
r_i(B)=2                 for i in B,
r_1(C)=r_2(C)=2,
r_i(S)=0                 in every remaining case with i in S.  (3.1)
```

The two triple rewards make outsider `2` want to join pure `A` and outsider
`1` want to join pure `B`.  The positive solos of players `0,1,2` break
all-`Never`.

An exact toggle check finds a profitable player at every nonempty pure
coalition.  One possible list of profitable labels is

```text
0:1, 1:0, 2:0, 3:3, 01:2, 02:1, 03:0, 12:1,
13:1, 23:2, 012:0, 013:0, 023:0, 123:1, 0123:0.
```

Every displayed gain is at least one.  Hence (3.1) has no pure sure-exit set,
and all-`Never` is not terminal Nash.

It nevertheless has an exact stationary terminal Nash profile.  Take hazards

```text
(h_0,h_1,h_2,h_3)=(2/5,2/3,2/3,0).                (3.2)
```

The joint continuation probability is `1/15`, so absorption is almost sure.
Direct exact evaluation gives

```text
              U_i   Quit-now value   Continue value
i=0             1          1                1
i=1             1          1                1
i=2             1          1                1
i=3             1        -2/15              1.
```

Players `0,1,2` are indifferent and may use the stated interior hazards;
player `3` optimally uses hazard zero.  Against stationary opponents, a pure
quit time has value

```text
R_i*(1+z_i+...+z_i^(t-1)) + z_i^t*Q_i,
```

where `z_i` is opponent joint continuation, `Q_i` is Quit-now value, and
`R_i` is the one-row payoff contribution from nonempty opponent actions.
The equality `Q_i=Continue_i=U_i` makes every time optimal for the first three
players; `Q_3<Continue_3` makes `Never` optimal for player `3`.  Therefore
(3.2) is Nash against every deterministic finite date and `Never`, hence
against every behavioral deviation.

The exact target pair masses are

```text
a=b=2/21.                                           (3.3)
```

So (3.1) decisively fails the affine-floor target (1.1), despite passing both
obvious pure-profile screens.

## 4. Weakening the premium selects one target edge

There is a second exact escape when the target premium is reduced.  In (3.1),
replace the target value `2` by `3/2`, replace each solo of players `0,1,2`
by `1/2,1,1` respectively, and retain the triple values `2`.

The symmetric stationary interior root disappears, but two asymmetric exact
stationary Nash profiles appear:

```text
(1/2,1/3,1,0),
(1/2,1,1/3,0).                                     (4.1)
```

At the first profile the exact action data are

```text
              U_i   Quit-now value   Continue value
i=0             1          1                1
i=1             1          1                1
i=2           7/6        7/6              19/18
i=3             1          0                1.
```

Thus players `0,1` mix, player `2` correctly quits surely, and player `3`
continues surely.  The pair masses are `(a,b)=(0,1/3)`; the other profile is
the symmetric `(1/3,0)` escape.  This is the exact pair-balance failure: after
the symmetric law is removed, the response system chooses one target rather
than maintaining two positive floors.

For the four-parameter passive family with target value `k`, triple value
`j`, solos `s_0,s_1=s_2`, and player `3` as above, the signs of the three
stationary root advantages reduce, up to a common positive denominator, to

```text
F_0 = (-2k+s_0)h_1h_2 +(k-s_0)(h_1+h_2)+s_0-1,

F_1 = (j-k+s_1)h_0h_2 +(k-s_1)h_0-s_1h_2+s_1-1,
F_2 = (j-k+s_1)h_0h_1 +(k-s_1)h_0-s_1h_1+s_1-1.   (4.2)
```

A symbolic support-enumeration experiment using exact rational equations over
the grid

```text
k,j in {6/5,4/3,3/2,2,3},
s_0,s_1 in {1/4,1/2,1,2}
```

returned stationary escapes for `370` of the `400` parameter tuples.  It
returned no stationary solution for the remaining `30`; this is a finite
experiment, not a completeness theorem for degenerate symbolic branches.  In
any event player `3` is globally passive throughout this family, so those
tuples reduce to a three-player quitting game and cannot serve as a genuinely
`Fin 4` negative producer.  A search for a fully interior symmetric period-two
root for `(k,j,s_0,s_1)=(3/2,2,1/4,1/4)` found none; this too is only a bounded
experiment, not a no-go theorem.

## 5. Activating the fourth player recreates a rational stationary escape

To remove the passive-player objection, modify (3.1) as follows:

```text
r_3({3})=8,
r_1(C)=r_2(C)=5,
r_0({0,3})=3,                                      (5.1)
```

and leave all other entries as specified by (3.1), except that no `-2` solo
remains.  This table is fully rational and all four players are strategically
active.

It still has no pure sure-exit set.  A profitable-label certificate is

```text
0:1, 1:0, 2:0, 3:0, 01:2, 02:1, 03:3, 12:1,
13:1, 23:2, 012:0, 013:0, 023:0, 123:1, 0123:0.
```

Again every listed pure toggle gain is positive, and every solo reward is
positive, so all-`Never` is also excluded.

Nevertheless the stationary profile

```text
h_0=h_1=h_2=h_3=1/2                               (5.2)
```

is an exact terminal Nash profile.  The root coalition is uniform over all
fifteen nonempty coalitions.  Exact summation gives, for every player,

```text
U_i=Quit-now value=Continue value=1.               (5.3)
```

As in Section 3, time homogeneity then makes every deterministic quit date and
`Never` worth one.  The complete behavioral deviation cap is one.  In
particular

```text
a=b=1/15.                                          (5.4)
```

The numbers in (5.1) were not found by floating fitting.  At the half-hazard
row, if the target value is `k`, common-player solo is `s_0`, exclusive-player
solo is `s_1`, triple value is `j`, player-`3` solo is `s_3`, and
`r_0({0,3})=d`, the four stationary advantages are proportional to

```text
d+2k+s_0-8,
j+k+s_1-8,
j+k+s_1-8,
s_3-8.                                             (5.5)
```

Choosing `(k,s_0,s_1,j,s_3,d)=(2,1,1,5,8,3)` makes all four vanish exactly.
This gives a reusable falsification warning: adding a fourth-player clock and
more join premiums can remove every pure and `Never` sink while simultaneously
calibrating a fully mixed stationary sink.

## 6. Why none of these tables supplies affine floors

At an exact terminal Nash profile `E=0`.  Therefore any universal lower bound
`a>=alpha_A-L_AE`, `b>=alpha_B-L_BE` must satisfy
`alpha_A<=a`, `alpha_B<=b` at that profile.  Sections 2--5 give respectively:

- a weighted-square equilibrium satisfying the sharp square-root law by
  Cauchy--Schwarz;
- a symmetric escape with `(a,b)=(2/21,2/21)`;
- asymmetric escapes `(0,1/3)` and `(1/3,0)`; and
- a four-active escape with `(a,b)=(1/15,1/15)`.

Thus none can have `sqrt(alpha_A)+sqrt(alpha_B)>1`.  No exact rational reward
table forcing the forbidden affine lower rectangle was found.

The failures separate the remaining obligations more sharply than pure
screening alone:

1. A candidate must break both target-pair sure exits and all-`Never`.
2. It must also exclude membership-mixed stationary roots, including roots
   created by the very premiums used in step 1.
3. It must keep the fourth player genuinely active; otherwise three-player
   existence is an immediate conceptual escape.
4. It must quantitatively prevent one-target selection such as (4.1), not
   merely force a large total `a+b` account.

These are producer requirements.  The overlapping clock theorem remains a
complete consumer once they are met, and still bypasses source chronology.

## 7. Sharp three-clock triangle law

Let

```text
a=P(T0=T1<T2, finite),
b=P(T0=T2<T1, finite),
c=P(T1=T2<T0, finite).
```

The genuinely stronger inequality is

```text
sqrt(a)+sqrt(b)+sqrt(c) <= sqrt(3/2).              (7.1)
```

The constant is sharp.  At date zero take hazards
`(1/2,1/2,2/3)` and, conditional on joint continuation, force
`T0=T1<T2` surely.  Then

```text
a=b=c=1/6,
sqrt(a)+sqrt(b)+sqrt(c)=sqrt(3/2).                 (7.2)
```

Write

```text
K=sqrt(3/2), A=2-K, B=K-1.
```

Thus `A+2B=K` and `A+B=1`.  If the future square-root coordinates
are `(u,v,w)`, the propagated objective at hazards `(x,q,r)` is

```text
G(u,v,w)
 =sqrt(x*q*(1-r)+d*u^2)
  +sqrt(x*r*(1-q)+d*v^2)
  +sqrt((1-x)*q*r+d*w^2),
d=(1-x)*(1-q)*(1-r).                              (7.3)
```

This is a convex function of `(u,v,w)`.  The reviewed overlapping-pair law
gives

```text
u+v<=1, u+w<=1, v+w<=1.                           (7.4)
```

The induction hypothesis also gives `u+v+w<=K`.  The resulting polytope has
exactly the seven vertices

```text
0; e_1,e_2,e_3; and the three permutations of (A,B,B).  (7.5)
```

At a unit vertex the one-step estimate is exact.  For example, at `e_1`, put
`X=1-x`, `Q=1-q`, `R=1-r` and `D=x*q+X*Q`.  Then

```text
sqrt(x*q*(1-r)+(1-x)(1-q)(1-r))
 +sqrt(x*r*(1-q))
 +sqrt((1-x)*q*r)
 =sqrt(R*D)+sqrt(r)*(sqrt(x*Q)+sqrt(X*q))
 <=sqrt(D+(sqrt(x*Q)+sqrt(X*q))^2)
 =sqrt(1+2*sqrt(x*X*q*Q))
 <=K.                                              (7.6)
```

Equality in (7.6) is unique:

```text
(x,q,r)=(1/2,1/2,2/3).                            (7.7)
```

The other unit vertices follow by permutation, and a unit vertex dominates
the zero-future vertex coordinatewise.  It remains to prove the three
exceptional vertices.  The next elementary product-overlap lemma does exactly
that.

## 8. Four-chord product-overlap lemma

### Lemma 8.1

Let `d_0,d_1,d_2,d_3>=0` and `L>0`.  If

```text
d_i<=L for every i,
sum_{i=0}^3 arcsin(d_i/L)<=pi,                    (8.1)
```

then for all `theta_1,theta_2,theta_3` in `[0,pi/2]`,

```text
d_0*c_1*c_2*c_3+d_1*s_1*s_2*c_3
 +d_2*s_1*c_2*s_3+d_3*c_1*s_2*s_3 <= L,          (8.2)
```

where `c_i=cos(theta_i)` and `s_i=sin(theta_i)`.

### Proof

Scale to `L=1` and maximize the left side on the compact cube.  A boundary
maximum is at most `max_i d_i`: after one angle is `0` or `pi/2`, the remaining
expression is a diagonal `2 by 2` bilinear form, and repeating this observation
finishes the boundary case.

For completeness, the standard interior calculation is recorded.  At an
interior stationary point write the four displayed summands as
`z_0,z_1,z_2,z_3` and their sum as `lambda`.  The three tangent equations are

```text
(z_1+z_2)*cot(theta_1)=(z_0+z_3)*tan(theta_1),
(z_1+z_3)*cot(theta_2)=(z_0+z_2)*tan(theta_2),
(z_2+z_3)*cot(theta_3)=(z_0+z_1)*tan(theta_3).    (8.3)
```

Eliminating the three tangents gives

```text
lambda^2
 =(d_0*d_1+d_2*d_3)*(d_0*d_2+d_1*d_3)
   *(d_0*d_3+d_1*d_2)
   /(4*(p-d_0)*(p-d_1)*(p-d_2)*(p-d_3)),          (8.4)
p=(d_0+d_1+d_2+d_3)/2.
```

Equation (8.4) is also the direct four-factor expansion obtained after
squaring (8.3).  Its geometric form says that the `d_i` are the four chord
lengths of a cyclic quadrilateral of circumradius `lambda/2`.  When
`lambda>max_i d_i`, all four are minor chords, so equivalently

```text
sum_i arcsin(d_i/lambda)=pi.                      (8.5)
```

If an interior maximum had `lambda>1`, monotonicity of `arcsin` would give

```text
pi=sum_i arcsin(d_i/lambda)
  <sum_i arcsin(d_i)<=pi,
```

a contradiction.  Zero sides follow by continuity.  This proves the lemma.

### Lemma 8.2 (the exceptional coefficient check)

For arbitrary `phi_1,phi_2,phi_3` in `[0,pi/2]`, set

```text
d_0=A*cos(phi_1)+B*cos(phi_2)+B*cos(phi_3),
d_i=sin(phi_i), i=1,2,3.                          (8.6)
```

Then the hypotheses of Lemma 8.1 hold with `L=K`, and in fact the angle sum
in (8.1) is strictly less than `pi`.

### Proof

Certainly `d_0<=A+2B=K` and `d_i<=1<K`.  Put

```text
w_1=A/K, w_2=B/K;  w_1+2*w_2=1,
g(phi)=arcsin(sin(phi)/K).
```

Convexity of `arcsin` and `arcsin(cos(phi))=pi/2-phi` give

```text
arcsin(d_0/K)+sum_i arcsin(d_i/K)
 <= pi/2 + h_{w_1}(phi_1)+h_{w_2}(phi_2)+h_{w_2}(phi_3),
h_w(phi)=g(phi)-w*phi.                            (8.7)
```

Here

```text
g'(phi)=cos(phi)/sqrt(K^2-sin(phi)^2)
```

is strictly decreasing.  Thus `h_w` has one maximum, at

```text
cos(phi_w)=w/sqrt(2*(1-w^2)).                     (8.8)
```

Substitution in (8.7) gives a strict margin.  To make the numerical-looking
part reproducibly exact, the following are rational interval bounds (angles
are in radians):

```text
0.632<w_1<0.634,       phi_{w_1}>0.95,
g(phi_{w_1})<0.735,    max h_{w_1}<0.135,

0.183<w_2<0.184,       phi_{w_2}>1.43,
g(phi_{w_2})<0.956,    max h_{w_2}<0.695.         (8.9)
```

Each bound follows from (8.8), `K^2=3/2`, and the alternating rational Taylor
bounds for sine and cosine on `[0,pi/2]`; for example the two last upper bounds
use `sin(0.735)>sin(phi_{w_1})/K` and
`sin(0.956)>1/K`.  Consequently

```text
max h_{w_1}+2*max h_{w_2}<0.135+2*0.695=1.525
                                      <1.57<pi/2. (8.10)
```

Equations (8.7)--(8.10) prove the strict form of (8.1).

## 9. Exceptional vertices and finite-horizon induction

Consider the exceptional future vertex `(A,B,B)`.  Write the current hazards
as

```text
x=sin(theta_1)^2, q=sin(theta_2)^2,
r=sin(theta_3)^2.
```

Dualizing each Euclidean norm in (7.3) gives

```text
G(A,B,B)=max_{phi_1,phi_2,phi_3}
 [d_0*c_1*c_2*c_3+d_1*s_1*s_2*c_3
   +d_2*s_1*c_2*s_3+d_3*c_1*s_2*s_3],            (9.1)
```

with the coefficients (8.6).  Lemmas 8.1--8.2 make (9.1) at most `K`.
The coefficient check is symmetric in the two `B` coordinates, and permuting
the hazards proves the other two exceptional vertices.

Now truncate the three target events to common stopping dates at most `N`.
The future vector after `N` is zero.  Assuming the triangle law at the tail,
the pairwise laws and the induction hypothesis put its root vector in the
polytope (7.4)--(7.5).  Convexity of `G`, followed by (7.6) and (9.1), propagates
the same bound one date backward.  Backward induction proves (7.1) for every
finite horizon.

## 10. Arbitrary clocks, `Never`, sharpness, and equality

For arbitrary laws on `Nat union {Never}`, the three truncated event
probabilities increase coordinatewise to `(a,b,c)`.  Continuity from below and
continuity of square root pass the finite-horizon result to (7.1).  No
stationarity, finite support, eventual absorption, atomlessness, or zero
`Never` mass is used.

The example (7.2) proves sharpness.  It also gives all nontrivial equality
laws, up to permutation, initial all-Continue dates, and null tails:

1. At the first non-all-Continue date the hazards of the pair corresponding
   to the future unit vertex are `1/2,1/2`, while the third hazard is `2/3`.
2. Conditional on joint continuation, that future pair is the exact finite
   first-quitter coalition with probability one.

Indeed, Lemma 8.2 is strict at every exceptional vertex, and the zero vertex
is strictly below `K`.  Equality at a unit vertex is uniquely (7.7).  A
nonvertex future vector is a convex combination of (7.5); equality in the
convex upper bound would require every used vertex to be an equality vertex,
and at a non-all-Continue row there is only the single unit vertex from (7.7).
All-Continue rows merely copy the tail and may be deleted.  Finally, the
reviewed boundary argument says that independent countable clocks realizing a
specified exact pair with probability one must put that pair at one common
deterministic finite date, with the third clock supported strictly later
(possibly at `Never`).

Thus, in the orientation of (7.2), after initial all-Continue dates the first
row is exactly `(1/2,1/2,2/3)` and, on its joint-continuation branch, clocks
`0,1` stop surely together at one later date before clock `2`.  The output is
necessarily `a=b=c=1/6`.  There are no boundary equalities with a zero
coordinate because the pairwise laws then give root sum at most one, strictly
below `K`.

## 11. Exact `K_4` triangle consumer and reward-table audit

For four independent clocks let `q_{ij}` be the probability that `{i,j}` is
the exact finite first-quitter coalition.  For each triple of distinct players
`i,j,k`, forgetting the fourth clock only enlarges all three events.  Therefore
(7.1) gives the four exact projections

```text
sqrt(q_{ij})+sqrt(q_{ik})+sqrt(q_{jk})<=sqrt(3/2) (11.1)
```

for the four triangles of `K_4`.  This is genuinely stronger than the fifteen
two-edge laws: the formal point

```text
q_{01}=q_{02}=q_{12}=1/4, all other q_e=0
```

satisfies every two-edge root bound but violates (11.1).  The theorem does not
by itself give the analogous three-edge `K_4` star bound: a star uses four
different clocks, so there is no event-inclusion reduction to (7.1).  Nor does
it improve a four-cycle without additional information.  This distinction is
important for the hard residual.

The exact terminal-gap consumer is the evident three-floor version.  If a
rational reward table proves, for the three edges of one triangle,

```text
q_e>=alpha_e-L_e*E,
Phi(delta)=sum_e sqrt(max(alpha_e-L_e*delta,0)),   (11.2)
```

and `Phi(0)>sqrt(3/2)`, let `Gamma` be the first `delta` at which
`Phi(delta)<=sqrt(3/2)`.  Then every profile has `E>=Gamma`; pure-time
approximation and the checked terminal-gap theorem consume the resulting
positive gap exactly as in the reviewed two-edge packet.  The law still does
not produce (11.2).

All exact escape profiles found in Sections 2--5 remain below the new
threshold.  At (3.2), the triangle pair masses are

```text
(q_{01},q_{02},q_{12})=(2/21,2/21,2/7),
```

whose root sum is about `1.152<sqrt(3/2)`.  At the asymmetric profiles (4.1)
the nonzero triangle masses are `1/3,1/6`, and at the fully active half-hazard
profile every pair mass is `1/15`.  Hence none of the existing reward tables
can force a three-edge floor above (11.1); the same stationary escapes reopen
before the threshold is reached.  This is an exact falsification of those
candidate tables, not a no-go theorem for all reward tables.

## 12. Sharp four-clock star law

For four independent clocks define

```text
s_j=P(T_0=T_j<min_{k notin {0,j}} T_k, finite), j=1,2,3.
```

Then

```text
sqrt(s_1)+sqrt(s_2)+sqrt(s_3)<=2/sqrt(3).          (12.1)
```

Put

```text
K=2/sqrt(3), A=2-K, B=K-1.
```

As before, the future root vector lies in the polytope cut out by the three
reviewed pairwise laws and the induction hypothesis.  Its vertices are

```text
0; e_1,e_2,e_3; and the permutations of (A,B,B). (12.2)
```

At current hazards `(x,p,q,r)`, with `x` the center hazard, the three immediate
star masses and common continuation are

```text
I_1=x*p*(1-q)*(1-r),
I_2=x*q*(1-p)*(1-r),
I_3=x*r*(1-p)*(1-q),
d=(1-x)*(1-p)*(1-q)*(1-r).                        (12.3)
```

The propagated root sum is again convex in the future root vector, so it is
enough to check (12.2).

## 13. Unit and exceptional star vertices

### Unit vertex

At future vertex `e_1`, write `X=1-x`, `P=1-p`, and put

```text
a=sqrt(x*p+X*P), W=sqrt(x*P).
```

If `q=sin(alpha)^2` and `r=sin(beta)^2`, the propagated sum is

```text
a*cos(alpha)*cos(beta)+W*sin(alpha+beta).
```

For fixed `alpha+beta=2*t`, the product of cosines is at most `cos(t)^2`.
Maximizing the resulting expression in `t` gives

```text
(a+sqrt(a^2+4*W^2))/2.                            (13.1)
```

It is at most `K`, because `K*a+W^2<=K^2`.  The latter follows after one
safe squaring from the exact identity

```text
(4-3*x*P)^2-12*(x*p+X*P)
 =(3*x*P-2)^2+12*p*X>=0.                          (13.2)
```

Equality occurs exactly in either of the two rows

```text
(x,p,q,r)=(1,1/3,1/3,1/3),
(x,p,q,r)=(2/3,0,1/3,1/3).                       (13.3)
```

The other unit vertices follow by permuting the leaves.  A unit vertex also
dominates the zero future vertex.

### Exceptional vertex

It remains to check future `(A,B,B)`.  For fixed `(x,p)`, put

```text
a=sqrt(x*p+(1-x)*(1-p)*A^2),
m=x*(1-p), n=(1-x)*(1-p)*B^2.
```

Using leaf odds `u=sqrt(q/(1-q))`, `v=sqrt(r/(1-r))`, the propagated sum is

```text
[a+sqrt(m*u^2+n)+sqrt(m*v^2+n)]
 /sqrt((1+u^2)*(1+v^2)).                          (13.4)
```

At an interior extremum, differentiation in `u,v` gives

```text
m-n=sqrt(m*u^2+n)*(a+sqrt(m*v^2+n)),
m-n=sqrt(m*v^2+n)*(a+sqrt(m*u^2+n)).              (13.5)
```

Unless `a=0`, subtraction forces `u=v`.  The case `a=0` consists of
`(x,p)=(0,1)` and `(x,p)=(1,0)`; direct substitution in (13.4) is strictly
below `K` in both cases.  If one of `u,v` is zero, the two
remaining resulting coordinates obey the reviewed two-event law and hence
have root sum at most one, while the zero-immediate coordinate is at most
`B`; hence the total is at most `1+B=K`.  Equality here forces its latter
coordinate to equal `B`, hence common continuation probability one and the
all-Continue row.  If an odd equals infinity,
only one immediate star coordinate survives and the sum is at most one.

It therefore remains only `q=r`.  Set `s=1-q=1-r`, `X=1-x`, `P=1-p`.
Then (13.4) becomes

```text
s*a+2*sqrt(P*s*(x*(1-s)+X*s*B^2)).                (13.6)
```

The following exact quadratic check will be useful.  Define

```text
C=a^2+4*P*x-4*P*X*B^2,
H(s)=K^2-2*(K*a+2*P*x)*s+C*s^2.                  (13.7)
```

Then `C>=0` and `H(s)>=0` for `0<=s<=1`.  Here are all details of the only
slightly tedious check.  First, with

```text
U=sqrt(x*p), V=sqrt(X*P),
```

Cauchy gives `U+V<=1`, and

```text
(K-2*B*V)^2-((1-V)^2+A^2*V^2)
 =(1-V)*(1+(12*K-9)*V)/3>=0.                     (13.8)
```

Thus `H(1)=(K-a)^2-4*P*X*B^2>=0`; also `H(0)=K^2`.
The coefficient `C` is nonnegative because

```text
C=x*p+P*(X*(A^2-4*B^2)+4*x),
A^2-4*B^2=K*(4-3*K)>0.                           (13.9)
```

If `x=0`, (13.6) is `K*s*sqrt(P)<=K`, with equality only when
`P=s=1`, the all-Continue row.  Hence suppose `x>0`.  If the vertex of the
convex quadratic (13.7) lies in `[0,1]`, its being at most one says

```text
F:=a^2-K*a+2*P*x-4*P*X*B^2>=0.                  (13.10)
```

The function `F`, as a function of `P`, is convex.  At `P=0` it is
`x-K*sqrt(x)<0`.  At `P=1` it is increasing in `x`, since its derivative is

```text
-A^2+K*A/(2*sqrt(1-x))+2+4*B^2>0,
```

and at `x=1/6` it is still negative:

```text
9*F(1/6,1)=-27-6*sqrt(10)+2*sqrt(30)+20*sqrt(3)<0. (13.10a)
```

For an entirely rational sign check in (13.10a), use
`sqrt(10)>79/25`, `sqrt(30)<11/2`, and `sqrt(3)<26/15`; the displayed
quantity is then less than `-22/75`.  A convex function on `[0,1]` is at
most the larger of its endpoint values.  Hence (13.10) forces `x>1/6`.

On `x>=1/6`, consider the convex function of `P`

```text
J=K^2*x-K*a*x-P*x^2-K^2*X*B^2.                 (13.11)
```

Here is a complete endpoint-and-stationary-point check that `J>=0`.  At
`P=0`, the function of `x`

```text
J_0=K^2*x-K*x*sqrt(x)-K^2*(1-x)*B^2
```

is concave, so its minimum on `[1/6,1]` is at an endpoint.  The endpoint
values are

```text
J_0(1/6)=-64/27-sqrt(2)/18+40*sqrt(3)/27>0,
J_0(1)=4/3-2*sqrt(3)/3>0.                       (13.11a)
```

For the first sign, multiply by `54` and use
`sqrt(3)>265/153`, `sqrt(2)<3/2`; the resulting lower bound is
`1855/306>0`.

At `P=1`, call the resulting function `J_1(x)` and put
`t=sqrt(1-x)`.  Direct differentiation gives `2*t*J_1'(x)=4*q(t)`, where

```text
q(t)=t^3+(1-sqrt(3))*t^2+(11/9-8*sqrt(3)/9)*t
     +(sqrt(3)-1)/3.
```

Its discriminant is
`4*(-9035+5214*sqrt(3))/729<0` (the squared integer difference is
`9035^2-3*5214^2=73837>0`).  Thus `q` has one real root; since
`q(0)>0` and `q(t)` tends to `-infinity` as `t` tends to `-infinity`, that
root is negative.  Therefore `J_1` is increasing.  Its left endpoint is

```text
108*J_1(1/6)=160*sqrt(3)-259-12*sqrt(10)+4*sqrt(30)>0. (13.11b)
```

The rational bounds `sqrt(3)>265/153`, `sqrt(10)<19/6`, and
`sqrt(30)>547/100` give the positive lower bound `7666/3825` in
(13.11b).

It remains to check an interior stationary point of `J`.  Put
`D=(1-x)*A^2-x`.  The stationary equation forces `D<0` and

```text
a=-K*D/(2*x).                                    (13.11c)
```

Feasibility forces `x>2/3`.  Indeed the right side of (13.11c) is increasing
in `x`, while `A*sqrt(1-x)` is decreasing; at `x=2/3` the former is strictly
smaller than the latter because
`A^2+2*A-2=22/3-4*sqrt(3)>0`.  Substitution in (13.11) now gives exactly

```text
(x-1)*(160*K*x-112*K+9*x^2-188*x+128)
 /(3*(12*K*x-12*K-19*x+16))>=0.                 (13.12)
```

On `[2/3,1]` the numerator in parentheses is positive and increasing, while
the denominator in parentheses is negative and decreasing.  It suffices to
check these claims at `2/3`: the values are respectively
`20/3-32*sqrt(3)/9>0` and `10/3-8*sqrt(3)/3<0`; their derivatives have the
same stated signs because `160*K-176>0` and `12*K-19<0`.  Since
`x-1<=0`, (13.12) is nonnegative.  This proves
`J>=0`.  Finally

```text
C*K^2-(K*a+2*P*x)^2=4*P*J>=0,                   (13.13)
```

so the interior minimum of `H` is nonnegative as well.  This exhausts the
quadratic.  Equality at `s=1` in (13.8) requires `V=1`, hence the
all-Continue row.  Equality at an interior minimum forces `J=0`, which the
preceding check permits only at `x=1,P=2/3`; then the minimizing value is
`s=2/3`.  This is the first row in (13.3).

Since `K-s*a` is nonnegative, squaring (13.6) shows that its being at most
`K` is exactly `H(s)>=0`.  Equality in the exceptional check is only the
all-Continue row or the first row in (13.3).

## 14. Star induction, arbitrary clocks, and equality

The vertex checks of Section 13 and convexity propagate (12.1) through every
finite horizon.  Truncation at common dates `<=N`, continuity from below, and
continuity of square root prove it for arbitrary nonstationary behavioral
hazards with atoms and arbitrary `Never` mass.

The constant is sharp in two forms, and the preceding equality audit shows
they exhaust equality up to a permutation of the leaves, initial
all-Continue dates, and null tails.

1. **Same date.**  The center stops surely and the three leaf hazards are all
   `1/3`.  Later leaf laws are irrelevant.  Each star mass is `4/27`.
2. **Staggered.**  At the first non-all-Continue date the center hazard is
   `2/3`, one designated leaf continues surely, and the other two leaf hazards
   are `1/3`.  Conditional on joint continuation, the center and designated
   leaf form the exact first-quitter pair with probability one.  Independence
   forces them to share one later deterministic finite date, with both other
   leaves supported strictly later.  Again each star mass is `4/27`.

The exceptional vertex can preserve equality only through all-Continue or
the absorbing same-date row.  The unit vertex gives exactly the two rows
(13.3).  To justify that this finite-row audit also covers arbitrary support,
observe that a nonzero star mass gives at least one finite atom, so the union
of the four finite supports has a least date.  Delete the preceding
all-Continue dates and apply the already-proved arbitrary-clock inequality to
the conditional tail after that date.  Equality in this one-step application
therefore has exactly the vertex equality just classified.  In the staggered
case the future unit coordinate must equal one.  Thus no infinite limiting or
`Never` equality case was lost.

## 15. Full `K_4` consumer and current producer status

For the six exact pair masses of four clocks, (12.1) gives the four star
facets

```text
sum_{j != i} sqrt(q_{ij})<=2/sqrt(3), i=0,1,2,3. (15.1)
```

Together with the four triangle inequalities (11.1), the fifteen reviewed
two-edge inequalities, and nonnegativity, these are a strictly stronger outer
body.  Summing (15.1) yields

```text
sum_{i<j} sqrt(q_{ij})<=4/sqrt(3).                (15.2)
```

For example the uniform formal point `q_{ij}=1/6`, which survives all two-edge
laws and saturates every triangle law, violates every star law and (15.2).
For a bare four-cycle, the two disjoint-edge inequalities still give the
stronger bound `sum_cycle sqrt(q_e)<=2`; the star theorem adds information
when diagonal masses or three incident floors are present.

An affine-floor terminal-gap consumer is obtained from any one star exactly
as in (11.2), with threshold `2/sqrt(3)`.  No existing hard-residual or
minimum-source statement inspected in this project supplies three
simultaneous lower bounds on actual exact pair masses of one behavioral
profile.  Those sources constrain payoff ledgers, localized sources, or a
supplied controller; they do not identify three star/triangle clock events.
Thus (15.1) is presently a counterexample-search consumer, not a producer and
not a chronology bypass by itself.  The candidate tables in Sections 2--5
all have exact stationary Nash profiles whose star root sums are far below
`2/sqrt(3)`.

The exact source audit is short.  The checked declarations
`finFourHardResidual_minimumLaw_causalSuffixAtom` and
`exists_finFourHardResidual_minimumLaw_causalSuffixAtom` in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinFourMinimumLawFiniteAtom.lean`
produce one positive finite coalition atom at a supplied or selected minimum
joint-law point; they neither select a pair label nor lower-bound three atoms.
The checked declaration
`FinFourQuantitativeFullSupportHardResidual.exists_terminalGap_collision_at_singleton`
in
`UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/PunishmentNormalAtomicCollisionHandoff.lean`
is a reward inequality at each pure singleton.  The current forced-pair
normal-form notebook can turn one chosen singleton occurrence into one chosen
pair occurrence only by replacing its marked root, hence on a different
profile.  None of these statements synchronizes three such choices on one
actual law.  That missing same-profile synchronization, not chronology after
the law is constructed, is the precise producer blocker.

## 16. Next exact question

Search directly for three star-edge affine floors crossing `2/sqrt(3)` (or
three triangle floors crossing `sqrt(3/2)`) while classifying every stationary
complementarity solution of the candidate table before any terminal-gap
claim.  The most useful structural follow-up on the law side is a non-pairwise
four-cycle inequality involving its two diagonal masses, since the bare cycle
projection is already controlled more sharply by disjoint pairs.
