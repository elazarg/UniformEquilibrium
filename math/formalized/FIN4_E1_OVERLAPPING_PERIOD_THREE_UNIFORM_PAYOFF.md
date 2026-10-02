# E1 overlapping period-three uniform payoff

Author: CODEX_SPINOZA

Independent reviews: [CODEX_NEGATIVE_CERTIFICATE](../feedback/CODEX_SPINOZA__E1_OVERLAPPING_PERIOD_THREE_CLOSURE__BY_CODEX_NEGATIVE_CERTIFICATE.md) and [CODEX_SNELL](../feedback/CODEX_SPINOZA__E1_OVERLAPPING_PERIOD_THREE_CLOSURE__BY_CODEX_SNELL.md)

## Exact statement

Players are `0,1,2,3`.  In bit-mask order, let the nonempty-coalition reward
rows be

```text
 1 ( 1,  4,  0, 0)      2 ( 4,  1,  0, 0)
 3 ( 1,  1,  1, 1)      4 ( 0,  0,  1, 4)
 5 ( 1,-5/2, 1, 2)      6 ( 0,  1,  1, 1)
 7 ( 1, -4,  0, 0)      8 ( 0,  0,  4, 1)
 9 ( 1,  0,  1, 1)     10 ( 2,  1, 16, 1)
11 ( 0,  7,  0, 0)     12 ( 1,  1,  1, 1)
13 ( 0,  0,  0, 4)     14 ( 0,  0, 17, 0)
15 (-1, -1, -1,-1).
```

Call this rational table `rE`.  The payoff when every player Continues
forever is zero.

### Theorem A: exact E1 closure

There are hazards in `(0,1)` with initial phase `0` and phase word

```text
phase 0: (0,a,b,0),
phase 1: (c,d,0,e),
phase 2: (f,0,g,h),                                  (1)
```

such that all eight active Quit-minus-Continue gaps vanish and all four
inactive gaps are strictly negative.  The three-phase root word absorbs and
contracts every player's fixed-opponent continuation.  Its phase-zero cyclic
terminal value is therefore a uniform-equilibrium payoff against unrestricted
behavioral deviations.

The unique root in the rational box certified below is numerically

```text
a = .3551693780902477    b = .2588856210079327
c = .2302690784708344    d = .0952220237568218
e = .2528341986655558    f = .4405211001832288
g = .2821769183533719    h = .1721135892992767.       (2)
```

The corresponding cyclic values, included only as locators, are

```text
V0 = (1.519272314792, 1,              1,              1.227112378976)
V1 = (0.975924615928, 1.349319387596, 1.550794838245, 0.978073312339)
V2 = (0.951433517765, 1.149545399206, 0.924180332285, 1.372914659558).
```

The proof uses the exact rational enclosure below, not these rounded values.

### Theorem B: a uniform 60-coordinate neighborhood

Put

```text
eta = 1/50000000.                                      (3)
```

Every real Fin4 reward table `r` satisfying

```text
max_(nonempty S,i) |r_i(S)-rE_i(S)| <= eta             (4)
```

has an exact cyclic Nash--Bellman block with word (1) and hazards in the
single rational box defined below.  Consequently every such table has a
terminal uniform-equilibrium payoff against unrestricted behavioral
deviations.

### Theorem C: an unbounded structural cylinder

For a reward coordinate write `(i,S)` for `r_i(S)` and define

```text
I = {(0,{1,2,3}), (0,{0,1,2,3}),
     (3,{0,1,2}), (3,{0,1,2,3})}.                     (5)
```

Let `rbar` satisfy

```text
|rbar_i(S)-rE_i(S)| <= 1/50000000
    for every (i,S) not in I.                          (6)
```

The coordinates of `rbar` in `I` need not be specified.  Choose independently
`alpha_i>0` and `beta_i` in `R`.  On every coordinate outside `I`, set

```text
r_i(S)=alpha_i*rbar_i(S)+beta_i,                       (7)
```

and assign the four coordinates in `I` arbitrary real values.  Then `r` has
an exact absorbing period-three Nash--Bellman block on (1), hence an
unrestricted terminal uniform-equilibrium payoff.

### Theorem D: reusable polyhedral interval-face criterion

Fix any finite phase-support word, a rational hazard box `X` contained in the
strict unit cube for its active hazards and having positive one-cycle
absorption throughout, and a rational invertible matrix `C` whose size is the
number of active hazards.  Form the cleared active-gap vector `F_r` as in the
definitions below.  Suppose

```text
C*F_r is negative on every lower coordinate face of X,
C*F_r is positive on every upper coordinate face of X,               (8)
```

and every inactive cleared gap is negative throughout `X`.  Then `r` has an
exact cyclic Nash--Bellman block on that support.  If every player faces a
positive opponent hazard somewhere in the word, the initial cyclic value is
an unrestricted terminal uniform-equilibrium payoff.

All conditions in (8) and the inactive screens are finite strict
inequalities.  For a fixed rational box, tensor-Bernstein coefficient signs
give a finite sufficient system of strict rational linear inequalities in
the reward coordinates.  This defines an explicit open polyhedral
certificate chamber.

## Conjecture-facing change

The table `rE` was the exact survivor E1 after stationary, partitioned
period-two, and several short-period screens in
[`CODEX_NEGATIVE_CERTIFICATE__ASYMMETRIC_STATIONARY_SEAM_CLOSURE.md`](../notes/CODEX_NEGATIVE_CERTIFICATE__ASYMMETRIC_STATIONARY_SEAM_CLOSURE.md).
Theorem A proves that it is not a negative candidate: an overlapping-support
period-three word closes it against the full behavioral strategy class.

Theorems B--D make the result more than an isolated table calculation.
Theorem B gives a full-dimensional open Fin4 neighborhood; Theorem C gives an
unbounded structural class with independent positive affine changes of every
player's payoff and four completely free reward coordinates; Theorem D gives
a finite rational polyhedral screening criterion reusable for other support
words.

This is a special-class existence theorem, not a producer for every Fin4
table.  It is compatible with
[`PASSIVE_PADDING_PERIODIC_CERTIFICATE_NO_GO.md`](PASSIVE_PADDING_PERIODIC_CERTIFICATE_NO_GO.md),
which excludes universal production of exact finite-period certificates.

## Definitions and assumptions

At phase `t`, players independently Quit with product probabilities `q_t`.
Let `I_t(i)` be player `i`'s unconditional immediate terminal-reward
contribution and let

```text
s_t = product_i (1-q_t(i)),
D   = 1-s_0*s_1*s_2.                                  (9)
```

Indices below are modulo three.  Define

```text
W_t(i) = I_t(i)+s_t*I_(t+1)(i)+s_t*s_(t+1)*I_(t+2)(i). (10)
```

When `D>0`, the actual cyclic terminal value is `V_t=W_t/D`.

For player `i` at phase `t`, let `Q_ti` be the endpoint payoff if `i` Quits
surely; let `A_ti` be the contribution to the pure-Continue endpoint from a
nonempty opponent coalition; and let `c_ti` be the probability that every
opponent Continues.  Define the cleared gap

```text
F_ti = D*(Q_ti-A_ti)-c_ti*W_(t+1)(i).                 (11)
```

Thus `F_ti/D` is exactly pure Quit minus pure Continue.  For (1), the active
system is

```text
(F_01,F_02,F_10,F_11,F_13,F_20,F_22,F_23)=0          (12)
```

in variable order `(a,b,c,d,e,f,g,h)`.  The inactive coordinates are
`(0,0),(0,3),(1,2),(2,1)`.  A negative inactive gap has the required
Continue orientation because its prescribed hazard is zero.

The strategy induced by the word (1) is calendar-periodic until absorption.
The conclusion permits an arbitrary unilateral behavioral replacement: the
deviator may use any history-dependent live hazard, including Never and
arbitrarily late quitting.  No stationarity, finite-horizon, bounded-memory,
or restricted-deviation assumption is made.

## Source correspondence

The checked downstream declaration is
`isUniformEquilibriumPayoff_quittingCyclicTerminalValue_of_certificate` in
[`UniformEquilibrium/Quitting/Cycles/PeriodicCompiler.lean`](../../UniformEquilibrium/Quitting/Cycles/PeriodicCompiler.lean).
Its local root notion uses `IsεQuittingRootNash` from
[`UniformEquilibrium/Quitting/Root/FirstBranch.lean`](../../UniformEquilibrium/Quitting/Root/FirstBranch.lean).
The compiler accepts an explicit initial phase, the cyclic policy recursion,
exact phasewise root Nash, and player-deleted cycle contraction.  It compares
the resulting profile with every unilateral behavioral deviation and returns
`IsUniformEquilibriumPayoff none` for the initial cyclic value.

The E1 rewards are the displayed deformation of the boundary table represented
in
[`UniformEquilibrium/Quitting/Examples/SolanVieilleBoundaryTable.lean`](../../UniformEquilibrium/Quitting/Examples/SolanVieilleBoundaryTable.lean).

The new content is the exact rational Poincare--Miranda enclosure, its uniform
60-coordinate reward version, the invisible-coordinate and affine cylinder,
and the abstract interval-face criterion.  These are ordinary mathematics,
not existing Lean declarations.

## Proof

### 1. Exact rational enclosure for E1

Let `x0` be the eight rational decimals in (2), interpreted literally, put
`rho=1/10^7`, and set

```text
X = x0 + [-rho,rho]^8.                                (13)
```

Let `F` denote (12) and let `C=10^-12 M`, where

```text
M =
 315143353187  366974958817  -49078078206  184811852330  232875167579 -254869288005  -25099394501   -1470845305
 602147704263  145073028566   -9776944759 -100954767104  648395477518  294319240668  121157930961 -211997987049
-309126321348  258278517492 -102280783703  318835250165  477261949039  398272112383   56650468854 -195187547313
   8141174505   -8490457215 -341152554699   89200975646   81054707800  142638748426    6864760919    -901901991
  68266279421  -92414191444   99419891079  230779479327  330411042247  -49452845261   97457493728  -65051669603
  -4718561732   76693224365 -112489910972   84672772712 -120106797257  339836466727   67508004707  469042378865
-344947719758  240513202079 -265825502558  367886940515 -509613507555  329832798069   25940159701  158832741351
  -2160865764  181328381440  -51514764712   38775903777  -55002918462  155628140095 -395004284185  214797999024.
                                                               (14)
```

The integer determinant of `M` is nonzero: modulo the prime `1000003` it is
`990083`.  Hence `C` is invertible.

Evaluate every occurrence of a variable in (10)--(12) by ordinary rational
interval arithmetic on `X`; different occurrences are deliberately not
correlated.  The resulting interval Jacobian satisfies

```text
D(X) is contained in (9/10,19/20),
K(X) := x0-C*F(x0)+(Id-C*J_F(X))*(X-x0)
     is contained in x0+[-rho/40000,rho/40000]^8.     (15)
```

All endpoints are rational.  The largest coordinate radius of `K(X)`,
divided by `rho`, is less than `1/40000`; its numerical locator is
`0.000019872`.

Put `H=C*F`.  For `x=x0+delta`, the integral mean-value Jacobian `Jbar` lies
in `J_F(X)`, and

```text
H(x) = delta-
  [-C*F(x0)+(Id-C*Jbar)*delta].                       (16)
```

The bracket belongs coordinatewise to
`[-rho/40000,rho/40000]^8`.  Hence `H_i<0` on the lower `i`-face of `X` and
`H_i>0` on its upper `i`-face.  Poincare--Miranda gives `H(x*)=0`; invertibility
of `C` gives `F(x*)=0`.  The interval Krawczyk theorem additionally gives
uniqueness of this zero in `X`, although uniqueness is not needed for the
equilibrium conclusion.

The same rational interval evaluation gives

```text
F_00(X)<-29/100,   F_03(X)<-29/100,
F_12(X)<-29/100,   F_21(X)<-29/100.                   (17)
```

Tighter decimal enclosures, included only as locators, are

```text
[-.476341,-.476337], [-.292682,-.292679],
[-.306788,-.306782], [-.373817,-.373812].             (18)
```

The box lies strictly in `(0,1)^8`.  Since `D>0`, (12) gives exact active
indifference and (17) gives the four strict inactive Continue inequalities.
The payoff is affine in each player's own Bernoulli marginal, so the two pure
endpoint comparisons cover every randomized one-stage deviation.

Every phase has at least two strictly positive hazards.  Consequently each
player faces a positive opponent hazard in every phase, so its product of
player-deleted Continue masses over the cycle is strictly below one.  Equations
(9)--(10) are the cyclic policy recursion.  The checked periodic compiler now
proves Theorem A against arbitrary behavioral unilateral deviations.

### 2. Uniform reward neighborhood

Replace independently each of the 60 reward coordinates in the rational
interval calculation by

```text
[rE_i(S)-eta,rE_i(S)+eta].                            (19)
```

Keep the same `x0`, `rho`, `X`, and `C`.  Direct rational interval evaluation
of (10)--(12), using (19) in both the center residual and the interval
Jacobian, gives uniformly for every `r` in (4)

```text
x0-C*F_r(x0)+(Id-C*J_(F_r)(X))*(X-x0)
  is contained in x0+[-5*rho/6,5*rho/6]^8,           (20)

F^r_00(X), F^r_03(X), F^r_12(X), F^r_21(X) < -29/100. (21)
```

The largest coordinate radius in (20), divided by `rho`, is less than
`0.824`; this is only a locator for the exact rational comparison with `5/6`.
On the upper and lower `i`-faces, the corresponding coordinate of `C*F_r`
therefore has signs `>rho/6` and `<-rho/6`.  Poincare--Miranda and
invertibility of `C` give an active zero in `X` for every fixed `r`.  Equations
(21) and the unchanged denominator bound give the inactive inequalities.
Support interiority and player-deleted contraction depend only on `X`, so the
same compiler proves Theorem B.  No continuous selection of roots over the
reward box is used.

### 3. Invisible coordinates and positive affine invariance

The phase supports are

```text
A0={1,2}, A1={0,1,3}, A2={0,2,3}.                    (22)
```

On path, every realized coalition is a nonempty subset of one of these sets.
If player `i` deviates at a phase, the coalition is either a subset of
`A_t\{i}` or that subset with `i` adjoined.  No phase contains all three
opponents of player 0, so neither player-0 coordinate on `{1,2,3}` or on the
full coalition can occur.  The same statement holds for player 3 and the two
remaining coordinates in (5).  A behavioral deviation changes only the
deviator's action and cannot add an absent opponent to a phase support.
Therefore all four coordinates in `I` are invisible to the cyclic values and
every relevant one-player endpoint.

Next suppose `r` has the displayed certificate and choose independently
`alpha_i>0`, `beta_i` real.  Define

```text
r'_i(S)=alpha_i*r_i(S)+beta_i.                        (23)
```

At phase `t`,

```text
I'_t(i)=alpha_i*I_t(i)+(1-s_t)*beta_i.
```

Substitution in the Bellman recursion gives

```text
V'_t(i)=alpha_i*V_t(i)+beta_i.                        (24)
```

Both pure endpoints transform by the same positive affine map.  Active
zeroes remain zero and inactive negative signs remain negative.  The
player-deleted contraction makes absorption almost sure even after an
arbitrary unilateral behavioral deviation, so the additive constant is
indeed received terminally.

To prove Theorem C, fill the four unspecified coordinates of `rbar` with
their E1 values.  Apply Theorem B, then (23)--(24), then overwrite the four
invisible coordinates arbitrarily.  None of these operations changes a
certificate field.

### 4. General interval-face criterion

Under Theorem D's hypotheses, Poincare--Miranda applied to `C*F_r` gives an
active zero in `X`.  Since `C` is invertible, it is a zero of `F_r`.  Positive
cycle absorption makes the clearing denominator positive, and the inactive
signs give the remaining root-Nash inequalities.  A positive opponent hazard
for each player somewhere in the word makes its player-deleted cycle Continue
product strictly below one.  The periodic compiler gives the unrestricted
terminal uniform payoff.

For fixed hazards, every cleared gap is linear in the reward table.  On a
fixed rational box, requiring all tensor-Bernstein coefficients of the
coordinate-face polynomials and inactive-gap polynomials to have the required
strict signs is therefore a finite system of strict rational linear
inequalities.  This proves the final polyhedral assertion.

## Boundary tests

1. **Orientation.**  Direct reconstruction gives `F_ti/D = Quit-Continue`.
   Thus active zero and inactive negative have exactly the required signs.
2. **Absorption.**  `D(X)` lies in `(9/10,19/20)`, so the cycle absorbs.
3. **Unrestricted deviations.**  Every player faces a positive opponent
   hazard in the word.  The checked player-deleted contraction compiler, not
   a stationary or bounded-clock argument, controls all behavioral updates.
4. **Exact interval recomputation.**  Both independent reviewers reconstructed
   all twelve gaps and the hazard Jacobian using exact rational arithmetic.
   They reproduced the determinant residue, (15), (17), (20), and (21).
5. **Independent neighborhood variables.**  The 60 reward coordinates in
   (19) are separate intervals in both residual and Jacobian; no correlated
   error variable is assumed.
6. **Invisible-coordinate boundary.**  Direct enumeration of every on-path
   and unilateral endpoint coalition confirms exactly the four invisible
   coordinates in (5).
7. **Affine boundary.**  Positivity of `alpha_i` is essential: a negative
   scale would reverse inactive Nash signs.  No bound on positive `alpha_i`,
   on `beta_i`, or on the final invisible coordinates is needed.
8. **Non-exhaustiveness.**  The proof supplies one support certificate and an
   open class.  Failure of its inequalities says nothing about terminal
   exploitability.  The passive-padding no-go forbids interpreting Theorem D
   as a universal exact-period producer.

## Adapter and consumer

The actual-data adapter is explicit.  For Theorem A it is the displayed
rational table `rE`; for Theorem B it is membership in the 60-coordinate box
(4); for Theorem C it is the visible-coordinate box, four positive affine
scales and origins, and four arbitrary invisible coordinates; for Theorem D
it is the finite list of rational face and inactive-gap inequalities.
Poincare--Miranda converts those data to an exact active root while the strict
screens supply the remaining Nash fields.

The checked consumer is
`isUniformEquilibriumPayoff_quittingCyclicTerminalValue_of_certificate`.
The proof above supplies its explicit initial phase, policy recursion, exact
root-Nash conditions, and player-deleted contraction.  The consumer returns
one fixed phase-zero `IsUniformEquilibriumPayoff none`, including unrestricted
behavioral deviations and every sufficiently long horizon in the project
semantics.

## Lean handoff

A narrow formalization can separate four layers.

1. Encode the E1 rational reward table, the three support roots, the eight
   active hazard variables, and the twelve cleared polynomials (11).
2. Formalize or import a box Poincare--Miranda theorem and verify the rational
   face inequalities using interval or Bernstein certificates.  The modular
   determinant witness proves invertibility of `C`.
3. Package the resulting root into the existing cyclic certificate with
   `initial := 0`, prove the four inactive signs and player-deleted
   contraction, and invoke the checked periodic compiler.
4. Prove the reward-box, invisible-coordinate, and positive-affine transport
   lemmas separately.  The general Bernstein chamber can remain a theorem
   about a supplied finite coefficient-sign certificate.

No floating-point locator should enter a Lean proposition.  The formal proof
should use only the rational bounds `1/40000`, `5/6`, `-29/100`,
`(9/10,19/20)`, and the exact input data.

## Scope and nonclaims

This packet proves a terminal uniform-equilibrium payoff for E1 and the stated
open/unbounded certificate classes.  It does not prove that every Fin4 table
has a period-three or any exact finite-period block.  It does not infer a
positive gap from failure of a support search.  It does not give a stationary,
finite-horizon, or discounted equilibrium theorem.  The rational interval and
Poincare--Miranda mathematics is independently reviewed ordinary mathematics,
not yet a checked Lean declaration.
