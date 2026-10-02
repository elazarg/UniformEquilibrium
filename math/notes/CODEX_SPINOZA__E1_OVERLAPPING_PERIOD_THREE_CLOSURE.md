# The E1 survivor closes by an overlapping period-three block

Author: `CODEX_SPINOZA`

Status: **computer-assisted exact ordinary-mathematics proof.  A rational
Krawczyk enclosure produces an exact absorbing cyclic Nash--Bellman block on
the support word `{1,2}|{0,1,3}|{0,2,3}`.  The checked periodic compiler then
gives a terminal uniform-equilibrium payoff against unrestricted behavioral
deviations.  The same calculation proves that the certificate persists on
the explicit sup-norm reward neighborhood of radius `1/50000000` in all 60
coordinates.  Section 5 enlarges this to an unbounded structural class using
four support-invisible coordinates and independent positive affine payoff
changes for the four players.  This is not Lean-formalized and requires
independent review of the displayed rational interval calculation.**

This note answers the concrete next test in
[`CODEX_NEGATIVE_CERTIFICATE__ASYMMETRIC_STATIONARY_SEAM_CLOSURE.md`](CODEX_NEGATIVE_CERTIFICATE__ASYMMETRIC_STATIONARY_SEAM_CLOSURE.md).
The table called (E1) there is not a negative candidate.  Its partition
screens miss a genuinely overlapping three-phase word.

## 1. Exact table and claim

Players are `0,1,2,3`.  In bit-mask order the nonempty-coalition reward rows
are

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

### Theorem 1.1 (overlapping period-three closure)

For this rational quitting table there are hazards in `(0,1)` with phase
word

```text
phase 0: (0,a,b,0),
phase 1: (c,d,0,e),
phase 2: (f,0,g,h),                                  (1.1)
```

such that all eight active Quit-minus-Continue gaps vanish and all four
inactive gaps are strictly negative.  The three-phase root word absorbs and
contracts every player's fixed-opponent continuation.  Its phase-zero value
is therefore a terminal uniform-equilibrium payoff against unrestricted
behavioral deviations.

The unique root in the rational box certified below is numerically

```text
a = .3551693780902477    b = .2588856210079327
c = .2302690784708344    d = .0952220237568218
e = .2528341986655558    f = .4405211001832288
g = .2821769183533719    h = .1721135892992767.       (1.2)
```

The corresponding cyclic values, shown only as locators, are

```text
V0 = (1.519272314792, 1,              1,              1.227112378976)
V1 = (0.975924615928, 1.349319387596, 1.550794838245, 0.978073312339)
V2 = (0.951433517765, 1.149545399206, 0.924180332285, 1.372914659558).
                                                               (1.3)
```

The existence and Nash claims use the exact enclosure below, not the rounded
numbers in (1.2)--(1.3).

## 2. Polynomial Nash--Bellman system

For a phase root `q_t`, let `I_t(i)` be player `i`'s unconditional immediate
reward at that phase and let

```text
s_t = product_i (1-q_t(i)),
D   = 1-s_0*s_1*s_2.
```

All are polynomials over the rational table.  Put, with indices modulo three,

```text
W_t(i) = I_t(i)+s_t*I_(t+1)(i)+s_t*s_(t+1)*I_(t+2)(i).  (2.1)
```

When `D>0`, the actual cyclic terminal value is exactly `V_t=W_t/D`.
Let `Q_ti` be the endpoint payoff if `i` Quits now, `A_ti` the contribution
to its Continue endpoint from a nonempty opponent coalition, and `c_ti` the
probability that every opponent Continues.  Define the polynomial

```text
F_ti = D*(Q_ti-A_ti)-c_ti*W_(t+1)(i).                  (2.2)
```

Thus `F_ti/D` is exactly the Quit-minus-Continue gap.  The square active
system is

```text
(F_01,F_02,F_10,F_11,F_13,F_20,F_22,F_23)=0,          (2.3)
```

in the variable order `(a,b,c,d,e,f,g,h)`.

## 3. Exact rational Krawczyk certificate

Let `x0` be the eight rational decimals displayed in (1.2), interpreted
literally, let `rho=1/10^7`, and put

```text
X = x0 + [-rho,rho]^8.                                (3.1)
```

Let `F` denote (2.3) and let `C=10^-12 M`, where

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
                                                               (3.2)
```

The integer determinant of `M` is nonzero: modulo the prime `1000003` it is
`990083`.  In particular `C` is invertible.  Evaluate every occurrence of a
variable in (2.1)--(2.3) by ordinary rational interval arithmetic on `X`;
different occurrences are deliberately not correlated.  The resulting
interval Jacobian `J_F(X)` satisfies the exact inclusions

```text
D(X) is contained in (9/10,19/20),
K(X) := x0-C*F(x0)+(Id-C*J_F(X))*(X-x0)
     is contained in x0+[-rho/40000,rho/40000]^8.      (3.3)
```

All endpoints in this calculation are rational.  The largest coordinate
radius of `K(X)`, divided by `rho`, is less than `1/40000`; the numerical
locator for that exact maximum is `0.000019872`.  The interval Krawczyk
theorem applied to (3.3) gives a unique exact zero `x*` of (2.3) in the
interior of `X`.

Existence also follows from (3.3) by an elementary Poincare--Miranda argument,
without using the uniqueness clause of the Krawczyk theorem.  Put `H=C*F`.
For `x=x0+delta`, the integral mean-value Jacobian lies in `J_F(X)`, and

```text
H(x) = delta-
  [-C*F(x0)+(Id-C*Jbar)*delta].                        (3.3a)
```

The bracket belongs coordinatewise to
`[-rho/40000,rho/40000]^8`.  Hence `H_i<0` on the lower `i`-face of `X` and
`H_i>0` on its upper `i`-face.  Poincare--Miranda gives `H(x*)=0`; the modular
determinant check makes `C` invertible, so `F(x*)=0`.

The same rational interval evaluation of the four inactive numerators gives

```text
F_00(X)<-29/100,   F_03(X)<-29/100,
F_12(X)<-29/100,   F_21(X)<-29/100.                    (3.4)
```

For orientation, their tighter computed interval enclosures are respectively

```text
[-.476341,-.476337], [-.292682,-.292679],
[-.306788,-.306782], [-.373817,-.373812].              (3.5)
```

Only (3.3)--(3.4), whose comparison bounds are rational, are used as the
certificate.  The box (3.1) lies strictly inside `(0,1)^8`.  Since `D>0`,
(2.3) gives exact active indifference and (3.4) gives the correct strict
Continue inequalities for all inactive players.  This proves the phasewise
Nash--Bellman assertions in Theorem 1.1.

Every phase has at least two strictly positive hazards.  Hence each phase has
positive absorption, and every player faces a strictly positive opponent
hazard in every phase.  The product of the player-deleted Continue masses is
therefore strictly below one for each player.  Iterating (2.1) identifies the
displayed Bellman word with the actual terminal mixture.  The hypotheses of
`isUniformEquilibriumPayoff_quittingCyclicTerminalValue_of_certificate` in
`UniformEquilibrium/Quitting/Cycles/PeriodicCompiler.lean` now hold, so its
conclusion supplies the asserted fixed terminal uniform payoff against all
behavioral deviations.

## 4. An explicit open reward neighborhood

The active zero is robust in all reward coordinates, not merely along a
selected deformation.

### Theorem 4.1 (uniform neighborhood closure)

Let `rE` be the E1 table in Section 1 and let

```text
eta = 1/50000000.                                      (4.1)
```

For every real reward table `r` satisfying

```text
max_(nonempty S,i) |r_i(S)-rE_i(S)| <= eta,            (4.2)
```

there is a root of the form (1.1), with its eight hazards in the single box
`X` from (3.1), which is an exact cyclic Nash--Bellman block.  Consequently
every table in the open sup-norm ball in (4.2) has a terminal
uniform-equilibrium payoff against unrestricted behavioral deviations.

**Proof.**  Replace independently each of the 60 reward coordinates in the
rational interval calculation of Section 3 by

```text
[rE_i(S)-eta,rE_i(S)+eta].                             (4.3)
```

Keep the same rational center `x0`, hazard radius `rho`, and preconditioner
`C`.  Direct rational interval evaluation of (2.1)--(2.3), including the
reward intervals (4.3) in both the center residual and the interval Jacobian,
gives uniformly for every `r` in (4.2)

```text
x0-C*F_r(x0)+(Id-C*J_(F_r)(X))*(X-x0)
  is contained in x0+[-5*rho/6,5*rho/6]^8,            (4.4)

F^r_00(X), F^r_03(X), F^r_12(X), F^r_21(X) < -29/100. (4.5)
```

The largest coordinate radius in (4.4), divided by `rho`, is in fact less
than `0.824`; this decimal is only a locator for the exact comparison with
`5/6`.  As in (3.3a), on the upper and lower `i`-faces the corresponding
coordinate of `C*F_r` has respectively the strict signs `>rho/6` and
`<-rho/6`.  Poincare--Miranda and the exact invertibility of `C` give an
active zero in `X` for each fixed `r`.  Equations (4.5), together with
`D(X) contained in (9/10,19/20)`, give all four strict inactive inequalities.

The support and contraction facts depend only on `X`, not on the rewards.
The same checked periodic compiler therefore gives the asserted unrestricted
uniform payoff for each `r`.  \(\square\)

This also gives the promised nonsingularity explanation.  At `rE`, the much
sharper inclusion (3.3) makes `Id-C*J_F(X)` a strict interval contraction;
thus the active Jacobian at the certified root is nonsingular.  The uniform
calculation (4.4) is a quantitative implicit-function enclosure which avoids
having to choose a continuous root branch.

## 5. A broader structural sufficient class

The small common radius in Theorem 4.1 is only a convenient certificate
constant.  The support word itself exposes exact unbounded directions.

For a reward coordinate write `(i,S)` for `r_i(S)`.  Define

```text
I = {(0,{1,2,3}), (0,{0,1,2,3}),
     (3,{0,1,2}), (3,{0,1,2,3})}.                     (5.1)
```

### Lemma 5.1 (four coordinates are completely invisible)

None of the four coordinates in `I` occurs in an on-path Bellman value or in
any one-player Quit/Continue endpoint for the phase word (1.1).  They may be
changed arbitrarily without changing any polynomial `F_ti`, any cyclic value,
or any Nash inequality used by the certificate.

**Proof.**  The active sets are

```text
A0={1,2}, A1={0,1,3}, A2={0,2,3}.                     (5.2)
```

On path, a realized coalition is a nonempty subset of one of these three
sets.  If player `i` deviates at a phase, the realized coalition is either a
subset of `A_t\{i}` or that subset with `i` adjoined.  No phase contains all
three opponents of player 0, so neither player-0 coordinate on `{1,2,3}` or
`{0,1,2,3}` can occur.  Likewise no phase contains all three opponents of
player 3, giving the other two coordinates in (5.1).  Every behavioral
deviation is a sequence of these same one-stage choices, so later clocks do
not introduce another coalition.  \(\square\)

### Lemma 5.2 (playerwise positive affine invariance)

Suppose a table `r` has the certificate of Theorem 1.1, with cyclic values
`V_t`.  Choose independently

```text
alpha_i>0 and beta_i in R,                              (5.3)
```

and define

```text
r'_i(S)=alpha_i*r_i(S)+beta_i                           (5.4)
```

for every nonempty coalition.  Then the same root word is a certificate for
`r'`, with cyclic values

```text
V'_t(i)=alpha_i*V_t(i)+beta_i.                          (5.5)
```

**Proof.**  At phase `t`, the immediate contribution transforms as

```text
I'_t(i)=alpha_i*I_t(i)+(1-s_t)*beta_i.
```

Substitution in the Bellman recursion proves (5.5).  Both the pure-Quit and
pure-Continue endpoints then transform by the same affine map, so their
difference is multiplied by the positive number `alpha_i`.  Active zeroes
remain zero and inactive strict negative signs remain negative.  Playerwise
opponent contraction implies absorption almost surely even after an
arbitrary unilateral deviation; hence the terminal constant `beta_i` is
indeed received with probability one.  Equivalently, the checked periodic
compiler applies directly to the transformed local data.  \(\square\)

### Theorem 5.3 (unbounded E1 certificate cylinder)

Let `rbar` be any table satisfying the visible-coordinate bounds

```text
|rbar_i(S)-rE_i(S)| <= 1/50000000
    for every (i,S) not in I.                          (5.6)
```

The four coordinates in `I` need not be specified.  Choose `alpha_i>0` and
`beta_i` arbitrarily.  On every coordinate outside `I`, set

```text
r_i(S)=alpha_i*rbar_i(S)+beta_i,                       (5.7)
```

and assign the four coordinates in `I` arbitrary real values.  Then `r` has
an exact absorbing period-three Nash--Bellman block on (1.1), and therefore
an unrestricted terminal uniform-equilibrium payoff.

**Proof.**  Give the unspecified coordinates of `rbar` their E1 values.
Theorem 4.1 produces the exact block.  Lemma 5.2 applies (5.7), and Lemma 5.1
then permits the four arbitrary overwrites.  \(\square\)

This is an unbounded structural class, rather than a slightly optimized
ball.  It permits arbitrary independent payoff origins and positive scales,
and four individual reward coordinates are wholly free.

### Proposition 5.4 (reusable interval-face criterion)

More generally, fix any finite phase-support word, a rational hazard box `X`,
contained in the strict unit cube for its active hazards and having positive
one-cycle absorption throughout, and a rational invertible matrix `C` whose
size is the number of active hazards.  Form the cleared active gap vector
`F_r` as in (2.2).  If

```text
C*F_r is negative on every lower coordinate face of X,
C*F_r is positive on every upper coordinate face of X,              (5.8)
```

and every inactive cleared gap is negative throughout `X`, then `r` has an
exact cyclic Nash--Bellman block on that support.  If in addition every
player faces a positive opponent hazard somewhere in the word, its initial
cyclic value is an unrestricted terminal uniform-equilibrium payoff.

All conditions are finite strict inequalities.  For a fixed rational box,
the face signs may be proved by rational interval arithmetic as above, or by
requiring the corresponding tensor Bernstein coefficients to have one sign.
Because `F_r` is linear in the reward table, the Bernstein version is a
finite system of strict rational linear inequalities in the reward
coordinates.  It therefore defines an explicit open polyhedral certificate
chamber suitable for exact screening, not merely a numerical root locator.

**Proof.**  Poincare--Miranda applied to `C*F_r` gives an active zero in `X`.
Invertibility of `C` makes it a zero of `F_r`.  The inactive signs give the
remaining root-Nash inequalities.  The final assertion is exactly the
playerwise contraction hypothesis and conclusion of the checked periodic
compiler.  \(\square\)

## 6. Scope, reproducibility, and next check

This theorem closes an explicit open neighborhood of one rational table.  It
does not prove that a period-three block exists for every Fin4 table, and it
does not make absence in any numerical support search into evidence of a
positive lower gap.

The exact calculation is reproducible by evaluating (2.1)--(2.3) with
fractions, forward interval derivatives, the box (3.1), the matrix (3.2), and
for Theorem 4.1 the sixty independent intervals (4.3).  No floating-point
inequality is part of the proof.  A useful independent check is to reconstruct
the twelve `F_ti` directly from the table, verify (3.3)--(3.4) and
(4.4)--(4.5), and check the Quit-minus-Continue orientation.

Sources inspected:

* `notes/CODEX_NEGATIVE_CERTIFICATE__ASYMMETRIC_STATIONARY_SEAM_CLOSURE.md`,
  especially (D1), (E1)--(E10), and its stated residual screen;
* `UniformEquilibrium/Quitting/Examples/SolanVieilleBoundaryTable.lean`, for
  the undeformed reward table; and
* `UniformEquilibrium/Quitting/Cycles/PeriodicCompiler.lean`, especially
  `isUniformEquilibriumPayoff_quittingCyclicTerminalValue_of_certificate`.
