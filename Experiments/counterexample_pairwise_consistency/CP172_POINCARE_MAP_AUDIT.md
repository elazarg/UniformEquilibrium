# Exact audit of the four-player Poincare construction in `172-Answer-GP`

## Verdict

The displayed return map, invariant ray, positive fixed point, four hazards,
and four advertised continuation-surplus thresholds are all correct.  The
construction can be completed to a fully specified rational quitting game in
which the claimed period-four profile is an exact equilibrium and its cyclic
annotations are its actual infinite-horizon terminal payoffs.

There is one important qualification.  The answer does **not** display a full
reward table: it specifies four ordered pair bonuses and says that all other
bonuses should be "sufficiently low."  It also leaves pair-spectator and
larger-coalition rewards open.  Thus there is no unique answer table to audit.
This experiment supplies one explicit completion and proves that the answer's
existence claim is valid for that completion.

No mathematical inconsistency was found among displayed formulas (8)--(15).
The `===` in the display preceding (12) is only a Markdown/typographical
artifact.  The incomplete off-path reward specification is the sole
substantive defect in the presentation.

The result is a solved-game regression, not a counterexample.  It refutes the
inference that a summable phantom Bellman tail plus a robust singleton blocker
already rules out equilibrium.  It does not refute the target existence
theorem, establish terminal instability, or close Question 172.

The executable certificate is
[`poincare_four_phase_audit.py`](poincare_four_phase_audit.py).  It uses only
the Python standard library.  Its general identities are checked in the exact
rational-function field `Q(a,b)`; its fixed-point claims are checked in the
exact quadratic field `Q(sqrt(889))`.  Decimal output is diagnostic only.

## Exact reconstruction of the return map

Rows of the singleton excess matrix are payoff recipients and columns are
singleton owners:

```text
E = [  0    -1/3    2/3    2/3 ]
    [ 2/3     0       1     -1  ]
    [-1/3    2/3      0      1  ]
    [  1     2/3   -2/3     0   ].
```

Writing `z = v - 1`, a phase in which only owner `j` quits with probability
`q` obeys

```text
z = (1-q) z' + q E[:,j].
```

Set

```text
D0 = 2 - 3a,
D1 = 4 + 3a - 6b,
D3 = 4 - 5a - 2b,
D4 = 8 + 15a - 18b.
```

Starting from `z0 = (0,a,0,b)`, exact elimination along owners
`0 -> 1 -> 3 -> 2 -> 0` gives:

```text
q0 = 3a/2,
z1 = (0, 0, a/D0, (2b-3a)/D0),

q1 = 3(2b-3a)/(2D0),
z2 = ((2b-3a)/D1, 0, 4(2a-b)/D1, 0),

q3 = 4(2a-b)/D1,
z3 = ((14b-25a)/(3D3), 4(2a-b)/D3, 0, 0),

q2 = (14b-25a)/(2D3),
z4 = (0, (41a-22b)/D4, 0,
          2(-25a+14b)/(3D4)).
```

The probe verifies all sixteen coordinates of the four Bellman equations by
cross multiplication in `Q(a,b)`.  The formulas are identities wherever the
displayed phase denominators are nonzero.  In particular, the answer's map is
exactly

```text
F(a,b) = ((41a-22b)/D4, 2(-25a+14b)/(3D4)).
```

No phase denominator vanishes at the positive fixed point below.

## Invariant ray, local branch, and positive fixed point

For `b = rho*a`, invariance of the ray cancels to

```text
2(-25+14rho) = 3rho(41-22rho),
```

equivalently

```text
66rho^2 - 95rho - 50 = 0.
```

The positive root is exactly

```text
rho = (95 + 5 sqrt(889))/132.
```

The audit checks both the quadratic equation and the cancelled invariance
identity in `Q(sqrt(889))`.  On this ray,

```text
a+ / a = (41-22rho)/(8 + (15-18rho)a).
```

For an explicit exact local fence, the probe verifies

```text
0 < (41-22rho)/8
  < (41-22rho)/(8 + (15-18rho)/100)
  < 1/10,
25/14 < rho < 2,
```

and verifies that all four phase hazards at `a=1/100` lie in `(0,1)`.
The rational hazard functions are increasing near zero, so the same holds for
`0 < a <= 1/100`; the displayed ratio gives geometric decay.  Consequently
the four hazards are `O(a)` and their cycle-by-cycle total is summable.  This
last monotonicity/summability sentence is an elementary analytic consequence
of the exact rational formulas; it is not separately encoded as a quantified
theorem in the probe.

The nonzero fixed point is

```text
a* = (517 - 11 sqrt(889))/450,
b* = (1 + 7 sqrt(889))/270.
```

The probe checks exactly that `b* = rho*a*`, that both coordinates are
positive, and that `F(a*,b*) = (a*,b*)`.  The hazards, in owner order
`0,1,3,2`, simplify to

```text
q0 = 517/300   - (11/300) sqrt(889),
q1 = 16/9      - (5/126)  sqrt(889),
q3 = 12209/14424 - (205/14424) sqrt(889),
q2 = 241/60    - (7/60)   sqrt(889).
```

Exact sign comparison proves every hazard lies strictly between zero and one.
The answer's decimal values agree:

```text
rho = 1.849094811809...
a*  = 0.420050814779...
b*  = 0.776713782305...
(q0,q1,q3,q2)
    = (0.630076222169..., 0.594599086042...,
       0.422677404222..., 0.538121312962...).
```

These decimal values are not used by any assertion.

## One full rational reward table

For singletons, set `r_i({j}) = 1 + E_ij`.  For a pair containing player `i`
and owner `j`, write

```text
beta_(i,j) = r_i({i,j}) - r_i({j}).
```

Use the four bonuses from the answer,

```text
beta_(2,0)=1/6, beta_(0,1)=1/6,
beta_(1,3)=1/2, beta_(3,2)=1/3,
```

and set every other ordered joining bonus to `0`.  Pair spectators and all
coordinates of coalitions of size at least three are set to zero.  This gives
the complete table:

```text
quitters       rewards to players (0,1,2,3)
{0}            (1,     5/3,   2/3,   2)
{1}            (2/3,   1,     5/3,   5/3)
{2}            (5/3,   2,     1,     1/3)
{3}            (5/3,   0,     2,     1)

{0,1}          (5/6,   5/3,   0,     0)
{0,2}          (5/3,   0,     5/6,   0)
{0,3}          (5/3,   0,     0,     2)
{1,2}          (0,     2,     5/3,   0)
{1,3}          (0,     1/2,   0,     5/3)
{2,3}          (0,     0,     2,     2/3)

{0,1,2}        (0,0,0,0)
{0,1,3}        (0,0,0,0)
{0,2,3}        (0,0,0,0)
{1,2,3}        (0,0,0,0)
{0,1,2,3}      (0,0,0,0)
```

Every coordinate of this completion lies in `[0,2]`.  The zero unspecified
bonuses are not canonical, but they are already low enough for every outsider
constraint and avoid enlarging the reward box.

## Exact Nash audit

At a phase owned by `j`, the owner's next continuation excess is zero.  Hence
its Continue endpoint and Quit endpoint both equal `1`; every mixing support
equality is exact.

For outsider `i`, Continue gives the Bellman value while immediate Quit gives

```text
(1-q)*r_i({i}) + q*r_i({i,j}).
```

Since `r_i({i})=1`, exact subtraction gives

```text
Continue - Quit
  = (1-q) z'_i - q beta_(i,j)
  = q [ ((1-q)z'_i/q) - beta_(i,j) ].
```

Thus the answer's threshold is exactly the outsider Nash condition, with no
missing term.  At the fixed point, all twelve thresholds are:

```text
owner 0: i=1 -> 0
         i=2 -> 1/3                         [blocker]
         i=3 -> (-103 + 5 sqrt(889))/198

owner 1: i=0 -> 1/3                         [blocker]
         i=2 -> (-73 + 5 sqrt(889))/264
         i=3 -> 0

owner 3: i=0 -> (-55 + 5 sqrt(889))/192
         i=1 -> 1                           [blocker]
         i=2 -> 0

owner 2: i=0 -> 0
         i=1 -> (-19 + sqrt(889))/30
         i=3 -> 2/3                         [blocker].
```

Every displayed threshold is exactly nonnegative.  The four positive bonuses
are strictly below their thresholds, and all other bonuses are zero.
Therefore all twelve outsider inequalities hold: the four zero-threshold
outsiders are indifferent and the other eight inequalities are strict.
Together with the four support equalities, this checks every player at every
phase.

The designated joiners also strictly destabilize every pure singleton exit:

```text
owner 0, joiner 2: watching 2/3, pair 5/6;
owner 1, joiner 0: watching 2/3, pair 5/6;
owner 3, joiner 1: watching 0,   pair 1/2;
owner 2, joiner 3: watching 1/3, pair 2/3.
```

In fact the same joiner is profitable against every stationary owner rate if
one ignores continuation surplus: at owner rate zero its own singleton reward
`1` strictly beats watching, and at owner rate one the positive pair bonus
strictly beats watching.  This is the robust singleton-blocking property.

## Annotations are actual periodic terminal payoffs

Let `d_k = 1-q_k` and let `P = d_0 d_1 d_3 d_2`.  Exact hazard bounds give
`0 < P < 1`, so the period-four profile absorbs almost surely.  Starting at
phase zero, the actual terminal payoff to player `i` is

```text
[q0 r_i({0})
 + d0 q1 r_i({1})
 + d0 d1 q3 r_i({3})
 + d0 d1 d3 q2 r_i({2})] / (1-P).
```

The analogous formulas hold after cyclic rotation.  The executable audit
computes these geometric sums in `Q(sqrt(889))` and proves all sixteen
identities

```text
actual payoff at phase k to player i = 1 + z^k_i.
```

Therefore the annotations used in the one-stage Nash checks are not phantom
values.  They are the profile's genuine continuation payoffs.  Since the only
nonterminal public history advances to the next phase, the four exact local
best-response checks establish the periodic strategy profile as an exact
equilibrium (indeed, the same checks apply after every continuation history).
There is no hidden one-stage-deviation-principle boundary issue here: even if
one deviator suppresses all of its own prescribed quitting, the other three
owners retain positive hazards and give a strict geometric survival factor
over every four-date block.  The probe verifies this bound exactly for each
possible deviator, so bounded arbitrary deviations follow from the finite
dynamic inequalities by passage to the limit.

## What the regression establishes

The production singleton module already proves that this excess matrix has a
strictly positive normalized source packet and no complementary singleton
probability satisfying its row conditions.  This audit does not duplicate
that result.  It adds the missing dynamic fact:

1. the local invariant branch supports a geometrically shrinking, summable
   phantom Bellman skeleton;
2. the same branch has a positive global Poincare fixed point;
3. pair rewards can block all singleton locks without breaking the fixed
   point's outsider incentives; and
4. the fixed point is an actual absorbing periodic equilibrium.

Accordingly, "singleton noncomplementarity + summable phantom branch + strict
singleton joiners" is not a sufficient counterexample criterion.  A valid
counterexample argument must also rule out nonlinear periodic closures (or
otherwise show why their annotations cannot be realized).

## Promotion recommendation

Do not promote the game-specific map or this particular zero-bonus completion yet.
They are valuable as an isolated solved-game regression, but no production
consumer currently needs their large exact witness.

The only plausibly reusable statement is the one-owner outsider identity

```text
Continue - Quit = (1-q)z'_i - q beta_(i,j),
```

together with its `q>0` threshold form.  It is elementary and should be
promoted only if a later dynamic-root module needs it as an API; otherwise a
new theorem would add more surface area than leverage.  The singleton
noncomplementarity facts and phantom-boundary identities are already in
production and should not be duplicated.

## Reproduction

From the repository root:

```text
python -B Experiments/counterexample_pairwise_consistency/poincare_four_phase_audit.py
```

The expected result is three `PASS` lines, exact radical data, the four
advertised thresholds, and the complete reward table above.
