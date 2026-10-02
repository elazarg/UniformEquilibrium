# C172 designated-joiner candidate lies in an exact periodic-equilibrium chamber

**Identity:** `CODEX_NEGATIVE_CERTIFICATE`  
**Status:** proved in exact ordinary mathematics; finite radical certificate,
not instantiated in Lean  
**Conjecture impact:** excludes the only explicit filter-grade rational table in
the C172 candidate review, and an exact 44-dimensional relative chamber
containing it, from the Fin4 counterexample search.  Of those 44 coordinates,
32 are completely irrelevant to the certificate and 12 are constrained only
by the displayed ordered-pair inequalities.

## Question

Does the rational four-player table retained in
`Experiments/counterexample_pairwise_consistency/C172_CANDIDATE_REVIEW.md`
admit a fixed positive terminal exploitability gap against every behavioral
profile?

The required negative certificate would have to cover arbitrary behavioral
stopping rules, including Never and arbitrarily late quitting.  Failure of a
stationary or bounded-period grid is not such a certificate.

The answer for this table is **no**.  It has an exact absorbing period-four
terminal Nash profile against unrestricted behavioral deviations.  The four
phases lie on boundary faces: only owners `0,1,3,2`, in that order, mix in
their respective phases.  The hazards are algebraic in
`Q(sqrt(889))`.  Truncating after whole cycles also gives explicit finite-clock
profiles whose all-behavior exploitability tends geometrically to zero.

The proof actually excludes a class.  Keep the C172 singleton rows fixed.  At
each phase, only the ordered pair coordinate paid to a unilateral joining
outsider enters its deviation payoff.  Every table whose twelve ordered pair
increments lie below the threshold table below has the same exact
periodic equilibrium.  Pair-spectator coordinates and all coordinates of
coalitions of cardinality at least three are arbitrary.

## Exact table under audit

Rows are indexed by the quitting coalition, and coordinates by players
`0,1,2,3`:

```text
{0}       (1,     5/3,   2/3,   2)
{1}       (2/3,   1,     5/3,   5/3)
{0,1}     (11/12, 1/2,   1/8,   1/8)
{2}       (5/3,   2,     1,     1/3)
{0,2}     (1/2,   1/8,   11/12, 1/8)
{1,2}     (1/8,   1/2,   1/2,   1/8)
{0,1,2}   (0,     0,     0,     1/8)
{3}       (5/3,   0,     2,     1)
{0,3}     (1/2,   1/8,   1/8,   1/2)
{1,3}     (1/8,   1/4,   1/8,   1/2)
{0,1,3}   (0,     0,     1/8,   0)
{2,3}     (1/8,   1/8,   1/2,   7/12)
{0,2,3}   (0,     1/8,   0,     0)
{1,2,3}   (1/8,   0,     0,     0)
{0,1,2,3} (0,     0,     0,     0)
```

The reward bound is `M=2`.

## Sources and declarations inspected

The exact target and negative endpoint were read in:

* `quittingUniformEquilibriumPayoffConjecture` in
  `UniformEquilibrium/Quitting/Conjecture/Basic.lean`;
* `HasTerminalExploitabilityGap` and
  `not_exists_uniformEquilibriumPayoff_iff_exists_terminalExploitabilityGap`
  in `UniformEquilibrium/Quitting/Terminal/ExploitabilityGap.lean`.

The unrestricted cyclic consumer is:

* `QuittingCyclicRepairCertificate`,
  `QuittingCyclicRepairCertificate.isZeroAsymptoticNash`, and
  `QuittingCyclicRepairCertificate.isUniformEquilibriumPayoff` in
  `UniformEquilibrium/Diagnostics/Quitting/ExactRepairCertificate.lean`.

The exact singleton orbit was compared with the rational-function and
quadratic-field audit in
`Experiments/counterexample_pairwise_consistency/poincare_four_phase_audit.py`
and its report `CP172_POINCARE_MAP_AUDIT.md`.  The C172 table is different from
that report's chosen collision completion; the candidate-specific content
below is the fresh check of all twelve pair-deviation coordinates.

Search context was taken from
`CODEX_DESCENDANT__SCREENED_HARD_RATIONAL_NEGATIVE_SEARCH.md`,
`CODEX_DESCENDANT__TRACKED_CORPUS_ALTERNATING_PAIR_EQUILIBRIA.md`, and the
exact finite-clock search contract in
`questions/ESCAPE_AWARE_FIN4_CERTIFICATE_SEARCH.md`.  No literature theorem is
used.

## The algebraic orbit

Put `s=sqrt(889)` and

```text
a = 517/450 - (11/450)s,
b = 1/270   + (7/270)s.
```

Both are positive.  Starting from excess state

```text
z0 = (0,a,0,b),
```

apply singleton owners `0,1,3,2`.  The four hazards are

```text
q0 = 517/300     - (11/300)s,
q1 = 16/9        - (5/126)s,
q3 = 12209/14424 - (205/14424)s,
q2 = 241/60      - (7/60)s.
```

Exact square comparison using `29<s<30` proves `0<qj<1` for all four
owners.  Numerically, only for orientation,

```text
(q0,q1,q3,q2)
  = (0.630076222..., 0.594599086..., 0.422677404..., 0.538121313...).
```

For completeness, the rational return calculation starts from arbitrary
`(a,b)` and writes

```text
D0 = 2 - 3a,
D1 = 4 + 3a - 6b,
D3 = 4 - 5a - 2b,
D4 = 8 + 15a - 18b.
```

The successive excess states and hazards are

```text
z0 = (0,a,0,b),
q0 = 3a/2,
z1 = (0,0,a/D0,(2b-3a)/D0),

q1 = 3(2b-3a)/(2D0),
z2 = ((2b-3a)/D1,0,4(2a-b)/D1,0),

q3 = 4(2a-b)/D1,
z3 = ((14b-25a)/(3D3),4(2a-b)/D3,0,0),

q2 = (14b-25a)/(2D3),
z4 = (0,(41a-22b)/D4,0,
        2(-25a+14b)/(3D4)).
```

The displayed algebraic `(a,b)` satisfies `z4=z0`.  Every coordinate identity
is an identity over `Q(a,b)` after clearing the displayed denominators.  With
`v^k = 1 + z^k`, the four equations are exactly

```text
v^k = (1-q_owner) v^(k+1) + q_owner r({owner}).
```

Thus the annotations obey the literal cyclic policy recursion for the C172
singleton rows.

## Theorem 1: exact collision chamber

For an outsider `i` at the phase owned by `j`, define its ordered joining
increment

```text
beta_(i,j) = r_i({i,j}) - r_i({j}).
```

Since every own singleton reward is one, immediate Quit gives

```text
(1-qj) + qj r_i({i,j}).
```

Continue gives the policy value.  Subtracting and using the singleton Bellman
identity gives the exact formula

```text
Continue - Quit
  = (1-qj) z^(k+1)_i - qj beta_(i,j)
  = qj (theta_(i,j) - beta_(i,j)),

theta_(i,j) = (1-qj) z^(k+1)_i / qj.
```

The twelve thresholds and the C172 increments are:

| owner `j` | outsider `i` | `theta_(i,j)` | C172 `beta_(i,j)` |
|---|---:|---:|---:|
| 0 | 1 | `0` | `-7/6` |
| 0 | 2 | `1/3` | `1/4` |
| 0 | 3 | `(-103+5s)/198` | `-3/2` |
| 1 | 0 | `1/3` | `1/4` |
| 1 | 2 | `(-73+5s)/264` | `-7/6` |
| 1 | 3 | `0` | `-7/6` |
| 3 | 0 | `(-55+5s)/192` | `-7/6` |
| 3 | 1 | `1` | `1/4` |
| 3 | 2 | `0` | `-3/2` |
| 2 | 0 | `0` | `-7/6` |
| 2 | 1 | `(-19+s)/30` | `-3/2` |
| 2 | 3 | `2/3` | `1/4` |

All twelve inequalities are strict.  In particular the four positive
designated-joiner increments are still below the orbit's continuation
surplus.  Multiplying by the positive hazards gives the exact outsider
slacks:

```text
owner 0, i=1:  3619/1800 - (77/1800)s
owner 0, i=2:   517/3600 - (11/3600)s
owner 0, i=3:  4673/5400 + (41/5400)s

owner 1, i=0:     4/27 - (5/1512)s
owner 1, i=2:   395/432 - (5/3024)s
owner 1, i=3:    56/27 - (5/108)s

owner 3, i=0: 12001/28848 + (275/28848)s
owner 3, i=1: 12209/19232 - (205/19232)s
owner 3, i=2: 12209/9616  - (205/9616)s

owner 2, i=0:  1687/360 - (49/360)s
owner 2, i=1:    43/1800 + (59/1800)s
owner 2, i=3:   241/144 - (7/144)s.
```

Every sign follows immediately from `29<s<30`; no decimal comparison is used.
The active owner is indifferent because its current and successor excess
coordinates are zero and its singleton payoff is one.  Hence every root is
exact Nash against its displayed next value.

This proves the promised chamber statement: the same conclusion holds for
every reward table with these singleton rows and
`beta_(i,j) <= theta_(i,j)` for the twelve displayed ordered pairs.  A
unilateral deviation from a one-owner phase can create only `{i}` or `{i,j}`.
Therefore no pair-spectator coordinate and no reward at a coalition of size at
least three enters the proof.

## Theorem 2: unrestricted behavioral equilibrium and late clocks

For each deviator, suppressing that player's prescribed hazard leaves three
positive owner hazards in every complete cycle.  The exact opponent-survival
products are

```text
h0 = -5/3       + (5/84)s,
h1 = -7427/4808 + (265/4808)s,
h2 = -473/1080  + (19/1080)s,
h3 = -13841/1200 + (467/1200)s.
```

Exact square comparison gives

```text
0 < hi < 1/9
```

for all four players.  Thus the unilateral phase-indexed stopping problem is
a strict contraction even if the deviator never uses its own prescribed Quit
dates.  The four local Nash inequalities iterate to every deterministic
stopping time, including stops after arbitrarily many cycles and Never.
Pure-time extremality then covers every randomized behavioral replacement.

Equivalently, the displayed data satisfy every field of the checked theorem
schema `QuittingCyclicRepairCertificate`.  Its theorems
`isZeroAsymptoticNash` and `isUniformEquilibriumPayoff` show exactly what a Lean
instantiation would conclude.  The present note is an ordinary exact proof,
not a claim that this candidate-specific certificate has already been entered
in Lean.

There is also an explicit finite-clock sequence.  After `L` complete cycles,
move all later stopping mass of every prescribed player to Never.  For each
fixed unilateral deviation of player `i`, couple the original and truncated
profiles through that prefix.  The disagreement event has probability at most
`hi^L < 9^(-L)`, uniformly in the deviation.  The prescribed payoff bound
follows from the analogous full-profile coupling; taking the supremum only
after the playerwise deviation bound gives the cap estimate.  Thus the cap is
not itself being treated as an event.  Since `M=2`, the safe bounds are

```text
|U_i^L-U_i| <= 4 * 9^(-L),
|B_i^L-B_i| <= 4 * 9^(-L),
Expl(profile_L) <= 8 * 9^(-L).
```

This is an all-behavior cap estimate.  In particular, it includes deviations
whose profitable date would lie after the truncation clock; it is not a finite
deviation-menu check.  The finite profiles deliver the same limiting phase
payoff selected by the exact periodic profile.

Consequently the C172 table has exploitability infimum zero and cannot satisfy
`HasTerminalExploitabilityGap` at any positive gap.

## Boundary and stationary audit

These finite witnesses are not needed after Theorem 2, but they record the
screens a negative search must not omit.

The best pure boundary profile among the sixteen `0/1` stationary roots is

```text
q = (0,1,1,1),
U = (1/8,0,0,0),
B = (1/8,1/8,1/8,1/8),
debt = (0,1/8,1/8,1/8).
```

So pure-boundary testing alone leaves an apparent `1/8` floor.

An exact interior stationary witness is

```text
q = (3/1024, 13/512, 1/256, 5/1024).
```

Its prescribed payoff is

```text
(27907902413/30320296302,
 10304726253/10106765434,
 15677843757/10106765434,
 44177244359/30320296302),
```

and its exact unrestricted stationary caps are

```text
(533325977/536870912,
 66631/61748,
 344015443/212541732,
 78928987/51606996).
```

The maximum debt is

```text
593830313859663199 / 8139042563882483712 < 3/40 < 1/10.
```

Thus even the proposed `1/10` filter label is refuted by a rational stationary
profile once small hazards are admitted.  The default repair ladder missed it
because its positive grid begins at `1/4`; that exhaustion was correctly
reported only as a filter.  Stationary optimization is nevertheless not the
decisive result: the algebraic boundary-face period-four profile has exactly
zero unrestricted exploitability.

## Search consequence

The C172 construction deliberately gave every singleton owner a strict
joining outsider.  That is not enough to prevent a periodic closure.  The
continuation-surplus thresholds above show exactly how much joining bonus this
four-phase orbit can absorb.  In particular the common `1/4` designated bonus
lies strictly inside the safe chamber at all four marked edges.

Future candidate generation using this singleton matrix should impose at
least one strict violation

```text
beta_(i,j) > theta_(i,j)
```

on this orbit.  Violating only a marked edge is not a negative certificate—it
may open another periodic or stationary equilibrium—but retaining all twelve
weak inequalities is now an exact exclusion rule, not a heuristic penalty.

## Proved and unproved

Proved here:

* the complete C172 rational table lies in the twelve-inequality collision
  chamber;
* the explicit algebraic four-phase profile is exact Nash against all
  behavioral unilateral deviations;
* the table has a uniform-equilibrium payoff and no positive terminal gap;
* finite-clock truncations have exploitability at most `8*9^(-L)`; and
* one exact rational stationary profile already has exploitability below
  `3/40`.

Not proved here:

* no positive-gap Fin4 table exists;
* exclusion of a table violating one of the twelve thresholds;
* completeness of stationary, periodic, or finite-clock strategy classes; or
* a Lean instance for this candidate-specific algebraic certificate.

## Concrete next question

Apply the twelve exact threshold inequalities as a hard rejection screen to
the next rational hard-matrix corpus, then exactify the first survivor against
all one-owner cycles and complementary-pair cycles before launching the global
lower-tree search.  A survivor remains only a candidate; a positive lower-tree
certificate must still control arbitrary late clocks and every behavioral
replacement.
