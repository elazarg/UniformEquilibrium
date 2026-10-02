# Exact period-three uniform payoff for a stationary-free Fin4 table

Author: `CODEX_NEGATIVE_CERTIFICATE`

Independent reviews:
[CODEX_SPINOZA](../feedback/CODEX_NEGATIVE_CERTIFICATE__DEADLOCK_FIBER_EXACT_SCREEN__BY_CODEX_SPINOZA.md),
[CODEX_SNELL](../feedback/CODEX_NEGATIVE_CERTIFICATE__DEADLOCK_FIBER_EXACT_SCREEN__BY_CODEX_SNELL.md)

This is a reviewed standalone ordinary-mathematics result.  The downstream
block-profile consumer is already Lean checked; the algebraic root certificate
and the literal-table adapter below are not yet formalized.

## Exact statement

Let the players be `0,1,2,3`.  For each nonempty quitting coalition, in binary
mask order, prescribe the payoff vector

```text
 1  {0}       (1,3,3,0)
 2  {1}       (4,1,-1,-1)
 3  {0,1}     (1,1,1,-2)
 4  {2}       (0,2,1,2)
 5  {0,2}     (1,4,1,1)
 6  {1,2}     (3,1,1,0)
 7  {0,1,2}   (1,1,1,-1)
 8  {3}       (4,-2,0,1)
 9  {0,3}     (1,0,2,1)
10  {1,3}     (7,1,-2,1)
11  {0,1,3}   (1,1,0,1)
12  {2,3}     (3,-1,1,1)
13  {0,2,3}   (1,1,1,1)
14  {1,2,3}   (6,1,1,1)
15  {0,1,2,3} (11,-1,1,0).
```

There exist `a,b,c,d` strictly between zero and one such that the period-three
product profile

```text
q^0=(a,0,0,0),  q^1=(0,0,b,0),  q^2=(0,c,0,d)
```

is an exact admissible quitting block.  Consequently the quitting game has the
fixed uniform-equilibrium payoff

```text
v=(1, 1+2a+b-ab, 1+2a, (1-a)(1+b))
```

against every unilateral behavioral deviation.  The root is unique in the
explicit rational parallelotope below.

Separately, the [complete exact stationary-face proof](../notes/CODEX_NEGATIVE_CERTIFICATE__DEADLOCK_FIBER_EXACT_SCREEN.md)
shows that this same table has no stationary terminal Nash profile.  That
stationary claim has already passed independent correction audit; the present
packet does not repeat or use it in proving the positive result.

## Conjecture-facing change

This table was the first exact survivor in the negative search after the
balanced-singleton, named rational-block, pure-coalition, pair, and complete
stationary-face screens.  The result closes it positively by an exact
nonstationary block with a fixed target and unrestricted behavioral consumer.
It therefore removes this literal candidate from the counterexample search
and proves, on exact data, that stationary nonexistence plus those earlier
screens does not reach the negative semantic endpoint.  It does not produce
an arbitrary-game or whole-fibre theorem.

## Definitions and assumptions

All finite data, product probabilities, and the fixed target are those in the
exact statement above; no additional source hypothesis is assumed.

## Proof

### Algebraic root and exact isolation

Define

```text
F0= 3bc+3bd+b-3c-3d,
F1=-2acd+2ac+2ad-2a+2c+d,
F2=-abd+ab+2ad-2a+bd-b+3d,
F3=-abc+ab-ac+a+bc-b+2c.
```

Let

```text
x=(2200649139/10^10,
   4455252923/10^10,
    598923293/10^10,
    415887857/(2*10^9)),

A=[ 7/20     -323/1000   137/500    631/1000
    213/250    22/125     309/1000    59/125
     7/100    267/1000    -69/1000    23/100
    253/1000  -19/250     101/250    141/500 ],

r=1/10^6,   P={x+Az: |z_j|<=r for every j}.
```

Here

```text
det A=-41914379009/10^12,
```

and exact interval addition puts `P` inside

```text
11/50<a<23/100,  11/25<b<9/20,
 1/20<c< 3/50,    1/5 <d<21/100.                 (1)
```

Put `F=(F0,F1,F2,F3)`, `G(z)=F(x+Az)`, and `T(z)=z-G(z)`.  Exact substitution
gives

```text
F(x)=(
  1732473241/(5*10^19),
  7039082593629169961/10^29,
  12514868747864475471/(2*10^29),
 -69568260756753837021/10^30),
```

so its infinity norm is below `1/10^9`.  For each entry of `DT`, expand in
the monomial basis in `z` and replace `u z^alpha` by the upper bound
`|u|r^|alpha|`.  Summing across each row gives, exactly,

```text
14618922367/10^13,
170910873577211158347/(5*10^22),
13928416905704981571/(3125*10^18),
191805008621195199843/10^23.
```

All four are below `1/200`.  Therefore `T` is a contraction on the closed
rational cube, and for `||z||_infinity<=r`,

```text
||T(z)||_infinity
 < 1/10^9+(1/200)(1/10^6)<1/10^6.
```

Banach's theorem supplies a unique fixed point `z_*` there.  As `T(z_*)=z_*`
is equivalent to `F(x+Az_*)=0`, set `(a,b,c,d)=x+Az_*`.  This proves exact
existence, uniqueness inside `P`, and (1).

As a redundant sign check, on `z_i=-r` one has `G_i<-99/10^8`, while on
`z_i=r` one has `G_i>99/10^8`.  Exact lower margins obtained from constant,
linear cross-term, and higher-degree coefficient bounds are

```text
24962771111137/(25*10^18),
99782438672735255019833/10^29,
199877926167001860463113/(2*10^29),
999457586075568031650689/10^30,
```

each above `99/10^8`.  Thus Poincare--Miranda independently proves existence.

### Exact block verification

Define

```text
U0=(1,1+2a+b-ab,1+2a,(1-a)(1+b)),
U1=(1,1+b,1,1+b),
U2=(1+3c+3d,1,1,1),
U3=U0.
```

Expanding the literal reward table, the stage-recursion residuals are all zero
except

```text
(phase 1, player 0): F0,
(phase 2, player 1): (1-c)F2,
(phase 2, player 2): F1,
(phase 2, player 3): (1-d)F3.
```

Thus all four displayed recursions are exact at the root.  The
Quit-minus-Continue endpoint differences against the next phase are

| phase | player 0 | player 1 | player 2 | player 3 |
|---:|---:|---:|---:|---:|
| 0 | `0` | `ab-2a-b` | `-2a` | `ab+a-b` |
| 1 | `F0` | `-b` | `0` | `-b` |
| 2 | `-3(c+d)` | `F2` | `F1` | `F3` |

The positive-hazard entries have zero difference.  The inactive entries
`(phase 1,player 0)` and `(phase 2,player 2)` are structural ties.  All other
inactive entries are uniformly strict on `P`, since (1) yields

```text
ab-2a-b<-a-b<-1/2,
-2a<-2/5,
ab+a-b<(23/100)(29/20)-11/25=-213/2000<-1/10,
-b<-2/5,
-3(c+d)<-3/4.
```

This is exact endpoint complementarity, with no numerical tolerance.

All hazards are probabilities by (1), and phase zero absorbs with positive
probability.  Every coordinate of every `Uk` lies between zero and two.  The
canonical reward bound is at least `11`, the absolute value of player zero's
grand-coalition reward, so the required value box holds.  After deleting
player zero use opponent hazard `b`; after deleting any of players one, two,
or three use opponent hazard `a`.  Hence every deleted-opponent cycle absorbs,
which is the checked admissibility disjunction.

## Adapter and consumer

The literal reward table, the algebraic root selected above, the three hazards,
and the four rows form an actual-data adapter: the preceding identities are
precisely the fields of `IsQuittingBlockCertificate` for `m=2` in
`UniformEquilibrium/Quitting/Cycles/BlockPeriodicProfile.lean`.  Its checked
consumer

```text
isUniformEquilibriumPayoff_of_isQuittingBlockCertificate
```

returns `(quittingGame reward).IsUniformEquilibriumPayoff none U0`.  The
theorem's deviation class is all behavioral strategies, not merely periodic
or stopping-time deviations.  The root and `U0` are fixed before the accuracy,
profile, and eventual-horizon quantifiers.

## Source correspondence

The exact declarations read were:

* `IsQuittingBlockCertificate`, `isQuittingBlockCertificate_of_root`, and
  `isUniformEquilibriumPayoff_of_isQuittingBlockCertificate` in
  `UniformEquilibrium/Quitting/Cycles/BlockPeriodicProfile.lean`;
* `quittingRewardBound` and `abs_reward_le_quittingRewardBound` in
  `UniformEquilibrium/Quitting/RewardBound.lean`; and
* the stationary endpoint bridge declarations listed in the owned note, which
  are not needed by this positive proof.

A narrow exact-row and exact-root search found no copy of this table or root
outside the owned note.  The nearby checked
`IsDeadlockRationalJointBlockCompletion` producer uses the same support word
on a different rational polyhedral chamber; the literal table here was
constructed to violate that chamber.  The new step is the algebraic-root
producer above, not the already checked block consumer.

## Boundary tests

The root is strictly interior, the cycle and every deleted-opponent cycle
absorb, all zero hazards are audited, and the two non-strict inactive gaps are
identified rather than counted among the six strict gaps.  The independently
audited stationary exclusion is compatible with this nonstationary block.

## Lean handoff

The narrow implementation route is:

1. define the literal `Fin 4` reward table and the four polynomials;
2. define the rational center, matrix, radius, affine cube, and the selected
   zero using the proved contraction self-map;
3. prove the four rational interval bounds and the recursion/gap tables by
   finite extensionality plus polynomial normalization;
4. package those fields directly as `IsQuittingBlockCertificate` with `m=2`;
   and
5. invoke `isUniformEquilibriumPayoff_of_isQuittingBlockCertificate`.

The proof should not assume the desired block certificate as source data.  The
new Lean work is the algebraic zero and literal-table adapter; the unrestricted
consumer is already checked.

## Scope and nonclaims

No full-dimensional neighborhood follows automatically: the two inactive
ties can split under reward perturbation.  This result does not prove a
whole-fibre theorem, an arbitrary-game producer, a counterexample, or the Fin4
conjecture.  It is independently reviewed ordinary mathematics awaiting Lean
formalization of its root/data adapter.
