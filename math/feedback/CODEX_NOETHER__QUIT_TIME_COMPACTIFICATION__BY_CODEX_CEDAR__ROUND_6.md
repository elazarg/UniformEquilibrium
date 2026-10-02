# Round 6 feedback on quit-time compactification

Reviewer: `CODEX_CEDAR`

Reviewed note: `notes/CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION.md`

Scope: Section 24, Proposition 22 only (the stabilized arbitrary-baseline
polyhedral full-core slice).

Status: `VALID_ORDINARY_MATHEMATICS; LEAN_OVERLAP_STATUS_UNRESOLVED`

## Claim checked

For `Player=Fin 4`, let `M=FullCoreDeadlock.deadlockMatrix`, choose arbitrary
`s in R^4`, impose singleton rows

`r({j})_i=s_i+M(i,j)`,

the joint row `r({1,3})=s`, and the eight displayed weak caps `(C)`.  The claim
is that the rational three-phase product block with supports
`{0},{2},{1,3}`, hazards

`(p_0,p_1,p_2,p_3)=(4/21,1/15,7/17,5/26)`,

and values

`X^J=s+(7/10,0,0,0)`,

`X^2=s+(0,7/17,0,7/17)`,

`X^0=s+(0,5/7,8/21,1/7)`

is an exact `IsQuittingBlockCertificate`.  The checked block consumer then
gives fixed target `X^0` against all unilateral behavioral deviations.

Before review I refreshed the conference filenames and inspected:

- `deadlockMatrix`, `IsFullCoreDeadlockCompletion`, and the normal-core facts
  in
  `UniformEquilibrium/Quitting/Classification/LCP/FullCore/DeadlockChargedReturn.lean`;
- `normalizedSoloMatrix_eq_projectiveLCPMatrix`
  in `UniformEquilibrium/Quitting/Classification/LCP/Normalization.lean`;
- `IsQuittingBlockCertificate` and
  `isUniformEquilibriumPayoff_of_isQuittingBlockCertificate`
  in `UniformEquilibrium/Quitting/Cycles/BlockPeriodicProfile.lean`; and
- the externally added file containing the candidate declaration
  `reward_isUniformEquilibriumPayoff_jointBlock`,
  `UniformEquilibrium/Quitting/Classification/LCP/FullCore/DeadlockJointBlockEquilibrium.lean`.

No Lean build was run.  The coordinator reports that the externally added
literal-table file is untracked, unimported, and failed its last narrow check;
it is therefore not evidence of a Lean-checked or integrated theorem.
Proposition 22 itself is also not checked in Lean here.

## 1. Singleton-family adapter

The matrix is

```text
M = [ 0  3 -1  3
      2  0  1 -3
      2 -2  0 -1
     -1 -2  1  0 ].
```

Because `M(i,i)=0`, the imposed rows have own solo payoff
`r({i})_i=s_i`.  The projective singleton matrix is therefore

`r({j})_i-r({i})_i=M(i,j)`.

Thus `normalizedSoloMatrix_eq_projectiveLCPMatrix` gives exactly
`normalizedSoloMatrix r=M`, i.e. `IsFullCoreDeadlockCompletion r`.
Conversely every completion with normalized matrix `M` has this singleton
form after taking `s_i=r({i})_i`.  This is the ordinary adapter equality; the
arbitrary nonsingleton caps are additional hypotheses and are not consequences
of the named matrix fact.

## 2. Exact recursions

The two solo recursions check directly from

`M(*,2)=(-1,1,0,1)` and `M(*,0)=(0,2,2,-1)`:

```text
(7/17)M(*,2)+(10/17)(7/10,0,0,0)
  =(0,7/17,0,7/17),

(4/21)M(*,0)+(17/21)(0,7/17,0,7/17)
  =(0,5/7,8/21,1/7).
```

At the joint phase the four exact event masses are

```text
P({1})   = 7/130 = 21/390,
P({3})   = 7/39  = 70/390,
P({1,3}) = 1/78  = 5/390,
P(empty) = 49/65 = 294/390.
```

They sum to one.  Subtracting `s`, coordinate `0` is
`3(21+70)/390=273/390=7/10`; coordinate `2` is

`-2(7/130)-7/39+(49/65)(8/21)=0`.

Coordinates `1` and `3` are zero because the two active endpoint values below
are both exactly their baselines.  Hence the joint successor is precisely
`X^J`.

Coordinatewise translation by arbitrary `s` is legitimate: the absorbing
event masses plus the continuation mass sum to one at every phase.  No sign
assumption on `s` is used.

## 3. Four active indifferences

All active hazards are strictly between zero and one, so their two endpoint
values must agree.

- At the solo-`0` phase, Quit gives `s_0` and Continue gives
  `X^2_0=s_0`.
- At the solo-`2` phase, Quit gives `s_2` and Continue gives
  `X^J_2=s_2`.
- At the joint phase, player `1` gets `s_1` from Quit whether player `3`
  Quits or Continues, because both `r({1})_1` and `r({1,3})_1` equal `s_1`.
  Continue has excess
  `(5/26)(-3)+(21/26)(5/7)=0`.
- Symmetrically player `3` gets `s_3` from Quit, while Continue has excess
  `(1/15)(-2)+(14/15)(1/7)=0`.

Thus the active complementarity fields are exact, not approximate.

## 4. Eight inactive caps and exhaustiveness

At phase `0`, a zero-hazard spectator `i`'s forced-Q value is

`q_0 s_i+p_0 r({0,i})_i`.

Comparing with `X^0_i` gives respectively

```text
r({0,1})_1-s_1 <= 15/4,
r({0,2})_2-s_2 <= 2,
r({0,3})_3-s_3 <= 3/4.
```

At phase `2`, comparison with `X^2` gives

```text
r({0,2})_0-s_0 <= 0,
r({1,2})_1-s_1 <= 1,
r({2,3})_3-s_3 <= 1.
```

At the joint phase, inactive player `i`'s forced-Q value uses weights
`294,21,70,5` over its singleton, the two pair collisions, and the triple
collision.  Subtracting the baseline and multiplying by `390` gives exactly

```text
21[r({0,1})_0-s_0]+70[r({0,3})_0-s_0]
  +5[r({0,1,3})_0-s_0] <= 273,

21[r({1,2})_2-s_2]+70[r({2,3})_2-s_2]
  +5[r({1,2,3})_2-s_2] <= 0.
```

These are all inactive endpoint comparisons: there are three spectators at
each solo phase and two at the joint phase.  Every other nonsingleton reward
coordinate is absent from both the on-path recursions and every unilateral
one-stage endpoint.  Therefore `(C)` is necessary and sufficient for this
fixed hazard/value block once the singleton and `{1,3}` equalities are fixed.

The sharpness qualification is correct.  Violating one of the first six caps
directly makes its unique spectator gain positive.  For either joint cap,
increasing any one of its three displayed coordinates through the boundary,
while holding the other data fixed, makes that joint-phase spectator gain
positive.  This is necessity only for this supplied block, not for other
profiles or certificates.

## 5. Box, absorption, and admissibility

All hazards are rational interior probabilities.  In particular phase `0`
already has positive absorption, and the one-period continuation probability
is strictly below one.

For each player there is a positive hazard owned by an opponent in the cycle:
player `0` sees player `2`; players `1,2,3` see player `0` (with many other
choices also available).  Hence the player-deleted one-turn survival product
is strictly below one for every coordinate.  The first admissibility branch
of `IsQuittingBlockCertificate` applies.  This remains valid for arbitrary
negative baselines; no nonnegative-solo shortcut is being used.

The displayed closed recurrence has one-turn survival below one and therefore
equals the eventual absorbing payoff expectation of the repeated product
cycle.  It is a convex combination of raw terminal reward coordinates, so
each displayed value lies between their minimum and maximum and has absolute
value at most `quittingRewardBound`.  This proves `box` even when `s` or unused
raw coordinates are arbitrarily large in either direction.

The path closes by construction, and the generic checked consumer covers all
unilateral behavioral strategies with the one fixed target `X^0`; it is not a
one-shot-deviation-only conclusion.

## 6. Boundary witness and current novelty

The proposed witness `s=(1,1,1,1)`, all nonsingleton coordinates equal to one
except `r({0,1,2,3})_0=10`, satisfies every cap with left side zero.  Own solo
payoffs are one, while the grand-coalition reward of member `0` is ten.  Thus
`QuittingCappedJointExit` and the derived weak solo-exit preference fail.  The
grand-coalition coordinate is genuinely unused by this block.  This is a
valid strict non-subsumption witness against that named capped-joint producer.

The mathematical overlap is with the already reviewed ordinary-mathematics
literal-table packet of Proposition 20.  An externally added Lean file now
contains a candidate formalization of that packet, but its current checked and
integration status is unresolved for the reasons stated above and it must not
be cited as a proved declaration.  In either status, that literal packet does
not state Proposition 22's arbitrary-baseline polyhedral adapter: the literal
table has baseline `s=1` but row `r({1,3})=0`, whereas Proposition 22 requires
that row to equal `s`.  The rational hazards here also differ from the literal
packet's algebraic block.

Therefore Proposition 22 remains a distinct nonlocal raw-table adapter, but
it is not new bare existence for the deadlock matrix or the literal named
table.  Its honest novelty is: a supplied rational block for a separate,
unbounded polyhedral slice of completions sharing the same normalized
singleton matrix.  No claim of exclusion from every other producer has been
established.

## Verdict

Proposition 22 is valid ordinary mathematics with exact quantifiers.  I found
no boundary falsifier: arbitrary negative baselines are handled by deleted-
clock admissibility, arbitrary unused coordinates only enlarge the reward
box, and the eight caps exactly exhaust the fixed certificate's inactive
conditions.  The checked consumer supplies the literal fixed target against
all behavioral deviations.

Before any export or formalization handoff, frame Proposition 22 as the
distinct rational polyhedral adapter beyond the accepted literal-table
ordinary-mathematics packet, and independently resolve the status of the
external candidate Lean file.  No `L` or new actual-data `A` seal is supplied
by this review.
