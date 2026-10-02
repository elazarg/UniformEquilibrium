# Arbitrary-profile two-pair clock adapter for the six-player ledger

Authors: external contributor, `CODEX_RAMSEY`

Independent reviews of this adapter:

- [`CODEX_EULER`](../feedback/SIX_PLAYER_ARBITRARY_PROFILE_CLOCK_ADAPTER__BY_CODEX_EULER.md), including an explicit boundary-hazard and label falsification audit; and
- [`CODEX_CEDAR`](../feedback/SIX_PLAYER_ARBITRARY_PROFILE_CLOCK_ADAPTER__BY_CODEX_CEDAR.md), including an independent source and novelty audit.

## Exact statement

Let the player type be `SixPlayerOnePair.SixPlayer = Fin 6`.  Use the checked
names

```text
player1=0, player2=1, player3=2,
player4=3, player5=4, player6=5 : Fin 6,
A=SixPlayerOnePair.targetA={player1,player2},
B=SixPlayerOnePair.targetB={player3,player4}.
```

Thus the human gloss “players 1 through 6” is represented by literal `Fin 6`
coordinates `0` through `5`; no literal coordinate `6` is used below.

Let `reward` be any quitting reward table and let `sigma` be any behavioral
profile.  Put

```text
roots(t)=quittingProfileLiveRoot reward sigma t.
```

For each human index `r=1,...,6`, write `q_r(t)` for the Quit probability of
the checked named element `SixPlayerOnePair.player_r` in `roots(t)`, and write

```text
S(t)=quittingJointSurvivalWeight roots 0 t.
```

Then the literal terminal masses

```text
a=exactCoalitionMass (quittingTerminalOutcomeMass reward sigma) A,
b=exactCoalitionMass (quittingTerminalOutcomeMass reward sigma) B
```

satisfy

```text
sqrt(a)+sqrt(b)<=1.                                  (1)
```

No equilibrium or exploitability premise is needed.  The theorem is a
probability-law adapter for every behavioral profile in the project's quitting
semantics.  It does not force either target mass to be positive.

The checked conditional theorem
`SixPlayerOnePair.integerReward_secondPairMass_le_of_clock` can therefore lose
its supplied `hclock` premise once the three bridges below are formalized.

## The three exact bridges

### 1. Construct the hazard clock from the live roots

Construct `Math.Probability.TwoPairHazardClock` from `roots` by taking

```text
first(t)  =q_1(t),    second(t)=q_2(t),
third(t)  =q_3(t),    fourth(t)=q_4(t),
background(t)=sqrt((1-q_5(t))(1-q_6(t))),
survivalRoot(t)=sqrt(S(t)).                          (2)
```

Thus `q_r` always denotes the hazard of the checked named element
`SixPlayerOnePair.player_r`; its subscript is a human index, not a literal
`Fin 6` numeral.

All hazards lie in `[0,1]`.  The background is in `[0,1]`, and `S(t)>=0`, so
the nonnegativity fields are immediate.  Also `S(0)=1`.  The root-sequence
survival recurrence is

```text
S(t+1)=S(t) product_i(1-q_i(t)).                    (3)
```

All factors in (3) are nonnegative.  Repeated use of
`sqrt(xy)=sqrt(x)sqrt(y)` therefore gives exactly

```text
survivalRoot(t+1)
 =survivalRoot(t) background(t)
   pairContinueAmplitude(first(t),second(t))
   pairContinueAmplitude(third(t),fourth(t)),       (4)
```

which is the `TwoPairHazardClock.survivalRoot_step` field.  The two remaining
`Fin 6` coordinates occur only through `background`; no player is omitted.

### 2. Identify the squared stage amplitudes

Let `roles : QuittingTwoPairGateRoles (Fin 6)` use `player1,player2` for `A`
and `player3,player4` for `B`.  At time `t`, the exact product-root mass of
`A` is

```text
q_1 q_2 (1-q_3)(1-q_4)(1-q_5)(1-q_6).               (5)
```

and the exact product-root mass of `B` is the symmetric expression.  Squaring
the amplitudes defined by (2), using `S(t)>=0` and all hazard bounds, gives

```text
clock.firstTargetAmplitude(t)^2
 =QuittingTwoPairGateRoles.rootSequenceStageCoalitionMass roots t A,

clock.secondTargetAmplitude(t)^2
 =QuittingTwoPairGateRoles.rootSequenceStageCoalitionMass roots t B. (6)
```

These are literal equalities, not bounds.  The survival factor is `S(t)`, and
the background square supplies exactly the Continue probabilities of the
named background players `player5,player6`.

### 3. Pass the finite clock bound to the terminal law

For every horizon `N`, the checked theorem
`Math.Probability.TwoPairHazardClock.finite_targetMass_sqrt_sum_le_one` and
(6) give

```text
sqrt(sum_(t<N) stageMass(roots,t,A))
 +sqrt(sum_(t<N) stageMass(roots,t,B)) <= 1.         (7)
```

The nonnegative partial sums increase to the corresponding `tsum`s.  Taking
`N -> infinity` in (7), using continuity of `sqrt`, yields

```text
sqrt(rootSequenceTerminalCoalitionMass roots A)
 +sqrt(rootSequenceTerminalCoalitionMass roots B) <= 1. (8)
```

Finally, the actual-profile live-mass identity and terminal-law time
disintegration identify, for `G=A,B`,

```text
rootSequenceTerminalCoalitionMass
  (quittingProfileLiveRoot reward sigma) G
= exactCoalitionMass
    (quittingTerminalOutcomeMass reward sigma) G.   (9)
```

Indeed, at each date both sides of the stage identity are joint survival
through the preceding live rows times the exact product-root mass of `G`.
Summing over dates gives the terminal mass; the `Never` atom contributes zero
to a nonempty exact-coalition event.  Substituting (9) into (8) proves (1).

## Conjecture-facing change

The formalized six-player packet proves an unconditional `31/66` one-pair and
leftover ledger and a completion-wide pure-target lock.  Its checked
second-pair upper bound still takes

```text
hclock : sqrt(a)+sqrt(b)<=1
```

as supplied data.  This packet is exactly the missing arbitrary-profile
adapter from the literal behavioral profile to that premise.  It closes no
positive-`B` producer and supplies no terminal exploitability gap.

## Probability, information, and deviation audit

Before absorption there is one public live history at each date.  The profile
may be fully time-dependent and may use arbitrary private behavioral
randomization.  At each live history the quitting-game stage law is the
independent product of the six displayed marginals, which is precisely the
product law used in (3)--(6).  Simultaneous quitting is retained.  `Never` is
the residual survival mass and is included in the leftover, but not in either
nonempty target atom.

No unilateral-deviation reduction is used here: the statement concerns the
outcome law of one arbitrary prescribed behavioral profile.  The strategic
deviation class enters only later, through the one-pair exploitability ledger.

## Source correspondence

As ordinary mathematics, inequality (1) is not new here.  Proposition 18 of
`notes/CODEX_GAUSS__CURL_FREE_TOGGLE_POTENTIAL.md` proves the stronger
countable-clock theorem for any finite family of disjoint pairs, including
positive Never mass.  The new contribution of this packet is the exact
repository-semantic bridge from an arbitrary `BehaviorProfile`, through its
actual live roots and the checked `TwoPairHazardClock`, to its literal terminal
outcome law.

The finite probability core is already checked by
`TwoPairHazardClock.finite_targetMass_sqrt_sum_le_one` in
`MathUE/Probability/SquareRootCoalitionClock.lean`.

The source-native quantities are already defined in
`UniformEquilibrium/Quitting/Chronology/TwoPairClockBoundary.lean`:

- `QuittingTwoPairGateRoles.rootSequenceStageCoalitionMass`;
- `QuittingTwoPairGateRoles.rootSequenceTerminalCoalitionMass`; and
- `QuittingTwoPairGateRoles.rootSequenceHazard`.

The live-root, survival, and terminal-law ingredients are checked by
`quittingProfileLiveRoot`, `quittingJointSurvivalWeight_succ`,
`quittingLiveMass_eq_jointSurvivalWeight_profileLiveRoot`,
`quittingStageCoalitionMass_eq_liveMass_mul_rootCoalitionMass`, and
`quittingTerminalOutcomeMass_eq_timeDisintegration` in their existing
quitting modules.

What is new relative to those sources is exactly the composition (2), the two
amplitude identities (6), and the terminal identification (9) plus the
finite-to-infinite limit for the actual behavioral profile.  The two reviews
named above independently checked those bridges, including zero and unit
hazards, positive Never mass, and arbitrary time dependence.

## Boundary tests

1. **All Continue.**  Every hazard and both target masses vanish; the survival
   root is constantly one and (1) is strict.
2. **Pure `A` at date zero.**  The first amplitude and `a` equal one, while the
   second amplitude and `b` vanish; (1) is equality.
3. **Positive Never mass.**  The limiting survival mass need not vanish.  The
   finite-to-infinite argument retains it as unused budget and still proves
   (1).
4. **Background quitting.**  Positive hazards of the named players
   `player5,player6` reduce both
   target atoms through the same background factor; they cannot be dropped
   from the clock construction.
5. **Time dependence.**  No stationary identification is used.  Each date has
   its own six marginal hazards and survival prefix.

## Checked Lean realization

The result is proved in
`UniformEquilibrium/Diagnostics/Quitting/SixPlayerArbitraryProfileClockAdapter.lean`.
The exact declarations are:

- `twoPairGateRoles` and `profileTwoPairHazardClock` for (2)--(4);
- `profileTwoPairHazardClock_firstTargetAmplitude_sq` and
  `profileTwoPairHazardClock_secondTargetAmplitude_sq` for (6);
- `sqrt_rootSequenceTargetMass_add_sqrt_rootSequenceTargetMass_le_one` for
  the finite-to-infinite passage (7)--(8);
- `rootSequenceTerminalCoalitionMass_profileLiveRoot_eq_exactCoalitionMass`
  for (9);
- `sqrt_firstPairMass_add_sqrt_secondPairMass_le_one` for (1); and
- `integerReward_secondPairMass_le` and
  `integerReward_one_tenth_secondPairMass_le_actualProfile` for the
  unconditional actual-profile consumers.

The packet has seals `M`, `L`, `A`, and `C`: the adapter begins with the
literal arbitrary behavioral profile and its checked consumer removes the
former `hclock` premise from the second-pair estimate.  Its consumer is a
quantitative mass bound, not a producer of positive second-pair mass or a
uniform-equilibrium theorem.

## Scope and nonclaims

- The adapter does not force `a>0` or `b>0`.
- It does not make the six-player integer table a counterexample; pure `A`
  remains an exact uniform-payoff equilibrium.
- It proves a probability constraint for an actual behavioral profile, not
  realizability of an arbitrary supplied terminal coalition law.
- It introduces no public correlation and does not enlarge the quitting-game
  information structure.
- It does not decide the incentive-gadget question or the finite-quitting
  conjecture.
