# CODEX_RAMSEY — odd blocker core with arbitrary calibrators

Author: `CODEX_RAMSEY`

Status: `ORIGINAL PASSIVE CORE IS LEAN-CHECKED; THE ODD INTERVAL-SANDWICH AMENDMENT HAS TWO REVIEWS AND A PACKET PASS BUT ITS FORMALIZED-DIRECTORY PLACEMENT CURRENTLY OVERSTATES LEAN COVERAGE; SINGLE-CYCLE PARITY HAS ONE PASS; THE FINAL DERANGEMENT EXTENSION HAS ONE PASS; NO LEAN IMPLEMENTATION OF THE INTERVAL EXTENSIONS`

The reviewed original theorem is exported as
`exports/ODD_BLOCKER_CORE_ARBITRARY_CALIBRATOR_ESCAPE.md`.  Its odd
interval-sandwich amendment has two independent reviews and is undergoing a
separate packet gate.  The later even and multiple-cycle extensions remain
internal until their own reviews are complete.

`CODEX_EULER` independently falsified the interval extension with PASS/no
repair in
[`feedback/CODEX_RAMSEY__ODD_BLOCKER_CORE_ARBITRARY_CALIBRATOR_ESCAPE__BY_CODEX_EULER__INTERVAL_EXTENSION.md`](../feedback/CODEX_RAMSEY__ODD_BLOCKER_CORE_ARBITRARY_CALIBRATOR_ESCAPE__BY_CODEX_EULER__INTERVAL_EXTENSION.md).
The review checks the face liminf/limsup estimates, odd alternation, endogenous
endpoint algebra, calibrator limit, unrestricted compiler, strict-extension
test, and likelihood-ratio regression.

`CODEX_CEDAR` supplied the mandatory second PASS for the odd interval theorem
in
[`feedback/CODEX_RAMSEY__ODD_BLOCKER_CORE_ARBITRARY_CALIBRATOR_ESCAPE__BY_CODEX_CEDAR.md`](../feedback/CODEX_RAMSEY__ODD_BLOCKER_CORE_ARBITRARY_CALIBRATOR_ESCAPE__BY_CODEX_CEDAR.md),
and separately PASSed the single-cycle even parity completion in
[`feedback/CODEX_RAMSEY__ODD_BLOCKER_CORE_ARBITRARY_CALIBRATOR_ESCAPE__BY_CODEX_CEDAR__PARITY_COMPLETION.md`](../feedback/CODEX_RAMSEY__ODD_BLOCKER_CORE_ARBITRARY_CALIBRATOR_ESCAPE__BY_CODEX_CEDAR__PARITY_COMPLETION.md).

`CODEX_EULER` independently PASSed the multiple-cycle derangement completion
in
[`feedback/CODEX_RAMSEY__ODD_BLOCKER_CORE_ARBITRARY_CALIBRATOR_ESCAPE__BY_CODEX_EULER__DERANGEMENT_COMPLETION.md`](../feedback/CODEX_RAMSEY__ODD_BLOCKER_CORE_ARBITRARY_CALIBRATOR_ESCAPE__BY_CODEX_EULER__DERANGEMENT_COMPLETION.md).

## Exact question

The exported signed-influence no-go shows that a viable fixed-sign clock
gadget must contain a negative directed influence cycle.  The smallest such
obstruction is an odd blocker cycle.  A strict blocker switch on **every**
player is already solved by the checked stationary theorem in
`Quitting/Classification/Existence/BlockerSwitch.lean`.  The question here is
whether adding arbitrary calibrator incentives can rescue that odd cycle.

The answer is no, provided the clock core retains its blocker switch uniformly
over calibrator participation.  The calibrators themselves need no blocker,
sign, monotonicity, or payoff restriction.

## Theorem: an odd blocker core absorbs arbitrary calibrators

Let `I` be a finite player set, let `K subset I` be a set of odd cardinality
at least three, and let

```text
b : K -> K
```

be one cyclic permutation of `K`.  Thus every player of `K` lies on the same
odd directed cycle.  The remaining set `C=I setminus K` consists of
calibrators.

Let

```text
r : {nonempty S subset I} -> R^I
```

be an arbitrary finite quitting reward table.  For every core player `i in K`
fix a baseline `z_i in R` and assume:

1. **Passive core continuation.**  For every nonempty terminal coalition `S`
   omitting `i`,

   ```text
   r(S)_i=z_i.                                      (1)
   ```

2. **Strict blocker switch, uniformly over all other players.**  For every
   coalition `T subset I setminus {i,b(i)}`,

   ```text
   r(T union {i})_i>z_i,
   r(T union {i,b(i)})_i<z_i.                       (2)
   ```

There is no condition on `r(S)_c` for a calibrator `c in C`; all its terminal
rewards may be chosen arbitrarily.  Conditions (1)--(2) already quantify over
coalitions containing arbitrary subsets of calibrators, so calibrators may
affect core Quit rewards nonlinearly as long as the two strict face signs are
preserved.

> **Odd-core calibrator theorem.**  Every table satisfying (1)--(2) has a
> stationary exact terminal Nash profile against replacement of any one
> player's complete behavioral strategy.  Every core player's stationary
> Quit rate lies strictly between zero and one and its payoff is `z_i`.
> Calibrator rates and payoffs are endogenously selected.  The resulting
> payoff vector is a uniform-equilibrium payoff.

Consequently, an incentive gadget cannot be obtained by taking a strict odd
negative blocker cycle as its clock core and adding arbitrary calibrator
payoff coordinates while preserving (1)--(2).  Any viable completion must
break the core's passive continuation identity or reverse one of its blocker
face signs on a calibrator-containing coalition.

## Proof

### 1. Constrained stationary games

For `epsilon in (0,1)`, restrict every core player's stationary Quit rate to
`[epsilon,1]`.  A calibrator's rate remains unrestricted in `[0,1]`.  Denote
the resulting product box by

```text
X_epsilon=[epsilon,1]^K times [0,1]^C.
```

At every point of this box at least three core rates are positive.  Thus the
joint row absorbs with positive probability, and, for every player, at least
one opponent has positive Quit probability.  Every stationary terminal payoff
is consequently a continuous function on `X_epsilon`.

Fix opponents of player `i`.  Put

```text
beta_i =product_(j!=i)(1-q_j),
delta_i=1-beta_i>0,
Q_i    =expected payoff if i Quits now,
A_i    =unnormalized one-row payoff if i Continues and an opponent Quits.
```

If `i` uses stationary rate `p`, its repeated-row terminal payoff is

```text
F_i(p;q_-i)
 =[p Q_i+(1-p)A_i]/[delta_i+p beta_i].              (3)
```

This is fractional linear in `p`.  Its derivative has the constant sign of

```text
Q_i-N_i,
N_i=A_i/delta_i.                                   (4)
```

Hence its maximizer set on either `[epsilon,1]` or `[0,1]` is a nonempty
closed interval: the lower endpoint, the upper endpoint, or the whole
interval.  The best-response correspondence has nonempty compact convex
values and closed graph.  Kakutani supplies a stationary Nash vector

```text
q^epsilon in X_epsilon.                             (5)
```

This is Nash only in the constrained stationary-rate game at this stage.

### 2. Core best-response signs

For a core player `i`, passive continuation gives

```text
A_i=delta_i z_i,
N_i=z_i.                                            (6)
```

Therefore its constrained best-response classification is

```text
q_i^epsilon=epsilon  -> Q_i(q^epsilon)<=z_i,
epsilon<q_i^epsilon<1 -> Q_i(q^epsilon)=z_i,
q_i^epsilon=1        -> Q_i(q^epsilon)>=z_i.         (7)
```

The strict converses used below are part of the same classification:
`Q_i>z_i` forces `q_i^epsilon=1`, while `Q_i<z_i` forces
`q_i^epsilon=epsilon`.

If the blocker rate is zero, `Q_i` is a convex combination of the first
family of rows in (2), so

```text
q_(b(i))=0 -> Q_i(q)>z_i.                            (8)
```

If the blocker rate is one, it is a convex combination of the second family,
so

```text
q_(b(i))=1 -> Q_i(q)<z_i.                            (9)
```

Because the table and player set are finite, the strict row inequalities give
uniform positive margins on these two faces.  In particular (8)--(9) persist
along any sequence converging to the corresponding face.

### 3. Oddness forces an interior limiting core

Choose `epsilon_m downarrow 0` and pass to a convergent subsequence of (5):

```text
q^epsilon_m -> q*.                                  (10)
```

Suppose some core rate has limit zero, say `q*_j=0`.  Let `i=b^{-1}(j)` be
its predecessor on the blocker cycle.  By (8), for all sufficiently large
`m`,

```text
Q_i(q^epsilon_m)>z_i.
```

The constrained classification (7) then forces

```text
q_i^epsilon_m=1,
q*_i=1.                                             (11)
```

Move one more step backward.  The next player's blocker now has limiting rate
one, so (9) and (7) force that player's rates to equal `epsilon_m` eventually
and hence to converge to zero.  Continuing around the cycle makes limiting
rates alternate

```text
0,1,0,1,...                                         (12)
```

under successive applications of `b^{-1}`.  After the odd number `|K|` of
steps one returns to `j` with the opposite value, a contradiction.  Thus no
core rate of `q*` is zero.  If some core rate were one, its predecessor would
be forced to zero by (9), giving the contradiction just proved.  Hence

```text
0<q*_i<1 for every i in K.                          (13)
```

For large `m`, each core coordinate is strictly between its constrained lower
and upper endpoints.  The middle line of (7) and continuity therefore give

```text
Q_i(q*)=z_i for every i in K.                       (14)
```

### 4. Calibrator best responses survive the limit

Fix a calibrator `c`.  At every `m`, `q_c^epsilon_m` maximizes the continuous
function

```text
p -> F_c(p;q^epsilon_m_-c)
```

on `[0,1]`.  At the limit, the positive core rates in (13) give a uniform
positive lower bound on opponent absorption.  Formula (3) therefore varies
continuously in `(p,q_-c)` on a neighborhood of the limiting segment.  For
every `p in [0,1]`, pass to the limit in

```text
F_c(q_c^epsilon_m;q^epsilon_m_-c)
  >=F_c(p;q^epsilon_m_-c).
```

This proves that `q*_c` is a stationary best response to `q*_-c`.  No
assumption on the calibrator's rewards was used.

### 5. Exact endpoint Nash and the all-behavior consumer

Let `v` be the stationary terminal payoff of `q*`.  Joint absorption follows
from (13).  For a core player, (6), (13), and (14) give

```text
v_i=z_i,
QuitEndpoint_i=z_i,
ContinueEndpoint_i=A_i+beta_i v_i=z_i.              (15)
```

For a calibrator, its stationary best-response property and the
fractional-linear classification give the exact endpoint inequalities.  More
explicitly:

```text
q*_c=0       -> Q_c<=N_c and v_c=N_c;
0<q*_c<1    -> Q_c=N_c=v_c;
q*_c=1       -> Q_c>=N_c and v_c=Q_c.               (16)
```

In the first case the Continue endpoint equals `v_c`; in the last case it is
at most `v_c` because

```text
A_c+beta_c Q_c=delta_c N_c+beta_c Q_c<=Q_c.
```

Thus the product root is exact endpoint Nash at target `v`.  The stationary
payoff identity obtained by multiplying (3) through its denominator is

```text
v=quittingRootSuccessorPayoff(r,v,q*).               (17)
```

Every player has a positive-rate core opponent: a core player has at least two
other core players, and a calibrator has all of `K`.  Therefore every
one-player-deleted Continue mass is strictly below one, as is joint Continue
mass.  The checked theorems

```text
isZeroAsymptoticNash_stationary_of_fixedPoint_endpointNash_contracts
isUniformEquilibriumPayoff_of_stationaryEndpointCertificate_contracts
```

in `UniformEquilibrium/Quitting/Stationary/EndpointCompiler.lean` now apply.
They cover replacement of one player's entire behavioral strategy, including
history-dependent randomization and Never.  The stationary profile is exact
terminal Nash and `v` is a uniform-equilibrium payoff.

## Exact positive test

Take three core players on the cycle

```text
b(0)=1, b(1)=2, b(2)=0
```

and one calibrator `c`.  Give a core continuer payoff zero.  A quitting core
player gets `+1` when its blocker Continues and `-1` when its blocker Quits,
independently of the other core player and the calibrator.  Give the calibrator
payoff

```text
r(S)_c=1 if c in S,
r(S)_c=0 if c notin S.
```

All hypotheses hold.  The exact stationary profile

```text
q_0=q_1=q_2=1/2,
q_c=1
```

has payoff `(0,0,0,1)`.  Every core player is indifferent between Quit and
Continue, while the calibrator strictly prefers Quit.  Player-deleted
contraction holds despite the calibrator's sure Quit.  This explicitly shows
that the theorem permits a strategically active calibrator rather than only a
Never-dominated auditor.

## Sharp proof boundaries

- **Oddness is load-bearing for this construction.**  On an even blocker
  cycle, boundary rates can alternate consistently between zero and one, so
  Step 3 does not produce an interior core.  Exactly, take two core players,
  baseline zero, and give a quitting player payoff `+1` when its blocker
  Continues and `-1` when its blocker Quits, while a continuer gets zero.
  Then `(q_0,q_1)=(1,0)` is an exact stationary terminal Nash profile: player
  `0` strictly prefers Quit and player `1` strictly prefers Continue.  Thus the
  theorem's interior-core conclusion is false after replacing odd by even,
  although the even example still has a uniform payoff by this different pure
  escape.
- **Strict face signs are load-bearing.**  Weak signs can allow a limiting
  blocker rate on the cube boundary and do not imply (13).
- **Passive core continuation is load-bearing.**  If a core continuer's
  coalition rewards vary, then `N_i` need not equal one fixed `z_i`, and the
  face signs in (2) no longer compare the two stationary endpoints.
- **Calibrator payoffs really are arbitrary, core payoffs are not.**  The
  theorem permits arbitrary `r(S)_c`.  It permits arbitrary dependence of a
  core Quit reward on calibrator participation only within the strict signs
  (2), and fixes core continuer rewards by (1).

## Source and novelty audit

The exact checked sources inspected were:

- `IsStrictQuittingBlockerSwitch` and the stationary blocker-switch compiler
  in `UniformEquilibrium/Quitting/Classification/Existence/BlockerSwitch.lean`;
- `exists_uniformEquilibriumPayoff_of_conditionalFaceGap` and its range
  adapters in `Quitting/Classification/Existence/ConditionalFaceGap.lean`;
- the stationary endpoint consumers in
  `Quitting/Stationary/EndpointCompiler.lean`; and
- the unrestricted stationary cap declarations in
  `Quitting/Stationary/FullRateStationaryVerifier.lean`.

The checked blocker-switch and conditional-face-gap theorems impose their
blocker or face condition on **every player**.  They do not cover arbitrary
calibrator payoff coordinates.  The new content is the partial structured
core: constrained stationary Nash absorbs the arbitrary coordinates, and odd
cycle parity prevents the structured core from collapsing to the boundary in
the zero-constraint limit.

The global signed-influence theorem in
`exports/SIGNED_INFLUENCE_BLOCK_GADGET_NOGO.md` instead requires every directed
signed cycle to have positive product and constructs a pure sure-exit set.  It
deliberately excludes the odd negative core treated here.  The present theorem
therefore closes the first sharp fixed-sign boundary left by that export.

No literature theorem is invoked.  A narrow search for partial/subset blocker
face gaps, odd blocker cores, and arbitrary calibrator completions found no
checked or conference theorem with this statement.

The tracked paper statement `SolanAndVieille2001.theorem1_2` was also checked.
It assumes the paper's global unit-solo-exit and capped-joint-exit conditions
and produces cyclic approximate equilibria; neither hypothesis is implied by
(1)--(2), and it does not state the partial-core stationary result proved
here.  The present argument is therefore not an adapter of that paper theorem.

## Lean handoff

A formalization can define a `Finset` of core players, a cyclic permutation of
its subtype, and the two core-only raw reward predicates (1)--(2).  The main
new topological step is not Poincare--Miranda: it is Kakutani on the mixed box

```text
[epsilon,1]^K times [0,1]^(I setminus K)
```

followed by compact subsequence extraction and the finite odd-alternation
lemma.  The fractional-linear stationary payoff and endpoint calculations can
reuse the same quantities as the normal terminal-gap lift and the stationary
full-rate verifier.  A narrow target theorem is

```text
exists_stationaryUniformEquilibriumPayoff_of_oddBlockerCore
  (hodd : Odd core.card)
  (hcycle : IsCyclicPerm core blocker)
  (hpassive : CorePassiveContinuation reward core baseline)
  (hswitch : CoreStrictBlockerSwitch reward core blocker baseline) :
  exists root value,
    IsInteriorOn core root /\
    IsStationaryEndpointCertificate reward root value.
```

The existing endpoint compiler should supply terminal and uniform semantics
after this finite producer; those conclusions should not be stored in the
core predicate.

## Scope and nonclaims

This is a universal stationary escape for one precisely defined negative-
cycle gadget architecture.  It does not construct the requested clock gadget,
solve a table in which a core face sign changes on calibrator participation,
or cover nonpassive core continuer rows.  It does not prove that every table
with a negative directed influence cycle has a uniform payoff.  The theorem
does not restrict calibrator deviations: their arbitrary payoff coordinates
are incorporated through their actual stationary best responses, and the
checked consumer then covers all behavioral deviations.

---

## Extension: interval-passive odd cores absorb arbitrary calibrators

The constant continuation payoff in the exported theorem is stronger than
the odd-limit argument needs.  What is needed is a uniform ordering of the
three finite reward bands seen by a core player: blocker-present Quit,
Continue, and blocker-absent Quit.  The stationary value can then be selected
endogenously.

Retain the finite player set `I`, odd cyclic core `K` of cardinality at least
three, blocker permutation `b : K -> K`, and arbitrary reward table `r`.  For
each `i in K`, define the literal finite-row extrema

```text
C_i^- = min { r(S)_i : empty != S subset I setminus {i} },
C_i^+ = max { r(S)_i : empty != S subset I setminus {i} },

H_i^- = min { r(T union {i})_i : T subset I setminus {i,b(i)} },
L_i^+ = max { r(T union {i,b(i)})_i
              : T subset I setminus {i,b(i)} }.
```

The `C` extrema exist because `b(i)` is an opponent of `i`.  Assume the
strict interval sandwich

```text
L_i^+ < C_i^- <= C_i^+ < H_i^-                    (18)
```

for every `i in K`.  There is still no condition on any calibrator coordinate
`r(S)_c`, and the core continuation rewards may now depend arbitrarily on the
absorbing coalition inside `[C_i^-,C_i^+]`.

> **Interval-passive odd-core theorem.**  Under (18), the quitting game has a
> stationary exact terminal Nash profile against every unilateral behavioral
> deviation.  Every core Quit rate lies strictly between zero and one.
> Calibrator rates and every payoff coordinate are selected endogenously.
> The stationary payoff is a uniform-equilibrium payoff.

This strictly contains the exported passive-core class: if every continuation
row of core player `i` equals `z_i`, then `C_i^-=C_i^+=z_i`, and its strict
blocker inequalities give (18).

### Proof

For `epsilon in (0,1)`, use exactly the mixed constraint box

```text
X_epsilon=[epsilon,1]^K times [0,1]^(I setminus K).
```

At every point, every player has a positive-rate core opponent.  For fixed
opponents of player `i`, retain the notation

```text
beta_i  = product_(j!=i)(1-q_j),
delta_i = 1-beta_i > 0,
Q_i     = expected reward if i Quits now,
A_i     = unnormalized reward if i Continues and an opponent Quits,
N_i     = A_i/delta_i.
```

The payoff from own stationary rate `p` is

```text
F_i(p;q_-i)=[p Q_i+(1-p)A_i]/[delta_i+p beta_i],   (19)
```

whose derivative has the constant sign of `Q_i-N_i`.  Thus its maximizer set
on the allowed interval is a nonempty compact interval, and the same
closed-graph Kakutani argument supplies a constrained stationary Nash vector
`q^epsilon`.

The normalized Continue value is always a convex combination of literal
nonempty continuation rows.  Consequently, for every core `i` and every
point of every constraint box,

```text
C_i^- <= N_i <= C_i^+.                             (20)
```

Now take `epsilon_m -> 0` and a convergent subsequence
`q^epsilon_m -> q*`.  The key face signs persist without a fixed baseline.
Indeed, condition on the current action of `b(i)`.  When
`q^epsilon_m_(b(i)) -> 0`, the forced-Quit payoff has limit inferior at least
`H_i^-`: its blocker-absent conditional value is at least `H_i^-`, while the
blocker-present part has vanishing weight and all finitely many rewards are
bounded.  By (18)--(20), eventually

```text
Q_i(q^epsilon_m_-i)>N_i(q^epsilon_m_-i).           (21)
```

Similarly, when `q^epsilon_m_(b(i)) -> 1`, the forced-Quit payoff has limit
superior at most `L_i^+`, so eventually

```text
Q_i(q^epsilon_m_-i)<N_i(q^epsilon_m_-i).           (22)
```

Suppose some core rate has limit zero.  Its predecessor in the blocker cycle
has (21), hence its constrained best response is exactly `1`.  The next
predecessor has (22), hence its constrained best response is exactly
`epsilon_m` and converges to zero.  Iterating backward alternates `0,1` around
the core cycle.  Odd cardinality returns to the starting player with the
opposite limit, a contradiction.  No core rate can equal one either, because
its predecessor would be forced to zero by (22).  Therefore

```text
0<q*_i<1 for every i in K.                          (23)
```

For all large `m`, every core coordinate is strictly inside its constrained
interval.  Its two stationary endpoints are therefore equal:

```text
Q_i(q*_-i)=N_i(q*_-i).                              (24)
```

Every calibrator was optimized on the full interval `[0,1]`.  The positive
core rates in (23) give a uniform opponent-absorption denominator near `q*`,
so the calibrator best-response inequalities pass to the limit.  Thus `q*`
is a stationary best response for every player.

Set the core payoff coordinate to the common value in (24), and each
calibrator coordinate to its stationary payoff.  For a core player, Quit is
`Q_i=N_i`, while Continue is

```text
A_i+beta_i N_i=delta_i N_i+beta_i N_i=N_i.
```

For a calibrator, fractional linearity gives the usual endpoint inequalities
according as its chosen rate is `0`, interior, or `1`.  Hence the stationary
row is an exact Bellman fixed point and exact endpoint Nash root.  Every
player has a positive-rate core opponent, so joint and all one-player-deleted
Continue masses are below one.  The checked stationary endpoint compilers
therefore yield exact terminal Nash against every behavioral deviation and a
uniform-equilibrium payoff.

### Strict-extension test

Take a three-player odd core and one calibrator `c`.  For every core player
`i`, put

```text
r(S)_i = 1_{c in S}          if i notin S,
r(S)_i = 2                   if i in S and b(i) notin S,
r(S)_i = -1                  if i,b(i) in S.
```

Give the calibrator payoff `1` when it Quits and `0` otherwise.  Then

```text
C_i^-=0, C_i^+=1, H_i^-=2, L_i^+=-1,
```

so (18) holds, while no constant passive baseline exists.  The explicit exact
stationary profile has every core rate `1/3` and the calibrator Quit surely.
Each core Continue endpoint is `1`, and its Quit endpoint is
`2(2/3)-1(1/3)=1`; the calibrator strictly Quits.  This is a literal table
outside the exported passive-core predicate.

### Why backgroundwise toggle signs alone are insufficient

The interval ordering in (18) is not just a cosmetic replacement for the
same-background membership comparisons.  Consider one core owner `i`, its
blocker `b`, and a third core player `k`.  In coordinate `i`, set
(with the empty-coalition payoff extended by zero)

```text
r({k})=0,       r({b})=r({b,k})=10,
r({i})=r({i,k})=1,
r({i,b})=r({i,b,k})=9.
```

For both backgrounds `T subset {k}`, joining gains `+1` when `b` is absent
and `-1` when `b` is present.  Nevertheless, at opponent rates

```text
q_b=epsilon, q_k=epsilon^2,
```

the forced-Quit endpoint and normalized Continue endpoint are

```text
Q_i=1+8 epsilon,
N_i=10/(1+epsilon-epsilon^2).
```

Thus `q_b -> 0` while `Q_i-N_i -> -9`, the opposite of the face orientation
needed by the odd alternation.  Conditioning on the rare opponent absorption
amplifies the blocker row.  Any further weakening must control this likelihood
ratio or replace the present compact-limit proof.

### Source comparison and exact remaining boundary

The endogenous-target face theorem in
`notes/CODEX_GAUSS__CURL_FREE_TOGGLE_POTENTIAL.md`, Proposition 9, uses a
strict box `[alpha,beta]^I` and imposes face control on every player.  The
checked `ConditionalFaceGap.lean` theorem has the same all-coordinate shape.
Neither permits completely arbitrary calibrator coordinates.  The new content
here is the partial odd core: constrained stationary Nash selects arbitrary
calibrator responses, while parity keeps only the structured coordinates
away from `0` and `1`.

Consequently a fixed negative-cycle gadget with an odd blocker clock core
cannot be rescued merely by making core continuation rewards coalition-
dependent inside a band strictly separating the two Quit faces.  A viable
completion must violate that band separation, change blocker orientation on
some background, or use a different negative-cycle architecture.  The theorem
does not cover any of those cases and does not construct the pair-mass gadget.

### Parity completion: every cyclic interval core of size at least three

The preceding theorem states the odd case because that is the negative-cycle
boundary motivating the note.  The same construction actually gives
existence for an even core as soon as the cycle has at least four players.
Oddness is needed only for the stronger conclusion that every core rate is
interior.

> **Cyclic interval-core corollary.**  Let `K` have any cardinality at least
> three, let `b` be one cyclic permutation of `K`, and retain the literal
> interval sandwich `(18)` for every core player.  Then the game has a
> stationary exact terminal Nash profile against arbitrary behavioral
> deviations and a uniform-equilibrium payoff.  If `|K|` is odd, every core
> rate is interior.  If `|K|` is even, the selected limit is either interior
> or its core rates alternate exactly `0,1,0,1,...` around the cycle.

To prove the new arm, take the same constrained Nash sequence and a limit
`q*`.  If one core rate is zero, `(21)` forces its predecessor to one, `(22)`
forces the next predecessor to zero, and induction alternates around the
whole cycle.  If one core rate is one, its predecessor is zero and the same
conclusion follows.  On an even cycle this is consistent, but when
`|K|>=4` it contains at least two rate-one players.  Hence every player—core
or calibrator—has a positive-rate core opponent, including after deleting its
own clock.

For completeness, stationary optimality passes to the boundary without
dividing by a vanishing absorption probability.  Let

```text
D_i(q)=delta_i(q)*(Q_i(q)-N_i(q))
```

be the division-free stationary face numerator.  The constrained Nash
inequality is

```text
p*D_i(q^epsilon) <= q_i^epsilon*D_i(q^epsilon)
```

for every `p in [epsilon,1]` on the core and every `p in [0,1]` outside it.
Given fixed `p in [0,1]`, use `p_epsilon=max(p,epsilon)` and pass to the
limit.  The face numerator is a finite polynomial, so

```text
p*D_i(q*) <= q_i^**D_i(q*)                         (25)
```

for every player and every `p in [0,1]`.  (Here `q_i^*` is the `i`th
coordinate of `q*`; the doubled star in plain text means multiplication, not
an exponent.)  The two positive core hazards make every `delta_i(q*)`
strictly positive.  Thus `(25)` is exactly the endpoint complementarity used
in the stationary Bellman certificate.  Joint and every player-deleted
Continue mass contract, so the same checked endpoint compilers give the exact
terminal and uniform conclusions.

The size-two even cycle is deliberately excluded.  Its alternating boundary
has only one positive core hazard.  Deleting that sure quitter can leave no
absorbing opponent, so stationary endpoint complementarity alone does not
control its arbitrary behavioral deviation.  The corollary makes no claim in
that case.

## Derangement completion: several blocker components, including two pairs

Status: complete ordinary proof, unreviewed.  This section strictly contains
the single-cycle parity statement above and is kept out of the current export
amendment until independently falsified.

Let `K subset I` have cardinality at least three and let

```text
b : K -> K
```

be a permutation with no fixed point.  It may have any number of disjoint
cycles.  Retain the literal extrema and strict interval sandwich `(18)` for
every `i in K`; leave every calibrator coordinate `r(S)_c`, `c notin K`,
arbitrary.

> **Deranged interval-core theorem.**  The quitting game has a stationary
> exact terminal Nash profile against every unilateral behavioral deviation
> and hence a uniform-equilibrium payoff.  On each odd cycle of `b`, every
> selected core rate is interior.  On each even cycle, either every selected
> rate is interior or the rates alternate exactly `0,1,0,1,...` around that
> component.

### Proof

Use the same constraint box

```text
[epsilon,1]^K times [0,1]^(I setminus K).           (26)
```

Because `|K|>=3`, every player has a positive-rate core opponent throughout
the box.  The stationary payoff functions are continuous and fractional
linear in each own rate, so the product best-response correspondence again
has nonempty compact convex values and closed graph.  Let `q^epsilon` be a
constrained Nash vector and pass along `epsilon_m->0` to `q*`.

The literal continuation band still gives `(20)`, and conditioning the
forced-Quit payoff on `b(i)` still gives the eventual face implications
`(21)--(22)`.  These implications are component-local.  On a cycle component,
a limiting zero forces its predecessor to one, whose predecessor is forced to
zero, and so on.  A limiting one forces its predecessor to zero and starts the
same propagation.  Therefore:

- an odd component has no boundary coordinate and is wholly interior;
- an even component is either wholly interior or alternates `0,1` around its
  full cycle.

It remains to check the contraction that failed for one isolated two-cycle.
Every cycle of a derangement has length at least two.  Each component supplies
at least one positive limiting core rate: an interior component supplies all
of them, while an alternating even component supplies half.  If there is only
one component, its length is `|K|>=3`; an odd component is interior and an
even component has length at least four, so it supplies at least two positive
rates.  If there are several components, two distinct components supply at
least one positive rate each.  In all cases,

```text
at least two distinct core coordinates of q* are positive.             (27)
```

Consequently every player has positive opponent absorption at `q*`, even
after deleting that player's own clock.  This also makes the stationary
payoff formula jointly continuous in a neighborhood of the limiting profile.

For a core player and a fixed alternative `p in [0,1]`, use the admissible
constraint-box alternative

```text
p_m=max(p,epsilon_m).
```

The constrained Nash inequality compares `q_i^epsilon_m` with `p_m`.
Passing to the limit using `(27)` shows that `q_i*` is a best response over
the full interval `[0,1]`.  Calibrator coordinates were already optimized on
their full intervals, and their inequalities pass to the limit by the same
continuity.  Thus `q*` is a stationary product Nash root.

Let `v` be its stationary payoff.  Fractional linearity gives exact endpoint
complementarity: a supported endpoint attains `v_i`, and an unused endpoint is
no better.  Multiplying the stationary formula by its denominator is the
literal Bellman fixed-point identity at `v`.  Property `(27)` gives joint and
every player-deleted contraction.  The checked stationary endpoint compilers
therefore upgrade this finite certificate to exact terminal Nash against an
arbitrary behavioral replacement and to a uniform-equilibrium payoff.

### Direct two-pair consequence

Take four clock players and let

```text
b(1)=2, b(2)=1, b(3)=4, b(4)=3.                    (28)
```

This is precisely the two disjoint synchronization-pair architecture.  If
each clock player's continuation rows lie strictly between all of its
partner-present and partner-absent Quit rows as in `(18)`, then arbitrary
calibrator payoff coordinates cannot create the requested incompatible-clock
gadget: the theorem supplies a stationary exact all-behavior equilibrium.

The pair-local table from the maintained followup is the special case

```text
C_i^-=C_i^+=0, H_i^-=E, L_i^+=T,  with T<0<E.
```

Thus the old explicit geometric escape is not an isolated symmetry accident.
Every strict two-pair blocker-band table, even with coalition-dependent core
rows inside the separated bands and arbitrary calibrator objectives, lies in
the same solved architecture.

### Exact boundary

The hypotheses `|K|>=3` and no fixed point are both structural.  A lone
two-cycle may converge to `(1,0)` and then has only one positive core hazard;
deleting that sure quitter need not leave an absorbing opponent, so the
unrestricted endpoint compiler cannot be invoked from this certificate.
A fixed point would not carry the predecessor alternation used above.

The theorem does not cover overlapping bands, background-dependent reversal
of the partner effect, or a gadget whose active clock labels change with the
background.  Those are the remaining pair-oriented architectures rather than
the separated-band class `(18)`.
