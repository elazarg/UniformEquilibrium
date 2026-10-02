# Odd blocker core with interval-passive calibrator coordinates

Author: `CODEX_RAMSEY`

Independent falsification reviews:

- [`CODEX_EULER`](../feedback/CODEX_RAMSEY__ODD_BLOCKER_CORE_ARBITRARY_CALIBRATOR_ESCAPE__BY_CODEX_EULER.md)
- [`CODEX_CEDAR`](../feedback/CODEX_RAMSEY__ODD_BLOCKER_CORE_ARBITRARY_CALIBRATOR_ESCAPE__BY_CODEX_CEDAR.md)

Independent reviews of the interval-passive extension:

- [`CODEX_EULER`](../feedback/CODEX_RAMSEY__ODD_BLOCKER_CORE_ARBITRARY_CALIBRATOR_ESCAPE__BY_CODEX_EULER__INTERVAL_EXTENSION.md)
- [`CODEX_CEDAR`](../feedback/CODEX_RAMSEY__ODD_BLOCKER_CORE_ARBITRARY_CALIBRATOR_ESCAPE__BY_CODEX_CEDAR.md)

Delta whole-packet review of the interval-passive extension:
[`CODEX_EULER`](../feedback/ODD_BLOCKER_CORE_ARBITRARY_CALIBRATOR_ESCAPE__BY_CODEX_EULER__INTERVAL_DELTA_GATE.md)

The even-cycle parity corollary recorded later in the author's notebook is
not part of this packet.

## Exact statement

Let `I` be a finite player set.  Let `K subset I` have odd cardinality at
least three, and let

```text
b : K -> K
```

be a cyclic permutation consisting of one cycle on `K`.  Write
`C=I setminus K` for the remaining players, called calibrators.

Let

```text
r : {nonempty S subset I} -> R^I
```

be a finite quitting reward table.  For every `i in K`, fix `z_i in R` and
assume:

1. **Passive core continuation.**  For every nonempty terminal coalition `S`
   omitting `i`,

   ```text
   r(S)_i=z_i.                                      (1)
   ```

2. **Uniform strict blocker switch.**  For every
   `T subset I setminus {i,b(i)}`,

   ```text
   r(T union {i})_i>z_i,
   r(T union {i,b(i)})_i<z_i.                       (2)
   ```

There is no condition on any calibrator coordinate `r(S)_c`, `c in C`.
Those coordinates may depend arbitrarily on the whole terminal coalition.
Core Quit rewards may also depend arbitrarily on calibrator participation,
subject only to the two strict signs in (2).

Then there is a stationary independent product profile which is an exact
terminal Nash profile against replacement of any one player's complete
behavioral strategy.  Every core player's stationary Quit probability lies
strictly between zero and one and its payoff is `z_i`.  Calibrator rates and
payoffs are selected endogenously.  The resulting payoff vector is a
uniform-equilibrium payoff.

## Reviewed interval-passive extension

The fixed continuation baseline can be replaced by a literal finite-row band.
For every core player `i`, define

```text
C_i^- = min { r(S)_i : empty != S subset I setminus {i} },
C_i^+ = max { r(S)_i : empty != S subset I setminus {i} },

H_i^- = min { r(T union {i})_i : T subset I setminus {i,b(i)} },
L_i^+ = max { r(T union {i,b(i)})_i
              : T subset I setminus {i,b(i)} }.
```

Assume, instead of (1)--(2), the strict interval sandwich

```text
L_i^+ < C_i^- <= C_i^+ < H_i^-                    (18)
```

for every `i in K`.  Core continuation rewards may now vary arbitrarily with
the absorbing coalition inside `[C_i^-,C_i^+]`; core Quit rewards may vary
inside their two separated bands; calibrator reward coordinates remain wholly
unrestricted.

Then the same conclusion holds: there is a stationary independent product
profile which is exact terminal Nash against every unilateral behavioral
replacement, every core Quit rate is strictly between zero and one, and the
endogenous stationary payoff is a uniform-equilibrium payoff.

The original theorem is a strict special case with
`C_i^-=C_i^+=z_i`.

## Conjecture-facing change

[`SIGNED_INFLUENCE_BLOCK_GADGET_NOGO.md`](../formalized/SIGNED_INFLUENCE_BLOCK_GADGET_NOGO.md)
proved that a fixed-sign influence architecture is solved whenever every
directed signed cycle has positive sign product.  It left a negative directed
cycle as the sharp necessary boundary for any viable fixed-sign incentive
gadget.

The smallest such obstruction is an odd cycle of blocker influences.  The
theorem here closes that first boundary even after adding an arbitrary finite
game on calibrator payoff coordinates.  The interval extension shows that a
fixed passive baseline is unnecessary: all core continuation rows may vary,
provided they remain strictly between the blocker-present and blocker-absent
Quit bands.  Therefore a viable completion of the negative-cycle architecture
must do at least one of the following:

```text
break the interval separation between core Continue and the two Quit bands;
reverse or erase a blocker orientation on some background;
or leave the single odd blocker-core architecture entirely.
```

This is a new special-case existence theorem with an exact source predicate
and an unrestricted-behavior semantic consumer.  It does not answer
`INCENTIVE_GADGET.md` outside this class.

## Probability, information, and deviation semantics

A stationary rate vector `q in [0,1]^I` means that at every live date each
player independently Quits with probability `q_i`.  The same product row is
repeated after unanimous Continue.  There is no public correlation device or
mixture over complete stationary profiles.

The finite construction below first proves stationary-rate optimality.  It
then proves an exact Bellman fixed point and exact endpoint Nash inequalities
with player-deleted contraction.  The checked stationary endpoint compiler
upgrades these finite facts to comparison with every unilateral behavioral
strategy: arbitrary time dependence, private randomization, pure stopping
times, ties, and Never are all included.  Thus the conclusion is not merely a
stationary- or bounded-controller equilibrium.

## Proof

### 1. The constrained stationary games

For `epsilon in (0,1)`, restrict every core rate to `[epsilon,1]` and leave
each calibrator rate in `[0,1]`.  The strategy box is

```text
X_epsilon=[epsilon,1]^K times [0,1]^C.              (3)
```

At every point of this box, each player has a positive-rate core opponent: a
core player has at least two other core players, while a calibrator has all of
`K`.  Consequently fixed-opponents absorption is positive for every player,
and the repeated stationary payoff is continuous on the whole box.

Fix the opponents of player `i`.  Put

```text
beta_i = product_(j!=i)(1-q_j),
delta_i=1-beta_i>0,
Q_i    = expected payoff if i Quits now,
A_i    = unnormalized payoff if i Continues and an opponent Quits.
```

If `i` uses own stationary rate `p`, its terminal payoff is

```text
F_i(p;q_-i)
  =[p Q_i+(1-p)A_i]/[delta_i+p beta_i].             (4)
```

Writing `N_i=A_i/delta_i`, direct differentiation shows that the derivative
of (4) has the constant sign of `Q_i-N_i`.  Hence the maximizer set on either
allowed interval is its lower endpoint, its upper endpoint, or the whole
interval.  It is nonempty, compact, and convex.  Joint continuity gives a
closed best-response graph.  Kakutani therefore supplies a constrained
stationary Nash point

```text
q^epsilon in X_epsilon.                             (5)
```

No equilibrium theorem for the original unconstrained quitting game has been
assumed here.

### 2. Core signs

For a core player `i`, (1) gives

```text
A_i=delta_i z_i,
N_i=z_i.                                            (6)
```

The constrained best-response classification is therefore

```text
q_i^epsilon=epsilon   -> Q_i<=z_i,
epsilon<q_i^epsilon<1 -> Q_i=z_i,
q_i^epsilon=1         -> Q_i>=z_i.                  (7)
```

Its strict converse form will be used below: `Q_i>z_i` forces the upper
endpoint `1`, and `Q_i<z_i` forces the lower endpoint `epsilon`.

If the blocker rate is zero, every terminal row in the forced-Quit
expectation is `T union {i}` for a background omitting `i,b(i)`.  Equation
(2) therefore gives

```text
q_(b(i))=0 -> Q_i>z_i.                              (8)
```

If the blocker rate is one, every such row also contains `b(i)`, so

```text
q_(b(i))=1 -> Q_i<z_i.                              (9)
```

There are finitely many terminal rows.  The strict inequalities in (2)
therefore have uniform positive margins on the two faces, so (8)--(9) persist
along sequences whose blocker rate tends respectively to zero or one.  This
remains true while every calibrator rate varies arbitrarily.

### 3. Oddness excludes the boundary

Choose `epsilon_m -> 0` and a convergent subsequence

```text
q^epsilon_m -> q*.                                  (10)
```

Suppose a core rate has limit zero, say `q*_j=0`.  Let
`i=b^{-1}(j)`.  By the uniform version of (8), eventually `Q_i>z_i`; hence
(7) forces

```text
q_i^epsilon_m=1,
q*_i=1.                                             (11)
```

Move one more step backward around the blocker cycle.  That player's blocker
now tends to one, so (9) and (7) force its rate to equal `epsilon_m`, hence to
converge to zero.  Iterating backward alternates limiting rates

```text
0,1,0,1,... .                                       (12)
```

After the odd number `|K|` of steps, the iteration returns to `j` with the
opposite value, a contradiction.  Thus no core rate is zero.  If some core
rate were one, its predecessor would be forced to zero by (9), which has just
been excluded.  Therefore

```text
0<q*_i<1 for every i in K.                          (13)
```

For all large `m`, each core coordinate lies strictly between
`epsilon_m` and `1`.  The middle line of (7) and continuity now give

```text
Q_i(q*)=z_i for every i in K.                       (14)
```

### 4. Arbitrary calibrator best responses survive the limit

Fix `c in C`.  At every constrained equilibrium, `q_c^epsilon_m` maximizes

```text
p |-> F_c(p;q^epsilon_m_-c)
```

on all of `[0,1]`; the calibrator coordinate was never truncated.  By (13),
the limiting core gives a uniform positive lower bound on `c`'s opponent
absorption in a neighborhood of the limit.  Formula (4) is consequently
jointly continuous there.  For every fixed `p in [0,1]`, pass to the limit in

```text
F_c(q_c^epsilon_m;q^epsilon_m_-c)
  >= F_c(p;q^epsilon_m_-c).
```

Thus `q*_c` is a stationary best response to `q*_-c`.  No inequality involving
a calibrator reward was used.

### 5. Exact endpoint certificate

Let `v` be the stationary terminal payoff of `q*`.  Joint absorption holds by
(13).  For a core player, (6), (13), and (14) give

```text
v_i=z_i,
QuitEndpoint_i=z_i,
ContinueEndpoint_i=A_i+beta_i v_i=z_i.              (15)
```

For a calibrator, fractional linearity and its stationary best response give
the three exact cases

```text
q*_c=0       -> Q_c<=N_c and v_c=N_c;
0<q*_c<1    -> Q_c=N_c=v_c;
q*_c=1       -> Q_c>=N_c and v_c=Q_c.               (16)
```

In the first case Continue equals `v_c`.  In the last case,

```text
A_c+beta_c Q_c=delta_c N_c+beta_c Q_c<=Q_c=v_c.
```

Thus every supported action attains `v` and every unused action is no better:
the product root is exact endpoint Nash at `v`.  Multiplying (4) through its
denominator is exactly the coordinatewise Bellman identity

```text
v=quittingRootSuccessorPayoff(r,v,q*).              (17)
```

Every player has a positive-rate core opponent.  Hence both the joint
Continue mass and every one-player-deleted Continue mass are strictly below
one.

### 6. Unrestricted terminal and uniform semantics

Apply the checked declarations

```text
isZeroAsymptoticNash_stationary_of_fixedPoint_endpointNash_contracts
isUniformEquilibriumPayoff_of_stationaryEndpointCertificate_contracts
```

from
`UniformEquilibrium/Quitting/Stationary/EndpointCompiler.lean` to (13),
(15)--(17), and the player-deleted contractions.  The first theorem proves
exact terminal Nash against arbitrary complete behavioral deviations.  The
second produces the fixed uniform-equilibrium payoff `v`.

This completes the proof.

### 7. Proof of the interval-passive extension

Use the same constraint boxes and stationary Nash vectors as in Section 1.
For fixed opponents, the normalized Continue value

```text
N_i=A_i/delta_i
```

is a convex combination of literal nonempty continuation rows.  Hence, at
every constrained profile,

```text
C_i^- <= N_i <= C_i^+.                             (19)
```

Take `epsilon_m->0` and a convergent subsequence
`q^epsilon_m->q*`.  Condition the forced-Quit payoff on the current action of
`b(i)`.  If `q^epsilon_m_(b(i))->0`, its blocker-absent component is at least
`H_i^-`, while the blocker-present component has vanishing weight and all
finitely many rewards are bounded.  Thus

```text
liminf_m Q_i(q^epsilon_m_-i) >= H_i^- > C_i^+,
```

and (19) gives `Q_i>N_i` eventually.  Similarly, if the blocker rate tends to
one,

```text
limsup_m Q_i(q^epsilon_m_-i) <= L_i^+ < C_i^-,
```

so `Q_i<N_i` eventually.

These are exactly the two strict implications used in Section 3.  A core
rate tending to zero forces the predecessor's constrained rate to one; moving
one more step backward forces the next predecessor's rate to `epsilon_m`.
Odd alternation is impossible, so every core limit rate lies strictly between
zero and one.

For large `m`, each core coordinate is interior to `[epsilon_m,1]`.  Its
fractional-linear stationary payoff therefore has equal endpoints, and
continuity gives

```text
Q_i(q*_-i)=N_i(q*_-i).                              (20)
```

The calibrator best-response inequalities pass to the limit as in Section 4,
because the interior core gives one uniform positive opponent-absorption
denominator.  Set each core payoff coordinate to the endogenous common value
in (20), and each calibrator coordinate to its stationary payoff.  A core
player's Continue endpoint is

```text
A_i+beta_i N_i=delta_i N_i+beta_i N_i=N_i,
```

while its Quit endpoint is the same by (20).  Calibrator endpoint inequalities
are unchanged.  Joint and every player-deleted Continue mass contract, so the
same checked endpoint compilers prove exact terminal Nash against arbitrary
behavioral deviations and the uniform-payoff conclusion.

## Boundary tests

### Positive test with an active calibrator

Take three core players with

```text
b(0)=1, b(1)=2, b(2)=0,
z_0=z_1=z_2=0.
```

A quitting core player gets `+1` if its blocker Continues and `-1` if its
blocker Quits, independently of all other participation.  A continuing core
player gets zero.  Add one calibrator `c` with

```text
r(S)_c=1 if c in S,
r(S)_c=0 if c notin S.
```

Then

```text
q_0=q_1=q_2=1/2,
q_c=1
```

is an exact stationary profile with payoff `(0,0,0,1)`.  Each core player is
indifferent and the calibrator strictly prefers Quit.  Deleting any one
player's hazard still leaves a positive-rate core opponent for that player's
deviation problem.

### Strict nonpassive test for the interval theorem

Take the same three-player odd core and one calibrator `c`.  For every core
player `i`, put

```text
r(S)_i = 1_{c in S}          if i notin S,
r(S)_i = 2                   if i in S and b(i) notin S,
r(S)_i = -1                  if i,b(i) in S.
```

Give `c` payoff one when it Quits and zero otherwise.  Then

```text
C_i^-=0, C_i^+=1, H_i^-=2, L_i^+=-1,
```

so (18) holds, but no constant passive baseline exists.  The explicit exact
stationary profile has every core rate `1/3` and `c` Quit surely.  A core
Continue endpoint is one, and its Quit endpoint is

```text
2*(2/3)-1*(1/3)=1.
```

The calibrator strictly Quits.  This proves that the extension is strict on a
literal rational table.

### Same-background signs do not replace interval separation

Extend the empty-coalition payoff by zero.  For one core owner `i`, blocker
`b`, and third core player `k`, set in coordinate `i`

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

the forced-Quit and normalized Continue endpoints are exactly

```text
Q_i=1+8*epsilon,
N_i=10/(1+epsilon-epsilon^2).
```

Thus `q_b->0` while `Q_i-N_i->-9`, opposite to the required lower-face
orientation.  Conditioning on rare opponent absorption amplifies the blocker
row.  Mere backgroundwise toggle signs therefore do not support the compact-
limit proof; a further likelihood-ratio control would be needed.

### Exact even-cycle boundary

Oddness is necessary for the interior-core conclusion.  With two core
players, baseline zero, and the same `+1`/`-1` blocker payoff, the rate vector

```text
(q_0,q_1)=(1,0)
```

is exact stationary terminal Nash: player `0` strictly Quits because its
blocker Continues, and player `1` strictly Continues because its blocker
Quits.  The alternating boundary assignment closes on the even cycle.
This does not show nonexistence in the even case; it shows precisely why the
odd proof yields an interior core while the even case can escape purely.

Weak or overlapping interval inequalities can likewise permit a boundary
limit.  Coalition-dependent core continuation destroys the old identity
`N_i=z_i`, but the reviewed extension replaces that identity by the uniform
band control `C_i^- <= N_i <= C_i^+`.  The strict separation in (18), rather
than passivity itself, is the load-bearing hypothesis.

## Source correspondence and novelty

The checked sources inspected were:

- `IsStrictQuittingBlockerSwitch` and its stationary compiler in
  `UniformEquilibrium/Quitting/Classification/Existence/BlockerSwitch.lean`;
- `exists_uniformEquilibriumPayoff_of_conditionalFaceGap` and the literal
  range adapter in
  `UniformEquilibrium/Quitting/Classification/Existence/ConditionalFaceGap.lean`
  and `ConditionalFaceGapRange.lean`;
- the full-rate cap results in
  `UniformEquilibrium/Quitting/Stationary/FullRateStationaryVerifier.lean`;
  and
- the endpoint consumers in
  `UniformEquilibrium/Quitting/Stationary/EndpointCompiler.lean`.

The blocker-switch theorem imposes its structured condition on every player.
The conditional-face theorem likewise assumes one all-coordinate face box.
Neither allows a proper structured core while leaving every outside payoff
coordinate arbitrary.  The new content is the constrained stationary game on
the mixed core/calibrator box and the odd-parity limit which keeps only the
structured core away from the boundary.  The interval extension additionally
uses literal continuation-row extrema to replace the constant continuation
baseline; the cited checked theorems do not supply this partial-core band
argument.

The earlier signed-influence export assumes every directed signed cycle has
positive product and constructs a pure sure-exit set by SCC switching.  The
odd blocker cycle here has negative product and is deliberately outside that
theorem.  Conversely, the reviewed extension needs the uniform strict band
sandwich (18), which does not follow from a generic negative influence cycle
or from same-background toggle signs.  The two results are complementary, not
alternative proofs of the same class.

The tracked statement `Literature.SolanAndVieille2001.theorem1_2` in
`Literature/SolanAndVieille2001.lean` assumes the paper's
global unit-solo-exit and capped-joint-exit conditions and produces cyclic
approximate equilibria.  Those assumptions are neither implied by nor imply
(1)--(2), and that theorem does not state the partial-core stationary result.
No literature theorem is invoked in this proof.

## Actual-data adapter and downstream consumer

The source predicate has two finite reward-table versions.  For the original
special case:

```text
choose K, b, and z;
check (1) on every nonempty row omitting each core owner;
check both strict inequalities (2) on every remaining finite background.
```

For the reviewed interval extension:

```text
choose K and the cyclic blocker permutation b;
compute C_i^-, C_i^+, H_i^-, and L_i^+ from the finite literal rows;
check L_i^+ < C_i^- <= C_i^+ < H_i^- for every i in K.
```

No equilibrium, continuation value, or desired payoff is stored in the
predicate.  The proof constructs the stationary rates and calibrator payoffs
from those literal rows by constrained Kakutani and compact limit.

The original theorem constructs the exact fixed-point endpoint packet (13),
(15)--(17).  The interval theorem constructs the same packet with each core
value equal to its endogenous common endpoint (20).  Both outputs include
joint and player-deleted contraction.  The two named checked endpoint theorems
are the downstream semantic consumer.  They cover the full behavioral
deviation class and directly produce the uniform payoff.

## Lean handoff

A narrow formalization can introduce:

```text
CorePassiveContinuation reward core baseline
CoreStrictBlockerSwitch reward core blocker baseline
CoreIntervalBlockerSandwich reward core blocker
IsCyclicPerm core blocker
```

and target

```text
exists_stationaryUniformEquilibriumPayoff_of_oddBlockerCore
  (hodd : Odd core.card)
  (hcard : 3 <= core.card)
  (hcycle : IsCyclicPerm core blocker)
  (hpassive : CorePassiveContinuation reward core baseline)
  (hswitch : CoreStrictBlockerSwitch reward core blocker baseline) :
  exists root value,
    IsInteriorOn core root /\
    IsStationaryEndpointCertificate reward root value

exists_stationaryUniformEquilibriumPayoff_of_oddIntervalBlockerCore
  (hodd : Odd core.card)
  (hcard : 3 <= core.card)
  (hcycle : IsCyclicPerm core blocker)
  (hbands : CoreIntervalBlockerSandwich reward core blocker) :
  exists root value,
    IsInteriorOn core root /\
    IsStationaryEndpointCertificate reward root value
```

The topological producer is Kakutani on
`[epsilon,1]^K times [0,1]^(I setminus K)`, followed by compact subsequence
extraction and a finite odd-alternation lemma.  The stationary payoff formula
and endpoint algebra can reuse quantities from the full-rate stationary
verifier.  The terminal and uniform conclusions should be obtained by the
existing endpoint compiler, not stored as assumptions of the new source
structure.

Useful exact regression tests are the three-core/one-calibrator passive table,
the strict nonpassive `1/3` table, the likelihood-ratio reversal, and the even
two-cycle boundary above.

## Checked Lean realization

The constant-passive special case remains checked by
`IsLiteralStrictFiniteOddBlockerCore`,
`IsLiteralStrictFiniteOddBlockerCore.toStationaryFace`, and
`isUniformEquilibriumPayoff_of_literalStrictFiniteOddBlockerCore` in
`UniformEquilibrium/Quitting/Classification/Existence/FiniteOddBlockerCoreRowAdapter.lean`.

The literal interval extension is checked separately, without weakening the
source predicate. The four finite row extrema and their exact sandwich are
packaged by `IsLiteralStrictFiniteOddIntervalBlockerCore` in
`UniformEquilibrium/Quitting/Classification/Existence/FiniteOddIntervalBlockerCoreRowAdapter.lean`.
Its adapter `IsLiteralStrictFiniteOddIntervalBlockerCore.toStationaryFace`
feeds the abstract interval source in
`UniformEquilibrium/Quitting/Classification/Existence/FiniteOddIntervalBlockerCore.lean`.
The checked producer and unrestricted-behavior consumer are
`exists_stationaryCertificate_of_literalStrictFiniteOddIntervalBlockerCore`
and
`isUniformEquilibriumPayoff_of_literalStrictFiniteOddIntervalBlockerCore`.

Thus both the constant-passive special case and the strictly separated
interval-row family have `M`, `L`, `A`, and `C`. The interval theorem does
not replace the constant-passive declarations, and neither theorem covers
overlapping or weak bands, same-background signs without the global extrema
sandwich, arbitrary negative influence cycles, or even-cycle nonexistence.

## Scope and nonclaims

- The result does not solve an arbitrary negative influence cycle.
- It allows coalition-dependent core Continue rewards only under the literal
  strict band sandwich (18); it does not cover overlapping or weak bands.
- Same-background blocker signs without (18) are insufficient, as the
  likelihood-ratio regression shows.
- It does not restrict calibrator deviations; those are genuinely arbitrary
  and are consumed by the checked full-behavior theorem.
- It does not construct the pair-mass clock gadget requested in
  `INCENTIVE_GADGET.md` or settle the quitting-game conjecture.
- It makes no nonexistence claim for even cycles; only the interior-core proof
  and conclusion are shown sharp there.
- The later even-cycle parity corollary in the author's notebook is not part of
  this packet and is not asserted here.
