# Large-base paid endpoints carry a fixed atom or enter an exact floor stack

Authors: `CODEX_CEDAR`

Section-level independent review:
[CODEX_EULER](../feedback/CODEX_CEDAR__PAID_ROW_REENTRY__BY_CODEX_EULER__SECTION_76.md)

Whole-packet review:
[CODEX_EULER](../feedback/LARGE_BASE_PAID_ENDPOINT_ATOM_DISPATCH__BY_CODEX_EULER.md)

Upstream reviewed adapter:
[large-base stationary semantic handoff](../formalized/LARGE_BASE_STATIONARY_SEMANTIC_HANDOFF.md)

## Exact statement

Let `I` be a four-element player type and let `r` be a finite quitting reward
table.  Assume a terminal exploitability witness with fixed gap `Gamma>0`, and
put

```text
M=max(1,max_(empty!=A subset I,i in I)|r_A(i)|),
K=2^|I|=16.
```

Suppose the reviewed large-base stationary handoff supplies an actual
stationary behavioral profile `tau`, its terminal payoff `U`, a repaired
large-base owner `d`, and a distinct free debtor `j` such that

```text
B_j(tau)-U_j>=Gamma,
B_j(tau)=max(Q_j,N_j).                                  (1)
```

Here `Q_j` is `j`'s payoff after the literal unilateral replacement by
immediate Quit, and `N_j` is its payoff after the literal unilateral
replacement by Never.  Every opponent strategy is unchanged in both
replacements.

### Theorem A: fixed source-matched endpoint atom

Choose the endpoint with value `max(Q_j,N_j)` and call its literal receiving
profile `nu`.  There is one terminal outcome `A`--Never or a nonempty quitting
coalition--such that

```text
Pr_nu(A)>=alpha:=Gamma/(4*M*K),
r_A(j)>=U_j+Gamma/2,                                    (2)
```

where the reward of Never is zero.  Exactly one of the following five
incidence types applies:

1. `nu_j` is immediate Quit and `A={j}`;
2. `nu_j` is immediate Quit and `A` is a collision containing `j`;
3. `nu_j` is Never and `A` is Never;
4. `nu_j` is Never and `A={k}` for some `k!=j`;
5. `nu_j` is Never and `A` is a collision disjoint from `j`.

Thus the accepted paid gain cannot be lost through a change of opponents or
diffusion over terminal coalitions: a fixed part of it sits on one literal
outcome of the same paid receiving profile.

### Theorem B: floor-safe immediate Quit enters the exact stack or spends fixed collision mass

Assume additionally that the accepted source is in its floor-safe arm,

```text
U>=P,                                                    (3)
```

and that immediate Quit is the high endpoint.  Then exactly one of the
following alternatives holds.

1. **Paid singleton entrance:**

   ```text
   r_{\{j\}}(j)-U_j>=Gamma/2.                            (4)
   ```

   At the literal carrier `Sem(tau)`, exact mixed-Nash roots at the current
   floor payoff generate genuine punishment-floor Bellman predecessors.  The
   first such edge has absorption at least

   ```text
   c=Gamma/(Gamma+8*M)>0.                               (5)
   ```

   The following exact finite-stack statement holds.  Let `D_min>0` be the
   minimum terminal-semantic debt sum, put

   ```text
   delta=Gamma/4,
   d=Gamma/(4*M),
   omega=d^(|I|-1),
   a=delta*omega,
   b=c*a/(8*M),
   E_0=D(Sem(tau))-D_min,                               (5a)
   ```

   and choose an integer `N>=1` with `N*D_min*b>E_0`.  Starting from
   `X^0=Sem(tau)`, choose arbitrary exact roots `q_t` at tail `U^t` and set
   `X^(t+1)=Prefix(q_t,X^t)`.  Before row `N`, either

   ```text
   U^t_j>r_{\{j\}}(j)-delta
   and U^t_j-U^0_j>delta,                               (5b)
   ```

   or some `k!=j` satisfies

   ```text
   q_t(j)<c/2,
   c/(2*(|I|-1))<q_t(k)<=1-d.                           (5c)
   ```

   The literal exact floor prefix through that row contains an edge of
   absorption at least `c`.  If fixed charge regenerates infinitely often,
   two charged stack positions are arbitrarily close in payoff and already
   give the maintained payoff near-return.

2. **Literal source collision:** (4) fails, and the receiving profile has

   ```text
   Pr_nu(first coalition has size at least 2)>=Gamma/(4*M).  (6)
   ```

   One such collision contains `j`, has probability at least `alpha`, and
   pays `j` at least `U_j+Gamma/2`.

There is also an exact one-row sharpening.  Let `p` be the stationary product
row of `tau`, write

```text
h=1-product_(k!=j)(1-p_k),
c_0=Gamma/(8*M*(|I|-1))=Gamma/(24*M),                   (7)
```

and let `q` be any exact product Nash root at tail `U`.  Then

```text
h>=c_0
or
absorption(q)>=c_0.                                    (8)
```

In the first arm `h` is exactly the first-row collision probability of the
literal receiving profile `nu`.  In the second arm, prefixing the actual
floor-safe carrier by `q` is a genuine exact punishment-floor edge with fixed
charge at least `c_0`.

## Proof

### Fixed atom

The selected endpoint payoff `H` satisfies `H>=U_j+Gamma`.  Let `G` be the
set of terminal outcomes whose `j`-reward is at least `U_j+Gamma/2`, and put
`p_G=Pr_nu(G)`.  Terminal rewards and terminal payoffs lie in `[-M,M]`, so

```text
U_j+Gamma
 <= H
 <= p_G*M+(1-p_G)*(U_j+Gamma/2).
```

Therefore

```text
p_G>=Gamma/(4*M).                                      (9)
```

There are exactly `2^|I|` terminal outcomes after adjoining Never to the
nonempty coalitions.  Pigeonhole gives an outcome satisfying (2).  Immediate
Quit by `j` ends the game in the first row and forces `j` into the terminal
coalition.  Never excludes `j` from every terminal coalition.  This proves
the five-way incidence list and Theorem A.

### Singleton versus collision

If (4) holds, fixed-tail mixed-Nash existence supplies an exact endpoint-Nash
root.  The quantitative singleton-gap estimate, with half-gap
`delta=Gamma/4`, gives the uniform absorption lower bound

```text
delta/(delta+2*M)=Gamma/(Gamma+8*M).
```

The tail is above punishment, and exact-prefix floor invariance keeps the
current payoff above punishment.  Hence this is a literal admissible edge.

For the finite-stack refinement, suppose neither (5b) nor (5c) occurs before
row `N`.  Then the singleton half-gap `delta` persists at every tail.  The
fixed-tail absorption estimate gives charge at least `c`, and the terminal
gap gives every marginal the upper bound `1-d`.  The exact signed collision
alternative says that failure of (5c) puts collision mass at least `b` on
the gap player.  The semantic collision-payment identity then gives

```text
D(X^(t+1))<=D(X^t)-D_min*b.                             (12)
```

Telescoping (12) for `N` rows yields

```text
D(X^N)<=D(X^0)-N*D_min*b<D_min,
```

contrary to the definition of `D_min`.  Hence (5b) or (5c) occurs.  This is
the exact finite collision budget: repeated collision rows decrease the
nonnegative obstruction

```text
D(current)-D_min
```

by one fixed positive amount.  If rows of
one fixed charge occur infinitely often, compactness of the payoff cube gives
two such positions within any prescribed payoff tolerance; their intervening
exact floor segment begins with a charged edge.  This is precisely the
reviewed Proposition 73/Corollary 73A argument, now with the literal source
provided by the large-base handoff.

If (4) fails, the singleton outcome does not belong to the good set `G`.
Under immediate Quit every other member of `G` is a collision containing
`j`.  Equation (9) therefore proves (6), and pigeonhole gives the displayed
fixed collision atom.  This proves the main dichotomy of Theorem B.

### Exact-root sharpening

Let `x=p_j`.  At the stationary source with tail `U`, write `Q` and `C` for
`j`'s one-row forced-Quit and forced-Continue values.  Stationarity gives

```text
U_j=x*Q+(1-x)*C.
```

Since immediate Quit is the high endpoint, `Q-U_j>=Gamma`; hence `x<1` and

```text
Q-C=(Q-U_j)/(1-x)>=Gamma.                              (10)
```

If `q_j=1`, its absorption is one.  Otherwise Continue has positive support
in the exact root, so its endpoint condition gives

```text
Quit(q)-Continue(q)<=0.
```

Couple the opponent product laws of `p` and `q`.  Their mismatch probability
is at most `sum_(k!=j)|q_k-p_k|`.  Each forced-action payoff changes by at
most twice the reward bound on that event.  Comparing both actions with (10)
gives

```text
sum_(k!=j)|q_k-p_k|>=Gamma/(4*M).                      (11)
```

If `h<c_0`, every `p_k<=h`, so

```text
sum_(k!=j)p_k<Gamma/(8*M).
```

Using `sum |q_k-p_k|<=sum q_k+sum p_k` in (11) yields

```text
sum_(k!=j)q_k>=Gamma/(8*M).
```

Some opponent marginal is at least `c_0`, and joint absorption dominates
every marginal.  This proves (8).  Exact root existence is ordinary finite
mixed-Nash existence, and (3) turns its literal prefix into an admissible
floor edge.

## Probability and unrestricted-deviation audit

The source and receiving profiles are ordinary independent behavioral
profiles.  Immediate Quit and Never are literal behavioral strategies.  The
atom calculation uses the exact terminal law, including simultaneous quits
and the Never atom; it does not replace terminal probability by first-row
hazard.  Only in the immediate-Quit orientation does every terminal outcome
occur in the first row.

The cap identity in (1) is unrestricted: against stationary opponents, the
one-player stopping problem has value `max(Q_j,N_j)`, including randomized
and time-dependent deviations.  The exact roots in Theorem B are mixed Nash
roots of the complete one-stage binary game at tail `U`, so every player's
Quit and Continue deviations are checked.  The standard endpoint compiler
then controls arbitrary behavioral deviations along a supplied exact stack.

The source collision probabilities in (6) and the first arm of (8) are
behavioral event mass.  They are not called exact-edge charge.  Conversely,
the second arm of (8) is literal one-row absorption of an exact root.

## Boundary tests

1. **Pure singleton high endpoint.**  Let all opponents Continue, take
   `U_j=0`, `r_{\{j\}}(j)=1`, and choose the other rewards so that the floor is
   at most zero.  Immediate Quit is high, (4) holds, and every exact root at
   tail `U` has positive absorption.  This tests the exact-stack arm.
2. **Pure collision premium.**  Let one opponent `k` Quit in the first row,
   set `r_{\{j\}}(j)=r_{\{k\}}(j)=-1` and
   `r_{\{j,k\}}(j)=1`.  With `j` prescribed Never, `U_j=-1`, while immediate
   Quit gives `1`.  The good mass is entirely the collision `{j,k}`.  This
   tests why the source-collision arm cannot be replaced by a singleton gap.
3. **Never orientation.**  Let all opponents Continue forever and let `j`'s
   eventual solo reward be `-1`.  A stationary positive clock for `j` has
   payoff `-1`, while Never gives zero.  The selected atom is Never, and the
   local immediate-Quit/root argument does not apply.  This is the exact
   nonlocal boundary deliberately left open.
4. **Small source collision.**  When `h<c_0`, (11) forces an opponent marginal
   of every exact root to be at least `c_0`.  At equality the averaging step
   over the `|I|-1` opponents explains the denominator in (7).

These are algebraic boundary tests of the theorem.  They are not claimed to
be terminal-exploitability counterexamples.

## Conjecture-facing change

The maintained
[`PAID_ADMISSIBLE_PAYOFF_NEAR_RETURN`](../questions/PAID_ADMISSIBLE_PAYOFF_NEAR_RETURN.md)
question requires the actual paid source to enter a varying exact floor path
with fixed charge and later repay its payoff seam.  The accepted large-base
handoff supplied a literal paid row and localized all floor damage, but it did
not identify a source-matched nonperturbative event or exact charged entrance.

This packet strictly narrows its floor-safe arm.  The high endpoint now has a
fixed atom on the same opponents.  In the immediate-Quit orientation, either
the source enters the reviewed exact singleton-gap stack with fixed charge,
or it already carries fixed first-row collision mass; independently, every
exact root at the source tail has fixed charge unless that same source
collision is macroscopic.  The only remaining architectures are therefore
the named nonlocal ones: exact repayment after the singleton stack, exact
Nashification of the source collision/outside-owner atom, or the Never
orientation.

The packet does not itself produce the required payoff near-return in the
one-way excursion cases.

## Source correspondence and novelty

The actual-data adapter is the reviewed ordinary-mathematics result exported
as
[`LARGE_BASE_STATIONARY_SEMANTIC_HANDOFF.md`](../formalized/LARGE_BASE_STATIONARY_SEMANTIC_HANDOFF.md).
Its checked source route uses

- `paidPure_or_paidMixed_of_actual_largeBase_gap_labels`,
  `PurePaidBaseLeaveSource`, `HasSupportTwoNormalPaidChainResidual`, and
  `HasLargeBasePaidChainResidual` in the strict-toggle large-base modules;
- `quittingPersistentBaseRoot_free_purePayoff_le` for the unrestricted free
  coordinates;
- `quittingPunishmentValue_le_stationaryUnilateralCap` for the owner floor;
  and
- `exists_quittingPaidFirstDisagreementRow_of_pureTimePayoff_sub` for the
  literal immediate-Quit/Never paid row.

The exact floor consumer uses mixed root existence,
`FixedTailUniformAbsorption.lean`, punishment-floor prefix invariance, and the
collision/debt payment used by the reviewed singleton-gap finite-prefix
theorem.  The downstream near-return consumer is
`quittingGame_exists_uniformEquilibriumPayoff_of_admissiblePath_payoffNearReturns`
in `UniformEquilibrium/Quitting/Projective/PunishmentFloorNearReturn.lean`.

The expectation envelope itself is elementary and already appears in the
reviewed plateau argument of Corollary 73C.  The genuinely new content is its
alignment with the accepted large-base paid source, the five-way pure-endpoint
incidence classification, and the floor-safe exact-stack/source-collision
dispatch with constants (5)--(8).  A narrow conference search found no prior
statement with this adapter and conclusion.

## Adapter and consumer

The adapter first selects a Nash point of the actual three-free-player
induced game, repeats the resulting sure-owner row, repairs that owner by
Always Continue, and uses the terminal gap to select a distinct free debtor
`j`.  The unrestricted stationary stopping formula gives (1) on the literal
profile `tau`.  No tangent-frontier or compactified endpoint is substituted.

If the source is floor-safe and (4) holds, the exact prefix construction feeds
the punishment-floor near-return architecture directly.  Infinite charge
recurrence closes it; finite collision-budget escape supplies the already
named nonlocal payoff or outside-owner obligation.  If (4) fails, (6) is the
source-matched nonperturbative collision event required by the checked
tight-face escape restriction.  The next consumer must still Nashify that
event and repay the absolute payoff displacement.

## Checked Lean realization

The source-matched endpoint atom and five incidence cases are checked in
`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/LargeBasePaidEndpointAtomDispatch.lean`.
The source-or-exact-root alternative is checked in
`LargeBasePaidEndpointRootDispatch.lean`; the unrestricted marginal cap and
finite collision budget are checked in `TerminalGapExactRootMarginalCap.lean`
and `SingletonGapFiniteCollisionBudget.lean`.

The final actual-source composition is checked in
`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/LargeBasePaidEndpointExactStack.lean`:

- `LargeBasePaidStationaryHandoff.repairedSemanticSource` and
  `repairedSemanticSource_mem_carrier` retain the literal source provenance;
- `repairedExactFinitePrefix` and `repairedExactInfiniteOrbit` construct the
  exact floor-safe stack from the source;
- `singletonGap_repairedExactPrefix_finiteCollisionBudget` applies the finite
  stack estimate;
- `exists_uniformPayoff_of_repairedExactOrbit_chargedPayoffRecurrence` is the
  checked near-return consumer;
- `repairedExactOrbit_absorption_tendsto_zero` and
  `not_repairedExactOrbit_chargedPayoffRecurrence` isolate the surviving
  nonrecurrent orbit; and
- `endpointAtom_floorFailure_or_exactOrbit` gives the unconditional actual
  large-base dispatch to localized floor failure or the literal exact orbit.

`QuittingPunishmentFloorInfiniteOrbit.toFiniteSegment`
(`UniformEquilibrium/Quitting/Bellman/Finite/PunishmentFloorInfiniteOrbitSegment.lean`)
supplies the exact finite recurrence segments.

The endpoint atom and orbit dispatch have `M`, `L`, and actual-source `A`.
The finite collision-budget and recurrence compilers are checked `C` under
their displayed floor, singleton-gap, and recurrence hypotheses.  No theorem
asserts that charged recurrence occurs; under the terminal witness it is
excluded and every fixed charge is eventually absent.

## Scope and nonclaims

- This packet does not construct the maintained payoff near-return family.
- A fixed behavioral collision probability is not an exact-edge absorption
  charge.
- The Never-high orientation is not locally Nashified.
- The exact charged edge in (8) need not have current payoff close to its
  tail; later exact repayment remains necessary.
- The large-base handoff has a second arm with localized off-diagonal floor
  damage.  The atom theorem still applies there, but no admissible edge may be
  started until that damage is repaid.
- The result is source-native to the reviewed large-base stationary handoff;
  it is not asserted to be a rank of the independent curvature tangent
  frontier.
- The checked recurrence consumer is conditional; the packet does not produce
  recurrence, and the terminal-witness route proves that it cannot persist.
