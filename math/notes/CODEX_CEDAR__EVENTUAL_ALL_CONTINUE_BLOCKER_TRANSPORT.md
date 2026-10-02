# Eventual all-Continue blocker transport

Author: `CODEX_CEDAR`
Status: `STATIC PLATEAU DATA INSUFFICIENT; THREE-CORE ROUTE INTEGRATED; PIVOTED`

Conjecture-closing thesis: assume a fixed positive
`HasTerminalExploitabilityGap reward gamma` and enter the eventual
all-Continue branch of the canonical exact dynamic tail.  The checked source
gives a positive-solo phantom owner and, at every positive solo hazard, a
strict joining opponent.  The proposed universal producer is a
**source-matched blocker chase**: choose the blocking opponent at the first
actual profitable history, reverse the resulting blocker orientation into a
finite ordered root block, and use the full behavioral terminal gap to show
that every failed block either enlarges its active support or transfers a
fixed amount of exploitability to a later reached history.  Finiteness plus
the exact survival account should yield either a support-rational divergent
path with vanishing paid defect or a positive floor-admissible return.  This
is a thesis, not a result.

Precise universal obligation changed by the next work: starting from the
literal data in
`QuittingPositiveDebtDynamicTailWitness.limitOwner_forall_quittingSoloJoiningObstruction`
and the same seam's exact terminal exploitability witness, construct one
finite **behavioral profile**, not a list of independent terminal rows, such
that every pure-time unilateral gain is below `gamma` unless a later reached
block carries a new blocker with a uniform survival-weighted gain.  The
construction must preserve one fixed target, exact chronological ordering,
and the distinction between a player's own survival and joint survival.

Kill criterion: abandon the blocker chase if an exact finite table and an
explicit sequence of reached blocker corrections show that the next
profitable pure-time deviation can jump to an earlier block or to `Never`
with no positive forward survival-weighted residue, even after the block
order and hazards are chosen adaptively.  A failure of a static stationary
or singleton certificate is not a kill criterion; it is already expected.

Next concrete question is pursued in
`notes/CODEX_CEDAR__FULL_CORE_JOINT_BLOCK_PRODUCER.md`.  Section 6 records the
source refresh: the three-coordinate ordered mechanism is already integrated
in a stronger ambient semantic-carrier theorem, so the live four-player
standard-Q obstruction has full normal core and cannot be reduced to another
three-cycle producer.

Everything in this note is ordinary mathematics unless a named Lean
declaration is explicitly said to be proved in Lean.  No Lean file or export
is proposed.

## 1. Self-contained question and source boundary

Let `I` be a nonempty finite player set and

`r : {S subset I | S nonempty} -> R^I`

a quitting reward table.  A uniform payoff must be one fixed target and must
be implemented, for every positive accuracy, against every unilateral
behavioral deviation at every sufficiently long finite horizon.  This note
does not weaken that contract to stationary or pure-time deviations.  It
uses pure quit times only when a checked extremality theorem supplies the
bridge to arbitrary behavioral deviations.

The chosen source is the eventual all-Continue residue in
`UniformEquilibrium/Diagnostics/Quitting/Chronology/EventualAllContinuePlateau.lean`.
The named checked facts inspected are:

- `terminalGap_le_limitDebt_le_soloReward_le_limitValue`: the canonical
  positive-debt owner has a positive singleton self-reward at least the
  terminal gap;
- `limitOwner_forall_quittingSoloJoiningObstruction`: every positive solo
  hazard is blocked by some strict opponent joining inequality;
- `limitOwner_endpointNash_requires_second_quitter`: any exact endpoint-Nash
  root at the owner's singleton payoff, with the owner active, must activate
  another player; and
- `limitOwner_exists_universalJoiner_or_switchingPair`: the affine obstruction
  is either one universal joiner or a pair of switching blockers.

The affine classification used by the last theorem is proved in Lean in
`UniformEquilibrium/Quitting/Punishment/BlockerIntervalCover.lean`.  The
strong stationary producer `isUniformEquilibriumPayoff_of_blockerSwitch`
(`UniformEquilibrium/Quitting/Classification/Existence/BlockerSwitch.lean`)
needs passive-continuation equalities and blocker signs against every
background coalition.  Those hypotheses do not follow from the plateau's
one-owner affine blocker data.

The exact consumer boundary remains
`VanishingDebtAtomChronologicalConsumer` and
`PaidFirstDisagreementAdmissibleReturnConsumer`
(`UniformEquilibrium/Diagnostics/Quitting/UniformExistenceBoundary.lean`).
An ordered-block construction here would instead aim first at the checked
support-rational divergent-path compiler; it is a genuinely different
endpoint route unless it also produces an exact admissible return.

Narrow searches also found two relevant no-go interfaces:

- payoff-cell preemption edges do not concatenate, and table-justified
  observer switches erase their positive cyclic weight
  (`QuittingSoloPreemptionCycle.target_ne_source_forcedCellGraph` and
  `QuittingStaticObserverSwitchData.augmentedCycleWeight_nonpos`); and
- asynchronous best-response correction may transfer a defect and then end
  at the zero-charge all-Continue root
  (`iterated_bestResponseReset_transfers_then_kills_defect` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPlateauMarkedResetCycleRegression.lean`).

Thus the sought object must be one reached behavioral chronology.  Neither a
player-label cycle nor an asynchronous correction list is sufficient.

## 2. Exact three-player plateau regression

The universal-joiner conclusion is substantially stronger than one positive
collision edge, but it still does not produce a positive Nash root at the
punishment floor.  The following exact table makes the deficit transparent.

Use cyclic players `1,2,3`.  For player `i` and an opponent coalition
`S subset {1,2,3} \ {i}`, define

`g_i(S) = 1_(i+1 in S) - 2*1_(i+2 in S)`,

with indices cyclic.  Define each payoff coordinate independently:

- if `i` belongs to the nonempty quitting coalition `Q`, put `r(Q)_i=1`;
- if `i` does not belong to `Q`, put `r(Q)_i=1-g_i(Q)`.

Hence every quitter gets exactly one.  The singleton rows are

```text
r({1})=(1,3,0),
r({2})=(0,1,3),
r({3})=(3,0,1).
```

### Proposition 2.1: exact punishment floor

Every player's behavioral punishment value is exactly one.

*Proof.* Quitting at date zero gives payoff one for every simultaneous
opponent action, so it guarantees one.  If every opponent always Continues,
the player receives either one when it eventually Quits or zero if it Never
Quits, so its best-response value is at most one.  Taking the infimum over
opponent profiles gives equality.  This argument includes arbitrary
behavioral opponent profiles in the lower bound.  ∎

### Proposition 2.2: unique root Nash at the floor

At continuation tail `P=(1,1,1)`, write `(x,y,z)` for the three Quit
probabilities.  The Quit-minus-Continue endpoint gaps are exactly

```text
G_1=y-2z,
G_2=z-2x,
G_3=x-2y.
```

The all-Continue root is the unique product Nash root.

*Proof.* The displayed formula is the expectation of `g_i` under the two
independent opponent actions.  If all three rates are positive, endpoint
Nash gives `y>=2z`, `z>=2x`, `x>=2y`, hence `x>=8x`, impossible for `x>0`.
If, for example, `x>0` and `y=0`, the first inequality forces `z=0`, while
the inactive third player requires `G_3=x<=0`, again impossible.  Cyclic
symmetry handles every partial support.  ∎

Thus the floor game has no positive exact admissible edge despite exact
punishment values and integer margins.

### Proposition 2.3: every pure toggle test passes with gap one

Every nonempty pure quitting coalition has a unilateral membership toggle
improving its member's payoff by at least one, while at the literal
all-Continue behavioral profile a singleton deviation improves zero payoff
to one.

*Proof.* At a pure opponent action, every `G_i` is an integer.  Directly:

```text
Q       one profitable toggle gain
{1}     player 3 joins, gain 1
{2}     player 1 joins, gain 1
{3}     player 2 joins, gain 1
{1,2}   player 2 leaves, gain 2
{2,3}   player 3 leaves, gain 2
{1,3}   player 1 leaves, gain 2
{1,2,3} any player leaves, gain 1.
```

At the empty coalition, literal nonabsorption pays zero and any player can
Quit alone for one.  These are exactly the finite pure-set conclusions of
`QuittingTerminalExploitabilityWitness.exists_toggle_gain`, but this table is
not claimed to possess a terminal exploitability witness: the calculation
shows that all those static necessary tests can hold without a positive root
at `P`.  ∎

### Proposition 2.4: a universal joiner for every owner

For owner `i`, player `i-1` cyclically is a universal joiner against every
positive stationary solo rate.  Its prescribed payoff at the owner's solo
exit is zero; Quitting immediately pays one whether or not the owner also
Quits.  Its deviation gain is therefore exactly one, independently of the
owner hazard.

In particular this table satisfies the strongest first branch of
`limitOwner_exists_universalJoiner_or_switchingPair` for every owner, not
merely the switching-pair alternative.

### Status of the regression

Propositions 2.1--2.4 are exact ordinary mathematics.  They do **not** give a
counterexample to uniform equilibrium or to the checked three-player closure.
They prove a narrower and conjecture-facing no-go: punishment-floor equality,
all pure terminal-gap toggle tests, and even universal joining for every
positive-solo owner do not imply a positive product Nash root at the floor.
Any proof of the eventual all-Continue branch must use an actual behavioral
chronology or another profile-level consequence of the terminal gap.

## 3. The reverse blocker order is the escape in the regression

The same table shows what the missing chronological information can look
like.  Take the ordered singleton owner word `(1,2,3)`, each with hazard
`h=1/2`, and repeat it periodically.  Let `C_1,C_2,C_3` be the phase values.
Solving

```text
C_1=(1/2)r({1})+(1/2)C_2,
C_2=(1/2)r({2})+(1/2)C_3,
C_3=(1/2)r({3})+(1/2)C_1
```

gives exactly

```text
C_1=(1,2,1),
C_2=(1,1,2),
C_3=(2,1,1).
```

At each phase the active owner's coordinate is exactly its singleton
self-reward one, and every coordinate is at least one.  Every player is
absent from two positive-hazard phases.  Thus these data have exactly the
arc/active/floor/divergence shape of the balanced singleton compiler.

The universal blocker arrows are

`1 -> 3 -> 2 -> 1`,

whereas the successful chronological owner word is their reverse

`1 -> 2 -> 3 -> 1`.

This orientation is not cosmetic.  Putting a collider immediately after the
owner reproduces its profitable early-joining deviation; placing it before
the owner lets the intervening continuation value pay the singleton envy.
The exact recurrence is the chronological datum absent from the static
universal-joiner statement.

The singleton rows coincide with those of the Flesch--Thuijsman--Vrieze
three-player table.  The existence of a balanced cyclic implementation for
that named table is already part of the checked/project literature surface;
no novelty or Lean status is claimed here for the mechanism.  Its use here is
as an exact diagnostic: a table can pass every static plateau obstruction and
escape only through ordered continuation values.

## 4. Proved and unproved separation

Proved in ordinary mathematics:

- the exact punishment value `(1,1,1)` of the regression table;
- the linear endpoint gap field and uniqueness of the all-Continue root at
  that tail;
- the gap-one pure-toggle audit for all eight pure profiles;
- a universal joiner of gain one for every positive-solo owner; and
- the exact reverse-blocker periodic recurrence with hazards `1/2` and phase
  values `(1,2,1)`, `(1,1,2)`, `(2,1,1)`; and
- Proposition 5.1's arbitrary-hazard criterion: under the six alternating
  strict singleton signs, the reversed three-cycle has an interior anchored
  floor solution exactly when the product of the three negative/positive
  margin ratios is below one, with the displayed unique hazards.

Unproved:

- the universal source-matched blocker-chase thesis;
- any implication from one universal joiner or switching pair to a balanced
  singleton/coalition block in an arbitrary game;
- any claim that the canonical eventual all-Continue seam supplies the extra
  singleton envy inequalities used by the regression's reverse cycle;
- a fixed target or an all-accuracy profile for the general game; and
- either exact direct consumer from `UniformExistenceBoundary.lean`.

Objection retained: the full behavioral terminal gap is much stronger than
the pure-toggle tests, but it is not a local row condition.  Applying it to
independently chosen blocker rows would lose the chronology again.  The next
argument must first define the whole ordered behavioral profile and only then
select its profitable pure-time deviation.

Concrete next check: Section 5 solves the arbitrary-hazard three-cycle
exactly.  The remaining question is source-facing: can failure of its escort
sign or product condition be converted, by applying the terminal gap to the
*whole ordered profile*, into a reached phase-stop/blocker transfer with a
strictly larger active support?  A rowwise application is insufficient.

## 5. Exact arbitrary-hazard reverse-blocker criterion

The three-block calculation can be completed in closed form.  Let

`b^k=r({k})`, `d_i=b^i_i`, and `a_(i,k)=b^k_i-d_i`.

Use chronological owner order `(1,2,3)` with hazards
`h_1,h_2,h_3 in (0,1)` and `c_k=1-h_k`.  The cyclic arc equations have the
unique solution

```text
C_1 = (h_1 b^1+c_1 h_2 b^2+c_1 c_2 h_3 b^3)/(1-c_1c_2c_3),
```

and its two cyclic rotations.  The three active-anchor equations are exactly

```text
h_2 a_(1,2)+c_2 h_3 a_(1,3)=0,                 (5.1)
h_3 a_(2,3)+c_3 h_1 a_(2,1)=0,                 (5.2)
h_1 a_(3,1)+c_1 h_2 a_(3,2)=0.                 (5.3)
```

Suppose the universal-blocker arrows point opposite the chronological word,
so

```text
a_(1,2)<0, a_(2,3)<0, a_(3,1)<0,
```

and suppose the other three cross-singleton excesses are positive.  Put

```text
lambda_1=-a_(1,2)/a_(1,3),
lambda_2=-a_(2,3)/a_(2,1),
lambda_3=-a_(3,1)/a_(3,2),
Lambda=lambda_1 lambda_2 lambda_3.
```

### Proposition 5.1

There are interior hazards satisfying all three active anchors if and only if
`Lambda<1`.  When they exist they are unique and can be written

```text
h_1=(1-Lambda)/(1+lambda_3(lambda_1+1)),
h_3=h_1/(lambda_2+h_1),
h_2=h_3/(lambda_1+h_3).
```

All phase values then satisfy every singleton floor `C_k(i)>=d_i`.

*Proof.* Equations (5.1)--(5.3) are equivalent to

```text
c_2h_3=lambda_1h_2,
c_3h_1=lambda_2h_3,
c_1h_2=lambda_3h_1.                              (5.4)
```

Multiplication gives `c_1c_2c_3=Lambda`, so interior hazards require
`Lambda<1`.  Conversely set `h_1` by the displayed formula, then
`h_3=h_1/(lambda_2+h_1)` and
`h_2=h_3/(lambda_1+h_3)`.  The first two equations of (5.4) hold by
construction.  Substitution into the third reduces it to

`lambda_1lambda_2lambda_3+
  (1+lambda_3(lambda_1+1))h_1=1`,

which is the formula for `h_1`.  Positivity and strict upper bounds follow
from positive `lambda_i` and `Lambda<1`.  Reversing the substitutions proves
uniqueness.

For the floors, fix player `1`.  Its phase-1 anchor and the phase-1 arc give
`C_2(1)=d_1`.  The phase-2 arc and (5.1) then give

```text
C_3(1)-d_1=-h_2a_(1,2)/c_2=h_3a_(1,3)>0.
```

Thus player `1` is at its floor in phases 1 and 2 and strictly above it in
phase 3.  Cyclic rotation proves the other coordinates.  ∎

For the regression table every `lambda_i=1/2`, hence `Lambda=1/8` and the
formula gives `h_1=h_2=h_3=1/2`.

### What the criterion isolates

A strict universal-joiner cycle supplies only the three negative excesses.
It does not supply the positive **escort** excesses on the reverse edges, and
even all six strict signs do not supply the quantitative holonomy condition
`Lambda<1`.  Proposition 5.1 therefore identifies the exact two additional
data a three-block source theorem must create:

1. a liked singleton row on the other side of each active phase; and
2. negative logarithmic holonomy
   `sum_i log(lambda_i)<0` around the reversed blocker cycle.

The second condition is genuinely cyclic: rescaling one player's payoff
coordinate cancels from its ratio but changing one cross-row margin can flip
the product without changing any sign.  The full terminal gap might price
this holonomy only through deviations from the entire ordered profile.  No
static singleton or collision inequality currently does so.

## 6. Source refresh: three-core elimination is already integrated

The explicit calculation above is not a missing producer.  The current source
contains a stronger theorem:

`exists_uniformEquilibriumPayoff_of_normalCore_card_three`
(`UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/AmbientCarrierElimination.lean`)

is proved in Lean and eliminates every game whose normalized singleton
matrix has a three-element normal core.  Its proof does more than the fixed
balanced cycle considered here: it labels the nonhomogeneous standard-Q core
as a positive directed cycle, starts from a literal Never semantic-carrier
point, performs three carrier-preserving ideal singleton resets, and iterates
a varying-height lasso whose total semantic debt tends to zero.  Ambient
players are retained throughout.

The exact matrix theorem
`standardQ_and_noHomogeneous_iff_exists_cyclic_labeling`
(`UniformEquilibrium/Quitting/Classification/LCP/ThreeByThreeZeroDiagonalQ.lean`)
also identifies Proposition 5.1's sign and product condition with the full
three-by-three standard-Q/nonhomogeneous chamber.  My calculation is an
independent fixed-cycle verification and supplies a closed hazard formula,
but it does not extend the integrated strategic boundary.

The same source proves
`normalCore_eq_univ_of_fourPlayer_not_exists_uniformEquilibriumPayoff`:
every hypothetical four-player counterexample has full four-player normal
core.  Thus continuing to refine the three-block blocker chase would violate
the conjecture-facing kill rule; that entire core size is already closed.
The remaining live direction is a full-core producer in which joint active
blocks or a different semantic-carrier return overcome the checked positive
debt barrier for reduced singleton lassos.
