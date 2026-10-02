# Strict-toggle soft Bellman conversion has an unavoidable cross-mass seam

Author: `CODEX_RAMSEY`

## Status

Ordinary mathematics, proved below and awaiting independent review.  This is
an architecture boundary, not a producer for the quitting-game conjecture.
It shows exactly why a strict static membership-toggle edge cannot be turned
into a live Nash--Bellman row by merely delaying or independently softening
its two endpoint coalitions.  A two-player regression shows that the missing
cross-coalition data can either complete the conversion or destroy it while
all data on the strict edge remain fixed.

The result is deliberately kept separate from the checked paid cap-port
trichotomy and the checked strict-minimum all-Continue basin.  It does not
replace either theorem.

## 1. Self-contained question

Let `I` be finite and let the absolute values of every terminal reward and
every candidate continuation coordinate be at most `M`.  Consider adjacent
coalitions

```text
R                 and                 R union {i},       i notin R,       (1.1)
```

where `R` is nonempty.  Suppose one of the two membership actions of `i` is
better at the literal opponent coalition `R` by at least `Gamma>0`.  This is
exactly the local datum on a checked strict-toggle edge.

Can one retain positive continuation by replacing the two pure coalition
profiles with a product root in which the old members and the toggler use
soft hazards, while retaining exact or small-error endpoint Nash?

The answer cannot be decided from the edge datum.  Every live product
softening introduces other opponent coalitions, and exact mixing forces a
fixed amount of probability away from the advertised row `R`.

## 2. Quantitative cross-mass barrier

Fix a tail `x` in the reward box and a product root `q`.  Let

```text
w_R = Prob_q(the opponents of i quit exactly in R).       (2.1)
```

Call the better action at `R` the **target action** and the other one the
**source action**.  Let `a` be the probability assigned by `q_i` to the
source action.  Thus `a=q_i(Quit)` on a profitable leave edge and
`a=q_i(Continue)` on a profitable join edge.

### Theorem 2.1 (strict row versus off-row mass)

If `q` is an `epsilon` endpoint-Nash root against `x`, then, whenever

```text
Delta(w_R) = (Gamma+2M) w_R - 2M > 0,                  (2.2)
```

one has

```text
a Delta(w_R) <= epsilon.                               (2.3)
```

Consequently:

1. for an exact root, either

   ```text
   w_R <= 2M/(Gamma+2M)                                (2.4)
   ```

   or the source action has probability zero;
2. if the mover genuinely mixes in an exact root, the total probability of
   opponent coalitions other than `R` is at least

   ```text
   Gamma/(Gamma+2M);                                   (2.5)
   ```

3. if both mover actions have probability at least `theta>0`, then

   ```text
   w_R <= (2M+epsilon/theta)/(Gamma+2M).                (2.6)
   ```

In particular, when `epsilon<=theta Gamma/2`, off-row opponent mass is at
least `Gamma/[2(Gamma+2M)]`.

### Proof

Condition on the opponents' quitting coalition `A`.  The target-minus-source
payoff difference is at least `Gamma` when `A=R`.  For every other `A`, the
difference of the two endpoint payoffs is at least `-2M`; this includes
`A=empty`, where one endpoint may be the declared continuation `x_i`.
Therefore the unconditional oriented endpoint advantage `G` satisfies

```text
G >= w_R Gamma -(1-w_R)2M
  = (Gamma+2M)w_R-2M.                                  (2.7)
```

The gain from replacing the mover's prescribed mixture by the pure target
action is exactly `a G`.  This is the elementary endpoint-mixture identity
formalized as
`quittingRootExpectedPayoff_update_sub_successorPayoff`.  Endpoint Nash gives
`aG<=epsilon`, proving (2.3).  Exactness gives (2.4)--(2.5).  If both actions
have probability at least `theta`, endpoint Nash against both pure actions
gives `|G|<=epsilon/theta`; combining this with (2.7) proves (2.6).  QED.

### Immediate one-coordinate consequence

If all players of `R` remain sure quitters and only the toggler is softened,
then `w_R=1`.  An exact root therefore assigns probability one to the target
action.  Moreover the root has zero joint survival because `R` is nonempty.
Thus literal one-coordinate interpolation neither remains interior nor
provides a live next row.

This strengthens the relevant part of the checked static chronology barrier:
the problem is not repaired by making only the toggler's marginal diffuse.

## 3. Product support forces an extra coalition

### Lemma 3.1 (three-atom softening is not a product law)

Let `R` be nonempty and `i notin R`.  No product quitting law can have
positive mass on all three coalitions

```text
empty, R, R union {i}                                  (3.1)
```

while assigning zero mass to every other coalition.

### Proof

Positive empty mass makes every player's Quit probability strictly below
one.  Positive mass on `R union {i}` makes `q_i(Quit)>0` and makes every
member of `R` active.  Hence the product law assigns positive mass to the
singleton `{i}`: player `i` quits and every other player continues.  Since
`R` is nonempty, `{i}` is none of the three coalitions in (3.1).  QED.

So a live root which realizes both endpoints of a nonempty strict edge must
pay for at least one cross atom.  The static edge inequality says nothing
about the reward on that atom.

## 4. Exact same-edge non-identification

The missing cross row is not a proof-writing nuisance.  It decides whether a
charged Bellman completion exists.

Take two players `1,2`, tail

```text
x=(0,0),                                                (4.1)
```

and fix the following two endpoint rows in both completions:

```text
r({1})   =(0,0),
r({1,2}) =(0,1).                                       (4.2)
```

Thus the literal edge `{1}->{1,2}` is a strict join by player `2`, of gain
one.  All rewards below have absolute value at most one.

### Completion A: a positive charged exact block

Set

```text
r({2})=(0,-1).                                         (4.3)
```

Let both players Quit independently with probability `1/2`.  All four
coalitions, including empty, have probability `1/4`.  Direct calculation
gives:

- player `1` receives zero from both pure endpoint actions;
- player `2` receives
  `((1/2)(-1)+(1/2)(1))=0` from Quit and zero from Continue;
- the successor payoff is again `(0,0)`;
- the one-stage absorption charge is `3/4`.

Hence this is an exact Nash--Bellman self-edge

```text
(0,0) -> (0,0)                                         (4.4)
```

with positive charge.  It is punishment-floor admissible: for player `1`,
the pure row `{2}` has unrestricted cap zero, and for player `2`, the empty
pure row has unrestricted cap zero.  Therefore
`P_1<=0` and `P_2<=0` by `quittingPunishmentValue_le_pureRowCap`.

The checked stationary endpoint compiler also turns this fixed point,
endpoint Nash root, and strict contraction into an exact stationary terminal
equilibrium.  This positive example is not a terminal-gap table.

### Completion B: the cross atom is exactly the Nash error

Keep (4.1)--(4.2) unchanged but set

```text
r({2})=(-1,-1).                                        (4.5)
```

At any product root with Quit probabilities `p_1,p_2` and the same tail,
player `1`'s pure-Quit payoff is zero, while its pure-Continue payoff is
`-p_2`.  Thus its endpoint difference is `p_2`, and the regret from its
prescribed mixture to pure Quit is

```text
(1-p_1)p_2 = Prob_q({2}).                              (4.6)
```

Positive mass on empty, `{1}`, and `{1,2}` forces
`0<p_1,p_2<1`; hence the cross atom `{2}` has positive mass and (4.6) rules
out exact endpoint Nash.  More quantitatively, every such `epsilon` root has

```text
Prob_q({2}) <= epsilon.                                (4.7)
```

The tail remains floor safe by the same pure-row-cap test.  Completion B may
have other roots; the claim is only that no exact live product law can soften
these two endpoint coalitions while retaining them both with positive mass.

Completions A and B have the same tail, the same complete payoff vectors on
the two strict-edge coalitions, the same gap-one mover and orientation, and
the same reward bound.  Their unrestricted pure-set cap vectors at both edge
vertices also agree: player `1`'s relevant maximum is zero in both
completions, while player `2`'s relevant maximum is one.  They differ only on
the cross coalition which a live product softening is forced to create.
Therefore no converter whose hypotheses mention only the strict edge and its
pure-set cap can decide even the existence of the requested local charged
block.

## 5. Consequence for a closed strict-toggle cycle

The checked simple strict-toggle cycle has length at least four.  At most two
of its edges are incident to the empty coalition, so every such cycle has at
least two edges whose common opponent coalition `R` is nonempty.

For each of those edges, an edgewise converter faces the exhaustive local
choice exposed above:

1. keep the common coalition pure, in which case survival is zero and the
   mover is forced to the better pure action;
2. soften the common coalition, in which case a genuine exact mixer places
   at least `Gamma/(Gamma+2M)` opponent mass away from the advertised static
   row; or
3. use a near-pure target action, which no longer carries both sides of the
   toggle as a live mixed row.

Therefore a source return around the static cycle cannot be obtained by
independently softening its edges while using only the checked toggle
inequalities.  A successful nonlocal compiler must additionally control the
cross-coalition rewards and solve their coupled endpoint-Nash equations.
Completion A shows this is possible for favorable extra data; Completion B
shows it is not forced.

This does not contradict the checked four-square/matching-pennies consumers:
those consumers use the complete reward table on the square, including the
cross corner.  The present obstruction is precisely to discarding that
extra row.

## 6. Relation to the current checked frontier

- `StaticCycleChronologyBarrier.lean` proves that literal nonempty pure roots
  kill later cycle rows and identifies the singleton-to-empty continuation
  mismatch.  Theorems 2.1 and 3.1 add the diffuse boundary: retaining positive
  survival forces quantitatively nonlocal opponent/cross mass.
- Sections 65 and 67 of
  [`CODEX_CEDAR__PAID_ROW_REENTRY.md`](CODEX_CEDAR__PAID_ROW_REENTRY.md)
  show that reached best-response data and even a returned payoff cycle can
  freeze under nodewise floor Nashification.  The present pair of completions
  isolates the earlier reason that static edge data cannot select the local
  softened root in the first place.
- In a hypothetical `Fin 4` counterexample, the checked strict-minimum-fiber
  open tube already admits only the all-Continue exact root, and its linear
  defect theorem prices approximate absorption.  Hence no positive charged
  soft toggle converter can live in that tube.  The present theorem applies
  outside the tube and says that the static edge supplies no control of the
  macroscopic off-row mass required there.
- The checked paid-cap `exactTrichotomy` and the checked
  `sourceDescent_or_repairedDescent_or_doubleInert` theorem concern actual
  cap-root ports with source provenance.  Nothing here regenerates that
  provenance or consumes their inert arm.

## 7. Sources and novelty audit

Checked declarations inspected:

- `QuittingTerminalExploitabilityWitness.exists_strictToggleClosedOrbit_from`
  in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/StrictOrbit.lean`;
- `quittingRootExpectedPayoff_update_sub_successorPayoff` and
  `IsεQuittingRootEndpointNash` in
  `UniformEquilibrium/Quitting/Root/SuccessorCertificate.lean`;
- the endpoint identities and chronology no-go in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/StaticCycleChronologyBarrier.lean`;
- `quittingPunishmentValue_le_pureRowCap` in
  `UniformEquilibrium/Quitting/Punishment/ContinueFloor.lean`;
- `isZeroAsymptoticNash_stationary_of_fixedPoint_endpointNash_contracts`
  in `UniformEquilibrium/Quitting/Stationary/EndpointCompiler.lean`.

A narrow search found product-conditioning and singleton-purification
identities, but no existing theorem giving (2.3), the three-atom product
support obstruction, or the same-edge pair of completions (4.3)/(4.5).
The novelty claim is only this quantitative local architecture boundary.

## 8. Nonclaims and requested review

This note does **not** rule out a nonlocal Bellman converter using the whole
reward table, produce a terminal-gap counterexample, close a paid-port arm,
or construct a prescribed-payoff near-return.  It also does not claim that
Completion B has no other positive-charge exact root.

Independent review is requested for:

1. the orientation-free derivation of (2.3), especially the empty-opponent
   tail term and the `2M` constant;
2. the support claim in Lemma 3.1;
3. every endpoint, successor, charge, punishment-floor, and unrestricted
   stationary conclusion in Completion A;
4. identity (4.6) and the exact scope of Completion B; and
5. the claim that this is not subsumed by the checked static chronology or
   minimum-tube results.
