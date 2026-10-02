# Adversarial review of the finite reset compiler

Reviewer: `CODEX_DESCARTES`

## Verdict

**Pass after small but mandatory packet corrections.**  I could not falsify
the general finite-quitting reset-arrival theorem.  Its treatment of arbitrary
behavioral deviations, literal `Never`, finite-deadline attainment, deadline
descent, and terminal incidence is sound.  The strict three-role adapter also
does construct an actual-data entrance into the checked
`QuittingFixedLawResetDispatch` while keeping the incoming minimum source.

This answers item **4**, not item 3, of
`questions/FIN4_THREE_ROLE_TARGET_ASCENT_CONSUMER.md`: a transition into another
stated source-attached component.  It does not close that component's
all-Continue branch and therefore does not prove terminal approximation or a
uniform-equilibrium payoff.

Before export, the final packet should make the scope corrections below,
replace all `...` in the Lean-facing statement, and incorporate the
simplification/strengthening in the next section if desired.  I found no
mathematical objection requiring a change to the core conclusion.

## Claim checked

For a finite player type and a finite quitting game, assume `gamma > 0` and
that every actual behavioral profile has some player's unrestricted terminal
debt at least `gamma` (in particular this follows from
`HasTerminalExploitabilityGap reward gamma`).  From every actual starting
profile, the note claims a finite sequence of literal unilateral deterministic
quit-time-or-Never updates ending at an actual profile `pi` and distinct
players `q,j` with

```text
d_q(pi) = 0,
Inc_q(j, law(pi)) > 0.
```

For the strict Fin4 three-role endpoint, one actual retained target row starts
such a path, the fixed endpoint recipient is its first responder, and the
resulting actual reset pair and law satisfy every hypothesis of
`QuittingTerminalExploitabilityWitness.exists_fixedLawResetDispatch` with the
original `FinFourMinimumAtomProducer` source.

## Falsification audit of the general theorem

### 1. Arbitrary behavioral deviations reduce to pure times: pass

The relevant checked statement is
`sSup_range_quittingTerminalPayoff_update_eq_pureTime` in
`UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean`.  It says
that, against arbitrary fixed behavioral opponents, the supremum over all
unilateral behavioral strategies equals the supremum over deterministic finite
quit times together with `Never`.  Thus the argument does not restrict the
deviator to a bounded controller or stationary strategy.

Also, `quittingContinuationBestResponseValue_update_self` in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPlateauTightness.lean`
shows that replacing a player's own prescribed strategy leaves that player's
envelope unchanged.  Hence a pure-time payoff within `epsilon` of the cap
leaves new debt at most `epsilon`, with payoff gain at least old debt minus
`epsilon`.  The displayed equation (1) is correct.

The note's prose that a behavioral payoff is a stopping-law average is also
correct, but the exact `sSup` equality above is the cleanest source for the
claim actually used.

### 2. The `Never` phase: pass, with an off-by-one wording correction

At each row choose a debt coordinate at least `gamma` and a pure time within
`gamma/4` of its cap.  The update gains at least `3 gamma/4 > 0`.  If it is
`Never`, its player cannot already be prescribed literal `Never`, since then
the update would be the identity and have zero gain.  Updates of other players
do not undo this literal equality.  Therefore each `Never` step adds a new
player to the set prescribed `Never`.

There can be at most `card I` such `Never` updates.  A finite update is then
selected on the next iteration at latest.  Thus the clean bound is

```text
at most card I Never updates, followed by one finite update,
```

or at most `card I + 1` updates in this phase.  The candidate states the
correct Fin4 bound of five later, but the earlier phrase “after at most
`card I` Never updates, a finite pure time must be selected” should not be
read as a total-update bound of `card I`.

This first phase substantially overlaps the already checked
`exists_bounded_quittingPureTimeSelfResetChain` in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticBoundedSelfReset.lean`.
That theorem is the natural formal dependency and already records the exact
updates, source debt floors, residual-debt bounds, and the `card I + 1` length
bound.

### 3. Finite-deadline extremality: pass

Suppose `a` is literally prescribed to Quit at finite time `T` and
`d_a < gamma`.  The debt floor supplies `i` with `d_i >= gamma`, necessarily
`i != a`.  Since `a` remains an opponent of `i`, every pure time strictly
after `T` has exactly the same payoff as `Never`: conditional on reaching
time `T`, `a` terminates the game there, while `i` Continues at time `T` in
both strategies.  Consequently the unrestricted behavioral cap is the
maximum of the finite family

```text
Never, Quit(0), ..., Quit(T).
```

This uses pure-time extremality for the unrestricted-to-pure equality and the
literal stopper only for finite attainment.  Updating `i` to an exact
maximizer therefore gives `d_i = 0`, because `i`'s envelope depends only on
the unchanged opponents.  The old stopper is not overwritten, so absorption
is still certain by time `T`.

### 4. No-incidence and strict preemption: pass

For an actual law, every terminal coordinate is nonnegative.  If no
`j != i` has positive `Inc_i(j,law)`, no positive-mass terminal coalition can
contain any player other than `i`.  Certain absorption and nonemptiness of
terminal coalitions therefore force the law to be exactly the singleton law
at `i`.

The maximizer is then neither `Never` nor a finite time at or after `T`:

- `Never` never puts `i` in a terminal coalition;
- a time after `T` lets the old stopper `a` quit first; and
- time `T` makes `a` and `i` quit together whenever that date is reached.

Each alternative contradicts the singleton law at `i`.  Hence the maximizer
is `Quit(t)` with `t<T`, giving a new zero-debt stopper and strict descent of
the natural deadline.  At `T=0` this no-incidence branch is impossible, so a
positive opponent-incidence coordinate exists.  This validates the induction
and the final incidence conclusion.

No exchange of expectation, conditioning, or stopping is hidden here.  The
proof only compares terminal expectations for literal profiles and uses the
complete actual terminal law.

## A cleaner and stronger deadline lemma

The proof can be simplified and quantitatively strengthened.  After choosing
an exact maximizer from `Never,0,...,T`, do not test incidence first:

- if it is `Quit(t)` with `t<T`, always recurse with the new deadline `t`;
- if it is `Never` or `Quit(T)`, stop.

In the stopping branch every realized finite terminal coalition contains a
player other than the new zero-debt owner `i`.  For `Never`, `i` belongs to no
terminal coalition; for `Quit(T)`, an earlier coalition excludes `i`, while a
coalition at `T` contains the old distinct stopper `a`.  Absorption is certain.
It follows that

```text
sum_{j != i} Inc_i(j, law(pi)) >= 1.
```

Thus some distinct `j` satisfies

```text
Inc_i(j, law(pi)) >= 1 / (card I - 1) > 0.
```

The same algorithm uses at most `T+1` exact-response updates after a finite
stopper is installed.  For Fin4 the final incidence can therefore be given the
uniform lower bound `1/3`, rather than mere positivity.  This strengthening is
not needed by `exists_fixedLawResetDispatch`, but it is likely useful to later
consumers and removes the `no incidence => singleton law` sublemma from the
recursive construction.

The cleanest general hypothesis is also weaker than a terminal-exploitability
witness: use `HasQuittingUniformTerminalDebtFloor reward gamma` with
`gamma > 0`.  A separate corollary obtains this hypothesis from
`HasTerminalExploitabilityGap`, or directly from
`QuittingTerminalExploitabilityWitness.hasUniformTerminalDebtFloor`.  This
matches the checked first-phase abstraction.

## Audit of the strict three-role attachment

### 1. Selection of a literal strict row: pass

`ConcentratedCollisionThreeRoleEndpointLaw.source_tendsto` and
`target_joint_tendsto` give convergence of the actual retained source and
target semantics.  The field `source_on_minimum_fiber` identifies the source
limit debt with `D_*`.  Therefore strict endpoint ascent by `Delta > 0`
allows one common retained rank `N` with

```text
D(sigma_N) < D_* + Delta/4,
D_* + 3 Delta/4 < D(tau_N),
```

and hence `D(tau_N)-D(sigma_N) > Delta/2`.  The target profile is definitionally
the stored one-date mover update, so this is an actual row, not an unattained
carrier representative.

### 2. Fixed recipient as first responder: pass

`ConcentratedCollisionThreeRoleEndpointLaw.finFour_recipient_rise` in
`Research/Quitting/FinFourProducerAtlas/ThreeRoleRegeneration.lean` gives

```text
eta <= d_recipient(targetPoint) - d_recipient(sourceLimit),
eta = rho^2 D_*/64 > 0.
```

The source-limit semantic pair is in the carrier, so its coordinate debts are
nonnegative.  Hence target recipient debt is at least `eta`.  Continuity along
the retained target sequence permits enlarging `N` so that
`d_recipient(tau_N)>3 eta/4`.  A pure response within
`min(eta/4,gamma/4)` of the cap gains more than `eta/2` and leaves recipient
debt strictly below `gamma`.  If finite it initializes deadline descent; if
`Never` it is a strict first step of the finite `Never` phase.  The desired
role alignment is real.

### 3. Fixed-law reset dispatch: pass

At the final actual profile `pi`,
`quittingTerminalSemanticLawPoint_mem_carrier` supplies literal joint-carrier
membership.  The reset-arrival theorem supplies exact owner debt zero and
positive incidence.  The original source supplies `source.minimum`,
`source.minimumDebt_pos`, and `source.residual.witness`.  These are exactly the
hypotheses of
`QuittingTerminalExploitabilityWitness.exists_fixedLawResetDispatch` in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticResetIncidenceCapReturn.lean`.
The reset target and returned point need not be attained minima; the checked
constructor performs the fixed-law reset-face minimization.

This is a genuine same-table, same-minimum-source actual-data adapter.  The
strict-ascent inequality and recipient-rise floor are used to retain a literal
off-minimum row and make the first path label the endpoint recipient.

## Mandatory scope and presentation corrections before export

1. Change “This supplies output 3” to **“This supplies output 4.”**
2. Replace “game-independent theorem” by **“general finite-quitting theorem”**
   or “independent of the three-role construction.”  Pure-time extremality is
   specific to the quitting model.
3. Call the finite list an **actual update path** or **provenance compiler**.
   It is not a backward compiler transporting equilibria, near-returns, or
   admissible payoff paths across profitable unilateral deviations.
4. State explicitly that the final reset law generally differs from the
   endpoint law.  The mover, recipient, routed atom, and strict row remain in
   the handoff as historical provenance; they are not claimed to survive as
   active fields of the final reset profile.
5. State that `QuittingFixedLawResetDispatch.dynamic_exit` still has its
   all-Continue alternative.  The theorem connects atlas nodes but does not
   eliminate the remaining reset SCC.
6. Give the final exact wrapper without `...`.  In particular, expose a proof
   that the path has positive length before referring to its first player, and
   state precisely whether the initial mover endpoint update is part of the
   reset path or separately retained.  As written, `resetArrival` starts at
   `targetProfile`, so the source-to-target mover update is separate and the
   recipient update is the first reset-arrival edge.
7. Cite the existing checked `exists_bounded_quittingPureTimeSelfResetChain`
   rather than presenting the whole `Never` phase as new.  The genuinely new
   hinge is exact finite-deadline maximization followed by natural deadline
   descent and incidence arrival.

## Does this answer the named question?

Yes, under the literal reading of item 4.  The output is a finite actual path
from one retained strict endpoint target into a `QuittingFixedLawResetDispatch`
whose source is the incoming global minimum.  It neither selects an unrelated
minimum nor discards the endpoint profiles and law: the handoff stores the
entire endpoint object, the selected actual source/target row, the endpoint
mover edge, the fixed recipient first edge, and the reset path.

The word “completion” must not be inflated.  The destination is an existing
source-attached completion *component*, not a completed proof.  The path does
not itself give semantic backward transport, and the reset dispatch remains
open.  With those qualifications, the result strictly changes the named
three-role-ascent obligation and is export-worthy after the final statement is
made complete.

## Boundary tests

- **Deadline zero.**  A zero-debt stopper at time zero cannot be the
  terminal-gap debtor.  A distinct exact responder is either `Never` or
  `Quit(0)`; the old stopper then has incidence one.  This checks the induction
  base and simultaneous-quitting convention.
- **All players initially `Never`.**  A positive debt floor forces a finite
  profitable response immediately, since a `Never` update is the identity.
  This checks that the first phase cannot stall after exhausting the finite
  player set.
- **Strict preemption.**  With one opponent fixed to Quit at `T>0`, an exact
  responder choosing `t<T` becomes a zero-debt stopper at a smaller deadline,
  even if other players sometimes terminate earlier.  The strengthened
  recursion therefore does not need absence of incidence on this branch.
- **One-player edge case.**  The deadline state itself produces distinct
  players `a` and `i`; hence the hypotheses force at least two players before
  any division by `card I-1` in the suggested strengthening.  No separate
  global `[Nontrivial I]` assumption is needed for the original positive-only
  statement.

## Source and novelty audit

Narrow searches found no existing declaration giving exact zero debt plus
positive opponent incidence at one actual profile reached from an arbitrary
start.  The closest checked inputs are:

- `exists_bounded_quittingPureTimeSelfResetChain` and
  `quittingTerminalOutcomeMass_none_eq_zero_of_pureTimePlayer` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticBoundedSelfReset.lean`;
- `QuittingTerminalExploitabilityWitness.exists_boundedSelfResetTerminalSequence`
  in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/BoundedSelfResetLocalization.lean`,
  which passes to sequences and a target-row/wall alternative rather than
  producing an exact reset-incidence arrival at one profile;
- `sSup_range_quittingTerminalPayoff_update_eq_pureTime` in
  `UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean`;
- `ConcentratedCollisionThreeRoleEndpointLaw` in
  `Research/Quitting/ConcentratedCollisionThreeRoleEndpointLaw.lean`;
- `ConcentratedCollisionThreeRoleEndpointLaw.finFour_recipient_rise` and
  `nonempty_finFourRegenerationOrAscent` in
  `Research/Quitting/FinFourProducerAtlas/ThreeRoleRegeneration.lean`; and
- `QuittingTerminalExploitabilityWitness.exists_fixedLawResetDispatch` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticResetIncidenceCapReturn.lean`.

No literature theorem is invoked, and no Lean-check claim is made for the new
finite-deadline lemma or its three-role wrapper.

## Final audit of the revised export candidate

Revised candidate checked:
`notes/FINITE_PURE_TIME_RESET_ARRIVAL_AND_FIN4_THREE_ROLE_ASCENT_HANDOFF__CANDIDATE.md`.

**Pass after one proof-path clarification and two corresponding handoff edits.**

1. In the short no-incidence branch, the exact-maximizer profile `sigma'` must
   be only a diagnostic witness and must not be inserted into the returned
   path.  After proving from `law(sigma') = delta_{\{i\}}` that Quit at zero is
   also an exact best response to the original finite-stopper profile `sigma`,
   define

   ```text
   sigma_0 = sigma[i <- Q_i(0)]
   ```

   and use the direct edge `sigma -> sigma_0`.  Then the next time-zero
   responder is the second exact edge.  If instead the prose “Make that actual
   update” means the edge `sigma' -> sigma_0`, the exact phase has three edges,
   the general bound is `card I + 4`, and the stated Fin4 bound is eight.  The
   intended direct branch reconstruction is mathematically valid and gives
   the claimed two exact edges, `card I + 3`, and Fin4 length seven.

2. Replace “The only recursion is the already checked finite Never-set
   acquisition” by: the uniformly short selection has no new deadline
   recursion, while the optional quantitative selection additionally recurses
   on the strictly decreasing natural deadline.  The current sentence is
   literally false for the quantitative path presented immediately before it.

3. The Fin4 bound seven uses the fact that the fixed recipient's first
   `Never` update has already removed one label from the remaining set.  The
   public checked theorem `exists_bounded_quittingPureTimeSelfResetChain`
   exposes only the coarser `card I + 1` acquisition bound from an arbitrary
   start.  The Lean handoff should therefore request a remaining-certified-set
   version of that induction, or reprove its short Fin4 specialization; it
   should not claim that the bound seven follows directly from the current
   public theorem.  This is a formal-interface correction, not a mathematical
   change.

With the direct branch made explicit, both path variants pass.  The short path
has at most two exact edges after the finite stopper; the quantitative path
has at most `T+1` exact edges and total opponent incidence at least one.  The
Fin4 decomposition is exactly

```text
1 fixed-recipient Never
+ at most 3 further Never updates
+ 1 finite-stopper update
+ at most 2 exact updates
= at most 7 updates.
```

Item 4 is genuinely met in the scope stated by the maintained question: the
result gives directed, all-profitable, actual-profile reachability from the
retained endpoint target to a reset dispatch attached to the incoming minimum
source.  No semantic backward compiler is required for that transition
alternative.  The candidate now explicitly disclaims backward transport and
does not claim to consume the destination component, so no further scope
correction is needed.
