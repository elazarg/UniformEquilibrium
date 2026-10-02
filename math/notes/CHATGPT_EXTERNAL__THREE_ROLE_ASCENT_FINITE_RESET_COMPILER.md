# Fin4 three-role strict ascent: finite pure-time reset compiler

Author: `CHATGPT_EXTERNAL`

Status: `PROOF_DRAFT`; ordinary mathematics, pending its independent gate.

Source: supplied in `ephemeral/ASCENT_NORM/` and moved here without rewriting
the mathematical body.

## Result

Let

```lean
source   : FinFourMinimumAtomProducer reward bound
packet   : QuittingReprojectionConcentratedPacket ...
endpoint : ConcentratedCollisionThreeRoleEndpointLaw
             source.point.1 packet mover recipient
```

and assume

```lean
hstrict :
  quittingTerminalSemanticDebtSum source.point.1 <
    quittingTerminalSemanticDebtSum endpoint.targetPoint.1.
```

Then the strict ascent has a source-faithful transition to an existing
`QuittingFixedLawResetDispatch`.

The transition starts at one actual retained endpoint row, not at an unrelated
carrier representative.  It keeps the incoming source and hard residual, the
fixed mover and recipient, the literal source-to-target endpoint update, the
routed terminal data, and a finite backward compiler consisting only of
unilateral pure-time updates.

The key new ingredient is a general finite normalization theorem:

> Under a fixed positive terminal exploitability gap, every actual behavioral
> profile admits a finite pure-time update path to an actual profile having one
> player of exact terminal debt zero and a distinct player of positive terminal
> incidence.

The path is well founded.  Before a finite stopping time is installed, every
`Never` update strictly increases the set of players already prescribed to
Never.  Once one player is prescribed to Quit at a finite deadline, every
source-preserving no-incidence best-response step strictly decreases that
natural deadline.

This is not a real-valued debt descent and does not use an unrelated reset
source.

## 1. Pure-time notation

For a player `i` and `t : Option Nat`, write `Q_i(t)` for

```lean
quittingPureTimeBehaviorStrategy reward i t.
```

For a profile `sigma`, define

```text
G_i^sigma(t)
  = u_i(sigma[i <- Q_i(t)]) - u_i(sigma),

d_i(sigma)
  = quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward sigma) i.
```

The pure-time envelope theorem gives

```text
d_i(sigma) = sup_t G_i^sigma(t).
```

Changing only player `i`'s prescribed strategy does not change `i`'s
best-response envelope.  Therefore, for every `epsilon > 0`, one can choose
`t` with

```text
G_i^sigma(t) >= d_i(sigma) - epsilon
```

and the updated profile satisfies

```text
d_i(sigma[i <- Q_i(t)]) <= epsilon.                 (1)
```

This is the only approximation used before the finite-deadline phase.

## 2. Acquiring a finite stopper

Assume a fixed terminal exploitability witness with gap `gamma > 0`.
Starting from an arbitrary actual profile `sigma`, repeat the following.

Choose a player `i` with

```text
d_i(sigma) >= gamma
```

and choose a pure time within `gamma / 4` of `i`'s cap.  Its gain is at least
`3 * gamma / 4`.

If the chosen time is finite, update `i` to that pure time.  By (1), `i` is now
a finite stopper whose debt is at most `gamma / 4 < gamma`.

If the chosen time is `Never`, update `i` to literal Never.  This strictly
increases the set

```text
{j | sigma j = Q_j(Never)}.
```

Indeed, `i` was not already prescribed to Never: otherwise its Never-update
would be the identity and would have gain zero.  Later updates of other
players do not remove `i` from this set.  A player already prescribed to Never
can never again have a positive-gain Never update.

There are finitely many players.  Hence after at most `card I` Never updates,
a finite pure time must be selected.  At the all-Never profile a positive-gap
witness certainly cannot be Never, since that update is the identity.

Thus every actual profile reaches, through a finite list of positive-gain
pure-time updates, a state

```text
(profile, stopper, deadline)
```

with

```text
profile stopper = Q_stopper(some deadline),

d_stopper(profile) < gamma.                         (2)
```

For `Fin 4`, the pre-deadline phase has at most five updates: at most four
Never updates and then one finite update.

## 3. Finite-deadline exact normalization

### Lemma

Suppose (2) holds.  Then there is a finite pure-time update path from `profile`
to an actual profile `finalProfile` and players `resetOwner != other` such that

```text
d_resetOwner(finalProfile) = 0,

0 < quittingTerminalOpponentIncidenceMass
      resetOwner other
      (quittingTerminalOutcomeMass reward finalProfile).
```

Every update in this phase is an exact pure-time best response with gain at
least `gamma`.  The recursion rank is the natural number `deadline`.

### Proof

The terminal-gap witness supplies a player `i` with debt at least `gamma`.
By (2), `i != stopper`.

Because `stopper` quits surely at `deadline`, every pure-time deviation of `i`
after `deadline` has the same payoff as `Never`: the game has already stopped
if it reaches the deadline.  Consequently `i`'s pure-time envelope is the
maximum of the finite family

```text
Never, 0, 1, ..., deadline.
```

Choose an exact maximizer `q` and put

```text
next = profile[i <- Q_i(q)].
```

Since `i`'s opponents are unchanged, exact maximization gives

```text
d_i(next) = 0.                                      (3)
```

The old stopper remains different from `i`, so `next` absorbs with probability
one by a finite deadline.

If some `j != i` has positive terminal incidence in `next`, (3) is the desired
arrival.

Otherwise every finite terminal coalition of positive mass contains no player
other than `i`.  Since the profile absorbs surely, its complete terminal law
is exactly the singleton law `{i}`.

The maximizer cannot be `Never`: a Never player belongs to no terminal
coalition, while the law has total finite mass one.  Write `q = some t`.
Moreover `t < deadline`.  If `deadline < t`, the old stopper quits first.  If
`t = deadline`, the old stopper and `i` quit together.  Either case contradicts
the singleton law `{i}`.

Thus the no-incidence arm produces another state of the form (2), now with

```text
stopper = i,
deadline = t < old deadline,
d_i(next) = 0.
```

Induction on the natural deadline terminates.  At deadline zero, a distinct
exact best responder either plays Never, giving incidence with the zero-debt
responder, or quits at zero together with the old stopper, again giving
positive incidence.

This proves the lemma.

## 4. The combined exact reset-arrival compiler

Combining Sections 2 and 3 gives the following game-independent theorem.

```lean
structure QuittingPureTimeResetArrival
    (start : (quittingGame reward).BehaviorProfile) where
  length : Nat
  profile : Fin (length + 1) ->
    (quittingGame reward).BehaviorProfile
  start_eq : profile 0 = start
  player : Fin length -> I
  choice : Fin length -> Option Nat
  step_eq : forall k,
    profile k.succ = Function.update (profile k.castSucc) (player k)
      (quittingPureTimeBehaviorStrategy reward (player k) (choice k))
  finalProfile : (quittingGame reward).BehaviorProfile
  final_eq : finalProfile = profile (Fin.last length)
  resetOwner other : I
  resetOwner_ne_other : resetOwner != other
  reset_debt_eq_zero :
    quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward finalProfile) resetOwner = 0
  incidence_pos :
    0 < quittingTerminalOpponentIncidenceMass resetOwner other
      (quittingTerminalOutcomeMass reward finalProfile)
```

The theorem is

```lean
theorem HasTerminalExploitabilityGap.nonempty_pureTimeResetArrival
    (hgamma : 0 < gamma)
    (witness : HasTerminalExploitabilityGap reward gamma)
    (start : (quittingGame reward).BehaviorProfile) :
    Nonempty (QuittingPureTimeResetArrival reward start)
```

The natural proof interface should additionally retain the two-phase rank:

```text
before a finite stopper: card {i | strategy i != Never};
after a finite stopper:  the stopping deadline.
```

It can be represented by a well-founded lexicographic sum.  Every recursive
edge strictly decreases that rank.  The output itself only needs the finite
path.

## 5. Choosing an actual strict-ascent endpoint row

Set

```text
D_*   = quittingTerminalSemanticDebtSum source.point.1,

Delta = quittingTerminalSemanticDebtSum endpoint.targetPoint.1 - D_*.
```

The strict-ascent hypothesis gives `Delta > 0`.

Let `sigma_n` and `tau_n` be the endpoint's retained source and target profiles.
Their semantic limits satisfy

```text
D(sigma_n) -> D_*,
D(tau_n)   -> D_* + Delta.
```

Choose one retained rank `N` such that

```text
D(sigma_N) < D_* + Delta / 4,
D_* + 3 * Delta / 4 < D(tau_N).
```

Then the literal endpoint row already has a strict finite ascent:

```text
Delta / 2 < D(tau_N) - D(sigma_N).                  (4)
```

The profiles are not reselected:

```text
sigma_N = ConcentratedCollisionFourRole.packetProfile packet
            (endpoint.ranks N),

tau_N = ConcentratedCollisionFourRole.targetProfile reward sigma_N
          (packet.mark (endpoint.ranks N)) mover.
```

The endpoint object still supplies the fixed recipient, routed terminal,
target joint-law convergence, routed mass floor, mover drop and recipient rise.

For a role-aligned first edge, let

```text
eta = packet.resolution^2 * D_* / 64.
```

The target recipient debt tends to a value at least `eta`.  Increase `N` if
necessary so that

```text
3 * eta / 4 < d_recipient(tau_N).
```

Choose a recipient pure-time response within

```text
min (eta / 4) (gamma / 4)
```

of its cap.  This first response has gain at least `eta / 2`, and the updated
recipient debt is strictly below `gamma`.  If it is finite, it directly starts
the deadline normalization.  If it is Never, it is the first strict step of
the finite Never-count phase.  Thus the final reset path begins with the
endpoint's fixed recipient rather than with an unrelated exploitability
witness.

## 6. Entering the checked fixed-law reset node

Let `pi` be the final actual profile, `q` the reset owner and `j` the positive
incidence player.  Define

```text
target = quittingTerminalSemanticPair reward pi,
mass   = quittingTerminalOutcomeMass reward pi.
```

Literal realizability gives

```text
(target, mass) in quittingTerminalSemanticLawCarrier reward.
```

The normalization gives

```text
quittingTerminalSemanticDebt target q = 0,
0 < quittingTerminalOpponentIncidenceMass q j mass.
```

Use the incoming source's retained fields

```text
source.minimum,
source.minimumDebt_pos,
source.residual.witness
```

in

```lean
source.residual.witness.exists_fixedLawResetDispatch
  source.point.1 target mass q j
  source.minimum source.minimumDebt_pos
  (quittingTerminalSemanticLawPoint_mem_carrier reward pi)
  reset_debt_eq_zero incidence_pos.
```

This returns

```text
returned : QuittingTerminalSemanticPair (Fin 4)

dispatch : QuittingFixedLawResetDispatch
  source.point.1 target mass q j returned.
```

Every field required by that existing node is therefore co-realized by the
same reward table and the same source.  The finite pure-time path is the
backward compiler from the literal strict endpoint target `tau_N` to the reset
target `pi`.

## 7. Source-attached handoff

The intended wrapper is:

```lean
structure FinFourThreeRoleStrictAscentResetHandoff
    (source : FinFourMinimumAtomProducer reward bound)
    (endpoint : ConcentratedCollisionThreeRoleEndpointLaw
      source.point.1 packet mover recipient)
    (hstrict :
      quittingTerminalSemanticDebtSum source.point.1 <
        quittingTerminalSemanticDebtSum endpoint.targetPoint.1) where
  endpointRank : Nat
  sourceProfile targetProfile : (quittingGame reward).BehaviorProfile
  sourceProfile_eq : sourceProfile = ...
  targetProfile_eq : targetProfile = ...
  target_eq_mover_update : targetProfile = Function.update sourceProfile mover ...

  separation : Real
  separation_eq : separation =
    quittingTerminalSemanticDebtSum endpoint.targetPoint.1 -
      quittingTerminalSemanticDebtSum source.point.1
  separation_pos : 0 < separation
  finite_ascent : separation / 2 <
    quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward targetProfile) -
      quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward sourceProfile)

  firstResponder_eq_recipient : ...
  firstResponder_gain_floor :
    packet.resolution^2 *
      quittingTerminalSemanticDebtSum source.point.1 / 128 <= ...

  resetArrival : QuittingPureTimeResetArrival reward targetProfile
  returned : QuittingTerminalSemanticPair (Fin 4)
  dispatch : QuittingFixedLawResetDispatch
    source.point.1
    (quittingTerminalSemanticPair reward resetArrival.finalProfile)
    (quittingTerminalOutcomeMass reward resetArrival.finalProfile)
    resetArrival.resetOwner resetArrival.other returned
```

The theorem is:

```lean
theorem nonempty_finFourThreeRoleStrictAscentResetHandoff
    (endpoint : ConcentratedCollisionThreeRoleEndpointLaw
      source.point.1 packet mover recipient)
    (hstrict :
      quittingTerminalSemanticDebtSum source.point.1 <
        quittingTerminalSemanticDebtSum endpoint.targetPoint.1) :
    Nonempty
      (FinFourThreeRoleStrictAscentResetHandoff source endpoint hstrict)
```

Consequently the existing exhaustive node refines to

```text
minimum target:
  FinFourThreeRoleMinimumTargetRegeneration;

strict target ascent:
  FinFourThreeRoleStrictAscentResetHandoff
    ending in QuittingFixedLawResetDispatch.
```

## 8. What is and is not closed

This supplies output 3 of the target-ascent question.  It is source preserving,
starts at an actual strict endpoint row, retains the complete endpoint object,
and gives an exact finite backward compiler into an already checked completion
node.

It does not claim that the reset dispatch's dynamic debt descent is renewable,
or that its all-Continue arm is consumed.  Those are descendants of the
existing fixed-law reset node, not unresolved provenance of the three-role
ascent.

The new mathematical hinge is the finite-deadline lemma.  Once a pure finite
stopper is present, cap nonattainment disappears, and every no-incidence exact
best response strictly decreases the actual stopping time.  That converts the
previously unstructured paid/response exit into a genuinely well-founded
source-faithful compiler.
