# Review of the Fin4 three-role ascent finite reset compiler

Reviewer: `CODEX_ROOT`

## Verdict

The finite pure-time reset-arrival theorem is mathematically valid and is a
genuine new producer.  Attached to one actual strict three-role endpoint, it
constructs an actual reset profile satisfying the complete input of the
checked `QuittingFixedLawResetDispatch`.  This answers the transition
alternative in `questions/FIN4_THREE_ROLE_TARGET_ASCENT_CONSUMER.md`, subject
to the scope corrections below.  It merits independent review and export-gate
treatment.

It does not consume the fixed-law reset dispatch's own dynamic-exit versus
all-Continue alternative, and therefore does not by itself prove terminal
approximants or a uniform-equilibrium payoff.

## General finite reset-arrival theorem

Assume a finite quitting game has a fixed terminal exploitability gap
`gamma > 0`.  From any actual behavioral profile one can reach, by finitely
many unilateral pure-time updates, an actual profile `pi` and distinct players
`q,j` such that

```text
d_q(pi) = 0,
Inc_q(j, law(pi)) > 0.
```

The proof has two well-founded phases.

### Acquiring a finite stopper

At every actual profile, choose a player with debt at least `gamma` and a
pure-time response within `gamma/4` of the cap.  The update has gain at least
`3 gamma/4` and leaves that player's debt at most `gamma/4`.

If the selected pure time is Never, the selected player was not already
prescribed Never, because that update would otherwise have gain zero.  As
long as no finite response has appeared, each step therefore strictly
enlarges the set of prescribed-Never players.  If a previously Never player
were selected with a finite response, that is already the desired phase
change.  Hence after at most `card I` Never steps, a finite stopper is
installed.

### Deadline descent

Suppose player `a` is prescribed to Quit at finite time `T` and has debt
strictly below `gamma`.  The gap selects another player `i` with debt at least
`gamma`.  Against the unchanged opponents, every pure time after `T` has the
same payoff as Never, so the behavioral cap is the maximum of the finite set

```text
Never, 0, 1, ..., T.
```

Choose an exact maximizing pure time and update `i`.  Its cap is unchanged by
its own strategy update, so its new debt is exactly zero.  The old stopper
still makes absorption certain by `T`.

If any opponent of `i` has positive terminal incidence, the construction is
done.  Otherwise every positive-mass terminal coalition is `{i}`; certain
absorption makes the complete law exactly the singleton law at `i`.  The
maximizer cannot be Never, cannot occur after `T`, and cannot equal `T`, since
the old stopper would then occur alone or simultaneously.  It is therefore a
finite time `t<T`.  Player `i` is a new zero-debt stopper with a strictly
smaller natural deadline.  Induction terminates.  At deadline zero, the next
distinct exact responder is either Never or Quit-at-zero, and the old stopper
has positive incidence in either case.

This proof handles unrestricted behavioral deviations because the checked
pure-time extremality theorem reduces every unilateral behavioral payoff to
the supremum of deterministic stopping-time payoffs.  The finite stopper then
turns that supremum into an attained finite maximum.

## Attachment to the three-role ascent

Strict ascent and semantic convergence select one retained finite rank at
which the endpoint target has literal total debt separated from its source.
The recipient-rise floor selects the endpoint's fixed recipient as the first
profitable pure-time responder.  Its update either supplies the finite stopper
immediately or starts the finite Never-set phase.  Thus the subsequent reset
arrival begins at the actual endpoint target and retains the complete incoming
source, endpoint profiles, roles, routed atom, and finite update path as
external provenance.

For the final actual profile `pi`, literal realizability gives

```text
(Sem(pi), law(pi)) in the joint terminal semantic/law carrier.
```

The incoming source provides the positive global minimum and terminal witness,
so `QuittingTerminalExploitabilityWitness.exists_fixedLawResetDispatch`
applies with the constructed zero-debt owner and positive-incidence player.
This is a real actual-data adapter to the existing fixed-law reset node.

## Required qualifications

1. In the current question, transition to another source-attached completion
   component is item 4, not item 3.
2. The finite pure-time list is a literal source-to-reset transition and a
   provenance certificate.  Calling it a “backward compiler” must not imply
   that equilibria, near-returns, or uniform payoffs at the final profile can
   be transported backward across arbitrary profitable unilateral updates.
   No such theorem is proved or needed for the stated same-game transition.
3. The final reset law need not equal the incoming endpoint law, and the fixed
   mover, recipient, and routed atom need not remain active at the final reset
   profile.  They remain stored historical provenance.
4. The fixed-law dispatch remains an open downstream node.  In particular its
   all-Continue arm is not consumed here.
5. The general reset-arrival theorem is stronger and cleaner than its Fin4
   application and should be stated first for an arbitrary finite player set.

## Sources checked

- `UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean`;
- `UniformEquilibrium/Quitting/Terminal/ExploitabilityGap.lean`;
- `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPlateauDebtTransfer.lean`;
- `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticResetIncidenceCapReturn.lean`;
- `Research/Quitting/ConcentratedCollisionThreeRoleEndpointLaw.lean`; and
- `questions/FIN4_THREE_ROLE_TARGET_ASCENT_CONSUMER.md`.

No Lean-check claim is made for the new reset-arrival or three-role adapter.
