# Whole-packet gate for `FIN4_SOLO_WALL_DEBT_DESCENT_OR_TWO_DEBTOR_HANDOFF`

Reviewer: `CODEX_EULER`

Verdict: **REVISE, then ACCEPT after the three literal source/typing repairs
below.**  The mathematics, finite wall termination, debt-descent constant,
stationary handoff composition, unrestricted-deviation audit, named frontier
narrowing, boundary tests, and Lean handoff otherwise satisfy
`exports/README.md`.  I found no new mathematical objection.

## Required repairs

1. The exact statement should quantify the witness whose field is used.  After
   `reward`, write for example

   ```text
   witness : QuittingTerminalExploitabilityWitness reward,
   Gamma=witness.terminalGap>0.
   ```

   Calling `Gamma` merely “its terminal exploitability gap” leaves the chosen
   witness implicit even though the handoff and decoder are witness-indexed.

2. `IsExactQuittingRootNash` is not the checked declaration name.  Replace the
   displayed source hypothesis by the literal checked predicate

   ```text
   IsεQuittingRootNash reward X.1 0 q.
   ```

   Alternatively define `IsExactQuittingRootNash` explicitly as that
   abbreviation before using it.  The proof already uses the zero-error
   predicate, so this is only a type spelling repair.

3. Correct and sharpen the source paths in `Source correspondence`:

   - `TerminalSemanticSoloSpineOccupation.lean` is directly at
     `UniformEquilibrium/Diagnostics/Quitting/`, not in a `Chronology/`
     subdirectory;
   - `exists_leave_or_join_gain` is in
     `UniformEquilibrium/Quitting/Classification/TerminalExploitabilityToggles.lean`;
   - `exists_atomicCollision_gain_of_normal` is in
     `UniformEquilibrium/Quitting/Boundary/Repair/PunishmentNormalAtomicCollision.lean`;
   - `quittingPersistentBaseNashSet_nonempty` is in
     `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseInducedGame.lean`;
   - the stationary envelope identity is in
     `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticNegativeVertexGerm.lean`,
     the oriented Quit-now/Never theorem in
     `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/LargeBaseStationarySemanticHandoff.lean`,
     and the paid-row decoder in
     `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPaidFirstDisagreement.lean`.

   Every cited declaration exists and has the asserted role; the only false
   path currently printed is the solo-spine `Chronology/` path.  The remaining
   additions make the mandatory declaration/file audit literal rather than
   referring to unnamed “subtrees.”

## Mathematical audit

### Wall and compact root split

The initial object is correctly called a literal carrier gate, not an attained
profile.  The repeated same-root wall theorem preserves its unique debtor,
owner pin, rate interval, floor provenance, and total debt.  At a reached wall
the exact-root set is a nonempty compact subset of the finite product cube.
If it avoids the singleton owner face, opponent absorption has a positive
minimum `omega`.  Exact debt transport then gives

```text
D(Prefix(z,W)) <= (1-omega)D(W),
absorption(z) >= OppAbs_k(z) >= omega.
```

The displayed relation orientation is correct: its payoff edge is
`W.1 -> Prefix(z,W).1` (tail to current), while behavioral execution reads
from the current prefix toward continuation `W`.

### Singleton face and diagonal compactification

For a singleton-supported exact root the affine blocker difference

```text
F(u)=(1-u)(s_i-W.1_i)+u c
```

has `F(x)>0` and `F(y)<=0`.  The all-Continue case `y=0` is excluded when
`c<=0`; the boundary `c=0` is excluded by `y<=1-d`; hence `c<0` and
`x<y<=1-d`.  Restart preserves the complete gate fields.

The packet includes the necessary `n_m>=m` condition.  For each fixed depth,

```text
Z_(n_m-t)=Prefix(root_(n_m-t-1),Z_(n_m-t-1))
```

passes to

```text
pair_t=Prefix(rho_t,pair_(t+1)),
rho_t exact at pair_(t+1).1.
```

This is exactly the checked solo-spine orientation.  Uniform owner hazards in
`[alpha,1-d]` give survival zero and a first row with positive Quit and
Continue mass, so the checked occupation theorem contradicts
`P_k<=s_k`.  The finite termination proof is complete.

### Triple join and stationary source

When the pair premium is positive, the full-gap membership-toggle split is
exhaustive.  The premium rules out removal of `i`; removal of `k` enters the
checked singleton-base handoff, while outsider join gives the pair-base
induced Nash construction.  Its free absorption is at least
`Gamma/(Gamma+2M)` and the three strict-superset masses sum to that quantity,
so the atom constant `Gamma/[3(Gamma+2M)]` is exact.  Two sure base quitters
make both free-player inequalities valid against arbitrary behavioral
deviations.  Terminal exploitability localizes a `Gamma` debtor to the base,
and the stationary cap/pure-time decoder gives the source-matched paid row.

The packet correctly separates provenance: the descent is a literal prefix
chronology; the stationary source is freshly selected on the same table and
is not claimed reached from the wall.

## Remaining gate items

- **Probability and agency:** independent private Boolean rows, arbitrary
  unilateral stopping laws in the semantic caps, and date-zero sure-base
  absorption are distinguished correctly.  No public correlation or
  stationary-only deviation test is smuggled in.
- **Adapter and consumer:** the two named upstream packets supply the literal
  carrier gate and compact constants.  The output strictly removes the solo
  selection and static triple-join residuals.  The paid near-return consumer
  is named but expressly not claimed satisfied.
- **Boundaries:** the arrow reversal, `c=0`/sure-Quit boundary, loss of compact
  separation near the singleton face, sharp three-atom pigeonhole, and
  nonchronological reselection tests all match the proof's load-bearing
  hypotheses.
- **Novelty:** the checked declarations contain the local carrier, toggle,
  handoff, and occupation pieces.  The finite restart/diagonal exclusion and
  composition consuming the triple join are the new reduction; no literature
  theorem is repackaged.
- **Lean handoff and nonclaims:** the proposed theorem decomposition is
  appropriately narrow.  It does not encode future regeneration, a Bellman
  return, or near-return as a field.  The nonuniform `omega`, carrier-limit
  source, same-table reselection, and terminal-mass-versus-Bellman-charge
  limitations are all explicit.

After the three literal repairs, my final verdict is **ACCEPT**.

## Final delta confirmation

The current packet explicitly quantifies `witness` and defines
`Gamma=witness.terminalGap`, uses the checked zero-error predicate
`IsεQuittingRootNash reward X.1 0 q`, and gives every corrected declaration
path listed above.  I rechecked the edited passages.  Final verdict:
**ACCEPT, with no remaining gate objection.**
