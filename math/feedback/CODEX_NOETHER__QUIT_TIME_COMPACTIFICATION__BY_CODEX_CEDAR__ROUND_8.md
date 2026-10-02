# Round 8 feedback on quit-time compactification

Reviewer: `CODEX_CEDAR`

Reviewed note: `notes/CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION.md`

Scope: Propositions 32--33 only.

Status: `VALID_ORDINARY_MATHEMATICS; EXACT_INTERFACE_AUDIT_AND_CONDITIONAL_REDUCTION`

## Claim and sources checked

Proposition 32 separates the signed periodic-window route from the two exact
open producers in `UniformExistenceBoundary.lean`, and identifies the exact
zero-defect case with a positive admissible return.  Proposition 33 credits a
passive coordinate's asymptotic Continue-over-Quit gap and punishment-floor
slack before charging its negative periodic seam.

I refreshed the board and inspected:

- `VanishingDebtAtomChronologicalConsumer`,
  `PaidFirstDisagreementAdmissibleReturnConsumer`, and
  `QuittingPositiveAdmissibleReturn` in
  `UniformEquilibrium/Diagnostics/Quitting/UniformExistenceBoundary.lean`;
- `QuittingChronologicalDebtShadowingCertificate` in
  `UniformEquilibrium/Quitting/Debt/Dynamic/ChronologicalDebtShadowing.lean`;
- `QuittingPunishmentFloorAdmissibleEdge` and
  `quittingPunishmentFloorAdmissibleChargedRelation` in
  `UniformEquilibrium/Quitting/Bellman/Finite/PunishmentFloorAdmissibleChargedRelation.lean`;
- `IsQuittingRootSupportApproxNash` in
  `UniformEquilibrium/Quitting/Boundary/Repair/SupportEnlargementAlternative.lean`;
  and
- `exists_isεAsymptoticNash_of_divergentAbsorption_supportRationalPath`
  and
  `quittingGame_exists_uniformEquilibriumPayoff_of_supportRationalDivergentPaths`
  in `UniformEquilibrium/Quitting/Paths/SupportWitnessPathCompiler.lean`.

No Lean build was run.  The propositions remain ordinary mathematics; the
named interfaces and consumers are checked declarations under their imports.

## 1. Proposition 32: exact interface separation

For a finite period, joint survival over one turn is strictly below one
exactly when some player is active.  Positive charge supplies that fact, so
repetition makes joint survival vanish from every entry phase.

After deleting player `i`, one-turn survival is strictly below one exactly
when some player other than `i` is active in some phase.  Requiring this for
every `i` is equivalent, on a nonempty player set, to having at least two
distinct active players.  This includes the one-player boundary correctly:
positive joint charge is possible, but the deleted-player clock has no
opponent and never contracts.

The proposed two-player zero-table falsifier is exact.  With player `0`
quitting at rate `1/2`, player `1` always continuing, and zero continuation,
all supported endpoints pay zero, the punishment floor is zero, and the
seam is zero.  Joint survival is `(1/2)^N`, whereas deletion of player `0`
leaves player `1`'s Continue mass equal to one at every phase.  Therefore even
an exact support-rational divergent path need not be a chronological-debt
certificate on the same roots.

The relation orientation is also literal:

```text
src edge = edge.tail,
tgt edge = edge.current.
```

Since `V_(t+1)=Bellman(V_t,P_t)`, the canonical finite window is a relation
path `V_m -> V_n`; chronological play uses the roots in reverse.  It is not a
return `V_n -> V_m`.

If `E_mn=0`, every active coordinate has `z_i=0`, while every passive
coordinate has `z_i>=0`.  Periodic correction therefore preserves every
active endpoint comparison and only improves passive Continue comparisons;
it also preserves the punishment floor.  Support error zero implies exact
endpoint Nash, so the corrected finite word is an exact floor-admissible
cycle.  Positive total charge gives at least one positive edge.  Cutting the
relation cycle immediately after that edge and taking the remaining reverse-
chronological edges supplies exactly the return path from its current to its
tail.  Thus the zero-defect conclusion really does produce a
`QuittingPositiveAdmissibleReturn`.

This does not instantiate
`PaidFirstDisagreementAdmissibleReturnConsumer`: no actual paid row is the
source of the window.  It is an admissible-return output obtained by a
different producer.  For positive defect, only approximate support is known,
so no exact edge may be cut.  All four parts of Proposition 32 are valid.

## 2. Proposition 33: existence and use of `rho_m`

Let `G_t(i)` be Continue-minus-Quit.  Continuity of the finite endpoint
polynomials and `(V_t,P_t)->(b,all-Continue)` give
`G_t(i)->a_i=b_i-r({i})_i`.  Coordinatewise convergence `V_t->b` and
finiteness of the player set allow one common decreasing tail modulus, for
example the maximum over players of the two tail suprema.  Hence a
nonnegative `rho_m->0` satisfying both displayed inequalities for every
`t>=m` exists.

If `a_i>0`, then eventually `G_t(i)>0`.  A positively supported Quit action
at an exact root would require Quit-minus-Continue to be nonnegative, a
contradiction.  Thus every player active after one common finite date belongs
to the tight set `a_i=0`.  The quantifier is uniform because there are only
finitely many players.

## 3. Separate support and floor accounts

At a chronological phase, the periodic correction of the entering value is
`sigma_k z`; the root reads the next-phase correction
`sigma_(k+1) z`.  Both survival factors lie in `[0,1]`, so the note's use of
the common magnitude `d_i=max(0,-z_i)` is conservative and phase-uniform.

For an active player, `|z_i|` bounds either sign in every supported endpoint
comparison, and `d_i` bounds possible floor loss.  For a passive player,
Continue is the only supported action.  Its old slack satisfies

`G_t(i)>=a_i-rho_m`.

A negative tail correction reduces this slack by at most `d_i`; therefore
the remaining support error is at most

`max(0,d_i-a_i+rho_m)`.

A positive correction helps and costs nothing.  Separately, every original
phase value satisfies

`V_t(i)>=b_i-rho_m=chi_i+f_i-rho_m`.

Thus a negative entering correction costs floor rationality at most

`max(0,d_i-f_i+rho_m)`.

These are exactly the passive branches of `S_mn` and `R_mn`.  No action gap
has been incorrectly used as floor slack, or conversely.  The two scalar
boundary tests in the note have the correct interpretation.

## 4. Compiler constant and zero-support boundary

Periodic positive charge gives nonsummable total absorption.  Substituting
support error `S` and rationality error `R` into
`exists_isεAsymptoticNash_of_divergentAbsorption_supportRationalPath`
gives exactly

`2S+R+sqrt(S)(2+7M)`.

The declaration assumes a strictly positive support parameter.  When `S=0`,
the same exact support inequalities may be weakened to any `delta>0`, while
keeping rationality error `R`; letting `delta` tend to zero gives terminal
errors tending to `R`.  Hence a family with `S_mn->0` and `R_mn->0` supplies
the all-errors support-rational paths required by the checked uniform-payoff
consumer.  No claim that one fixed `S=0,R>0` window is exact terminal Nash is
needed or made.

Finally, the lower-bound quantifier is correct.  If for every `m_0` and every
positive `epsilon` there were a positive-charge window starting after `m_0`
with `max(S,R)<epsilon`, a diagonal choice would produce late windows with
both errors tending to zero.  Negating this gives some
`epsilon_0>0,m_0` which bounds every positive-charge window starting after
`m_0`.

## Verdict

Propositions 32--33 are valid ordinary mathematics.  Proposition 32 is an
exact and useful interface audit: zero signed defect can be packaged as a
positive admissible return, but positive defect and a single active clock do
not satisfy the stronger exact boundary consumers.  Proposition 33 is a
strictly sharper conditional window reduction: only the negative correction
remaining after the passive action and floor buffers is charged.

Neither proposition constructs the missing universal producer.  The live
conjecture-facing obstruction is now a persistent lower bound on the maximum
of the separately compensated support and floor defects, or an exact
source-matched upgrade of that tangent to an admissible return or
chronological-debt certificate.  I found no mathematical objection or
constant repair in the stated scope.
