# Independent review of `FIN5_FACE_CYCLIC_SEED`

**Reviewer:** `CODEX_EULER`  
**Date:** 2026-08-26  
**Verdict:** **PASS for the conditional five-phase debt theorem.  Keep the
producer and scalar-alignment claims internal and conditional.**

I independently derived the periodic payoff attachment and the deleted-player
Green account, checked every rotation and constant, and tested the theorem at
zero, mixed-root, empty-atom, and approximate-seam boundaries.  The displayed
bound

\[
D_i^t\le {5\over\rho_i}
  \left(\varepsilon+{5\delta\over\rho}\right),
\qquad \rho=\min_i\rho_i,
\]

is correct under the explicit hypotheses in the note.  The debt is the full
terminal deviation debt against arbitrary behavioral deviations.

The exact `epsilon=delta=0` compiler is already covered by the checked
periodic compiler once the atom hypotheses are converted to playerwise
opponent-cycle contraction.  The new Research target is therefore the
quantitative approximate-debt wrapper, not a second exact compiler.

## 1. Exact theorem reviewed

Fix a quitting reward table on `Fin 5`.  Let

```text
x : Fin 5 -> Fin 5 -> PMF Bool
v : Fin 5 -> Payoff (Fin 5)
```

and read the phases cyclically through `finRotate 5`.  Assume
`epsilon,delta>=0` and:

1. for every phase `t` and coordinate `j`,

   \[
   |v_j^t-F_j(x^t;v^{t+1})|\le\delta;
   \]

2. `x^t` is `IsεQuittingRootNash` against `v^(t+1)` with error
   `epsilon`;
3. for each player `i`, `x^i_i` is pure Continue and there is a nonempty
   `A_i` not containing `i` with

   \[
   \rho_i>0,
   \qquad
   \operatorname{CoalMass}_{x^i}(A_i)\ge\rho_i.
   \]

Let `u^t` be the actual terminal payoff of the literal periodically repeated
root word started at phase `t`, and let `D_i^t` be that profile's unrestricted
terminal deviation debt.  Then the displayed bound holds for every phase and
player.

## 2. Payoff attachment and the first factor `5`: PASS

Let

\[
\beta_t=\Pr_{x^t}(\hbox{all players Continue}).
\]

The root successor operator depends on a continuation coordinate with exact
scalar coefficient `beta_t`.  Since the actual cyclic payoff satisfies the
exact Bellman recursion, the approximate policy equation gives

\[
e_{i,t}:=|u_i^t-v_i^t|
 \le\delta+\beta_t e_{i,t+1}.                       \tag{2.1}
\]

At phase `i`, the all-Continue event and the exact nonempty coalition event
`A_i` are disjoint.  Hence

\[
\beta_i\le1-\rho_i\le1-\rho.
\]

Every rotated window of five consecutive phases contains phase `i` exactly
once.  Consequently the product of the five joint-Continue coefficients is
at most `1-rho`.  Iterating (2.1) once around the cycle gives

\[
e_{i,t}\le5\delta+
  \left(\prod_{s\in\operatorname{Fin}5}\beta_s\right)e_{i,t},
\]

and therefore

\[
|u_i^t-v_i^t|\le {5\delta\over\rho}.                \tag{2.2}
\]

All five residual terms have prefix weights at most one, so the numerator
`5 delta` is valid for every rotation.  No extra terminal term remains because
the word and both value families are exactly five-periodic.

The checked theorem
`abs_sub_quittingCyclicTerminalValue_le` in `PeriodicCompiler.lean` contains a
slightly more refined weighted version of the same cyclic-contraction
calculation.  The note's coarser `5 delta/rho` estimate is a correct
specialization.

## 3. Tail stability and local defect: PASS

Only player `j`'s continuation coordinate enters player `j`'s endpoint
difference.  Equation (2.2) therefore lets
`isεQuittingRootEndpointNash_of_tail_close` transfer every phase root from the
declared next value to the actual periodic continuation with error

\[
\eta_0=\varepsilon+{5\delta\over\rho}.              \tag{3.1}
\]

By `isεQuittingRootNash_iff_coordinateNashDefect_le`, the actual continuation
coordinate defect at every phase and player is at most `eta_0`.  There is no
missing factor two: endpoint difference is one-Lipschitz in the player's tail
coordinate, and the checked tail-stability theorem already packages the two
played-action inequalities.

This step remains valid for genuinely mixed roots.  It uses endpoint Nash for
the whole product root, not a pure-support approximation.

## 4. Opponent-Green account and the second factor `5`: PASS

Write

\[
m_{i,t}=\Pr_{x^t}(\hbox{every opponent of }i\hbox{ Continues}).
\]

The checked one-step theorem
`quittingRootSequenceTerminalDebt_le_actualCoordinateDefect_add` gives

\[
D_i^t\le\eta_0+m_{i,t}D_i^{t+1}.                    \tag{4.1}
\]

At phase `i`, the event `A_i` is an opponent-only absorbing event.  Since
`i` Continues surely there, its displayed root mass is literally an event in
the opponent product law after forcing `i` to Continue.  Thus

\[
m_{i,i}\le1-\rho_i.                                 \tag{4.2}

All deleted-player Continue factors are in `[0,1]`.  Iterating (4.1) through
one rotated five-phase window and using exact periodicity
`D_i^(t+5)=D_i^t` yields

\[
D_i^t\le5\eta_0+(1-\rho_i)D_i^t.
\]

Terminal debt is nonnegative, so division by `rho_i>0` proves the theorem.
The phase carrying the contraction depends on the deviating player, but every
five-step rotation contains that phase once; no common phase or common atom is
being assumed.

This is an unrestricted-strategy statement.  The one-step Green theorem's
left side is `quittingTerminalDeviationDebt`, whose cap ranges over arbitrary
behavior strategies.  Pure-time extremality is already built into the
underlying terminal-debt API; the proof is not confined to periodic or
stationary deviations.

## 5. Boundary and falsification tests

### `rho_i=1`

Then phase `i` has certain opponent absorption and `m_{i,i}=0`.  The displayed
bound reduces to the sum of at most five local errors.  The proof remains
valid; it does not divide by `1-rho_i`.

### Small positive `rho_i`

The `1/rho_i` blow-up is necessary for this Green argument.  As the unique
opponent absorption probability tends to zero, a local error can be carried
through order `1/rho_i` cycles before absorption.

### Empty atom

The nonempty hypothesis is essential.  An empty root atom is the
all-opponents-Continue event and gives no bound below one on `m_{i,i}`.  The
standard isolated negative-singleton cycle provides the exact failure mode:
one player mixes a finite Quit hazard forever while all its opponents remain
silent, its finite Quit and Continue endpoints are locally tied at a negative
value, but switching to Never gains a fixed positive amount.  Thus exact
phasewise Nash--Bellman equations alone do not control unrestricted debt when
the deleted-player survival product is one.  This is the boundary already
recorded in `AdmissibleCycleTerminalEquilibrium.lean`.

### Approximate seams

The proof spends one `delta` at each of five Bellman rows and then amplifies
by the single cyclic gap.  It does not require the seam errors to have a
common sign.  A two-sided sup-norm residual is sufficient.  If a later scalar
producer distributes error among multiple rows, the formal theorem should
either retain the phasewise error vector and use
`quittingCyclicResidualCharge`, or first bound every row by the stated common
`delta`.

### Mixed roots and simultaneous Quit atoms

No disjointness mistake occurs.  `A_i` is one exact nonempty coalition atom
not containing `i`; it is disjoint from all Continue and is contained in the
opponent-absorption event.  Other coalition atoms and simultaneous Quit
events only improve the contraction.

## 6. Quantitative counterexample consequence: PASS

Let

\[
a=\inf_\sigma\max_i d_i(\sigma)>0
\]

and let `alpha` be the largest actual-continuation coordinate root defect of
the five-period word.  Apply the theorem with `v=u`, `delta=0`, and
`epsilon=alpha`.  Then

\[
a\le\max_iD_i^t\le {5\alpha\over\rho},
\]

so

\[
\alpha\ge {a\rho\over5}.
\]

If every `rho_i>=a/(64M)`, then `M>0` is already forced by `a>0` and the
bounded-reward source, and

\[
\alpha\ge {a^2\over320M}.
\]

The approximate-seam inequality in the note is the direct rearrangement of
the same debt bound and is correctly oriented.

## 7. Exact compiler and subsumption audit

When `epsilon=delta=0`, the Bellman residual gives exact policy recursion and
tail stability gives exact local root Nash at the actual cyclic values.  For
each player `i`, (4.2) makes its full opponent-cycle product strictly less
than one.  Therefore the supplied roots and values satisfy the checked
`QuittingCyclicRepairCertificate` interface.

The exact conclusion is already subsumed by:

* `isZeroAsymptoticNash_quittingCyclicBehaviorProfile_of_certificate`; and
* `isUniformEquilibriumPayoff_quittingCyclicTerminalValue_of_certificate`

in `Quitting/Cycles/PeriodicCompiler.lean`, also wrapped by
`QuittingCyclicRepairCertificate` in `Diagnostics/Quitting/ExactRepairCertificate.lean`.
No punishment-floor hypothesis is required.  The note is correct to invoke
this compiler, but that exact arm is not new.

I found no named declaration giving the displayed approximate terminal-debt
constant.  Its proof is, however, a short composition of already checked
ingredients:

* quantitative cyclic policy evaluation from `PeriodicCompiler.lean`;
* tail stability from `Root/TailStability.lean`;
* coordinate-defect equivalence from `Root/NashDefect.lean`; and
* the one-step or finite telescope in `Root/TerminalDebtGreenAccount.lean`.

Thus the mathematical novelty is an exact supplied-object adapter and coarse
constant, not a new local-to-global principle.

## 8. Producer and scalar-alignment scope

The reviewed quiet-face extraction does not supply the hypotheses of the
conditional theorem unconditionally:

* its selected coalition may be empty, which fails (4.2); and
* its five reached suffix families are independently selected and do not
  supply one cyclic Bellman annotation with vanishing seam.

The scalar systems do separate by payoff coordinate because both successor
payoffs and endpoint differences use only the corresponding continuation
coordinate.  `finiteAffineIntervalFeasible_iff` can certify any correctly
assembled finite affine interval system.  It does not imply that an
infeasible system is witnessed by two literal face rows: closing-seam and
payoff-box rows are genuine constructors and may occur in the certificate.
The note now retains this distinction correctly.

The sentence that the other phase values are affine functions of one cut
scalar should be read only for the chosen exact-recursion/cut-seam
formulation.  A system allowing independent Bellman residual slack at every
phase needs those slack variables or the corresponding doubled affine rows;
the interval theorem alone does not eliminate them.

## 9. Research formalization recommendation

The narrowest honest Research declaration is the conditional theorem only:

```text
Fin 5 cycle roots + approximate Bellman values
+ phasewise IsεQuittingRootNash
+ for every player one designated phase with
   positive nonempty opponent-only coalition mass
-> terminalDeviationDebt(cyclicProfile, player)
   <= 5/rho_player * (epsilon + 5*delta/rhoMin).
```

The proof should reuse `abs_sub_quittingCyclicTerminalValue_le` or the direct
five-step joint-mass recurrence, then
`isεQuittingRootEndpointNash_of_tail_close`,
`isεQuittingRootNash_iff_coordinateNashDefect_le`, and
`quittingRootSequenceTerminalDebt_le_actualCoordinateDefect_add`.
The implementation should explicitly prove that `quittingCyclicOrbit phase`
visits the designated player phase once in five steps and that the selected
coalition mass bounds both joint and deleted-player survival.

Do not include an unconditional quiet-face adapter, a two-face scalar
certificate, or a new exact compiler in this first declaration.  The theorem
is suitable for the Research lane as a checked conditional interface test,
but it is not export-ready under the conference consumer gate because its
five-source cyclic annotation and nonempty-atom producer remain open.

## 10. Sharper general-cycle statement

The conditional theorem admits a useful strengthening.  The atom assigned to
player `i` need not occur at phase `i`, and player `i` need not Continue
surely at that phase.

Let `K>0`, let the finite player type be nonempty, and let

```text
markedPhase : I -> Fin K
rho         : I -> Real
atom        : I -> Finset I
```

satisfy, for every player `i`,

```text
0 < rho i,
(atom i).Nonempty,
i ∉ atom i,
rho i <= quittingRootCoalitionMass
  (cycle (markedPhase i)) (atom i).
```

No injectivity or surjectivity condition on `markedPhase` is needed: several
players may use the same phase and some phases may be unmarked.

Indeed, for `A=atom i` and `x=cycle (markedPhase i)`, product independence
gives

\[
\Pr_x(Q=A)
 =\Pr_x(i\text{ Continues})
   \Pr_{x_{-i}}(Q_{-i}=A)
 \le \Pr_{x_{-i}}(Q_{-i}=A).
\]

Because `A` is nonempty, the last event is contained in opponent absorption.
Therefore

\[
m_{i,\operatorname{markedPhase}(i)}\le1-\rho_i
\]

without forcing `i` to Continue.  The same nonempty full-root atom is also
disjoint from joint all-Continue, so it bounds the joint survival coefficient
at that phase.

Put

\[
\rho_{\max}=\max_i\rho_i.
\]

Choosing a player attaining this finite maximum shows that the joint
all-Continue product around one cycle is at most `1-rho_max`.  Hence the
general `K`-phase estimates are

\[
|u_j^t-v_j^t|\le {K\delta\over\rho_{\max}},
\]

and

\[
\boxed{
D_i^t\le {K\over\rho_i}
  \left(\varepsilon+{K\delta\over\rho_{\max}}\right).}
\]

The note's original theorem follows because its designated phase is `i` and
`rho_min<=rho_max`; its displayed constant with `rho_min` is therefore valid
but not sharp.  If a simpler first Lean statement is preferred, one may retain
`rho_min`; nevertheless the phase map and absence of an own-purity hypothesis
should be reflected in the strongest reusable Research interface.
