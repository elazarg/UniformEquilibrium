# Independent falsification review: finite-deadline Nash horizon escape

**Reviewer:** `CODEX_RAMSEY`  
**Source:** [`notes/CODEX_FERMAT__FINITE_DEADLINE_NASH_HORIZON_ESCAPE.md`](../notes/CODEX_FERMAT__FINITE_DEADLINE_NASH_HORIZON_ESCAPE.md)  
**Verdict:** **PASS as ordinary mathematics; minor source/handoff wording repair; do not export as a standalone result.**

I derived the finite timing-game construction independently before comparing
it with the prior review.  I found no mathematical counterexample, including
at zero tail denominators, zero Never mass, negative singleton reward, or
under unrestricted behavioral deviations.  The exact theorem is, however,
strictly subsumed by Sections 3--6 of
[`CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION.md`](../notes/CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION.md).

## Claim checked

Assume a finite nonempty player type and a uniform all-profile terminal gap
`gamma>0`.  For every `n`, the finite game in which each player chooses one
of `0,...,n,Never` has a mixed Nash equilibrium.  Its behavioral hazard
realization controls every listed pure time and Never, while some player gains
at least `gamma` by the first omitted time `n+1`.  Hence no table-uniform
finite menu of pure quit times, even augmented by Never, detects the global
gap on every profile.

## 1. Finite mixed Nash and probability mode

The timing game is a genuine finite game.  At a pure action vector, its first
finite minimum and tied minimizers are exactly the quitting date and quitting
coalition of the corresponding deterministic strategies.  Its all-Never row
has the repository cemetery payoff zero.  Thus the pure payoff table is
literally the quitting-game pure-time payoff table.

`GameTheory.exists_isNash_mixed` in
`GameTheory/Analysis/Nash.lean` supplies a mixed Nash equilibrium.  Mixed Nash
uses independent private player randomizations, which is exactly the product
probability mode required here; no public random variable or correlated
selection is introduced.

For player `i`, every permitted pure action has payoff at most the mixed
equilibrium payoff `P_i`.  Conversely `P_i` is the player's own mixed-law
average of those pure-action payoffs.  Therefore

\[
 \max_{t\in\{0,\ldots,n,\infty\}}V_i(t)=P_i.       \tag{1}
\]

This does not require every pure action to have positive equilibrium weight.

## 2. Exact behavioral hazard realization

Let

\[
 M_t=\mu_i(\{t,t+1,\ldots,n,\infty\})
\]

and use quit hazard `mu_i(t)/M_t` when `M_t>0`, and zero when `M_t=0`.
The exact induction invariant is

\[
 \Pr(T_i\ge t)=M_t.                                  \tag{2}
\]

If `M_t>0`, then

\[
 1-\mu_i(t)/M_t=M_{t+1}/M_t,
\]

so (2) advances.  If `M_t=0`, all masses from `t` onward, including Never,
are zero, while the live history already has probability zero.  The arbitrary
zero hazard on that unreachable tail therefore changes no stopping mass.
Consequently

\[
 \Pr(T_i=t)=\mu_i(t),\qquad
 \Pr(T_i=\infty)=\mu_i(\infty)                       \tag{3}
\]

in all boundary cases.

Applying the reconstruction coordinatewise preserves the independent product
law.  Hence terminal payoffs and every unilateral pure-time payoff agree with
the finite timing game.  The repository now contains the general checked
law-reconstruction map
`quittingStoppingLawBehaviorStrategy` and equality
`quittingBehaviorStoppingLaw_stoppingLawBehaviorStrategy` in
`UniformEquilibrium/Quitting/Terminal/StrategicallyPrecompactWatchdogProperBoundary.lean`.
These declarations explicitly cover the zero-denominator convention through
`StoppingLaw.toScalarHazard`.

## 3. The late value and the exact indexing

The behavioral realization may quit at dates `0,...,n` and is all-Continue
strictly after date `n`.  In the checked interface this is

```text
QuittingFiniteDeadlineNashProfile reward profile (n+1),
```

because its permitted finite dates are `t < deadline` and its all-Continue
tail begins at `deadline`.

Against the realized opponent laws, all finite deviations `t>n` have the same
payoff.  On paths absorbed by date `n` they agree with Never; if every opponent
selected Never, quitting at any such `t` makes `i` the sole quitter.  Therefore

\[
 L_i=V_i(\infty)+E_i r_i(\{i\}),                    \tag{4}
\]

where `E_i` is the product of the opponents' Never masses.  Formula (4) also
holds when `E_i=0` or the singleton reward is negative.  Its checked analogue
is `quittingRootSequencePureTimeTerminalValue_late_sub_none_eq` in
`TerminalSemanticFiniteDeadlineNashEscalation.lean`.

Thus date `n+1` itself realizes the common omitted value; no limiting or
supremum-attainment argument is needed for that step.

## 4. Unrestricted behavioral deviations

The checked theorem
`sSup_range_quittingTerminalPayoff_update_eq_pureTime` in
`UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean`
identifies the unrestricted behavioral best-response cap with the supremum
over deterministic finite times and Never.  By (1), all permitted values have
maximum `P_i`; by (4), all omitted finite values equal `L_i`.  Therefore

\[
 B_i-P_i=\max(0,L_i-P_i).                            \tag{5}
\]

Equation (5) is exact even if no arbitrary behavioral best response is
attained.  Applying the assumed global gap to the constructed profile selects
`i` with `L_i-P_i>=gamma`, and the literal deviation at `n+1` realizes that
gain.  This proves the main theorem.

For a nonempty finite time set `F`, choose `n>=max F`; for `F=empty`, choose
any `n`, such as zero.  The note has already incorporated this boundary.

## 5. Comparison with the checked consumer and Lean status

`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFiniteDeadlineNashEscalation.lean`
defines `QuittingFiniteDeadlineNashProfile` and proves its unrestricted
escape-charge consequences, but still assumes that certificate as input.  A
narrow search found no declaration constructing such a certificate from an
arbitrary reward table and deadline.

Accordingly, the **combined named producer wrapper is genuinely absent from
Lean**.  Its ingredients are not absent:

- `GameTheory.exists_isNash_mixed` supplies finite mixed Nash existence;
- `quittingStoppingLawBehaviorStrategy` realizes every complete stopping law,
  including its Never atom; and
- the checked payoff/stopping-law and pure-time-extremality declarations
  supply the strategic transport.

Thus the Lean handoff should no longer say that the Nash dependency or
finite-law hazard reconstruction might be unavailable.  The remaining task is
to package these checked ingredients and prove the finite timing-game payoff
identification.

This is the one wording repair I recommend in Section 8: replace the stale
instruction to “confirm” a generic finite mixed-Nash theorem with the exact
declaration above, and cite the now-checked canonical stopping-law
reconstruction rather than describing it as a missing primitive.

## 6. Subsumption and export assessment

Noether Sections 3--6 already prove:

1. the same finite-deadline mixed-Nash producer and hazard realization;
2. the stronger exact identity
   \[
   d_i=\max(0,E_i r_i(\{i\})-\sigma_i),
   \]
   where `sigma_i=P_i-V_i(Never)` is the finite-game Never slack; and
3. under a global terminal gap, a uniform positive adjusted deficit for every
   deadline and every finite-game Nash selection.

The Fermat horizon-escape statement follows by observing that the adjusted
deficit is exactly the gain of the common omitted late value and selecting
date `n+1`.  It is a particularly clean formulation, but it is not new
mathematics relative to that reviewed note.

Under
[`questions/ESCAPE_AWARE_FIN4_CERTIFICATE_SEARCH.md`](../questions/ESCAPE_AWARE_FIN4_CERTIFICATE_SEARCH.md),
the result is useful as a sound warning that fixed finite-horizon adversaries
are incomplete.  The question already records that warning as a non-answer,
and the theorem supplies neither an escape-complete relaxation nor a dual
certificate, semantic consumer, or positive-gap table.

**Export recommendation: do not make a standalone packet.**  It fails the
novelty/subsumption gate because Noether's adjusted-deficit theorem is
strictly stronger.  Retain the note internally as a concise regression and
use the missing named Lean producer as a formalization task if desired.

## 7. Scope confirmed

The theorem is conditional on a table-wide terminal gap.  It does not produce
such a table, a uniform-equilibrium payoff, a Bellman chronology, or an
escape-aware lower-bound certificate.  It rules out only a table-uniform
finite menu of pure-time witnesses; profile-dependent times and source classes
with additional compactness or reach control remain possible.
