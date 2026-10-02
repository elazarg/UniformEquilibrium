# Review of near-minimum retained-tail timing Nash identity no-go

**Reviewer identity:** `TIMING_IDENTITY_REVIEW`

**Verdict:** **PASS**

**Status:** second-round independent ordinary-mathematics audit; no Lean claim.

Source note:
[`CODEX_ROOT__NEAR_MINIMUM_RETAINED_TAIL_TIMING_NASH_IDENTITY_NOGO.md`](../notes/CODEX_ROOT__NEAR_MINIMUM_RETAINED_TAIL_TIMING_NASH_IDENTITY_NOGO.md)

## Second-round verdict

**PASS.** The repaired note closes the first-round objections. In particular,
it now defines the retained-tail normal-form game, proves the two pieces of
its recursion rather than applying the checked zero-tail theorem verbatim,
reconstructs the original timing law, and gives the missing Fin4
chronology--punishment--hazard--certificate composition. I found no remaining
mathematical objection to the stated ordinary-mathematics result.

This pass does not attach a Lean seal. The retained-tail normal-form adapters
and their Fin4 composition remain proposed formalization work, exactly as the
revised source audit says.

### Nash law gives every retained-tail certificate field

Fix a Nash law `mu` of `Gamma_N(tau)`, and let `roots` be the finite hazard
word obtained from its marginal timing laws. There are three exact payoff
identifications behind the adapter.

1. The mixed normal-form payoff of `mu` equals the terminal payoff of
   `quittingRetainedTailFiniteTimingGraft reward roots tau`. Independent
   hazard reconstruction reproduces the product timing law: the earliest
   finite declaration and its minimizing coalition have the same law, and on
   joint Never the profile resumes `tau`.
2. Replacing player `i` by the pure finite timing action `t<N` equals the
   behavioral pure-time deviation at `some t` from that graft. Therefore the
   Nash inequality against this pure action is exactly
   `IsQuittingRetainedTailFiniteTimingNash.finiteStop_le i t`.
3. Replacing player `i` by pure Never makes all of that player's finite
   hazards pure Continue and leaves `tau` unchanged after the word. Its
   behavioral realization is exactly
   `quittingRetainedTailFiniteTimingPassProfile reward roots tau i`.
   Therefore the Nash inequality against pure Never is exactly
   `IsQuittingRetainedTailFiniteTimingNash.pass_le i`.

These are all fields of `IsQuittingRetainedTailFiniteTimingNash`; the
structure asks only for the finite pure dates and pass-through comparison.
No hidden comparison with arbitrary behavioral deviations is needed at this
adapter stage. The checked theorem
`IsQuittingRetainedTailFiniteTimingNash.debt_le_deletedReturn_mul_tailDebt`
is precisely what later upgrades those supplied pure comparisons to the full
behavioral cap.

The survival identity is also exact. For each player, multiplying her finite
conditional Continue hazards telescopes to the probability that her timing
law declares Never. Rearranging the finite double product gives

\[
\operatorname{JointSurvival}(\text{roots})
 =\prod_i\mu_i(\infty).
\]

This remains valid if an intermediate survival becomes zero; both sides are
then zero. After the return-floor theorem makes the left side positive, every
individual Never mass is positive, as required by the recursion.

### Retained-tail recursion

The repaired Section 2 has the correct two deviations.

- Replacing only player `i`'s conditional shifted law changes whole-game
  payoff by the shorter-game gain times `prod_j C_j`. Positive joint Never
  implies every `C_j>0`, so ordinary normal-form Nash makes the conditional
  tail a Nash law of `Gamma_(N-1)(tau)`.
- Holding the conditional shifted law fixed and changing only the current
  Boolean marginal is an admissible timing-law deviation. Hence the current
  product root is Nash against the prescribed payoff of the conditional
  retained-tail graft.

After induction makes that graft pure Never, a finite all-Continue prefix
leaves its payoff exactly `U(tau)`. Section 1 therefore kills the current
Quit marginals, and equation (13) reconstructs the original law as pure
Never. Positive Never mass removes the only off-path failure; no
subgame-perfect assumption is being smuggled in.

### Fin4 punishment and constant chain

Take `chi_i` to be player `i`'s punishment value. The hard residual gives

\[
\chi_i\le r_i(\{i\}).
\]

The minimum-fiber theorem gives `Delta>0`, and semantic-pair convergence of
the actual chronology gives eventually

\[
U_i(\tau_n)\ge r_i(\{i\})+3\Delta/4.
\]

For each player, stationary approximation selects a root whose stationary
unilateral cap is strictly below `chi_i+Delta/8`. Taking its actual stationary
profile and using `quittingBestReplyValue_stationary` together with
`quittingContinuationBestResponseValue_eq_bestReplyValue` gives the required
actual punishment profile `pi_i` with

\[
B_i(\pi_i)<\chi_i+\Delta/8.
\]

With `kappa_floor=Delta/4`, the return-floor hypotheses follow exactly:

\[
U_i(\tau_n)\ge \chi_i+3\Delta/4
              \ge \chi_i+\kappa_{\rm floor},
\qquad
B_i(\pi_i)<\chi_i+\Delta/8
           =\chi_i+\kappa_{\rm floor}/2.
\]

The finite player set permits all punishment profiles to be chosen at once.
Separately, Section 1 uses the stronger singleton margin
`kappa=3 Delta/4`. Since every actual profile has debt at least `D_*`, set
`epsilon_n=D(tau_n)-D_*>=0`; (15) makes `epsilon_n` tend to zero, so one late
`n` satisfies the strict threshold (4). The two uses of `kappa` are distinct
and consistent.

The terminal witness supplies the exact positive `gamma` and
`HasTerminalExploitabilityGap`; any positive coordinate reward bound may be
used as `R` (and a bound can be enlarged if necessary). Thus the application
of `terminalGap_retainedTailFiniteTimingNash_jointReturn_ge` is valid and
produces the positive Never product consumed by Section 2.

### Source and wording repairs

The note now correctly records
`exists_finFour_minimumFiberIsolation_and_debtMoat_of_no_uniformPayoff`
as the existing qualitative overlap and identifies the explicit modulus plus
timing identity theorem as the additional content. It also corrects the word
“attained”: the identity law has joint return `1`, not equality with the
numerical return-floor constant.

## First-round review, superseded by the repaired note

The material below records the objections to the original version. Each
required repair listed there is now present and was rechecked above.

### Claim reviewed

The note claims three things.

1. If an actual tail `tau` is within `epsilon` of a positive global minimum
   `D_*`, lies uniformly `kappa` above every own-singleton reward, and `q` is
   an exact product Nash root against the prescribed payoff `U(tau)`, then
   `q` is all Continue under the displayed explicit threshold.
2. If every finite retained-tail timing Nash has positive joint return, then
   every such timing Nash is pure Never at every finite horizon.
3. The maintained Fin4 hard residual supplies all hypotheses needed to apply
   the checked retained-tail return-floor theorem and hence obtains the
   eventual identity conclusion.

I find Claim 1 correct, and Claim 2 correct after the retained-tail timing
game and its recursion are stated precisely. Claim 3 is not presently proved
by the note and is not an exact match to the current checked interface. The
missing pieces are elementary-looking but material adapters, so the proper
verdict is `REVISE`, not `PASS`.

### First-round 1. Robust one-stage rigidity: passed

Write `p_i=(q_i(true)).toReal` for player `i`'s Quit probability and

\[
H_i=\prod_{j\ne i}(1-p_j).
\]

The note's coordinate estimate is exactly the actual-profile specialization
of
`quittingTerminalDeviationDebt_rootThenContinuation_le_coordinateDefect_add`
(`UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean`). Exact root Nash
against the literal continuation payoff makes the defect vanish by
`isZeroQuittingRootNash_iff_coordinateNashDefect_eq_zero`
(`UniformEquilibrium/Quitting/Root/NashDefect.lean`). Thus

\[
d_i(q*\tau)\le H_i d_i(\tau)
\]

really controls the supremum over complete behavioral deviations; it is not a
one-stage or pure-time debt bound. The continuation in this declaration is
the prescribed payoff `U(tau)`, not the cap coordinate. There is no cap-versus-
`U` substitution in Section 1.

For a participant `j` with `p_j>0`, exact mixed-Nash support implies that the
Quit endpoint is at least the Continue endpoint. On the all-opponents-
Continue event the difference is

\[
r_j(\{j\})-U_j(\tau)\le-\kappa.
\]

On its complement both endpoints are current absorbing rewards in `[-R,R]`,
so their difference is at most `2R`. Consequently

\[
0\le-\kappa H_j+2R(1-H_j),\qquad
1-H_j\ge c:=\frac{\kappa}{2R+\kappa}.
\]

This support step is valid even when `p_j=1`; when both actions have positive
mass it gives indifference, and when only Quit has positive mass the Nash
inequality gives the required weak preference. The checked generic support
fact is `KernelGame.mixedGain_eq_zero_of_mem_support`
(`UniformEquilibrium/Diagnostics/FiniteMixedNashSupport.lean`).

The omitted pigeonhole detail is also valid. The product union bound

\[
1-\prod_{k\ne j}(1-p_k)\le\sum_{k\ne j}p_k
\]

shows that some opponent `k` has

\[
p_k\ge\beta:=\frac{c}{|I|-1}.
\]

For every participant `i`, the same endpoint argument gives
`1-H_i >= c >= beta`. If `i` is a nonparticipant, the selected `k` cannot
equal `i` because `p_k >= beta > 0`; hence `k` is an opponent of `i` and
`1-H_i >= p_k >= beta`. This verifies the claimed contraction of every
coordinate, including the initially selected participant and all
nonparticipants.

Summing and using that `q*tau` is an actual profile gives

\[
D_*\le D(q*\tau)\le(1-\beta)D(\tau)
   \le(1-\beta)(D_*+\varepsilon).
\]

For `beta<1`, the displayed threshold

\[
\varepsilon<\frac{\beta}{1-\beta}D_*
\]

is exactly equivalent to making the final expression strictly smaller than
`D_*`. If `beta=1`, the contraction factor is zero and positivity of `D_*`
already contradicts the inequality. Under the note's `R>0` one in fact has
`c<1` and hence `beta<1`, so the infinity convention is harmless but
unnecessary.

The global-infimum use is legitimate: no attainment is needed because the
prefixed profile is actual. The checked identification of the literal
infimum with a carrier minimum, when a minimum carrier point is used, is
`quittingTerminalDebtSumInf_eq_terminalSemanticDebtSum_of_minimum`
(`UniformEquilibrium/Diagnostics/Quitting/TerminalCapNashEndpointTransport.lean`).

One source-audit omission should be repaired. Fin4 already has a related,
non-explicit neighborhood theorem:
`exists_finFour_minimumFiberIsolation_and_debtMoat_of_no_uniformPayoff`
(`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinFourMinimumFiberIsolation.lean`)
puts every sufficiently near-minimum carrier prescribed payoff in a tube
where all Continue is the unique exact product root. The note's useful new
content here is the displayed general finite-player modulus, not the bare
eventual Fin4 uniqueness statement.

### First-round 2. Timing induction: mathematically valid, but the cited declaration was
not yet the needed theorem

For a retained-tail timing game with actions
`{0,...,N-1,Never}`, define the pure payoff by executing the earliest finite
declared date and, if everybody declares Never, literally resuming `tau`.
With that definition, the induction works.

Positive joint Never mass is the product of the players' Never masses, so it
forces every individual Never mass to be positive. In particular every
player has positive probability of continuing at the current date. A player
can replace only the conditional shifted tail of her timing law while
preserving her current Continue mass. Ordinary normal-form Nash then rules
out a profitable conditional-tail replacement because the whole-game gain
is the shorter-game gain multiplied by the strictly positive joint current-
Continue probability. Thus normal-form Nash plus positive Never masses is
sufficient; no subgame-perfect refinement is needed.

Once the conditioned shorter law is pure Never by induction, its prescribed
continuation payoff is exactly `U(tau)`. A finite string of all-Continue roots
before an actual tail does not change its terminal payoff. The current
Boolean root is therefore an exact one-stage Nash root against `U(tau)`, so
Section 1 makes it all Continue. Equal current marginal plus equal
conditioned tail reconstructs the original timing law, giving pure Never.
There is no surviving positive-reach off-path counterexample.

However,
`timingLawTail_isNash_of_isNash_of_positiveContinue`
(`UniformEquilibrium/Diagnostics/Quitting/FiniteDeadlineTimingRecursion.lean`)
is stated for `quittingFiniteDeadlineTimingGame`. In that checked game the
Never action is literal always-Continue forever and therefore has payoff
zero; it does not resume an arbitrary retained behavioral tail. The note
cannot cite that declaration verbatim for a game whose Never outcome pays
`U(tau)`. Moreover, the cited file supplies tail-Nash transfer but no generic
declaration that the current Boolean marginal is root Nash against the
conditioned-tail payoff. The table-specific proof in
`UniformEquilibrium/Diagnostics/Quitting/FinFourHardDeadlineTimingNashUniqueness.lean`
derives its current-root facts separately.

The revision should therefore include, in ordinary mathematics, all four
small adapters rather than call them “the standard recursion”:

1. the retained-tail finite normal-form game and its mixed-payoff/behavioral-
   graft identity;
2. conditional-tail Nash transfer under positive current Continue mass;
3. current-root Nash against the conditional-tail payoff, obtained by mixing
   current Quit with a lifted copy of the player's conditional tail; and
4. marginal reconstruction from current action and conditional shifted tail.

The checked analogues for Items 2 and 4 are respectively
`timingLawTail_isNash_of_isNash_of_positiveContinue` and
`timingLaw_eq_of_current_tail_eq`
(`UniformEquilibrium/Diagnostics/Quitting/FiniteDeadlineTimingRecursion.lean`).
The payoff remaining `U(tau)` after the induction is correct, but it should be
proved from the retained-tail Bellman identity rather than inherited from
the zero-tail checked game.

### First-round 3. Fin4 and the return-floor theorem: adapter gap

The current hard residual does supply the raw ingredients:

- `FinFourMinimumAtomProducer.minimumDebt_pos` and the fields
  `inf_pos`/`debt_eq_inf`
  (`Research/Quitting/FinFourProducerAtlas/Source.lean`) give `D_*>0` at the
  selected minimum point.
- `QuittingMinimumLawCausalSuffixAtom.chronology`
  (`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticLawCarrierCausalization.lean`)
  gives actual profile tails whose complete semantic pairs converge to that
  point. Hence their total debts converge to `D_*`, and the prescribed
  payoff convergence transports the positive minimum-fiber singleton gap to
  one uniform late `kappa`.
- `exists_pos_uniformSingletonGap_minimumFiber_of_punishmentNormal`
  (`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinFourMinimumFiberIsolation.lean`)
  gives the uniform positive gap on the minimum fiber. The hard residual's
  `all_punishmentNormal` field says the punishment value is below the own
  singleton reward.
- `source.residual.witness.terminalGap_pos` and
  `source.residual.witness.terminalExploitability` supply exactly the positive
  `gamma` and `HasTerminalExploitabilityGap` required by the return-floor
  theorem.

But these raw fields are not yet the hypotheses of
`terminalGap_retainedTailFiniteTimingNash_jointReturn_ge`
(`UniformEquilibrium/Diagnostics/Quitting/RetainedTailFiniteTimingReturnFloor.lean`).
That theorem consumes:

- a supplied root list satisfying
  `IsQuittingRetainedTailFiniteTimingNash`;
- actual player-indexed punishment profiles, not merely punishment values;
- a single explicit `kappa>0` separating the selected actual tail from those
  actual punishment caps; and
- the equality between the root-list joint survival and the normal-form
  timing law's joint Never probability if Section 2 is to consume its output.

None of these bridges is stated or proved in the note. The current project
map explicitly records the same boundary: the retained-tail return-floor
theorem has `M/L` only and there is no Fin4 adapter deriving the timing
certificate or uniform punishment separation (`docs/FRONTIER.md`, retained-
tail timing-Nash screen; `docs/TOOLKIT.md`, retained-tail variant).

The punishment-profile part appears repairable from checked ingredients:
`exists_stationaryRoot_cap_lt_punishmentValue_add`
(`UniformEquilibrium/Quitting/Paths/SupportWitnessIndividualRational.lean`),
`quittingBestReplyValue_stationary`
(`UniformEquilibrium/Quitting/Stationary/MinMax.lean`), and
`quittingContinuationBestResponseValue_eq_bestReplyValue`
(`UniformEquilibrium/Quitting/Classification/Existence/StationarilyGeneratedSemanticCarrier.lean`).
Because the player set is finite, one can choose one stationary punishment
profile per player within, say, `kappa/4` of the punishment value. But the
note must actually make this choice and check the inequalities.

Likewise, a mixed Nash of the newly defined finite retained-tail game should
yield the supplied `IsQuittingRetainedTailFiniteTimingNash` certificate by
checking every finite pure date and Never, and its hazard realization should
identify joint survival with the product of Never atoms. These are plausible
finite adapters, not consequences of the currently cited declarations.

Finally, “the return floor is attained only by the trivial block” is false if
“attained” means equality with the numerical lower bound. The identity block
has joint return `1`, whereas
`gamma^2 / (2*R*(gamma+2*R))` is generally strictly below `1`. The intended
statement is that, among the finite retained-tail timing Nash laws, the only
law to which the positive return floor applies is the identity law.

### First-round boundary and falsification audit

- **Zero Never mass:** later conditional play can be arbitrary and
  noncredible. The positive-return hypothesis is exactly what removes this
  counterexample.
- **Positive Never mass:** every current Continue denominator and the joint
  reach multiplier are positive, so ordinary normal-form Nash does transfer
  to the conditional tail. No off-path failure remains.
- **Cap versus prescribed payoff:** Section 1 correctly uses `U(tau)`.
  Section 3 still needs an explicit construction turning punishment values
  into actual profiles with bounded continuation-best-response caps.
- **Tail payoff after a finite identity prefix:** it remains exactly
  `U(tau)`; no discounting or finite-horizon averaging error is introduced in
  terminal semantics.
- **Global minimum:** the contradiction uses the literal infimum over all
  actual behavioral profiles and the prefixed profile is actual, so no
  carrier-attainment assumption is hidden.
- **Threshold:** the strict inequality and factor
  `beta/(1-beta)` are exact. Equality at the threshold would not give a
  contradiction and must remain excluded.

### First-round required revision

Retain Section 1, adding the one-line product union bound and the exact
declaration names. Expand Section 2 into a self-contained retained-tail
normal-form recursion with the four adapters above. Expand Section 3 into an
actual composition: choose late chronology tails and one uniform `kappa`,
construct the punishment profiles, obtain a mixed Nash of the retained-tail
game, convert it to `IsQuittingRetainedTailFiniteTimingNash`, apply the return
floor, identify joint survival with joint Never mass, and then invoke the
induction. Until those steps are written, (13) is a plausible repair target,
not an established consequence of the current checked Fin4 residual.

### Files and declarations inspected

- `quittingTerminalDeviationDebt_rootThenContinuation_le_coordinateDefect_add`
  (`UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean`)
- `isZeroQuittingRootNash_iff_coordinateNashDefect_eq_zero`
  (`UniformEquilibrium/Quitting/Root/NashDefect.lean`)
- `KernelGame.mixedGain_eq_zero_of_mem_support`
  (`UniformEquilibrium/Diagnostics/FiniteMixedNashSupport.lean`)
- `timingLawTail_isNash_of_isNash_of_positiveContinue` and
  `timingLaw_eq_of_current_tail_eq`
  (`UniformEquilibrium/Diagnostics/Quitting/FiniteDeadlineTimingRecursion.lean`)
- `quittingFiniteDeadlineTimingGame`
  (`UniformEquilibrium/Diagnostics/Quitting/FiniteDeadlineTimingGame.lean`)
- `IsQuittingRetainedTailFiniteTimingNash` and
  `IsQuittingRetainedTailFiniteTimingNash.debt_le_deletedReturn_mul_tailDebt`
  (`UniformEquilibrium/Diagnostics/Quitting/RetainedTailFiniteTimingNash.lean`)
- `terminalGap_retainedTailFiniteTimingNash_jointReturn_ge`
  (`UniformEquilibrium/Diagnostics/Quitting/RetainedTailFiniteTimingReturnFloor.lean`)
- `exists_finFour_minimumFiberIsolation_and_debtMoat_of_no_uniformPayoff`
  (`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinFourMinimumFiberIsolation.lean`)
- `QuittingMinimumLawCausalSuffixAtom.chronology`
  (`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticLawCarrierCausalization.lean`)
- `FinFourMinimumAtomProducer` and
  `FinFourMinimumAtomProducer.minimumDebt_pos`
  (`Research/Quitting/FinFourProducerAtlas/Source.lean`)
- `FinFourQuantitativeFullSupportHardResidual`
  (`UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/FullSupportProjectiveQBarResidual.lean`)
- `quittingTerminalDebtSumInf_eq_terminalSemanticDebtSum_of_minimum`
  (`UniformEquilibrium/Diagnostics/Quitting/TerminalCapNashEndpointTransport.lean`)
