# Round 7 feedback on quit-time compactification

Reviewer: `CODEX_CEDAR`

Reviewed note: `notes/CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION.md`

Scope: Propositions 27--31 only: the canonical punishment-floor phantom,
strict finite attainment, periodic active-seam correction, the normalized
active defect, and the signed late-window extension.

Status: `VALID_ORDINARY_MATHEMATICS; UNIVERSAL_REDUCTION_NOT_YET_A_PRODUCER`

## Claim checked and sources

The claim is that failure of a uniform payoff forces the selected exact
punishment-floor predecessor orbit into a summable-charge all-Continue
phantom `b`; a phantom strictly above every own singleton reward is attained
in finite time; and finite reversed orbit words become divergent periodic
support-witness paths whenever their support-paid normalized seam is zero or
tends to zero.

Before review I refreshed the conference filenames and inspected these exact
declarations and definitions:

- `quittingPunishmentFloorForward_policy`,
  `quittingPunishmentFloorForward_isZeroNash`,
  `quittingPunishmentFloor_le_forwardValue`,
  `isQuittingRootSupportApproxNash_zero_of_isZeroNash`, and
  `quittingGame_uniformPayoff_or_punishmentFloorForwardChargeBound` in
  `UniformEquilibrium/Quitting/Bellman/Finite/PunishmentFloorForward.lean`;
- `abs_quittingRootSuccessorPayoff_sub_tail_le_two_mul_absorptionMass` in
  `UniformEquilibrium/Quitting/Debt/Marked/TimeAdvance.lean` and
  `quittingRoot_quitProbability_le_absorptionMass` in
  `UniformEquilibrium/Quitting/Cycles/ConditionedDiffuseProductRescaling.lean`;
- `exists_uniformEquilibriumPayoff_of_zeroSolo` in
  `UniformEquilibrium/Quitting/Punishment/ZeroSoloDisjunct.lean` and
  `quittingPunishmentValue_le_max_solo` in
  `UniformEquilibrium/Quitting/Stationary/MinMax.lean`;
- `IsQuittingRootSupportApproxNash` in
  `UniformEquilibrium/Quitting/Boundary/Repair/SupportEnlargementAlternative.lean`,
  `IsQuittingRootSequenceSupportApproxNash` in
  `UniformEquilibrium/Quitting/Paths/SupportWitnessClockCollapse.lean`, and
  `exists_isεAsymptoticNash_of_divergentAbsorption_supportRationalPath`
  and
  `quittingGame_exists_uniformEquilibriumPayoff_of_supportRationalDivergentPaths`
  in `UniformEquilibrium/Quitting/Paths/SupportWitnessPathCompiler.lean`;
- `quittingRootSuccessorPayoff_sub_eq_continueMass_mul` in
  `UniformEquilibrium/Quitting/Cycles/PeriodicCompiler.lean` and the exact
  signed-correction comparison
  `isQuittingRotationUniformSignedResidual_iff_value_close` in
  `UniformEquilibrium/Quitting/Projective/SignedProjectiveLasso.lean`; and
- `quittingGame_exists_uniformPayoff_of_positive_admissible_cycle` in
  `UniformEquilibrium/Quitting/Bellman/Finite/PositiveAdmissibleCycle.lean`.

No Lean file was created or edited and no Lean build was run.  The five
propositions reviewed here remain ordinary mathematics; the named consumers
above are checked Lean declarations under their stated imports.

## 1. Proposition 27: summable charge gives the positive phantom

The orientation is correct.  `P_t` is Nash against tail `V_t` and the forward
predecessor value is

`V_(t+1)=Bellman(V_t,P_t)`.

Thus a chronological word must later read the roots in decreasing time.
Nothing in the compactness argument silently reads the forward orbit as play.

In the second branch of
`quittingGame_uniformPayoff_or_punishmentFloorForwardChargeBound`, all partial
sums of the nonnegative `alpha_t` are bounded.  Hence the real series is
summable and `alpha_t -> 0`.  The canonical-box facts supply exactly the two
hypotheses omitted from the displayed shorthand application of the
time-advance estimate:

```text
|reward(S)_i| <= M,  |V_t(i)| <= M.
```

Consequently

`|V_(t+1)(i)-V_t(i)| <= 2 M alpha_t`

has summable right side.  Every coordinate therefore has finite total
variation and a limit `b_i`; finiteness of the player set makes this a single
payoff vector.

The marginal step is also exact, not merely a union-bound analogy:
`quittingRoot_quitProbability_le_absorptionMass` gives
`P_t(i)(Quit) <= alpha_t`.  Hence every marginal converges to pure Continue.
The root payoff and endpoint inequalities are finite polynomial expressions,
so exact Nash passes to `(b,all-Continue)`.  Its pure-Quit comparison is
precisely `r({i})_i <= b_i`.  The floor inequality passes to the same limit.
Finally, if all own singleton rewards were nonpositive, the hypothesis
`IsQuittingZeroSolo` of
`exists_uniformEquilibriumPayoff_of_zeroSolo` would hold.  Therefore failure
of a uniform payoff forces at least one `0 < r({i})_i <= b_i`.

This proves the four stated conclusions.  It does not produce a return from
`b`; the note correctly retains that as the residual universal obligation.

## 2. Proposition 28: strictness forces finite attainment

If every singleton inequality is strict, finiteness gives

`eta=min_i (b_i-r({i})_i)>0`.

At the limit root, player `i`'s endpoint difference is
`r({i})_i-b_i <= -eta`.  Continuity makes every such difference negative for
all sufficiently large `t`, uniformly over the finite player set.  The exact
support theorem says a positively used Quit action must have nonnegative
endpoint difference.  Thus every Quit marginal is exactly zero, not merely
small, from some date onward.  The policy identity then gives
`V_(t+1)=V_t`; since this constant tail converges to `b`, it is literally
equal to `b`.

The split is exhaustive.  In particular, an asymptotic but unattained
phantom must lie on at least one singleton equality face.  I found no missing
compactness, subsequence, or support-selection assumption in this step.

## 3. Proposition 29: exact active/passive seam correction

For the reversed strict word write `c_k` for joint Continue mass and

```text
sigma_k = product_{ell=k}^{T-1} c_ell,
s = sigma_0,
z = (b-chi)/(1-s).
```

The original values satisfy `b=A+s chi`.  Periodic evaluation gives

```text
D_0=(b-s chi)/(1-s),
D_0-b=s z,
D_0-chi=z,
D_k-W_k=sigma_k z.                    (*)
```

This exact calculation also agrees with the signed monodromy identity behind
`isQuittingRotationUniformSignedResidual_iff_value_close`.  At phase `k`, the
tail used by the root changes by `sigma_(k+1) z`; this one-index distinction
is worth making explicit, although it does not change any bound in the note.

Proposition 27 gives `b>=chi`, so `z>=0`.  If player `i` is active and
`b_i=chi_i`, then `z_i=0`: all of that player's endpoint comparisons are
unchanged at every phase.  If `i` is passive, Continue is its only supported
action; its continuation coordinate is raised, while its Quit endpoint is
tail-independent, so Continue remains optimal.  Thus the corrected periodic
word is exact support-wise Nash.  Equation `(*)`, `W_k>=chi`, and `z>=0`
give exact individual rationality.  At least one phase absorbs, so repetition
makes total charge nonsummable.

The proof that an active player exists is also sound: Proposition 27 provides
`r({j})_j>0`, while
`quittingPunishmentValue_le_max_solo` gives
`chi_j<=r({j})_j<b_j` in the strict branch.  Hence `b!=chi`, which an entirely
all-Continue word could not realize.

The support-witness periodic adapter therefore yields a uniform payoff.  The
alternative phrasing through `positive_admissible_cycle` is mathematically
equivalent after packaging the corrected phase values as admissible states,
but that packaging is not itself a new checked declaration in this note; the
support-witness route already supplies the exact checked consumer needed for
the conclusion.

## 4. Proposition 30: only active coordinates pay the normalized seam

For an active player `i`, `0<=z_i<=E`.  Replacing the tail at a phase changes
its Quit-minus-Continue endpoint difference by

`- opponentContinueMass * sigma_(k+1) z_i`.

Thus a supported Quit inequality loses at most `E`, while every supported
Continue inequality improves.  A passive player has no Quit-support
obligation and its Continue inequality also improves.  This is exactly
`IsQuittingRootSupportApproxNash` with error `E`, without multiplying a defect
by the player's own action probability.  The same correction is nonnegative,
so rationality error is zero.  For `E>0`, the displayed compiler error is
therefore exactly

`2E+sqrt(E)(2+7M)`.

If a family has `E_n -> 0`, then for each requested positive tolerance choose
a word with `E_n` below it and use monotonicity of support and rationality
inequalities.  If some `E_n=0`, Proposition 29 already applies (equivalently,
the exact conditions can be weakened to any positive compiler tolerance).
So the all-errors uniform-payoff consequence is valid.

This is a conditional producer objective, not an actual arbitrary-game
producer: no argument here constructs a source-matched family with
`E_n -> 0`.  The note states this distinction honestly.

## 5. Proposition 31: signed late windows

For a positive-charge window `[m,n)`, reversal has original entry `V_n`,
terminal `V_m`, and survival product `s_mn`.  If

`z=(V_n-V_m)/(1-s_mn)`,

the same affine calculation as `(*)` shows that an entering phase value is
corrected by `sigma_phase z`, where `sigma_phase` is survival from that phase
to the seam.  The tail used by a phase has the corresponding next-phase
factor.  All factors lie in `[0,1]`.

The asymmetric definition of `E_mn` has the correct signs:

- if `i` Quits somewhere, both signs can hurt one of its supported actions,
  so `|z_i|` is necessary;
- if `i` is passive, positive `z_i` raises Continue and is free, while
  negative `z_i` costs at most `max(0,-z_i)`.

Since every late Continue marginal is positive, these exhaust all supported
actions.  Original phase values are above the punishment floor, and a
negative correction has magnitude at most `E_mn`, giving rationality error
`E_mn`.  Positive window absorption repeats each period, so charge diverges.
The checked compiler with support and rationality errors both `E_mn` gives
exactly

`3E_mn+sqrt(E_mn)(2+7M)`.

The final lower-bound quantifier is the correct negation: if for every late
date and every positive tolerance there were a positive-charge window with
smaller `E`, a diagonal choice would give windows with `E -> 0`; conversely,
failure of such a sequence supplies some `epsilon_0,m_0` bounding every
positive-charge window starting after `m_0`.  As in Proposition 30, an exact
`E=0` window is handled directly before invoking the compiler's strict
positivity hypothesis.

## Falsification checks and verdict

I checked the seam formulas on the smallest scalar affine blocks.  For two
phases with continuation factors `c_0=1/2`, `c_1=1/3`, terminal `chi=0`, and
original entry `b=2`, one has `s=1/6`, `z=12/5`, entry correction
`s z=2/5`, and phase-one correction `c_1 z=4/5`, exactly as `(*)` predicts.
Changing the endpoint order so `z<0` reverses which supported action is
harmed and confirms Proposition 31's absolute-active/negative-passive split.
The tests expose no missing factor of `s`, `1-s`, or two.

Propositions 27--31 are valid ordinary mathematics.  Propositions 27 and 28
are genuine universal reductions; Propositions 29--31 are exact conditional
consumers of increasingly weak seam control.  Together they sharpen the full
conjecture-facing obstruction to a uniformly positive support-paid normalized
late-window defect.  They do not yet settle the conjecture because the note
does not eliminate that defect or construct windows on which it vanishes.

The only presentational repairs I recommend are:

1. in the periodic proofs, distinguish the entering-value correction
   `sigma_k z` from the root's tail correction `sigma_(k+1) z`; and
2. when `E=0`, state explicitly that the exact periodic result is used before
   calling the compiler, whose declaration assumes a strictly positive
   support parameter.

Neither point changes a proposition or its constants.
