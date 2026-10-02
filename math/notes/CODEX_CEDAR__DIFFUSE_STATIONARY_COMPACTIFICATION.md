# CODEX_CEDAR — diffuse stationary compactification by a two-scale survival seam

## Current best attempt

**Exact reviewable claim and thesis.**  Let `family` be a
`QuittingDiffuseStationaryPrefixFamily reward`, pass to a fixed punished-player
subsequence with divergent horizons, and suppose the one-row Continue mass
`q_n` tends to one.  In addition to the checked fixed-depth phantom datum, retain
the whole-prefix survival

\[
 z_n=q_n^{H_n+1}.
\]

After a further subsequence, `z_n -> z in [0,1]`.  Proposition 2 proves the
following exact conditional producer: if the repeated block has positive
absorption and every player-deleted survival through the block tends to zero,
then the roots themselves are stationary terminal approximate equilibria
against every behavioral deviation.  Proposition 3 proves that, if joint
survival tends to zero, failure of this deleted-clock condition localizes to
at most one exceptional owner.  I am now testing whether the global Nash
inequality for the *actual* finite prefix controls that final owner seam.  The
intended conclusion is exactly the
`hcompactify` premise of
`fixedThreeQuittingBranches_of_pointwiseAlternative_of_diffuseCompactification`.

**Status.**  Source audit complete; the many-player contraction subcase is
proved in ordinary mathematics.  Proposition 4 extracts the exact normal
no-harm singleton datum in the unique exceptional-owner subcase, but that datum
does not prove the requested `S.1 or S.3` classification.  The positive
whole-block-survival case also remains open.  The checked fixed-depth limit
keeps the forward phantom value and actual punishment semantic endpoint
separate, and I do not identify them.  Proposition 1 below proves that the
one-player phantom residual always falls into the stationary branch, so the
existing one-player endpoint-decoupling regression is not a counterexample to
compactification.

**Strategic qualification.**  This notebook changes a named classification
deficit, not the full uniform-existence deficit.  The diffuse premise already
gives terminal approximate Nash profiles at every error through
`quittingApproximateEquilibriumExistence_of_stationarilyGenerated`, and the
checked fixed-target compactness consumer already converts those profiles to a
uniform payoff.  Accordingly this route is no longer my primary
conjecture-closing thesis after the present checkpoint.

**Main gap.**  When one player supplies essentially all block absorption, that
player can unilaterally Continue through the block with nonvanishing
probability; changing the punishment suffix to a stationary repetition is then
not a small semantic perturbation.  One must pay this exceptional-player seam
from global Nash or produce a solo stationary repair.  A limit of fixed-depth
Bellman equations alone cannot do this.

**Sections to check.**  Sections 2 (exact obligation), 4 (one-player test),
5 (finite seam identity), and 6–7 (deleted-clock producer and unique-owner
reduction).

**Kill criterion.**  Abandon this route if there is an actual diffuse family
whose all-Continue phantom subsequence has neither stationary approximate
equilibria nor a well-supported absorbing sequence, or if the family axioms
permit arbitrary independent choices of the forward ray and punishment seam
even after the scalar `q_n^{H_n+1}` and global Nash inequalities are retained.
The existing abstract phantom structure alone does not meet this criterion.

## 1. Status and scope

This is ordinary mathematics, not checked in Lean.  It is a direct attack on
the positive semantic endpoint
`DIFFUSE_STATIONARY_COMPACTIFICATION`, distinct from Simon necessity/orbit
work and from finite-depth punishment-floor admissible-chain producers.

No claim below identifies a terminal, finite-horizon, or discounted value.
All Nash statements intended for the consumer cover unrestricted behavioral
deviations and use the terminal payoff functional.

## 2. Exact universal obligation

For every finite player type `ι` and every quitting reward table `reward`, prove

\[
 \texttt{QuittingDiffuseStationarilyGeneratedApproximateEquilibria reward}
 \Longrightarrow S.1\ \lor\ S.3,
\]

where `S.1` is `QuittingStationaryεEquilibriumExistence reward` and `S.3` is
`QuittingWellSupportedAbsorbingSequenceExistence reward`.

The current checked reduction supplies a family with, at each index `n`:

- error `e_n>0`, with `e_n -> 0`;
- product root `x_n` with one-row Continue mass `q_n>0`;
- finite horizon `H_n>1`;
- a punished player `i_n`;
- an actual behavioral punishment sequence `P_n` satisfying its cap; and
- global terminal `2e_n`-Nash for `x_n` repeated through the prefix and then
  `P_n`.

In the positive-live divergent-horizon regime, the checked compactification
passes every fixed depth to a limiting root, bounded Bellman ray, exact local
endpoint-Nash inequalities, and an actual punishment semantic pair.  When
`q_n -> 1`, that limiting root is all Continue and the forward Bellman ray is
constant.  The only checked local inequality then is

\[
 r(\{i\})_i\le v_i.
\]

The punishment endpoint `p` is separately realizable and capped, but `v=p`
is false in general.

## 3. Sources and declarations inspected

The bounded source lookup was limited to the named endpoint files and their
nearby definitions.

- `QuittingDiffuseStationaryPrefixFamily`,
  `exists_quittingDiffuseStationaryPrefixFamily`, and
  `exists_uniformEquilibriumPayoff_or_stationaryPrefix_residual` in
  `UniformEquilibrium/Quitting/Classification/Existence/StationarilyGeneratedWitnessRegimes.lean`.
- `quittingJointSurvivalWeight_stationaryPrefixFamilyPlan`,
  `exists_quittingPositiveLiveStationaryPrefixLimit`,
  `QuittingPositiveLiveStationaryPrefixLimit.wellSupported_or_phantom`,
  `QuittingPositiveLiveStationaryPrefixLimit.singleton_le_value_zero_of_phantom`,
  `wellSupported_or_exists_allContinuePhantom_of_stationaryPrefix_family`, and
  `QuittingPositiveLiveStationaryPrefixLimit.exists_punishmentTail_realizers`
  in
  `UniformEquilibrium/Quitting/Classification/Existence/StationarilyGeneratedPositiveLiveLimit.lean`.
- `QuittingStationaryεEquilibriumExistence` in
  `UniformEquilibrium/Quitting/Classification/ExistenceBranches.lean`.
- `fixedThreeQuittingBranches_of_pointwiseAlternative_of_diffuseCompactification`
  in
  `UniformEquilibrium/Quitting/Classification/Existence/CorrectedFixedBranch.lean`.
- `limitProfile_not_isExactNash` and
  `not_tendsto_terminalPayoff_to_limit` in
  `UniformEquilibrium/Quitting/Classification/Existence/StationarilyGeneratedCompactnessObstruction.lean`.
- `quittingStationaryPrefixThenRoots_eq_phaseSwitch` and the opponent-survival
  bounds in
  `UniformEquilibrium/Quitting/Classification/Existence/PositiveAbsorptionStationarySplice.lean`.
- `quittingRootSequenceTerminalValue_quittingPhaseSwitchRoots` and
  `quittingRootSequenceHazardTerminalValue_quittingPhaseSwitchRoots` in
  `UniformEquilibrium/Quitting/Cycles/PhaseSwitchProfile.lean`.
- `divergent_opponentClocks_or_positive_exceptionalSuffix` and its explicit
  warning about the missing absorption/tail-Nash adapter in
  `UniformEquilibrium/Quitting/Paths/OpponentClockDichotomy.lean`.
- Conference questions `DIFFUSE_STATIONARY_COMPACTIFICATION.md` and
  `CORRECTED_POINTWISE_EXTRACTION.md` (read-only).

The exact checked survival identity is, for every `t <= H_n+1`,

\[
 \Pr(\text{all Continue through }t)=q_n^t.
\]

## 4. First exact test: one player is always stationary

### Proposition 1 (proved, ordinary mathematics)

For a one-player quitting game with singleton reward `s`, branch `S.1` holds
exactly, independently of any diffuse family or phantom endpoint.

### Proof

If `s<=0`, the stationary all-Continue profile has prescribed terminal payoff
zero.  Every pure finite quit time gives `s<=0`, and Never gives zero.  Hence
all Continue is an exact unrestricted behavioral terminal Nash profile.

If `s>0`, fix any stationary Quit probability `a in (0,1]`.  Absorption occurs
almost surely, so the prescribed terminal payoff is `s`.  Every pure finite
quit time also gives `s`, and Never gives zero.  A behavioral deviation is a
mixture of these pure stopping laws and has payoff at most `s`.  Thus this
stationary profile is again exact unrestricted terminal Nash.

Consequently `QuittingStationaryεEquilibriumExistence` holds for every one-
player table.  In particular, the checked one-player unit-reward phantom with
forward value one and punishment prescribed payoff zero witnesses endpoint
decoupling, but it cannot falsify the desired compactification.

## 5. Two-scale survival seam

Write

\[
 q_n=\prod_i(1-x_{n,i}),\qquad N_n=H_n+1,\qquad
 z_n=q_n^{N_n}.
\]

Compactness of `[0,1]` gives a subsequence `z_n -> z`.  This scalar is erased
by the existing fixed-depth compactification: for every fixed `t`, `q_n^t->1`
even though `z` can be any point of `[0,1]`.

The inclusive-horizon convention is now pinned down: the root is played at
dates `0,...,H_n`, so the switch is at `N_n=H_n+1`.  This is exactly
`quittingStationaryPrefixThenRoots_eq_phaseSwitch`.

Let `A_n` be the one-row absorbing contribution of `x_n`, let

\[
 W_n=A_n/(1-q_n)
\]

be the terminal payoff of repeating `x_n` forever (defined when `q_n<1`), and
let `P_n` be the actual terminal payoff vector of the punishment tail.  The
checked phase-switch decomposition and the finite geometric sum give the exact
coordinatewise identity

\[
 U_n=(1-z_n)W_n+z_nP_n.
\]

This identity alone does not compare the forward phantom vector `v` with
`P_n`: the fixed-depth continuation from time `t` is

\[
 V_{n,t}=(1-q_n^{N_n-t})W_n+q_n^{N_n-t}P_n
\]

For fixed `t`, the residual exponent still lives at the horizon scale, so its
limit can retain a nontrivial seam.  The next task is to derive, directly from
global Nash, the analogous decomposition for every unilateral pure quit time
and Never, then pass those inequalities jointly with `z_n`.

## 6. Deleted-clock contraction gives the stationary branch

For player `i`, write

\[
 d_{i,n}=\prod_{j\ne i}(1-x_{n,j})
\]

for one-row opponent Continue mass.  A unilateral deviation can increase the
probability of reaching the suffix from `q_n^{N_n}` to at most
`d_{i,n}^{N_n}`.  This is why joint survival alone is insufficient.

### Proposition 2 (proved, ordinary mathematics)

Assume along a subsequence that:

1. `q_n<1` (the root has positive absorption);
2. the phase-switch profile is terminal `epsilon_n`-Nash against every
   behavioral deviation, with `epsilon_n->0`; and
3. `max_i d_{i,n}^{N_n}->0`.

Then the stationary profiles that repeat `x_n` forever are terminal
`eta_n`-Nash against every behavioral deviation, where, for a reward bound
`M`, one may take

\[
 \eta_n=\epsilon_n+2M q_n^{N_n}
              +2M\max_i d_{i,n}^{N_n}.
\]

In particular branch `S.1` holds.

### Proof

The stationary profile and the phase-switch profile agree through the first
`N_n` rows.  Under prescribed play their terminal payoffs differ only on the
event that all players Continue through those rows, which has probability
`q_n^{N_n}`.  Since every terminal coordinate lies in `[-M,M]`, the prescribed
payoff difference is at most `2M q_n^{N_n}`.

Fix player `i` and an arbitrary behavioral deviation.  Before absorption the
public history is unique, so this deviation is an arbitrary time-dependent
hazard.  The deviated stationary and phase-switch profiles again agree through
the first `N_n` rows.  Reaching the suffix requires every opponent of `i` to
Continue at every row, irrespective of `i`'s hazard, and therefore has
probability at most `d_{i,n}^{N_n}`.  Their deviating payoffs differ by at most
`2M d_{i,n}^{N_n}`.  Transport the phase-switch Nash inequality across these
two payoff comparisons.  The displayed bound follows uniformly over all
players and all behavioral deviations.  Because it tends to zero, the roots
supply the every-error stationary branch.

This is the reverse-direction analogue of the survival estimates used in
`exists_stationaryPrefix_punishment_nash`, but it is not asserted here as a
Lean declaration.

## 7. Failure localizes to one exceptional owner

Suppose additionally that `q_n^{N_n}->0`.  Define logarithmic block charges

\[
 a_{i,n}=-N_n\log(1-x_{n,i}),\quad
 A_n=\sum_i a_{i,n}=-N_n\log q_n,
\]

with the usual extended interpretation at a zero Continue probability.  In
the phantom regime all marginal Continue probabilities tend to one, so the
quantities are finite eventually.  Then

\[
 d_{i,n}^{N_n}=\exp(-(A_n-a_{i,n})).
\]

### Proposition 3 (proved, ordinary mathematics)

If `A_n->infinity`, then either every player-deleted charge
`A_n-a_{i,n}->infinity` (and Proposition 2 applies), or after a subsequence
there is a unique exceptional owner `o` for which `A_n-a_{o,n}` stays bounded;
for every `j!=o`, `A_n-a_{j,n}->infinity`.

### Proof

Finiteness lets us pass to fixed offending labels.  Two distinct exceptional
players `i,j` are impossible, because

\[
 A_n\le (A_n-a_{i,n})+(A_n-a_{j,n});
\]

the right side contains every nonnegative coordinate charge at least once.
If `o` is exceptional and `j!=o`, then
`A_n-a_{j,n}>=a_{o,n}=A_n-(A_n-a_{o,n})->infinity`.

Thus vanishing joint survival leaves precisely one uncontrolled behavioral
coordinate, not an arbitrary many-player seam.  This matches the checked
`OpponentClockDichotomy` warning: positive opponent survival alone does not
supply absorption or tail Nash for the exceptional stationary fallback.

## 8. The exceptional owner is normal and no-harm

The failure of semantic transport still leaves a strong exact table datum.
Suppose, after subselection, that for an owner `o`

\[
 q_n^{N_n}\to0,\qquad d_{o,n}^{N_n}\ge c>0,
\]

while `q_n->1`.  Write `p_n=x_{n,o}` and `b_n=1-d_{o,n}`.  The prefix
probability that the first absorbing coalition is exactly `{o}` is

\[
 (1-q_n^{N_n})\frac{p_nd_{o,n}}{1-q_n}.
\]

### Proposition 4 (proved, ordinary mathematics)

In this regime, the prescribed payoff vector of the phase-switch profile
converges to the singleton row `r({o})`, and `o` is a
`QuittingNormalNoHarmSingletonOwner`:

\[
 r(\{i\})_i\le r(\{o\})_i\quad\hbox{for every }i,
 \qquad
 \chi_o\le r(\{o\})_o.
\]

### Proof

The lower bound `d_{o,n}^{N_n}>=c` implies `N_n b_n` is bounded.  Since

\[
 q_n^{N_n}=(1-p_n)^{N_n}d_{o,n}^{N_n}\to0
\]

and `p_n->0`, one has `N_np_n->infinity`.  Hence `b_n/p_n->0`, and therefore

\[
 \frac{p_nd_{o,n}}{1-q_n}
 =\frac{p_nd_{o,n}}{p_nd_{o,n}+b_n}\to1.
\]

The probability of the punishment suffix is `q_n^{N_n}->0`; bounded rewards
then give convergence of the prescribed payoff to `r({o})`.

For player `i`, the pure Quit-at-zero deviation payoff converges to
`r({i})_i`, since the root converges to all Continue.  The global behavioral
Nash inequality and the preceding prescribed-payoff limit give
`r({i})_i<=r({o})_i`.

For normality, apply the elementary min-max inequality
`quittingPunishmentValue_le` to the *whole actual phase-switch opponents*.
Their best-reply value is bounded by the prescribed payoff plus the global
Nash error.  Passing to the limit gives `chi_o<=r({o})_o`.  This argument does
not require `o` to equal the family's named punished player.

The checked declaration
`exists_uniformEquilibriumPayoff_of_normalNoHarmSingletonOwner` in
`UniformEquilibrium/Quitting/Classification/LCP/ProjectiveQBarBehavioralDecoder.lean`
consumes this table datum directly.  That direct existence conclusion is
mathematically valid but redundant here, because the diffuse-family premise
itself already has a checked direct fixed-target consumer.  What remains open
for this notebook is specifically whether normal no-harm also implies `S.1`
or `S.3`.

## 9. Proved versus unproved

### Proved here

- Proposition 1: every one-player quitting game is in the exact stationary
  branch.
- The exact whole-prefix survival scalar is `q_n^(H_n+1)`.
- Proposition 2: persistent player-deleted contraction transports the actual
  phase-switch Nash certificate to stationary roots with an explicit
  unrestricted-deviation error.
- Proposition 3: when whole-prefix joint survival vanishes, failure of that
  contraction has one unique exceptional owner after subselection.
- Proposition 4: the exceptional owner supplies the exact normal no-harm
  singleton datum from the actual family, without using the named punishment
  label.
- The whole-prefix survival scalar is a necessary missing compact
  coordinate, using the checked finite-prefix survival identity.
- A fixed-depth limit cannot determine that scalar when `q_n->1` and
  `H_n->infinity`.

### Not proved

- A stationary repair or seam bound for the unique exceptional owner.
- The regime in which `q_n^(H_n+1)` has a positive subsequential limit.
- The full diffuse compactification consumer.

## 10. Concrete next check

In the exceptional-owner regime, derive the exact global-Nash inequalities for
owner Quit at dates `0` and `N_n` and owner Never.  Test whether their
difference controls the suffix premium by the small opponent absorption
`1-d_{o,n}^{N_n}`.  The smallest exact test is a two-player root with hazards
`(a_n,b_n)`, `N_na_n->infinity`, and bounded `N_nb_n`, followed by an arbitrary
deterministic punishment endpoint.  If the endpoint premium remains free even
under all three inequalities, retain the exact counterexample ledger and test
the checked solo stationary fallback hypotheses one by one.

For a future classification-only continuation, the sharper question is:
does `QuittingNormalNoHarmSingletonOwner` imply `S.1 or S.3`?  The currently
checked consumer produces a stationarily generated family and then a fixed
uniform target, not either classification branch.
