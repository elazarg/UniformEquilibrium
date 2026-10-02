# Audit of `AKRS_REVERSE`

## Verdict: REVISE

The central mathematical result survives: Lemma 1 is correct, its useful
null-tail consequence is correct after making the alternative nonexclusive,
the one-dummy construction is an exact stationary every-tail S.3 witness, and
the retraction inequalities (18)--(21) cover unrestricted behavioral
deviations.  The universal one-player cardinal shift and the resulting
all-finite-cardinal equivalence are also correct.

Three corrections are required before the answer should be treated as final:

1. Corollary 2 says "exactly one", but the two displayed conclusions need not
   be disjoint.  Replace this by "at least one" or "one (possibly both)".
2. The Lean correspondence for padding is a zero-Never theorem with a finite
   fresh block `J`; the displayed factor is obtained only after subtracting
   `z` coordinatewise and specializing to one fresh player.  This adapter
   should be stated at the first source-correspondence claim, not left
   implicit until Section 5.
3. The final attribution to an "AKRS errata" is unsupported by the tracked
   source.  The tracked Literature file says that the publisher's 2025 update
   changed only an affiliation and itself records the reverse implication as
   open.  Cite that file/status instead, unless a separate erratum is supplied.

These are exact-statement/source corrections, not failures of the padding
reduction.

## Claim audited

I checked the answer in `gpt/AKRS_REVERSE.md` against the definitions in
`questions/AKRS_THEOREM_3_4_REVERSE_S3_NULL_TAIL_GAP.md`.  The audited claim is
that the restarted-null-tail defect can be dispatched, while the universal
reverse-S.3 schema is equivalent, after adding one passive player, to terminal
approximate-equilibrium existence for arbitrary finite quitting games.

The argument is ordinary mathematics, not a newly checked Lean theorem.  The
Lean corpus already checks the passive-padding reward, its unrestricted
behavioral retraction, the all-normal S.3 consumer, and the journal theorem's
current open reverse status.

## 1. Lemma 1 and the null-tail corollary

Lemma 1 passes.  If an initially absorbing root sequence has a restarted tail
with positive limiting survival, there is a last row `L` whose Continue
product is zero.  The suffix product after `L` is positive.  Consequently

\[
 a_{n,\infty}\longrightarrow 1,
 \qquad c(q_n)\longrightarrow 1,
 \qquad q_n^j\longrightarrow 0
\]

for every player `j`.  The restarted-tail terminal mass is
`1-a_{n,\infty}`, so boundedness of the finite table gives
`gamma_n^i -> z^i`.  The Quit endpoint is a finite polynomial in the
opponents' row probabilities and hence tends to `r^i({i})`.  Passing to the
limit in `Q_n^i <= gamma_n^i + epsilon` proves

\[
 r^i(\{i\})\le z^i+\varepsilon.
\]

The subsequent vanishing-error argument also passes: if such non-every-tail
witnesses occur along errors tending to zero, then every own singleton payoff
is at most the Never payoff.  Against all-Continue opponents, an arbitrary
behavioral deviation produces a convex combination of the own-singleton and
Never payoffs, so all Continue is exact terminal Nash.

The word "exactly" in Corollary 2 is false.  In the one-player game with
`z=0` and `r({i})=0`, all Continue is exact, while the stationary sequence
`q_n^i=1` is also exact row-perfect and terminates from every restarted tail.
Thus both listed conclusions hold.  The proof establishes the sufficient
nonexclusive alternative:

> either all Continue is exact, or below some positive error every S.3
> witness terminates from every restarted tail (and in particular an
> every-tail witness exists at each such error).

This correction does not weaken any later conclusion.

## 2. Exact one-dummy S.3 construction

Proposition 3 passes as written in ordinary mathematics.  At the stationary
row where the dummy quits surely and every old player continues surely:

- every restarted tail absorbs in its first row;
- each old player has `C=V=H_i` and
  `Q=r^i({i}) <= H_i` (the Quit deviation collides with the dummy, and deleting
  the dummy leaves `{i}`);
- the dummy has `Q=C=V=-P`.

These identities verify both global upper and used-action lower clauses of
row perfection at error zero.  They also cover arbitrary old Never payoff
`z`, because `H_i` was defined using both the terminal values and `z^i`.

The precise Lean relationship needs an adapter sentence.  The declaration
`quittingPassivePaddingReward` in
`UniformEquilibrium/Quitting/Terminal/PassivePlayerPadding.lean` is a
zero-Never quitting-game construction on `I ⊕ J`: old-containing terminal
sets retain the old reward after deletion, fresh-only terminal sets give old
players the supplied upper endpoint, and participating fresh players receive
the negative penalty.  For the answer's arbitrary-`z` game, first replace
every old terminal coordinate by `r^i(S)-z^i`.  Then the canonical upper and
lower endpoints are `H_i-z^i` and `L_i-z^i`, their width is `W_i`, and taking
`J=PUnit` is exactly the one-dummy case.  Adding `z^i` back to all old outcomes
recovers the displayed game and leaves every unilateral gain unchanged.

I found no checked declaration that separately packages the dummy-sure-Quit
row as an S.3 producer.  The exact S.3 verification in Proposition 3 should
therefore remain labelled as the elementary ordinary-math proof above; the
formal source checks the reward and retraction it uses.

## 3. Retraction inequalities (18)--(21)

All four inequalities pass for unrestricted behavioral strategies.

Let `alpha` be the probability of dummy-only first absorption.  The dummy's
baseline payoff is `-P alpha`, and deviating to Never yields zero on every
terminal or nonterminal outcome.  Hence

\[
 P\alpha\le \widehat e.
\]

Couple all old live-history randomizations and continue them
counterfactually after dummy-only absorption.  Off the dummy-only event the
projected and padded old payoff agree.  On that event the padded payoff is
`H_i`, while the eventual projected payoff, including Never, lies in
`[L_i,H_i]`.  Therefore (18) holds.  Applying the same coupling after any
arbitrary behavioral replacement of old player `i` gives the one-sided
inequality (19).  Combining those facts with padded exploitability gives

\[
 E_G(\sigma)\le (1+W/P)E_{\widehat G}(\widehat\sigma),
\]

and positivity of `P` and nonnegativity of `W` make (21) equivalent.
No stationarity, finite-clock, bounded-controller, or attainment assumption
enters this argument.

The checked source matches this scope.  In
`UniformEquilibrium/Quitting/Terminal/PassivePlayerPaddingRetraction.lean`,

- `isεAsymptoticNash_project_passivePadding_mul` projects an arbitrary
  padded behavior profile against every old behavioral deviation, with
  multiplier `1 + card J * width / penalty`;
- `isεAsymptoticNash_project_passivePadding` gives the ratio form; and
- `quittingPassivePaddingRetractionFactor` is
  `penalty / (penalty + card J * width)`.

In
`UniformEquilibrium/Quitting/Terminal/PassivePlayerPaddingExploitabilityRetraction.lean`,
`retractionFactor_mul_quittingTerminalExploitability_project_le` is the
pointwise literal-exploitability form.  The global gap theorem
`HasTerminalExploitabilityGap.passivePlayerPadding_canonical` in
`UniformEquilibrium/Quitting/Terminal/PassivePlayerPaddingCanonical.lean`
has factor

\[
 \frac{P}{P+|J|W}.
\]

Thus the answer's `P/(P+W)` is exactly the `J=PUnit` specialization after the
zero-Never normalization described above.  The upward nonexistence corollary
is
`not_exists_uniformEquilibriumPayoff_passivePlayerPadding_canonical` in
`UniformEquilibrium/Quitting/Terminal/PassivePlayerPaddingCorollaries.lean`.

## 4. Cardinal shift and universal equivalence

For every nonempty `n`-player game, the construction produces an
`(n+1)`-player game satisfying the stronger exact stationary every-tail S.3
premise.  Applying reverse S.3 at cardinality `n+1` and projecting a profile
whose padded exploitability is at most
`eta * P/(P+W)` yields old exploitability at most `eta`.  The zero-player case
is vacuous.  Conversely, approximate-equilibrium existence for all finite
games trivially includes every S.3 game.  Equations (22)--(24) therefore pass,
including the exact transport of a positive all-profile exploitability gap.

There is one additional Lean quantifier adapter worth stating.  The question's
S.3 supplies witnesses only for all sufficiently small positive errors, while
`QuittingSequentiallyεPerfectAbsorbingExistence` in
`UniformEquilibrium/Quitting/Classification/ExistenceBranches.lean` quantifies
over every positive error.  The two forms agree: for a requested `epsilon`,
choose a source error below both `epsilon` and half the fixed threshold, then
use `QuittingRowεPerfect.mono`.  This exact small-error adapter is already
checked as
`hasSmallAbsorbingSequentiallyPerfectProfiles_iff_table` in
`Literature/AshkenaziGolanKrasikovRainerAndSolan2024.lean`.

The all-normal source claim is also accurate after that adapter:
`exists_terminalNash_of_all_normal_of_sequentiallyPerfectAbsorbing` and
`exists_uniformEquilibriumPayoff_of_all_normal_of_sequentiallyPerfectAbsorbing`
in
`UniformEquilibrium/Quitting/Classification/Existence/NormalSequentiallyPerfectAbsorbingUniformPayoff.lean`
use `IsCompletelyAbsorbing`, which is the initial survival-product limit zero,
not every-tail termination.  Their deviations are unrestricted behavioral
replacements.

The abnormal-player consequences quoted in Section 5 are checked by
`quittingSoloSelfPayoff_neg_of_abnormal`,
`quittingPunishmentValue_nonpos_of_abnormal`, and
`abnormal_singletonFloor_chain` in
`UniformEquilibrium/Quitting/Classification/AbnormalSingletonConsequences.lean`
(the other-owner floor originates in
`quittingPunishmentValue_le_soloReward_of_abnormal` in
`AbnormalSingletonFloor.lean`).

## 5. Status attribution correction

The current repository status claim itself is supported: the maintained
frontier records the all-normal consumer but no universal reverse-S.3 consumer
and no counterexample.  The paper-facing tracked source is
`Literature/AshkenaziGolanKrasikovRainerAndSolan2024.lean`; its
`publishedApproximateEquilibriumExistence_iff_threeBranchAlternative` retains
the reverse direction with `sorry`, and its header explicitly says the
publisher's 24 May 2025 update corrected only an affiliation.

Accordingly, the final sentence should not say "the AKRS errata classifies"
the reverse implication as a gap unless a separate erratum is cited.  A source-
faithful replacement is:

> The tracked current-journal statement and the maintained repository
> frontier record the unrestricted reverse implication as open: there is an
> all-normal consumer, but no universal consumer and no counterexample.

## Sources inspected

- `questions/AKRS_THEOREM_3_4_REVERSE_S3_NULL_TAIL_GAP.md`
- `gpt/AKRS_REVERSE.md`
- `UniformEquilibrium/Quitting/Boundary/Analytic/UnboundedInverseIterate.lean`
  (`IsCompletelyAbsorbing`)
- `UniformEquilibrium/Quitting/Classification/ExistenceBranches.lean`
  (`QuittingRowεPerfect`,
  `QuittingSequentiallyεPerfectAbsorbingExistence`)
- `UniformEquilibrium/Quitting/Terminal/PassivePlayerPadding.lean`
- `UniformEquilibrium/Quitting/Terminal/PassivePlayerPaddingCanonical.lean`
- `UniformEquilibrium/Quitting/Terminal/PassivePlayerPaddingRetraction.lean`
- `UniformEquilibrium/Quitting/Terminal/PassivePlayerPaddingExploitabilityRetraction.lean`
- `UniformEquilibrium/Quitting/Terminal/PassivePlayerPaddingCorollaries.lean`
- `UniformEquilibrium/Quitting/Classification/AbnormalPlayers.lean`
- `UniformEquilibrium/Quitting/Classification/AbnormalSingletonFloor.lean`
- `UniformEquilibrium/Quitting/Classification/AbnormalSingletonConsequences.lean`
- `UniformEquilibrium/Quitting/Classification/Existence/NormalSequentiallyPerfectAbsorbingUniformPayoff.lean`
- `Literature/AshkenaziGolanKrasikovRainerAndSolan2024.lean`
- `docs/FRONTIER.md` and `docs/TOOLKIT.md` for maintained status only.

## Requested exact edits

1. In Corollary 2, replace "exactly one of the following holds" by "at least
   one of the following holds (and both may hold)".
2. After the first passive-padding source sentence, add that the Lean theorem
   is applied to `r-z`, with `J=PUnit`; its general factor is
   `P/(P+card J * W)`.
3. When mentioning the all-normal theorem, add the small-error-to-all-error
   monotonicity adapter or cite
   `hasSmallAbsorbingSequentiallyPerfectProfiles_iff_table`.
4. Replace the final "AKRS errata" wording by the tracked Literature/frontier
   wording above, unless a distinct erratum source is supplied.

