# Source and gate audit: constructive passive-padding retraction

Reviewer: `GATE_SOURCE_AUDIT`

Target:
[`CODEX_ROOT__PASSIVE_PADDING_CONSTRUCTIVE_RETRACTION.md`](../notes/CODEX_ROOT__PASSIVE_PADDING_CONSTRUCTIVE_RETRACTION.md)

Verdict: **PASS for a narrow export packet.**  I found no mathematical gap in
the quantitative reverse projection, fixed-target compilation, or quiet lift.
The statement covers unrestricted behavioral deviations and keeps the same
padded target.  It is absent from the checked tree and closes the explicit
“no converse” boundary in the checked passive-padding packet.

This is the second independent mathematical review of the unrestricted-
strategy claim.  I did not use the earlier mining report as evidence.  I read
the target note, its prior review, the relevant Lean definitions and theorem
bodies, and the existing formalized/revisit packets directly.

The export should emphasize the genuinely new result: the quantitative
same-target reverse projection.  The generic existence-level forward lift is
already covered by block deletion.  The concrete canonical `(oldTarget, 0)`
lift remains a useful adapter, not a new generic principle.

## Claim audited

Let `I` and `J` be finite nonempty player types.  Let `r` be a quitting reward
on `I`; let `H_i` and `L_i` be the canonical upper and lower endpoints including
zero; put

\[
 \Omega=\max_i(H_i-L_i),\qquad m=|J|,
 \qquad f=\frac{A}{A+m\Omega},
\]

where `A>0`.  Canonically pad `r` to `I \oplus J`: an old-containing terminal
coalition deletes the new labels for old rewards and pays every new coordinate
zero; a new-only terminal coalition pays old coordinate `i` the value `H_i`
and pays each participating new player `-A`.

The note proves:

1. every padded terminal `epsilon`-Nash profile, for `epsilon>=0`, projects to
   an old terminal `(epsilon/f)`-Nash profile;
2. if its old-coordinate terminal payoff is within `epsilon` of a padded
   target, the projected old payoff is within `epsilon/f` of the restriction
   of that same target;
3. therefore the old-coordinate restriction of every padded uniform-
   equilibrium payoff is an old uniform-equilibrium payoff; and
4. conversely, quietly adding the new players maps an old target `v` to the
   padded target `(v,0)`.

All four assertions are correct under the stated hypotheses.

## 1. Canonical map and probability semantics

The reward map in the note exactly matches
`quittingPassivePaddingReward` in
`UniformEquilibrium/Quitting/Terminal/PassivePlayerPadding.lean`.
The profile projection is exactly
`quittingPassivePaddingProjectProfile`: it reads the old coordinates of the
*actual padded live roots* and builds an old behavioral profile from them.
It is not a projection of terminal laws, a stationary approximation, or a
choice of a semantically similar old profile.

The quantity `s` is
`quittingPassivePaddingFreshOnlyMass` at start zero.  It is the infinite-
horizon probability that the first absorbing coalition is nonempty and
contains no old player.  Simultaneous old/new quitting is not included in `s`;
such a terminal is old-containing and is coupled exactly to its old
projection.  The checked definition is a summable series of literal stage
masses, so no finite-horizon limit is silently substituted.

The canonical bounds used in the note are checked in
`PassivePlayerPaddingCanonical.lean`:

- `quittingPassivePaddingLowerEndpoint_nonpos`;
- `quittingPassivePaddingUpperEndpoint_nonneg`;
- `quittingPassivePaddingReward_mem_canonicalInterval`;
- `quittingPassivePaddingCoordinateWidth_le_width`; and
- `quittingPassivePaddingWidth_nonneg`.

Thus `Omega>=0`, `m>0`, and `A>0` imply `f>0`.  The formula remains valid when
`Omega=0`, in which case `f=1`.

## 2. Fresh-only mass estimate

For every new player `j`, the complete behavioral deviation to literal Never
has terminal payoff exactly zero by
`quittingTerminalPayoff_update_passivePadding_fresh_never_eq_zero`.
Terminal `epsilon`-Nash therefore gives

\[
 -U^+_j\leq\epsilon.
\]

The checked aggregate account
`sum_quittingTerminalPayoff_passivePadding_fresh_le` gives

\[
 \sum_{j\in J}U^+_j\leq-A s.
\]

Multiplying by `-1`, summing the individual Nash bounds, and using `A>0`
gives exactly

\[
 A s\leq\sum_j(-U^+_j)\leq m\epsilon,
 \qquad s\leq\frac{m\epsilon}{A}.
\]

The directions are correct even if some individual fresh payoff is zero and
another carries all of the penalty.  No averaging, independence beyond the
original product behavior, or attainment of a best response is used.

## 3. Old payoff and arbitrary-deviation projection

For an old player `i`, the checked coupling
`quittingTerminalPayoff_passivePadding_old` gives

\[
 0\leq U_i^+(\sigma^+)-U_i(\sigma)
 \leq (H_i-L_i)s\leq\Omega s.
\]

Fix an arbitrary old behavioral strategy `tau_i`.  The definition
`quittingPassivePaddingLiftOldDeviation` replays its complete live-history
hazard in the padded game.  The theorem
`quittingTerminalPayoff_update_passivePadding_old_ge` proves

\[
 U_i(\sigma[i\leftarrow\tau_i])
 \leq U_i^+(\sigma^+[\mathrm{inl}(i)\leftarrow\widetilde\tau_i]).
\]

Subtracting the two baselines in the correct direction yields

\[
\begin{aligned}
 U_i(\sigma[i\leftarrow\tau_i])-U_i(\sigma)
 &\leq \epsilon+\Omega s\\
 &\leq\epsilon\left(1+\frac{m\Omega}{A}\right)
 =\frac{\epsilon}{f}.
\end{aligned}
\]

The strategy `tau_i` was arbitrary.  In a quitting game the unresolved public
history is the live all-Continue history, and the lift retains its hazard at
every date.  Consequently this proves the full repository-native
`IsεAsymptoticNash` assertion; it does not cover only pure times, finite
support, Markov strategies, or stationary strategies.

The same baseline estimate and the triangle inequality prove the target error
bound.  Only old-coordinate closeness to the padded target is logically
needed, although the fixed-target acceptance certificate supplies closeness
in every coordinate.

## 4. Fixed-target quantifiers

The theorem
`exists_quittingTerminalTargetAcceptanceCertificate_of_isUniformEquilibriumPayoff`
in
`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalTargetSemantics.lean`
keeps one declared target fixed and, at every positive error, returns one
terminal approximate-Nash profile whose terminal payoff is close to that same
target.

Given requested old error `eta>0`, choose `epsilon=f*eta`.  Since `f>0`, this is
an admissible certificate accuracy.  The quantitative projection has both
Nash and target error at most

\[
 \frac{f\eta}{f}=\eta.
\]

Therefore
`quittingGame_isUniformEquilibriumPayoff_of_terminalNash_all_errors_approxTarget`
applies to the literal coordinate restriction
`fun i => paddedTarget (.inl i)`.  There is no compactness selection, new
target, contradiction principle, or nonexistence assumption in this proof.

## 5. Quiet lift and fresh deviations

The direct quiet lift is also correct.  Copy every old live-root strategy and
make every new player Never quit.  Old prescribed payoffs and old unilateral
behavioral deviations then agree exactly with the old game.

Fix a new player `j` and an arbitrary complete behavioral replacement.
Because all other new players remain Never:

- if `j` strictly precedes every old quitter, the terminal coalition is
  `{j}` and `j` receives `-A`;
- if `j` ties an old absorption, the terminal is old-containing and `j`
  receives zero;
- if an old coalition preempts `j`, or play never absorbs, `j` receives zero.

Hence the deviating payoff is exactly

\[
 -A\Pr(j\text{ strictly preempts old absorption})\leq0,
\]

while the quiet baseline is zero.  This covers private randomization,
calendar dependence, Never, and arbitrarily late quitting.  Thus every old
terminal `epsilon`-Nash profile lifts with the same error and target
`(oldTarget,0)`.

The general all-behavior principle is already present as
`isεAsymptoticNash_liftDeletedProfile_of_blockDispensable` and
`exists_uniformEquilibriumPayoff_eq_on_survivors_of_blockDispensable` in
`UniformEquilibrium/Quitting/Classification/BlockDeletion.lean`.  For the
canonical padding block, join rewards of a new player are identically zero on
old-containing coalitions, its solo reward is `-A`, and its survivor Continue
floor is zero.  The genuinely new forward content is only the concrete
sum-type adapter and the exact fresh target zero, for which the direct proof
above is cleaner than compactly selecting deleted coordinates.

## 6. Strengthening: exact target-set and exploitability relations

Two immediate corollaries strengthen the export without new ideas.

### Fresh target coordinates are forced to zero

Every new coordinate payoff in the padded table is nonpositive.  In a padded
terminal `epsilon`-Nash profile, deviation to Never also gives
`U^+_j>=-epsilon`.  Along the fixed-target acceptance profiles,

\[
 -\epsilon\leq U^+_j\leq0,
 \qquad |U^+_j-v^+_j|<\epsilon.
\]

Letting `epsilon` tend to zero gives `v^+_j=0`.  Therefore the target-level
statement is not merely a pair of existence implications:

\[
 \operatorname{UEPayoffs}(r^+)
 =\{(v,0):v\in\operatorname{UEPayoffs}(r)\}.
\]

### Pointwise and infimum exploitability bounds

Apply the quantitative theorem with `epsilon` equal to the padded profile's
terminal exploitability.  Since the finite player maximum is an admissible
terminal Nash error, it gives the pointwise inequality

\[
 f\,E_r(\operatorname{project}\sigma^+)\leq E_{r^+}(\sigma^+).
\]

The quiet lift has exactly the same old debts and zero new-player debt, hence
its exploitability equals that of the old profile.  Taking infima yields

\[
 f\,\eta(r)\leq\eta(r^+)\leq\eta(r).
\]

These are precisely the unformalized refinements retained in
`revisit/TERMINAL_EXPLOITABILITY_PASSIVE_PLAYER_PADDING_POINTWISE_INFIMUM.md`.
Thus the retraction packet can close that revisit item rather than duplicating
it.  If formalization of the `csInf` corollary is inconvenient, the
profilewise and target-set theorems should land first; the mathematics of the
infimum statement is nevertheless complete.

## 7. Boundary and falsification audit

- **`A=0`: genuine failure.**  A fresh player is then indifferent to exclusive
  absorption, so fresh-only mass need not shrink with the Nash error.  The
  factor has no useful positive reverse estimate.  Strict positivity of `A`
  is essential.
- **Empty `J`: identity boundary.**  The note correctly excludes it from the
  division-based statement.  It can be handled separately by the identity
  map.
- **Empty `I`: excluded correctly.**  The canonical extrema and width require
  a nonempty old type.
- **`Omega=0`: no singularity.**  The factor is one and the old baseline is
  preserved exactly.
- **Fresh collisions:** harmless.  A new-only coalition with several new
  quitters contributes at least one `-A` to the aggregate account; a coalition
  containing an old player pays every new coordinate zero.
- **Old/new ties:** projected old rewards agree exactly after deletion of the
  new labels, so they create no unaccounted coupling error.
- **Nonabsorption:** pays zero in both games and is included in the canonical
  interval.
- **Behavioral deviations:** the old lift and fresh Never deviation are
  complete behavioral strategies.  No best-response attainment is assumed.
- **Arbitrary padded games:** not covered.  The reverse projection relies on
  the exact canonical padding reward and says nothing about a generic
  `(k+1)`-player table.

I also tested the tempting failure mode in which all fresh-only mass is carried
by one new player: the proof remains valid because it sums the individual
Never inequalities before applying the aggregate penalty account.  The factor
`m` is necessary for this worst case.  Conversely, when all fresh players
share the loss evenly, the same factor is attained by the aggregate argument;
there is no illicit assumption that one player alone sees the full mass.

## 8. Freshness and conjecture relevance

The current checked source contains:

- the canonical reward and live-root projection;
- the old baseline comparison and arbitrary-deviation lift;
- the aggregate fresh penalty and exact Never payoff;
- upward terminal-gap transport and upward nonexistence; and
- generic block-dispensable forward lifting.

I found no declaration proving the quantitative padded-to-old profile
projection, restriction of the same padded target, forced-zero fresh target
coordinates, or the resulting target-set equality.  No packet in `exports/`
or `formalized/` states them.  The closest checked packet,
`formalized/TERMINAL_EXPLOITABILITY_PASSIVE_PLAYER_PADDING.md`, explicitly
lists “No converse from a padded game to its old-player subgame” as a
nonclaim.  The pointwise numerical consequences remain in `revisit/`.

This result therefore makes a strict, named boundary change: canonical passive
padding is a quantitative target-preserving retraction, not only upward
counterexample transport.  It completely classifies the uniform-payoff target
set of this padded subclass.  It does not solve a new player cardinality or
advance the hard Fin4 residual, and the export must say so.

## 9. Exact Lean handoff

Suggested new file:

```text
UniformEquilibrium/Quitting/Terminal/PassivePlayerPaddingRetraction.lean
```

Minimal imports:

```text
UniformEquilibrium.Quitting.Terminal.PassivePlayerPaddingCanonical
UniformEquilibrium.Quitting.Terminal.TargetTail.TerminalTargetSemantics
```

Import `Classification/BlockDeletion.lean` only if the forward adapter is
implemented through its generic API; the direct quiet-lift proof does not
need its existential compactness theorem.

Recommended declaration order:

1. `freshOnlyMass_le_of_isεAsymptoticNash_passivePadding`

   From `epsilon>=0`, terminal `epsilon`-Nash, the fresh Never equality, and
   the aggregate payoff bound, prove
   `freshOnlyMass <= card J * epsilon / penalty`.

2. `isεAsymptoticNash_project_passivePadding`

   In the general interval-bounded form, return the projected terminal Nash
   error
   `epsilon * (1 + card J * width / penalty)`.  This algebraic form avoids
   division by the factor during the main proof.

3. `terminalTargetError_project_passivePadding`

   Under old-coordinate padded target error `<=epsilon`, prove the same bound
   for the target restriction.

4. `IsUniformEquilibriumPayoff.of_passivePlayerPadding_canonical`

```lean
theorem IsUniformEquilibriumPayoff.of_passivePlayerPadding_canonical
    [Nonempty I] [Nonempty J]
    (reward : {S : Finset I // S.Nonempty} → Payoff I)
    {penalty : ℝ} (hpenalty : 0 < penalty)
    {paddedTarget : Payoff (I ⊕ J)}
    (hpadded :
      (quittingGame (quittingPassivePaddingReward
        (J := J) reward
          (quittingPassivePaddingUpperEndpoint reward) penalty))
        |>.IsUniformEquilibriumPayoff none paddedTarget) :
    (quittingGame reward).IsUniformEquilibriumPayoff none
      (fun old => paddedTarget (.inl old))
```

5. `isUniformEquilibriumPayoff_passivePadding_canonical_iff`

   Package the direct quiet lift and the fresh-coordinate-zero lemma as

```text
paddedTarget is a uniform-equilibrium payoff
iff
(its old restriction is an old uniform-equilibrium payoff
 and every fresh coordinate is zero).
```

   An alternative simpler surface is the exact image theorem for targets
   `(oldTarget,0)`.

6. `quittingTerminalExploitability_project_passivePadding_le` and the two
   infimum inequalities, discharging the existing `revisit/` packet.

The quantitative proof should reuse, rather than reproving:

- `quittingTerminalPayoff_update_passivePadding_fresh_never_eq_zero`;
- `sum_quittingTerminalPayoff_passivePadding_fresh_le`;
- `quittingTerminalPayoff_passivePadding_old`;
- `quittingTerminalPayoff_update_passivePadding_old_ge`;
- the five canonical bound declarations listed in section 1; and
- the two fixed-target terminal compiler declarations listed in section 4.

No desired conclusion needs to be introduced as a structure field.  The
actual profile, deviation lift, mass, and target restriction are all explicit
terms already present in the source.

## Final export recommendation

Promote one final packet after incorporating this audit's stronger target-set
statement and correcting the novelty wording.  The packet qualifies as a
complete quantitative reduction and a special-class target classification,
not as a Fin4 breakthrough.  It has an actual-data adapter (live-root
projection), an unrestricted semantic consumer (fixed-target terminal-to-
uniform compilation), sharp boundary tests, two independent reviews, and a
narrow Lean implementation path.
