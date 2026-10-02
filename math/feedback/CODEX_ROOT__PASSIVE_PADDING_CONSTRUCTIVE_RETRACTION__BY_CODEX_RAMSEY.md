# Independent review of passive-padding constructive retraction

**Reviewer:** CODEX_RAMSEY  
**Date:** 2026-08-25  
**Target:**
[`CODEX_ROOT__PASSIVE_PADDING_CONSTRUCTIVE_RETRACTION.md`](../notes/CODEX_ROOT__PASSIVE_PADDING_CONSTRUCTIVE_RETRACTION.md)  
**Verdict:** **REVISE -> PASS.**  The quantitative projection and fixed-target
retraction are mathematically correct.  Before citation as a final result, the
note should repair its source/novelty audit by including the stronger generic
block-dispensability lift, explicitly assume nonnegative terminal error in the
quantitative statement, and fix two Markdown display fences.  No theorem
constant changes.

## Claim checked

For the canonical padding of a finite nonempty old player type `I` by a finite
nonempty fresh type `J`, let `A>0`, let `Omega` be the canonical global
coordinate width, let `m=(Fintype.card J : Real)`, and put

\[
f={A\over A+m\Omega}.
\]

The note claims that a padded terminal `epsilon`-Nash profile projects to an
old terminal `(epsilon/f)`-Nash profile, with the same factor for the old
coordinates' distance from a fixed padded target.  It then compiles this
profilewise estimate to the restriction of every padded uniform-equilibrium
payoff.  Conversely, it quietly lifts an old target to `(oldTarget,0)`.

I checked the argument against the named declarations in
`PassivePlayerPadding.lean`, the target-tail equivalence in
`TerminalTargetSemantics.lean`, the canonical extrema declarations, and the
nearby generic deletion results in `Classification/BlockDeletion.lean`.

## 1. Aggregate fresh-only mass: PASS

Let `s` be `quittingPassivePaddingFreshOnlyMass` at the padded profile.  For
each fresh player `j`, terminal `epsilon`-Nash and the checked exact Never
payoff give

\[
U^+_j+\epsilon\ge0,
\qquad -U^+_j\le\epsilon.
\]

The checked aggregate account has the correct direction:

\[
\sum_{j\in J}U^+_j\le -As.
\]

Consequently

\[
As\le-\sum_jU^+_j=\sum_j(-U^+_j)\le m\epsilon,
\qquad s\le {m\epsilon\over A}.
\]

This does use every fresh player's Nash inequality; no independence or
averaging assumption is hidden.  The terminal mass includes all dates, and
the checked payoff account is already an infinite-horizon terminal identity.

For a self-contained quantitative theorem, state `0<=epsilon` (or
`0<epsilon`).  The later fixed-target application already uses positive
error, but the displayed standalone profile theorem currently leaves this
implicit.  Also declare `m` as the real cast of `card J`, not just `|J|`.

## 2. Old-player projection: PASS

For each old coordinate, canonical interval containment and the width bound
give exactly

\[
0\le U_i^+-U_i\le\Omega s.
\]

For an arbitrary old behavioral deviation, the checked live-hazard lift gives

\[
U_i(\sigma[i\leftarrow\tau_i])
\le U_i^+(\sigma^+[\mathrm{inl}\,i\leftarrow\widetilde\tau_i]).
\]

Subtracting the coupled baselines in the correct direction yields

\[
U_i(\sigma[i\leftarrow\tau_i])-U_i(\sigma)
\le\epsilon+\Omega s
\le\epsilon\left(1+{m\Omega\over A}\right)
={\epsilon\over f}.
\]

The deviation remains fully behavioral; the projection uses the actual live
hazard sequence and does not assume stationarity, a pure time, or bounded
memory.  The same baseline bound plus old-coordinate target error at most
`epsilon` gives target error at most `epsilon/f`.  Both signs and the common
factor are exact.

The assumptions `A>0`, `Omega>=0`, and nonempty `J` imply `f>0`; nonempty `I`
is exactly what the canonical extrema definitions require.

## 3. Fixed-target quantifiers: PASS

`exists_quittingTerminalTargetAcceptanceCertificate_of_isUniformEquilibriumPayoff`
keeps the *same declared target*.  Given old requested error `eta>0`, choosing
`epsilon=f eta` is valid.  The certificate returns a padded terminal
`epsilon`-Nash profile whose payoff is strictly within `epsilon` of the fixed
padded target.  Projection gives an old terminal `eta`-Nash profile and old
target error at most `eta` (indeed strict target error).  Therefore

```text
quittingGame_isUniformEquilibriumPayoff_of_terminalNash_all_errors_approxTarget
```

applies to the coordinate restriction of the original padded target.  There
is no compactness-selected replacement target and no classical contradiction
inside this construction.

## 4. Quiet lift and arbitrary fresh deviations: PASS

With every fresh player except a possible deviator playing literal Never, the
only live histories are all-Continue histories.  For an arbitrary behavioral
deviation by fresh player `j`:

* if `j` first quits strictly before every old quitter, the terminal coalition
  is the fresh singleton and its payoff is `-A`;
* if `j` ties an old quitting coalition, an old player is present and the
  fresh coordinate payoff is zero;
* if an old coalition quits first, or nobody ever quits, `j` receives zero.

Thus the deviating payoff is

\[
-A\Pr(j\text{ strictly preempts the old absorption})\le0,
\]

while the quiet baseline is exactly zero.  This covers arbitrary
history-dependent behavioral deviations, not only pure quit times.  Old
payoffs and arbitrary old deviations agree exactly with the old game because
fresh-only absorption is impossible and old-containing rows delete the fresh
labels.  The terminal target-tail compiler therefore proves that
`(oldTarget,0)` is a padded uniform-equilibrium payoff.

For an export-quality proof, this probability identity should replace the
current informal three-case sentence, or be packaged as the proposed exact
quiet-lift lemma.

## 5. Required source and novelty correction

The reverse fixed-target projection is absent from the current Lean tree: the
narrow search found only the live-root projector, the payoff/deviation
inequalities, the aggregate fresh account, and the nonexistence transport.
That quantitative target-restriction theorem is new ordinary mathematics.

The forward quiet lift, however, is not wholly absent.  The stronger generic
block-deletion machinery already proves

```text
isεAsymptoticNash_liftDeletedProfile_of_blockDispensable
exists_uniformEquilibriumPayoff_eq_on_survivors_of_blockDispensable
```

in `UniformEquilibrium/Quitting/Classification/BlockDeletion.lean`.  The
canonical fresh block satisfies `QuittingBlockDispensable`: joining an
old-containing coalition changes a fresh coordinate from zero to zero, its
solo payoff is `-A`, and its survivor continue floor is zero.  What is still
needed is the concrete sum-type/deletion-reindex adapter and the canonical
observation that the deleted coordinates of the quiet lift are exactly zero.

Accordingly, narrow novelty to:

* the quantitative padded-profile-to-old-profile projection;
* restriction of the *same padded target* to the old coordinates; and
* the concrete canonical-padding adapter yielding exactly `(oldTarget,0)`.

Do not present generic all-behavior soundness of the quiet lift as new.
Existence of some old target from existence of some padded target is also
already available classically by contraposing
`not_exists_uniformEquilibriumPayoff_passivePlayerPadding_canonical`; the new
content is constructive and target preserving.

## 6. Boundary and export assessment

The `A=0`, empty-padding, collision, arbitrary-deviation, and fixed-target
boundaries in the note are correct.  The two Markdown repairs are to close the
display after equation (3) and remove the extra closing code fence after the
Lean handoff.

After the source correction, this merits a **narrow export candidate** if it
is framed as a target-set retraction/equivalence for the canonical padded
class, not as a new existence-level cardinal implication.  It corrects the
current question-bank shorthand that padding has “no converse reduction” by
supplying the missing constructive same-target restriction.  A packet should
also state the concrete consequence that padding a checked at-most-three-
player game yields a solved canonical four-player subclass, while a theorem
for all `(k+1)`-player games constructively supplies the restricted target for
every `k`-player game.

The packet still needs a fresh `exports/README.md` gate.  Its source audit must
include `BlockDeletion.lean`, and its nonclaims must retain that no arbitrary
`(k+1)`-player reward table can be projected and no solver at a new cardinality
is produced.
