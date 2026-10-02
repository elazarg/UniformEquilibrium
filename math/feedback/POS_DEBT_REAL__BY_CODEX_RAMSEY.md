# Independent review of `POS_DEBT_REAL.md`

Reviewer: `CODEX_RAMSEY`

Source reviewed: [`../POS_DEBT_REAL.md`](../../POS_DEBT_REAL.md)

Related conference transcription:
[`CHATGPT_EXTERNAL__OPPONENT_TIGHT_POSITIVE_MINIMUM_REALIZATION.md`](../notes/CHATGPT_EXTERNAL__OPPONENT_TIGHT_POSITIVE_MINIMUM_REALIZATION.md)

## Verdict

**REVISE -> PASS as ordinary mathematics after three scope/topology wording
repairs.**  The opponent-tight realization theorem, the two-proper-clock
criterion, and the one-proper-clock negative-singleton bound are correct.  I
found no counterexample to the quantitative argument.

The original source should not be exported verbatim because its phrases
“equivalently, for some fixed player” and “falls into exactly two classes”
can be read with quantifiers stronger than the proof.  The related conference
transcription already states the correct selected-subsequence scope.  It also
correctly calls the approximating event late-or-Never rather than literal
Never.

The result is genuinely new relative to the checked declarations searched
below and is directly relevant to the positive-minimum attainment seam.  I
recommend formalization after the three repairs, and eventual export only
after the required second independent review of its unrestricted behavioral
cap conclusion and a fresh packet gate.

## 1. Probability model and topology

For a quitting behavioral profile, the unique live public history lets each
player's private randomizations be encoded by one complete stopping law on

\[
 \overline{\mathbb N}=\mathbb N\cup\{\infty\}.
\]

The latent stopping times are independent across players.  Conversely, every
law is realized by the checked hazard reconstruction
`quittingStoppingLawBehaviorStrategy`, with exact inverse statement
`quittingBehaviorStoppingLaw_stoppingLawBehaviorStrategy` in
`Quitting/Terminal/StrategicallyPrecompactWatchdogProperBoundary.lean`.

The topology must be stated as the **one-point compactification topology** on
`Option Nat`, and the weak topology on its probability laws.  Under this
topology:

- every singleton finite date is clopen;
- for fixed `H`, the tail `{H+1,H+2,...,infinity}` is clopen, because its
  complement is finite; but
- `{infinity}` itself is closed and generally not open, so its mass is not a
  continuous coordinate.

The proof uses only the first two facts.  It does **not** need, and must not
claim, convergence of the Never atoms `mu_i^n({infinity})` themselves.
Compactness of the finite product of law spaces gives the simultaneous
subsequence, and the checked hazard reconstruction realizes its limiting
marginals by an actual profile.

This is mathematically sound.  It is not currently a named Lean package:
formalization still needs the weak compact probability-law space (or an
equivalent diagonal/tightness construction) and its clopen-cylinder
convergence lemmas.

## 2. Opponent-tight realization

Let

\[
 M_{-i}^n=\min_{j\ne i}T_j^n
\]

and assume

\[
 \lim_{H\to\infty}\limsup_n\Pr(M_{-i}^n>H)=0
 \quad\text{for every }i.                            \tag{OT}
\]

The prescribed-payoff argument is exact.  Absorption by time `H` is a finite
polynomial in finite-date masses and tail coordinates, hence passes to the
weak limit.  The discarded contribution is bounded by

\[
 R\Pr(\min_iT_i^n>H)
 \le R\Pr(M_{-i_0}^n>H).
\]

For the cap coordinate define the pure-time values `v_{i,n}(t)`, including
Never.  If `s,t>H`, then the two deviations give the same terminal coalition
on `{M_{-i}^n<=H}`.  Therefore

\[
 |v_{i,n}(s)-v_{i,n}(t)|
 \le 2R\Pr(M_{-i}^n>H).                              \tag{1}
\]

Comparing both tails with `H+1` gives uniform convergence over all finite
times and Never.  The limiting tail term is legitimate: for each fixed `H`,
the clopen tail event converges under weak convergence, so (OT) also makes
`Pr(M_{-i}^infty>H)` tend to zero as `H` grows.

Finally,
`sSup_range_quittingTerminalPayoff_update_eq_pureTime` in
`Quitting/Cycles/BehaviorPureTimeExtremality.lean` identifies the unrestricted
behavioral cap with the supremum of these pure-time values.  Uniform
convergence thus proves simultaneous convergence of every prescribed payoff
and every unrestricted cap.  There is no stationarity or finite-horizon
restriction hidden here.

## 3. Two proper clocks and the common late event

If a limiting law `mu_j` is proper, then for every fixed `H`

\[
 \Pr(T_j^n>H)\longrightarrow\mu_j(\{H+1,H+2,\ldots,\infty\}),
\]

and the right side tends to zero with `H`.  If two distinct players have
proper limiting laws, every player has one of them among its opponents, so
(OT) holds.  The semantic limit is actual.

Hence a compactified realizing subsequence of a nonattained point has at most
one proper limiting law.  On that **fixed selected subsequence**:

- if exactly player `i` is proper, choose that `i`;
- if no player is proper, choose any fixed `i`.

Then

\[
 q_{-i}=\prod_{j\ne i}\mu_j(\{\infty\})>0.
\]

For each fixed `H`, independence and convergence of the clopen tails give

\[
 \Pr(T_j^n>H\ \forall j\ne i)
 \longrightarrow
 \prod_{j\ne i}\mu_j(\{H+1,H+2,\ldots,\infty\})
 \ge q_{-i}.                                         \tag{2}
\]

Thus the sequential statement may use any `0<kappa<=q_{-i}` (indeed
`kappa=q_{-i}` works).  This verifies the proposed lower bound.

### Mandatory quantifier repair 1

The player `i` and `kappa` depend on the selected compactified subsequence.
Nonattainment does not select one player uniformly over every realizing
sequence or every possible law-limit subsequence.  Replace the original
“Equivalently, for some fixed player” sentence by:

> For every fixed compactified realizing subsequence, after choosing (and, if
> needed, further fixing) its proper-player case, there are `i` and
> `kappa>0` for which (15) holds on that subsequence.

### Mandatory topology repair 2

At the limiting profile, (2) converges downward to the literal common-Never
event.  At finite `n`, however, (15) is a common **late-or-Never** event.  The
approximating laws can have zero Never mass at every `n`.  Any wording saying
that the original profiles themselves share a fixed positive Never event
must be replaced by the late-or-Never formulation.

## 4. Exactly one proper clock at a positive minimum

Assume the selected law limit has exactly one proper coordinate `k` and that
`z=(u,b)` globally minimizes total debt with `D(z)=D_*>0`.

The proper `k` clock makes total absorption uniformly tight, so the limiting
actual profile `hat sigma` has prescribed payoff `u`.  For every `j!=k`, the
proper player `k` is an opponent, so the coordinatewise version of the
opponent-tight cap proof gives

\[
 B_j(\widehat\sigma)=b_j.
\]

Writing `hat b_k=B_k(hat sigma)`, global minimality applies because
`Sem(hat sigma)` is actual and hence in the carrier.  Therefore

\[
 D_*\le D(\operatorname{Sem}(\widehat\sigma))
     =D_*+\widehat b_k-b_k,
\]

so `hat b_k>=b_k`.

Every fixed finite pure-time value passes to the limit and is bounded by the
approximating cap.  Hence

\[
 \beta_k^{\rm fin}=\sup_{t<\infty}v_k(t)\le b_k.
\]

If `hat b_k=b_k`, all semantic coordinates agree with `z`, contradicting
nonattainment.  Thus `hat b_k>b_k>=beta_k^fin`.  Pure-time extremality then
forces the excess cap value to be the Never value.

The proposed endpoint formula is also exact.  Pathwise, if some opponent
stops at a finite date, sufficiently late finite Quit and Never induce the
same terminal coalition.  On the event that all opponents play Never, finite
Quit pays `s_k=r_k({k})` whereas Never pays zero.  Dominated convergence gives

\[
 v_k(t)\longrightarrow v_k(\infty)+q_{-k}s_k.        \tag{3}
\]

Since every finite value is at most `b_k` and
`v_k(infinity)=hat b_k`, (3) yields

\[
 0<\widehat b_k-b_k\le -q_{-k}s_k,
\]

and therefore `s_k<0`.  The signs and constant are sharp.  At `q_{-k}=1`,
(3) reduces to the elementary boundary `finite late value = Never value +
solo reward`; with a second proper clock `q_{-k}=0`, the jump mechanism
vanishes, consistently with the realization theorem.

## 5. Exhaustiveness and its required scope

At most one law is proper, so for a **fixed compactified realizing
subsequence** exactly one of the following holds:

1. no law is proper, equivalently every limiting law has a positive Never
   atom; or
2. exactly one law is proper, and if the positive minimum is nonattained the
   negative-singleton jump above occurs at that player.

This is exhaustive and mutually exclusive for that selected law limit.

### Mandatory quantifier repair 3

Do not present these as two intrinsic, mutually exclusive classes of the
carrier point `z` without mentioning a subsequence.  Different realizing
sequences or different compactified subsequences could in principle have law
limits in different arms.  The correct statement is the one above, which the
conference transcription already uses.

The claim “if all singleton rewards are nonnegative, the one-proper arm is
impossible” is then correct on every selected subsequence.  The remaining
all-nonproper arm should be called an all-player escape in the compactified
law limit.  Descriptions involving continuous-time or transfinite clocks are
motivation, not an additional proved classification.

## 6. Source, overlap, and novelty audit

Checked inputs at repository head `26f226139785a6729572a567f76735a6b1e5fb0b`:

- `not_exists_uniformEquilibriumPayoff_iff_hasPositiveMinimumTerminalSemanticDebt`
  in `Quitting/Terminal/PositiveMinimumSemanticDebt.lean`; this confirms the
  source's opening assertion that an explicit finite table with a strictly
  positive attained carrier minimum would be a counterexample to
  uniform-equilibrium-payoff existence;
- `quittingStoppingLawBehaviorStrategy` and
  `quittingBehaviorStoppingLaw_stoppingLawBehaviorStrategy` in
  `Quitting/Terminal/StrategicallyPrecompactWatchdogProperBoundary.lean`;
- `sSup_range_quittingTerminalPayoff_update_eq_pureTime` and
  `quittingTerminalPayoff_update_le_sSup_pureTimeBehaviorStrategy` in
  `Quitting/Cycles/BehaviorPureTimeExtremality.lean`; and
- the compact terminal-semantic carrier infrastructure, including
  `quittingTerminalSemanticCarrier_isCompact`.

Nearby results do not subsume the theorem:

- the reviewed/exported strategically-precompact watchdog theorem uses one
  proper finite approximation class to build auxiliary Nash profiles.  It
  does not prove realization of an arbitrary semantic limit or classify a
  one-proper cap discontinuity;
- `PositiveDebtTerminalSemanticNonattainment.lean` gives an explicit
  two-player nonattained positive-debt point with global minimum zero.  Its
  diffuse sequence lands in the all-nonproper arm here, but it does not state
  opponent-tight realization or the positive-global-minimum classification;
  and
- existing minimum-fiber isolation results work on the closed semantic
  carrier and explicitly do not assert actual profile attainment.

A narrow search found no checked declaration packaging either the uniform
pure-time cap convergence under (OT) or the bound
`0 < hat_b_k-b_k <= -q_{-k}s_k`.  Those are the genuine new results.

The opening literature statement is accurate: the April 2026 paper
[*The APS approach for undiscounted quitting games*](https://link.springer.com/article/10.1007/s00182-026-00982-6)
states that equilibrium-payoff existence is known for two and three players
and remains unknown for at least four, while its own APS result characterizes
a particular absorption-path subclass.  This literature context is not used
in the proof.

## 7. Formalization and export recommendation

After the wording repairs, the theorem merits formalization.  The smallest
new formal package should contain:

1. compact subsequence extraction for a finite family of stopping laws on the
   one-point compactification of `Option Nat`;
2. convergence of finite cylinders and fixed clopen tails;
3. the oscillation estimate (1) and uniform pure-time-value convergence;
4. opponent-tight semantic realization; and
5. the one-proper minimum-debt/Never-jump corollary.

Do not formalize convergence of the singleton Never masses: it is false in
this topology and unnecessary.  Do not encode a player uniform over all
subsequences.

Because the cap conclusion covers arbitrary behavioral deviations, one
ordinary review is not enough for export under `exports/README.md`.  Subject
to a second independent falsification and a packet-level gate, the corrected
result is export-worthy: it removes every opponent-tight positive-minimum
nonattainment seam and reduces the survivor to a precise all-player escape or
negative-singleton one-proper boundary.
