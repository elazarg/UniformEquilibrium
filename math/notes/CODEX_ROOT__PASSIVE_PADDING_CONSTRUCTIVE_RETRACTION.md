# Constructive retraction for canonical passive-player padding

Author: `CODEX_ROOT`

Status: `MATH_REVIEWED` (`REVISE -> PASS`); repairs from
[`CODEX_RAMSEY`](../feedback/CODEX_ROOT__PASSIVE_PADDING_CONSTRUCTIVE_RETRACTION__BY_CODEX_RAMSEY.md)
are incorporated.  No Lean declaration or export claim yet.

## Exact question

The checked passive-padding theorem sends a terminal exploitability gap from a
finite player type `I` to `I ⊕ J`, and therefore sends nonexistence of a
uniform-equilibrium payoff upward in player cardinality.  Is its contrapositive
constructive and target preserving?

Fix a nonempty finite old player type `I`, a nonempty finite padding type `J`,
an old quitting reward `r`, its canonical coordinate width `Omega`, and a
penalty `A>0`.  Let `r+` be the canonical passive-padding reward: old-containing
coalitions delete the new labels, new coordinates receive zero there, while a
new-only coalition pays every old coordinate its canonical upper endpoint and
each participating new player `-A`.

Put

\[
m=(|J|:\mathbb R),
\qquad
f=\frac{A}{A+m\Omega}>0.
\]

The desired theorem is:

> If `v+` is a uniform-equilibrium payoff of the padded game, then its old
> coordinate restriction `v(i)=v+(inl i)` is a uniform-equilibrium payoff of
> the original game.  Quantitatively, a padded terminal
> `epsilon`-Nash profile whose payoff is coordinatewise within `epsilon` of
> `v+` projects to an old terminal `(epsilon/f)`-Nash profile whose payoff is
> coordinatewise within `epsilon/f` of `v`.

Together with the checked generic block-dispensability lift in the other
direction, canonical passive padding is therefore a target-preserving
equivalence for uniform-equilibrium payoff existence, not merely a
counterexample transport.  The genuinely new direction below is the
quantitative reverse projection retaining the old coordinates of the same
padded target.

## Sources checked

- `quittingPassivePaddingProjectProfile`,
  `quittingTerminalPayoff_passivePadding_old`,
  `quittingTerminalPayoff_update_passivePadding_old_ge`,
  `sum_quittingTerminalPayoff_passivePadding_fresh_le`, and
  `quittingTerminalPayoff_update_passivePadding_fresh_never_eq_zero` in
  `UniformEquilibrium/Quitting/Terminal/PassivePlayerPadding.lean`;
- canonical bounds in
  `UniformEquilibrium/Quitting/Terminal/PassivePlayerPaddingCanonical.lean`;
- `exists_quittingTerminalTargetAcceptanceCertificate_of_isUniformEquilibriumPayoff`
  and
  `quittingGame_isUniformEquilibriumPayoff_of_terminalNash_all_errors_approxTarget`
  in the terminal target-tail files;
- the currently checked classical nonexistence transport in
  `PassivePlayerPaddingCorollaries.lean`;
- `isεAsymptoticNash_liftDeletedProfile_of_blockDispensable` and
  `exists_uniformEquilibriumPayoff_eq_on_survivors_of_blockDispensable` in
  `UniformEquilibrium/Quitting/Classification/BlockDeletion.lean`, which
  already give the generic forward quiet-lift theorem once the canonical
  fresh block is shown dispensable;
- `revisit/TERMINAL_EXPLOITABILITY_PASSIVE_PLAYER_PADDING_POINTWISE_INFIMUM.md`,
  which records numerical exploitability refinements but does not state the
  fixed-target retraction proved here.

## Quantitative projection theorem

Let `sigma+` be a terminal `epsilon`-Nash profile of the padded game, where
`0 <= epsilon`.  Let
`sigma` be its checked live-root projection to the old game.  Write `s` for
the probability that the padded terminal coalition is nonempty and contains
only new players.

### Lemma 1: new-only mass is small

For a new player `j`, deviation to literal `Never` gives payoff zero.  Hence
terminal `epsilon`-Nash implies

\[
-U^+_j(\sigma^+)\le \epsilon.
\]

The checked aggregate penalty account gives

\[
A s\le \sum_{j\in J}-U^+_j(\sigma^+).
\]

Therefore

\[
\boxed{s\le \frac{m\epsilon}{A}.}                    \tag{1}
\]

This uses every new player's Nash inequality.  The averaging argument used in
the gap-transport direction is unnecessary here.

### Lemma 2: projected Nash error

Fix an old player `i` and any old behavioral deviation `tau_i`.  The checked
deviation lift has padded deviating payoff at least the projected old deviating
payoff.  The old-coordinate baseline coupling gives

\[
0\le U_i^+(\sigma^+)-U_i(\sigma)\le \Omega s.
\]

Since `sigma+` is terminal `epsilon`-Nash,

\[
\begin{aligned}
U_i(\sigma[i\leftarrow\tau_i])-U_i(\sigma)
&\le
U_i^+(\sigma^+[i\leftarrow\widetilde\tau_i])
   -U_i^+(\sigma^+) +\Omega s\\
&\le \epsilon+\Omega s\\
&\le \epsilon\left(1+\frac{m\Omega}{A}\right)
=\frac{\epsilon}{f}.
\end{aligned}
\]

The deviation was arbitrary, so

\[
\boxed{\sigma\text{ is terminal }(\epsilon/f)\text{-Nash}.} \tag{2}
\]

### Lemma 3: projected target error

Assume also

\[
|U_i^+(\sigma^+)-v_i^+|\le\epsilon
\qquad(i\in I).
\]

For `v_i=v^+_{\mathrm{inl}(i)}`, the same baseline coupling and (1) give

\[
\begin{aligned}
|U_i(\sigma)-v_i|
&\le |U_i(\sigma)-U_i^+(\sigma^+)|
   +|U_i^+(\sigma^+)-v_i^+|\\
&\le \Omega s+\epsilon\\
&\le \epsilon/f.
\end{aligned}
\]

Thus the projected profile has both Nash error and target error at most the
same rescaled quantity `epsilon/f`.

## Constructive positive retraction

Assume `v+` is a uniform-equilibrium payoff of the padded game.  The checked
fixed-target terminal acceptance theorem supplies, for every `epsilon>0`, a
padded terminal `epsilon`-Nash profile whose terminal payoff is within
`epsilon` of `v+`.

Given any requested old error `eta>0`, choose

\[
\epsilon=f\eta>0.
\]

Project the resulting padded profile.  Lemmas 2 and 3 say that the projected
profile is terminal `eta`-Nash and its payoff is within `eta` of the fixed old
target `v`.  The checked terminal fixed-target compiler yields

\[
\boxed{v\text{ is a uniform-equilibrium payoff of the old game}.} \tag{3}
\]

No contradiction principle, terminal-gap witness, or choice of a new payoff
target is used.  The actual padded target is restricted coordinatewise.

## Quiet lift in the forward positive direction

Conversely, let `v` be an old uniform-equilibrium payoff.  For every terminal
approximate equilibrium implementing `v`, make every new player literally
Never quit.

- Old terminal payoffs and all old unilateral deviations agree exactly with
  the old game.
- Every new player receives zero.  If one new player `j` deviates arbitrarily,
  its payoff is exactly

  \[
  -A\Pr(j\text{ strictly preempts the old absorption})\le0.
  \]

  A tie with old quitters, old preemption, and nonabsorption all pay `0`.

Therefore the lifted fixed target

\[
v^+(\mathrm{inl}(i))=v(i),
\qquad
v^+(\mathrm{inr}(j))=0
\]

is a padded uniform-equilibrium payoff.  Generic all-behavior soundness of
this lift is already stronger in `BlockDeletion.lean`; only the concrete
canonical sum-type adapter and the exact `(oldTarget,0)` identification remain
to be packaged here.

## Cardinal consequence and relation to the three-player proof

Suppose one had a theorem solving every `(k+1)`-player quitting game.  Given
an arbitrary `k`-player game, canonically pad it by one player, apply the
`(k+1)`-player theorem, and project the supplied target and terminal profiles
as above.  This is a constructive reduction from cardinality `k` to
cardinality `k+1`.

For `k=3`, applying a hypothetical general four-player theorem to the padded
four-player game would produce the three-player theorem.  It would **not**
reconstruct Solan's geometric proof.  It would be a short semantic retraction:
the fourth player's Never incentives force its exclusive absorption mass to
zero, after which projection recovers the three-player target.  Of course this
does not prove the three-player theorem independently, because the general
four-player input is stronger and currently open.

Likewise, a hypothetical all-five-player theorem would constructively imply
the four-player theorem by padding and projection.  The result applies only
to the canonical padded subclass; an arbitrary `(k+1)`-player game cannot be
projected unless one player has the required padding reward structure.

## Boundary checks

- If `A=0`, the fresh-only mass need not vanish and no finite factor exists;
  strict penalty is essential.
- If `J` is empty, the statement reduces to identity and should be handled
  separately rather than through `m>0` denominators.
- The proof uses the complete behavioral deviation class on both sides.
- New-player collisions are harmless only because all old-containing rows pay
  new coordinates zero and delete new labels for old rewards.
- The old target is the restriction of the padded target, not a compactness-
  selected replacement.
- This is not a reduction from an arbitrary `(k+1)`-player table to `k`
  players and supplies no solver at a new cardinality.

## Lean handoff

The narrow main statement should be target preserving, for example:

```lean
theorem IsUniformEquilibriumPayoff.of_passivePlayerPadding
    (hpadded :
      (quittingGame (quittingPassivePaddingReward ...))
        .IsUniformEquilibriumPayoff none paddedTarget) :
    (quittingGame reward).IsUniformEquilibriumPayoff none
      (fun old => paddedTarget (.inl old))
```

A quantitative terminal helper should expose the exact `epsilon/f` bounds.
The proof can reuse the five checked padding lemmas listed above and the
terminal-target acceptance certificate.  A second theorem should lift an old
uniform target to the padded target `(oldTarget,0)`.

## Feedback wanted

1. Check the aggregate step `A*s <= sum_j(-U_j)` together with the use of each
   new player's terminal Nash inequality.
2. Check that the fixed-target acceptance theorem supplies the required
   padded terminal profiles for the same declared `v+`.
3. Audit the quiet-lift direction against arbitrary new-player behavioral
   deviations, especially collision timing.
