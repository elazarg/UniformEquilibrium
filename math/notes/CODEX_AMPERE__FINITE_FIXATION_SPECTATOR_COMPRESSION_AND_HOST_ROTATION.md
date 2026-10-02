# Finite-fixation spectator compression and host rotation

## Status

Ordinary mathematics, not checked in Lean and not independently reviewed.

The finite-fixation forced-pair packet gives no upper bound on the spectator
leakage

$$
K_p=\sum_{i\ne p}\bigl(d_i(Y)-d_i(Z)\bigr)
$$

after the canonical payer is spent.  Positive-minimum provenance and the
terminal witness give lower bounds on this leakage, not the missing upper or
no-entry bound.

There is, however, an exact source-attached compression which replaces the
three uncontrolled spectator coordinates by one owner coordinate.  It uses the
forced owner's literal finite clock, re-equilibrates the other three players in
a finite timing game, and makes the remaining owner's unrestricted cap a
finite maximum.  The result is stronger in provenance than the existing
generic singleton-base handoff, but it does not preserve the other players'
literal source word, the minimum fibre, or the forced-pair law.

The residual is a finite host-rotation problem.  A strict Never repair has an
exact sign certificate.  Host labels range over a finite set, but the induced
semantic state does not: re-equilibrating around a new host can reactivate a
player previously changed to Never.  Thus even the Never updates have no
finite-deletion rank.  The checked cyclic-plateau regression reinforces that
host-label recurrence is not semantic recurrence or a support descent.

## Question and input

Let a four-player quitting game have a terminal exploitability witness with gap
`gamma > 0`.  Suppose the source-attached forced-pair construction supplies an
actual profile `Z`, a finite marked date `T`, and a pure marked coalition

$$
C=\{j,o\}.
$$

Let `p != o` be the canonical paid mover and let `Y` be the profile obtained by
changing only `p` to its exact better endpoint at the marked row.  The forced
owner `o` is unchanged.  Consequently, against every unilateral deviation of
any other player, `o` still quits no later than `T` whenever play remains live.

The original target was an upper bound, no-new-support statement, or
chronological control on the spectator leakage after the move `Z -> Y`.

## 1. Why global minimality does not upper-bound leakage

Write

$$
L=D(Z),\qquad g=d_p(Z),\qquad d_p(Y)=0.
$$

Because changing `p`'s prescribed strategy leaves `p`'s best-response cap
unchanged,

$$
D(Y)=L-g+K_p.
$$

Global minimality gives only

$$
K_p\ge g-(L-D_*).
$$

The terminal witness at `Y` also points in the same direction.  Since the
mover's debt is now zero, some spectator has debt at least the witness gap, so
the witness supplies another lower bound on aggregate spectator debt.  Neither
argument controls support entry.

On the unilateral stopping-law chord from `Z` to `Y`, the mover's prescribed
payoff is affine and its cap is fixed.  The other caps are suprema of affine
pure-time payoff functions, hence convex and piecewise affine when the relevant
menu is finite.  Convexity does not control the endpoint slope from above.
Thus the natural global-minimum mixture argument does not reverse the sign.

## 2. Finite-anchor complementary Nash theorem

### Theorem

Let `h` be a player in a finite quitting game and let `sigma_h` be a literal
behavioral strategy such that, if play remains live, `h` quits by a fixed date
`T` with probability one.  Then there is an actual behavioral profile
`widehat sigma` with the following properties.

1. Player `h` uses exactly `sigma_h`.
2. Every player `i != h` has zero unrestricted terminal debt:

   $$
   d_i(\widehat\sigma)=0.
   $$

3. Every complementary player uses a stopping law supported on
   `0,...,T,infinity` and Continues after `T`.
4. Player `h`'s unrestricted cap is attained by one of the finite menu

   $$
   Q_0^h,\ldots,Q_{T+1}^h,Q_\infty^h.
   $$

### Proof

Keep `sigma_h` fixed.  Form the finite strategic timing game for the other
three players, with pure actions

$$
A_T=\{0,1,\ldots,T,\infty\}.
$$

The payoff of a timing profile is its quitting-game terminal payoff against
the fixed law of `sigma_h`.  This is a finite game, so it has a mixed Nash
equilibrium.  Realize each independent mixed stopping time behaviorally by the
usual hazard construction, and prescribe Continue after date `T`.

Fix a complementary player `i`.  Against the other strategies, an arbitrary
behavioral deviation of `i` is equivalent to first sampling its eventual
stopping time.  Since `h` quits by `T`, every stopping time after `T` has the
same payoff as Never.  The arbitrary deviation payoff is therefore a convex
combination of the finite pure-action payoffs in `A_T`.  Nash optimality of the
finite timing game proves `d_i=0` against the full behavioral strategy class.

For player `h`, the three opponents stop only at dates at most `T`, or Never.
All finite stopping times of `h` after `T` have the same payoff, represented by
`Q_{T+1}^h`; Never remains the only other limiting action.  Every behavioral
payoff of `h` is a convex combination of these finitely many pure-time values.
Thus its unrestricted cap is the displayed finite maximum and is attained.

## 3. Application to the paid forced-pair endpoint

Apply the theorem to `Y` with host `h=o`.  The construction retains:

* the same reward table and terminal witness;
* the exact forced owner's complete behavioral strategy;
* its actual finite quitting deadline and marked source date; and
* a pointer to the full incoming forced-pair packet.

It does **not** retain the other three players' prefix roots, the marked pair
law, the minimum semantic point as the new profile's semantics, or the
canonical payer's zero-debt identity.  The re-equilibration changes all three
free stopping laws.

At the new profile, all three free debts vanish.  The terminal witness hence
forces

$$
d_o(\widehat\sigma)\ge\gamma.
$$

Choose a cap-attaining action from the finite menu and replace `o` by it.
Because an own-strategy replacement does not change the owner's cap, this is
an actual source-attached paid move of gain `d_o`, and the updated owner debt is
exactly zero.  The terminal witness then forces debt of at least `gamma` onto a
free player.

This is an exact compression of arbitrary spectator leakage into one paid
host move.  It is not yet a return or a rank decrease.

## 4. Exact classification of the Never arm

Let `rho` be the probability that all three finite-clock opponents of `h`
choose Never.  Put

$$
s_h=r_h(\{h\}).
$$

For every finite `t > T`, all opponent terminal events before `t` are identical
under `Q_t^h` and Never.  On the only remaining event, of probability `rho`,
`Q_t^h` terminates alone and Never gives the infinite-play payoff zero.
Therefore

$$
\boxed{
V_h(Q_{T+1}^h)-V_h(Q_\infty^h)=\rho s_h.
}
$$

Consequences:

* if `rho=0`, Never ties the finite action `Q_{T+1}`;
* if `s_h >= 0`, a finite action weakly dominates Never;
* a genuinely strict Never-only maximizer requires

  $$
  \rho>0\quad\text{and}\quad s_h<0.
  $$

Thus the exceptional branch is finite and signed.  Punishment normality
`chi_h <= s_h` does not exclude it.  Under the hard residual it instead forces
the alternative singleton-collision geometry recorded by the existing witness
dispatch; that recreates a possible new host but is not a contradiction.

## 5. Host rotation is not finite deletion

The complementary timing equilibrium is a finite-clock profile.  If its host
best response is finite, that best response is a new literal sure clock and
the complementary-Nash construction can be repeated with the same host.

If the strict best response is Never, the immediate update replaces a player
whose current strategy was not Never: a player already prescribed Never cannot
gain strictly by choosing Never again.  If one now postpones
re-equilibration, keeps the remaining finite-clock profile fixed, and repeatedly
uses the terminal witness, every new positive-gain cap is still attained on a
finite menu.  Each Never repair removes one currently non-Never law.  Thus,
within at most four such literal repairs, some selected repair is finite and
provides a new sure host.  A player already prescribed Never can only be a
positive-debt witness through a finite repair.

This bounded *host-recovery episode* does **not** define a global deletion
rank.  Once a new finite host is chosen, solving its complementary timing game
changes the other three complete stopping laws and can give positive stopping
mass to a player deleted in an earlier episode.  The number of non-Never
strategies therefore need not decrease across re-equilibrated host changes.

Therefore exact finite-cap repairs admit a finite host-rotation description:

$$
\boxed{
\text{finite host}
\longrightarrow
\text{finite host repair}
\quad\text{or}\quad
\text{strict signed Never deletion},
}
$$

but neither arm decreases a known natural-valued rank.

This is not a well-founded semantic descent.  Re-equilibrating the other three
players changes three complete strategies at once.  Returning to a previous
host label does not return to the same semantic pair, terminal law, minimum
source, or exact prefix word.  The paid gains do not telescope against one
fixed prescribed payoff.

## 6. Comparison with existing results

### Pure singleton re-equilibration

`notes/ATLAS_GATEKEEPER__PURE_SINGLETON_REEQUILIBRATION.md` already solves the
three free players around a pure singleton base and leaves a single owner wall.
Its cleanest form is a date-zero singleton followed by an actual tail; the
owner wall is measured against the tail cap.  The strict wall remains an
off-minimum obstruction.

The theorem here has the same game-theoretic core.  Its additional content is
the finite-clock attachment: the host is the literal forced owner from the
incoming paid endpoint, it guarantees absorption at the actual finite source
date, and its unrestricted cap reduces to a finite pure-time menu.  This makes
the next owner repair actual and finitely attained.  It does not by itself
consume that repair.

### `SingletonBaseSameLawResetProducer`

The checked `SingletonBaseSameLawResetProducer` constructs, for a prescribed
owner, a stationary singleton-base source with complementary equilibrium,
owner gap, paid row, terminal atom, and same-law reset data.  It may select a
new stationary source on the same reward table.

The present construction is narrower but more source-faithful: it retains the
incoming forced owner's literal finite stopping strategy and marked deadline.
It does not supply the checked producer's stationary same-law reset target or
its full packet fields.  Consequently it is not a replacement for that
producer, and downstream consumers which require the reset target gain nothing
from the extra attachment.

## 7. Sharp no-go for closing by host labels alone

The checked four-player cyclic-plateau regression gives a finite cycle of
literal unilateral reset moves with exact debt circulation, a persistent host
debt, and all-Continue as the unique exact cap-Nash root.  Its global minimum is
zero, so it is not a counterexample to the positive-minimum theorem.  It does
show that

$$
\text{finite cap attainment + paid host rotation + label recurrence}
$$

does not imply chronological return, debt descent, or a nontrivial cap root.
Any positive theorem must use the retained positive-minimum/source provenance
quantitatively, rather than merely append it to the host-rotation state.

## Verdict and remaining interface

No upper or no-entry control on `K_p` follows from the current positive-minimum
data.  The strongest new exact reduction is:

$$
\boxed{
\begin{array}{c}
\text{source-attached finite forced owner}\
\Downarrow\\
\text{three unrestricted debts vanish}\
+\ \text{one finitely attained owner cap}\
\Downarrow\\
\text{finite paid repair}\
\quad\text{or}\quad
\text{strict Never deletion with }\rho>0,\ s_h<0.
\end{array}}
$$

The remaining producer must turn the resulting source-attached host rotation
into one of:

* a return to one fixed minimum semantic/full-law target;
* a renewable support or face-rank decrease; or
* terminal approximants.

Without such a theorem, this result is a source-provenance strengthening of an
existing singleton-base reduction, not a consumer of the finite-fixation
obstruction.

## Repository declarations and files inspected

* `QuittingConcentratedCollisionMinimumResidual`
* `QuittingPositiveMinimumReturnForcedPair`
* `FinFourMaximalPrefixRayDichotomy`
* `FinFourNormalizedReturnCapstone`
* `quittingSameStageEndpointMonodromyImpossible`
* `FinFourCyclicPlateauCandidate`
* `SingletonBaseSameLawResetProducer`
* `QuittingSingletonBaseSemanticDispatch`
* `QuittingPrescribedOwnerStationaryHandoff`
* `TerminalSemanticPlateauPairDropoutConsumer`
* `TerminalSemanticSignedPairDropoutConsumer`
* `exists_pureTimeCap_gap`

Files inspected include the corresponding modules under
`Research/Quitting/FinFourProducerAtlas/`,
`Research/Quitting/SameStageEndpointMonodromyImpossible.lean`,
`Research/Quitting/FourPlayerCyclicPlateauCandidate.lean`, and
`UniformEquilibrium/Diagnostics/Quitting/Collision/`.

## Next concrete question

Does positive-minimum provenance imply that one finite-host
complementary-Nash repair can be selected so that either its strict Never arm
lands on the minimum fibre with smaller positive-debt support, or its finite
repair returns to the incoming minimum law?  A valid theorem must compare the
new re-equilibrated profile to the incoming source, not only compare host
labels.
