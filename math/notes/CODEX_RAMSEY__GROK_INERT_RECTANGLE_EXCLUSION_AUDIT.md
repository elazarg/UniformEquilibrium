# Adversarial audit of the proposed inert-rectangle exclusion

**Owner/reviewer:** `CODEX_RAMSEY`  
**Source reviewed:** `../GROK_INERT/inert_rectangle_exclusion.tex`  
**Target:** [`FIN4_BT_QUESTION.md`](../FIN4_BT_QUESTION.md)  
**Verdict:** **FAIL.**  The first fatal gap is Proposition `Sure
complementary quitter`; the later best-reply, dummy-removal, small-boundary,
and cyclic-phase arguments contain additional independent fatal gaps.

This audit does not edit the supplied TeX and does not claim that the target
problem is false.

## 1. Exact sources checked

- `FinFourQuantitativeFullSupportHardResidual.exists_terminalGap_collision_at_singleton`
  in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/PunishmentNormalAtomicCollisionHandoff.lean`;
- `QuittingStoppingLawCommonResponseWitness` in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/VanishingDebtAtomAlternative.lean`;
- `QuittingStoppingLawVanishingDebtRectangleSequence` in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/OffDiagonal/AtomRectangleSequenceAlternative.lean`;
- `QuittingStoppingLawRectangleJointAtomLimit` and the reset minimizer bridge
  in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/RectangleResetFaceMinimizer.lean`;
- `quittingGame_exists_uniformEquilibriumPayoff_threePlayer` in
  `UniformEquilibrium/Quitting/Classification/ThreePlayer/Existence.lean`;
- `quittingGame_terminalNash_all_errors_of_isUniformEquilibriumPayoff` in
  `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`;
- `sSup_range_quittingTerminalPayoff_update_eq_pureTime` in
  `UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean`;
- the stationary fixed-point and endpoint requirements in
  `UniformEquilibrium/Quitting/Stationary/Root.lean` and
  `UniformEquilibrium/Quitting/Stationary/EndpointCompiler.lean`.

## 2. The opening residualization is substantially salvageable

The full-gap singleton joiner is real, but its source is more precise than
the TeX says.  It is not punishment normality alone.  The checked theorem
uses both `residual.witness.exists_atomicCollision_gain_of_normal` and
`residual.all_punishmentNormal`; its margin is
`residual.witness.terminalGap`.  Any smaller positive `gamma` may then be
used.

The rectangle atom is initially a signed difference of terminal-law
coordinates.  In the stated positive-reward orientation, nonnegativity of
the comparison law does give positive endpoint mass.  Since the selected
coalition contains the pure-time observer, the selected pure time must be
finite, and that terminal-law coordinate is a literal stage mass.  Its
uniform lower bound gives the claimed reach floor.

Conditioning at that reached row also works.  If `pi_n` is the shifted
suffix and `h_n` its reach, concatenating any observer deviation in `pi_n`
with the original prefix gives

\[
 h_n d_o(\pi_n)\le d_o(X_n).
\]

Because the observer is sure Quit at the first row of `pi_n`, every other
player's unrestricted debt is exactly its binary one-shot defect in
`Gamma_o`.  Consequently the displayed inequality labelled `(common)` is
not an imported rectangle declaration, but it can be recovered *after*
these two facts:

\[
 D_*\le D(\pi_n)
 =d_o(\pi_n)+\sum_{j\ne o}\rho_j,
 \qquad
 d_o(\pi_n)\le d_o(X_n)/\ell.
\]

The note should therefore remove the nonexistent imported “common lemma”
and reorder this deduction.  This is a repair, not the fatal issue.

The complementary finite game `Gamma_o` and its Nash equilibrium are also
legitimate.  The checked full-gap collision theorem excludes its
all-Continue root.  With the observer committed to sure Quit, complementary
one-shot Nash indeed means zero unrestricted debt for those three players.

## 3. Earliest fatal gap: one-shot Nash is not stationary Nash

Proposition `Sure complementary quitter` selects a Nash equilibrium `x` of
a four-player simultaneous-move game after assigning an arbitrary dummy
payoff to all Continue, and asserts that stationary repetition of `x` is an
exact terminal Nash profile whenever `x` absorbs.  This is false.

For a repeated stationary quitting profile, the all-Continue continuation
payoff must be its **actual stationary payoff vector**.  The exact checked
compiler requires

\[
 v=\operatorname{Succ}_r(v,x)
\]

as well as root endpoint Nash and the relevant boundary conditions.  A Nash
root against an arbitrary dummy vector supplies none of these.  This is
exactly why `Stationary/Root.lean` proves only the necessity direction and
why `Stationary/EndpointCompiler.lean` explicitly assumes the fixed-point
identity.

A two-player calculation already falsifies the inference.  Give player `i`
payoff `1` when it quits alone and `0` when the other player quits (alone or
tied).  Assign dummy all-Continue payoff `v_i=1` in the one-shot game.  For
every symmetric `q in (0,1)`, Quit and Continue both pay `1-q`, so the
product root `(q,q)` is a one-shot Nash root and absorbs with positive
probability.  Its stationary repeated payoff is instead

\[
 U_i={q(1-q)\over 1-(1-q)^2}={1-q\over 2-q}<1-q.
\]

Immediate Quit is therefore strictly profitable in the repeated profile.

The sure quitter present in the earlier, independently selected
`Gamma_o` equilibrium does not force the newly selected four-player Nash
`x` to retain a sure quitter.  Constraining that old label to Quit would fail
to check that label's own deviation.  “Replacing” a coordinate of `x` by a
nearby absorbing perturbation likewise destroys exact Nash and does not
repair the missing fixed point.  Thus the proof already stops in Section 5.

## 4. The claimed three-player profile class and best reply are unavailable

The checked three-player capstone produces a uniform-equilibrium payoff.
Together with the general target-tail theorem it yields a terminal
`epsilon`-Nash profile for each positive error.  It does **not** state that
these profiles are finite-periodic.  The TeX's dichotomy “absorbing endpoint
or finite dispatch of the germ” is proof provenance, not a theorem saying
the resulting terminal profiles are periodic.

For an arbitrary behavioral `sigma^epsilon`, pure-time extremality identifies
the observer cap with a supremum over finite dates and Never.  It does not
assert that this supremum is attained.  Therefore the exact best reply
`tau^epsilon` used to define `C^epsilon` need not exist, and the identity
`d_o(C^epsilon)=0` is unsupported.  An approximate best reply can be chosen,
but all later exact zero-debt and exact-descent formulas would then acquire
errors and require a new argument.

If a finite periodic profile had independently been produced, attainment
could be proved by finite-phase stopping analysis.  The current Lean theorem
does not supply that premise.

## 5. The one-state DFG lemma does not fix the boundary

On the one-state cube with `p_o>=alpha_0>0`, the fractional-linear own-rate
formula, joint continuity, and one-dimensional quasi-concavity are valid.
Debreu--Fan--Glicksberg consequently does return one stationary hazard
vector, rather than a distribution over hazard vectors.  Increasing and
flat observer branches can be upgraded, after checking the `beta=0`
endpoint separately.

The decisive `Dummy-to-free defect` estimate is nevertheless false.  The
proof bounds the payoff-law change on both sides of player `j`'s Nash
inequality by

\[
 {\alpha_0\over \alpha_0+(1-\alpha_0)\beta(y^*)}.
\]

That bound is valid for the prescribed row `y^*`.  After player `j`
deviates, the complementary absorption is
`beta(y^*[j <- q])`, which may be much smaller.  For example, if the entire
original complementary absorption is supplied by `j`, its deviation to
Continue makes that absorption zero; the dummy observer then participates
with probability one, however small `alpha_0` is.  The two payoff-law
comparisons therefore cannot share the displayed denominator.

The valid bound must use an absorption floor uniform over every unilateral
deviation of every complementary player, for example a positive lower bound
on absorption by the *other* complementary players.  Neither the DFG
equilibrium nor the hard-residual packet supplies such a floor.  Hence
`d_j(nu)` is not bounded as claimed, and the large-`beta` descent does not
follow.

The `beta=0` boundary is especially revealing: positive dummy rate makes the
truncated payoff continuous, but after removing the dummy, a complementary
deviation can move directly onto the nonabsorbing discontinuity.  Uniform
geometric absorption in the truncated game is not uniform over the
dummy-free comparison.

## 6. The decreasing-boundary case split is incomplete and circular

Even granting the false dummy-removal estimate, the later reduction is not
exhaustive.  The displayed estimate would force `D(nu)<D_*` only when

\[
 {\beta\over\alpha_0}

\]

exceeds a specific constant of order `M/D_*`.  “Bounded away from zero” is
not enough.  Shrinking `alpha_0` does not change this required ratio.  Thus
the region `beta asymp c alpha_0` with a small positive `c` is not covered by
either the descent arm or the asserted `beta/alpha_0 -> 0` approximation to
`Gamma_o`.

Proposition `Vanishing observer, Case II row` then explicitly replaces the
row by a new Solan profile and says that the result has “already been
dispatched” by Sections 7 and 8.  But the best-reply-lift branch in Section 7
had merely assumed `D(C^epsilon)>=D_*`, while Section 8 is the same DFG cube
whose decreasing boundary is under analysis.  This is a return to the
starting branch, not termination.

The assertion that the new limit is “already constructed as `A_*`” is also
too strong: `Gamma_o` may have several Nash equilibria.  At most it is
another Nash row of the same finite game.

## 7. The `m`-phase extension misuses quasi-concavity

The three-player theorem did not supply a finite period, but even under a
supplied period the final DFG paragraph is not valid as written.  A player's
strategy in the phase game is an `m`-vector of hazards.  Fractional-linearity
in each coordinate separately gives separate quasi-concavity, not
quasi-concavity in the whole vector; DFG requires convex upper contour sets
in the player's entire strategy set.  No such joint theorem is proved.

A suitable finite-state stochastic-game theorem might replace this step,
but it would need exact hypotheses, a constrained-action version, and a
fresh proof of the unrestricted stopping and dummy-removal boundary.  The
current repository declaration `quittingGame_exists_uniformEquilibriumPayoff_threePlayer`
is not that theorem.

## 8. Final disposition

The genuinely useful surviving lemma is the source-matched
sure-row residualization:

\[
 d_o(\pi_n)\le d_o(X_n)/\ell,
 \qquad
 d_j(\pi_n)=\rho_j\ (j\ne o),
 \qquad
 \sum_{j\ne o}\rho_j\ge D_*-d_o(X_n)/\ell.
\]

It turns the rectangle atom into a three-player one-shot defect source and
the hard residual excludes complementary all Continue.  It does not
re-equilibrate that source into an original-game terminal Nash profile: the
continuation fixed point, best-reply attainment, and a deviation-uniform
dummy-removal absorption floor are all missing.

Accordingly the main theorem is unproved, none of `FIN4_BT_QUESTION` Outputs
1--4 follows, and the proposal is not an export or formalization candidate.

