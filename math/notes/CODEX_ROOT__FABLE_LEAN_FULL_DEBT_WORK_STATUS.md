# Fable Lean full-debt work: mathematical status

Identity: CODEX_ROOT  
Date: 2026-08-31  
Status: the original seven scratch files are kernel checked under Lean 4.32.2, with no `sorry`
or forbidden constructs; consolidated axiom audits report only `propext`,
`Classical.choice`, and `Quot.sound`.  Nothing imports this scratch lane and
production integration is pending.  No full-debt consumer is claimed.

## Files inspected

- `fable/lean/FableStoppingSelection.lean`;
- `fable/lean/FableProfitableFork.lean`;
- `fable/lean/FableDebtActualReach.lean`;
- `fable/lean/FableFullDebtGeometry.lean`;
- `fable/lean/FableUniformEntrance.lean`; and
- `fable/lean/FableCommonPrefixFork.lean`; and
- `fable/lean/FableTimeEscapeRegression.lean`.

The subsequent strengthened wrapper
`fable/lean/FableActualReachSupport.lean` has also appeared in the scratch
lane and was inspected here.

All seven originally listed scratch files compile under `lake env lean`.  The
directory is an ongoing scratch lane, not a production Lean integration or
conference export.  The strengthened wrapper now exposes the earlier missing
source-witness support clause: the selected source is either a finite clock
with positive stopping mass or Never with positive Never mass.  The
common-prefix fork itself closes the earlier scope caveat for the reached-atom
reduction.  Neither strengthening controls the new caps after the complete
stopping-law replacement.

## 1. Stopping-law selection

The scratch layer proves two useful exact facts for a bounded pure-time value
function under one behavioral stopping law.

If the prescribed expectation is at least (Delta>0) below its cap, the mass
of stopping choices losing at least (Delta/2) is at least

\[
\frac{\Delta}{4M}.
\]

It also selects the earliest finitely supported bad stopping time, or the
Never branch when all finite bad choices have zero mass, and obtains the
corresponding owner-survival floor. The treatment of Never is literal rather
than a finite-support truncation.

## 2. Profitable complete stopping-law fork

Redirecting all bad stopping-law mass to a pure time within (Delta/4) of
the cap produces one legal unilateral behavioral replacement with gain

\[
\boxed{\frac{\Delta^2}{16M}}.
\tag{1}
\]

The implementation uses the exact equivalence between a behavioral quitting
strategy and its law on (mathbb N\cup\{\infty\}). Thus the fork covers Never,
arbitrarily late pure times, and randomized original hazards.

This proves a complete behavioral payoff edge. It does not control the other
players' unrestricted caps after the replacement.

## 3. Actual reached first-disagreement row

The same positive-debt input supplies a literal paid first-disagreement row
with local gain at least (Delta/4). At its start date,

\[
\Delta\le4M\,S_i,
\qquad
\Delta\le8M\,H_i,
\]

where (S_i) is the prescribed player's own survival and (H_i) is the
opponents' live mass. Their exact product factorization yields the genuine
joint source-reach bound

\[
\boxed{
\Delta^2\le32M^2\,
\Pr_\sigma(\text{reach the row start}).}
\tag{2}
\]

This is the important advance. It removes the earlier defect in which the
paid row carried only deleted-observer or opponents-only reach.

## 4. Full-debt geometry

## 4. Literal common prefix of the complete fork

The newer scratch theorem
`positiveDebt_exists_commonPrefix_profitableStoppingLawFork` strengthens the
actual-reach result.  The profitable complete stopping-law replacement is
chosen so that the observer's transported stopping law agrees with the
source law at every finite time strictly before the paid row.  The file proves
this at four equivalent levels:

- finite stopping masses;
- survival probabilities;
- reconstructed conditional hazards; and
- the realized behavioral strategy at every earlier live history.

Thus the fork is not merely attached to a source carrying positive reach.  It
is a literal source suffix replacement at its first paid disagreement.  Its
quantitative fields are unchanged: row gain at least (Delta/4), total payoff
gain at least (Delta^2/(16M)), own survival at least (Delta/(4M)), and
opponent live mass at least (Delta/(8M)).

This removes the pre-row chronology seam.  It does not control the other
players' unrestricted caps after the observer's stopping law is changed, and
therefore does not make the old outer cap--Nash roots exact for the target.

## 5. Full-debt geometry

Two finite-dimensional lemmas in the scratch layer are mathematically sound.

First, near a full-debt global minimum, source profiles are eventually
strictly above every behavioral punishment floor. This follows from the
global singleton moat and the positive complementary debt of the other three
players.

Second, along a marked exact orbit whose source is sufficiently close to a
full-debt minimum, every debt coordinate remains uniformly positive. Exact
prefix debt is coordinatewise antitone, while global minimality bounds the
total loss. In the displayed normalization every coordinate stays at least
(delta/2).

These facts prevent an accidental support drop along the selected exact
prefix orbit.

## 6. Uniform entrance through exact floor prefixes

The proposed prefix theorem combines two checked ingredients:

1. the terminal exploitability gap bounds every exact punishment-floor
   root's Continue probabilities away from zero; and
2. the canonical prefix-charge theorem bounds the sum of its absorption
   masses.

If each absorption (a_t\le1-\eta) and
(sum_ta_t\le B), then

\[
\prod_t(1-a_t)\ge e^{-B/\eta}>0.
\tag{3}
\]

Consequently every finite certified prefix retains one horizon-independent
positive fraction of the source suffix. This is stronger than a stagewise
Continue floor alone.

It does not say that the same roots remain exact after the downstream paid
fork changes a player's complete strategy and the other players' caps.

## 7. Exact all-Continue time escape

The regression layer verifies literally that iterated all-Continue prefixing
preserves the complete terminal semantic pair and the time-forgetting
terminal law whenever the cap dominates singleton rewards. It shifts every
finite pure-time deviation by the prefix length and fixes Never.

This is the sharp negative boundary: arbitrary depth, fixed semantics, and a
fixed law do not provide a forward chronological return. Pure-time witnesses
can simply escape to later dates.

## 8. Combined consequence

For a near-full-debt source, the scratch development now supplies all of:

- punishment-floor safety;
- persistence of full debt along the selected exact orbit;
- a complete profitable stopping-law replacement with floor (1);
- a paid first-disagreement row with actual joint reach (2); and
- a complete fork literally identical to the source before that row; and
- uniform source entrance through every finite exact floor prefix, via (3).

This closes the local producer problem “does positive full debt give an
actually reached paid fork?”

It does **not** close the full-debt chamber. After the stopping-law
replacement, the old prefix roots need not remain Nash against the changed
continuation caps. The remaining theorem is still an extension-compatible
rebase, return, or cap-leakage consumer:

\[
\boxed{
\text{uniformly reached paid fork}
+\text{bounded exact-prefix capacity}
\Longrightarrow
\text{terminal approximation, charged return, or contradiction}.}
\]

The all-Continue time-escape regression shows why semantic/law invariance
alone cannot supply this implication.  After the common-prefix upgrade, the
uncontrolled seam is now sharply localized: it is the target-side cap/root
change caused at and after the first paid disagreement, not source ancestry
or pre-row reach.

## 9. Fixed paid depth or all-player marginal escape

There is a useful source-level consequence which does not require preserving
the old roots after the fork.  Let actual source profiles converge to a
full-debt minimum point.  Choose

\[
0<\Delta<\min_i d_i(x).
\]

For every sufficiently late source profile, apply the common-prefix theorem
to one fixed player.  Its first-disagreement date (t_n) satisfies the uniform
joint-reach bound

\[
\Pr_{\sigma_n}(\hbox{all players survive to }t_n)
 \ge \frac{\Delta^2}{32M^2}=:c>0.
\]

After a subsequence, exactly one of the following occurs.

1. The dates (t_n) are one fixed finite date.  Then the source family carries
   a fixed-depth, uniformly reached paid behavioral fork.
2. The dates tend to infinity.  Compactify the four marginal stopping laws.
   For every fixed (N), eventually (t_n>N), so the limiting product law gives
   probability at least (c) to joint survival beyond (N).  Letting (N) tend
   to infinity shows that the reconstructed limiting profile has joint-Never
   mass at least (c).

The second arm is precisely an all-player marginal-escape input: the selected
time-forgetting terminal-law limit may still place that mass on finite
coalitions, which is why the checked all-player escape account is needed.
It is not a terminal equilibrium or an attainment theorem.  The strict
positive-social-surplus subarm of that account still has no consumer.

This split is nevertheless useful bookkeeping.  Full debt cannot hide every
paid witness in a merely diffuse sequence of dates: the only escape from a
fixed paid depth is a quantitatively positive joint-Never atom in the compact
marginal-law realization.

## Integration caution

The local theorem names are kernel-checked scratch names, but should not be
cited as production declarations until the files pass the project's
integration and import gates. No conference export is needed for code already
being developed; the mathematical result should be counted at its present
checked-scratch level.
