# Second independent falsification of Proposition 6BM

Reviewer: `CODEX_CEDAR`

Verdict: **PASS, no repair**, as ordinary mathematics in the exact
proper-sentinel strategy-class scope.  This is the required second
independent falsification for the unrestricted-class claim.  I checked the
weak topology and truncation uniformly in all unrestricted opponent laws,
the compact-game Nash hypotheses, the selector and tail contrapositives,
the new intrinsic-Never addendum `(6BM.6a)`, the complete-class consumer,
and the nonproper-law boundary example.

## Theorem 6BM.1: continuity and compact-game Nash

For `Omega = Nat union {infinity}` with its one-point compactification,
`P(Omega)` is compact, convex, and metrizable in the weak topology.  Every
point is an ordinary complete quit-time law; the conditional hazard formula
realizes it behaviorally, with arbitrary post-zero-reach hazards irrelevant.

Let `F_s` be a finite proper net.  Each member has zero Never mass and finite
tail tending to zero.  Finiteness gives one cutoff `H` with

```text
sup_(nu in conv(F_s)) nu(T_s > H) < eta.
```

The convex-hull bound is exact because tail probability is affine.  On
`T_s <= H`, absorption occurs by `H`.  The cells `{0},...,{H}` and the tail
`{H+1,...,infinity}` are clopen in the one-point compactification, so the
truncated payoff is a finite multilinear polynomial in weakly continuous
coordinate masses.  Replacing the payoff by zero on the discarded event
costs at most `M eta`, not `2 M eta`, because this is truncation of one
bounded payoff rather than comparison of two terminal rewards.  Thus the
actual payoff is a uniform limit of jointly continuous functions, uniformly
over every unrestricted opponent law.

The auxiliary strategy sets

```text
conv(F_s) x product_(i != s) P(Omega)
```

are nonempty compact convex subsets of locally convex spaces.  The payoff is
jointly continuous and affine, hence quasiconcave, in each own law.
Fan--Glicksberg/Kakutani therefore gives an exact auxiliary Nash profile.
All nonsentinel players already have the full stopping-law space, so their
inequalities cover every behavioral deviation exactly.  The sentinel's
inequality for each `f in F_s`, followed by its global strategic-net estimate,
gives the stated `eps` inequality for every member of `D_s`.  This also
covers the declared empty-family convention.

## Selector tails and `(6BM.6a)`

A fixed-gap selector cannot have any properly strategically approximable
range: at the profile from Theorem 6BM.1 the selected nonsentinel is
controlled exactly, while a selected sentinel is controlled within
`eps < g`.  An empty range is approximable, so every player identity must
occur.

Proper finite TV approximation is equivalent to the uniform cutoff condition
whose tail includes infinity.  One direction unions finite cutoffs for a
finite proper net.  Conversely, move the uniformly small tail to one fixed
finite date and net the resulting finite-dimensional simplex.  The centers
are proper and the TV error is the moved tail mass.  Together with
`d_s <= 2 M TV`, the contrapositive gives one fixed positive late-or-Never
mass for each identity.  Combining this with reviewed Proposition 6BL is
legitimate and yields genuinely late finite mass for at least two distinct
identities, without asserting simultaneous selection.

The new addendum `(6BM.6a)` also checks.  If total bounded `D_s` fails proper
approximation at error `eta`, choose an `eta/3` strategic net with centers in
`D_s`.  Were every center within `eta/3` of some proper law, the finitely many
chosen proper laws would form a `2 eta/3`-net, contradicting failure at
`eta`.  Hence some center has distance at least `eta/3` from every proper
law, so one may take `zeta_s = eta/3`.  That center must have positive Never
mass: zero Never mass is exactly properness on this clock space and would put
the center itself in `P_s`.  This is an intrinsic payoff separation, not a
claim that the essential-Never witness is selected simultaneously with either
late-finite witness.

## Complete-class consumer

If the sentinel range is complete for unrestricted best responses, take the
supremum of its approximate inequality over `D_s` and apply completeness.
Every nonsentinel inequality is already unrestricted.  This gives terminal
`eps`-Nash profiles at all positive errors, and the checked theorem
`quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
then yields a uniform-equilibrium payoff.  No compactness or completeness of
the other reply ranges is used.

## Concrete nonproper boundary test

Assume the sentinel's solo payoff and every payoff it receives while absent
are zero.  Couple `Never` with `mu_L`, uniform on `L` distinct finite dates,
against arbitrary opponent clocks.  If the sentinel is strictly first, both
comparisons pay zero (solo versus the eventual absent/Never outcome); if an
opponent is strictly first, both pay the same zero absent row.  They can
differ only when the sentinel ties the opponents' first time.  The tie events
at the `L` dates are disjoint, and each sentinel atom has mass `1/L`, so their
total probability is at most `1/L`.  The comparison payoff is zero on the
Never side and has magnitude at most `M` on a tie.  Therefore

```text
d_s(mu_L,Never) <= M/L
```

with no missing factor two.  Hence `{Never}` is properly strategically
approximable despite containing no proper law.  If every row containing the
sentinel also pays it at most zero, every deviation has payoff at most zero
while Never pays zero; `{Never}` is then best-response complete exactly as
claimed.

## Source and scope audit

The checked terminal-all-errors theorem supplies only the final consumer.
The compact-game argument is ordinary mathematics and does not assume a Nash
theorem for the discontinuous full stopping-law product: one uniformly proper
sentinel is precisely what restores continuity.  The opposing all-clocks
escape seam is the one recorded in
`notes/CODEX_CEDAR__STOPPING_TIME_COMPACT_GAME.md`.

The theorem does not construct an incentive table, simultaneous late clocks,
target-pair atoms, or a leftover-mass estimate.  It applies only when one
player has the stated properly approximable (and, for the existence consumer,
complete) class.  Within that scope the proof covers arbitrary behavioral
strategies of every other player.  I found no mathematical objection to
packet assembly, but the separate whole-packet `exports/README.md` gate,
including source correspondence and Lean handoff, remains required.

