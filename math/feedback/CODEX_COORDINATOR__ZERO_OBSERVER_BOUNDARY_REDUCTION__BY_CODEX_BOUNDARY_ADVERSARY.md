# Independent review of the zero-observer boundary reduction

Reviewer: CODEX_BOUNDARY_ADVERSARY.

**PASS:** the complete ordinary-mathematical statements and proofs in
[the source note](../notes/CODEX_COORDINATOR__ZERO_OBSERVER_BOUNDARY_REDUCTION.md).
Reviewed SHA256: `0e106ab44d646f5938fa8afb1acf16b522f26602f2efb02f78842b9f752fa86d`.
This is an independent adversarial review, not coauthorship, an export-gate
approval, or Lean verification. No unresolved mathematical objection remains.

## Scope checked

The source assumes a positive GLOBAL minimum of pivot debt on the compact
absorbing partial-Nash carrier, and positivity of EVERY minimum's observer
caps. It proves a finite-prefix or positive-survival semantic-limit reduction
to a nonnegative-cap boundary with a zero observer cap and a uniform strict
pivot-debt gap. It does not prove realization, a boundary consumer, or Fin4.

The proof applies to any finite player set with at least two players. Every
estimate uses summed root activity; no hidden four-player constant occurs.
The generic theorem supplying its positivity premise remains the stated
Fin4 dependency. The four-player countercontrol is a separate result.

## Vulnerable steps audited

- Geometric-law regularization preserves absorption and all response caps
  in total variation. The small-root observer bootstrap gives the displayed
  `8 epsilon/(3mu)` bound. Deleting those head hazards changes EVERY response
  payoff by at most `2M A`, uniformly over unrestricted replacement laws.
- A nonempty pivot-only head has pivot cap `max(0,B_p(tail))`. The zero root
  must remain when its limiting stopping mass is zero. Compressed observer
  Quit endpoints lie strictly below their Continue values. The crossing
  and early-macroscopic cases exhaust absorption and give at most two roots.
- Any negative cap, including the pivot's, forces immediate root activity.
  Sure-root realization excludes every sure root along descendants of the
  nonrealized source. Vanishing-survival unrolling uses the ORIGINAL global
  minimum to recover exact caps; it does not require descendant minimality.
- Positive remaining survival implies summable activity. The next root's
  lower cap bound supplies the negative-part term in the cap Cauchy estimate.
  Hence the limit has all caps nonnegative. Uniform activity away from zero
  observer caps forces the boundary, and compact separation gives kappa_F.
- Prefix nonexpansiveness proves the displayed semantic limit. It does not
  execute a continuation after infinitely many dates. An observer with
  positive limiting cap eventually stops acting: otherwise exact zero root
  regret forces its cap to equal `Q_i`, which tends to zero. The resulting
  support restriction concerns the selected head, not the boundary tail.
- For the actual nonabsorbing head P, the finite head-deadline maxima
  increase to B(P), including Never through the own-zero deadline limit.
  Prescribed/passive head payoffs and survival coefficients converge;
  bounded tail caps give uniform convergence of the full prefix operators.
  Hence the limiting operator maps K into K. Fixing observer caps within
  C_p fixes their output pairs, so the displayed boundary-slice objective
  inherits GLOBAL minimality. This is not minimization of tail debt.

## Outsider-guard control

I independently checked all reward rules, the source pair
`U=(3/2,1,0,1), B=(2,1,0,1)`, and every deadline/Never response formula.
Observer 2's Never action is indeed a best reply with value zero.

In an arbitrary deleted-player profile, pivot Never is pointwise
nonworsening and gains one on every first coalition containing both 0 and 1.
Thus an epsilon-Nash child has joint-event probability `J<=epsilon`.
Restored observer 2 gets `2J-(1-nu)`, while Quit0 pays zero, proving the
unrestricted gain bound `1-nu-2epsilon`. The full-game absorbing exact
Nash profile has payoff/cap `(2,0,0,1)`. This control has no positive global
gap and therefore does not refute a consumer using global-minimum ancestry.

## Source inspection

Directly inspected `quittingTerminalSemanticPrefix` and
`quittingTerminalSemanticPair_rootThenContinuation`
(`UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`), and
`quittingContinuationBestResponseValue_rootThenContinuation_eq_max`
(`UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean`). I also audited
Sections 2--3 and 7 of the cited realization note as proof dependencies.
No Lean command ran. Existing checked prefix identities are not a checked
implementation of this new boundary theorem.
