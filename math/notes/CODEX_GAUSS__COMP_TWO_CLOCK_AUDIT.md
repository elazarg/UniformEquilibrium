# COMP periodic two-clock audit

Current status: the Section 4 consumer is mathematically valid after an exact
generated-secant statement repair. The valid constant is slightly stronger
than the draft's constant. Full proof and source audit are in
[`../feedback/COMP__BY_CODEX_GAUSS__TWO_CLOCK.md`](../feedback/COMP__BY_CODEX_GAUSS__TWO_CLOCK.md).

## Declarations inspected

* `twoDiscountDebtError_eq`
* `abs_survivalWeightedSum_le_prefixAbsMax`
* `tendsto_survivalProduct_mul_bounded_zero`
* `exists_quittingTerminalSemanticPrefix_secant`
* `QuittingChronologicalDebtData.prescribedDefect`
* `QuittingChronologicalDebtData.directDebtDefect`
* `QuittingChronologicalDebtShadowingCertificate.isAsymptoticNash`
* `quittingGame_exists_uniformEquilibriumPayoff_of_terminalNash_all_errors`

## Separation of proved and open claims

Proved in ordinary mathematics here: periodic `O(h)` residuals with `O(h^2)`
period sums and `Omega(h)` contraction of both clocks give an unrestricted
terminal `O(h)`-Nash profile; such data at arbitrarily small `h` imply a fixed
uniform-equilibrium payoff.

Already checked in Lean: the exact two-clock identity, generated-secant
recursions, full behavioral cap conversion, and terminal-to-uniform payoff
selection.

Open: construction of the periodic data from either Fin4 endpoint-monodromy
geometry.

## Next concrete question

Can the common-host endpoint cycle be interpolated by literal product roots so
that its generated secants, rather than only its deleted-player Continue
masses, have one-period product at most `1-rho h` while its Bellman residuals
have the required first-order cycle derivative and `O(h^2)` period sum?
