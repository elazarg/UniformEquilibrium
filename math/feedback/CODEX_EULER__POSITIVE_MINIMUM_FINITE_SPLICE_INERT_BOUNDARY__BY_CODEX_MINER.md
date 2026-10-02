# Independent review of positive-minimum finite-splice inert boundary

Reviewer: `CODEX_MINER`

Verdict: **PASS at the stated internal/no-consumer scope.**  The finite
subsequence dichotomy, semantic/debt convergence after four splices, and the
eventual literal-`InertStall` conclusion all check.  This does not contract the
maintained paid descent-or-inert residual; it sharply rules out finite capping
as a way to regenerate a charged port near the strict Fin4 minimum plateau.

## Claim checked

Starting with actual profiles whose terminal-semantic pairs converge to the
strict positive Fin4 minimum point, successively move each player's late and
Never mass to a finite cutoff.  After diagonal subselection, either one stage
retains a fixed positive

```text
NeverMass * MaxPairDeletedSurvivalLimit
```

or all four finite splices perturb the full semantic pair by `o(1)`.  In the
second arm the final profiles still have total debt tending to the positive
minimum and every freshly generated canonical paid cap port is eventually a
literal inert stall.

## Checks

1. The terminal value of `quittingFiniteSpliceError` is exactly the product
   used in the note.  After selecting a convergent subsequence at one stage,
   a positive limit gives a uniform positive lower bound, while a zero limit
   is precisely the premise of
   `exists_finiteSpliceCutoffs_tendsto_zero_of_capTight`.  Further finite
   subselections preserve all earlier convergence and cutoff-divergence
   statements.

2. The checked payoff and unrestricted best-response-envelope estimates both
   have the required `2*M*error` form, and the debt estimate has the required
   `4*M*error` form.  Applying them at four successive player splices gives
   convergence of both coordinates of the final semantic pairs to the same
   minimum.  Later splices modify only other marginals, so each already capped
   marginal remains a proper finite-deadline stopping law.

3. The nonapproximation conclusion is exact.  If the final profiles were
   `epsilon_n` terminal asymptotic Nash with `epsilon_n -> 0`,
   `quittingTerminalSemanticDebtSum_le_card_mul_of_isEpsilonAsymptoticNash`
   would force total debt to zero.  This contradicts convergence to
   `D_*>0`.  The displayed `D_*/8` coordinate lower bound is valid for
   `Fin 4` once total debt is eventually at least `D_*/2`.

4. The use of the open tube in Corollary 5.1 is sound.  Semantic convergence
   gives envelope convergence `B(sigma_n^4) -> B_*`; the tube is open and
   contains `B_*`, the `t=0` endpoint of the closed debt homotopy.  Hence the
   initial envelope is eventually in the tube.  At each canonical cap-prefix
   depth, `quittingCapLiftedPrefixRoot_exactNash` makes the selected root exact
   Nash against the current envelope.  Tube uniqueness forces that root to be
   literally all Continue.  Then
   `quittingTerminalSemanticPrefix_allContinue_eq_self_iff_isZeroNash_at_cap`
   fixes the entire semantic pair, so the same envelope remains in the tube
   and the induction continues at every finite depth.

5. Since every canonical root is all Continue, each nonnegative absorption
   summand is zero and the complete total-absorption series is exactly zero.
   `QuittingPaidCapLiftedSource.inertStall_of_totalAbsorption_eq_zero` then
   packages the claimed cap-displacement, semantic-pair, reach, debt, and
   lossless shifted-paid-row fields.  Re-running the actual-profile paid-port
   adapter after the splices gives the required fresh source/profile
   provenance; no old paid row is silently transported through the splices.

## Scope and novelty

The argument composes checked finite-splice estimates with the independently
reviewed ordinary-mathematics eventual-inert theorem.  It does not prove a new
Lean declaration.  Its complementary positive deleted-clock product has no
current terminal-approximation, charged-return, or rank consumer.  The
cap-tight arm returns to the already maintained inert obstruction rather than
eliminating it.  I therefore recommend retaining this note internally and not
exporting it as conjecture progress.

