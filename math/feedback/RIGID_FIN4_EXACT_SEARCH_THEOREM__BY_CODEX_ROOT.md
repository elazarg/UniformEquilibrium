# Review of rigid Fin4 exact search

## Verdict

**PASS as ordinary mathematics for the per-accuracy resolver, with a required
scope correction.**  The package gives a sound exact generator/verifier for
the following statement: for each normalized rational Fin4 table and each
rational `epsilon > 0`, the dovetailed search eventually returns either a
global positive exploitability lower certificate of size `epsilon / 4`, or an
actual rational finite-clock profile of exploitability below
`3 * epsilon / 4`.

It does **not** give a terminating table-level decision procedure, consume the
strict inert Fin4 component, or by itself produce a counterexample table.  On
the zero-gap side it is a productive infinite process: successively requested
scales emit profiles of vanishing error, but no finite stage certifies that all
future scales will do so.

## Claim checked

For level `N`, use literal product stopping laws on `8 * N + 1` finite dates
and a separate Never atom.  Let `O_N` be the coordinatewise `12 / N` semantic
tube around those actual centers, and minimize

`max(0, B_0-U_0, ..., B_3-U_3)`

over `O_N`.  Exact interval subdivision searches for a lower bound on this
outer minimum, while exact rational finite-clock enumeration searches for a
small-exploitability actual profile.  With

`N = floor(96 / epsilon) + 1`, `a = epsilon / 4`, and
`b = 3 * epsilon / 4`, at least one search terminates.

## Mathematical audit

The constants and all-behavior interpretation agree with the checked project
foundation:

- `quantileClockSupport_fin4` gives support `8 * N + 1`;
- `quantileClockRadius_fin4` gives semantic radius `12 / N`;
- `escapeAwareQuantileClock_fin4_normalized_quantitative_bracket` gives the
  objective gap `24 / N`; and
- the forward and reverse pure-time transport results in
  `Research/Quitting/EscapeAwareQuantileClockTransport.lean` control the
  unrestricted pure-time-or-Never cap, not a bounded or stationary cap.

The single-shell relaxation is sound.  Every actual semantic pair lies in the
last shell, while every shell center is an actual independent finite-clock
profile.  The exploitability objective is 2-Lipschitz, so its shell minimum
`A_N` satisfies

`eta - 24/N <= A_N <= eta`.

The finite expression system correctly retains:

- four independent marginal laws;
- a separate Never mass;
- a zero-mass after-support date available to deviations;
- exact earliest-coalition product probabilities; and
- the maximum over every payoff-distinct finite deadline and Never.

The interval-tree checker is sound.  Its strict-margin completeness argument
is also valid: if `A_N > gamma`, every point of the compact root box has an
open neighborhood certified by a separated equality, a violated inequality,
or an objective lower bound.  Longest-normalized-side dyadic subdivision makes
box diameters tend to zero on every infinite branch, so compactness (or
equivalently Koenig's lemma) gives a finite complete tree.

The scale dichotomy is exact.  If `A_N > a`, the lower tree eventually closes.
If `A_N <= a`, a witnessing actual center has exploitability below
`a + 24/N < epsilon/2`, leaving strict room below `b`; rational density then
makes the upper enumeration terminate.  The equality case `A_N = a` is safely
in the upper arm.

## Implementation audit

I inspected `rigid_fin4_exact_search.py`, the theorem document, manifest, and
all nine regression tests.  In the supplied environment `pytest` is not
installed, but the module compiles and all nine plain test functions pass when
invoked directly.  The direct finite-clock semantics and generated outer
expressions agree exactly on the nontrivial rational test instance.

`ScaleSearch` is an actual dovetailed generator, not merely a verifier.
`LowerTreeCertificate.verify` regenerates the problem and checks every leaf
with `Fraction` arithmetic.  `ProfileCertificate.verify` recomputes the full
finite-clock payoff and cap.  Practical scale is severe: already
`epsilon = 1/10` uses `N = 961` and tens of thousands of probability
variables.  This affects feasibility, not mathematical termination.

The command-line interface exposes only `scale` and `verify`; it does not
currently expose `ScaleSearch.run`.  Thus the package is an executable Python
API and certificate checker, but not yet a convenient end-to-end search CLI.

## Required scope corrections

1. The phrase "terminating exact search" must be qualified as **terminating at
   each supplied accuracy**.  The induced whole-table process is productive:
   it halts with a lower certificate on the positive-gap side and otherwise
   runs forever while emitting increasingly accurate profiles.

2. For a supplied positive-minimum strict-inert object, eventual production
   of a lower certificate merely certifies the positive gap already implied by
   that hypothesis.  It does not contradict or consume the inert object.  The
   inert source is not encoded in either JSON certificate; saying it is
   "carried unchanged" can only mean external bookkeeping.

3. The result is generic in the reward table.  It does not encode the rigid
   inert constraints, prove their infeasibility, extract a compiler-ready dual,
   or find a qualifying table.  Therefore it does not answer
   `FIN4_INERT_MACHINE_CERTIFICATE_SEARCH.md` as currently gated.

4. It materially advances `ESCAPE_AWARE_FIN4_CERTIFICATE_SEARCH.md` by giving
   the previously missing complete per-query generator and an independently
   checkable certificate language, but it is not Lean-checked.  The remaining
   formal adapter is the equivalence of the substituted single-shell
   expression system with the checked finite-clock center plus interval-tree
   soundness/completeness.

## Strong corollary worth retaining

There is a complete semidecision procedure for a negative answer to Fin4.
Enumerate normalized rational Fin4 reward tables and all dyadic scales, and
dovetail their scale resolvers.  If any real normalized Fin4 table has
positive gap, the 2-Lipschitz dependence of exploitability on rewards gives a
nearby rational positive-gap table.  At a sufficiently fine scale its lower
search terminates, yielding an exact finite certificate.  Conversely every
emitted lower certificate is sound against all behavioral profiles.

Thus, if a Fin4 counterexample exists, this exhaustive process eventually
prints one with a certificate.  Nontermination does not prove UE.

## Files and declarations inspected

- `../rigid_fin4_exact_search/RIGID_FIN4_EXACT_SEARCH_THEOREM.md`
- `../rigid_fin4_exact_search/rigid_fin4_exact_search.py`
- `../rigid_fin4_exact_search/tests/test_exact_search.py`
- `Research/Quitting/EscapeAwareQuantileClockTransport.lean`
- `Research/Quitting/EscapeAwareQuantileClockHierarchy.lean`
- `Research/Quitting/FiniteClockPolynomialCenter.lean`
- `Research/Quitting/EscapeAwareQuantileClockPolynomialLower.lean`
- `questions/ESCAPE_AWARE_FIN4_CERTIFICATE_SEARCH.md`
- `questions/FIN4_INERT_MACHINE_CERTIFICATE_SEARCH.md`

