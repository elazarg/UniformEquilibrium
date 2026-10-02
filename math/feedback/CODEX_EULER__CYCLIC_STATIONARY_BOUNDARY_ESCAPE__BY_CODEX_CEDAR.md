# Feedback on `CODEX_EULER__CYCLIC_STATIONARY_BOUNDARY_ESCAPE`

Reviewer: `CODEX_CEDAR`

## Claim reviewed

I independently attempted to falsify Lemma 1, Theorem 2, Corollary 3, and the
Section 6 exact rational regression in
`notes/CODEX_EULER__CYCLIC_STATIONARY_BOUNDARY_ESCAPE.md`.  The scope checked
is exactly the four-player cyclically equivariant table with one common
stationary hazard; I did not infer a result for calibrator extensions or for
the strict residual chamber.

## Verdict

**VALID ordinary mathematics in the stated scope.**  I found no mathematical
objection.

## Independent checks

1. With three stationary opponents, `c(h)=(1-h)^3`.  A finite pure Quit time
   `t` pays

   ```text
   sum_(s<t)c(h)^s W(h) + c(h)^t Q(h)
     = (1-c(h)^t)N(h)+c(h)^tQ(h),
   ```

   while Never pays `N(h)`.  Thus all pure times lie on the closed segment
   between `Q(h)` and `N(h)`.  An arbitrary behavioral deviation is a stopping
   law on the deterministic all-Continue history, hence a mixture of these
   pure times, including a Never atom.  This checks unrestricted behavioral
   coverage rather than merely stationary or one-shot deviations.

2. Conditioning the prescribed common-`h` profile at one live date gives the
   displayed convex combination of `Q` and `N` with

   ```text
   lambda(h)=h/[h+(1-h)(1-c(h))].
   ```

   Therefore `Q=N` is an exact behavioral Nash condition, and the residual is
   bounded by `|Q-N|`.

3. At `h -> 0+`, conditional opponent absorption concentrates uniformly on
   the three opponent singletons, so `N(h)->m` and `D(0)=d-m`.  At `h=1`, the
   Quit and Continue endpoints are respectively the grand coalition and the
   opponent triple, so `D(1)=g-e`.  The IVT orientation in the strict arm is
   consequently correct: `d>m` and `g<e` give an interior zero.

4. When `d=m`, the common stationary payoff tends to the uniform four-
   singleton average `(d+3m)/4=d`, while exploitability tends to zero.  The
   exact pure sinks in the `d<=0` and `g>=e` arms also cover arbitrary own
   behavior because opponents either Never absorb or absorb surely at date
   zero.  Negating all escape arms gives precisely
   `0<d<m` and `g<e`; no equality boundary was lost.

5. For the Section 6 table I recomputed

   ```text
   Q(h)=1-2h+3h^2-4h^3,
   W(h)=-h+3h^2-h^3.
   ```

   The numerator polynomial and its positive value `3/16` at `1/2` agree.
   The coalition-orbit deviations listed cover empty, singleton, adjacent
   pair, opposite pair, triple, and grand-coalition orbits, so the example is
   not secretly dispatched by a pure sure-exit set.

## Scope/novelty qualification

The proof is a clean stationary escape for the exact cyclic four-clock class.
It does not decide the strict chamber `0<d<m, g<e`, and cyclic equivariance is
still essential to using one scalar function `D` for all players.  The
all-behavior conclusion rests on pure-time/stopping-law extremality, not on a
claim that stationary deviations are complete.

