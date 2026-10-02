# Review of universal one-shot Nash outer-zero bound

Reviewer: CODEX_MINER

Source: [`notes/CODEX_EULER__UNIVERSAL_ONE_SHOT_NASH_OUTER_ZERO_BOUND.md`](../notes/CODEX_EULER__UNIVERSAL_ONE_SHOT_NASH_OUTER_ZERO_BOUND.md)

## Verdict

**PASS as ordinary mathematics.**  I attempted to falsify the theorem at
pure and mixed Nash boundaries, at zero and unit all-opponents-Never mass,
with positive and nonpositive singleton rewards, and against late/Never
deviations.  The universal `2R/3` unrestricted-debt bound and the Fin4
`L_M=0` conclusion through `M=36` are correct.

This is formalization-worthy and, in my view, suitable for a narrow export
packet after the required second independent unrestricted-strategy
falsification and whole-packet gate.  Its export value is not a conjecture
solution: it gives a new arbitrary-table actual-center producer and exactly
removes levels `M<=36` from the positive lower-certificate search in
[`questions/ESCAPE_AWARE_FIN4_CERTIFICATE_SEARCH.md`](../questions/ESCAPE_AWARE_FIN4_CERTIFICATE_SEARCH.md).

## 1. One-shot game and the all-Continue convention

For a fixed player `i`, write `S` for the opponents quitting at date zero.
The simultaneous game with continuation tail zero has the two action values

\[
 Q_i=\sum_S\pi_i(S)r_i(S\cup\{i\}),\qquad
 C_i=\sum_{S\ne\varnothing}\pi_i(S)r_i(S).
\]

The missing `S=empty` term in `C_i` is exactly zero, not an omitted quitting
reward: if everyone Continues at date zero in the literal date-zero/Never
profile, everyone then Never quits.  Thus the all-Continue dummy payoff used
by the root game agrees exactly with the terminal semantics of this profile.

The checked producer `exists_isZeroQuittingRootNash` in
`UniformEquilibrium/Quitting/Root/NashExistence.lean`, specialized to tail
zero, supplies the required product mixed Nash root.  If `p_i` is the
probability of Quit, Nash complementarity gives

\[
 U_i=p_iQ_i+(1-p_i)C_i=\max(Q_i,C_i).
\]

This remains exact at the boundaries: `p_i=0` implies `C_i>=Q_i`, and
`p_i=1` implies `Q_i>=C_i`.  No interior-support assumption is being used.

## 2. Audit of the unrestricted deviation cap

Against opponents who act only at date zero and Never, the deterministic
pure-time values really have exactly three forms:

* Quit at date zero: `Q_i`;
* Never: `C_i`;
* Quit at any finite date `t>=1`: `L_i=C_i+a_i s_i`, where
  `a_i=prod_(j!=i)(1-p_j)` and `s_i=r_i({i})`.

On every nonempty date-zero opponent event the game has already absorbed and
the late quitter receives the same term included in `C_i`; on the empty event
the late quitter receives the singleton reward.  Never instead receives zero
on that empty event.

The declaration
`sSup_range_quittingTerminalPayoff_update_eq_pureTime` in
`UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean` covers
arbitrary randomized history-dependent behavioral deviations.  Therefore

\[
 B_i=\max(Q_i,C_i,L_i),\qquad
 d_i=B_i-U_i=\max(0,L_i-U_i).
\]

This is the crucial unrestricted-strategy upgrade; it is not a bounded-time
or one-shot Nash assertion.

## 3. The two bounds and cancellation

If `s_i<=0`, then `L_i<=C_i<=U_i`, hence `d_i=0`.  If `s_i>0`, comparison
with Continue gives

\[
 d_i\le L_i-C_i=a_is_i\le a_iR.
\]

For comparison with immediate Quit, expand and cancel the empty-coalition
singleton term:

\[
 L_i-Q_i
 =\sum_{S\ne\varnothing}\pi_i(S)
   \bigl(r_i(S)-r_i(S\cup\{i\})\bigr)
 \le 2R(1-a_i).
\]

Since `U_i>=Q_i`, one may write the fully explicit safe step as

\[
 d_i=\max(0,L_i-U_i)
 \le\max(0,L_i-Q_i)
 \le2R(1-a_i).
\]

The last inequality uses `2R(1-a_i)>=0`.  Equivalently, split on `d_i=0`.
The source note compresses this harmless `max` step into one sentence; I do
not regard it as a gap, though it should be explicit in a Lean handoff.

Thus

\[
 d_i\le R\min\{a_i,2(1-a_i)\}\le {2R\over3}.
\]

The scalar maximum is attained at `a_i=2/3`.  The proof does not claim that a
single complete table simultaneously saturates this scalar estimate and all
Nash conditions.

## 4. Boundary falsification

* `a_i=0`: `L_i=C_i`, so `d_i=0`; the first bound alone is exact.
* `a_i=1`: all opponents Never.  Then `Q_i=L_i=s_i` and `C_i=0`.
  Nash choice of `i` makes `U_i=max(s_i,0)`, so again `d_i=0`.
* `s_i<=0`: late quitting cannot improve on Never, independently of whether
  `i` is pure or mixed in the root equilibrium.
* `R=0`: every terminal and dummy payoff is zero, and no division occurs.
* `|I|=1`: `a_i=1` and the preceding endpoint calculation applies.  In the
  hierarchy corollary the radius is zero, but the selected center is already
  diagonal, so the conclusion remains valid.
* Zero-probability coalition cells and Nash ties cause no change: every
  formula is polynomial/affine and uses no division by a mixing probability.

## 5. Hierarchy corollary

The date-zero/Never stopping law belongs literally to `A_1`, hence by support
monotonicity to every `A_(K_m)`.  If its semantic pair is `a=(U,B)`, define
the diagonal midpoint `z` coordinatewise by

\[
 z_{U_i}=z_{B_i}=(U_i+B_i)/2.
\]

Then the hierarchy objective is exactly zero and

\[
 \lVert z-a\rVert_\infty={1\over2}\max_i d_i\le R/3.
\]

For every `m<=M`, the radius `n(n-1)/m` is at least its value at `M`.
Consequently `R/3<=n(n-1)/M` puts this same `z` in every outer neighborhood
through `M`, and hence in `R_M`.  Nonnegativity of the objective proves
`L_M=0`.  For normalized Fin4 this is `1/3<=12/M`, exactly `M<=36`.

In checked vocabulary, the relevant support and metric facts are
`quittingFiniteClockSemanticReachable_mono`,
`dist_le_of_semanticPairWithin`, `quantileClockSupport`, and
`quantileClockRadius` in
`Research/Quitting/EscapeAwareQuantileClockHierarchy.lean`.  The current
checked lower-value declarations still take an explicit
`HasEscapeAwareQuantileClockCompression reward` argument; the exported
ordinary hierarchy proves that analytic input.  A Lean statement of the
corollary should either quantify over this argument or import its eventual
formalization explicitly.

The prototype command

```text
python3 experiments/fin4_quantile_center_prototype.py \
  dump-one-shot-universal --lambda-value 3/4
```

runs successfully and emits valid JSON.  Its `A_1` convention is date zero
plus the exact Never atom, agreeing with the theorem.

## 6. Novelty and export/formalization disposition

A narrow declaration/phrase search found no existing theorem with this
universal `2R/3` cap or the `M<=36` outer-zero consequence.
`exists_isZeroQuittingRootNash` supplies only the finite simultaneous Nash
root; pure-time extremality supplies only the cap reduction.  The cancellation
and uniform minimax bound combining them are new ordinary mathematics.

The useful formal theorem should be split narrowly:

1. existence of a tail-zero root whose one-shot-then-Never profile has every
   unrestricted terminal debt at most `2R/3`;
2. membership of its diagonal midpoint in the quantile outer intersection
   under `R/3<=n(n-1)/M`; and
3. the Fin4 corollary `escapeAwareQuantileClockLower ... M = 0` for
   `1<=M<=36`.

Because item 1 explicitly covers every behavioral deviation, the conference
rule calls for a second independent falsification review before export.
Subject to that review and a packet gate, I recommend narrow export and Lean
formalization.  The nonclaims in the source are correct: nothing here decides
`M=37`, proves `eta=0`, constructs a uniform payoff, or resolves the Fin4
hard residual.
