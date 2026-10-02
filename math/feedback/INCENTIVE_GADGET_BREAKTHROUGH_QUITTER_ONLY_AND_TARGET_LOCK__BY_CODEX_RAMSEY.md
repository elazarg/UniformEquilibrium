# Second independent falsification of the quitter-only / target-lock results

Reviewer: `CODEX_RAMSEY`

Source reviewed:
[`INCENTIVE_GADGET_BREAKTHROUGH_QUITTER_ONLY_AND_TARGET_LOCK.md`](../../INCENTIVE_GADGET_BREAKTHROUGH_QUITTER_ONLY_AND_TARGET_LOCK.md)

Detailed self-contained audit:
[`CODEX_RAMSEY__QUITTER_ONLY_TARGET_LOCK_AUDIT.md`](../notes/CODEX_RAMSEY__QUITTER_ONLY_TARGET_LOCK_AUDIT.md)

## Verdict

**REVISE -> PASS after five bounded statement/editorial repairs.**  I found no
mathematical counterexample.  Theorem 3.1, Theorem 4.1, the target-lock
theorem, the universal participant-only stationary all-behavior theorem, and
the `2 delta` perturbation corollary are valid with their displayed main
constants.

This is the second independent falsification of the unrestricted participant-
only class theorem.  Once the five repairs below are applied, the ordinary-
mathematics two-review requirement is satisfied; export would still require a
separate whole-packet gate.

## Required repairs

1. State the omitted hypotheses of (4.7): nonempty target `G` of size `m`,
   unchanged target-member indicator rewards, `R>=0`, cross penalty `-M`, and
   `M+R>0` (normally `M>0`).
2. Before Corollary 5.2 writes `r_i(G\{i})`, define the extended empty-row
   reward to be zero, or split off singleton `G`.
3. In the status summary, “arbitrary bounded completion on every row” must say
   arbitrary completion of the allowed **outsider coordinates**; the target
   coordinates are fixed by (3.1).
4. Delete the duplicated sentence following Definition 6.1.
5. Define

   ```text
   delta(r)=max({0} union {|r_i(S)| : S nonempty, i notin S})
   ```

   so the one-player/empty-index case is meaningful.

These repairs change no main theorem, proof, or constant.

## Falsification summary

For the integer table, outsider Never deviations give the exact incidence
bound `g/31`; the four-outsider union bound and the target-member payoff
identity give

```text
g>=31(1-a)/66>=31 ell/66.
```

The robust completion calculation gives

```text
p_d<=(2+epsilon)/32,
a>=3/4-17epsilon/8,
ell<=1/4+17epsilon/8.
```

The numerical specializations and the `ell^2>=4ab` consequence are exact.

At the pure target row, the member-leave and outsider-join comparisons are
exactly `IsQuittingSureExitSet`; the checked sure-exit characterization covers
all randomized and history-dependent deviations.  Thus the whole direct
cross-penalty completion class is locked.

For participant-only tables, a mixed Nash `q` of the one-shot binary game has
Continue payoff zero and Quit payoff `Q_i`.  Complementarity gives the three
boundary signs.  Stationary repetition has value `max(0,Q_i)` in every case:

- `rho=1`: all hazards zero and every `Q_i<=0`;
- `0<rho<1` without sure hazards: every active numerator vanishes;
- `rho=0`: complementarity gives the value coordinatewise; and
- a unique active/saturated coordinate is covered without assuming opponent
  contraction.

At a reached date the quit value remains `Q_i`; opponent absorption while the
player Continues pays zero, and Never pays zero.  Pure-time extremality (or the
stationary endpoint compiler including its saturated boundary) therefore
bounds every behavioral deviation by `max(0,Q_i)`.  The profile is exact
terminal Nash and supplies a uniform-equilibrium payoff.

Zeroing passive coordinates changes every prescribed or deviating terminal
payoff by at most `delta`, hence changes every unilateral gain by at most
`2delta`.  Corollary 7.1 follows.

## Source and novelty boundary

- `SureExitSet.lean` subsumes the strategic proof of target lock; the new
  content is its application to the entire robust completion class.
- `exists_heterogeneousStationaryFaceNash` can replace the finite one-shot
  Nash selection at lower hazard zero.
- `Stationary/BestResponse.lean` and `Stationary/EndpointCompiler.lean`
  already supply the pure-time/all-behavior and saturated-face machinery.
- I found no named checked declaration covering **every** participant-only
  reward table or the quantitative `2delta` passive perturbation.
- The no-harm singleton, acyclic solo, and odd-blocker compilers cover
  different classes and do not subsume arbitrary background-dependent signed
  participant rewards.

Thus the genuine new universal-class statement is the participant-only
architecture no-go, not finite Nash existence or stationary best-response
theory.  It is an accepted negative-answer form for
`questions/INCENTIVE_GADGET.md`, while the six-player table is only a sharp
one-pair/leftover partial producer and explicitly has the pure target
equilibrium.
