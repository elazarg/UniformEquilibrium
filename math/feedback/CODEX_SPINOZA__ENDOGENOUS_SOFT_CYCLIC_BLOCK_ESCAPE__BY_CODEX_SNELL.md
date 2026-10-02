# Review of `ENDOGENOUS_SOFT_CYCLIC_BLOCK_ESCAPE`

Reviewer: `CODEX_SNELL`

Reviewed authoritative frozen SHA-256:

```text
9c2680d1a4216f28ce74b20dddaa684991edcfdd43477fc781d097f39de224b0
```

## Verdict

**PASS with one declaration-citation correction.**  I found no mathematical
counterexample to the producer, the terminal cap estimate, or either escape
branch.  The fixed-payoff conclusion in Corollary 3.2 is valid, but the
source list names the target-free equivalence rather than the checked
fixed-target theorem which proves that the particular subsequential limit
`v` is a uniform-equilibrium payoff.  The correct declaration is
`quittingGame_isUniformEquilibriumPayoff_of_terminalNash_tendsto` in
`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`.
The named
`quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
would prove existence of some target only.

## Claim independently checked

For every finite period `H` and positive row tolerance `epsilon`, the note
produces strictly interior product roots and continuation values satisfying
exact cyclic Bellman equations and row Nash defect at most `epsilon`.
Repeating the word gives an actual almost-surely absorbing behavioral profile.
For player `i`, if `P_i` is the survival probability of all three opponents
through one period, its unrestricted terminal debt is at most

```text
H epsilon / (1-P_i).
```

Consequently a sequence for which these four ratios vanish produces the
fixed limiting uniform payoff.  Under a positive global terminal gap, a
subsequence has one fixed debtor whose three opponents' period absorption
vanishes.  It then splits into a singleton-dominant owner arm and a
vanishing-total-hazard arm.

## Independent proof audit

### Soft Brouwer producer

The map in (6) is a continuous self-map of the stated compact convex box.
For fixed opponents and continuation, the logit coordinate is strictly in
`(0,1)`.  At a fixed point, the two-action logit regret is at most
`theta log 2 = epsilon`; no regularized payoff is substituted into the game.
The Bellman coordinate remains in `[-M,M]` because it is a convex combination
of terminal rewards and the continuation coordinate.

Unrolling the exact phase equations once around the period gives
`v_0=a+P v_0`, where `P` is full joint survival.  Strict interiority gives
`P<1`, so infinite repetition absorbs almost surely and has terminal payoff
exactly `v_0`.  This verifies both the endogenous boundary and the claimed
actual-profile interpretation.

### Unrestricted deviation bound

Against fixed periodic opponents, the player's problem is a scalar optimal
stopping problem.  Pure-time extremality gives exactly

```text
W_t=max(Q_t,D_t+c_t W_(t+1)).
```

Writing `delta_t=W_t-v_t` and using
`C_t=D_t+c_t v_(t+1)`, the row defect yields

```text
delta_t <= epsilon+c_t delta_(t+1).
```

One full turn gives
`delta_0 <= H epsilon+P_i delta_0`.  Since every opponent root is strictly
interior, `P_i<1`.  This proves (9) and includes arbitrary late clocks and
Never; it is not merely a deviation bound for the displayed period.

As explicit low-period falsification tests, for `H=1` this reduces to
`delta <= epsilon+c delta`, and for `H=2` to
`delta_0 <= epsilon+c_0 epsilon+c_0c_1 delta_0`; both give the stated, slightly
coarse, bounds.  No phase-index or closure reversal appears.

### Fixed target and positive-gap escape

Under (12), the four unrestricted debts tend to zero.  After taking
`v_(n,0) -> v`, the checked fixed-target theorem cited in the verdict applies
directly to these actual terminal payoffs.  Thus the particular `v`, not only
an unnamed target, is obtained.

If some debt is at least `Gamma`, (9) forces
`1-P_i <= H epsilon/Gamma`; finite label stabilization and payoff-box
compactness give Theorem 4.1.  For fixed `H`, a product tending to one forces
every individual opponent factor to tend to one, so Corollary 4.2 is also
correct.  The note properly does not turn the isolated limit into a terminal
Nash profile.

### Two boundary arms

In the singleton arm, every within-period outcome other than singleton `i`
requires an opponent of `i` to Quit, hence has unnormalised probability at
most `A_i^-`.  Period absorption is at least the marginal event that owner
`i` Quits, namely `A_i^+ >= a`.  Repetition normalises the one-period outcome
law, giving convergence to `delta_{\{i\}}`.  For outsider `j`, its opponents
include `i`, so `A_j^- >= A_i^+`; (20) follows from (9).

In the other arm, owner and opponent period survival both tend to one.
Therefore full joint survival tends to one, and
`sum -log(1-x_(t,j)) -> 0`.  Since `-log(1-q) >= q`, (22) follows even when
the periods grow.  Nothing in this argument supplies the missing relative
scale (23), and the note does not claim it.

### Never boundary regression

The Section 6 example is valid.  Player `0` is indifferent between every
finite Quit time and the cyclic continuation value `-1`; each outsider gets
zero by Continue and `-1` by Quit.  Nevertheless player `0` obtains zero by
Never, so its terminal debt is one while `A_0^- = 0`.  This does not contradict
Theorem 3.1, whose soft roots make `A_i^- > 0`, and it correctly shows why total
absorption cannot replace player-deleted absorption in the denominator.

## Scope confirmed

The packet is an unconditional producer of approximate cyclic roots with
exact Bellman return.  Its terminal conclusion is conditional on the
charge-relative ratios (12).  Under a positive gap, the output is an
isolated-owner or vanishing-hazard boundary packet, not a paid port, an exact
root block, or a proof that either boundary is impossible.  Those
qualifications are accurately stated.

## Corrected frozen-byte delta

I also checked the corrected authoritative SHA-256

```text
3c95ea060c516d65243c114c4ecfe0c3a13aad571fedf9b6c12742771d646e73.
```

**Exact-hash PASS.**  The fixed-target paragraph now names
`quittingGame_isUniformEquilibriumPayoff_of_terminalNash_tendsto` and says
that the particular limit `v` is obtained, exactly resolving the citation
issue above.  The added moving-period singleton boundary test is correct:
with owner hazard `1/H` on each of `H>=2` phases,
`1-(1-1/H)^H>=1/2`; a tester who receives `Gamma` only on the tie coalition
has pure-time gain exactly
`(Gamma/H)(1-1/H)^n`, while Never and every non-tie outcome pay zero.
Pure-time extremality therefore bounds its unrestricted behavioral gain by
`Gamma/H`.  The table is punishment-normal and has an all-Never equilibrium,
so the stated limited scope is accurate.  I found no new claim or regression
in the delta beyond these two advertised repairs.

## Export-format candidate

I independently checked the repaired staged export candidate
`/tmp/ENDOGENOUS_SOFT_CYCLIC_BLOCK_ESCAPE.md` at SHA-256

```text
2e1e48709b65d08a694a08dd7835753620443a11a9a18b1651f2aacbc0b7fc38.
```

**Exact-hash standalone/delta PASS.** Relative to the reviewed theorem, the
candidate preserves the producer, cap recurrence (with `D_i` explicitly
defined), fixed-target conclusion, and both qualified escape arms. The
mandatory export sections and review links are present. Inline delimiters
balance `105/105`, display delimiters balance `23/23`, and the control-byte
scan is clean. The literal `(H\\)` search hits are all ordinary substrings
of correctly delimited `\\(H\\)` expressions, not malformed mathematics.
