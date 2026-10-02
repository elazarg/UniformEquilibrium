# Review of endogenous soft cyclic blocks

Reviewer: `CODEX_NEGATIVE_CERTIFICATE`

Reviewed note:
[`CODEX_SPINOZA__ENDOGENOUS_SOFT_CYCLIC_BLOCK_ESCAPE.md`](../notes/CODEX_SPINOZA__ENDOGENOUS_SOFT_CYCLIC_BLOCK_ESCAPE.md)

Reviewed SHA-256:
`3c95ea060c516d65243c114c4ecfe0c3a13aad571fedf9b6c12742771d646e73`.

## Verdict

**PASS.**  I found no mathematical, probability-mode, or unrestricted-
deviation error.  The unconditional soft-cycle producer, the
`H epsilon/(1-P_i)` terminal-debt estimate, the positive-gap isolated-owner
escape, the two boundary regimes, and both explicit regressions are correct at
the reviewed hash.  The result is a serious arbitrary-table producer, but its
stated singleton/diffuse boundary remains genuinely unconsumed; it does not by
itself prove the Fin4 conjecture.

## Claim audited

For every finite Fin4 quitting reward table, period `H>=1`, and positive row
error `epsilon`, the note produces an actual absorbing periodic behavioral
profile with exact cyclic Bellman values and rowwise two-action defect at most
`epsilon`.  If

```text
c_(t,i)=product_(j != i) (1-x_(t,j)),
P_i=product_(t<H) c_(t,i),
A_i^-=1-P_i,
```

then its complete unilateral terminal debt satisfies

```text
d_i <= H epsilon / A_i^-.
```

Under a hypothetical uniform terminal gap `Gamma>0`, a subsequence has one
fixed debtor whose opponents' absorption per period is at most
`H epsilon/Gamma`.  Depending on the selected owner's absorption, this yields
the singleton-dominant arm or the vanishing-total-hazard arm stated in the
note.

## Brouwer and logit audit

The map in (6) is a continuous self-map of the asserted compact convex box.
For fixed opponents and continuation, `F_i` is exactly the convex combination
of the Quit and Continue endpoints.  Those endpoints lie in `[-M,M]`, so the
value half of the map preserves the box.  The logit half is strictly in the
open unit interval.

For two numbers `Q,C`, the logit probability

```text
x=exp(Q/theta)/(exp(Q/theta)+exp(C/theta))
```

satisfies

```text
max(Q,C)-[x Q+(1-x) C] <= theta log 2.
```

Thus `theta=epsilon/log 2` gives exactly (5); no regularized payoff has been
substituted for the quitting payoff.  Brouwer simultaneously fixes all roots
and all cyclic successor values, so there is no false imposed zero boundary.

At the fixed point, the probability of all players Continuing through one
period is

```text
P=product_(t<H,i) (1-x_(t,i)) < 1.
```

Unrolling the exact Bellman identity gives `v_0=a+P v_0`.  Repeating the word
has survival `P^N -> 0`, and the same geometric unrolling identifies the
actual undiscounted terminal payoff with `v_0` (and likewise at every phase).
This checks the passage from an endogenous cyclic boundary to an actual
behavioral profile.

## Unrestricted cap audit

For a fixed player `i`, strict interiority of all three opponent coordinates
gives `P_i<1`.  Against the periodic opponents the complete stopping value is
the unique bounded solution of

```text
W_(t,i)=max(Q_(t,i), D_(t,i)+c_(t,i) W_(t+1,i)).
```

Here `D_(t,i)` is the absorbing contribution when `i` Continues, so the
prescribed Continue endpoint is `D_(t,i)+c_(t,i)v_(t+1,i)`.  This recursion
includes arbitrary cycle counts and Never.  It is also supported by the
checked behavioral pure-time equality
`sSup_range_quittingTerminalPayoff_update_eq_pureTime` in
`UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean` and the
periodic stopping development in
`UniformEquilibrium/Quitting/Cycles/PeriodicPureTimeBellman.lean`.

Since the prescribed behavioral strategy is one admissible unilateral
strategy, `delta_(t,i)=W_(t,i)-v_(t,i)>=0`.  The two endpoint bounds in (5)
give exactly

```text
delta_(t,i) <= epsilon+c_(t,i) delta_(t+1,i).
```

One cyclic iteration has at most `H epsilon` additive error and multiplier
`P_i`; division by `1-P_i=A_i^-` proves (9).  This is the correct
player-deleted denominator.  It is not a bounded-controller estimate.

The cited fixed-target consumer is also exact:
`quittingGame_isUniformEquilibriumPayoff_of_terminalNash_tendsto` in
`UniformEquilibrium/Quitting/Terminal/TargetTail/
TerminalUniformPayoffSelection.lean` takes terminal approximate Nash errors
tending to zero and convergence of the actual terminal payoff to one target.
Finite-dimensional compactness supplies the required subsequence of `v_(n,0)`;
no continuity of the choice of Brouwer fixed point is needed.

## Positive-gap and boundary-regime audit

If every actual profile has maximum terminal debt at least `Gamma`, choose a
debtor `i_n`.  Combining `Gamma<=d_(i_n)` with (9) gives

```text
A_(n,i_n)^- <= H_n epsilon_n/Gamma.
```

Fin4 pigeonhole stabilizes the label.  The playerwise bound (16) has the
correct orientation because each individual opponent survival product is at
least the joint opponent survival product.

For fixed `H`, compactness and `A_i^- -> 0` force every nonowner hazard at
every phase to zero.  This gives exactly an all-Continue limit or an isolated
owner word; it does not give terminal Nash because the deleted-owner survival
factor can equal one.  This matches
`isQuittingIsolatedWindow_iff_opponentSurvivalWeight_eq_one` in
`UniformEquilibrium/Quitting/Cycles/CycleIsolatedCoordinate.lean`.

In the singleton-dominant arm, every nonsingleton or wrong-singleton outcome
within a period requires an opponent of the owner to Quit, so its one-period
mass is at most `A_i^-`.  Total period absorption is at least `A_i^+>=a`.
Normalization under infinite repetition therefore makes the terminal
coalition law converge to the owner singleton.  For an outsider `j`, the
owner belongs to `j`'s opponent set, hence `A_j^- >= A_i^+`; (20) follows
from (9).

In the diffuse arm, joint period survival is
`(1-A_i^+)(1-A_i^-)->1`.  Since
`-log(1-q)>=q`, its negative logarithm bounds the sum of all phase hazards,
proving (22).  Nothing in this calculation supplies the missing relative
rate (23), exactly as the note says.

## Falsification attempts and explicit regressions

I tried to close the singleton arm directly from punishment normality.  The
reviewed moving-`H` example correctly blocks that inference.  With only owner
`i` using hazard `1/H` on every phase and reward
`r_j({i,j})=Gamma` as the sole nonzero coordinate, owner absorption per period
is

```text
1-(1-1/H)^H >= 1/2,
```

all players are punishment-normal, and the collision premium is exactly
`Gamma`.  Yet player `j`'s pure-time gain at absolute time `n` is exactly

```text
(Gamma/H)(1-1/H)^n <= Gamma/H.
```

Pure-time extremality extends the bound to every behavioral deviation.  The
qualification is essential and present: this table has the all-Never
equilibrium, so it refutes a direct static-premium argument, not the full
positive-gap hypothesis.

I also recomputed the moving-period Never regression.  The prescribed owner
gets `-1` from every finite Quit and from cyclic continuation; outsiders get
zero by Continue and `-1` by Quit.  Hence the displayed word is exact local
Nash--Bellman and absorbs surely, but the owner's Never deviation pays zero,
leaving debt one because `A_0^-=0`.  This confirms both the sign and the need
for the deleted-player denominator.

Diffuse/nonattainment does not break the proof: Brouwer is used separately for
each finite `(H,epsilon)`, while only the phase-zero payoff and the fixed
debtor label are compactified.  The note does not assume a limit of the full
moving-period word.

## Nonblocking clarifications

1. In (10), `D_i` is introduced only in the proof; defining it explicitly as
   the Continue absorbing contribution would make the source translation
   easier for a future formalizer.
2. The phrase `O(H epsilon)` in the escape discussion has the fixed hidden
   constant `1/Gamma`.  It is not uniform as `Gamma` varies.

Neither point changes the theorem or verdict.

