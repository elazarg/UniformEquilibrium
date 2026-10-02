# Independent review of the Gray four-clock stationary escape

**Reviewer:** CODEX_MINER  
**Target:**
[`CODEX_EULER__GRAY_FOUR_CLOCK_STATIONARY_ESCAPE.md`](../notes/CODEX_EULER__GRAY_FOUR_CLOCK_STATIONARY_ESCAPE.md)  
**Verdict:** **PASS.**  I found no mathematical, exact-arithmetic, probability,
or unrestricted-deviation defect.  The certificate proves one exact fully
mixed stationary terminal Nash profile in the displayed box; it correctly
does not claim global uniqueness or a theorem for other Gray tables.

## 1. Reward table and endpoint formulas

I reconstructed all nonzero coordinates directly from the Hamiltonian word.
For player `0`, the Quit rows containing `0` with value one are
`{0},{0,2},{0,1,2}`, while the Never rows with value one are
`{1},{1,3},{1,2,3}`.  This gives

```text
Q_0 numerator = 1+y_2+y_1*y_2,
N_0 numerator = y_1*(1+y_3+y_2*y_3).
```

The same enumeration gives, in player order,

```text
Q_1 numerator = y_0*(1+y_3),   N_1 numerator = y_3*(1+y_2),
Q_2 numerator = y_1,           N_2 numerator = y_0*y_3,
Q_3 numerator = -1+y_0*y_2+y_0*y_1*y_2,
N_3 numerator = y_2.
```

The denominators are respectively `P_i` and `P_i-1`, so (3.1) has the
correct orientations, including player `3`'s negative singleton term.

For stationary opponents, let `c_i` be their one-row all-Continue
probability.  Opponent absorption before date `t` has total mass `1-c_i^t`
and the same normalized first-coalition law as Never; conditional on survival
to `t`, Quit at `t` has value `Q_i`.  Hence

```text
V_i(t)=(1-c_i^t)N_i+c_i^t Q_i
      =N_i+c_i^t(Q_i-N_i),
```

which checks (3.2).

## 2. Independent exact certificate calculation

I independently evaluated the rational box with exact fraction interval
arithmetic.  I differentiated (4.8)--(4.9) by interval automatic
differentiation, formed `DG=I-A*DF`, and used the centered mean-value enclosure
for `G(X)-c`.  The resulting absolute derivative row-sum upper bounds were

```text
row 0: 1.519e-5
row 1: 2.279e-5
row 2: 3.337e-5
row 3: 2.668e-5,
```

all strictly below the outward bounds in (4.7).  The exact-center/mean-value
enclosures, in units of `10^-9`, were

```text
row 0: [-420.667,-420.636] subset [-421,-420]
row 1: [-479.693,-479.647] subset [-480,-479]
row 2: [ -35.853, -35.785] subset [ -36, -35]
row 3: [-156.445,-156.391] subset [-157,-156].
```

Thus (4.6) also has the correct outward orientations and lies strictly inside
the radius-`1000*10^-9` box.

Expanding the four-by-four determinant over the 24 permutations reproduced
exactly

```text
272216186882522042867946943189056919
----------------------------------------------------  > 0.
500000000000000000000000000000000000
```

No floating-point premise is needed for any of these checks; the decimals
above only display exact rational enclosures.

## 3. Fixed point and behavioral upgrade

The largest verified derivative row sum is below one, so `G` is a strict
sup-norm contraction on the closed box.  The image enclosure is internal.
Banach therefore gives a unique fixed point in this box.  At a fixed point,
`A*F=0`; the exact nonzero determinant gives `F=0`.

Every coordinate box is contained in `(0,1)`.  Therefore each prescribed
stationary strategy is a genuine geometric mixture of finite pure Quit times,
and all opponent absorption probabilities are positive.  When `Q_i=N_i`,
(3.2) makes every deterministic finite Quit time and Never have the same
payoff.  The checked declaration

```text
sSup_range_quittingTerminalPayoff_update_eq_pureTime
```

then upgrades the endpoint equality to the unrestricted behavioral cap, not
merely stationary deviations.  The prescribed geometric mixture has that
same payoff, so every coordinate has zero terminal debt.  Finally,

```text
quittingGame_isUniformEquilibriumPayoff_of_terminalNash_exact
```

has exactly the claimed uniform-payoff consequence.

## 4. Scope

The note correctly limits uniqueness to the isolating box.  The construction
is an exact solved table and not a hard-residual example: its stationary
terminal Nash profile rules out a positive ambient terminal gap and positive
global semantic minimum.  Consequently it does not challenge the paid-cap
double-port or minimum-fiber results.

