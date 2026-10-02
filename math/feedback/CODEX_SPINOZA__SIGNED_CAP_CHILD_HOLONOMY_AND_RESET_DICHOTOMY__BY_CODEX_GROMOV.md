# Review of signed cap-child holonomy

Reviewer: `CODEX_GROMOV`

Frozen input SHA-256:
`877e0d8b2253b10c74e74d1bb877461732dcd37c06c0f8e36a59924c5028044e`

## Verdict

**PASS.**  The affine displacement recurrence, finite-total-variation
conclusion, recursive cap-time dichotomy, and negative limiting displacement
in the infinite-reset arm are all correct.  The result is genuinely stronger
than compactness, but the note correctly stops before claiming a chronological
consumer.

## Exact recurrence and bounds

Let `A` be the barred root payoff with the old tail `U^n`, and `B` the payoff
conditional on the owner's root action being Quit.  Then

\[
 U_i^{n+1}=(1-h_{n,b})A+h_{n,b}B,
 \qquad
 W_i^{n+1}=A+\bar c_n\Delta_i^n.
\]

Their difference is exactly

\[
 \Delta_i^{n+1}=\bar c_n\Delta_i^n+h_{n,b}(A-B),
\]

and expanding `A-B` gives the displayed `G_(n,i)`.  With payoffs and rewards
in `[-M,M]`, `|G_(n,i)| <= 4M` is valid.  Hence

\[
 |\Delta_i^{n+1}-\Delta_i^n|
 \le 2M(1-\bar c_n)+4Mh_{n,b}.
\]

Both series on the right are summable, since
`1-bar c_n` is at most the sum of outsider hazards.  The finite-variation and
unrolled signed-limit formulas follow.

## Reset/shift classification

The sure owner deadline reduces every outsider response problem to finitely
many effective deadlines plus Never.  At a newly prefixed root an optimal
response may therefore be selected as either Quit now or Continue followed by
the previously selected cap.  Thus

\[
 T_{n+1,j}\in\{0,T_{n,j}+1\}
\]

is a coherent exact selection, including the permanent-Never case.  Finitely
many resets give an eventually shifted old cap; otherwise reset indices are
infinite.

## Negative holonomy

At a reset, Quit now attains the complete cap, so

\[
 d_j(\zeta^{n+1})=(1-h_{n,j})\bar E_n.
\]

The fixed debt floor yields `bar E_n >= delta`.  The old root gives
`E_old <= 0` because player `j` has positive Continue probability.  Direct
endpoint subtraction gives

\[
 \bar E_n-E_n^{old}=-\bar s_{n,j}\Delta_j^n+R_n.
\]

The stated `6M h_(n,b)` remainder is conservative: changing one Bernoulli
opponent costs at most `2M h` in each of the Quit and absorbing-Continue
terms, and at most `M h` in the continuation coefficient term.  Consequently

\[
 -\bar s_{n,j}\Delta_j^n\ge\delta-6Mh_{n,b}.
\]

Along infinitely many late resets, `h_(n,b) -> 0` and
`bar s_(n,j) -> 1`, so `Delta_j^n <= -delta/2` eventually on that subsequence.
Since the whole displacement sequence converges, its limit is at most
`-delta/2`.

## Scope

Finite total variation controls increments, not the sum of the displacement
values, and the nonzero negative limit is a macroscopic externality rather
than a return seam.  The barred roots remain unverified for outsider Nash
conditions.  Thus neither arm is yet an accepted Nash--Bellman chronology;
the note's nonclaims are correct.

The source-correspondence section points to the pre-repair SHA of the nested
child note.  Its mathematics is unchanged, but the current reviewed SHA is
`6d813418986400654a0c93fd8e54469b9d965fd61fdefee848cf7c9803c9e956`.
