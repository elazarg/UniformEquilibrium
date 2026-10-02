# Review of the persistent-pair and two-date zero-debt chambers

Reviewer: `CODEX_HOPF`

Reviewed note:
[`CODEX_RIEMANN__PERSISTENT_PAIR_CHAMBER_NO_GO.md`](../notes/CODEX_RIEMANN__PERSISTENT_PAIR_CHAMBER_NO_GO.md)

## Scope of this review

I reviewed the two exact chamber theorems in Sections 1 and 4, including their
claim to cover every unilateral behavioral deviation.  I also independently
recomputed the displayed persistent-pair witness's four crossing numbers, two
base stay gains, and equilibrium payoff.  I did not review the search program,
the pure-toggle enumeration, or the numerical candidate in Section 6.

## Verdict

Both zero-debt chamber theorems are correct.  They are genuine all-behavior
terminal-Nash constructions, not stationary-only screens.  Their common
reason is sure absorption before any off-path strategy can matter.

There is one presentation correction needed in the first worked table: the
printed bit strings are read with `f` as the least significant/rightmost bit.
Thus the visible left-to-right bit order is `(o,h,s,f)`, not `(f,s,h,o)` in
the ordinary string sense.  With that convention the arithmetic in
(11)--(14) is correct.  The theorem itself is unaffected.

## 1. Persistent-pair theorem

Let `B={f,s}` quit surely at date zero and let `h,o` independently Quit with
probabilities `y,z`.  Since at least two base players are prescribed to Quit,
absorption at date zero remains certain after every unilateral deviation.
Hence an arbitrary behavioral deviation reduces exactly to its date-zero
Quit probability.

For `h`, Quit minus Continue is

\[
 (1-z)a_0+za_1,
\]

and the stated value

\[
 z=-a_0/(a_1-a_0)
\]

makes it zero under `a_0<0<a_1`.  For `o`, the analogous expression is

\[
 (1-y)b_0+yb_1,
\]

and `y=b_0/(b_0-b_1)` makes it zero under `b_1<0<b_0`.
The two sure base players' Quit-minus-Continue differences are exactly
`G_f(y,z)` and `G_s(y,z)`.  Their nonnegativity therefore proves Nash against
the full behavioral deviation class.

The cited checked interfaces exist in
`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/`:

- `quittingPersistentBaseNashSet` in `PersistentBaseInducedGame.lean`;
- `nonempty_quittingPersistentBaseCertificate_of_inducedNash`; and
- `exists_uniformPayoff_of_persistentBase_inducedNash_signs`
  in `PersistentBaseNashSemanticAdapter.lean`.

The strict inequalities together with strict base stay gains define an open
semialgebraic chamber, as claimed.

### Worked-table arithmetic

Reading mask `0011` as `B={f,s}`, I obtain exactly

\[
 a_0=-1,
 \quad a_1=1/4,
 \quad b_0=1,
 \quad b_1=-1,
\]

and hence `y=1/2`, `z=4/5`.  Direct expectation over the four free-player
action profiles gives

\[
 G_f=7/10,
 \qquad G_s=9/10,
\]

and prescribed payoff

\[
 (3/5,1,1/5,-1/2).
\]

Thus the displayed table really is in the strict chamber.  If instead one
reads `1100` as `B={f,s}`, the displayed numbers do not result.  The note
should state the bit significance explicitly.

## 2. Ordered two-date chamber

Prescribe `j` to Quit at date zero, `k` to Quit at date one, and all other
players Never.

For any deviator `i != j`, player `j` still Quits surely at date zero.  The
deviator therefore has only two effective outcomes: Continue and receive
`r_i({j})`, or Quit at date zero and receive `r_i({i,j})`.  Inequality (18)
exhausts these deviations.

For deviator `j`, there are exactly three effective pure stopping outcomes:

- Quit at zero and receive `r_j({j})`;
- Continue once and Quit with `k` at date one, receiving `r_j({j,k})`; or
- let `k` preempt, receiving `r_j({k})`.

Every randomized, history-dependent, arbitrarily late, or Never deviation is
a convex combination or repetition of these outcomes.  Inequality (17)
therefore proves exact all-behavior Nash.

The strict version is again an open chamber.  No finite-horizon or stationary
completeness assumption is being used.

## Conjecture-facing assessment

The note correctly treats these theorems as no-go chambers for a local
negative search, not as progress toward a positive-gap example.  In
particular, a pure-toggle floor and even the retained inert passport do not
exclude exact behavioral equilibria.  The results are mathematically useful
provided the mask-order sentence is repaired and the unreviewed numerical
Section 6 remains outside any export claim.

