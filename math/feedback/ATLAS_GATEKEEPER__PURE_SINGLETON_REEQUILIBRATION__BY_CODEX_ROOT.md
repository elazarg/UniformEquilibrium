# Review of pure-singleton re-equilibration

Reviewer: `CODEX_ROOT`

## Claim reviewed

For an arbitrary literal tail `Z` and owner `j`, force `j` to Quit surely at
the current root and choose a mixed Nash equilibrium of the induced
three-player date-zero game for the outsiders.  Then every outsider has zero
unrestricted behavioral debt, while the owner's sole debt is its
Continue-cap value against `B_j(Z)` minus its Quit payoff.  Under a positive
global minimum `D_*`, compact minimization over outsider equilibria gives
either a minimum-fiber singleton-debt endpoint or a strictly off-minimum
one-active wall.  Hazard interpolation does not generally return toward the
minimum.

## Verdict

**The mathematical statement and the regression are valid.**  The note is a
useful exact reduction of a pure source-attached singleton endpoint.  It does
not consume the strict one-active wall, so I do not yet recommend export as a
completed atlas consumer.

## Verification

With `j` surely quitting, every outsider deviation still leaves absorption at
the current date.  The induced finite-game Nash inequalities therefore cover
all behavioral deviations, not just one-stage deviations.  This proves

\[
 d_i=0\qquad(i\ne j).
\]

If the outsider action is `A`, the owner's Quit value is

\[
 Q_j=\mathbb E r_j(\{j\}\cup A),
\]

whereas its Continue deviation absorbs on `A != empty` and, on `A=empty`,
exposes an arbitrary best response in `Z`.  The continuation term is therefore
`B_j(Z)`, not `U_j(Z)`.  Hence

\[
 D=[C_j-Q_j]_+.
\]

The constructed root-plus-tail profile is actual, so a positive global
minimum implies `D>=D_*>0`; the positive part disappears and all debt belongs
to `j`.

The outsider mixed-Nash set is a nonempty closed subset of a finite product
simplex and is compact.  The owner gap is continuous in the outsiders'
mixture.  Its minimum `G_j(Z)` is therefore attained and satisfies
`G_j(Z)>=D_*`.  Equality gives an actual minimum point with positive-debt
support exactly `{j}`.  Strict inequality gives the stated positive wall.

The regression also checks exactly.  With the note's table and owner hazard
`p`, the unique outsider equilibrium is all-Continue and

\[
 d_0(p)=1+p,
 \qquad d_1(p)=(1-p)\varepsilon,
 \qquad d_2(p)=d_3(p)=0,
\]

so

\[
 D(p)=1+\varepsilon+p(1-\varepsilon).
\]

For `0<epsilon<1` this is strictly increasing.  Thus continuity and even a
unique continuous outsider-equilibrium selection do not consume the strict
wall.  The regression's global minimum is zero, as the note explicitly says;
it is a local no-go, not a counterexample to the conjecture.

## Scope and remaining seam

The equality branch is a genuine support-rank consumer when the retained
minimum source has at least two debtors.  If it is already one-active, it only
re-enters that maintained boundary.  The strict branch supplies more than a
generic paid row—one actual source-matched profile with all debt on the owner
and a uniform off-minimum margin—but it supplies no exact return, regenerative
sequence, or floor-safe prefix operation.

A next result would have to consume

```text
source-attached one-active wall with gap > D_*
```

by producing an exact charged return or a regenerated minimum-fiber support
transition.  Merely varying the owner's hazard is ruled out by the displayed
regression.

## Minor issue

Equation (4) in the author note contains a stray control character in the
rendered `\bigl`; this is typographical only.
