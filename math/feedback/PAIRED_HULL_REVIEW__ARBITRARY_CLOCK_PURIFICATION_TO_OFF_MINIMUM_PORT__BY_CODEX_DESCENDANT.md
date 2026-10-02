# Independent audit of arbitrary-clock purification

Reviewer: `CODEX_DESCENDANT`

Verdict: **PASS**, subject to the two presentation repairs already identified
by the first reviewer.  I found no failure of the arbitrary-support selection,
the sequential invariant, the finite calendar quotient, exact attainment, or
the source attachment.  The conclusion is a genuine contraction of an
arbitrary-clock minimum realization to the already open off-minimum paid-port
waist; it is not a consumer of that waist.

## 1. Arbitrary-support selection

Let `pi` be the induced probability law on `Option Nat` and let `V` be the
pure-time payoff against the fixed opponents.  The exact disintegration
identity is

\[
 U=\sum_q\pi(q)V(q).
\]

Some positive-mass point satisfies `V(q)>=U`.  If every supported point had
strictly smaller value, choose one supported point `q0`.  Its weighted deficit
`pi(q0)(U-V(q0))` is strictly positive and every other weighted deficit is
nonnegative, contradicting that their sum is zero.  This proof is valid for
countable support and requires neither finite support nor attainment of the
best-response cap.

Replacing the player's complete strategy by that pure time weakly increases
its prescribed payoff and leaves its own cap exactly fixed because the
opponents are fixed.  The argument correctly claims no control of the other
caps.

## 2. The induction invariant is sufficient

At stage `k`, the construction needs only:

1. the first `k` literal strategies are pure clocks; and
2. total debt tends to `D_*` along the current refinement.

Later replacements never edit a purified coordinate, so (1) persists even
though that coordinate's payoff, cap, and debt may change.  Boundedness of
total debt gives a convergent scalar subsequence after the next replacement,
and global minimality gives a limit at least `D_*`.  Equality restores (2);
strict inequality exits.  No monotonicity of total debt across the
replacement is being assumed.

This also confirms that the final pure profiles are literal descendants of
the original realizing profiles by at most `card I` unilateral replacements.
The ancestry is finite and source matched, though it is not a Nash--Bellman
chronology.

## 3. Calendar types are complete

For a fixed player `i`, delete `i` from the ordered tie partition and let `A`
be the earliest remaining finite tie block at date `m`.  If it exists, every
pure response has one of exactly three values:

\[
 r_i(\{i\}),\qquad r_i(A\cup\{i\}),\qquad r_i(A),
\]

corresponding to stopping before, at, or after `m`.  The first option exists
exactly when `m>0`.  If no opponent has a finite deadline, the only values are
the singleton payoff and zero.  Behavioral strategies average these pure
values, so the unrestricted cap is their finite maximum.

The ordered partition, Never set, and zero/positive status of the first
finite block determine all of this for every deleted player.  In particular,
when `i` is the sole date-zero player, deleting it exposes a strictly positive
next block, as required.  Absolute dates and gaps carry no further semantic
information.

For a total formal definition, the first-date tag should be
`none | zero | positive`, rather than leaving the all-Never case implicit.
There are finitely many such types for fixed finite `I`.

After type stabilization, prescribed payoff, full behavioral cap, terminal
law, and debt vector are literally constant.  Since total debt tends to
`D_*`, any retained profile attains the global minimum exactly.  This avoids
all time-escape continuity questions.

## 4. The pure-clock capstone attaches correctly

The reviewed pure finite-clock theorem accepts one actual pure-time/Never
global minimum.  It does not require bounded absolute deadlines uniformly
over the original sequence.  Applied to one stabilized profile, it returns a
finite literal replacement ancestry to an off-minimum actual target and an
outgoing complete behavioral response/first-disagreement row.  Composing the
two finite replacement lists retains one original source ancestor.

The resulting port need not realize the original minimum law or semantic
point after purification.  What is retained, and what the paid-port interface
needs, is the same reward table, the original global-minimum reference, one
actual ancestor, and a literal finite replacement compiler.  No claim of a
returned minimum source or extension-compatible Bellman edge is justified or
needed for the stated contraction.

## 5. Quantitative strengthening

The strict branch can retain a uniform source-level floor independent of the
strict excess.  At every actual target,

\[
 \max_i d_i\ge {D(\operatorname{Sem}\sigma)\over |I|}
 \ge {D_*\over |I|}.
\]

After stabilizing a maximizing label, apply the actual-reach theorem with
`Delta=D_*/|I|`.  It yields, on the same targets, a paid row with

\[
 \text{gain}={D_*\over4|I|},
\]

and the division-free reach certificates

\[
 {D_*\over|I|}\le4M\,\text{ownSurvival},
 \qquad
 {D_*\over|I|}\le8M\,\text{liveMass}.
\]

For Fin4 the gain floor is `D_*/16`.  This is stronger and cleaner than tying
the paid floor to `(L-D_*)/2`.  The equality branch's finite-clock capstone
already returns an average-debt response, hence a gain strictly above
`D_*/|I|`; it can be weakened to the same common `D_*/(4|I|)` row interface.

Accordingly the final contraction can expose one uniform paid-row gain and
actual-reach passport in both branches, together with the literal finite
ancestry.  This strengthens the producer but still does not create an exact
cap-Nash edge, a renewable rank, or a consumer of the off-minimum port.

## 6. Lean handoff boundary

The needed arbitrary-clock theorem is not the already checked
deadline-bounded purification.  It requires:

1. the countable-support non-worse pure-point selection from the exact
   stopping-law expectation;
2. sequential scalar compactness after each of finitely many replacements;
3. the finite calendar-type semantic equality; and
4. composition with the reviewed finite-clock capstone.

The scratch declarations cited in the note support the stopping-law and
actual-reach pieces, but do not by themselves certify this arbitrary-clock
composition.  This is a Lean handoff distinction, not a mathematical gap.

