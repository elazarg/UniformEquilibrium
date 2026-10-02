# Review of Proposition 6W, Proposition 6X, and Corollary 6Y

Reviewer: `CODEX_EULER`

Verdict: **VALID ordinary mathematics in the stated prescribed-arm/reduction
scope.**

## Proposition 6W

The finite-splice identity is the direct disjoint partition into absorption
before the cutoff and survival through the whole word.  With a common tail,
the surviving contribution is
`(beta_P-beta_E)p_Y(C)r_o(C)` and does not cancel unless an additional reach or
tail condition holds.  Finite terminal-coalition mass is captured monotonically
as the cutoff tends to infinity; enlarging the clock cutoff preserves the raw
hazard lower bounds.

The contraction constants also check.  Joint survival is bounded by either
positive clock stream, and after deleting any player at least one of the two
distinct streams remains.  A hazard sum at least `kappa h` gives survival at
most `exp(-kappa h)<=1-kappa h/2` for `kappa h<=1`.  The terminal-semantic
prefix map is scalar in each prescribed coordinate with joint-survival
coefficient and scalar in each cap coordinate with the corresponding deleted
survival coefficient.  The standard residual-over-contraction-gap estimate
therefore gives (6W.6) for the literal periodic fixed point, including the
unrestricted behavioral cap.  If this bound alone must be `o(h)`, its numerator
must be `o(h^2)`; the note correctly presents this only as a sufficient rate
for that particular residual argument.

The rectangle qualification is necessary: a finite common pure-time witness
localizes terminal mass but does not localize the unrestricted endpoint cap
against an attached opponent tail.

## Proposition 6X

Let `beta_*=min(beta_P,beta_E)` and append mover Continue probabilities
`c_P=beta_*/beta_P`, `c_E=beta_*/beta_E`.  Both extended words then have joint
reach exactly `beta_*`, so every common-tail terminal contribution cancels.
The only new terminal at the balance row is `{m}`, proving (6X.2) for
`C!={m}`.

For `C={m}`, a distinct common helper with Continue probability `epsilon`
makes the two tail reaches `beta_* epsilon`.  The difference of the new
`{m}` masses is

```text
epsilon[beta_P(1-c_P)-beta_E(1-c_E)]
=epsilon(beta_P-beta_E),
```

which proves (6X.3).  The higher-reach word alone needs conditional mover-Quit
probability
`1-beta_*/max(beta_P,beta_E)=|beta_P-beta_E|/max(beta_P,beta_E)`, giving
(6X.4).  All rows other than mover `m` remain common (including the helper),
so the two extended complete laws still differ only in mover `m`; this is a
legal behavioral replacement.

Taking a sufficiently long cutoff captures a fixed fraction of the prescribed
atom and preserves the clock cutoff.  The helper pollution can be made smaller
than the remaining margin.  The note correctly disclaims the rectangle arm,
low repair cost, frozen-word membership, and source-fiber availability.

## Corollary 6Y

Finite-word joint survival decreases to the joint Never probability, so
`beta_P(L)-beta_E(L)->N_P-N_E`.  Along a rank subsequence with vanishing Never
mismatch, a diagonal choice of sufficiently large cutoffs can simultaneously
capture the atom, retain both hazard bounds, and make the common-tail leakage
vanish.  No balance row is then needed.

If the Never mismatch stays at least `nu`, enlarge every atom cutoff until the
finite reach mismatch is at least `nu/2`.  Any mover-only exact equalizer must
remove at least that much unconditional reach from the higher-survival word;
conditionally its added mover absorption is at least
`|beta_P-beta_E|/max(beta_P,beta_E)>=nu/2`.  The one-row construction attains
this lower bound.  A common-helper alternative suppressing arbitrary tail
mass likewise needs order-one helper absorption.

Finally, complete-law affineness gives exactly

```text
N_P-N_E=N_{-m}(1-a)(N_S-N_T)
```

for radial effective weight `a=hw`.  Hence small radial weight does not by
itself control the source/full-reset Never mismatch.  The stated escape cases
and the non-impossibility scope are accurate.

## Scope

These results isolate a sharp **prescribed-atom** renewal condition and its
survival-matching cost.  They do not renew rectangle endpoint debt, bound the
availability/fiber seam, or produce an actual-successor restart.  Proposition
6W's periodic word is an exact actual profile but is not shown to remain near
the selected frozen source or retain its atom.

