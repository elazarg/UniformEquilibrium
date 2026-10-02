# Review of paid cap-lifted summable port

Reviewer: `CODEX_ROOT`

Contribution: external `ChatGPT` argument supplied by the user

## Claim reviewed

At a positive global minimum of total terminal semantic debt, start from the
actual receiving profile of a paid curvature witness.  Prefix exact roots
chosen against the literal profiles' behavioral caps, use those caps as the
punishment-floor Bellman annotations, and prove that the resulting literal
chronology has summable absorption, uniformly retains the paid suffix, and
converges to an exact all-Continue port.  Shift the original two pure-time
witnesses to obtain a fixed-gain paid row at every finite depth.

## Verdict

**PASS after two stated scope corrections.**

The construction removes the floor hypothesis from the previously formalized
`PaidRowExactPortAlternative`: the relevant exact relation lives on `B(x_n)`,
not on `U(x_n)`.  The proof is source-matched because the same roots prefix the
same actual receiving profile and generate both coordinates of its literal
semantic pair.

The result does not close the paid route.  It replaces the upstream floor
adapter by an unconditional marked summable port; consuming or restarting
that port remains open.

## Verification of the main steps

### Cap floor and exact policy

For every actual opponents' profile, the best-response envelope dominates the
behavioral punishment value by definition of the latter as an infimum over
opponent plans.  Thus `b_n=B(x_n)` is floor-safe without any claim about
`U(x_n)`.

The declaration
`quittingTerminalSemanticPrefix_envelope_eq_rootSuccessorPayoff_of_capNash`
proves exactly

```text
B(q ▷ x)=F(q,B(x))
```

when `q` is exact Nash against `B(x)`.  Together with literal semantic
prefixing, this validates the exact floor-orbit claim.  The finite version is
already packaged by `quittingMaximalCapPrefixPunishmentFloorPrefix`.

### Summability and uniform reach

The checked debt recursion gives `D_(n+1)=c_nD_n`.  Global minimality applies
because every `Sem(x_n)` is an actual carrier point.  Hence

```text
D* a_n <= D_n-D_(n+1).
```

The finite telescope proves summability.  Iterating the exact recursion also
gives `D_n=S_nD_0`; comparison with `D*` yields the stronger uniform reach
bound `S_n>=D*/D_0`.  In particular, no terminal-exploitability witness is
needed to exclude a sure-absorption outer root in this cap chronology.

### Shifted paid rows

For one outer root, a shifted pure-time deviation makes the observer Continue
at that root.  Its payoff has the form

```text
common outer reward + OppCont(q,o) * suffix payoff.
```

Subtracting two such deviations cancels the common term.  Induction over the
outer word yields the claimed product formula, including when either witness
is `Never`.  Dropping the observer's Continue factor shows opponent survival
is at least joint survival.  Therefore the shifted payoff gap is at least
`(D*/D_0)g`, and
`exists_quittingPaidFirstDisagreementRow_of_pureTimePayoff_sub` reconstructs
the exact shifted row.

This finite shift identity is the only substantive local lemma not already
found in the inspected maximal-cap development.

### Limit

The cap values and roots satisfy the hypotheses of the existing summable
all-Continue-port construction.  The honest prescribed coordinate follows
the same literal roots and converges using either its Bellman increment bound
or `u_n=b_n-d_n` with exact debt scaling.  Closedness of the terminal semantic
carrier gives the fixed semantic port.

## Required wording corrections

1. The limit port is a carrier/Bellman limit.  Every finite `x_n` literally
   contains `x_0` after `n` roots and reaches it with probability at least
   `D*/D_0`; one should not describe a limiting behavioral profile as running
   `x_0` after infinitely many dates.
2. The original curvature carrier's `source_approx` and `receiving_approx`
   remain immutable metadata at the original source and receiving profiles.
   The construction proves shifted paid rows at `x_n`, not shifted
   near-optimality at `x_n`.  Thus “complete paid witness persists” must mean
   retained provenance plus a new shifted row, not a new curvature witness at
   every depth.

Neither correction affects the marked-port theorem.

## Boundary checks

- The cap lift does not imply `punishmentValue<=U(x0)` and never uses it.
- Paid live mass is not identified with root absorption.  The valid comparison
  is deleted-player outer survival `>=` joint outer survival.
- A positive minimum is essential for a uniform reach floor.  At zero minimum,
  debt scaling alone permits the paid suffix's reach to vanish.
- The cap orbit is exact in the punishment-floor relation, but the paid row is
  behavioral data on the parallel literal profile.  No exact paid return edge
  is thereby produced.
- Maximal absorption is a canonical selection convenience; exact cap Nash is
  the property used in debt scaling and the Bellman identity.

## Source audit

The central cap-prefix, debt-budget, and finite-prefix declarations already
exist in `Research/Quitting/CausalTailEscapeMaxAbsorptionDispatch.lean`.  The
previous integrated `PaidRowExactPortAlternative.lean` uses prescribed values
and therefore retains an explicit floor hypothesis; it does not subsume this
cap lift.  A narrow search found no existing declaration for the shifted
pure-time paid-row transport or the infinite cap-orbit wrapper.

No unresolved mathematical objection remains within the corrected scope.

