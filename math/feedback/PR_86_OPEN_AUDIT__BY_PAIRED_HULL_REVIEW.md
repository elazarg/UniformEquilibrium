# Open PR #86 mathematics and current-main overlap audit

Reviewer: PAIRED_HULL_REVIEW  
Date: 2026-08-31  
Recommendation: **close after salvaging the one-step record strengthening**

## Exact object audited

PR #86, `Expose canonical paid/reset successor data and Zeno boundary`, is a
draft from `research/paid-reset-canonical-zeno` at
`ca7470e6f97e92df9b967160efbd10739caae9cb`.  Relative to its merge base it
changes exactly two mathematical files:

- `Research/Quitting/PaidCapMaximalOneStepRegeneration.lean`; and
- the new `Research/Quitting/PaidResetCanonicalZenoRay.lean`.

There are four non-merge commits: the public one-step record strengthening,
the conditional ray package, its temporary umbrella import, and a final
temporary focused-build commit.

At this head, `Focused Lean` and the exact-source-artifact job passed.  The
ordinary CI job failed only because the new ray module was not reachable from
`Research.lean`; its documentation, unit tests, and experiment checks had
already passed.  Thus this current audit supersedes older feedback describing
Lean elaboration failures at an earlier PR head, but not the older
mathematical boundary analysis.

## Unique useful content

The genuinely useful nonduplicated change is the strengthening of
`MaximalOneStepPaidResetRegeneration`.  Every inhabitant, rather than merely
the theorem's chosen constructor, now exposes:

\[
\begin{aligned}
S^+.\mathrm{observer}&=S.\mathrm{observer},\\
S^+.\mathrm{gain}&=c(S)S.\mathrm{gain},\\
d_i(S^+)&=c(S)d_i(S)\quad(i\in I),\\
D(S^+)&=c(S)D(S),\\
c(S)I_{r,o}(S)&\le I_{r,o}(S^+),
\end{aligned}
\]

together with the two literal one-date shifts of the stored pure-time
witnesses.  Here \(c(S)\) is the joint all-Continue mass of the selected
maximum-absorption exact root, and \(I_{r,o}\) is the aggregate reset
incidence.  These are sound public-interface facts.  They prevent a later
consumer from replacing the canonical descendant by a record carrying an
arbitrarily weakened annotation.

The exact equality for `gain` concerns the deliberately conservative stored
certificate.  The physical shifted pure-time payoff difference is multiplied
by the observer-opponents' Continue mass, which can be strictly larger than
the joint Continue mass.  PR #86 uses the correct inequality when it rebuilds
the paid row.

This one-step record repair remains absent from current `main` at
`831e82aec87cf7b92e7767c8e3d3626abb27f626` and is worth reapplying in a
small current-main change.

## Content already present on current main

Most of `PaidResetCanonicalZenoRay.lean` wraps older checked maximal-prefix
mathematics which remains on current main:

- exact coordinate and total-debt product formulas;
- the positive global-minimum survival floor;
- invariance of positive-debt support and normalized debt;
- literal maximal-prefix profile realization; and
- summability and vanishing late tails of canonical absorption.

These are supplied by `MaximalCapSemanticPrefixOrbit.lean` and
`MaximalCapSemanticPrefixReturn.lean`, and are already used by the maintained
Fin4 maximal-prefix ray packages.  Current main has since added stronger
source-facing reductions, including the forced-pair ray dichotomy,
source-faithful paid-cycle renewal, positive-minimum two-cut splice, and the
response-rectangle maximal-root trichotomy.  None is literally the PR's
generic paid/reset record, but they make a second parallel conditional ray
wrapper poor integration value.

The PR ray's only additional bookkeeping beyond those generic scalar results
is the conservative paid-certificate product and inherited aggregate reset
incidence.  Those facts follow immediately once the strengthened one-step
record is available and can be added later at the actual consumer site.

## Unresolved mathematical gaps

`CanonicalMaximalPositiveRay` is an input structure.  Its fields already
contain an infinite coherent source sequence, a positive one-step
regeneration at every time, and literal successor equations.  PR #86 proves
no theorem producing that structure from an initial source and no exhaustive
finite-stop/infinite-ray theorem.

It also does not provide:

- a marked causal atom (aggregate incidence is not a selected coalition at a
  selected date);
- a source-matched chronological use of the fixed-law reset output;
- a positive late charge (the ray instead proves summable absorption);
- a finite rank, charged return, or terminal approximants; or
- a contradiction in the unique-all-Continue stopping branch.

The strengthened current-main rectangle and two-cut work does not repair
those omissions.  In particular, the recent maximal-root rectangle theorem
consumes a supplied common response rectangle; it does not turn this
conditional infinite maximal-prefix ray into an executable return.

## Mathematical disposition

The PR should not remain open as a current completion branch.  Its headline
ray theorem is conditional, mostly duplicated by maintained maximal-prefix
modules, and has no consumer.  Rebasing the whole draft would create a second
parallel API around a frontier now expressed through newer source-attached
objects.

The right disposition is:

1. transplant only the seven one-step public fields and their constructor
   proofs onto current main;
2. optionally add the division-free paid/incidence product lemmas at the
   first downstream use; and
3. close PR #86 rather than merge its stale conditional ray module.

This preserves all unique information.  Closing the PR loses no conjecture-
facing theorem: the PR never constructs or consumes its infinite ray.

