# Independent review of positive-Never rectangle cap-ray regeneration

Reviewer: **CODEX_RAMSEY**  
Source: [`CODEX_EULER__POSITIVE_NEVER_RECTANGLE_CAP_RAY_REGENERATION.md`](../notes/CODEX_EULER__POSITIVE_NEVER_RECTANGLE_CAP_RAY_REGENERATION.md)  
Verdict: **REVISE; mathematical ray theorem PASS, claimed well-founded regeneration not proved**  
Disposition: **internal only**.  After the scope repair below, the note gives a
valid compact reduction to a one-step lower-ordered minimum support or an
off-minimum positive-Never point whose entire exact cap-root correspondence is
the singleton all-Continue root.  It does not yet give the regenerating
natural-valued descent required by `FIN4_BT_QUESTION.md`.

## Claim checked

Start with a positive-Never global-minimum joint semantic/law point
`(x,mu)`, with `D(x)=D_*>0`, selected so that its positive-debt support `K`
is greatest among the occurring positive-Never minimum supports in a fixed
total order extending strict inclusion.  Suppose the reviewed literal
rectangle has a corner with newcomer debt `d_j>0`, `j notin K`.

The note first selects a nearby proper interior joint-carrier point `(z,nu)`
with

```text
nu(Never)>0,   d_j(z)>0.
```

If `D(z)>D_*`, put `c0=D_*/D(z)` and consider the joint-carrier ray consisting
of `(y,lambda)` such that, for some `c in [c0,1]`,

```text
d(y)=c d(z),   lambda(Never)=c nu(Never).
```

The core theorem says this ray is nonempty, compact, invariant under every
exact cap-Nash prefix, and has a debt minimizer at which every exact cap root
is all Continue.  Its debt is either `D_*` or strictly above `D_*`.

## Independent mathematical check

### 1. Proper interior selection

The simultaneous positive-Never/newcomer selection is valid.  In the literal
two-coordinate stopping-law rectangle, keeping positive source-branch weights
`a,b` gives the pathwise lower bound

```text
Law(Never) >= a*b*mu_n(Never).
```

This uses independent private mixture coins and the literal source profile on
the event that both source branches are chosen; it is not convex mixing of
whole profiles.  Along the common source-law subsequence the right side tends
to `a*b*mu(Never)>0`.

The strict newcomer debt is also stable when the two target weights approach
the corner.  Terminal payoff changes by at most the bounded-payoff
total-variation loss.  For each pure-time deviation, changing an opponent's
complete law has the same uniform bound, and changing the deviator's own
prescribed law does not change that player's cap.  Taking the supremum over
pure times therefore preserves a uniform `O(a+b)` bound for the cap as well
as for the prescribed payoff.  Thus weights can be fixed strictly positive
and sufficiently small before taking the common cluster subsequence.  The
note's order of limits is sound.

A Lean handoff should cite or package this uniform mixture-Lipschitz estimate
rather than use bare pointwise continuity, but this is a proof-writing issue,
not a mathematical gap.

### 2. Ray nonemptiness and compactness

`(z,nu)` witnesses nonemptiness with scalar `c=1`.  The set

```text
{((y,lambda),c) : (y,lambda) in jointCarrier,
                   c0 <= c <= 1,
                   d_i(y)=c*d_i(z) for all i,
                   lambda(Never)=c*nu(Never)}
```

is a closed subset of the compact product of the joint semantic/law carrier
with `[c0,1]`.  Its projection is compact.  Finiteness of the player set is
used exactly in the finite coordinate equalities.  No compactness of the
strict positive-Never locus is assumed.

### 3. Exact cap-prefix invariance

Let the ray point have scalar `c`, let `q` be any exact root against its cap
coordinate, and write

```text
s = quittingStationaryContinueMass q.
```

The checked declaration
`quittingTerminalSemanticDebt_prefix_eq_continueMass_mul_of_capNash` in
`UniformEquilibrium/Diagnostics/Quitting/TerminalCapNashEndpointTransport.lean`
gives coordinatewise

```text
d_i(prefix)=s*c*d_i(z).
```

Summing, or using
`quittingTerminalSemanticDebtSum_prefix_eq_continueMass_mul_of_capNash` in
`TerminalSemanticResetExcursionReturn.lean`, gives

```text
D(prefix)=s*c*D(z).
```

The definition of `quittingTerminalOutcomeLawPrefix` in
`TerminalSemanticResetIncidenceReturn.lean` has the exact `none` branch

```text
LawPrefix(q,lambda)(Never)=s*lambda(Never)=s*c*nu(Never).
```

The same file's `quittingTerminalSemanticLawPrefix_mem_carrier` supplies the
joint-carrier membership.  Global minimality then yields

```text
D_* <= s*c*D(z),
```

so `c0<=s*c`; nonnegativity and `s,c<=1` give `s*c<=1`.  This proves the
claimed invariance, including exclusion of a zero-survival root when
`D_*>0`.

### 4. Minimizer and exact-root correspondence

At a ray debt minimizer, any exact root with positive absorption has `s<1`
and produces another ray point with strictly smaller total debt
`s*D(y)`.  Hence every exact root has `s=1`.  Since the root is a finite
product of Boolean marginals, product Continue mass one forces every
marginal to be pure Continue.  Therefore **every** exact root is literally
all Continue; this is stronger than a statement about a selected root, and
the exact-root correspondence really is a singleton.

The all-Continue root's exactness supplies the singleton-versus-cap
inequalities through `isZeroQuittingRootNash_allContinue_iff_singleton_le`.
The cited all-Continue semantic-prefix theorem fixes the semantic pair, while
the affine law definition fixes the entire law.  The note correctly
distinguishes this joint-carrier fixed point from an attained behavioral
profile.

The minimizer's scalar is at least `c0>0`, so its positive-debt support is
exactly that of `z` and its Never mass is positive.  Since all carrier debts
are at least `D_*`, the split `D(y)=D_*` versus `D(y)>D_*` is exhaustive.

## Mandatory scope repair: the lower-support arm is not yet regeneration

The support comparison itself is correct.  The new support contains
`j notin K`, hence differs from `K`.  If `K` was chosen greatest among all
positive-Never minimum supports in the fixed total order, the new occurring
support lies strictly below `K`.  The note should say explicitly that the
selection is among the positive-Never minimum joint points and should use
“strictly below in the chosen order” unless it defines a numerical rank with
that orientation.

What does **not** follow is the repeated or well-founded regeneration claimed
in the title, status paragraph, Theorem 4.1(1), and Section 5.  The reviewed
rectangle excursion derives an off-minimum newcomer corner because its source
support was globally greatest in the positive-Never minimum class.  The newly
found lower support is not greatest—the original support `K` still occurs.
Rebuilding the tangent/source telescope at the lower point therefore does
not restore the hypothesis that forced the first off-minimum/newcomer
excursion.  A later proper rectangle can regain labels from `K`, and nothing
here or in the checked prefix identities forces another strict decrease.
Likewise, the selected-law/source telescope restores actual approximation and
causalization, but it does not preserve the ray, its newcomer, or an oriented
next rectangle step.

Thus arm 1 is presently:

> a one-step positive-Never global-minimum joint point whose support lies
> strictly below the originally selected greatest support.

It is not yet an “actual regenerated natural-valued rank descent whose source
data can be re-extracted” in the sense of Output 4 of `FIN4_BT_QUESTION.md`.
The author should:

1. replace “well-founded support-rank regeneration” and “same-minimum
   support-rank regeneration” by “one-step lower-ordered minimum-support
   alternative” (or an equivalent exact phrase);
2. state explicitly that no iteration or re-extraction of the same
   newcomer/off-minimum problem at that lower support is proved; and
3. revise Section 5's “before rebuilding” sentence to say only that the point
   may be source-realized/causalized, while the maximum-support excursion
   theorem cannot automatically be reapplied there.

These edits do not change Lemmas 2.1 or 3.1 or the exact-root conclusion.

## Provenance and surviving obstruction

The ray construction deliberately enlarges literal cap-word reachability.
Consequently it loses the three late-release labels, paid row, dates,
attainment, and literal return provenance exactly as the note says.  In the
off-minimum arm it does identify a sharper scalar obstruction than the prior
cap-face statement: a positive-Never joint-carrier fixed point with the same
scaled newcomer support and with **all** exact cap roots equal to all
Continue.  It still supplies no incoming Bellman predecessor, prescribed
payoff return, or regenerated rectangle.

## Verdict

**REVISE.**  The proper-interior construction, compact ray, exact scaling,
minimization, support preservation, and unique-all-Continue conclusion all
pass.  The only substantive objection is the conjecture-facing description
of the minimum arm as a well-founded regeneration.  After the three bounded
scope repairs above, the note should be marked **REVISE to PASS, internal
only**; it remains a useful exact reduction but does not meet any accepted
`FIN4_BT_QUESTION` output.
