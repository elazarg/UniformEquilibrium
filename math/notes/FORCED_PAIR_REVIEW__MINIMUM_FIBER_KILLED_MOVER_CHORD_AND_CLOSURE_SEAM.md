# Minimum-fiber killed-mover chords and the exact closure seam

Author: `FORCED_PAIR_REVIEW`

## Status

There is a complete consumer for a **source-attached killed-mover chord** whose
source is maximum-supported in a minimum-fibre class closed under the chord.
It gives strict support descent and checked tangent-family re-extraction.

The canonical exact-prefix pure-pair source has exactly the missing
killed-mover property.  Thus this route is strictly stronger than the generic
`ThreeRoleLimitChord`, whose mover debt merely decreases.

The consumer is not presently renewable.  A marked endpoint update preserves
the literal prefix and tail, but generally destroys the fact that the old
prefix roots are exact cap--Nash roots for the new suffix.  If one enlarges the
compact class enough to contain the endpoint and its stopping-law chord, a
maximum-support point of that enlarged class need not itself be an exact-prefix
pure-pair source.  If one instead maximizes only among exact-prefix pure-pair
sources, the mixed chord point need not remain in the maximizing class.  Fresh
exactification returns precisely to the maintained maximal-prefix / normalized-
passport route and its unique-all-Continue inert branch.

So the minimum-fibre subarm has an exact one-step consumer, but no closed
iteration from the current fields.

## 1. Exact question

Fix a finite quitting table, a positive global minimum debt `D_*`, an actual
profile `P`, and a marked date `t`.  Assume:

1. the marked root is a pure nonempty coalition, in particular a pure pair;
2. the complete post-date tail is a retained actual tail;
3. every root strictly before `t` is an exact cap--Nash root against its
   actual successor semantic pair;
4. a player `m` has positive marked root-coordinate defect, and `P'` is the
   literal best-endpoint update of `m` at `t`; and
5. `Sem(P)` approaches or equals a point `X` on the minimum fibre.

What follows if `Sem(P')` also approaches a minimum-fibre point `Y`?  Can the
result be iterated inside a compact source-attached class?

All debts and caps below are terminal and quantify over unrestricted
behavioral deviations.

## 2. Exact prefix localization kills the mover

Let `L` be the probability of reaching the marked date.  At a pure pair, a
different sure quitter remains after either endpoint action of `m`.  Hence
the current-suffix debt of `m` is exactly its marked coordinate Nash defect
`delta_m`; the continuation debt is screened off.  This is the content of
`quittingTerminalSemanticDebt_prefix_eq_coordinateNashDefect_of_other_sureQuitter`
in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticReachedRowDebtLocalization.lean`.

Every exact cap--Nash prefix above that row scales every debt coordinate by
its joint Continue mass.  Iterating
`quittingTerminalSemanticDebt_prefix_eq_continueMass_mul_of_capNash` therefore
gives

\[
                     d_m(P)=L\,\delta_m.                 \tag{1}
\]

The checked literal endpoint identity
`quittingLiteralSameStage_bestEndpoint_gain_and_debt` in
`Research/Quitting/SameStageEndpointMonodromy.lean` gives

\[
 U_m(P')-U_m(P)=L\,\delta_m,
 \qquad d_m(P')=d_m(P)-L\,\delta_m.                     \tag{2}
\]

Combining (1)--(2),

\[
                         \boxed{d_m(P')=0.}              \tag{3}
\]

This is the substantive distinction from
`ConcentratedCollisionFourRole.ThreeRoleLimitChord`: that structure stores
only

\[
 d_m(Y)\le d_m(X)-c,
\]

and permits `d_m(Y)>0`.  The full-support circulation countermodel in
`ATLAS_GATEKEEPER__THREE_ROLE_LIMIT_CHORD_NONCAPSTONE.md` therefore applies to
the generic chord but not to (3).

## 3. Maximum-support minimum-fibre consumer

Let `C` be a class of source-attached joint semantic/law points satisfying:

* every member projects to the terminal-semantic carrier;
* `C` contains the source `X` and target `Y`;
* whenever it contains the two endpoints of this one-player stopping-law
  update, it contains every stopping-law mixture between them; and
* `X` has maximum positive-debt-support cardinality among the members of `C`
  whose total debt is `D_*`.

Assume

\[
 D(X)=D(Y)=D_*,\qquad d_m(X)>0,\qquad d_m(Y)=0.          \tag{4}
\]

For `0<s<1`, mix only `m`'s complete stopping laws at every actual
approximating index.  The complete terminal law is exactly affine by
`quittingTerminalOutcomeMass_stoppingLawMixture_eq`, prescribed payoff is
affine, and debt is coordinatewise convex.  Global minimality and the equality
of the two endpoint totals force every convexity gap to vanish.  The joint
limit `Z_s` therefore satisfies

\[
 d_i(Z_s)=(1-s)d_i(X)+s d_i(Y)                           \tag{5}
\]

for every player, while its terminal law is the same affine combination of
the endpoint laws.  Nonnegativity gives the exact lattice identities

\[
 \operatorname{supp}_+d(Z_s)
  =\operatorname{supp}_+d(X)\cup\operatorname{supp}_+d(Y),              \tag{6}
\]

and, for the positive coordinates of the displayed terminal law,

\[
 \operatorname{supp}\mu_{Z_s}
  =\operatorname{supp}\mu_X\cup\operatorname{supp}\mu_Y.               \tag{7}
\]

Because `Z_s` is a minimum point in `C`, maximum support at `X` and (6)
imply

\[
 \operatorname{supp}_+d(Y)\subseteq\operatorname{supp}_+d(X).
\]

Equation (4) makes this strict:

\[
 \boxed{\operatorname{supp}_+d(Y)
        \subsetneq\operatorname{supp}_+d(X).}            \tag{8}
\]

This is the reviewed maximum-support common-chord argument of
`CODEX_EULER__MAXIMUM_SUPPORT_COMMON_CHORD_EXCHANGE_COLLAPSE.md`, now with
the killed-mover premise supplied by the exact-prefix pure-pair calculation.

If `X` is the base of a positive-minimum tangent family, (8) supplies the
support-subset and vanished-old-coordinate hypotheses of
`exists_reextracted_of_minimumFiber_of_supportSubset_of_vanished` in
`PositiveMinimumDebtTangentFamily.lean`.  Thus a new tangent family based at
`Y` has strictly smaller positive-debt support.  More generally, carrier
membership, minimum-fibre equality, and positivity alone already let
`exists_positiveMinimumDebtTangentFamily_of_pair` construct a fresh family at
`Y`; the actualizing endpoint sequence is not itself the tangent family.

## 4. Exact support alternative without maximum support

Write

\[
 A=\operatorname{supp}_+d(X),\qquad B=\operatorname{supp}_+d(Y).
\]

The strongest unconditional finite alternative from (3)--(6) is:

1. `B proper-subset A`, giving the checked rank handoff;
2. `B \ A` is nonempty, in which case every proper interior chord point has
   support `A union B`, strictly larger than `A`; or
3. `A=B`, in which case the killed mover premise rules this case out.

Thus **with a killed mover**, a newcomer is the only obstruction to strict
support descent, and maximum support removes it.  By contrast, for the
generic `ThreeRoleLimitChord`, case 3 survives because the mover can remain
positive; this is the exact equal-support debt-circulation arm.

The whole-law refinement (7) supplies no additional orientation.  Taking the
same full-support terminal law at both endpoints makes the law support
constant while the debt exchange occurs.  Hence a rank formed only from debt
support and law support cannot consume the generic equal-support chord.

## 5. Literal source attachment survives; exact source status does not

For a one-date corner update of a pure pair:

* all roots before the marked date are literally unchanged;
* the probability of reaching the marked date is unchanged;
* the routed nonempty coalition receives the same reached mass;
* all live roots strictly after the marked date are literally unchanged; and
* the source, target, and their one-player mixtures are actual profiles with
  one common prefix and post-date tail.

The stopping-law mixture also preserves those off-date live roots.  Before
the mark the endpoint strategies agree.  At the mark they differ by the pure
endpoint action.  After the mark, only the endpoint component that survives
the mark contributes, and its formal tail is the common stored tail.

But an earlier root `q` being exact cap--Nash is a statement about the cap of
its **current successor**.  The marked corner update changes that successor's
semantic pair.  Therefore the unchanged earlier root need not be exact for
the target or midpoint.  What survives is literal prefix provenance, not the
exact-prefix certificate that proved (1).

This gives the closure incompatibility:

* Let `C_exact` contain only exact-prefix pure-pair sources.  Its source points
  satisfy (1), but the target and mixed chord points need not belong to
  `C_exact`; maximum support there cannot exclude a newcomer by (6).
* Enlarge to a compact corner- and mixture-closed class `C_cube`.  The chord
  stays in `C_cube`, but a maximum-support minimum point of `C_cube` need not
  be a pure-pair source with an exact incoming stack.  At that maximizer,
  (1)--(3) cannot be invoked.

The active paid passport has the same problem.  At the best endpoint, the
selected mover's marked defect is zero, and the routed coalition label may
change.  A class retaining a fixed positive current-gain density is not
endpoint-closed.  A class retaining only historical gain and marked live
mass is endpoint-closed, but its maximizer need not possess a fresh active
endpoint operation.

## 6. Why fresh exactification returns to the maintained inert branch

One can restore exact prefix status above the modified marked suffix by
selecting fresh exact cap--Nash roots.  This preserves the causal suffix only
through the new roots' survival factors and obeys the exact debt scaling law.
It is precisely the maximal-prefix architecture already isolated in:

* `FORCED_PAIR_REVIEW__MAXIMAL_PREFIX_RAY_DICHOTOMY.md`; and
* `FORCED_PAIR_REVIEW__NORMALIZED_PASSPORT_MINIMIZER_ELIMINATES_SUPPORT_ENTRY.md`.

The normalized-passport minimizer eliminates a positive-absorption
support-entry restart: it would strictly lower the normalized slice debt.
Its surviving point is an off-minimum decorated minimizer at which every
exact cap root has zero absorption, equivalently the unique product root is
all-Continue.  Re-exactifying the killed-mover target therefore does not
complete the consumer; it returns to that exact inert branch.

## 7. Relation to maximum-support source selection

At table level one may choose a globally maximum-support point on the compact
positive minimum fibre, lift it to a joint semantic/law point using
`exists_terminalSemanticLawCarrier_lift`, and causalize a finite atom at that
same point using
`finFourHardResidual_minimumLaw_causalSuffixAtom`.  This is a valid source
selection improvement.

It does not by itself make every later pure-pair whole source maximum-
supported.  A pure-pair/cross-tail construction can return to a different
minimum point.  If that returned source has strictly smaller support
cardinality, one has a one-step rank drop; if it has the same (globally
maximal) cardinality, the killed-mover chord consumer above applies.  After a
drop, however, global maximum support still exists elsewhere, so this
selection argument is not automatically renewable at the child.

## 8. Off-minimum endpoint

If the killed-mover endpoint has

\[
                         D(Y)>D_*,                      \tag{9}
\]

the actual endpoint sequence is sufficient to invoke, at every index, the
checked terminal-gap construction
`HasTerminalExploitabilityGap.nonempty_actualProfilePaidCapPort`.  The charged
near-return arm is incompatible with the same exploitability witness, leaving
quantitative debt descent or an inert stall.

This does not close (9).  A global best-response replacement can destroy the
old pair atom, marked tail, recipient label, and exact-prefix certificates.
The fresh terminal-witness paid row is source-matched to the new endpoint but
does not recreate those decorations.  Thus replacing the marked endpoint by
an arbitrary global best response reduces the minimum arm to support descent,
but sends the off-minimum arm to the **generic** paid-cap descent/inert route,
which is weaker than the retained forced-pair normalized passport.

Using the literal marked endpoint avoids that provenance loss and gives (3)
under exact prefixes, but fresh exactification is still needed afterward and
again reaches the inert branch described in section 6.

## 9. Verdict

The maximum honest theorem is

\[
\boxed{
\begin{array}{c}
\text{maximum-supported minimum exact-prefix pure-pair source}\\
+\ \text{minimum-fibre marked best-endpoint target}
\end{array}
\Longrightarrow
\text{strict support descent and tangent-family re-extraction}.}
\]

It genuinely bypasses the generic `ThreeRoleLimitChord` in this equality
arm because the mover is killed rather than merely decreased.

What is not proved is a compact invariant class whose selected maximizer both
retains exact-prefix pure-pair status and is closed under the endpoint chord.
The missing operation is exactly a **source-attached re-exactification that
retains the support orientation**, or a consumer of the resulting unique-all-
Continue inert point.

## Sources inspected

* `ConcentratedCollisionFourRole.ThreeRoleLimitChord` and its producer in
  `Research/Quitting/ConcentratedCollisionFourRoleMonodromy.lean`;
* `quittingLiteralSameStage_bestEndpoint_gain_and_debt` in
  `Research/Quitting/SameStageEndpointMonodromy.lean`;
* `quittingTerminalSemanticDebt_prefix_eq_coordinateNashDefect_of_other_sureQuitter`
  in `TerminalSemanticReachedRowDebtLocalization.lean`;
* exact cap-prefix debt scaling in `TerminalCapNashEndpointTransport.lean`;
* stopping-law law/debt convexity and minimum-fibre affinity in
  `TerminalSemanticStoppingLawDebtConvexity.lean` and
  `TerminalSemanticStoppingLawMinimumFiberAffine.lean`;
* tangent-family extraction and re-extraction in
  `PositiveMinimumDebtTangentFamily.lean`;
* the independently reviewed
  `CODEX_EULER__MAXIMUM_SUPPORT_COMMON_CHORD_EXCHANGE_COLLAPSE.md`; and
* `ATLAS_GATEKEEPER__THREE_ROLE_LIMIT_CHORD_NONCAPSTONE.md`.

