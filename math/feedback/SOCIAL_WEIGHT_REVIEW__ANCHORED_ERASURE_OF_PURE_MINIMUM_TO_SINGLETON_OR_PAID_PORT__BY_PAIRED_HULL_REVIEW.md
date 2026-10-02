# Adversarial review of anchored erasure

Reviewer: `PAIRED_HULL_REVIEW`  
Date: 2026-08-31  
Verdict: **REVISE**

## Claim reviewed

The note claims that an actual pure finite-clock global minimum can be
reduced, by deleting all but one quitter at its first absorbing date, to
either:

1. a literal off-minimum sibling carrying an outgoing complete behavioral
   response of gain greater than \(D_*/4\); or
2. a literal singleton global minimum whose exact owner response either exits
   the minimum fibre or anchors a reset-rigid fixed-law chamber.

I checked the complete cap calculation under deletion, the orientation at the
first strict face exit, the singleton debt calculation, the response target's
incidence, and the law-tight re-anchor.  I also tried the boundary cases in
which the deleted player prefers the retained coalition, prefers the smaller
coalition, or is indifferent, and in which the singleton owner's selected
response is finite or Never.

The mathematical reduction is sound.  The revision verdict is for one real
interface/provenance overstatement and two smaller hypothesis/wording issues.
No counterexample to the core erasure argument was found.

## 1. The adjacent cap identity is exact

Suppose the current minimum sibling has first absorbing date \(t\), quitter
set \(S\), and the retained anchor \(b\in S\setminus\{p\}\) Quits surely at
\(t\).  Against the fixed opponents of \(p\), there is no opponent absorption
before \(t\), and \(b\) screens every history after \(t\).  Thus every pure
stopping time of \(p\) has one of only three values:

\[
 s_p=r_p(\{p\}),\qquad r_p(S),\qquad r_p(S\setminus\{p\}).
\]

Arbitrary behavioral randomization only convexifies these values.  The
minimum singleton margin gives

\[
 B_p-s_p\ge D_*>0,
\]

so \(s_p\) cannot maximize.  Therefore

\[
 B_p=\max\{r_p(S),r_p(S\setminus\{p\})\}.
\]

Changing only \(p\)'s prescribed strategy leaves \(B_p\) literally
unchanged.  Hence the better endpoint is a complete unrestricted behavioral
best response at the worse endpoint.  If the two rewards tie, both endpoints
are cap-attaining and the gain is zero in either direction.  Never and every
late stopping law are included because they are screened by \(b\)'s sure
Quit.

This calculation does require that “first stopping date with pure coalition
\(S\)” mean: no opponent has positive stopping probability before \(t\), the
players in \(S\) Quit surely at \(t\), and every player outside \(S\)
Continues surely there.  In the intended application this follows from the
reviewed pure-time/Never purification, but it should be made explicit in the
standalone result.

## 2. The first off-minimum split and its orientation are correct

Every erased sibling is an actual profile, hence carrier minimality gives
\(D\ge D_*\).  At the first strict sibling, the preceding sibling is a literal
global minimum.  The direction statements in the note are exact:

- if Continue has the larger endpoint value, the minimum-to-off-minimum edge
  is a best response;
- if Quit has the larger endpoint value, the reverse off-minimum-to-minimum
  edge is a best response;
- in the tie case the common face edge has zero gain in both directions.

The note does not falsely claim that the entire erasure list is a directed
chronology.  This is important and is handled correctly.

At the off-minimum sibling, a maximum-debt player has debt

\[
 d_h\ge D/4>D_*/4.
\]

For a finite-clock opponent profile, the complete cap is attained at a pure
finite time or Never, so replacing \(h\) gives the stated actual paid
behavioral edge.  In the intended post-purification application the profile
is pure-time/Never, and the checked pure-time first-disagreement decoder
applies literally.  If the theorem is instead stated for an arbitrary mixed
finite-clock input having only a pure first row, the paid-edge assertion
survives but the claimed single pure-time first-disagreement passport needs
the mixed-clock decomposition used in Proposition 9.3.  The clean repair is
to state the main input as a fully pure-time/Never profile.

## 3. The singleton endpoint and owner response are correct

If every erasure stays on the minimum fibre, the last profile terminates as
the singleton \(\{b\}\).  Hence \(U_b=s_b\), and the singleton margin plus
\(\sum_i d_i=D_*\) forces

\[
 d_b=D_*,\qquad d_i=0\quad(i\ne b).
\]

An exact pure-time or Never response of \(b\) gains exactly \(D_*\), leaves
\(B_b\) unchanged, and kills \(b\)'s debt.  If its target remains at total
debt \(D_*\), that target is an attained global-minimum joint-law point.

The incidence conclusion is valid, but “some opponent has a finite deadline”
is too deterministic for a mixed finite-clock formulation.  What is needed is
positive opponent finite stopping mass.  A profitable finite response cannot
absorb strictly before every opponent event, because that would give the old
singleton payoff.  If all opponents are literally Never, a profitable
response can only be Never and the target is the pure-Never law, which is
excluded by
`exists_positive_finiteLawAtom_of_finFourHardResidual_minimum`.

There is an even cleaner checked route: apply
`totalOpponentIncidence_pos_of_minimumLaw_of_debt_eq_zero` directly to the
equality target and its zero owner debt.  This avoids any ambiguity about
mixed finite deadlines.

## 4. Required repair: the reset-rigid re-anchor

The final paragraph conflates the fixed-law reset dispatch with the later
three-chamber classifier.  A `QuittingFixedLawResetDispatch` does not itself
have “full-debt” and “singleton/Never” chambers.  More importantly, the
checked reset-rigid theorem generally returns a **possibly different semantic
pair on the same literal law**.  It does not prove that its `returned` field is
definitionally the attained response target.

The desired result nevertheless follows by an explicit and source-faithful
re-anchor:

1. Let \(Z'=(z',\mu')\) be the literal equality response target.
2. Take `origin = minimum = point = Z'`.  The theorem
   `quittingLawTightCapNashSaturationHull_origin_mem` puts \(Z'\) in its own
   hull.  Since \(z'\) is a global minimum and the hull is a carrier subset,
   it supplies `IsQuittingLawTightCapNashSaturationMinimum`; the origin is in
   its own minimum face.
3. Use the literal singleton source pair before the owner response as the
   `source` argument.  It is a positive global minimum, so the checked source
   hypotheses hold and the dispatch retains the full killed-debt transfer.
   Using \(z'\) itself as `source` is also legal but weakens this transfer to a
   trivial zero-owner inequality.
4. Apply `exists_quittingLawTightResetRigidChamber` with owner \(b\),
   \(d_b(z')=0\), and the positive opponent incidence.

The chamber is therefore anchored at the exact attained target and retains
its exact law; its returned semantic pair may differ within that same-law
minimum face.  No unrelated minimum law or behavioral source is selected.

Accordingly, replace “reaches a same-target reset-rigid global minimum” by
something unambiguous such as:

> reaches an attained global-minimum target which, used as its own law-tight
> origin/minimum/point and retaining the literal singleton source, produces a
> reset-rigid chamber on the same target law.

The alternative three-chamber classifier is unnecessary here.  If it is
retained for exposition, the singleton/Never arm is excluded by positive
opponent incidence (or the Fin4 minimum-incidence theorem), not by referring
to chambers of the fixed-law dispatch.

## 5. Exact-root neutralization is sound

At any positive global minimum \(z'\), an exact cap--Nash root \(q\) gives

\[
 D(T_qz')=c(q)D_*.
\]

The prefixed point remains in the carrier, so global minimality gives
\(D_*\le c(q)D_*\).  Since \(0\le c(q)\le1\) and \(D_*>0\), one has
\(c(q)=1\), hence every player's product action is Continue surely.  Thus
all Continue is the unique exact root.  This is a semantic/root fact, not a
chronological use of an erased horizontal face.

## 6. Source attachment and finite abstract checks

Every erased profile is obtained from the supplied profile by one literal
date-\(t\) action change.  All earlier roots and the full post-\(t\) tail are
unchanged.  The first strict sibling and its preceding minimum are therefore
genuinely source-related.  The later maximum-debt response is launched from
that literal off-minimum profile.  No unrelated carrier realizer is used.

The two-player local face embedded in Fin4 gives a complete boundary test.
Fix the anchor \(b\), deleted player \(p\), and values
\(s_p<a=r_p(S)<c=r_p(S\setminus\{p\})\).  The cap is \(c\), so the deletion
is the correctly oriented response.  Reversing \(a<c\) reverses the edge;
setting \(a=c\) gives the asserted zero-gain tie.  Arbitrary changes to the
tail do not affect any of these values.  Thus there is no hidden fourth cap
endpoint.  Conversely, an abstract same-law minimum face can contain two
different cap vectors, showing why one may not identify the reset theorem's
returned pair with the literal target without an additional theorem.

## 7. Dependency and disposition

The entrance used in Section 6 is Proposition 9.3 of
`CODEX_SINGLETON_SOURCE__ONE_SURE_OWNER_EXACT_RESPONSE_HANDOFF.md`.  It has an
independent review marked PASS, with the bookkeeping clarification that the
strict arm consists of at most four purification edges followed by the paid
response edge.  Section 6 should cite that reviewed status and use the same
scope: literal finite-clock ancestry is retained, but an atlas-level marked
atom or prefix stack is not supplied automatically.

After the re-anchor wording is repaired, the pure-time/Never input is stated
explicitly, and “finite deadline” is replaced by positive finite stopping
mass (or the direct checked incidence theorem), I see no remaining
mathematical objection.  The result is a genuine contraction to two still
open components; it does not consume either the off-minimum paid port or the
reset-rigid chamber.

## Lean declarations inspected

- `minimumTerminalSemantic_singletonMargin` in
  `TerminalSemanticAuxiliaryNashBudget.lean`;
- `exists_positive_finiteLawAtom_of_finFourHardResidual_minimum` in
  `TerminalSemanticFinFourMinimumLawFiniteAtom.lean`;
- `totalOpponentIncidence_pos_of_minimumLaw_of_debt_eq_zero` in
  `TerminalSemanticFinFourMinimumOpponentIncidence.lean`;
- `quittingLawTightCapNashSaturationHull_origin_mem` and
  `quittingLawTightCapNashSaturationHull_subset_carrier` in
  `LawTightCapNashSaturationHull.lean`;
- `IsQuittingLawTightCapNashSaturationMinimum.minimum_mem_face` and
  `quittingLawTightCapNashSaturationMinimumFace_rootNash_iff_allContinue` in
  `LawTightCapNashMinimumFace.lean`;
- `QuittingTerminalExploitabilityWitness.exists_fixedLawResetDispatch` in
  `TerminalSemanticResetIncidenceCapReturn.lean`;
- `exists_quittingLawTightResetRigidChamber` in
  `LawTightCapNashStrictMinimum.lean`.

---

## Delta review: proposed elimination of the singleton arm

Date: 2026-08-31  
Verdict on the strengthening: **FAIL**

The revised note replaces the singleton response/reset branch by the claim
that the Fin4 hard residual supplies, for every singleton owner \(b\), a
distinct outsider \(c\) such that

\[
 r_c(\{b,c\})\ge r_c(\{b\})+\Gamma.
\tag{D.1}
\]

This is not a field of `FinFourQuantitativeFullSupportHardResidual`, and it
does not follow unconditionally from its terminal exploitability witness.
The exact checked statement is
`QuittingTerminalExploitabilityWitness.singleton_refusal_or_exists_collision_gain`:

\[
 \Gamma\le -r_b(\{b\})
 \quad\lor\quad
 \exists c\ne b,\quad
 r_c(\{b\})+\Gamma\le r_c(\{b,c\}).
\tag{D.2}
\]

The stronger theorem `exists_collision_gain` requires the extra hypothesis

\[
 -\Gamma<r_b(\{b\}).
\tag{D.3}
\]

Neither the singleton moat

\[
 B_b-r_b(\{b\})\ge D_*
\]

nor the equality \(d_b=D_*\) implies (D.3).  They constrain the difference
between the cap and the singleton payoff, not the absolute sign of the
singleton payoff.  All-player punishment normality also gives no such lower
bound.  For example, the local data

\[
 r_b(\{b\})=-\Gamma,
 \qquad
 r_c(\{b,c\})\le r_c(\{b\})\quad(c\ne b)
\]

are fully compatible with the singleton toggle requirement: the owner-leave
arm in (D.2) pays the terminal gap, while every outsider collision can be
nonprofitable.  This is an exact finite-table obstruction to the inference,
not a compactness issue.

If (D.1) were available, the rest of the new contradiction would be correct.
At the literal pure singleton profile, outsider \(c\)'s unilateral strategy
which Continues before \(t\) and Quits at \(t\) changes the sure terminal
coalition from \(\{b\}\) to \(\{b,c\}\).  Its whole-profile gain is exactly

\[
 r_c(\{b,c\})-r_c(\{b\})\ge\Gamma,
\]

because absorption is sure at that row under both strategies.  Hence its
complete debt at the singleton source would be positive, contradicting the
already proved \(d_c=0\).  No horizontal face would be misused as chronology
in that conditional argument.

The missing refusal arm cannot simply be substituted into the same proof.
The table-level refusal comparison is from the stationary pure singleton to
the empty coalition payoff zero.  In the supplied finite-clock profile,
after \(b\) Continues at date \(t\), later opponent clocks may terminate and
give a different payoff.  Thus the static refusal toggle need not be a
profitable unilateral response on the literal retained tail.  Even when all
opponents are Never, a profitable refusal only explains the singleton
owner's already positive debt; it does not contradict \(d_b=D_*\).

Therefore the unconditional conclusion

\[
 \text{fully pure-time/Never positive global minimum}
 \Longrightarrow
 \text{actual off-minimum paid port}
\]

is not proved by the revision.  The earlier reviewed conclusion—off-minimum
paid port **or** literal singleton minimum followed by its exact owner
response and the minimum/off-minimum reset split—remains the sound theorem.
The collision-only strengthening is valid after adding (D.3), but that
conditional version does not eliminate the general singleton arm.

Additional declarations inspected for this delta:

- `QuittingTerminalExploitabilityWitness.exists_collision_gain` and
  `singleton_refusal_or_exists_collision_gain` in
  `TerminalExploitabilityToggles.lean`;
- the fields of `FinFourQuantitativeFullSupportHardResidual` in
  `FullSupportProjectiveQBarResidual.lean`;
- the literal whole-profile collision identities in
  `ImmediateSingletonCollision.lean`.

### A different repair is available

The desired pure finite-clock conclusion can still be recovered without
asserting (D.1).  For a **canonical pure-time/Never** singleton minimum at
earliest date \(t\), let \(u>t\) be the next finite opponent deadline.  The
owner's unrestricted cap has only the values

\[
 s_b,\qquad r_b(A\cup\{b\}),\qquad r_b(A),
\]

corresponding respectively to stopping before \(u\), at \(u\), and after
\(u\)/Never.  The singleton moat removes the first value.  An exact response
can therefore be chosen as QuitAt \(u\) or Never.  If its target stays
minimum, it deletes the old earliest deadline \(t\) and introduces no new
deadline.  Iterating anchored erasure and this singleton response strictly
decreases the finite set of active deadlines.  The last response reaches
all Never, which cannot be a positive global minimum, so an off-minimum paid
exit occurs after finitely many rounds.

The complete proof and its exact scope are recorded separately in
`CODEX_SINGLETON_TIME_RANK__ANCHORED_ERASURE_AND_DEADLINE_DESCENT.md`.  It
requires independent review; it is not a repair of the collision paragraph
as currently written.
