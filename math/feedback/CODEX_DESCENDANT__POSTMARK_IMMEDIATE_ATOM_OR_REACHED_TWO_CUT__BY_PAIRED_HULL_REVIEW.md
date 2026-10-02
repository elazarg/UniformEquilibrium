# Strengthening and export review of the postmark atom/two-cut producer

Reviewer: `PAIRED_HULL_REVIEW`  
Date: 2026-08-31  
Verdict: **PASS as mathematics; REVISE before export**

## Claim checked

The note starts with one actual Fin4 family \(s_n\) whose joint
terminal-semantic/law points converge to a positive global minimum and fixes
one nonempty terminal coalition \(A\) of limiting mass \(\mu>0\).  It proves
the exhaustive same-family alternative

1. a uniform \(A\)-atom at date zero; or
2. uniform reach to date one followed by a finite block of uniformly positive
   total marginal Quit hazard.

It then instantiates the checked positive-minimum two-cut theorem, using one
silent all-Continue padding row in the immediate arm.

I checked the probability identities, all constants, the padding
construction, the unrestricted-response splice, the source boundary, the
existing earlier producer, and the export criteria.  The stated theorem is
correct.  It should be strengthened and repackaged before export because a
strictly simpler argument gives a stronger source adapter, and because the
current note does not yet name the atlas-level actual-data adapter required by
the export gate.

## 1. The stated atom dichotomy is correct

Coordinate convergence of the finite terminal laws gives, eventually,

\[
  \nu_n(A)=\sum_{t\geq 0}w_{n,t}(A)>\frac{3\mu}{4}.
\]

If \(w_{n,0}(A)\geq\mu/8\) cofinally, the immediate subsequence exists.
Otherwise this inequality fails eventually and

\[
  \sum_{t\geq1}w_{n,t}(A)>\frac{5\mu}{8}.
\]

Finite truncation supplies \(e_n>1\) with mass greater than \(\mu/2\) on
\(1\leq t<e_n\).  Every such event survives date zero, so the date-one reach
is greater than \(5\mu/8\).  At each date,

\[
 w_{n,t}(A)
 \leq \Pr_{q_{n,t}}(\text{absorption})
 \leq \sum_{i<4}q_{n,t,i}(Q),
\]

where the first inequality discards the live-mass factor.  Summation proves
the advertised hazard floor.  No source rank, sibling profile, or law is
reselected.

The one-row padding in the immediate arm is also valid.  With the padded
roots

\[
  (\mathbf C,q_{n,0},q_{n,1},\ldots),
\]

take `markedRow = 0`, `entryCut = 1`, and `exitCut = 2`.  The entry suffix is
exactly the canonical live-root realization of \(s_n\), its absolute reach is
one, and its exit suffix is the original date-one suffix.  A strategy update
which begins at the entry cut has exactly the same payoff difference as its
counterpart in \(s_n\).

One subtlety is already handled correctly in the note: the silent prescribed
padding row need not preserve the whole unrestricted cap of the parent,
because a deviator may Quit during that row.  The checked theorem does not
require the padded parent to be near the minimum; its entry pair is \(Z(s_n)\).

## 2. The checked two-cut constants are correct

For a branch hazard floor \(\chi_a\), set

\[
 K_a=(1-e^{-\chi_a})D_*,\qquad
 \delta_a=\frac{e^{\chi_a}-1}{2}D_*.
\]

The production theorem gives either exit debt at least
\(D_*+\delta_a\), or one entry coordinate of debt greater than \(K_a/8\).
With response tolerance \(K_a/16\), the conditional entry gain is greater
than \(K_a/16\) and the updated **entry-suffix** payer debt is at most
\(K_a/16\).  Multiplication by the absolute entry reach gives exactly the
whole-parent floors in the note:

\[
  K_0/16\quad\text{and}\quad \mu K_1/32.
\]

Because only the payer's complete strategy changes, its unrestricted cap
against the fixed opponents is unchanged, so this whole-parent payoff gain is
also its exact whole-parent debt decrease.  No analogous claim is made for
the other coordinates.

## 3. Stronger universal silent-padding theorem

The immediate/later split is useful as an unpadded timing statement, but it
is unnecessary for the checked two-cut interface.  The silent padding used in
the immediate arm works for the entire terminal atom.

More generally, let \(I\) be any finite nonempty player set.  Suppose
\(\nu_n(A)\to\mu>0\) for one nonempty terminal coalition \(A\).  Fix any

\[
  0<\chi<\mu.
\]

Eventually \(\nu_n(A)>\chi\).  For each such \(n\), choose a finite
\(e_n>0\) such that

\[
  \sum_{0\leq t<e_n}w_{n,t}(A)>\chi.
\]

Prefix one deterministic all-Continue row and set

\[
  \operatorname{markedRow}=0,\qquad
  \operatorname{entryCut}=1,\qquad
  \operatorname{exitCut}=e_n+1.
\]

Then:

* the entry suffix is exactly \(s_n\);
* the absolute entry reach is exactly one;
* the exit suffix is exactly \(\operatorname{suffix}_{e_n}s_n\); and
* the total marginal hazard in the block is greater than \(\chi\).

The last item follows by summing the same stage-mass inequalities as above.
Thus, for \(m=|I|\), the checked theorem yields

\[
 D(\operatorname{suffix}_{e_n}s_n)
 \geq D_*+\frac{e^\chi-1}{2}D_*
\]

or an entry payer with debt greater than

\[
 \frac{(1-e^{-\chi})D_*}{2m}.
\]

Choosing tolerance \((1-e^{-\chi})D_*/(4m)\) gives the same strict lower
bound on the whole padded-parent payoff gain, because entry reach is one.  In
Fin4 the gain floor is \((1-e^{-\chi})D_*/16\).

This theorem is strictly stronger for the consumer than the branchwise
constants in the current note: \(\chi\) may be any fixed number below
\(\mu\), and the entry pair is always the original near-minimum \(Z(s_n)\).
It also cleanly separates the general finite-player probability lemma from
the Fin4 hard-residual theorem used to obtain \(A\).

Recommendation: make this the primary exported producer.  Retain the
immediate-versus-strictly-later dichotomy only as a corollary recording where
the mass sits in the unpadded original chronology.

## 4. The padding exposes the exact `postmark` boundary

`QuittingUniformlyReachedPostMarkTwoCutBlock` stores only the inequality
`markedRow < entryCut`; it stores no atom, paid edge, or ancestry at
`markedRow`.  Hence the artificial silent row genuinely inhabits the current
checked type.  It does **not** prove a block lying after an independently
selected paid first-disagreement row, nor does it transport a paid passport
through that row.

The export should say explicitly that it closes the weak checked two-cut
source interface, whose marked row is only an order witness.  It does not
answer the stronger chronological producer problem.  This is especially
important because the current question
`FIN4_POST_MARK_TWO_CUT_RENEWABLE_CHILD_SOURCE.md` already assumes the weak
block and asks to consume its outputs.

## 5. Source and novelty audit

The earlier note
`CODEX_ADVERSARY__FIN4_POSTMARK_TWO_CUT_SOURCE_ADAPTER.md`, Sections 8--9,
already derives a finite window with `entryCut = 0`, reach one, positive
hazard, and the same off-minimum/paid output.  It could not literally inhabit
the checked postmark wrapper because no natural `markedRow` precedes zero.
The universal silent padding above is the small but decisive missing adapter.
The new packet should cite that overlap and present itself as completion of
the wrapper/source interface, not as an unrelated second producer.

The current note still begins from an abstract supplied family \(s_n\).  For
export criterion 4 it must state the exact atlas-level actual-data adapter.
The likely source is `FinFourMinimumReturnPacket.normalizedDecoratedFamily`
and its literal tail, with:

* `forcedPairTail_eq_tail`;
* `normalizedDecoratedFamily_postDateSpine_eq_reference`;
* `minimumTailSource.tailDebt_tendsto`; and
* joint semantic/law compactification along the **same** strict subsequence.

The export must define \(s_n\) from those fields and prove the hypotheses of
the universal padding theorem.  Merely saying “in the atlas application” is
not yet a named actual-data adapter.  If a different current source is
intended, it should be named with the same precision.

Likewise, the sentence saying that the immediate arm “is a renewed
minimum-source entrance” should either be downgraded to “supplies the inputs
for source-faithful causalization” or completed by naming the exact
causalization-to-`FinFourMinimumAtomProducer` assembly.  The two-cut producer
itself does not reconstruct that source.

## 6. Exact remaining corrections before export

1. Lead with the general universal-padding theorem above, or explain a
   mathematical downstream requirement which forbids using it.  Keep the
   current dichotomy as the sharper unpadded-location corollary.
2. Add the named Fin4 atlas adapter producing the exact family \(s_n\), its
   common subsequence, the limiting joint point, and the hard-residual atom.
3. Position the conjecture-facing change precisely: this adds source `A` to
   the formerly conditional checked weak two-cut interface.  It does **not**
   consume the off-minimum or paid output and therefore does not answer
   `FIN4_POST_MARK_TWO_CUT_RENEWABLE_CHILD_SOURCE.md`.
4. Define \(H_n\) before using it in (2.8), or replace it there by the
   displayed hazard sum.
5. Clarify or complete the claimed renewed-source conclusion as described in
   Section 5.
6. Include the overlap audit with the earlier `entryCut = 0` producer and the
   exact reason the silent padding is new and necessary for the present Lean
   wrapper.
7. Add a boundary test where silent padding changes an unrestricted parent
   cap.  This prevents a future formalizer from strengthening the valid
   entry-pair identity into a false whole-parent semantic equality.

After those corrections, one independent delta review should suffice.  The
ordinary mathematics then appears suitable for export as a complete
source adapter to an established semantic endpoint, with the downstream
consumer explicitly still open.  In its present form it is mathematically
sound but not yet through the export gate.

## Delta review of the universal-padding revision

Date: 2026-08-31  
Verdict: **REVISE; do not export yet**

The revision correctly incorporates the principal strengthening:

* one arbitrary fixed \(0<\chi<\mu\);
* one finite original-tail window carrying more than \(\chi\) of the fixed
  atom;
* one universal silent padding row;
* entry reach exactly one;
* entry semantic profile equal to the original \(s_n\); and
* the sharp Fin4 paid floor \((1-e^{-\chi})D_*/16\).

It also adds the correct atlas family, the overlap audit, the artificial-mark
boundary, the unpadded corollary, and the exact nonclaims.  Those revisions
close items 1--6 of the earlier review.

One substantive false sentence remains.  Equation (2.7) currently asserts
unconditionally that prefixing the silent all-Continue row preserves the
complete terminal semantic pair:

\[
 Z(\bar s_n)=Z(s_n).
\]

The prescribed payoff and terminal law are indeed unchanged, but the
unrestricted cap can acquire the new date-zero singleton option.  The exact
coordinate formula is

\[
 B_i(\bar s_n)=\max\{r_i(\{i\}),B_i(s_n)\}.
\tag{D.1}
\]

Thus the displayed semantic equality is false for a general family.  In the
present positive-minimum application it can be repaired without changing the
theorem: the limiting minimum satisfies

\[
 B_i(z_*)-r_i(\{i\})\geq D_*>0,
\]

by `minimumTerminalSemantic_singletonMargin`, and semantic convergence makes
\(B_i(s_n)>r_i(\{i\})\) eventually for all four players.  After deleting that
finite prefix, (D.1) proves the desired semantic equality.  Alternatively,
delete the semantic equality from Section 2 entirely: the checked two-cut
theorem only needs the near-minimum **entry** pair \(Z(s_n)\), not a
near-minimum padded parent.

The mandatory boundary test requested in the first review is also still
absent.  Add, for example, a delayed pure-pair profile for which player \(i\)'s
singleton reward is \(10\) and every payoff available at or after the pair
root is \(0\).  Its unpadded cap is \(0\), while one silent prefix raises the
cap to \(10\).  This verifies (D.1) and prevents a formalizer from using a
false unconditional prefix-semantic identity.

There is one remaining interface clarification.  The checked structure's
`parentProfile` is the canonical history-independent profile reconstructed
from the supplied live-root sequence.  It is semantically equivalent to the
literal padded behavioral profile but need not be definitionally equal as a
complete off-path strategy object.  The final packet should name the standard
live-root/canonical-profile equality when identifying its paid splice with a
silent prefix of the update of \(s_n\).

Finally, in the atlas adapter, (4.1) should be written with the exact existing
definition

\[
 s_n=\operatorname{quittingAllContinueProfileSpine}
   ((\operatorname{packet.stream.frame}\ n).\operatorname{targetProfile})
   ((\operatorname{packet.stream.frame}\ n).\operatorname{stage}+1).
\]

or definitionally as the corresponding continuation profile.  The current
notation is mathematically identifiable, but the final handoff should not
leave `Spine` or \(m_n\) informal when the exact declaration already exists.

After repairing (2.7), adding the cap regression, and making the canonical
profile identification explicit, I see no remaining mathematical or export
criterion blocker.  The result will then be ready as the source adapter to
the checked weak two-cut endpoint; its two outputs remain the named open
consumer waist.

## Final delta review

Date: 2026-08-31  
Verdict: **PASS**

The revised note closes every substantive objection from the preceding delta
review.

1. It gives the exact prefix-cap formula

   \[
   B_i(\bar s_n)=\max\{r_i(\{i\}),B_i(s_n)\},
   \]

   rather than claiming unconditional semantic invariance.
2. It invokes `minimumTerminalSemantic_singletonMargin` at the limiting
   positive global minimum and cap-coordinate convergence to prove eventual
   strict nonbinding of every singleton option.  Since there are four
   coordinates, one finite prefix may be deleted simultaneously, after which
   the complete semantic equality is valid.
3. The added exact regression shows that a silent prefix can raise a cap from
   zero to one while preserving prescribed payoff and law.  This correctly
   delimits the use of the minimum margin.
4. It explicitly distinguishes the checked canonical live-root profile from
   the literal padded behavioral strategy object and claims only the standard
   semantic, law, and splice equalities—not definitional equality off path.

The universal padding adapter itself is sound.  For any fixed
\(0<\chi<\mu\), finite truncation of the same terminal-law coordinate gives
one \(e_n>0\); the stage-mass/root-absorption/union-bound chain gives hazard
strictly above \(\chi\); the artificial prefix gives `markedRow = 0`,
`entryCut = 1`, `exitCut = e_n + 1`, and entry reach exactly one.  The entry
pair is the original \(Z(s_n)\), and the exit pair is its literal
\(e_n\)-suffix.

The atlas chain is source-faithful at the level claimed.  The profiles are
the exact post-date spines of one `FinFourMinimumReturnPacket`; the named tail
equalities identify their debt with the stored tail debt; joint compactness
only refines this same family; and the hard-residual finite-atom theorem is
applied at that resulting minimum joint-law point.  No unrelated law,
minimum, or profile family is substituted.

The constants remain exact:

\[
 K=(1-e^{-\chi})D_*,
 \qquad
 \delta=\frac{e^\chi-1}{2}D_*.
\]

The checked Fin4 split is exit debt at least \(D_*+\delta\), or entry debt
strictly above \(K/8\).  Tolerance \(K/16\) gives conditional and
whole-padded-parent gain strictly above \(K/16\), because entry reach is one,
and exact same-coordinate whole-parent debt decrease.  The small target debt
bound is correctly scoped to the updated entry suffix.

The artificial-mark boundary is stated exactly: the inserted row witnesses
only the record's order inequality and carries no atom, payment, cap-Nash
property, or original chronology.  Reattaching behind the original sure
forced pair need not retain positive gain.  The note also correctly claims no
exit return, renewable child, nonpayer-cap control, charged chronology,
terminal approximation, or uniform payoff.

For the final export handoff, write the informal `Spine` in (4.1) as the
existing full name `quittingAllContinueProfileSpine reward`; this is a
notation/copy edit, not a mathematical objection.  I found no remaining gate
blocker.
