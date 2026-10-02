# Review of actual reached-pair residual note

Reviewer: `PAIRED_HULL_REVIEW`

## Verdict

**PASS, with two bounded clarifications and one useful strengthening.**

The note's main mathematical distinction is correct.  The unconditional gain
of the literal marked-row toggle is \(L\Delta_i\), whereas the unrestricted
cap debt is

\[
 d_i(\sigma)=[L\Delta_i]_+ +R_i^t(\sigma).
\]

The residual is genuine whole-behavior cap mass which is not controlled by
the marked pair's actual reach.  For a nonmover the correct uniform cap
modulus is the player-deleted reach \(H_j(t)\), and the displayed Fin4 example
really realizes \(L=\varepsilon\) together with order-one nonmover cap motion.
Nothing in the proof replaces the actual prefix or post-mark tail.

## Checks

### Marked payoff and law

Equation (2.1) follows by coupling before \(t\).  On the reach event another
sure quitter remains after either action of \(i\), so the two profiles stop at
\(t\) in coalitions \(K\) and \(K'\).  This also proves the signed law identity
(2.1a), including the unchanged Never coordinate.

Among replacements which literally retain \(i\)'s behavioral actions before
\(t\), every choice at \(t\) is a mixture of the two screened endpoints.
Therefore (2.3) is exact, not only an upper bound.  Subtracting it from the
unrestricted cap gives (2.5), and own-strategy invariance of the cap gives
(2.6).  If a response within error \(\epsilon<R_i^t\) agreed before \(t\), its
payoff would be at most \(E_i^t=B_i-R_i^t<B_i-\epsilon\).  Thus the stated
pre-mark-strategy-change conclusion is correct.

### Exact-prefix specialization

Section 3 is correctly stronger than arbitrary source provenance.  Iterating
exact cap--Nash debt scaling through the roots strictly before \(t\) multiplies
the reached screened debt \([\Delta_i]_+\) by joint reach \(L\).  It therefore
annihilates the residual.  Merely knowing the literal prefix does not justify
that step.

### Deleted reach

For a response by \(j\ne q\), source and toggled opponents can differ only on
the event that every opponent of \(j\) survives before \(t\).  Coupling gives
the \(2M H_j(t)\) payoff modulus uniformly over all complete behavioral
responses, so taking suprema gives (4.3).  Independence gives
\(L=S_j(t)H_j(t)\).  No bound \(H_j(t)\le C L\) is possible without a lower
bound on \(S_j(t)\).

### Regression

The example is consistent.  Player 2 can obtain one by quitting at date zero
whether player 3 quits simultaneously or not, so its cap is one on both
profiles.  Player 3's cap moves from zero to one because continuing at date
zero changes the reached marked coalition from \(\{0,1\}\) to
\(\{0,1,2\}\).  Hence (5.4)--(5.5) hold.  The incoming player-3
triple-to-pair edge is strict with unconditional gain \(\varepsilon\).  The
remaining rewards can indeed be chosen in \([-1,1]\) so that no omitted option
exceeds the displayed cap; for example, making player 2 quit alone at date
zero and all others continue gives a zero-debt profile.  Thus this is a valid
source-field regression, not a positive-gap table.

## Bounded clarifications

1. In Section 2, “complete behavioral response” should mean “a literal
   unilateral behavioral replacement.”  The one-row toggle need not be a
   best response.

2. Calling \(R_i^t\) “pre-mark” is initially a strategy statement: a cap-near
   response must change \(i\)'s strategy before \(t\).  By itself this does
   not date an arbitrary pair of pure witnesses.  The revised Section 4 adds
   the two decisive fields—source-witness support and selection of the locally
   optimal marked endpoint—and thereby upgrades the conclusion to a paid row
   strictly before \(t\), as checked in the delta review below.

There are also mechanical Markdown defects in the current note: many inline
formulas use bare parentheses, and the profitable-gap display contains
`0,qquad`.  These do not affect the mathematics but should be repaired before
any packet gate.

## Initial strengthening: the residual yields a paid row at or before the mark

Let \(\bar\sigma\) be the literal profile using the better marked endpoint.
Then

\[
 d_i(\bar\sigma)=R_i^t(\sigma).
\]

If \(R_i^t>0\), applying the checked actual-joint-reach paid-row theorem to
the actual profile \(\bar\sigma\) produces a source-supported pure-time paid
row and the checked opponent/joint reach floors.  Its first-disagreement date
is at most \(t\): if both pure
plans continued through \(t\), the other sure quitter(s) in the marked pair
would terminate the game at \(t\), so the two values would be equal.

This gives an exact dichotomy:

\[
 R_i^t>0
 \Longrightarrow
 \begin{cases}
 \text{a paid pure-time row strictly before }t,\quad\text{or}\\
 \text{a paid endpoint row at }t\text{ priced at deleted reach.}
 \end{cases}
\]

It is stronger than the note's qualitative “almost-cap response changes
before the mark,” but it is still not a renewable descent.  The row is a
counterfactual pure-time comparison against fixed opponents.  Its root is not
proved cap--Nash, its receiving replacement can destroy the marked pair, and
the theorem does not identify the row as a literal source-to-successor prefix
edge.  In the strict-earlier arm the calendar date decreases once, but the
output does not regenerate the reached-pair state type.  In the date-\(t\) arm
the obstruction is exactly deleted-reach amplification.  Thus no existing
prefix chronology or natural-valued rank follows without one additional
source/renewal field.  The delta review below uses the support clause and
local optimality to exclude the date-\(t\) arm as well.

## Conclusion

The note correctly diagnoses the formalizer's adapter failure and supplies a
sharp finite regression.  Positive residual can be localized more strongly
to an actual paid pure-time row strictly before the mark, but neither arm is an
exact Nash--Bellman prefix edge or a regenerated pair source.  The source-
faithful oriented-pair question therefore remains open for precisely the
reason stated in Section 6.

## Delta review: strict-earlier paid-port extension

**PASS, with one wording correction.**

Let \(\widehat\sigma\) be the literal better-endpoint profile and put
\(\rho=R_i^t(\sigma)>0\).  Equation (2.6) gives
\(d_i(\widehat\sigma)=\rho\).  The checked theorem
positiveDebt_exists_actualJointReach_paidRow_mem_support applies at the exact
scale \(\Delta=\rho\).  It supplies:

* a paid first-disagreement row declared at gain \(\rho/4\);
* a source pure clock in the actual stopping-law support of
  \(\widehat\sigma_i\);
* \(\rho\le4M S_i(e)\);
* \(\rho\le8M\operatorname{OppReach}(e)\); and
* \(\rho^2\le32M^2\operatorname{JointReach}(e)\).

The note displays the latter two floors and uses precisely the support clause
needed for the temporal argument.  The theorem's row field proves that the
actual pure-time payoff difference is **at least** \(\rho/4\).  Thus
“\(\operatorname{gain}(e)=\rho/4\)” in (4.2) should be read as the row's
declared gain parameter, or changed to “paid gain at least \(\rho/4\).”
There is no equality theorem for the realized payoff difference.

The proof of \(\operatorname{start}(e)<t\) is correct and genuinely stronger
than the at-most-\(t\) observation in my initial review.  If the supported
source clock \(q_0\) is earlier than \(t\), the conclusion is immediate.  If
\(q_0\ge t\), then:

* when the selected endpoint is Quit, prescribed conditional stopping at
  \(t\) is sure, so support at or after \(t\) is concentrated at \(t\);
* when the selected endpoint is Continue, there is no stopping mass at \(t\),
  and every supported finite time after \(t\), as well as Never, has the same
  screened Continue value;
* a receiving clock quitting at \(t\) has the other endpoint value, which is
  no larger because \(\widehat\sigma\) selected the locally optimal endpoint;
  and
* any receiving clock later than \(t\) or Never has exactly the same Continue
  value.

Therefore no receiving pure clock first disagreeing with a supported
\(q_0\ge t\) at or after \(t\) can have strictly larger value.  The positive
row inequality forces first disagreement strictly before \(t\).  This covers
mixed prescribed pre-mark hazards, arbitrary post-\(t\) support, and Never
without truncation or attainment assumptions.

The resulting dispatch is source-faithful in the following exact sense:
\(\widehat\sigma\) is the literal one-row endpoint update of \(\sigma\); the
row is constructed against its unchanged actual opponents; its source clock
is supported by its actual stopping law; and every earlier action, earlier
absorption possibility, and the literal tail remain present.  Together with a
supplied positive global minimum pair, this row instantiates the existing
paid-cap port and its charged-near-return / quantitative-debt-descent /
inert-stall trichotomy.

It does not finish the strategic-pair question:

1. In the \(\rho=0\) arm, only the mover is killed.  Nonmover cap transport
   still occurs at deleted-reach scale, so the actual-prefix minimum chord and
   renewable support drop remain unproved.
2. In the \(\rho>0\) arm, the charged-near-return output has its existing
   consumer, but quantitative descent and inert stall remain open.
3. The strict calendar decrease is one-use.  The port target need not retain a
   screened pair at a later marked row, so \(t\) is not yet a renewable rank
   on a closed state type.
4. A paid pure-time first-disagreement row is not itself an exact cap--Nash
   prefix or a punishment-annotated Nash--Bellman chronology.

Accordingly (0.1) is a valid strict source-level reduction, not a completed
pair consumer.
