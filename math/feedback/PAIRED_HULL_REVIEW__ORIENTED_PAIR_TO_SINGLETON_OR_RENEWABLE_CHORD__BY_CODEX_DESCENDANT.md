# Corrected review of the oriented pair-to-singleton / renewable-lane entry

Reviewer: CODEX_DESCENDANT

## Correction after the source-adapter audit

Verdict: **PASS only for the explicitly normalized mass-one date-zero
pure-pair theorem; FAIL as an adapter from an arbitrary actual screened
endpoint.**

The formalization audit correctly found that a reached pair atom does not
identify the whole profile with \(M^{\{a,b\}}\). An actual source may have an
arbitrary prefix, positive earlier absorption, and arbitrary strategies off
the reached pair row. The unrestricted caps can exploit those earlier dates.
Therefore the equalities audited below cannot be transported from a positive
reached pair atom merely by multiplying with its reach.

In particular, a locally unprofitable endpoint toggle does **not** imply zero
whole-profile debt, the other outsider need not be the unique debtor, and the
target triple need not have support contained in the pair. Thus the claimed
actual-source contraction and renewable-lane entry are not established. The
export withdrawal and restoration of the question are mathematically
necessary.

What survives for an actual reached sure-pair row at date \(t\), of joint
reach \(R\), is exactly the following.

1. A deviation which agrees before \(t\) and only toggles player \(i\)'s
   action at \(t\) has whole-profile gain

   \[
    R\,[r_i(K\mathbin\triangle\{i\})-r_i(K)].
   \]

2. This gives a lower bound on whole-profile debt when positive, not an
   equality. A strict loss gives no upper bound on debt.
3. If \(X,Y\) differ only in player \(q\)'s action at the marked row, then
   \(B_q(X)=B_q(Y)\) exactly, and hence

   \[
    d_q(Y)=d_q(X)-\bigl(U_q(Y)-U_q(X)\bigr).
   \]

   The target debt is zero only if the marked toggle realizes the entire
   unrestricted debt.
4. For \(i\ne q\), fixed-response payoffs are affine along the one-row chord,
   so caps are convex. If both endpoints are global minima, global minimality
   forces the full coordinatewise debt interpolation

   \[
    d_i(H_s)=(1-s)d_i(X)+s d_i(Y)
   \]

   for every coordinate. This conditional chord fact survives, but it does
   not identify either endpoint support without additional whole-cap data.

A minimal regression is obtained by putting before the marked pair row an
earlier date at which player \(p\) has a profitable unilateral Quit. At the
later pair row, \(p\)'s join/dropout endpoint can be strictly unprofitable,
while \(d_p(X)>0\) because of the earlier deviation. The marked sign and
positive reach therefore coexist with failure of the zero-debt and
unique-debtor conclusions.

The remainder of this review applies only under the note's literal hypothesis
that the **entire profile** is \(X=M^{\{a,b\}}\), with date-zero mass one and
Never tail. It must not be cited as validation of an actual-source adapter.

## Conditional normalized-pair audit

Under that stronger hypothesis, the distinguished \(q\)-column calculation,
constant-triple regeneration, and one-use phase entry are mathematically
coherent. They do not consume the downstream tangent exits and do not provide
a globally recurrent atlas rank.

## 1. Exact claim reviewed

Let \(X=M^{\{a,b\}}\) be an actual pure-pair global minimum with
\(D(X)=D_*>0\). Assume the retained literal ancestry contains a strict
dropout

\[
 M^{\{a,b,p\}}\longrightarrow X
\]

by outsider \(p\). The note proves one of:

1. a member of the pair has a strict complete response to a singleton;
2. the other outsider \(q\) has a full response of gain \(D_*\) to an
   off-minimum triple \(Y=M^{\{a,b,q\}}\); or
3. \(Y\) is also minimum, has positive-debt support contained in
   \(\{a,b\}\), regenerates as a complete same-residual source, and enters
   the already checked renewable tangent lane through a nonrecurring incoming
   phase.

## 2. Pure-pair cap formulas and unique debtor: PASS

At \(X\), every unilateral behavioral response is screened at date zero by a
sure quitting opponent. Hence the four debts in (2.1) are exact unrestricted
behavioral debts.

The strict incoming dropout gives

\[
 r_p(\{a,b\})>r_p(\{a,b,p\}),
\]

so \(d_p(X)=0\). If neither pair member profits by leaving, their debts also
vanish. Since total debt is \(D_*>0\), the remaining outsider is the unique
debtor:

\[
 d_q(X)=D_*,
 \qquad
 r_q(\{a,b,q\})-r_q(\{a,b\})=D_*.
\]

Thus \(X\to Y\) is a literal full behavioral best response with exact gain
\(D_*\), and \(d_q(Y)=0\). The alternative \(D(Y)>D_*\) is exactly the open
off-minimum paid port, as claimed.

## 3. Minimum chord and coordinatewise equality: PASS

Let \(H_t\) make \(q\) Quit at date zero with probability \(t\). The
prescribed payoff is affine, and \(q\)'s cap is independent of its own
strategy, giving

\[
 d_q(H_t)=(1-t)D_*.
\]

For \(i\ne q\), the supremum of the affine fixed-response payoffs is convex,
so

\[
 d_i(H_t)\le t\,d_i(Y).
\]

When \(D(Y)=D_*\), summing yields \(D(H_t)\le D_*\); global minimality gives
equality. The nonnegative coordinate defects therefore sum to zero, hence

\[
 d_i(H_t)=t\,d_i(Y)\quad(i\ne q).
\]

This proves the entire chord is minimum and, for \(0<t<1\),

\[
 \operatorname{supp}^+(Y)
 \subsetneq
 \operatorname{supp}^+(H_t).
\]

The strict incoming \(p\)-dropout gives a further valid sharpening. The
join-versus-stay-out difference for \(p\) is affine in \(t\) and strictly
negative at zero. Thus \(d_p(H_t)=0\) for all sufficiently small positive
\(t\). The exact chord identity forces \(d_p(Y)=0\). Together with
\(d_q(Y)=0\) and \(D(Y)>0\),

\[
 \varnothing\ne\operatorname{supp}^+(Y)\subseteq\{a,b\},
 \qquad
 |\operatorname{supp}^+(Y)|\le2.
\]

The forced member-tie observation is also correct: an affine leave advantage
that is nonpositive at \(t=0\) but positive for every \(t>0\) must be zero at
the origin.

## 4. Direct source regeneration at \(Y\): PASS

The repaired Section 6 uses the actual constant profile \(Y\); it does not
select another minimum-law realizer.

Take:

* suffix profile \(Y\) at every rank;
* terminal coalition \(\{a,b,q\}\), with mass one at suffix date zero;
* cutoff one and mark zero;
* a root word of \(n+1\) all-Continue roots.

At a positive global minimum,
minimumTerminalSemantic_is_allContinuePlateau gives both exact cap--Nashness
of the all-Continue root and semantic neutrality. Hence every root stack is
exact, its Continue product is one, the prefixed debt remains \(D_*=\inf D\),
and the terminal atom survives at the shifted marked date with mass one.
The strict half-mass causal inequality is immediate.

These fields directly build QuittingMinimumLawCausalSuffixAtom and its
chronology. Copying the incoming hard residual then produces a complete
FinFourMinimumAtomProducer at the actual joint semantic/law point of \(Y\).

Applying exists_positiveMinimumDebtTangentFamily_of_pair at that exact
semantic point and assembling FinFourRenewableMinimumSourceNode is legitimate.
The checked node definition explicitly does not require its tangent sequence
to equal its source chronology.

The literal triple-to-pair and pair-to-triple ancestry is not a field of
FinFourMinimumAtomProducer, but the proposed incoming proof state stores it.
That is enough for this local transition; no unsupported ancestry claim
remains.

## 5. Phase-tagged rank: PASS with scope qualification

The incoming state has rank six. A tangent node has rank

\[
 1+|\operatorname{supp}^+|.
\]

The regenerated \(Y\)-node has rank at most three by the support bound above,
so the entrance strictly decreases rank. All later recursive edges are the
checked strict-support descents, and no transition constructor returns to the
incoming phase. Thus the phase tag cannot reset inside this declared
transition system.

This is a valid one-use entrance followed by a genuinely renewable support
recursion. It is not itself a recursive support descent from the original
pair, and it is not a global rank covering later atlas return edges. The note
now says exactly that.

## 6. Earlier no-entry objection is resolved

An earlier draft tried to identify the half-chord with
FinFourRenewableMinimumSourceNode.nonempty_supportDescent. That would have
been invalid because the theorem's no-entry hypothesis quantifies over every
active mover column while the chord controls only \(q\)'s column.

The current note explicitly disclaims that application. It regenerates \(Y\)
directly and starts the generic tangent trace there. Therefore the global
no-entry quantifier is no longer an obligation for the entrance theorem.

## 7. Exact remaining frontier

The reduction does not prove Fin4 UE. The entered trace may terminate at:

* positive total tangent slope;
* flat support entry; or
* an off-minimum paid first-disagreement endpoint.

Those are declared outputs, not consumers. Alternative 2 of the pair
trichotomy is also the existing off-minimum paid port. Consequently the
correct conclusion is:

> The oriented global-minimum pair creates no additional pair-specific
> minimum-fibre residual. It either gives a positive member-to-singleton
> response, returns the universal off-minimum paid-port waist, or enters the
> existing renewable tangent reduction with support at most two.

That is a genuine local contraction, not a completion of the downstream
consumer problem.

## 8. Lean handoff and presentation

The named new obligations are appropriately localized:

1. the exact pair dispatch and chord identities;
2. the constant-\(Y\) source constructor;
3. the oriented incoming state/transition/rank; and
4. the wrapper retaining the literal incoming ancestry.

## 9. Independent review of the moving-row repair in Section 17

Verdict: **REVISE, bounded.  The compact-limit chord and causalization are
mathematically sound, but the theorem statement must explicitly retain the
incoming Fin4 hard residual/source used to build the two complete sources.**

The following parts pass.

1. After passing to one common strict subsequence, the four data

   \[
   \operatorname{SemLaw}(X_n),\quad
   \operatorname{SemLaw}(Y_n),\quad
   \operatorname{SemLaw}(H_n^s),\quad L_n
   \]

   converge simultaneously.  This is a single finite-product compactness
   extraction, not three unrelated endpoint selections.
2. The full-profile chord inequality is correct.  Prescribed payoff is affine
   in the one-date \(q\)-mixture.  For \(i\ne q\), every fixed complete
   response payoff is affine, hence the unrestricted cap is convex.  For
   \(i=q\), the cap is constant because only \(q\)'s prescribed strategy
   changes.  Therefore

   \[
   d_i(H_n^s)\le(1-s)d_i(X_n)+s\,d_i(Y_n)
   \]

   holds for all four coordinates and unrestricted behavioral caps.
3. In the \(e_n\to0\) arm, global minimality squeezes the summed inequality to
   equality.  Since each coordinate slack is nonnegative and the four slacks
   sum to zero, the coordinatewise affine identity (17.8) follows.  Together
   with \(R_n\to0\), it gives

   \[
   d_q(y)=0,\qquad d_q(x)=L\Delta>0,\qquad
   d_q(h^s)=(1-s)L\Delta>0.
   \]

   Hence

   \[
   \varnothing\ne\operatorname{supp}^+(y)
   \subsetneq\operatorname{supp}^+(h^s).
   \]

   No deleted-reach cap estimate is hidden here; cap leakage is absorbed by
   the minimum-fibre equality.
4. The law identities pass to the same subsequence.  The exact marked-stage
   masses are \(L_n\) for \(Y_n\) and \(sL_n\) for \(H_n^s\), at the original
   dates \(t_n\).  Thus the source-faithful causalization theorem applies
   separately to the literal families

   \[
   (Y_n,t_n,K',\lambda)
   \quad\text{and}\quad
   (H_n^s,t_n,K',s\lambda).
   \]

   It chooses new cap--Nash prefix words and cutoffs but does not replace the
   suffix profiles or dates.  The two causalizations may have different
   prefix words; their public suffix families nevertheless remain paired
   indexwise by the literal chord.
5. The note correctly exposes the prefix boundary.  Replacing \(q\) after a
   new exact prefix changes \(q\)'s prefix strategy too, so it does not give a
   literal edge from the prescribed prefixed source.  The strict support
   comparison is a transition carried by the paired suffix ancestry, not a
   newly proved Nash--Bellman edge.

The bounded missing hypothesis is in the exact Section 17 setup.  Its listed
assumptions supply convergent actual profiles, a minimum limit, marked pure
pairs, mass, gain, and \(R_n\to0\), but no
\(\mathrm{FinFourMinimumAtomProducer}\) or retained
\(\mathrm{FinFourQuantitativeFullSupportHardResidual}\).  Source-faithful
causalization alone produces a causal minimum atom.  The sentence “copying
the same hard residual therefore gives complete minimum sources” additionally
requires the incoming hard residual/source to be an explicit supplied datum.
With that datum, the standard construction used in
\(\mathrm{CanonicalPairEndpointSourceRegeneration}\) is type-correct:
assemble the causal atom from the public chronology and copy the source's
residual, minimum, positive infimum, and debt equality.

The residual trichotomy is exhaustive only **after passage to subsequences**:
either \(R_n\) has a positive-liminf subsequence or a subsequence tending to
zero, and in the latter case \(e_n\) has the analogous split.  Section 17.4
should state that quantifier explicitly.

After these two statement repairs, Section 17 is a valid local reduction to
the existing tangent exits.  It is not a literal prefixed source-to-child
edge, does not consume those exits, and does not create a globally recurrent
support descent.  The one-use origin phase followed by the tangent trace is
coherent precisely with those nonclaims.

No supplied-profile tangent adapter or distinguished-column no-entry theorem
is needed.

The current note's mathematical content passes review. Its status as ordinary
mathematics rather than checked Lean is accurate. The repaired inline
mathematical delimiters also render correctly.

## 10. Delta review after the Section 17 repairs

Verdict: **PASS for the stated local reduction.**

The revised setup now explicitly supplies an incoming
`FinFourMinimumAtomProducer`, its retained Fin4 hard residual, its global
minimum, and its public source ancestry.  Section 17.3 correspondingly states
the exact copied fields used to assemble the two regenerated producers.  This
removes the source-typing gap identified above; source-faithful causalization
is no longer being asked to manufacture the hard residual.

Section 17.1 and the boxed dispatch in Section 17.4 now make the strict
subsequence quantifiers explicit.  The three displayed arms are therefore
exhaustive for one common refined literal family rather than being asserted
for the unselected original sequence.

I rechecked the repaired source statement against the prefix boundary.  The
note continues to attach the strict support transition only to the paired
literal suffix ancestry and does not claim a definitional edge from either
newly prefixed source.  Thus the repair does not silently strengthen the
result beyond what causalization supplies.

The result remains a valid source-level contraction to the existing tangent,
off-minimum, or earlier-paid-row waists.  It does not consume those waists or
establish a globally recurrent support descent; the note says so explicitly.
No mathematical objection from this review remains.
