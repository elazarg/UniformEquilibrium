# Review of PAIRED_HULL_REVIEW__ORIENTED_PAIR_TO_SINGLETON_OR_RENEWABLE_CHORD

Reviewer: SOCIAL_WEIGHT_REVIEW

Verdict: **REVISE.** The pair debt calculation and the affine
minimum-fibre chord are correct. The claimed invocation of the existing
renewable-support edge is not: the note proves no entry for the selected
outsider column only, whereas the checked hypothesis is a global
all-columns no-entry predicate.

## Valid mathematics

At the pure pair \(X=M^{\{a,b\}}\), sure date-zero screening gives exactly

\[
\begin{aligned}
d_a(X)&=[r_a(\{b\})-r_a(\{a,b\})]_+,\\
d_b(X)&=[r_b(\{a\})-r_b(\{a,b\})]_+,\\
d_p(X)&=[r_p(\{a,b,p\})-r_p(\{a,b\})]_+,\\
d_q(X)&=[r_q(\{a,b,q\})-r_q(\{a,b\})]_+ .
\end{aligned}
\]

The strict incoming dropout by \(p\) kills \(p\)'s pair debt. If neither
pair member leaves profitably, global minimality and \(D_*>0\) indeed force
\(q\) to be the unique debtor with \(d_q(X)=D_*\). Its pure join \(Y\) is an
exact unrestricted best response of gain \(D_*\) and has \(d_q(Y)=0\).

Assuming \(D(Y)=D_*\), the chord calculation is also exact. For the profile
\(H_t\) in which only \(q\)'s date-zero marginal is softened,

\[
d_q(H_t)=(1-t)D_*,
\qquad
d_i(H_t)\le t\,d_i(Y)\quad(i\ne q).
\]

The first identity uses invariance of \(q\)'s cap under its own replacement.
The second is the convexity of each nonmover cap minus affine prescribed
payoff. Since global minimality gives the reverse total-debt inequality,
all coordinate inequalities are equalities:

\[
D(H_t)=D_*,
\qquad
d_i(H_t)=t\,d_i(Y)\quad(i\ne q).
\]

Consequently, for \(0<t<1\),

\[
\operatorname{supp}^+(Y)
 \subsetneq \operatorname{supp}^+(H_t),
\]

and the half-chord replacement \(H_{1/2}\to Y\) is a complete best response
of gain \(D_*/2\). There is no support entry in this **particular \(q\)
column**. The profitable pair-to-singleton branch is likewise a genuine
unrestricted response.

The singleton tie/refusal discussion is consistent with the checked
singleton-margin calculation: at a pure singleton positive minimum, the
owner debt already equals all of \(D_*\), so every outsider debt is zero.

## Main blocker: columnwise no entry is not the checked hypothesis

The proposed supplied-profile tangent adapter must store a replacement
column for every player in the positive-debt support of \(H_{1/2}\), not only
for \(q\). The checked predicate
HasQuittingStoppingLawFlatSupportEntry is existential over **all** active
movers:

\[
\exists m\in\operatorname{supp}^+(H_{1/2}),\ 
\exists j\notin\operatorname{supp}^+(H_{1/2}),\
T_{m,j}>0.
\]

Thus its negation says that no active mover's column enters any inactive
coordinate. Equations (5.1)--(5.5) prove only

\[
T_{q,j}=0
\quad\text{for inactive }j.
\]

They give no information about \(T_{m,j}\) for another active mover \(m\).
At the screened product profile, a nonmover cap is a maximum of affine
endpoint functions, so another best-response direction can activate a
previously tied cap and create exactly such first-order support entry.
Neither global minimality nor the \(q\)-chord identity rules this out.

Accordingly the note cannot invoke
FinFourRenewableMinimumSourceNode.nonempty_supportDescent as written. That
theorem requires the global negation of
HasQuittingStoppingLawFlatSupportEntry, and the structure
FinFourRenewableSupportDescent stores that proof. The strict inclusion
already proved for the literal pair \(H_{1/2},Y\) does not inhabit this
structure by itself.

This is substantive, not merely a Lean naming issue. In the present API,
support entry by any other column is a separate terminal exit. It is not an
already consumed branch, so the headline claim that the minimum-fibre pair
branch has no remaining obstruction is too strong.

## Repairs that preserve the valid core

There are three honest repairs.

1. Add a fourth output:

   \[
   \text{positive tangent support entry at }H_{1/2}.
   \]

   Under its negation, the existing nonempty_supportDescent theorem applies
   to the \(q\)-endpoint. This is the smallest repair, but it leaves another
   unconsumed exit besides the off-minimum paid port.

2. Define a new direct literal-chord edge. Regenerate a complete minimum
   source at \(Y\), attach an arbitrary tangent family there, and use the
   already proved literal inclusion
   \(\operatorname{supp}^+(Y)\subsetneq
   \operatorname{supp}^+(H_{1/2})\) as a bespoke one-use transition. Then
   start the checked renewable trace at the \(Y\)-node. This is ordinary
   mathematics plausibly supported by the source-causalization machinery,
   but it is **not** an instance of FinFourRenewableSupportDescent; the new
   transition and its no-return phase must be stated explicitly.

3. Prove a genuinely new theorem that all other selected tangent columns at
   this screened chord have no inactive entry. Nothing in the current note
   proves that statement.

Repair 2 can yield a real renewable lane after the one-use chord: subsequent
recursive edges are the checked strict-support descents. It must not be
described as if the current global no-entry theorem already supplied the
first edge.

## Adapter and source comments

A constant-profile tangent specialization is plausible but remains a new
adapter. To identify its \(q\)-column literally with \(Y\), it must choose
the strict date-zero cap attainer for \(q\), compute the normalized chord
direction, and prove its sum is zero. The generic
exists_positiveMinimumDebtTangentFamily_of_pair chooses a realizing
sequence and vanishing-regret responses; it does not expose this prescribed
constant sequence or prescribed response.

The source regeneration claim is also plausible: both \(H_{1/2}\) and \(Y\)
are actual positive-minimum product profiles with positive finite atoms, so
the existing source-faithful causalization can build complete same-residual
sources from constant literal sequences. The implementation must invoke
that construction and retain the exact marked atom; merely saying that
all-Continue prefixes are neutral does not by itself fill every producer and
chronology field.

## Formatting and scope

The file currently contains widespread lost LaTeX delimiters such as
(I=...), (D_*>0), and (H_t), and the Lean-handoff paragraph is duplicated.
These should be repaired before any export review.

The valid current result is:

\[
\boxed{
\begin{array}{c}
\text{profitable pair-to-singleton response}\\
\lor\ \text{off-minimum outsider join}\\
\lor\ \text{literal minimum chord }H_{1/2}\to Y
\text{ with strict endpoint support inclusion}.
\end{array}}
\]

The last arm is a strong source-regeneration candidate. It is not yet the
claimed existing renewable-support edge without one of the repairs above.

## Post-repair delta audit

Verdict on the revised Sections 6--7: **PASS.**  The author adopted repair 2
rather than trying to manufacture the missing all-columns no-entry proof.

The repaired argument regenerates a complete source directly at the literal
triple profile (Y).  This is mathematically sound.  The constant realizing
sequence has the actual semantic pair and law of (Y); the triple atom has
mass one at date zero.  Prefixing (n+1) all-Continue roots is a genuine
cap--Nash stack: positive global minimality gives both the all-Continue
plateau and the strict singleton margin, so the cap is unchanged after every
prefix.  The prefix debt and law are constant, and the shifted marked atom
still has mass one.  These data fill the causal atom and chronology fields
without selecting a new behavioral realizer.  Copying the hard residual is
legitimate because it is a reward-table residual, and the generic tangent
extractor may be attached at the exact semantic point of the regenerated
source by the checked node definition.

The rank is now honestly phase tagged.  The first edge is a one-use
`incoming -> tangent(Y)` transition; it is not advertised as
`nonempty_supportDescent`.  Thereafter every recursive edge is one of the
checked strict-support descents, and no constructor returns to `incoming`.
Thus this is not an indefinitely renewable one-time comparison: after the
single literal/source-attached entry, the existing renewable trace supplies
the recursion.  The downstream positive-slope, support-entry, and off-minimum
terminal exits remain expressly unconsumed.

The support bound at (Y) actually makes the recursive part shorter than the
generic Fin4 estimate: its initial support has cardinality at most two, so at
most one strict nonempty-support child descent is possible.  This is an
optional strengthening, not a repair.

No mathematical objection from the original review remains.  The result is
still a reduction into the renewable tangent lane, not a terminal Fin4
consumer.

## Post-formalization source-typing correction

Verdict on the proposed **atlas adapter**: **FAIL.**  I retract the last
paragraph's acceptance of that adapter.  The local theorem remains correct
for the literal mass-one profile (M^{\{a,b\}}), but the screened endpoint
provided by the source atlas is not such a profile.  It retains an arbitrary
pre-mark prefix, possible earlier absorption, and the original post-mark
tail.  Only its conditional marked root is the pure pair.

This distinction changes complete caps.  At the conditional pair root an
outsider (q) has only the stay-out and join values, but in the complete
actual profile (q) may also obtain a larger value by changing an earlier
action.  Hence a strict marked-row join need not attain (q)'s unrestricted
cap, need not kill (d_q), and need not make (q) the unique global debtor.
The identities (4.1)--(5.7) therefore cannot be applied to the atlas endpoint
without an additional cap-alignment theorem.

A minimal regression already uses one earlier partially absorbing row.
Choose its all-Continue probability (L\in(0,1)), put the pure pair at the
next reached row, and give (q) a positive conditional join premium there.
Give (q) a still larger payoff from a unilateral Quit at the earlier row.
The marked join is then a strict source-attached update of unconditional gain
(L) times its local premium, but the earlier Quit remains the complete cap
attainer on both sides.  The marked update does not kill (q)'s debt.  All
off-date strategies and the post-mark tail can be held fixed, so neither
screening at the marked row nor literal ancestry repairs the failure.

There is a valid conditional replacement for the failed adapter.  Suppose
one separately knows for the actual prefixed profiles (X,Y) that:

1. (X) and (Y) are both global minima;
2. only (q)'s marked-row action differs;
3. that update attains (q)'s complete cap, so its gain is (d_q(X)) and
   (d_q(Y)=0).

Then the full-profile chord (H_t), formed by mixing only that marked action,
does preserve the literal prefix and tail.  Prescribed payoffs are affine in
(t); every fixed nonmover response payoff is affine in (t), even though
its reach of the mark may differ from prescribed reach; and the supremum
therefore gives

\[
 d_q(H_t)=(1-t)d_q(X),\qquad
 d_i(H_t)\le(1-t)d_i(X)+t d_i(Y)\quad(i\ne q).
\]

Global minimality makes the summed inequality an equality, hence makes every
coordinate inequality an equality.  This is the honest reach-preserving
chord lemma.  It is conditional on the missing complete-cap alignment and
does not derive that alignment from a conditional pure pair.

Likewise, passing to the literal suffix at the mark recovers the mass-one
pair calculation, but loses the needed global-minimum comparison: that suffix
has total debt at least (D_*), not necessarily exactly (D_*).  A copied
suffix response lifts to the parent with its payoff gain multiplied by the
prescribed reach, but its complete-cap and support conclusions do not lift.

The corrected durable result is therefore only the local normalized theorem
plus the conditional full-profile chord above.  The source-faithful oriented
pair question remains open, exactly as stated in
`questions/FIN4_STRATEGIC_PAIR_TERMINAL_CONSUMER.md`.
