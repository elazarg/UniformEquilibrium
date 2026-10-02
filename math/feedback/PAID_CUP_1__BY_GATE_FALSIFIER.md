# Adversarial review of `PAID_CUP_1.md`

Author: `CODEX_GATE_FALSIFIER`

## Verdict

**The proposed solution fails, but Sections 1--2 contain a valid and
apparently unrecorded off-minimum root-classification theorem.**

I found no sign error and no small counterexample to the classification.  The
finite root game against the prescribed payoff is well defined, an exact
mixed product root exists, and prefixing such a root to an actual source
profile gives an actual behavioral profile.  The strict-debt calculation is
correct.

The surviving theorem does **not** close the paired unique-cap question.  A
strict real debt descent produced this way need not retain the paid row,
positive incidence, or a renewable reset packet, and the solo-debtor outputs
have no terminal or return consumer.  The result refines the paired unique-cap
state into sharper prescribed-payoff gates; it does not supply any of the five
accepted conclusions.

## 1. The endpoint-difference sign is correct

Write

\[
\Delta_i(v,x)=Q_i(x)-C_i(v,x),
\qquad
s_i(x)=\prod_{j\ne i}x_j(C).
\]

The Quit endpoint is independent of the continuation vector because player
\(i\) quits surely.  The Continue endpoint uses \(v_i\) exactly on the event
that every opponent Continues, whose probability is \(s_i(x)\).  Therefore

\[
C_i(b,x)=C_i(u,x)+s_i(x)(b_i-u_i)
\]

and hence

\[
\boxed{\Delta_i(b,x)=\Delta_i(u,x)-s_i(x)d_i.}
\]

Thus the sign in equation (1) is correct.  Raising the continuation from the
prescribed payoff \(u_i\) to the cap \(b_i\) makes Continue more attractive
and decreases Quit-minus-Continue.

This is also exactly the direction of the checked continuation-update formula
`quittingRootContinuePayoff_update_add`.  The Quit invariance is checked as
`quittingRootQuitPayoff_continuation_invariant`.

## 2. Active-zero-debt lifting is valid

Suppose \(x\) is an exact Nash root in the finite binary root game with
continuation payoff \(u\), and

\[
x_i(Q)>0\Longrightarrow d_i=0.
\]

For a player with positive Quit probability, the whole endpoint comparison is
unchanged because \(d_i=0\).  This covers both pure Quit and a genuinely mixed
marginal.  For a player with zero Quit probability, the prescribed action is
pure Continue; exactness at \(u\) says \(\Delta_i(u,x)\le0\), and the identity
above gives \(\Delta_i(b,x)\le\Delta_i(u,x)\le0\).  Therefore \(x\) is exact
against \(b\).

Consequently, if all-Continue is the unique exact root against \(b\), every
non-all-Continue exact root against \(u\) has some active positive-debt player.
Equation (3) is correct.

The phrase “exact root against \(u\)” is not problematic.  It means a mixed
Nash equilibrium of the finite one-stage binary-action game whose
all-Continue continuation payoff is \(u\).  Nash existence supplies such a
product root for every finite payoff vector \(u\).  It is not being identified
with a dynamic cap root.

## 3. The stronger debt-prefix bound is correct

For an exact root against \(u=p.1\), the semantic prefix identity is

\[
d_i(p')=
\max\{0,s_i(x)d_i(p)-e_i(u,x)\},
\]

where \(e_i(u,x)=\max(0,\Delta_i(u,x))\ge0\).  Hence

\[
\boxed{d_i(p')\le s_i(x)d_i(p)\le d_i(p).}
\]

This is stronger than the plain coordinatewise contraction theorem and is
already available algebraically through
`quittingTerminalSemanticDebt_prefix_eq_blockAct` and
`Block.act_le_survival_mul_debt`.

For a generic semantic pair one should call this a semantic-prefix debt
contraction.  It becomes the “actual debt descent” asserted in the note only
when \(p\) is the semantic pair of an actual profile.  Both singleton-source
profiles used in Section 3 are actual stationary profiles, so the application
is legitimate: prefix the selected root literally to that profile.

## 4. The strict/equality classification is correct

Let \(x\ne\mathbf C\) be exact against \(u\), and assume the cap at \(b\) has
unique root \(\mathbf C\).  By active-zero-debt lifting, choose \(i\) with

\[
d_i>0,qquad x_i(Q)>0.
\]

If another player \(j\ne i\) has positive debt, then player \(i\)'s positive
Quit probability gives \(s_j(x)<1\).  Therefore

\[
d_j(p')\le s_j(x)d_j(p)<d_j(p),
\]

while every other coordinate weakly decreases.  Total debt decreases
strictly.

If \(i\) is the unique debtor but some other player quits with positive
probability, then \(s_i(x)<1\), so the same strict conclusion holds in
coordinate \(i\).

Thus failure of strict total-debt descent implies exactly the necessary face
conditions

\[
\operatorname{supp}_+(d)=\{i\},
\qquad
x_k=\mathbf C\quad(k\ne i).
\]

The note correctly says that equality is *possible only* on this face.  It
does not incorrectly assert the converse: an exercise premium can still make
the solo-debtor prefix decrease debt strictly.

The general surviving statement is therefore:

> Let \(p=(u,b)\) be an actual terminal semantic pair with nonnegative debts
> and suppose all-Continue is the unique exact root at \(b\).  For any exact
> root \(x\) at \(u\), either \(x=\mathbf C\), the literal prefix
> \(x\triangleright p\) has strictly smaller total debt, or \(p\) has a unique
> positive debtor and \(x\) is supported on that debtor's marginal alone.

Existence of an exact payoff root then gives the three-way alternative in
equation (7).

## 5. Application to the source and repaired profiles

The source-side support assertion is checked data:
`FinFourSingletonBaseSameLawResetProducer.positiveDebtSupport_eq` says the
singleton owner is the unique positive debtor, while `owner_gap` makes its
debt positive.  Hence its prescribed-payoff root alternative is exactly

\[
\text{all-Continue only}
\quad\lor\quad
\text{strict actual debt descent}
\quad\lor\quad
\text{solo-owner root}.
\]

On the repaired side, the owner debt is zero and the paid row supplies a
positive-debt free player.  The same theorem gives all-Continue only, strict
descent, or a unique free debtor carrying the sole nontrivial root marginal.
Combining the two independent alternatives gives equation (8).  No logical
case is missing.

This combination should be described as a **refinement of the double-unique
cap branch**, not as a strict strengthening of the entire maximal-root
trichotomy.  The full maximal-root theorem and the prescribed-payoff theorem
operate on different root games and have different descendant data.

## 6. Cross-law equation (9)

The displayed algebra is correct provided the notation records the already
available source/repair law relation.  Let \(c\) be the probability that all
free players Continue in one root.  The quantitative free-absorption lower
bound gives \(c<1\).  Under the repaired stationary profile, absorption by a
nonempty free coalition occurs almost surely, and if \(\nu_R\) denotes its
terminal law, then

\[
\nu_S(\{o\})=c,
\qquad
\nu_S(Q\cup\{o\})=(1-c)\nu_R(Q).
\]

Together with \(b_o^S=u_o^R=b_o^R\), direct subtraction of the source
prescribed payoff gives

\[
d_o^S=(1-c)\sum_{Q\ne\varnothing}\nu_R(Q)
  \bigl(r_o(Q)-r_o(Q\cup\{o\})\bigr)
 +c\bigl(u_o^R-r_o(\{o\})\bigr).
\]

It remains only an average reward-toggle identity.  The note's limitations
paragraph is correct: it creates no root Nash condition, punishment-floor
edge, return, or rank.

## 7. Why this does not solve or renew the branch

A prescribed-payoff root with strict debt descent need not retain the
complete paid/reset source required for another iteration.

- Its fresh root absorption changes the complete terminal law.
- If its joint Continue mass is zero, the old positive incidence and paid row
  can disappear completely.
- If the joint Continue mass is positive, the old row and incidence are only
  inherited with a survival factor; no fixed lower bound or fresh reset
  dispatcher has been proved.
- The old exact cap roots are not roots against this new continuation cap.
- Strict decrease of the bounded real number \(D\) is not well founded.

Likewise, a solo-debtor root is only a finite face classification.  No theorem
turns the source solo-owner and repaired solo-debtor gates into one ordered
admissible chronology or a support-rank descent.

Therefore the strongest correct conclusion is the refinement

\[
\boxed{
\begin{array}{c}
\text{strict actual debt descent on at least one side},\quad\text{or}\\
\text{a source solo-owner gate},\quad\text{or}\\
\text{a repaired solo-debtor gate},\quad\text{or}\\
\text{all-Continue is unique at both prescribed payoff vectors.}
\end{array}}
\]

None of the four outputs currently has a closing consumer under the retained
fields.

## Effect on the maintained question

This result **does narrow** `FIN4_DOUBLE_UNIQUE_CAP_CLOSURE.md`: the paired
unique-cap configuration has the additional exact prescribed-payoff
classification above.  The question should record it as a supplied local
reduction so that future work does not stop after rediscovering the lifting
lemma or a nonrenewable strict debt drop.

It does not answer that question.  An acceptable completion must still:

- make strict descent renewable or compile it into a return;
- consume one of the solo-debtor gates; or
- contradict/consume uniqueness at both prescribed payoff vectors.

This is useful internal mathematics and a plausible small formalization
packet.  By itself it does not pass the export relevance gate because it
ends at four unconsumed alternatives and produces neither a terminal
consumer, a renewable rank, nor a positive-gap table.

## Declarations inspected

- `quittingRootContinuePayoff_update_add` and
  `quittingRootQuitPayoff_continuation_invariant`;
- `quittingTerminalSemanticDebt_prefix_eq_blockAct` and
  `quittingTerminalSemanticDebt_prefix_le`;
- `Math.SurvivalWeightedObstruction.Block.act_le_survival_mul_debt`;
- `quittingTerminalSemantic_minimum_stratum_alternative`;
- `FinFourSingletonBaseSameLawResetProducer.positiveDebtSupport_eq` and
  `.owner_gap`;
- the repaired-owner zero-debt theorem used by
  `exists_repairedPaidResetRegeneration`; and
- the maximal double-regeneration declarations in
  `FinFourPaidCapMaximalDoubleRegeneration.lean`.

