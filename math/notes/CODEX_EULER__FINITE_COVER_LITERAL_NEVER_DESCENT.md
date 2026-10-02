# Finite-cover literal-Never debt-support descent

## Status

**PASS as an ordinary-mathematics conditional theorem.**  This note preserves
only the genuinely new finite-cover result from Sections 3 and 10 of
`../NEVER_DELETION.md`.  The source document contains duplicated and
superseded audits; they are not imported here.

The theorem is a real same-table, minimum-fiber support-rank consumer when its
finite hypotheses are supplied.  A narrow source search found no current
Fin5 four-role theorem that supplies its aggregate cover hypotheses, so it
does not close the four-role branch and is not presently an export candidate.

## 1. Data and definitions

Let `I` be finite, let `reward` be a quitting reward table with zero payoff on
the all-Never outcome, and let

\[
 x:(\text{quitting game}).\mathrm{BehaviorProfile}
\]

be an actual profile.  Fix `w in I` and let

\[
 y=x[w\leftarrow\mathrm{Never}].
\]

Write

\[
 d_i(x)=B_i(x)-U_i(x),\qquad D(x)=\sum_i d_i(x).
\]

Let `z_0` be a terminal-semantic carrier point globally minimizing total
debt, put

\[
 D_0=D(z_0),\qquad A_0=\{i:d_i(z_0)>0\},
\]

and assume `D_0>0` only when a nonempty maintained rank is desired.

Let `mu_x(S)` be the literal terminal-coalition law of `x`.  Extend reward to
the empty coalition by `bar r_i(emptyset)=0`, and define

\[
 m_i^w=\min_{T\subseteq I\setminus\{w\}}
       \bigl(\bar r_i(T)-r_i(\{w\})\bigr),
\]

\[
 g_i^w(x)=
 \sum_{\varnothing\ne T\subseteq I\setminus\{w\}}
 \mu_x(T\cup\{w\})
 \bigl(r_i(T)-r_i(T\cup\{w\})\bigr)
 +\mu_x(\{w\})m_i^w.
\]

For `i != w`, let

\[
 \kappa_i^w=\max\!\left(
 0,
 \max_{\varnothing\ne T\subseteq I\setminus\{w\}}
       [r_i(T)-r_i(T\cup\{w\})],
 \max_{T\subseteq I\setminus\{w\}}
       [\bar r_i(T)-r_i(\{w\})]
 \right).
\]

Finally define the prospective debt cover, now including the deleted player,

\[
 \widehat q_i^w=
 \begin{cases}
 \max\{0,d_w(x)-g_w^w(x)\},&i=w,\\[1mm]
 \max\{0,d_i(x)+\kappa_i^w-g_i^w(x)\},&i\ne w,
 \end{cases}
\]

and

\[
 C_w=\{i:\widehat q_i^w>0\}.
\]

All extrema are finite.  In the Fin5 application they range over the sixteen
subsets of the four-player complement of `w`.

## 2. Exact endpoint bounds

### Lemma 2.1 (prescribed payoff)

For every player `i`,

\[
 U_i(y)-U_i(x)\ge g_i^w(x). \tag{2.1}
\]

**Proof.**  Couple the complete stopping laws and replace only `w`'s stopping
time by infinity.  If an opponent stops before `w`, the outcome is unchanged.
If `w` ties the nonempty first coalition `T`, the outcome changes from
`T union {w}` to `T`.  If `w` is uniquely first, deletion exposes some later
coalition `T` in the complement, including the empty coalition if everyone
else plays Never.  The first two event classes give the displayed weighted
terms and the last is bounded by `m_i^w`.  These events exhaust the sample
space.  QED.

### Lemma 2.2 (unrestricted caps)

For every `i != w`,

\[
 B_i(y)-B_i(x)\le\kappa_i^w. \tag{2.2}
\]

For `i=w`,

\[
 B_w(y)=B_w(x). \tag{2.3}
\]

**Proof.**  Fix an arbitrary complete behavioral deviation of `i != w` and
use the same stopping-law coupling.  Every changed outcome is one of the two
classes included in `kappa_i^w`, so the deviating payoff increases by at most
that uniform constant.  Taking the supremum over all behavioral deviations
gives (2.2).  For `w`, unilateral replacement does not change the opponents,
so the entire optimization problem is identical, proving (2.3).  QED.

### Corollary 2.3 (finite debt cover)

For every `i`,

\[
 d_i(y)\le\widehat q_i^w. \tag{2.4}
\]

For `i != w`, subtract (2.1) from (2.2) in the exact debt identity.  For
`i=w`, (2.3) gives

\[
 d_w(y)=d_w(x)-[U_w(y)-U_w(x)]
        \le d_w(x)-g_w^w(x).
\]

Taking a maximum with zero is legitimate because semantic debt of an actual
profile is nonnegative.  Notice that no condition
`g_w^w(x) >= d_w(x)` is required: residual debt of `w` is allowed, provided
the entire prospective cover is small enough.

## 3. Finite-cover literal-Never descent theorem

Assume

\[
 \sum_{i\in I}\widehat q_i^w\le D_0 \tag{3.1}
\]

and

\[
 |C_w|<|A_0|. \tag{3.2}
\]

Then

\[
 D(\operatorname{Sem}(y))=D_0 \tag{3.3}
\]

and

\[
 \left|\operatorname{supp}^{+}d(\operatorname{Sem}(y))\right|
 <|A_0|. \tag{3.4}
\]

**Proof.**  By Corollary 2.3 and nonnegativity,

\[
 D(\operatorname{Sem}(y))
 \le\sum_i\widehat q_i^w\le D_0.
\]

The point `Sem(y)` belongs to the same terminal-semantic carrier because `y`
is a literal profile for the same reward table.  Global minimality of `z_0`
gives the reverse inequality, proving (3.3).

If `d_i(y)>0`, (2.4) forces `widehat q_i^w>0`.  Therefore

\[
 \operatorname{supp}^{+}d(\operatorname{Sem}(y))\subseteq C_w.
\]

Cardinality and (3.2) give (3.4).  QED.

This is a strict decrease of the maintained natural-valued rank
`card(support^+ d)` inside the global-minimum fiber.  No floor interpolation,
Bellman chronology, or cap-port restart is needed for the endpoint theorem.

## 4. Relation to the older deletion conditions

The earlier conditions

\[
 w\in A_0,\quad g_w^w(x)\ge d_w(x),\quad
 \sum_{i\ne w}q_i^w\le D_0,\quad
 q_j^w=0\ (j\notin A_0)
\]

imply (3.1)--(3.2): the first two force
`widehat q_w^w=0`, the inactive-coordinate conditions put the remaining cover
inside `A_0 setminus {w}`, and the old aggregate inequality is (3.1) with the
zero `w` term.

The new premises are formally weaker and permit all of the following at the
certificate level:

- `w` may be outside `A_0`;
- `w` may retain positive debt;
- an initially inactive coordinate may enter the prospective cover; and
- the target support need not be a subset of `A_0`.

The source document says without qualification that “the converse fails.”
No actual quitting-table regression establishing strict nonimplication under
all global-minimum hypotheses was supplied.  The safe statement is the one
above: the old hypotheses imply the new ones, while the displayed new scalar
conditions do not logically include the old coordinatewise requirements.
For example, abstract cover data can have `w notin A_0` and a smaller cover;
realizability by an actual positive-minimum quitting source is a separate
question.

## 5. Narrow producer/source audit

I inspected the following neighboring declarations.

1. `exists_twoMatchedHalfResets_or_firstExcessCharge` in
   `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/
   TerminalSemanticStoppingLawGlobalRetention.lean` supplies two literal
   half resets, positive transfer recipients, nonnegative first-target
   excess, and quarter retention in its two-reset arm.  It supplies no
   deletion payoff bound, cap-exposure bound, aggregate `widehat q` budget,
   or cover cardinality.
2. `exists_twoReset_fourRoleWindow_or_excessCharge` in
   `Research/Quitting/TwoResetFourRoleAdapter.lean` supplies an omitted label
   among at most four roles.  Omission is label incidence only; it gives no
   sign or aggregate control on that label's Never deletion.
3. `exists_omitted_transferDefectRole_or_sameProfileClockDebtCharge` and its
   terminal-Nash specialization in
   `UniformEquilibrium/Diagnostics/Quitting/
   OneActiveAlignedRankCollapse.lean` give either an omitted role or a
   clock-times-debt charge.  They require same-profile clock/debt alignment
   and do not bound `sum_i widehat q_i^w`.
4. `quittingTerminalSemanticDebtSum_le_card_mul_of_isEpsilonAsymptoticNash`
   gives `D(y) <= 5 epsilon` if the deletion endpoint itself is terminal
   `epsilon`-Nash.  The four-role output supplies no such Nash field.  For
   `epsilon < D_0/5` it would instead contradict global minimality.

No current `SparePlayerCancellation.lean` file was present in the searched
tree.  A draft mentioned in `../NEVER_DELETION.md` therefore cannot serve as
checked producer evidence.

## 6. Scope and disposition

The theorem is worth retaining because it is the sharp endpoint rank consumer
for any future producer of a small prospective cover.  It does not produce
such a cover from the Fin5 non-excess four-role output.  If (3.1)--(3.2) fail,
their negations are conservative-certificate failures, not actual semantic
branches; no terminal approximation, return, or rank descent follows.

Accordingly this note remains internal.  Export would be appropriate only
after a same-source Fin5 theorem actually produces the aggregate cover
hypotheses on a maintained branch, or after an explicit question accepts the
conditional finite-cover consumer by itself.

