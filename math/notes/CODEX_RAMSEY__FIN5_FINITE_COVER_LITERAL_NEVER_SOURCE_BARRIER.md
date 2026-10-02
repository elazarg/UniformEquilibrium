# Fin5 finite-cover descent: the literal-Never source barrier

**Author:** CODEX_RAMSEY  
**Status:** independently reviewed PASS; internal source barrier  
**Date:** 2026-08-25  
**Head audited:** `fed7258`

**Independent review:**
[`CODEX_EULER`](../feedback/CODEX_RAMSEY__FIN5_FINITE_COVER_LITERAL_NEVER_SOURCE_BARRIER__BY_CODEX_EULER.md)

## 1. Question and answer

The finite-cover consumer in
[`CODEX_EULER__FINITE_COVER_LITERAL_NEVER_DESCENT.md`](CODEX_EULER__FINITE_COVER_LITERAL_NEVER_DESCENT.md)
is genuinely stronger than the older coordinatewise deletion certificate.  Its
prospective cover is

\[
 \widehat q_w^w=\max\{0,d_w(x)-g_w^w(x)\},\qquad
 \widehat q_i^w=\max\{0,d_i(x)+\kappa_i^w-g_i^w(x)\}\quad(i\ne w),
\]

and it asks for

\[
 \sum_i\widehat q_i^w\le D_0,
 \qquad
 |\{i:\widehat q_i^w>0\}|<|A_0|.                 \tag{1.1}
\]

Here `D_0` is the global minimum of terminal semantic debt and `A_0` is the
positive-debt support of a selected minimum.

This note asks whether the actual Fin5 interfaces produce (1.1) on one
literal source.  The answer is sharp and negative for every currently
available quiet/restricted-equilibrium source:

> If `w` is already literal Never at `x`, then the aggregate inequality in
> (1.1) holds **only if** `Sem(x)` is already a global minimizer and every
> survivor exposure `kappa_i^w` is zero.  Under those conditions the cover
> cardinality inequality is exactly the desired support-rank conclusion.

Thus the finite-cover test is a nontrivial cancellation criterion only at a
source where `w` can actually stop.  Applying it after quiet lift, or after
the final Never deletion, is circular as a rank producer.  The literal
four-role source is the only remaining possible input, and its checked output
contains no estimate of the required removal exposures or gains.

This is a source barrier, not a counterexample to the conjecture and not a
counterexample to the conditional finite-cover theorem.

## 2. Sources and scope inspected

The bounded source audit used:

1. `exists_twoMatchedHalfResets_or_firstExcessCharge` in
   `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/
   TerminalSemanticStoppingLawGlobalRetention.lean`;
2. `exists_twoReset_fourRoleWindow_or_excessCharge` in
   `Research/Quitting/TwoResetFourRoleAdapter.lean`;
3. `MinimalFinQuittingCounterexample.exists_uniformEquilibriumPayoff_of_card_lt`
   and `properRestriction_exists_uniformEquilibriumPayoff` in
   `UniformEquilibrium/Diagnostics/Quitting/MinimalFinCounterexample.lean`;
4. `quittingTerminalPayoff_liftDeletedProfile`,
   `quittingBestReplyValue_liftDeletedProfile`, and
   `quittingTerminalPayoff_update_liftDeletedProfile_eq_deleteDeviation` in
   `UniformEquilibrium/Quitting/Classification/PlayerDeletionLift.lean`;
5. the reviewed source analyses
   [`CODEX_EULER__FIN5_RESTRICTED_EQUILIBRIUM_FROZEN_SOURCE_SEPARATION.md`](CODEX_EULER__FIN5_RESTRICTED_EQUILIBRIUM_FROZEN_SOURCE_SEPARATION.md)
   and
   [`CODEX_EULER__FIN5_QUIET_WHOLE_LAW_ATOM_PAID_CONNECTOR.md`](CODEX_EULER__FIN5_QUIET_WHOLE_LAW_ATOM_PAID_CONNECTOR.md).

All debts and caps below use unrestricted complete behavioral deviations.
No stationary reduction is made.

## 3. Literal-Never collapse of the prospective cover

Let `x` be any actual behavioral profile and suppose that player `w` plays
literal Never.  Put `y=x[w<-Never]`; literally `y=x`.

### Lemma 3.1 (deletion gain vanishes)

For every player `i`,

\[
                         g_i^w(x)=0.                 \tag{3.1}
\]

Indeed the terminal law of `x` assigns zero mass to every coalition
containing `w`, including the singleton `{w}`.  Every coefficient occurring
in the definition of `g_i^w(x)` is therefore zero.  Equivalently, the actual
prescribed-payoff change under the deletion is zero because the profile did
not change.

### Proposition 3.2 (exact cover formula)

For a literal-Never source,

\[
 \widehat q_w^w=d_w(x),\qquad
 \widehat q_i^w=d_i(x)+\kappa_i^w\quad(i\ne w),     \tag{3.2}
\]

and hence

\[
 \sum_i\widehat q_i^w
   =D(\operatorname{Sem}(x))+\sum_{i\ne w}\kappa_i^w,               \tag{3.3}
\]

\[
 C_w=\operatorname{supp}^{+}d(\operatorname{Sem}(x))
       \cup\{i\ne w:\kappa_i^w>0\}.                \tag{3.4}
\]

The debts and every `kappa_i^w` are nonnegative, so the maxima in the
definition of `widehat q` do nothing after (3.1).  Equations (3.3)--(3.4)
follow coordinatewise.

### Theorem 3.3 (quiet-source barrier)

Let `z_0` be a global minimum with debt `D_0`.  At a literal-Never source
`x`,

\[
 \sum_i\widehat q_i^w\le D_0                              \tag{3.5}
\]

holds if and only if

\[
 D(\operatorname{Sem}(x))=D_0
 \quad\text{and}\quad
 \kappa_i^w=0\quad\forall i\ne w.                        \tag{3.6}
\]

**Proof.**  Global minimality gives
`D_0 <= D(Sem(x))`.  Equation (3.3) and nonnegativity of every `kappa`
therefore give

\[
 D_0\le D(\operatorname{Sem}(x))
      \le D(\operatorname{Sem}(x))+\sum_{i\ne w}\kappa_i^w.
\]

If (3.5) holds, equality holds throughout, proving (3.6).  Conversely (3.6)
and (3.3) give (3.5).  QED.

Under (3.6), (3.4) reduces to

\[
 C_w=\operatorname{supp}^{+}d(\operatorname{Sem}(x)).      \tag{3.7}
\]

Consequently the second finite-cover premise

\[
 |C_w|<|A_0|                                               \tag{3.8}
\]

is then literally the desired minimum-fiber support-rank decrease.  The
finite-cover theorem remains useful before deletion, but at an already
Never source (3.5)--(3.8) do not produce the descent: they assume it, together
with the extra table-wide condition `kappa=0`.

For clarity, `kappa_i^w=0` is not a small-error consequence.  Expanding its
finite definition, it is equivalent to the simultaneous table inequalities

\[
 \bar r_i(T)\le r_i(\{w\})
       \quad\forall T\subseteq I\setminus\{w\},
 \qquad
 r_i(T)\le r_i(T\cup\{w\})
       \quad\forall\varnothing\ne T\subseteq I\setminus\{w\}.      \tag{3.9}
\]

Thus the quiet-source budget requires, for every survivor, both domination
of every complement outcome by the singleton-`w` payoff and no loss when `w`
is adjoined to any nonempty complement coalition.  Neither condition appears
in the quiet-lift or four-role records.

## 4. Why quiet lifts cannot supply the missing condition

The obstruction is not merely absence of a named declaration.  The survivor
exposures are invisible to the complete quiet-source semantic data.

### Proposition 4.1 (containing-`w` row-face freedom)

Assume `I\{w}` is nonempty, let `x_w=Never`, fix `i ne w`, a nonempty
`T subset I\{w}`, and `L>0`.  Form a new reward table `r^L` by changing only
player `i`'s payoff at the coalition `T union {w}`:

\[
 r_i^L(T\cup\{w\})=r_i(T\cup\{w\})-L.               \tag{4.1}
\]

Then all of the following remain exactly unchanged at `x`:

* the complete stopping laws and every chronological atom;
* every prescribed terminal payoff `U_j(x)`;
* every unrestricted best-response cap `B_j(x)`;
* the entire terminal semantic pair and its debt support;
* the reduced game obtained by deleting `w`; and
* every paid-row assertion whose observer is `w`, after reconstructing the
  same numerical row witnesses for the new reward-table type.

For `j ne w`, no unilateral deviation changes `w`'s literal-Never law, so no
outcome containing `w` is reachable in the calculation of `B_j(x)`.  For
`j=w`, the changed reward coordinate is `i`, not `w`, so `B_w(x)` is also
unchanged.  This proves the semantic assertions, including unrestricted
deviations.

On the other hand,

\[
 \kappa_i^{w,r^L}\ge
 r_i(T)-r_i(T\cup\{w\})+L,                           \tag{4.2}
\]

so this one prospective-cover coordinate can be made arbitrarily large
without changing any of the listed source fields.  Repeating the construction
in distinct payoff coordinates inflates all four Fin5 survivor exposures.

This is an exact same-profile interface separation.  It deliberately does
not claim that the perturbed table retains a global terminal witness or the
same global minimum; those are nonlocal properties of the whole table.
Rather, it proves that the local quiet-lift, atom, paid-row, and deleted-game
interfaces contain no hidden control of `kappa`.

The reconstruction qualification is type-theoretic as well as mathematical:
a paid-row record is dependent on the reward table and hence is not literally
the same term after perturbation.  The observer's roots and payoff coordinate
are unchanged, so its chronology, edge identity, and gain rebuild verbatim;
the canonical `quittingRewardBound` may change and its generic bound is
reproved for the new table.  The perturbation is not asserted to preserve
punishment values, punishment normality, absence of a uniform payoff,
cardinal-minimal-counterexample status, a fixed reward-bound constant, the
global witness/minimum, or a four-role selector.

## 5. Comparison with the actual Fin5 producer interfaces

### 5.1 Cardinal-minimal restricted equilibria

Deleting a preselected `w` from a cardinal-minimal Fin5 table and quietly
lifting a reduced `epsilon`-Nash profile makes `w` literal Never.  The checked
deletion naturality gives survivor debts at most `epsilon`, while the ambient
terminal-gap witness localizes a full-gap debt and finite paid row to `w`.
These are strong co-realized facts, but Theorem 3.3 applies immediately:
the finite-cover aggregate premise at this same source would additionally
require that the source already lie in the global minimum fiber and that all
four `kappa_i^w` vanish.  Neither follows from reduced-game equilibrium.

The containing-`w` row faces do not even occur in the reduced reward table.
Proposition 4.1 explains why the exact player-deletion transport theorems
cannot recover their signs.

### 5.2 Quiet whole-law interpolation

The reviewed whole-law connector retains a chronological four-survivor atom
and localizes the ambient paid row to `w`, all on one mixed profile.  It too
keeps `w` literal Never.  Therefore its prospective cover is exactly
(3.2), not a small perturbation of the cover at the original four-role
source.  The retained atom gives positive mass on coalitions avoiding `w`;
it supplies no inequality `kappa_i^w=0` on the opposite containing-`w`
faces.

### 5.3 Literal four-role source

At the second literal half-reset profile `x_2`, the omitted label is unchanged
by the two selected updates but need not play Never.  Thus nonzero deletion
gain `g_i^w(x_2)` can in principle cancel `kappa_i^w`, and the finite-cover
criterion is genuinely noncircular there.

However, `exists_twoReset_fourRoleWindow_or_excessCharge` returns only the
two update identities, positive transfer recipients, an omitted label, and
quarter retention of original chronological atoms.  It returns no payoff
comparison on any pair `T,T union {w}`, no aggregate deletion budget, and no
cover cardinality.  The reduced equilibrium and whole-law constructions
reselect a profile with `w=Never`; they cannot be used to estimate the
`g/kappa` balance back at `x_2` without a source-matching theorem.  The
reviewed frozen-source separation shows that such reselection can reverse
the omitted player's debt by the full terminal gap.

## 6. Strongest surviving producer statement

The new finite-cover theorem narrows the original source question as follows.

* On the actual non-Never four-role source, one still needs a new theorem
  producing either the conservative `g/kappa` aggregate cover, or direct
  control of the exact endpoint debts
  `d_i(x_2[w<-Never])`, together with a smaller prospective cover.
* Passing first to any currently checked quiet/restricted-equilibrium source
  cannot supply it.  There the aggregate cover condition is equivalent to
  global-minimum membership plus four table-wide zero-exposure identities,
  and its cardinal condition is already the desired descent.

The minimal missing implication is therefore not another deletion consumer:

> **Missing source-matched producer.**  At the literal second half-reset
> profile, select an omitted label whose actual prescribed-payoff gains cancel
> its containing-face cap exposures in aggregate and leave a prospective
> support smaller than the selected minimum support.

No checked four-role, cardinal-minimal deletion, or quiet whole-law theorem
provides this implication.  Conversely, no full minimal-counterexample
regression is claimed: constructing one would decide the conjecture
negatively.

## 7. Disposition

Theorem 3.3 and Proposition 4.1 are independently reviewed exact
ordinary-mathematics barriers.  They remain internal because they explain why the new
finite-cover consumer does not combine with the current Fin5 quiet-source
machinery, while leaving open the only noncircular route at the literal
non-Never four-role source.
