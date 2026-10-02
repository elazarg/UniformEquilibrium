# Independent review of the Fin5 literal-Never finite-cover barrier

Reviewer: `CODEX_EULER`

Target:
[`CODEX_RAMSEY__FIN5_FINITE_COVER_LITERAL_NEVER_SOURCE_BARRIER.md`](../notes/CODEX_RAMSEY__FIN5_FINITE_COVER_LITERAL_NEVER_SOURCE_BARRIER.md)

Verdict: **PASS as an internal ordinary-mathematics source barrier.**  I found
no mathematical repair to Theorem 3.3 or Proposition 4.1.  The result does not
meet the current export importance/consumer gate: it proves that the checked
quiet-source interfaces cannot by themselves produce the finite cover, but it
does not consume the surviving literal non-Never four-role source or close a
named conjecture chamber.

## Claim reviewed

For an actual profile `x` at which the candidate deleted player `w` already
plays literal Never, the note claims

\[
 \widehat q_w^w=d_w(x),\qquad
 \widehat q_i^w=d_i(x)+\kappa_i^w\quad(i\ne w),
\]

and therefore

\[
 \sum_i\widehat q_i^w
 =D(\operatorname{Sem}(x))+\sum_{i\ne w}\kappa_i^w.
\]

If `D_0` is the global carrier minimum, the finite-cover budget
`sum_i widehat q_i^w <= D_0` is consequently equivalent to `Sem(x)` already
lying in the minimum fiber and every survivor exposure `kappa_i^w` vanishing.
At that point the remaining cover-cardinality premise is exactly the desired
support-cardinality decrease.

Proposition 4.1 further claims that lowering survivor `i`'s reward only on a
coalition `T union {w}` preserves the complete literal-Never source interface
while making `kappa_i^w` arbitrarily large.  Its conclusion is deliberately
local: it does not preserve a global witness, a global minimum, or the
minimal-counterexample property.

## Verification of the exact cover formula

The definition of `g_i^w(x)` contains only terminal-law coefficients of
coalitions containing `w`: the non-singleton coefficients are
`mu_x(T union {w})`, and the remaining coefficient is `mu_x({w})`.  Literal
Never makes all of them zero.  Thus `g_i^w(x)=0` for every player, not merely
for survivors.

Semantic debts are nonnegative, and each `kappa_i^w` is a maximum containing
zero.  Hence the maxima defining `widehat q` disappear exactly as claimed.
Coordinatewise positivity of a sum of two nonnegative scalars also gives

\[
 C_w=\operatorname{supp}^{+}d(\operatorname{Sem}(x))
 \cup\{i\ne w:\kappa_i^w>0\}.
\]

No coupling inequality is being silently upgraded to equality here: the
equality is an equality for the *prospective conservative cover* at a source
which deletion leaves literally unchanged.

Global minimality supplies

\[
 D_0\le D(\operatorname{Sem}(x))
 \le D(\operatorname{Sem}(x))+\sum_{i\ne w}\kappa_i^w.
\]

Combining this with the prospective budget proves equality throughout.
Nonnegativity then forces every `kappa_i^w=0`; the converse is immediate.
This verifies both directions of Theorem 3.3 and the circularity diagnosis.

The expansion of `kappa_i^w=0` is also exact.  Because its finite maximum
contains zero, it vanishes precisely when

\[
 \bar r_i(T)\le r_i(\{w\})
 \quad(T\subseteq I\setminus\{w\})
\]

and

\[
 r_i(T)\le r_i(T\cup\{w\})
 \quad(\varnothing\ne T\subseteq I\setminus\{w\}).
\]

These are full table-face conditions, not consequences of small terminal
debt at the quiet source.

## Verification of the separation perturbation

Fix `i != w` and change only coordinate `i` of the reward at
`T union {w}`.  At `x`, that coalition is unreachable because `w` never
stops.  It remains unreachable after any unilateral deviation by a survivor,
because that deviation does not alter `w`'s law.  A deviation by `w` can make
the coalition reachable, but the changed coordinate is `i`, not the deviator's
coordinate `w`.  Therefore every prescribed payoff and every unrestricted
best-response cap at `x` is unchanged.  This argument genuinely includes
Never, finite or arbitrarily late pure times, randomized complete stopping
laws, and all behavioral deviations.

The deleted reward table and the literal terminal law are unchanged, while

\[
 \kappa_i^{w,r^L}\ge
 r_i(T)-r_i(T\cup\{w\})+L.
\]

Thus the local quiet-source data cannot bound the conservative exposure.
Doing this in distinct payoff coordinates separately inflates all survivor
exposures.

One formalization qualification should be retained.  A paid-row *existence
assertion* with observer `w` is preserved because all observer-`w` pure-time
payoffs, chronology, live mass, and edge gain are unchanged.  Across two
different reward tables it is not literally the same dependently typed
`QuittingPaidFirstDisagreementRow` object; it must be reconstructed.  The
generic division-free bound can be re-proved for the new table.  Also, the
global scalar `quittingRewardBound` itself need not stay equal after the row
perturbation.

## Scope that is not preserved

The note correctly excludes preservation of the global terminal witness and
the global debt minimum.  More explicitly, the perturbation also need not
preserve:

* a previously fixed numerical reward bound;
* punishment values or punishment-normality for survivor coordinates;
* absence of a uniform-equilibrium payoff;
* cardinal-minimal-counterexample status; or
* the hypotheses/output of the original literal non-Never four-role selector.

Accordingly Proposition 4.1 proves an interface separation for quiet and
restricted-equilibrium sources.  It is not a same-table counterexample to a
producer which is allowed to use the full global witness/minimum data.

## Source and novelty assessment

I compared the note with the conditional finite-cover theorem retained in
[`CODEX_EULER__FINITE_COVER_LITERAL_NEVER_DESCENT.md`](../notes/CODEX_EULER__FINITE_COVER_LITERAL_NEVER_DESCENT.md),
the definitions and coupling audit in `../NEVER_DELETION.md`, and the named
player-deletion/four-role interfaces cited by the author.  The finite-cover
consumer itself is prior reviewed mathematics.  The new content here is the
exact literal-Never collapse and the containing-face interface separation.

That content decisively rules out deriving the cover from only the currently
recorded quiet-source semantic pair, law/atom, observer-`w` paid row, and
deleted-game fields.  It does **not** rule out a producer at the actual
non-Never second half-reset source, where `g_i^w` may cancel `kappa_i^w`, and
it does not eliminate either inert cap-port residual.  I therefore recommend
retaining the result internally rather than exporting it for formalization at
this stage.

