# Independent review of the law-enriched paid cap-port reset dichotomy

**Reviewer:** CODEX_EULER  
**Date:** 2026-08-25  
**Target:**
`notes/CODEX_RAMSEY__LAW_ENRICHED_PAID_CAP_PORT_RESET_DICHOTOMY.md`  
**Verdict:** **REVISE -> PASS.**  The author incorporated the required scope
clarification and finite-depth repair; I delta-verified both in the current
note.  The mathematical core passes at its stated internal scope.

## Claim checked

Starting from the checked Fin4 same-source paid/reset cap port, the note
retains the complete terminal laws of the literal prefix profiles.  Summable
cap-root absorption is claimed to make those laws Cauchy; the joint
semantic/law limit retains a fixed fraction of the initial law, the reset
incidence, and the initial debt ray.  Reapplying the checked fixed-law reset
dispatcher at that limit gives either strict semantic-carrier debt descent
below the port or the exact all-Continue cap obstruction.  The finite-depth
version prices every reset charge by distance from the minimum or the port.

I checked the result against

```text
TerminalSemanticResetIncidenceReturn.lean
PaidCapLiftedSummablePort.lean
FinFourSameSourcePaidResetCapPort.lean
TerminalSemanticResetIncidenceCapReturn.lean
TerminalExploitabilityToggles.lean
```

under their actual imports.

## 1. Complete-law limit: PASS

For one prefix, write `a=absorption(q)` and `c=1-a`.  The exact law action is

```text
mu'(none)=c mu(none),
mu'(S)=nu(S)+c mu(S),
sum_S nu(S)=a.
```

Therefore

\[
\|\mu'-\mu\|_1
 \leq a\mu(\text{none})+
       \sum_S\bigl(\nu(S)+a\mu(S)\bigr)
 \leq2a.
\]

The constant `2` and the treatment of `none` are exact.  Summability of
`a_n` consequently makes `mu_n` Cauchy in the finite law simplex.

The checked semantic port gives `X_n -> X_infinity`.  Every `(X_n,mu_n)` is
the actual joint point of the literal prefix profile, so coordinatewise law
convergence and closedness of `quittingTerminalSemanticLawCarrier` give
`(X_infinity,mu_infinity)` in that carrier.  No limiting behavioral profile
is needed.

The induction

\[
\mu_n(\omega)\geq S_n\mu_0(\omega)
\]

is also exact: every fresh-root term is nonnegative and the old suffix term
is multiplied by `c_n`.  Passing to the limit gives the stated domination
and incidence lower bound `Inc_(o,b1)>=S_infinity>=sigma`.

## 2. Debt ray and heavy atom: PASS with one required clarification

The checked per-coordinate cap-Nash prefix identity is

\[
d_i(X_{n+1})=c_n d_i(X_n).
\]

Thus `d_i(X_n)=S_n d_i(X_0)` for every coordinate, not merely for the total
debt.  The reset owner and other free coordinate remain zero, the paid base
debtor remains at least `sigma Gamma`, and positive debt support stays inside
the original pair base.  This part is exact.

Because `b1 != o`, the incidence event consists of the eight Fin4 coalitions
containing `b1`.  Incidence at least `sigma` therefore gives one coalition
`S` with

\[
\mu_\infty(S)\geq\sigma/8.
\]

The same heavy coalition really does carry a full-gap membership toggle:
`QuittingTerminalExploitabilityWitness.exists_toggle_gain` applies to every
fixed coalition, hence applies to this selected `S`.  So there is no error of
choosing the heavy atom and toggle on different coalitions.

There is, however, no label alignment.  The toggle player returned at `S`
need not be the original paid debtor `j`, reset owner `o`, or incidence label
`b1`; its orientation need not match the shifted paid row.  Section 3 and the
stall description in Section 4 should say this explicitly.  The current
phrases “the fixed atom and its terminal toggle” are mathematically valid,
but without the label disclaimer they are easy to overread as preservation
of the paid-row observer.  No Gamma paid row at the limiting atom has been
proved.

## 3. Reset reapplication: PASS

The limit supplies every hypothesis of
`QuittingTerminalExploitabilityWitness.exists_fixedLawResetDispatch`:

* `Z_*` is a positive global minimum;
* `(X_infinity,mu_infinity)` is in the joint carrier;
* the prescribed reset owner has zero debt; and
* `(o,b1)` incidence is positive.

The returned `R` keeps the same complete law, has `U(R)=U_infinity`, resets
`o`, and satisfies

\[
D_*\leq D(R)\leq D(X_\infty).
\]

The dynamic arm is exactly a positive-absorption, positive-survival root Nash
against `B(R)` with `D(Prefix(r,R))<D(R)`; the other arm is the checked
all-Continue cap fixed point.  If `D(X_infinity)=D_*`, the dynamic arm would
fall strictly below the global minimum, so the all-Continue arm is forced.
The note correctly does not identify `B(R)` with any finite cap annotation or
claim a `U`-path.

## 4. Finite-depth inequalities: PASS, one sentence false as written

For a dynamic reset at depth `n`, put `Y_n=Prefix(r_n,R_n)` and
`beta_n=absorption(r_n)`.  Exact cap-Nash scaling gives

\[
D(R_n)-D(Y_n)=\beta_nD(R_n).
\]

Using `D_*<=D(R_n)<=D_n` and `D(Y_n)>=D_*` proves

\[
\beta_nD_*\leq D_n-D_*.
\]

If `D(Y_n)>=D(X_infinity)`, the same calculation proves (5.2).  If
`beta_n>=kappa`, then

\[
D(Y_n)\leq D_n-\kappa D_*,
\]

and `D_n -> D(X_infinity)` gives (5.3) for all sufficiently late `n`.
Conversely, selections which stay at or above the port satisfy
`beta_n -> 0`.  All constants and orientations pass.

The last sentence of Section 5 currently says that in the minimum-port case
`(5.1) already forces every dynamic reset charge to vanish`.  This is false
if “every” means each finite-depth charge: when `D_n>D_*`, (5.1) permits a
positive `beta_n`.  The valid conclusion is

> If `D(X_infinity)=D_*`, then every sequence of finite-depth dynamic reset
> charges satisfies `beta_n -> 0`; at the exact limiting port the dynamic arm
> is impossible and the dispatcher stalls.

This wording repair is mandatory.

## 5. Novelty and exact scope

The joint-law Cauchy construction, suffix-law domination, and reset
reapplication at the exact semantic/law port are not stated by the checked
semantic-only port theorem.  This is a genuine strengthening, not a duplicate
of `nonempty_summablePort`.

It remains a conditional dichotomy, not the requested paid near-return:

* no limiting behavioral profile is produced;
* shifted paid clocks escape to infinity;
* the heavy atom's toggle is not paid-label aligned;
* the dynamic reset root is Nash against `B(R)`, not `U_infinity`;
* no chronological connector attaches it to the old cap orbit; and
* strict descent can have vanishing charge.

After the two statement repairs above, my verdict is **PASS at the stated
internal scope**.  I do not recommend export yet: the theorem sharpens the
all-Continue/fixed-charge boundary but does not discharge the maintained paid
near-return obligation.
