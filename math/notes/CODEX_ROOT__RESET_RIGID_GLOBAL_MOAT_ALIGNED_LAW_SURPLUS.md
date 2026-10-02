# Reset-rigid global moat localizes on the retained law

Status: proved ordinary mathematics from checked carrier and moment identities;
not a terminal consumer.  The result strengthens the reset-rigid chamber by
putting the singleton premium, positive opponent incidence, and strict toggle
on one retained-law atom, except for one explicit Never alternative.

## Question

Let \((X,\mu)\) be a positive global minimum of terminal semantic debt in a
finite quitting game.  Suppose player \(o\) has zero debt at \(X\).  Can the
global singleton moat be aligned with the *given* law \(\mu\), rather than
with an independently selected reward-moment representation?

The answer is yes.

## Exact retained-law alternative

Write

\[
 D_*:=D(X)>0,
 \qquad s_o:=r_o(\{o\}).
\]

Assume

1. \((X,\mu)\) belongs to the joint terminal-semantic/law carrier;
2. \(X\) globally minimizes total terminal semantic debt;
3. \(d_o(X)=0\); and
4. the game has a terminal exploitability witness.

Then one of the following holds.

1. **Never certificate.**  The retained law has positive Never mass and
   \[
   s_o\le -D_*.
   \tag{1}
   \]

2. **Aligned finite atom.**  There are a nonempty terminal coalition \(S\)
   and a player \(j\ne o\) such that
   \[
   \mu(S)>0,\qquad j\in S,
   \qquad r_o(S)-r_o(\{o\})\ge D_*.
   \tag{2}
   \]
   Moreover the same coalition has a strict membership-toggle blocker:
   either one member strictly prefers to leave it or one outsider strictly
   prefers to join it.

Thus the finite branch uses one literal coordinate of the already retained
law.  It does not select an unrelated moment representation, and the atom
carrying the owner premium itself has positive opponent incidence relative to
the zero-debt owner.

The statement applies in particular to the `returned` point and unchanged
law stored by `QuittingLawTightResetRigidChamber`, after transferring global
minimality from the chamber origin by the same two inequalities used in
`GLOBAL_MINIMUM_SINGLETON_MOAT_AND_FIN4_TWO_CHAMBER_REDUCTION.md`.

## Proof

Joint carrier membership gives the exact reward-moment identity

\[
 X^u_o=\sum_{\omega}\mu(\omega)r_o(\omega),
 \tag{3}
\]

where the reward at Never is zero, and \(\sum_\omega\mu(\omega)=1\).

The checked global-minimum singleton margin gives

\[
 D_*\le X^B_o-s_o.
 \tag{4}
\]

Since \(d_o(X)=X^B_o-X^u_o=0\), equations (3)--(4) imply

\[
 D_*\le
 \sum_\omega \mu(\omega)\bigl(r_o(\omega)-s_o\bigr).
 \tag{5}
\]

The outcome set is finite.  Hence some outcome \(\omega\) in the positive
support of \(\mu\) satisfies

\[
 r_o(\omega)-s_o\ge D_*.
 \tag{6}
\]

If \(\omega\) is Never, then its reward is zero and (6) is exactly (1).
Otherwise \(\omega=S\) is a nonempty terminal coalition.  It cannot be
\(\{o\}\), because that outcome has surplus zero while \(D_*>0\).  Therefore
\(S\) contains some \(j\ne o\), whether or not it also contains \(o\), and
(2) follows.  Finally, the terminal exploitability witness says that every
nonempty pure terminal coalition has a strict member-leave or outsider-join
toggle blocker.  Apply it to this same \(S\).

## Quantitative support refinement

Assume a reward bound \(|r_i(S)|\le M\), with \(M>0\).  Equation (5) also gives a weighted
version.  Put

\[
 P=\{\omega:r_o(\omega)-s_o>0\}.
\]

Then

\[
 D_*\le
 \sum_{\omega\in P}\mu(\omega)
       \bigl(r_o(\omega)-s_o\bigr)
 \le 2M\,\mu(P).
\]

Consequently \(\mu(P)\ge D_*/(2M)\).  Splitting \(P\) into Never and finite
outcomes yields either

\[
 \mu(\mathrm{Never})\,(-s_o)\ge D_*/2
\]

or a finite coalition \(S\ne\{o\}\) with

\[
 \mu(S)\bigl(r_o(S)-s_o\bigr)
 \ge \frac{D_*}{2(2^{|I|}-1)}.
 \tag{7}
\]

For Fin4 the denominator in (7) is \(30\).  This product form is the useful
chronological scale: causal realization of the retained law preserves a
fixed amount of owner premium times atom mass, even when neither factor is
separately maximized.

## What this repairs

`exists_fixedLaw_dispatch_and_sourceAggregate` deliberately keeps its source
aggregate-surplus outcome separate from the reset target's incidence atom.
That separation is necessary at its stated generality because its `source`
and `target` can be different points.  At the law-tight global-minimum face,
however, the reset return itself is globally minimizing and its prescribed
coordinate is represented by its stored law.  The argument above can
therefore use that exact law and removes the separation.

## Remaining boundary

This is not yet an executable reset transition.

- The strict toggle at \(S\) need not belong to the zero-debt owner.
- Purifying or toggling the reached atom can change other players' unrestricted
  caps and leave the minimum fibre.
- The Never alternative (1) is not presently inconsistent with punishment
  normality; it says only that the owner's singleton and punishment floor can
  be uniformly negative.
- Law convergence supplies causal access to the atom but does not make the
  reached row cap--Nash.

The next concrete question is whether the finite branch's product floor (7),
together with zero owner debt and the hard supported toggle on the same atom,
forces either the macroscopic nonexact seam already identified by the
source-faithful capacity account or a same-law successor preserving all
previous zero debts.  The Never branch should be attacked separately as a
negative-singleton punishment chamber.

## Checked sources inspected

- `minimumTerminalSemantic_singletonMargin` in
  `TerminalSemanticAuxiliaryNashBudget.lean`;
- `terminalSemanticLawCarrier_rewardMoment` and the simplex law fields used
  throughout `TerminalSemanticMinimumAggregateSurplusConsumer.lean`;
- `QuittingTerminalExploitabilityWitness.terminalCoalition_has_strictToggle`
  in `TerminalSemanticMinimumAggregateSurplusConsumer.lean`;
- `QuittingFixedLawResetDispatch` and
  `exists_fixedLaw_dispatch_and_sourceAggregate` in
  `TerminalSemanticResetIncidenceCapReturn.lean`; and
- `QuittingLawTightResetRigidChamber` in
  `LawTightCapNashStrictMinimum.lean`.
