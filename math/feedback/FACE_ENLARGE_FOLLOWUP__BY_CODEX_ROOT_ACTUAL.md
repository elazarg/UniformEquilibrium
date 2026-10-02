# Review of the actual `FACE_ENLARGE_FOLLOWUP.md`

Reviewer: Codex Root

## Verdict

**REVISE; the central handoff and paid-collision theorem are mathematically
promising and appear correct.  Do not export the submission wholesale yet.**

The new file is not the earlier duplicate of `COMP_b.md`.  Its principal new
content is an actual-profile construction:

1. solve the three-player deletion;
2. quietly lift it with the deleted helper playing literal Never;
3. choose a finite pure quitting time which is nearly best for the helper;
4. force the ambient gap to move to a surviving player; and
5. under a sharp solo-premium inequality, identify a positive-mass terminal
   collision financing the helper's gain.

This is stronger than the existing static deletion passport because it
retains the actual source, date, update, coalition, and unconditional stage
mass.  It remains a local producer, not a uniform-payoff proof.

## Sources inspected

- `UniformEquilibrium/Quitting/Classification/PlayerDeletionLift.lean`:
  `quittingTerminalPayoff_liftDeletedProfile`,
  `quittingDeletedDeviation`, and the survivor-deviation naturality theorem.
- `UniformEquilibrium/Quitting/Classification/PlayerReindex.lean` and
  `UniformEquilibrium/Quitting/Classification/ThreePlayer/Existence.lean`:
  three-player uniform-payoff existence.
- `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/ActualProfileTerminalGapPaidCap.lean`:
  pure-time extraction from an actual terminal-gap witness.
- `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticLiveWeightedCollisionTransfer.lean`:
  the live-weighted tail-excess/endpoint-gain dispatch, exact mover-debt
  subtraction, and routed stage-mass preservation.
- `UniformEquilibrium/Quitting/Classification/LCP/ThreeByThreeZeroDiagonalQ.lean`:
  `forward_or_reverse_orientation` for a zero-diagonal standard-Q,
  nonhomogeneous `3 x 3` matrix.
- `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/SupportThreeFourSignGraph.lean`
  and `FullSupportHardPrincipalDispatch.lean` for the current three-label sign
  and hard-principal interfaces.
- `notes/CODEX_CEDAR__OPERATIONAL_ESSENTIAL_SUPPORT_REDUCTION.md` for the
  already known quiet-lift outsider localization and exact full-gap pure-time
  witness.

## 1. Literal debt handoff

The proposition is valid.

Let `sigma` be the quiet lift of a terminal `epsilon`-Nash profile of the
three-player deletion, with `epsilon < gamma`.  Exact deletion naturality
makes every survivor's ambient debt at most `epsilon`.  The ambient terminal
gap therefore belongs to the deleted player `j`, so

\[
d_j(\sigma)\ge\gamma.
\]

Pure-time extremality permits a finite time `t` whose payoff is within
`delta` of `B_j(sigma)`.  It is finite because the `Never` point is the
currently prescribed strategy and has zero gain.  With
`tau=sigma[j <- Q_t]`, opponents are unchanged, hence

\[
B_j(\tau)=B_j(\sigma),
\qquad d_j(\tau)\le\delta,
\]

and

\[
U_j(\tau)-U_j(\sigma)
\ge d_j(\sigma)-\delta
\ge\gamma-\delta.
\]

Applying the ambient gap again to `tau`, player `j` cannot be selected when
`delta < gamma`; therefore a survivor has debt at least `gamma`.

This combines two facts which should be distinguished from the earlier Cedar
note.  Exact stopping-law disintegration can choose a finite pure time with
the full gap, but that time need not nearly attain the cap.  The present
near-best choice loses `delta` in gain and in exchange makes the helper debt at
the target at most `delta`.  That near-cap debt transfer is the useful new
interface.

The result does not use the blocker hypothesis.  It should first be stated
for an arbitrary deleted player whose survivor game has terminal
approximants, and only then specialized to the blocker-selected helper.

## 2. Paid collision under the solo-premium inequality

The calculation is correct.  Put

\[
f_j=\min\bigl(0,\min_{\varnothing\ne S\subseteq C}r_j(S)\bigr),
\qquad
\pi_j=r_j(\{j\})-f_j.
\]

At the selected finite date, exact pure-time transport gives

\[
\begin{aligned}
U_j(\tau)-U_j(\sigma)
={}&L_t\mu_t(\varnothing)
  \bigl(r_j(\{j\})-V_{t+1}\bigr)\\
&+\sum_{\varnothing\ne S\subseteq C}m_t(S)
  \bigl(r_j(S\cup\{j\})-r_j(S)\bigr).
\end{aligned}
\]

Since `V_{t+1} >= f_j`, the solo term is at most `pi_j`.  If
`pi_j < gamma` and `0 < delta < gamma-pi_j`, the collision sum is at least
`gamma-pi_j-delta`.  There are seven nonempty survivor coalitions, so one
literal atom satisfies

\[
m_t(S)\,[r_j(S\cup\{j\})-r_j(S)]
\ge {\gamma-\pi_j-\delta\over7}>0.
\]

The resulting mass lower bound through the join cap `c_j` is also valid once
the preceding inequality has established `c_j>0`.

For a two-player blocked face, the additional nonpositive margin against the
other outside singleton excludes that one coalition and changes the divisor
from seven to six, as claimed.

This is the strongest export candidate in the submission.  Its exact
quantifiers should be retained: for every suitable `epsilon` and `delta`, it
returns source-dependent `rho,sigma,tau,t,i,S`.  The final display (29) is too
informal about these quantifiers.

## 3. Collision consumer

Applying the checked live-weighted collision theorem to the literal profile
`tau`, literal date `t`, and literal nonsingleton terminal `S union {j}` is
legitimate.  Substitution of the mass floor gives the stated fixed tail-excess
or endpoint-gain scales.

The selected positive-defect endpoint mover is not `j`: positive gain of
`Q_t` over the Never continuation makes Quit strictly better than Continue at
that live row, while `j` already plays pure Quit there.  This should be proved
through the exact pure-time transport identity rather than asserted in prose.

The second update preserves the routed atom and subtracts its gain exactly
from the mover's unrestricted behavioral debt.  It does not prove total-debt
decrease, no support entry, a minimum-fiber endpoint, or a uniform payoff.

The phrase “literal two-edge chronology” should be replaced by “literal
source-matched profile-update chain.”  These are two counterfactual profile
updates at one selected date, not two successively reached Bellman rows in a
single play chronology.

The survivor debt of size `gamma` obtained after the first update is not used
by the collision dispatch as currently written.  It is extra source data and
should be retained explicitly, since it may help a downstream support or
role-selection consumer.

## 4. Passive-helper no-go

The matrix argument appears correct under the exact hard-residual
hypotheses.

If the deleted row is nonnegative outside its diagonal, standard-Q of the full
matrix restricts to standard-Q on the surviving principal: solve the full LCP
after extending `q_C` by `q_j=1`; positivity of row `j` forces `z_j=0`.
Likewise a homogeneous direction on the restriction extends to the full
matrix, so full nonhomogeneity passes to the restriction.

If the bad face has three players, the restriction is the strict-blocker face
itself and cannot be standard Q.  If it has two players, the three-player
restriction is zero diagonal, standard Q, and nonhomogeneous.  The checked
three-dimensional classification forces opposite strict signs on every
reciprocal pair, whereas the two-player strict blocker forces both entries of
its reciprocal pair to be negative.

Thus `r_j({j}) <= f_j` is impossible; in fact the proof works for every
outside player of the strict bad face, not only the helper selected by the
positive outside column.  The conclusion is strict positivity `pi_j>0`, not a
uniform lower bound in terms of `gamma`.

The final hard-residual split `pi_j >= gamma` versus the paid collision branch
is therefore valid but conditional on a fixed blocker face and helper, and it
does not consume the `pi_j >= gamma` arm.

## 5. Solved class beyond projective Q-bar

The example correctly indicates a class strictly larger than projective
Q-bar: a table may have a dispensable player whose three-player deletion has
a uniform payoff even though the normalized singleton matrix has a bad
two-player principal.

For export, the example must define a complete reward table rather than only
the singleton matrix and player `2`'s nonsingleton coordinates.  One simple
presentation is to set every own singleton baseline, all missing singleton
coordinates, and every unspecified nonsingleton payoff explicitly, then
verify:

1. the normalized singleton matrix is exactly the displayed matrix;
2. the face `{0,1}` is not projective Q;
3. player `2` satisfies the exact `QuittingBlockDispensable` fields; and
4. the checked block-deletion theorem plus three-player existence yields the
   ambient uniform payoff.

The most reusable theorem is not the particular table: it is the general
dispensable-player extension of the three-player class, together with one
fully specified rational witness proving strict noncontainment in projective
Q-bar.

## Required revisions and review gate

Before export:

1. state the general deleted-player near-best debt-handoff theorem separately
   from blocker selection;
2. package the actual paid collision with all `epsilon,delta` quantifiers and
   the surviving full-gap debtor;
3. replace “chronology” by the correct profile-update language;
4. prove `q != j` explicitly from pure-time transport;
5. state the exact full-matrix standard-Q and nonhomogeneous hypotheses in the
   passive-helper no-go;
6. fully specify the rational enlargement witness; and
7. distinguish the remaining `pi_j >= gamma` residual from a consumed branch.

Because the handoff and collision packet quantify over unrestricted
behavioral debt and claim source-exact provenance, they require an independent
falsification review before export.  The passive-helper no-go and strict
projective-Q-bar enlargement should also be reviewed independently, preferably
separately from the semantic handoff.

