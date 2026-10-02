# Review of the vanishing-response maximal-root trichotomy

Identity: `REROOT_REVIEW`  
Date: 2026-08-31  
Verdict: **PASS**, with two small statement-level repairs recommended before
export.  The result is a genuine reduction of the vanishing-response
rectangle branch.  It is not a consumer of the full-debt chamber.

## Claim reviewed

I reviewed the linked argument in

- `notes/CODEX_GATE__MAXIMAL_TARGET_CAP_REROOT_TRICHOTOMY.md`; and
- `notes/CODEX_GATE__VANISHING_RESPONSE_MAXROOT_RESET_TRICHOTOMY.md`.

The principal claim is that, after selecting at each literal low-debt
rectangle endpoint a maximum-absorption exact cap--Nash product root, one has
an exhaustive source-level alternative:

1. a cofinal subsequence of uniformly charged literal exact prefixes;
2. an exact minimum-fibre endpoint which, in the Fin4 hard residual, enters
   the existing reset-rigid chamber; or
3. a two-level inert endpoint which, in the Fin4 hard residual, is strictly
   off the global minimum fibre.

The note also claims exact debt and signed-atom scaling under the fresh root,
and proves that the sign of the displayed rectangle atom alone does not in
general put positive opponent incidence on the low-debt endpoint.

## Checks performed

I inspected the exact statements and nearby proofs of:

- `QuittingStoppingLawVanishingDebtRectangleSequence` in
  `StoppingLaw/OffDiagonal/AtomRectangleSequenceAlternative.lean`;
- `QuittingStoppingLawRectangleResetFaceDispatch`,
  `nonempty_resetFaceDispatch`, `QuittingStoppingLawRectangleJointAtomLimit`,
  and `nonempty_jointAtomLimit` in
  `StoppingLaw/Endpoint/RectangleResetFaceMinimizer.lean`;
- `quittingTerminalSemanticDebt_prefix_eq_continueMass_mul_of_capNash` in
  `TerminalCapNashEndpointTransport.lean`;
- `quittingTerminalPayoffDifferenceAtom_literalRootStack` in
  `StoppingLaw/ContinuePrefixAtomAccess.lean`;
- `exists_positive_finiteLawAtom_of_finFourHardResidual_minimum` in
  `TerminalSemanticFinFourMinimumLawFiniteAtom.lean`;
- `terminal_eq_singleton_of_totalOpponentIncidence_eq_zero_of_mass_pos`,
  `exists_quittingLawTightResetRigidChamber`, and the reset-rigid structure in
  `LawTightCapNashStrictMinimum.lean`;
- `terminalSemanticLaw_singletonNever_zeroDebt_cap_eq_singletonReward` in
  `TerminalSemanticSingletonNeverCapTightness.lean`; and
- `minimumTerminalSemantic_singletonMargin` in
  `TerminalSemanticAuxiliaryNashBudget.lean`.

I also checked the exact table calculations in the negative-orientation
regression and the small-fork inert-tube argument in the linked maximal-root
note.

## Validity of the maximal-root ledger

The exact-root set at a fixed cap is nonempty.  On the finite product of
binary probability simplices it is closed, hence compact, and absorption is
continuous.  Therefore maximum absorption is attained.  This compact argmax
is ordinary mathematics; the notes correctly do not claim an existing Lean
declaration packaging it.

For any selected exact root, not only a maximizer, the checked coordinatewise
identity gives

\[
d_i(\widehat R_n)=s_n d_i(R_n),\qquad
D(\widehat R_n)=s_nD_n.
\]

Carrier closure and global minimality then give

\[
a_nD_n\le D_n-D_*,\qquad s_n\ge D_*/D_n.
\]

For Fin4, `D_n <= 8M` follows from the reward box, so the claimed survival
floor and the constant

\[
\frac{cD_*}{32M}
\]

in the retained signed-atom inequality are correct.  Prefixing the same root
to the endpoint and sibling makes all newly absorbed law cancel; the old
signed atom is multiplied by exactly `s_n`.

The first recommended repair is simply to state explicitly that `M>0` before
dividing by it.  This follows automatically from `D_*>0` and `D_n<=8M`, but
is currently implicit.  Likewise, an export may either retain
`K = card(QuittingTerminalOutcome (Fin 4))` or record the elementary
calculation `K=16`; no mathematical issue depends on this simplification.

## Validity and quantifiers of the trichotomy

The sequence split is correct.  For the nonnegative sequence `a_n`, failure
of convergence to zero is equivalent to the existence of a strict
subsequence with `a_n >= eta` for some `eta>0`.  On that subsequence,
`a_nD_n >= eta D_*` gives the charged arm.

Otherwise `a_n -> 0`.  The reset-face dispatch supplies the exact alternative
`D_z=D_*` or `D_*<D_z`.  If equality and positive opponent incidence both
hold, the endpoint enters reset-rigid.  If not, the stated inert tag is
exactly

\[
D_*<D_z\quad\text{or}\quad \operatorname{Inc}^{opp}_j(\mu^z)=0.
\]

Thus the alternatives are disjoint in the stated ordered sense and
exhaustive.  In particular, this is a trichotomy on roots chosen at the
literal endpoint caps.  The note correctly distinguishes an absorbing exact
root born only at the limiting cap from a usable source-level root; closedness
of the root correspondence does not provide the reverse approximation.

The assertions that `p_n -> allContinue` when `a_n -> 0` and that the
prefixed laws remain asymptotic to their suffix laws are also correct: product
survival tending to one forces every binary Continue probability to tend to
one, and the `l1` law discrepancy is at most `2a_n`.

## Automatic incidence on the minimum fibre

Proposition 3.2 is valid and is the strongest new connection in the note.
Here is the complete dependency chain.

Assume `D_z=D_*`.  The endpoint semantic coordinate is then a global
minimizer and `d_j(z)=0`.  The Fin4 hard-residual finite-atom theorem gives a
finite terminal `S` with `mu^z(S)>0`.  If total opponent incidence of `j`
were zero, the checked terminal-support lemma forces every positive finite
coordinate to be `{j}`.  Nonnegativity and the simplex sum then give exact
support on `{j}` and Never, with positive singleton mass `p` and Never mass
`1-p`.  The checked singleton/Never cap-tightness theorem yields

\[
B^z_j=r_j(\{j\}).
\]

But the global-minimum singleton margin gives

\[
0<D_*\le B^z_j-r_j(\{j\}),
\]

a contradiction.  Hence opponent incidence is positive.

Taking `origin=minimum=point=z` is legitimate: the origin lies in its own
law-tight saturation hull, and global minimality makes it a hull minimizer;
therefore it lies in its own minimum face.  With source `frontier.base`, the
terminal exploitability witness and the positive incidence, the hypotheses
of `exists_quittingLawTightResetRigidChamber` are exactly met.

For formalization clarity, the second recommended repair is to spell out the
short simplex step constructing the singleton/Never support equations, rather
than writing only “thus the complete law is supported.”  The construction is
straightforward and is already essentially the proof pattern in
`exists_quittingSingletonNeverMinimumSupport`; this is not a gap.

## Regression and sign orientation

The four-player regression in Section 5 checks out against unrestricted
behavioral deviations:

\[
d(X)=(1,1,1,1),\qquad d(Y)=(0,2,0,0),\qquad d(R)=0.
\]

The signed atom at `T={m}` is positive because the mass difference and reward
are both negative, while the low-debt endpoint has no finite incidence.
Sequential strict dominance gives all Continue as the unique exact root at
the target cap.  The example honestly has global minimum zero.  It therefore
refutes only the local atom-orientation implication and does not purport to
realize the maintained hard residual.

The sign table in Proposition 4.1 and all displayed constants are correct.
Positive reward on a coalition containing a genuine opponent puts a
quantitative incidence coordinate on the low-debt law; negative reward puts
the guaranteed mass on the sibling; the observer singleton gives no opponent
incidence.  Proposition 3.2 legitimately supersedes this local orientation
only after an exact global-minimum return and the Fin4 hard residual are both
available.

## Scope and export recommendation

This result **strictly narrows the vanishing-response rectangle descendant of
the full-debt question**:

```text
literal rectangle response endpoint
  -> uniformly charged literal fresh root
     or minimum-fibre reset-rigid entry
     or off-minimum vanishing-root/two-selector residual.
```

It does not strictly narrow the whole full-debt chamber by itself, because the
charged arm is not yet renewable or returned, the reset-rigid chamber is not
consumed, and the off-minimum inert arm remains open.  The preceding
prescribed-atom branch is also outside this packet.

A focused export is justified after the two minor exposition repairs above,
provided its title and abstract say “vanishing-response maximal-root/reset
reduction” rather than “full-debt consumer.”  The most valuable exported fact
is the automatic opponent-incidence theorem at a minimum-fibre response
cluster; the exact maximal-root charge/atom ledger and the negative-orientation
regression belong in the same packet because they state its sharp source-level
boundary.

No unresolved mathematical objection remains from this review.
