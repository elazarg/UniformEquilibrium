# Review of the corrected Fin5 actual-endpoint reduction

**Reviewer:** CODEX_MINER  
**Date:** 2026-08-25  
**Checked repository head:** `a277602` (the requested `a277602c` prefix)  
**Verdict:** `SECTIONS 8--11 PASS AFTER ONE FORMULA REPAIR AND TWO SCOPE CLARIFICATIONS`

I independently checked the corrected reduction in
[`CODEX_EULER__FIN5_LITERAL_NEVER_SPARE_PRODUCER_AUDIT.md`](../notes/CODEX_EULER__FIN5_LITERAL_NEVER_SPARE_PRODUCER_AUDIT.md),
the earlier audit in [`CANCEL.md`](../../CANCEL.md), and the current checked
declarations named below.  The actual-profile paid-source regeneration is
correct and materially improves the old handoff.  It does not solve the
port-limit restart or inert-stall obstruction.

## 1. The semantic Never descent uses no floor

The pathwise deletion calculation is correct against unrestricted behavioral
deviations.  If `y_w=x_2[w<-Never]`, then the opponents faced by `w` are
literally unchanged, so its behavioral cap is unchanged.  For `i!=w`, coupling
an arbitrary deviating stopping law while replacing only `w` by Never gives
the stated cap upper bound.  Thus the debt identities and inequalities used in
Corollary 3.3 are valid.

The condition `U_w(x_2)>=P_w` is absent from the semantic argument.  It is only
a coordinatewise floor-safety fact for the interpolation in `w`; without
additional hypotheses it does not make the whole interpolation floor-safe.
Its removal from the minimum-fiber/support descent theorem is mandatory and
correct.

## 2. The `g/kappa/q` failures are not semantic alternatives

The displayed bounds have the directions

\[
  \Delta_i^w\ge g_i^w,\qquad K_i^w\le\kappa_i^w,
  \qquad d_i(y_w)\le q_i^w.
\]

Their converses do not follow.  The rational null-event construction in
Section 5 correctly separates unreachable extrema in `m` and `kappa` from the
actual terminal law.  In particular, failure of the owner `g` test need not
mean owner nonclosure, a large aggregate `q` need not mean an off-minimum
endpoint, and positive inactive-coordinate `q` need not mean actual support
entry.  Only the realized quantities `d(y_w)`, `D(y_w)`, and realized support
have semantic force.

## 3. Arbitrary-profile terminal gap gives the full-gap literal paid row

Lemma 11.1 is correct.  At an arbitrary literal behavioral profile `sigma`,
`HasTerminalExploitabilityGap reward gamma` supplies `j,tau` with

\[
  U_j(\sigma[j\leftarrow\tau])-U_j(\sigma)\ge\gamma.
\]

Applying
`quittingTerminalPayoff_update_eq_expect_stoppingLaw_pureTime` to `tau` and to
the prescribed strategy `sigma(j)` expresses the two terms as expectations of
the same bounded pure-time payoff function under two PMFs on `Option Nat`.
If every positive-mass product atom had difference strictly below `gamma`, the
nonnegative deficit would be strictly positive on at least one atom, hence
would have strictly positive expectation.  That contradicts the weak expected
gap.  Therefore a support pair has pure-time difference at least the full weak
gap `gamma`.

The hypotheses of
`exists_quittingPaidFirstDisagreementRow_of_pureTimePayoff_sub` are then exact:
`gamma>0`, the weak pure-time inequality, and the literal receiving profile
`sigma`.  Either pure time may be finite or Never.  The observer is not
controlled, and the selected `sourceWitness` is a pure atom of the prescribed
stopping law rather than the whole prescribed behavioral strategy; neither is
required by the paid-row structure.

Consequently this construction applies at **every** actual endpoint `y_w`.
No failure of support descent, no positive endpoint debt coordinate, and no
floor condition is needed to obtain the row.

## 4. Lifted source and current exact trichotomy

The construction of `QuittingPaidCapLiftedSource` is complete.  Its fields are
exactly the independently supplied global minimum and lower-bound proof,
positive minimum debt, literal endpoint `y_w`, selected observer, positive
gain `gamma`, and the paid row.  It has no floor or support hypothesis.
`QuittingPaidCapLiftedSource.nonempty_summablePort` then returns a port.

At the current head,
`QuittingPaidCapLiftedSource.exactTrichotomy` in
`PaidCapPortExactTrichotomy.lean` is an exhaustive, pairwise-disjoint
trichotomy **of that selected port**:

1. `ChargedNearReturn`;
2. `QuantitativeDebtDescent`; or
3. `InertStall`.

This corrects the older state described in `CANCEL.md`: its `eta/2` paid-row
adapter remains valid but is strictly weaker than the full-gap product-PMF
argument, and its “support drop or paid summable port” theorem is only an
inclusive statement.  The paid port now exists even on the support-drop arm,
and the current exact trichotomy refines that unconditional port output.

## 5. Logical forms (7) and (8)

The proposed statement (7), for every omitted `w`,

\[
  \text{strict minimum-fiber support descent}
  \ \lor\ \text{Charged}
  \ \lor\ \text{Quantitative}
  \ \lor\ \text{Inert},
\]

is true after choosing the port, but the first disjunct is redundant: the last
three already exhaust every endpoint.  It is not an exact four-way partition,
because support descent can coexist with a port arm.  The clearer formulation
is to retain two separate facts:

* the exact realized deletion alternative of Section 4; and
* the unconditional, pairwise-disjoint port trichotomy at every `y_w`.

Statement (8) can be strengthened.  Under the positive terminal-gap
counterexample witness,

\[
  D(z_w)=D_0 \quad\Longrightarrow\quad \operatorname{InertStall}(y_w).
\]

No assumption that strict support descent fails is needed.  Indeed the charged
arm already contains a uniform-equilibrium payoff and is contradicted by the
terminal-gap witness.  In the quantitative arm, positive displacement gives a
strict drop below the source debt.  If the source debt equals the global
minimum `D_0`, the port limit would have debt below `D_0`, contradicting its
checked membership in the terminal-semantic carrier and global minimality.
Only the inert arm remains.  Thus support success/failure is logically
independent of this equality-fiber port classification.

## 6. Mandatory quantitative formula repair

Let

\[
 R=\operatorname{quittingRewardBound}(reward),\qquad
 D_w=D(\operatorname{Sem}(y_w)),\qquad
 D_\infty=D(port.semanticPort.limit),
\]

and let `rho_w` be the checked cap displacement.  The current theorem proves

\[
 D_w-D_\infty
 \ \ge\ D_0\frac{\rho_w}{2R}.                       \tag{A}
\]

This is because `source.initialDebt` is definitionally `D_w`, while the
multiplier is the debt of `source.minimum`, namely `D_0`.  The sentence in
Section 11 displaying

\[
  D_0-D_\infty\ge D_*\rho/(2M)
\]

is therefore wrong for an off-minimum endpoint unless its left-hand `D_0` was
intended to denote the source debt.  It must be replaced by (A), or explicitly
restricted to `D_w=D_0`.

If `E_w=D_w-D_0`, global minimality and (A) give exactly

\[
  0\le D_\infty-D_0
  \le E_w-D_0\frac{\rho_w}{2R}<E_w
\]

in the positive-displacement arm.  This is a genuine strict decrease of
off-minimum excess on that one slice, but is not a well-founded rank when
positive displacements may shrink along restarts.

The denominator also needs precise naming.  The checked constant is the
canonical sum bound `quittingRewardBound reward`.  Replacing it by `M` is valid
if `R<=M` (in particular if `M=R`), not merely from the coordinatewise claim
`|reward outcome who|<=M`.

## 7. Inert preservation and the remaining provenance boundary

The note's inert description matches the current `InertStall` fields.  Total
absorption and cap displacement vanish; every selected root is literally all
Continue; every finite prefix has the same semantic pair, debt coordinates,
and debt sum as the source; observer reach is one; and a paid row of the same
gain is shifted losslessly with its live mass, reached gain, orientation,
start, and delay controlled.

This is strong finite-prefix preservation, but it does not attach the reset
roles or omitted label to the arbitrary observer chosen by Lemma 11.1, turn the
port limit into an actual behavioral profile, or regenerate a source-connected
reset/deletion packet at that limit.  Reapplying the terminal gap at actual
finite prefixes supplies paid rows there, not a restart at the abstract carrier
limit.

Accordingly “actual approximation regenerates a full-gap paid row” genuinely
solves **literal paid-source provenance at every actual endpoint** and removes
the need for separate SC4/SC5 paid-row producers.  It does not solve recursive
provenance, incidence alignment, the positive-displacement Zeno issue, or the
inert all-Continue stall.  The note's final nonclaim is correct once the
quantitative formula above is repaired.

## Sources checked

* `HasTerminalExploitabilityGap` in
  `UniformEquilibrium/Quitting/Terminal/ExploitabilityGap.lean`;
* `quittingTerminalPayoff_update_eq_expect_stoppingLaw_pureTime` in
  `UniformEquilibrium/Quitting/Paths/BehaviorStoppingPayoff.lean`;
* `exists_quittingPaidFirstDisagreementRow_of_pureTimePayoff_sub` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPaidFirstDisagreement.lean`;
* `QuittingPaidCapLiftedSource`, `initialDebt`, and `nonempty_summablePort` in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/PaidCapLiftedSummablePort.lean`;
* `QuantitativeDebtDescent`, `InertStall`, `ChargedNearReturn`, and
  `exactTrichotomy` in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/PaidCapPortExactTrichotomy.lean`;
* `quittingRewardBound` in `UniformEquilibrium/Quitting/RewardBound.lean`.

