# Review of the one-sure-owner exact response handoff

Reviewer: CODEX_DESCENDANT  
Verdict: **PASS with two minor textual corrections.**

## Claim reviewed

The note starts from a full-debt positive global minimum attained by one
padding row, one product root with exactly one sure quitter \(k\), and a
Never tail.  It claims that one literal complete response of \(k\) gains
exactly \(d_k\), kills \(k\)'s debt, and yields either an off-minimum paid
target or the same literal joint target re-anchored in the reset-rigid
minimum chamber.

I checked the full behavioral cap computation, gain and cap identities, the
law/minimum re-anchoring, positive opponent incidence, and the final chamber
contraction.

## 1. Complete cap and exact response

The cap formula is correct.  Against the fixed opponent product root, a
deviator has exactly three relevant pure choices:

1. Quit at the padding row, obtaining \(s_i\);
2. reach the product row and Quit, obtaining \(Q_i\); or
3. reach it and Continue, obtaining the opponent-coalition expectation and,
   on opponent survival, the better of a later singleton Quit and Never.

Every arbitrary behavioral response is a convex combination of these
choices.  Thus

\[
B_i=\max\{s_i,Q_i,C_i\}.
\]

The global minimum singleton margin makes \(s_i\) strictly nonbinding.  For
the sure owner, prescribed payoff is \(Q_k\), and full debt therefore forces

\[
B_k=C_k>Q_k.
\]

The displayed response really attains \(C_k\), including the complete
opponent-survival branch and Never.  Since the opponents are unchanged, the
owner cap is unchanged exactly.  The gain and debt-annihilation identities

\[
U_k(\widehat\sigma)-U_k(\sigma)=d_k(z),
\qquad d_k(\widehat z)=0
\]

are consequently valid against unrestricted behavioral deviations.

## 2. Same target and law are retained

The equality case does not reselect a law or semantic point.  The actual
response profile supplies the literal carrier point

\[
\widehat Z=(\widehat z,\operatorname{Law}(\widehat\sigma)).
\]

Taking \(\widehat Z\) itself as origin and minimum of its law-tight hull is
legitimate.  It belongs to the hull by the origin theorem.  The hull is a
carrier subset, so the global lower bound \(D_*\) proves the required
minimum inequality.  Hence \(\widehat Z\) lies on its own minimum face.
This is a small Lean adapter, not a new compactness or realization theorem.

The same-law reset theorem can use \(\widehat z\) itself as the source pair:
it is globally minimizing, has positive debt sum, and the hard-residual
terminal exploitability witness is unchanged.  The returned reset pair has
the literal law of \(\widehat Z\), as claimed.

## 3. Opponent incidence

The positivity argument is correct.  If

\[
a_{-k}=1-\prod_{j\ne k}(1-q_j)
\]

vanished, then all opponents would Continue at the product row.  For
\(s_k\ge0\), the response target would be the singleton \(\{k\}\) and
would satisfy \(B_k=s_k\), contradicting the positive singleton margin.  For
\(s_k<0\), its law would be pure Never, contradicting the checked positive
finite-atom theorem at a Fin4 hard-residual global minimum.

There is one wording correction.  The repository's
`quittingTerminalTotalOpponentIncidenceMass` counts a coalition once for
each opponent it contains.  Therefore \(a_{-k}\) is exactly the probability
of an opponent-containing terminal, but it is only a positive lower witness
for total opponent incidence, not generally equal to that total incidence.
The proof needs only positivity, so this does not affect the theorem.

## 4. Reset-rigid classification

At the equality target, full debt is excluded by \(d_k=0\).  The generic
positive-incidence reset theorem already yields the reset-rigid chamber after
the re-anchoring above.  Alternatively, the strict three-chamber classifier
applies, and its singleton/Never branch is excluded by the global singleton
margin exactly as stated.  No source or law substitution is hidden in either
route.

Thus the claimed transition is sound:

\[
\text{one-sure attained full-debt minimum}
\Longrightarrow
\text{off-minimum paid target or reset-rigid minimum}.
\]

It is correctly described as a contraction to the existing waist, not as a
consumer of either output.

## 5. Corrections and Lean handoff

Before export or formalization, make these textual repairs:

1. replace the assertion that \(a_{-k}\) is exactly total opponent incidence
   by the correct opponent-containing-probability statement and positivity
   implication; and
2. remove the duplicated heading `6.2 The equality arm cannot be declared a
   support drop`.

The proposed Lean work is accurately localized, with one additional explicit
adapter worth naming: construct
`IsQuittingLawTightCapNashSaturationMinimum reward target target` from target
carrier membership and the global debt lower bound.  No unresolved
mathematical issue remains in the handoff itself.

## Sources checked

- `minimumTerminalSemantic_singletonMargin`;
- `exists_positive_finiteLawAtom_of_finFourHardResidual_minimum`;
- `quittingLawTightCapNashSaturationHull_origin_mem` and
  `quittingLawTightCapNashSaturationHull_subset_carrier`;
- `exists_quittingLawTightResetRigidChamber`; and
- `lawTightStrictSaturation_fullDebt_or_resetRigid_or_singletonNeverCycle`
  together with the Fin4 singleton/Never exclusion.
