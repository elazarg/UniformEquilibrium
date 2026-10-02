# Adversarial review of periodic complementarity and passive padding

Reviewer: `CODEX_SNELL`

Verdict: **mathematical PASS; the staged export requires two mechanical
freeze corrections before promotion.**

Objects reviewed:

- `notes/CODEX_SPINOZA__PERIODIC_COMPLEMENTARITY_AND_PASSIVE_PADDING_NO_GO.md`,
  SHA-256
  `25eebca60979a6cc659ed5837caa2bed2d63e2f10cf1cc72e6ebe9155fbaf066`;
- `/tmp/PASSIVE_PADDING_PERIODIC_CERTIFICATE_NO_GO.md`, SHA-256
  `81f516947626dbd2c426b06a1d2e5f166e86c510d5ae700193c8c01259810101`.

The staged candidate has no control bytes.  Its mathematics is covered by
this review.  It should not be promoted byte-identically yet: the review list
does not name this second review, and the exact statement calls \(W\) the
canonical coordinate oscillation without giving its finite max--min formula.
Both repairs are expository rather than mathematical, but both belong inside
the frozen self-contained packet.

## Claim restated

For a zero-Never quitting game \(G\), add one dummy whose solo quit gives each
old player a coordinatewise upper bound \(H_i\), gives the dummy \(-P<0\), and
whose joint quit with any old player reproduces the old reward and pays the
dummy zero.  The note claims:

1. deleting the dummy from an exact finite
   `IsQuittingBlockCertificate` produces a bounded completely absorbing
   inverse iterate of \(G\);
2. applying this projection to Solan's perturbed three-player table yields an
   existential rational Fin4 table with no such certificate of any finite
   period; and
3. checked profile-level projection and quiet lift preserve the literal live
   hazard period and compare unrestricted terminal exploitabilities by the
   passive-padding factor.

I checked the exact finite-cycle projection independently, including dummy
refusal and the sure-Quit face, and checked the approximate statements against
arbitrary behavioral deviations rather than periodic deviations alone.

## Exact projection audit

Write the old hazards in phase \(k\) as \(p^k\), the dummy hazard as \(x_k\),
and

\[
A_k=\prod_{i\in I}(1-p_i^k),\qquad
A_{k,-i}=\prod_{j\ne i}(1-p_j^k).
\]

### Dummy refusal is valid

At the dummy coordinate, the solo-reward branch of certificate admissibility
is \(0\le -P\), which is false.  The remaining branch is exactly

\[
A:=\prod_k A_k<1.
\]

Thus the old opponents absorb almost surely when the dummy plays Never.  This
is stronger than full padded absorption and is the precise fact needed for
the refusal calculation.

The padded Bellman cycle is absorbing, so
`eq_quittingCyclicTerminalValue_of_rootSuccessorPayoff_of_absorbing`
identifies displayed values with terminal values.  Every dummy terminal
reward is either \(0\) or \(-P\), hence every displayed dummy value is at most
zero.  Against dummy Never, old-opponent absorption is almost sure and the
dummy receives zero at every possible terminal coalition.  The comparison
`quittingCyclicHazardTerminalValue_le_of_isZeroRootNash_of_admissible`, after
the certificate-to-cycle conversion, gives the reverse inequality.  Hence
every dummy value is zero.

Substitution into the dummy Bellman equation gives

\[
0=-P x_kA_k,
\]

so \(x_kA_k=0\) for every phase.  This remains sound when \(A_k=0\); no
division by \(A_k\) is used.  I found no dummy-refusal counterexample.

### Bellman projection is exact

For every old coordinate \(i\), direct conditioning on whether the old part
of the quitting coalition is empty gives

\[
F^{\widehat G}_{(p^k,x_k),i}(v^{k+1})
=F^G_{p^k,i}(v^{k+1})
+x_kA_k(H_i-v_i^{k+1}).
\]

The last term vanishes by \(x_kA_k=0\).  Thus deletion preserves the Bellman
recursion exactly, not approximately.

### The sure-Quit boundary passes

Forcing old player \(i\) to Quit always makes the old coalition nonempty, so
its Quit endpoint is unchanged.  The Continue endpoint acquires only the
dummy-alone branch.  Therefore

\[
g_i^G=g_i^{\widehat G}
+x_kA_{k,-i}(H_i-v_i^{k+1}).
\]

The old displayed coordinate is a terminal mixture of old rewards at most
\(H_i\) and the dummy-alone reward \(H_i\), hence \(v_i^{k+1}\le H_i\).

If \(p_i^k<1\), then

\[
0=x_kA_k=x_k(1-p_i^k)A_{k,-i}
\]

forces \(x_kA_{k,-i}=0\), so both endpoint gaps agree.  If \(p_i^k=1\), the
projected Continue-support inequality is vacuous.  The padded Quit-support
inequality gives \(g_i^{\widehat G}\ge0\), and the displayed correction is
nonnegative, so \(g_i^G\ge0\).  This includes multiple simultaneous
sure-Quit coordinates.  The proof never divides by \(1-p_i^k\).

The finite value word is bounded, and periodic repetition of the old word has
survival \(A^n\to0\).  These are exactly the remaining boundedness and
complete-absorption fields.  I therefore find Theorem A sound.

## Solan source scope

The reward table in the note matches Figure 1 of E. Solan, *The Dynamics of
the Nash Correspondence and n-Player Stochastic Games* (2001), Theorem 2.1,
in the paper's integer scaling.  The paper literally excludes every
completely absorbing inverse iterate, but the assertion preceding its display
(1) places a nontrivial initial value in the convex hull of terminal rewards.
That assertion fails for an unbounded continuation-value sequence because a
homogeneous boundary term can survive.

For a bounded completely absorbing sequence, the survival prefix tends to
zero and its product with the uniformly bounded continuation value tends to
zero.  The convex-hull assertion is then valid for every shifted tail, and
the remainder of the paper's compactness argument applies inside the fixed
terminal-reward hull.  This is precisely the bounded correction described in
`UnboundedInverseIterate.lean`; the checked unbounded witness does not touch
it.  A periodic projected value word is automatically bounded.

For every sufficiently small positive perturbation the corrected bounded
theorem therefore excludes the projected object.  Choosing a rational
parameter in that interval and below \(2\) is legitimate by density; it gives
an existential rational member of the displayed parametric family, not a
numerically isolated table.  The candidate states that scope correctly.

The candidate also correctly does **not** use Solan's Theorem 2.2.  That
theorem's published sketch neither defines the approximate periodic class
precisely nor supplies a quantitative rate and contains a parameter-limit
slip.  No part of Theorems A or B depends on it.

## Approximate and unrestricted-deviation audit

`QuittingPayoffTable.oneDummyPadding_project_exploitability_le` is a
pointwise theorem for an arbitrary padded `BehaviorProfile`.  Its proof
transports an arbitrary old-player behavioral deviation into the padded game;
it is not a comparison only against stationary or periodic replacements.
Its multiplier is exactly

\[
1+\frac{W}{P},
\]

where \(W\) is the largest canonical coordinate width including zero.
`quittingTerminalExploitability_passivePaddingQuietProfile_le` is likewise a
literal terminal-exploitability statement and includes deviations by the
dummy, including refusal and arbitrarily late clocks.

`quittingPassivePaddingProjectProfile` rebuilds an old profile from the
actual old-player live-root sequence of the padded profile, and its checked
live-root identity says that every projected live row is the old-coordinate
restriction.  Quiet lift appends the constant Continue/Never root.  Therefore
both operations preserve any stated period of the live hazard word.  They do
not claim to preserve off-live controller states or least period, and neither
property is needed.  Taking infima gives the exploitability sandwich, and the
least-period inequalities follow with the candidate's \(+\infty\) convention.

For Solan's table every reward coordinate and zero lie in \([0,3]\), so
\(W=3\), and the factor at \(P=1\) is \(4\).  The candidate's constants and
inequality directions are correct.

## Freeze corrections

I found no mathematical objection.  Before promotion, make these two
candidate-only corrections and request a hash delta check:

1. Add this review to `Independent reviews`; the current candidate lists only
   `CODEX_NEGATIVE_CERTIFICATE`, although this review was explicitly requested
   as the second unrestricted-strategy falsification audit.
2. Define the width in the exact statement, for example
   \(L_i=\min(0,\min_S r_i(S))\),
   \(H_i=\max(0,\max_S r_i(S))\), and
   \(W=\max_i(H_i-L_i)\).  The current phrase “canonical coordinate
   oscillation” points to the correct checked definition but is not itself a
   self-contained definition.

Subject only to those freeze repairs, the packet passes the mathematical,
source, boundary, arbitrary-behavior, adapter, and consumer audits.

## Final candidate delta

The corrected candidate at
`/tmp/PASSIVE_PADDING_PERIODIC_CERTIFICATE_NO_GO.md` has SHA-256
`47188fbd995d586305ff52a768808d99c78628a73d21a24465f5a07db0b23edd`.
It adds this review to the independent-review list and defines
\(L_i,H_i,W\) by the requested finite extrema.  The new formulas agree with
`quittingPassivePaddingLowerEndpoint`,
`quittingPassivePaddingUpperEndpoint`, and `quittingPassivePaddingWidth`.
The control-byte scan is empty.  No mathematical claim changed, and no new
claim was introduced.  **Delta PASS for this exact candidate and hash.**
