# Independent audit of Section 20

## Verdict: PASS, with one scope clarification

I audited only Section 20, the universal cyclic seam toll.  The theorem is
correct for the stated finite cyclic family of actual terminal-semantic
carrier points and product roots evaluated against their displayed
unrestricted caps.

## Exact identity and signs

For

\[
 w^k=\operatorname{Prefix}(q_k,z^k),\qquad
 c_k=\Pr_{q_k}(\text{all Continue}),\qquad a_k=1-c_k,
\]

the named checked declaration
`quittingTerminalSemanticDebtSum_prefix_eq_continueMass_mul_add_capDefect`
gives exactly

\[
 D(w^k)=c_kD(z^k)+N_k,
\]

where

\[
 N_k=\sum_i\left(\max\{Q_{k,i},C_{k,i}\}-U_{k,i}^{\rm root}\right)\ge0.
\]

Thus, with the note's orientation

\[
 s_k=D(z^{k+1})-D(w^k),
\]

cyclic telescoping gives

\[
 \sum_ks_k
 =\sum_kD(z^k)-\sum_k(c_kD(z^k)+N_k)
 =\sum_k(a_kD(z^k)-N_k).
\]

The signs in (20.3)--(20.5) are therefore correct.  In particular, an exact
root has `N_k = 0`, not a negative charge, and the lower bound

\[
 \sum_ks_k\ge D_*\sum_ka_k
\]

follows from the carrier lower bound \(D(z^k)\ge D_*\).

The carrier scope is also sound.  Each \(z^k\) is an actual carrier point,
its second coordinate is the unrestricted behavioral cap used to test
\(q_k\), and `quittingTerminalSemanticPrefix_mem_carrier` places every
\(w^k\) in the carrier for an arbitrary fixed product prefix.  The argument
does not silently replace an actual cap by a Bellman annotation.

## Metric and approximate forms

Writing the full semantic seam as

\[
 e_U^k=U(z^{k+1})-U(w^k),\qquad
 e_B^k=B(z^{k+1})-B(w^k),
\]

one has

\[
 s_k=\sum_i(e^k_{B,i}-e^k_{U,i}).
\]

Hence the displayed \(\ell^1\) estimate is correct.  On `Fin 4`, the
semantic pair has eight scalar coordinates, so

\[
 E_k\le 8\|z^{k+1}-w^k\|_\infty.
\]

This proves the factor \(D_*/8\) in (20.9).  No extra factor of two is
missing.

For an ordinary \(\eta_k\)-Nash root, the checked estimate
`quittingRootTotalNashDefect_le_card_mul_of_isεQuittingRootNash` gives

\[
 N_k\le4\eta_k.
\]

Substitution in the same exact cyclic identity yields

\[
 \sum_kE_k\ge D_*\sum_ka_k-4\sum_k\eta_k.
\]

Thus both the claimed correction and the little-oh consequence are valid.
The sharper intrinsic statement is obtained by replacing
\(4\sum_k\eta_k\) with \(\sum_kN_k\).

## Finite regressions

The sign can be checked on literal profiles.  For two players, give every
player reward \(1\) at every nonempty quitting coalition, take \(z\) to be
the all-Never profile, and let \(q\) have player \(0\) Quit surely while
player \(1\) Continues surely.  Then

\[
 U(z)=(0,0),\quad B(z)=(1,1),\quad D(z)=2,
\]

\(q\) is an exact root against \(B(z)\), \(a=1\), and its literal prefix has
\(U(w)=B(w)=(1,1)\), hence \(D(w)=0\).  The one-phase cyclic rebase has
\(s=D(z)-D(w)=2=aD(z)\), exactly with the sign claimed.

The same construction on four players gives \(D(z)=4\), \(a=1\),
\(D(w)=0\), and seam pair sup norm \(1\), consistent with the lower bound
\(4/8\).  These are algebra checks, not positive-global-minimum examples:
the constant-reward games themselves have global minimum debt zero.

## Scope clarification

The last sentence about arbitrary multiplicities should be read literally:
it applies when every repeated phase copy carries its actual rebase seam
from the prefixed carrier point back to the source of the next copy.  It does
not license multiplying phase charges while omitting the intermediate
same-source rebases.  A short clarification would prevent that stronger,
false reading.

## Effect on the maintained forward-packet question

This removes the second macroscopic-seam alternative currently listed in
`FIN4_APPROXIMATE_FORWARD_PACKET_OR_CAPACITY_BARRIER`: finitely many moves
between actual carrier tails cannot cancel their full payoff-and-cap seams
while retaining positive exact-root absorption.  More generally, they cannot
make semantic rebase error \(o(\sum a_k)\) when
\(\sum\eta_k=o(\sum a_k)\).

Accordingly, a source-attached construction must instead pay the seam through
an accepted chronological ledger, turn it into a renewable rank transition,
leave the actual carrier-cap chart by introducing a new annotation, or reach
a terminal consumer.  Section 20 is a genuine no-go for cyclic cancellation;
it is not itself the required producer or consumer.

## Declarations checked

- `quittingTerminalSemanticDebtSum_prefix_eq_continueMass_mul_add_capDefect`
  in
  `UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/CapDebtBellmanReduction.lean`;
- `quittingRootTotalNashDefect_le_card_mul_of_isεQuittingRootNash` and the
  definition/nonnegativity of total Nash defect in
  `UniformEquilibrium/Quitting/Root/NashDefect.lean`;
- `quittingTerminalSemanticPrefix_mem_carrier` in
  `UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`;
- the signed finite-chain orientation in
  `UniformEquilibrium/Quitting/Debt/Dynamic/TerminalSemanticSignedSeamTelescope.lean`.

## Delta review: stationary coupling strengthening

**Verdict: PASS.**

I checked the frozen packet
`/tmp/POSITIVE_MINIMUM_CARRIER_CYCLE_SEAM_TOLL.md` at SHA-256
`3a9348ba842eb6611bf3e7fd402711c36491863d8686c33e3a40fa43cc78dea6`.

The coupling identity is exact. Since both marginals of
\(\lambda_{k\ell}\) equal \(\beta\),

\[
\sum_{k,\ell}\lambda_{k\ell}
  \bigl(D(z^\ell)-D(w^k)\bigr)
=
\sum_k\beta_k\bigl(D(z^k)-D(w^k)\bigr)
=
\sum_k\beta_k\bigl(a_kD(z^k)-N_k\bigr).
\]

The root \(q_k\) remains evaluated against the unrestricted cap of its
original source \(z^k\); only the proposed rebase target is rematched.
Therefore no root/source typing is changed. For exact roots the last
quantity is nonnegative and at least
\(D_*\sum_k\beta_ka_k\). Weighted triangle inequalities give the stated
full semantic and Fin4 sup-norm bounds. The approximate correction is
likewise \(-|I|\sum_k\beta_k\eta_k\).

The permutation test is the deterministic equal-weight coupling and has the
claimed marginals. The packet correctly states the boundary: unequal
source/target marginals introduce an endpoint-debt term, and the coupling is
an external algebraic rematching rather than public correlation in the
quitting game. I found no mathematical or scope blocker in this delta.
