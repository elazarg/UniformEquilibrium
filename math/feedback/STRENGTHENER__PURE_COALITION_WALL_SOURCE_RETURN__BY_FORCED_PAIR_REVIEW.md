# Review of the pure-coalition wall

Reviewer: Forced Pair Review

## Verdict

The two principal wall calculations are correct:

1. a pure-set stationary profile has total unrestricted terminal debt exactly
   the sum of its positive Boolean membership-toggle gains; and
2. an arbitrary actual profile reaching a pure **nonsingleton** coalition
   $C$ with live probability $L$ has total unrestricted terminal debt at
   least $L H_C$.

The equality case really produces an attained global minimum with explicitly
known debt support.  For the maintained strict-join pair, one named coordinate
has zero debt.  This gives a checked strict support-rank re-extraction only
when the old support contains the new support and loses a coordinate; in
particular it works from a Fin4 rank-four source.  It is not an unconditional
rank descent from an arbitrary old source.

The strict-wall reach bound and the six-cycle regression are also correct.
The reach bound is a separator, not an exact chronology or a well-founded
rank.  Consequently I recommend formalizing the exact wall package, but I do
**not** recommend exporting the whole note as a completed forced-pair
consumer.  The equality arm is a genuine conditional exit; the complementary
strict arm still has no semantic consumer and therefore does not pass export
gate item 4.

There is one important sharpening of the presentation.  For the forced-pair
obligation, use the pair-specific dichotomy

\[
 H_{\{j,o\}}=D_*
 \quad\text{or}\quad
 \kappa_{j,o}:=H_{\{j,o\}}-D_*>0.
\]

The table-wide dichotomy in the note is mathematically true, but equality can
occur at an unrelated coalition while the retained pair remains strictly
above the minimum.  In that situation the table-wide minimum gap is zero and
does not control the pair.  All pair reach estimates remain valid with
\(\kappa_{j,o}\), without assuming every other pure coalition is strict.

## 1. Exact pure-wall semantics

For a nonempty finite coalition $C$, define

\[
 H_C=\sum_i [r_i(C\mathbin\triangle\{i\})-r_i(C)]_+,
\]

using the project's empty-set reward convention.  The checked declaration

```text
quittingTerminalSemanticDebt_pureSetRoot_eq
```

in `UniformEquilibrium/Quitting/Paths/SureExitSet.lean` states, against the
full behavioral strategy class,

\[
 d_i(\sigma_C)
 =\max\{r_i(C\cup\{i\}),r_i(C\setminus\{i\})\}-r_i(C).
\]

One of the two entries in the maximum is $r_i(C)$, according as $i\in C$
or $i\notin C$.  Therefore

\[
 d_i(\sigma_C)=[r_i(C\triangle\{i\})-r_i(C)]_+,
 \qquad D(\sigma_C)=H_C.
\]

This is not a stationary-deviation approximation.  The companion declaration
`quittingContinuationBestResponseValue_pureSetRoot_eq` takes the supremum over
arbitrary behavioral deviations and proves that the two membership endpoints
already exhaust the cap.

If $D_*$ is the global carrier minimum, the actual semantic pair of
\(\sigma_C\) belongs to the carrier, hence $H_C\ge D_*$.  If equality holds,
that actual pair lies on the minimum fibre.  Its positive-debt support is
exactly

\[
 A_C=\{i:r_i(C\triangle\{i\})>r_i(C)\}.
\]

The hypotheses of
`exists_positiveMinimumDebtTangentFamily_of_pair` in
`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/PositiveMinimumDebtTangentFamily.lean`
are then available: actual carrier membership, global minimality, and positive
total debt.  Thus the tangent-family re-extraction claim is valid.

## 2. Forced-pair coordinate and support rank

Let $C=\{j,o\}$, with $j\ne o$, and suppose

\[
 r_o(\{j,o\})>r_o(\{j\}).
\]

At the pure pair, $o$'s opposite membership endpoint is the leave endpoint
\(\{j\}\).  Hence

\[
 d_o(\sigma_C)
 =[r_o(\{j\})-r_o(\{j,o\})]_+=0.
\]

On Fin4 this proves \(|A_C|\le3\).  It does not by itself prove
\(A_C\subsetneq A_{\mathrm{old}}\).  In particular, a new three-element
support may exchange a label with an old three-element support.

There is, however, an exact checked rank consequence from an old rank-four
frontier.  A four-element positive-debt support on `Fin 4` is `univ`, so:

* $A_C\subseteq A_{\mathrm{old}}$ automatically;
* $o\in A_{\mathrm{old}}$; and
* $d_o(\sigma_C)=0$.

The theorem

```text
QuittingPositiveMinimumDebtTangentFamily.
  exists_reextracted_of_minimumFiber_of_supportSubset_of_vanished
```

then returns a tangent family based at the pure pair whose support is a strict
subset of the old support.  This is the maximal honest support-rank consumer.
Without old rank four, one must separately prove support inclusion and loss of
an old active coordinate.

## 3. Live-weighted wall against unrestricted deviations

Let an arbitrary actual behavioral profile \(\rho\) have pure coalition
\(C\) at date $t$, where \(|C|\ge2\), and let $L$ be the prescribed
probability of reaching the live history at $t$.

For each player $i$, define one complete behavioral deviation which agrees
with \(\rho_i\) at every earlier live history and at $t$ chooses the better
Boolean endpoint.  Since the earlier behavior is unchanged, the probability
of reaching $t$ remains exactly $L$.  If $i\in C$, at least one member of
\(C\setminus\{i\}\) still Quits surely; if $i\notin C$, the original
coalition $C$ still Quits surely.  Hence both endpoint plays absorb at
date $t$, and the continuation after $t$ is invisible.  Outcomes before
$t$ are identical.  The complete deviation gain is therefore exactly

\[
 L[r_i(C\triangle\{i\})-r_i(C)]_+.
\]

This literal deviation is among the strategies over which the unrestricted
cap is taken.  Thus coordinatewise

\[
 d_i(\operatorname{Sem}(\rho))
 \ge L[r_i(C\triangle\{i\})-r_i(C)]_+,
\]

and summing gives

\[
 \boxed{D(\operatorname{Sem}(\rho))\ge L H_C.}
\]

Arbitrary earlier roots, private behavioral randomization, Never, and
arbitrarily late deviations cause no gap in this argument.  The earlier roots
only determine $L$; the lower-witness deviation copies them.  Never and late
strategies remain in the cap, which can only make the debt larger.

The checked reached-row identity
`quittingTerminalPayoff_stageBestEndpointDeviation_sub_eq_liveMass_mul_defect`
in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPlateauLocalizedOtherDefect.lean`
is the closest existing local declaration.  A new pure-nonsingleton
specialization should identify its coordinate defect with the Boolean toggle
positive part and then derive the sum bound.

The nonsingleton condition is genuinely necessary for this formula.  At a
pure singleton, making its owner Continue exposes the actual tail, whereas
the static pure-set formula uses the all-Continue infinite-play value $0$.
Those continuation values need not agree.

## 4. Strict-wall reach bounds

For any fixed nonsingleton $C$, set

\[
 \kappa_C:=H_C-D_*\ge0.
\]

If \(\kappa_C>0\) and actual profiles \(\rho_n\) reach a pure $C$-row with
probability $L_n$, while \(D(\rho_n)\to D_*\), the wall gives

\[
 \limsup_n L_n\le {D_*\over H_C}
 ={D_*\over D_*+\kappa_C}<1.
\]

Since failure to reach a finite marked date is exactly absorption before that
date,

\[
 \liminf_n(1-L_n)
 \ge {\kappa_C\over D_*+\kappa_C}>0.
\]

If the pure marked $C$-mass has a uniform floor \(\lambda\), then it equals
the live mass for that pure root, so \(L_n\ge\lambda\).  Hence
\(\lambda H_C>D_*\) rules out convergence of the whole profiles to minimum
debt.  These calculations are exact.

If every nonempty pure coalition is strict, the note's table-wide
\(\kappa=\min_C(H_C-D_*)>0\) is valid by finiteness and gives the uniform
version.  It is stronger than needed for a fixed forced pair and can fail
solely because an unrelated coalition attains the minimum.

The bound is not yet exact cap charge.  The probability $1-L_n$ may be
generated by arbitrary non-Nash prescribed roots.  It carries neither a
prescribed-payoff return seam nor an admissible exact-edge certificate.

## 5. Exact-prefix specialization

The conditional equality

\[
 D(\rho)=L H_C
\]

is correct if the complete pre-$C$ word is recursively an exact cap--Nash
stack for the **actual modified suffix at every stage**.  The one-row checked
declaration is

```text
quittingTerminalDebtSum_rootThenContinuation_eq_continueMass_mul_of_capNash
```

in
`UniformEquilibrium/Diagnostics/Quitting/TerminalCapNashEndpointTransport.lean`.
Iteration multiplies by the stack's joint Continue product, which is exactly
the live reach $L$; the pure $C$-suffix has debt $H_C$.

It is not enough that the copied roots were exact against the cap of a former
continuation.  Replacing the marked row or its tail changes the continuation
cap and can destroy cap--Nash exactness.  The source note records this
limitation correctly.

## 6. Six-cycle falsification of a wall rank

The cycle

\[
 01\to012\to02\to023\to03\to013\to01
\]

is a chordless six-cycle in the Fin4 Boolean cube.  Give every displayed
directed edge gain $1$, and orient every other edge incident to a cycle
vertex toward that vertex.  There is no consistency obstruction:

* nonconsecutive cycle vertices are not Boolean neighbors; and
* for a fixed player $i$, the $i$-edges are disjoint unordered pairs, so
  the two endpoint values of $r_i$ on each edge can be assigned
  independently.

At each cycle vertex the forward cycle edge is the unique outgoing improving
toggle and has gain $1$.  Thus $H_C=1$ at all six vertices.  The prescribed
differences are realized by rational rewards (take endpoint values $0,1$ on
the relevant coordinate edges).  Remaining coordinate values are arbitrary.

This is a valid exact counterexample to both strict decrease and any potential
interpretation of $H_C$ along improving toggles.  It is not a positive-gap
quitting-game counterexample and makes no such claim.

## 7. Maximal formalizable result and export judgment

The narrow formalization target should be a package of four results:

1. `pureSetDebtSum_eq_toggleWall` and exact support membership;
2. `pureNonsingleton_liveMass_mul_toggleWall_le_debtSum`;
3. the pair-specific alternative
   \(H_{\{j,o\}}=D_*\) or \(0<H_{\{j,o\}}-D_*\), with the equality arm's
   actual minimum and \(d_o=0\);
4. from an old Fin4 rank-four tangent source, equality yields checked strict
   support re-extraction; from strictness, near-minimum pair sources obey the
   quantitative reach barrier above.

The global finite wall dichotomy and the six-cycle no-go are also cleanly
formalizable, but neither supplies the missing forced-pair chronology.

The equality arm is a real special-case advance when the current source has
rank four.  The strict-wall arm is only a source-return obstruction.  Because
the combined statement still leaves that entire arm without terminal
approximants, an admissible return, or a finite-rank regenerated source, it is
not yet a complete answer to the forced-pair question and should remain in
`notes/` rather than enter `exports/`.  If a later exact-prefix or
pre-absorption consumer closes the strict arm, this reviewed wall package is
ready to be incorporated at maximal strength.

## Sources inspected

* `quittingContinuationBestResponseValue_pureSetRoot_eq` and
  `quittingTerminalSemanticDebt_pureSetRoot_eq` --
  `UniformEquilibrium/Quitting/Paths/SureExitSet.lean`.
* `quittingTerminalPayoff_stageBestEndpointDeviation_sub_eq_liveMass_mul_defect`
  --
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPlateauLocalizedOtherDefect.lean`.
* `quittingTerminalSemanticDebt_stageBestEndpoint_eq_sub_gain` --
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticLiveWeightedCollisionTransfer.lean`.
* `quittingTerminalDebtSum_rootThenContinuation_eq_continueMass_mul_of_capNash`
  --
  `UniformEquilibrium/Diagnostics/Quitting/TerminalCapNashEndpointTransport.lean`.
* `exists_positiveMinimumDebtTangentFamily_of_pair` and
  `QuittingPositiveMinimumDebtTangentFamily.exists_reextracted_of_minimumFiber_of_supportSubset_of_vanished`
  --
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/PositiveMinimumDebtTangentFamily.lean`.
* The current forced-pair source/tail boundary --
  `exports/FIN4_WEAK_SINGLETON_TO_MINIMUM_TAIL_FORCED_PAIR.md`.
