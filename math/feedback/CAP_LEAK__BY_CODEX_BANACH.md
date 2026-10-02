# Review of `CAP_LEAK.md`

Reviewer: `CODEX_BANACH`

## Verdict

**PASS for the balanced cap-leakage rigidity theorem, with minor statement
repairs.  Not export-worthy and not a Fin4 consumer.**

The proof of equations (4)--(5) is correct.  It genuinely controls the
unrestricted behavioral best-response envelope: bounded product-law
multiaffinity is uniform in the deviating behavioral strategy, and an
`o(lambda_n)`-optimal deviation suffices even when the cap is not attained.
Global minimum provenance is then exactly what converts the one-sided cap
inequality into coordinatewise equality at first order.

The theorem supplies a useful formalizable intermediate result:

> a balanced family of unilateral stopping-law tangent columns based
> `o(lambda)` above the global debt minimum has a literal simultaneous reset
> whose entire debt vector is displaced by `o(lambda)`, and whose cap-envelope
> nonadditivity is `o(lambda)`.

It does **not** supply root absorption, a Nash--Bellman edge, a chronological
block, a return, or renewable rank.  The proposed radial realization theorem
is a clear statement of the missing consumer, not a consequence of the proved
lemma.  The claim that all four current residuals have been reduced to that
one seam is not established by the argument in this document and should be
phrased as a proposed common capstone unless separate source adapters are
cited.

## Exact claim restated

Fix a finite player set `I`, a finite set `A` of distinct movers, a bounded
quitting reward table, actual profiles `sigma_n`, and positive scales
`lambda_n -> 0`.  For each `a in A`, let `sigma_n^a` replace player `a`'s
source stopping law by the mixture

\[
 (1-\lambda_n)\operatorname{Law}(\sigma_{n,a})
   +\lambda_n\operatorname{Law}(\beta_{a,n}),
\]

where `sigma_(n,a)` is the original player-`a` strategy in `sigma_n`, not the
already reset profile.  Let `bar sigma_n` mix all these
player laws independently, using
intensity `m_a lambda_n` for mover `a`, where

\[
 m_a\ge0,\qquad \sum_a m_a=1.
\]

Assume

\[
 \frac{D(\sigma_n)-D_*}{\lambda_n}\to0
\]

and, for every debt coordinate `j`,

\[
 \frac{d_j(\sigma_n^a)-d_j(\sigma_n)}{\lambda_n}
   \to T_{ja},
 \qquad
 \sum_a m_aT_{ja}=0.
\]

Then

\[
 \frac{d_j(\bar\sigma_n)-d_j(\sigma_n)}{\lambda_n}\to0
\]

for every `j`, and

\[
 \frac{1}{\lambda_n}\left(
 \sum_am_a[B_j(\sigma_n^a)-B_j(\sigma_n)]
 -[B_j(\bar\sigma_n)-B_j(\sigma_n)]\right)\to0.
\]

The theorem only needs `lambda_n>0` and `lambda_n -> 0`; monotone decrease is
not used.

## 1. Uniform multiaffinity is valid for arbitrary behavioral deviations

Before absorption, a quitting game has one live public history at each date.
Every behavioral strategy determines a probability law on
`Nat union {infinity}`.  Conversely, the stopping-law mixtures used in the
repository are executable behavioral strategies.  With player stopping laws
independent, terminal payoff is the integral of one bounded terminal-reward
function against the product of those laws.

Fix player `j` and one arbitrary complete behavioral deviation `rho_j`.  Its
payoff is therefore affine in each opponent stopping law separately.  Expanding
the finite product gives

\[
 F_{\rho_j,n}(\lambda_nm)
 =F_{\rho_j,n}(0)
 +\sum_am_a(F_{\rho_j,n}(\lambda_ne_a)-F_{\rho_j,n}(0))
 +R_{\rho_j,n},
\]

where every term in `R` contains at least two reset factors.  If rewards have
absolute value at most `R`, then

\[
 |R_{\rho_j,n}|\le C(R,|A|)\lambda_n^2
\]

uniformly in `rho_j`, the source laws, and the replacement laws.  If `a=j`,
the corresponding coordinate is simply irrelevant to `F`, which is harmless.

Thus equation (6) is correct.  The notation should be `O_{R,|A|}` rather than
`O_R` unless the fixed mover set is understood globally.

The same exact product expansion applies to prescribed payoff.  This proves
equation (8), including when the prescribed player `j` is among the movers.

Relevant checked infrastructure includes
`quittingStoppingLawMixtureBehaviorStrategy` and
`quittingTerminalPayoff_stoppingLawMixture_eq` in
`UniformEquilibrium/Quitting/Paths/StoppingLawMixture.lean`, and the finite
reset-cube affine-remainder bounds in
`UniformEquilibrium/Diagnostics/Quitting/Frozen/RadialResetCube.lean`.

## 2. The cap-envelope inequality is correctly derived

Choose `rho_{j,n}` within `epsilon_n=o(lambda_n)` of the cap against
`bar sigma_n`, and write

\[
 g_n=B_j(\sigma_n)-F_{\rho_{j,n},n}(0)\ge0.
\]

For each unilateral reset,

\[
 F_{\rho_{j,n},n}(\lambda_ne_a)\le B_j(\sigma_n^a).
\]

After inserting the multiaffine expansion, the coefficient of the base gap
is

\[
 -g_n+\left(\sum_am_a\right)g_n=0.
\]

This is the important cancellation; it does not assume one common maximizing
deviation at the unilateral profiles.  Consequently

\[
 B_j(\bar\sigma_n)-B_j(\sigma_n)
 \le\sum_am_a[B_j(\sigma_n^a)-B_j(\sigma_n)]
 +O(\lambda_n^2)+o(\lambda_n).
\]

Subtracting the prescribed-payoff expansion gives the correct one-sided debt
bound

\[
 \limsup_n
 \frac{d_j(\bar\sigma_n)-d_j(\sigma_n)}{\lambda_n}\le0.
\]

This really covers Never and arbitrarily late stopping.  Alternatively, the
checked equality
`quittingContinuationBestResponseValue_eq_sSup_pureTimeDeviationPayoff` in
`TerminalSemanticPositiveSlopeRectangle.lean` can reduce the cap to the
complete pure-time menu, but the proof in `CAP_LEAK.md` does not need that
reduction.

## 3. Global minimality correctly upgrades one-sided control to equality

The simultaneous reset is an actual behavioral profile, so

\[
 D(\bar\sigma_n)\ge D_*.
\]

Hence

\[
 \liminf_n
 \frac{D(\bar\sigma_n)-D(\sigma_n)}{\lambda_n}\ge0
\]

by the `o(lambda_n)` source-excess assumption.  Finiteness of the player set
and the coordinatewise limsup bounds give the reverse total limsup.  Therefore
the normalized total displacement tends to zero.

If one coordinate had a subsequence bounded above by a fixed negative
constant, every other coordinate would be eventually bounded above by an
arbitrarily small positive constant along that subsequence, forcing a negative
total limit.  This proves coordinatewise convergence to zero.  Equations
(4), (8), and the balanced tangent limits then yield equation (5) exactly.

No sign or attainment assumption on individual caps has been smuggled into
this step.

## 4. Falsification and boundary tests

I did not find a counterexample satisfying the hypotheses.  The elementary
two-menu cap switch explains both why the theorem is nontrivial and why the
near-minimum rate is essential.

Let

\[
 B(x_1,x_2)=\max\{x_1,x_2\}
\]

and, for a scale `lambda`, set

\[
 U(x_1,x_2)=-\lambda+2x_1.
\]

At the base `x=(0,0)`, debt is `lambda`.  On the two unilateral reset rays,
the normalized debt changes are `T_1=-1` and `T_2=1`, so equal weights balance
them.  At the simultaneous half reset
`x=(lambda/2,lambda/2)`, debt drops by `lambda/2`.  Correspondingly, the cap
subadditivity defect is also order `lambda`, not order `lambda^2`.

This is the exact phenomenon the proposed theorem rules out.  It does not
contradict the theorem because the source is order `lambda`, not
`o(lambda)`, above its lower debt level.  It shows that weakening (1) to
`D(sigma_n)-D_*=O(lambda_n)` is false even at the elementary maximum-of-two-
affine-functions level.

Likewise, if the tangent balance is removed, the same cap
`max{x_1,x_2}` with prescribed payoff zero has unilateral slopes `1,1` and a
simultaneous half-reset slope `1/2`; conclusion (4) fails.  For one mover the
theorem reduces to the assumed zero tangent and is immediate.

The maximum-of-affine-functions test is the local normal form of a behavioral
cap.  The proof above shows that no additional quitting-specific counterexample
can arise from escaping response times, because the multiaffine error bound is
uniform over the entire behavioral response class.

## 5. Repository correspondence and novelty

The nearest checked results are:

* `exists_frozenBalancedResetPacket` in
  `Frozen/BalancedResetPacket.lean`, which balances a finite star of actual
  unilateral reset columns but explicitly does not compose them;
* `exists_frozenRadialBoundedResetCube` in
  `Frozen/RadialResetCube.lean`, which builds one literal simultaneous radial
  cube and controls its frozen edge sum and positive diagonal charge;
* `quittingSimultaneousStoppingLawMixture_minimumFloor_slopeOrFlat_withUnilateralPassport`
  in `TerminalSemanticSimultaneousResetMinimumDichotomy.lean`, which gives
  total-debt ascent or flatness but not this coordinatewise envelope-additivity
  conclusion; and
* `activePassport_flatSimultaneous_directed_or_localizedPositiveSlope` in
  `TerminalSemanticSimultaneousResetOrientationLocalization.lean`, which
  localizes loss of one unilateral orientation but does not prove the full
  simultaneous cap defect is `o(lambda)`.

Thus the balanced rigidity theorem appears to be a genuine strengthening of
the existing terminal-semantic reset-cube layer.  A natural Lean handoff is a
theorem on `frozenRadialResetCubeData` showing, under the circulation weights,
that the full active vertex has coordinatewise normalized debt displacement
and full-face cap nonadditivity tending to zero.

The positive-minimum exact-cap budget statement used later in `CAP_LEAK.md`
is already checked.  In particular,
`semanticMinimum_mul_capNashStackAbsorptionSum_le_debtDrop` and
`literalReset_capNashStack_debtBudget_or_identity` in
`Research/Quitting/CapChangingLawRetainedSquareNoGo.lean` imply:

* at positive minimum excess zero, every exact cap--Nash prefix is literally
  all-Continue; and
* at excess `o(lambda)`, every finite exact cap-stack has total absorption
  `o(lambda)`.

So the document is correct that canonical cap lifting cannot manufacture an
order-`lambda` absorption block from the flat simultaneous reset.

## 6. The scheduling sentence needs a renewal qualifier

For a single numerical modulus `omega(h)->0`, one can indeed choose positive
scales `h_k->0` with

\[
 \sum_kh_k=\infty,
 \qquad
 \sum_kh_k|\omega(h_k)|<\infty.
\]

For example, choose a scale with `|omega|<=2^{-r}` at level `r` and repeat it
enough times to contribute order one total `h`-mass.

The proved rigidity theorem does not supply one state-uniform modulus or
show that the hypotheses survive after applying the reset.  Therefore the
sentence saying this is "precisely the strength needed for a diagonal
schedule" must be qualified: it is the needed **analytic error rate once a
renewable source-uniform reset theorem is supplied**.  It does not by itself
license concatenating the reset profiles.

## 7. Exact consumer supplied

The theorem supplies no existing terminal or return consumer.  Its exact
output is:

```text
balanced source-attached unilateral tangent star
+ o(scale) source excess
------------------------------------------------
literal simultaneous behavioral reset
+ coordinatewise o(scale) debt displacement
+ o(scale) cap-envelope nonadditivity
```

This removes first-order behavioral cap switching as an obstruction inside
that supplied reset cube.  It leaves unchanged the type mismatch emphasized
by the author:

```text
behavioral reset displacement/diagonal gain
    !=
exact punishment-floor Nash--Bellman absorption charge.
```

The proposed `Radial collision realization theorem` would be the missing
consumer.  It is not proved here, and its renewal, exact Bellman, floor,
absorption, and backward-compiler fields do not follow from equations
(4)--(5).

The four short residual discussions do not construct the source adapters
needed to place all four branches under the balanced theorem.  Accordingly,
"the four residuals collapse to one seam" should be read as a research
proposal, not as a theorem established by this packet.

## Export-gate verdict

**Do not export.**  The mathematical lemma is valid and worth formalizing in
the Research reset-cube layer, but it is a conditional supplied-object
verifier.  It has neither an arbitrary Fin4 source adapter across the claimed
four residuals nor a downstream semantic consumer.  It therefore fails the
actual-data/consumer requirement and does not answer
`questions/FIN4_MINIMUM_RETURN_CAPSTONE.md`.

The appropriate disposition is:

* retain the proof as a research note;
* formalize the balanced full-face cap-additivity theorem if useful to the
  current radial-cube work; and
* keep the radial collision realization theorem as the explicit open
  producer/consumer boundary.
