# Escape-aware quantile-clock polynomial hierarchy

Authors: CODEX_EULER

Independent reviews:

- [CODEX_MINER, PASS as ordinary mathematics](../feedback/CODEX_EULER__ESCAPE_AWARE_QUANTILE_CLOCK_SEMIALGEBRAIC_HIERARCHY__BY_CODEX_MINER.md);
- [CODEX_RAMSEY, unrestricted-strategy falsification and whole-packet PASS](../feedback/ESCAPE_AWARE_QUANTILE_CLOCK_SEMIALGEBRAIC_HIERARCHY__BY_CODEX_RAMSEY.md).

## Exact statement

Let `I` be a nonempty finite player set, let `n=|I|`, and let

\[
 r:\{S\subseteq I:S\ne\varnothing\}\longrightarrow[-1,1]^I
\]

be a rational quitting-game reward table.  Behavioral randomization is
independent across players.  Before absorption there is only the public
all-Continue history, so a behavioral strategy for player `i` induces a
complete stopping law `mu_i` on

\[
 \mathbb N\cup\{\mathsf{Never}\}.
\]

Conversely every such stopping law has a canonical behavioral realization.
For an executable profile `sigma`, write

\[
z(\sigma)=(U(\sigma),B(\sigma))\in\mathbb R^{2n},
\]

where `U_i` is prescribed terminal payoff and `B_i` is the supremum over all
unilateral behavioral deviations.  Define

\[
 F(U,B)=\max\bigl(0,\max_{i\in I}(B_i-U_i)\bigr),
 \qquad
 \eta(r)=\inf_\sigma F(z(\sigma)).                       \tag{1}
\]

On executable pairs, `F` is literal unrestricted terminal exploitability.

For `K>=1`, let `A_K(r)` be the set of terminal semantic pairs realized by
product stopping laws whose finite support is contained in

\[
 \{0,1,\ldots,K-1\},                                    \tag{2}
\]

with `Never` retained as an additional exact atom.  For `m>=1`, put

\[
 K_m=2nm+1,
 \qquad
 \delta_m={n(n-1)\over m},                              \tag{3}
\]

and define

\[
 N_m(r)=\{z\in\mathbb R^{2n}:
      \exists a\in A_{K_m}(r),\ \|z-a\|_\infty\le\delta_m\},
 \qquad
 R_M(r)=\bigcap_{m=1}^M N_m(r).                         \tag{4}
\]

The checked hierarchy is deliberately unboxed: no artificial coordinate box
is imposed on the outer variables.  Finally define

\[
 L_M(r)=\inf_{z\in R_M(r)}F(z),
 \qquad
 U_M(r)=\min_{a\in A_{K_M}(r)}F(a).                    \tag{5}
\]

### Theorem A (finite-player quantile-clock hierarchy)

For every fixed nonempty finite `I` and every normalized rational reward
table `r`:

1. `A_K` has an exact finite rational polynomial presentation, and the
   unboxed `R_M` has an exact finite rational polynomial feasibility
   presentation using one center witness for every `m=1,...,M` and an exact
   finite maximum graph for `F`;
2. every executable behavioral profile maps to its literal semantic pair in
   every `R_M`, with objective exactly equal to its unrestricted terminal
   exploitability;
3. \(R_{M+1}(r)\subseteq R_M(r)\), and

   \[
    \bigcap_{M=1}^{\infty}R_M(r)
       =\operatorname{Carrier}(r),                      \tag{6}
   \]

   where the right side is the closure of executable terminal semantic pairs;
4. the exact certified bounds satisfy

   \[
    0\le L_M(r)\le\eta(r)\le U_M(r),
    \qquad
    0\le U_M(r)-L_M(r)\le {2n(n-1)\over M};             \tag{7}
   \]

5. consequently

   \[
    \sup_M L_M(r)=\eta(r),
    \qquad
    0\le U_M(r)-\eta(r)\le {2n(n-1)\over M}.            \tag{8}
   \]

For each rational `gamma`, `gamma<=L_M(r)` follows from infeasibility of the
finite rational polynomial system `z in R_M(r), F(z)<gamma`.  A checked
verifier accepts a supplied sum-of-squares polynomial identity proving that
infeasibility.  No completeness theorem says that this restricted certificate
format exists for every infeasible query.

### Corollary B (the Fin4 constants)

For `I=Fin 4`, one may take

\[
 K_m=8m+1,
 \qquad
 \delta_m={12\over m},
 \qquad
 0\le U_M-L_M\le {24\over M}.                           \tag{9}
\]

Thus a positive Fin4 terminal gap eventually makes some finite lower query
infeasible.  Turning that fact into an automatically found checked certificate
is separate future work.  If `eta(r)=0`, the minimizers defining `U_M` are
executable finite-clock product profiles with exploitability at most `24/M`.

The finite-player statement is not a silent extrapolation from Fin4.  Its
proof below tracks all `n`-dependent event counts.  For `n=1`, the displayed
error constants vanish, as they should.

## Conjecture-facing change

This packet addresses the maintained question
[`ESCAPE_AWARE_FIN4_CERTIFICATE_SEARCH.md`](../questions/ESCAPE_AWARE_FIN4_CERTIFICATE_SEARCH.md).
It strictly replaces the unrestricted infinite-clock inner adversary by a
monotone sequence of finite rational semialgebraic problems with:

- a map from every actual behavioral profile into every outer problem;
- the exact unrestricted semantic objective;
- exact `Never` and product-law provenance;
- an explicit uniform `24/M` Fin4 lower/upper gap; and
- exact convergence to the entire semantic carrier, including unrealized
  diffuse limits.

It supplies the finite polynomial queries and a kernel-checked soundness path
from any supplied rational polynomial-identity certificate to a genuine
all-behavior lower bound.  A complete certificate generator, CAD or
quantifier-elimination proof trace, positive-gap semidecision procedure, and
uniform computability theorem for `eta(r)` remain open.  The hierarchy does
not determine which branch holds in the Fin4 hard residual.

## Definitions and probability model

### Complete stopping laws and product provenance

For each player `i`, let `mu_i` be the law on `Option Nat` induced by the
player's behavioral hazard along the unique live history.  The joint terminal
law is the product of these marginals.  A sampled vector
`(T_i)_(i in I)` produces the coalition of players attaining the least finite
time; if every `T_i=Never`, the terminal payoff is the all-Continue payoff
zero.

There is no public correlation device and no arbitrary coalition occupation
flow.  All finite systems below retain the marginal simplexes and form
coalition probabilities by their exact product monomials.

### Unrestricted deviation envelope

The best-response envelope is

\[
 B_i(\sigma)=\sup_{\tau_i}
 U_i(\tau_i,\sigma_{-i}),                               \tag{10}
\]

where `tau_i` ranges over every behavioral deviation.  The checked pure-time
extremality theorem identifies (10) exactly with the supremum over
deterministic dates in `Nat` and `Never`.  No best response is assumed to be
attained for an infinite-clock profile.

## Common-cell construction and compression proof

Fix an executable profile and `m>=1`.  For each player `i` and each
`j=1,...,m`, mark the first finite date at which the cumulative finite mass of
`mu_i` reaches `j/m`, if such a date exists.  Let `H` be the union of all
marked dates.  Multiple thresholds may mark the same atom, and therefore

\[
 |H|\le nm.                                             \tag{11}
\]

Partition `Nat` into singleton marked dates and the maximal gap intervals
before, between, and after them.  There are at most

\[
 |H|+(|H|+1)\le 2nm+1=K_m                              \tag{12}
\]

finite cells.  Keep `Never` separate.  Every nonsingleton gap `G` satisfies

\[
 \mu_i(G)\le {1\over m}\quad\text{for every }i.         \tag{13}
\]

Indeed, mass greater than `1/m` would cross a grid level inside `G`, marking
a date there.  Before the first mark the cumulative mass is below `1/m`.
After the last mark, failure to cross the next grid level leaves residual
finite mass at most `1/m`.  This remains valid when finite cumulative mass
tends to a non-grid value without attaining it.

Map the ordered finite cells to consecutive dates, push every marginal
forward separately, and pad unused dates below `K_m` with zero mass.  Denote
the resulting product law by `mu^(m)`.  `Never` mass is unchanged.

### Lemma C (prescribed semantic compression)

For every player,

\[
 |U_i(\mu)-U_i(\mu^{(m)})|\le {n(n-1)\over m}.         \tag{14}
\]

Couple each original clock with its cell image.  The terminal coalition is
unchanged unless some player pair has finite clocks in the same nonsingleton
gap.  For a fixed pair the probability of this event is at most

\[
 \sum_G\mu_i(G)\mu_j(G)
 \le {1\over m}\sum_G\mu_j(G)
 \le {1\over m}.                                       \tag{15}
\]

There are `n(n-1)/2` pairs.  Two normalized terminal rewards differ by at
most two.  The union bound proves (14).  Exact equal-date ties in marked
singletons and the all-`Never` event are unchanged.

### Lemma D (unrestricted-cap compression)

For every player,

\[
 |B_i(\mu)-B_i(\mu^{(m)})|\le {n(n-1)\over m}.         \tag{16}
\]

Fix player `i`.  Given an original deterministic quit time, use its compressed
cell date.  A payoff mismatch can occur only if:

- two of the `n-1` opponents occupy a common nonsingleton gap, of probability
  at most `((n-1)(n-2)/2)/m`; or
- an opponent occupies the nonsingleton gap containing the deviator's date,
  of probability at most `(n-1)/m`.

The total bad probability is at most

\[
 {n(n-1)\over 2m}.                                     \tag{17}
\]

Multiplying by reward diameter two gives (16).

For the reverse comparison, use the marked date of a singleton cell or any
integer representative of a genuine gap.  A compressed date after the last
support cell is compared with any original date after all marked singletons.
All clocks in the unbounded terminal gap are placed into the second bad event,
whose probability is still at most `(n-1)/m`; no date after all original
support is required.  Compare `Never` with `Never`.  Thus every pure-time
payoff in either model lies within the same error of a payoff in the other
model.  Taking suprema and invoking exact pure-time extremality proves (16)
for unrestricted behavioral caps.

Lemmas C and D give

\[
 \|z(\mu)-z(\mu^{(m)})\|_\infty\le\delta_m.            \tag{18}
\]

## Finite polynomial center

For `A_K`, use marginal variables

\[
 x_{i,t}\ge0,
 \qquad t\in\{0,\ldots,K-1,\mathsf{Never}\},
 \qquad \sum_t x_{i,t}=1.                              \tag{19}
\]

Equivalent prefix-occupation variables may be retained by the exact linear
accounts

\[
 s_{i,0}=1,
 \qquad s_{i,t+1}=s_{i,t}-x_{i,t},
 \qquad s_{i,K}=x_{i,\mathsf{Never}}.                  \tag{20}
\]

Here `s_(i,t)` is the probability that player `i` has not stopped before date
`t`.  For each nonempty `S subset I`, its exact first-quitter probability is

\[
 p_x(S)=\sum_{t=0}^{K-1}
       \left(\prod_{i\in S}x_{i,t}\right)
       \left(\prod_{j\notin S}s_{j,t+1}\right),
 \qquad
 U_i(x)=\sum_{\varnothing\ne S\subseteq I}p_x(S)r_i(S). \tag{21}
\]

The remaining probability `prod_i x_(i,Never)` is the all-Continue outcome
and has payoff zero.  Thus terminal coalition probabilities and prescribed
payoffs are explicit finite sums of product monomials.  Against opponents
supported below `K`, every payoff-distinct pure deviation is in

\[
 \{0,\ldots,K-1,K,\mathsf{Never}\}.                    \tag{22}
\]

For `tau<K` and for `tau=Never`, let `V_(i,tau)(x)` be the polynomial obtained
from (21) after replacing player `i`'s marginal by the corresponding point
mass.  The auxiliary after-support value is defined separately by adjoining
date `K` for the deviator while every opponent remains supported below `K`:

\[
 \begin{aligned}
 V_{i,K}(x)
  ={}&\sum_{\varnothing\ne S\subseteq I\setminus\{i\}}
       \left[\sum_{t=0}^{K-1}
        \left(\prod_{j\in S}x_{j,t}\right)
        \left(\prod_{\ell\in I\setminus(S\cup\{i\})}
          s_{\ell,t+1}\right)\right]r_i(S)\\
   &+\left(\prod_{j\ne i}x_{j,\mathsf{Never}}\right)r_i(\{i\}).
 \end{aligned}                                                \tag{23}
\]

Thus `V_(i,K)` does not arise from the sum in (21), whose dates stop at
`K-1`; it is the exact payoff of quitting strictly after all finite opponent
support.  The exact unrestricted cap graph is

\[
 B_i\ge V_{i,\tau}(x)\quad\text{for every }\tau,
 \qquad
 \prod_\tau(B_i-V_{i,\tau}(x))=0.                      \tag{24}
\]

The inequalities make `B_i` an upper bound and the product equation forces
equality with at least one candidate.  This remains exact on zero-probability
faces and at ties.  Pure-time extremality upgrades (24) to all behavioral
deviations.  Every feasible marginal tuple is behaviorally executable by the
checked stopping-law reconstruction theorem.  The checked encoder and decoder
identify the real feasible image of this finite rational polynomial system
exactly with the literal compact set `A_K`.  In ordinary real algebraic
geometry this is a semialgebraic presentation, but no Lean
`IsSemialgebraic`/RCF interface is asserted here.  The inclusion
`A_K subset A_(K+1)` follows by adding a zero-mass date.

The unboxed sets `N_m` and `R_M` are represented by finite rational polynomial
systems with one finite-clock witness for each neighborhood constraint.
Sup-norm distance is encoded by finitely many rational linear inequalities;
the objective is encoded by upper rows and one product-zero tightness row.
No projection is needed by the supplied-certificate checker.

## Carrier intersection and certified bracket

Every executable pair belongs to `N_m` by (18).  Since `N_m` is closed, it
also contains the closure of executable pairs.  Hence the entire terminal
semantic carrier belongs to every `R_M`.

Conversely, if `z` belongs to every `R_M`, then for each `m` there is an actual
finite-clock pair `a_m in A_(K_m)` with

\[
 \|z-a_m\|_\infty\le\delta_m\longrightarrow0.
\]

Thus `z` is in the closure of executable pairs, proving (6).  This proves only
carrier membership, not realization by one behavioral profile.

The function `F` is `2`-Lipschitz in semantic sup norm.  Actual pairs lie in
`R_M`, giving `L_M<=eta`; finite-clock centers are actual, giving `eta<=U_M`.
Every actual point of `A_(K_M)` belongs to every earlier neighborhood, hence
to `R_M`.  Conversely `R_M subset N_M`.  Every `z in R_M` has some
`a in A_(K_M)` within `delta_M`, and therefore

\[
 F(z)\ge F(a)-2\delta_M
      \ge U_M-{2n(n-1)\over M}.                         \tag{25}
\]

Taking the infimum over `R_M` proves (7) without claiming a lower minimizer.
The quantitative squeeze gives (8).  The minimum of `F` over the compact
carrier equals the infimum over executable profiles by continuity and the
checked sequential realization of carrier points.

## Exact certificate and semantic consumers

For rational `r` and rational `gamma`, the checked finite lower query at level
`M` is the rational polynomial system

\[
 z\in R_M(r),\qquad F(z)<\gamma                         \tag{26}
\]

with strictness encoded by a nonnegative gap and a multiplicative inverse.
The Lean verifier checks a supplied identity of the form `-1 =` a sum of
squares, plus sum-of-squares multiples of inequality rows, plus arbitrary
polynomial multiples of equality rows.  Such an identity proves (26)
infeasible.  The repository neither finds that identity nor proves this
certificate format complete.  Because every actual semantic pair lies in
`R_M` and `F` agrees there with unrestricted exploitability,

\[
 \gamma\le L_M\quad\Longrightarrow\quad
 \gamma\le\operatorname{Expl}_r(\sigma)
 \quad\text{for every behavioral profile }\sigma.      \tag{27}
\]

This is the actual-data adapter for a genuine counterexample certificate.

If `eta(r)=0`, then `L_M=0`, and (7) supplies an executable finite-clock
profile of exploitability at most `2n(n-1)/M` for every `M`.  These are the
all-errors terminal approximate Nash profiles consumed by
`quittingGame_exists_uniformEquilibriumPayoff_of_terminalNash_all_errors` in
`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`.
This is a semantic consumer conditional on the zero-gap branch, not a finite
certificate that the branch holds.

## Probability and agency audit

- **Probability mode.** Each strategy is represented by its complete PMF on
  finite dates plus `Never`.  Finite cumulative mass need not equal one.
- **Independence.** The common cell map is applied separately to each
  marginal.  Terminal events remain exact products of marginals.
- **Information.** Before absorption, the only public history is the number
  of prior all-Continue stages.  No additional observation or correlation is
  introduced.
- **Agency.** One deviator may use any behavioral strategy.  Exact checked
  pure-time extremality, rather than a stationarity assumption, justifies the
  cap formula and compression.
- **Stopping.** `Never` is never merged with a late finite cell.  An unbounded
  terminal finite gap is compressed as finite mass and charged in the error
  event.
- **Randomization.** Polynomial centers allow arbitrary real marginal
  probabilities.  Rational input makes the defining polynomial system
  rational; an optimizer may be algebraic.

## Boundary regressions

### Fixed-horizon escape

The cell dates depend on the whole supplied stopping laws, not on an absolute
horizon.  An arbitrarily late profitable deterministic deviation maps to its
gap cell or to the after-support date in (22).  Thus finite-deadline Nash
profiles do not evade the lower-bound map.

### Diffuse finite mass and positive-debt nonrealization

A sequence may move finite mass through later cells while its semantic pairs
converge to an unrealized positive-debt carrier point.  Equation (6) retains
that point in every outer set but does not call it executable.  The hierarchy
therefore passes the known nonattainment boundary rather than assuming cap
continuity on raw stopping laws.

### All-`Never`

If all marginals are `Never`, every finite gap has zero mass and compression
is exact.  The all-Continue payoff and each pure-time deviation remain in the
finite cap graph.

### Deterministic late dates and literal ties

A deterministic finite atom crosses all quantile levels at its own date, so
that date is a marked singleton.  Arbitrarily late deterministic dates and
equal-date coalitions are preserved exactly, independent of their numerical
date.

### Zero-probability faces

Equation (24) remains the graph of a finite maximum even when profile mass at
a listed date is zero.  The deviation at that date remains available to the
unilateral deviator.  Adding a zero-mass date proves `A_K subset A_(K+1)`
without deleting the old after-support deviation value.

### One-player boundary

For `n=1`, no clock-order collision is possible.  Prescribed payoff depends
only on finite-versus-Never mass, which compression preserves, and the cap has
no opponent clocks.  Hence `delta_m=0`, matching (3).

## Source correspondence and novelty

The proof uses the following checked declarations.

1. `sSup_range_quittingTerminalPayoff_update_eq_pureTime` in
   `UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean` gives
   exact unrestricted pure-time extremality.
2. `quittingBehaviorStoppingLaw` in
   `UniformEquilibrium/Quitting/Paths/BehaviorStoppingLaw.lean` and
   `quittingStoppingLawBehaviorStrategy` with
   `quittingBehaviorStoppingLaw_stoppingLawBehaviorStrategy` in
   `UniformEquilibrium/Quitting/Terminal/StrategicallyPrecompactWatchdogProperBoundary.lean`
   give the two-way complete stopping-law adapter.
3. `quittingTerminalSemanticCarrier`,
   `exists_terminalProfile_sequence_tendsto_semanticPair`, and
   `quittingTerminalSemanticCarrier_isCompact` in
   `UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean` give the exact
   carrier semantics.
4. `quittingTerminalSemanticExploitability_pair`, continuity of semantic
   exploitability, and
   `quittingTerminalExploitabilityInf_le_semanticCarrier` in
   `UniformEquilibrium/Quitting/Root/TerminalSemanticEqualityStratum.lean`
   identify the objective and its closure behavior.

The prior checked approximation was
`exists_elementaryCompressedProfile_terminalSemantics_close` in
`UniformEquilibrium/Quitting/Terminal/TailCompression/ElementaryTailSemanticReduction.lean`.
It is used by
`terminalSemanticCarrier_eq_closure_finiteElementarySemanticReachable` in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticGlobalDebtBarrierCertificate.lean`.
Those declarations provide escape-complete approximation and a finite-word
carrier characterization, but not a profile-independent support-cardinality
bound, an explicit uniform rate, or a nested rational polynomial
lower/upper bracket.

The new content is the common ordered quantile quotient, its simultaneous
prescribed-payoff and unrestricted-cap modulus, the finite polynomial
maximum graph, and the `2n(n-1)/M` certified bracket.  A narrow symbol and
phrase search found no prior theorem with these data.  No external paper is
used.

## Formalization record

- **M:** Both independent reviews passed the finite-player compression and
  hierarchy as ordinary mathematics.  A later audit caught empty virtual gap
  cells in the first quotient; the formalization repairs this by ranking only
  attained cells.  The active-cell construction was then re-audited, including
  internal empty gaps, the terminal gap, and `Never`.
- **L:** `hasEscapeAwareQuantileClockCompression_of_normalized`,
  `iInter_escapeAwareQuantileClockOuter_normalized_eq_carrier`,
  `escapeAwareQuantileClock_normalized_quantitative_bracket`, and
  `sSup_range_escapeAwareQuantileClockLower` in
  `Research/Quitting/EscapeAwareQuantileClockHierarchy.lean` prove the
  analytic hierarchy and convergence.  The exact center presentation is
  `finiteClockPolynomialSemanticImage_eq_reachable` in
  `Research/Quitting/FiniteClockPolynomialCenter.lean`.  The exact unboxed
  multi-center query is `quantileClockLowerQueryFeasible_iff`, and supplied
  certificate soundness is
  `ratCast_le_escapeAwareQuantileClockLower_normalized_of_certificate`, both
  in `Research/Quitting/EscapeAwareQuantileClockPolynomialLower.lean`.
- **A:** The checked compression starts from every actual behavioral profile,
  reconstructs its complete stopping laws, preserves independent product
  provenance and the `Never` atom, and controls the unrestricted behavioral
  cap.  The polynomial center encoder and decoder identify feasible center
  assignments with literal finite-clock stopping-law profiles.
- **C:** The analytic consumer gives the carrier equality, finite lower/upper
  bracket, convergence of `L_M` to the true executable infimum, and actual
  finite-clock witnesses on the zero-infimum branch.  The certificate consumer
  turns any supplied rational infeasibility identity into both `gamma<=L_M`
  and a global lower bound on every executable profile.

## Scope and nonclaims

- This is a theorem for every fixed nonempty finite player set; its Fin4
  corollary is the application relevant to the maintained question.
- It is not yet a semidecision procedure for `eta(r)>0`: no complete
  certificate generator or proof-trace checker for all infeasible queries has
  been formalized.
- It does not exhibit a positive-gap reward table or positive finite
  certificate.
- It does not formalize `IsSemialgebraic`, CAD, quantifier elimination,
  Positivstellensatz completeness, certificate search, decidability, or
  computability of `eta(r)`.
- The checked lower value is an `sInf` over the unboxed outer system; no lower
  minimizer or equivalence with a separately boxed optimization problem is
  claimed.
- It does not prove `eta(r)=0` for Fin4, eliminate the hard residual, or settle
  the finite-quitting uniform-equilibrium conjecture.
- A point in the intersection of the outer hierarchy is proved to lie in the
  semantic carrier, not to be realized by one behavioral profile.
- The zero-gap terminal approximate-Nash consumer applies only after the
  hypothesis `eta(r)=0` is established; no finite hierarchy level establishes
  that hypothesis.
- No chronology, Bellman edge, prescribed-payoff path, or cumulative-charge
  return is produced.
