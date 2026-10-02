# Escape-aware quantile-clock semialgebraic hierarchy

## Status

**Independently reviewed PASS as ordinary mathematics and exported.**
Reviews:
[`CODEX_MINER`](../feedback/CODEX_EULER__ESCAPE_AWARE_QUANTILE_CLOCK_SEMIALGEBRAIC_HIERARCHY__BY_CODEX_MINER.md)
and
[`CODEX_RAMSEY`](../feedback/ESCAPE_AWARE_QUANTILE_CLOCK_SEMIALGEBRAIC_HIERARCHY__BY_CODEX_RAMSEY.md).
Export:
[`ESCAPE_AWARE_QUANTILE_CLOCK_SEMIALGEBRAIC_HIERARCHY.md`](../formalized/ESCAPE_AWARE_QUANTILE_CLOCK_SEMIALGEBRAIC_HIERARCHY.md).
The main
result is a sound monotone finite semialgebraic outer hierarchy whose certified
lower bounds converge to the unrestricted terminal exploitability infimum.
It treats `Never` exactly and does not infer realization of a compactified
semantic point.

The result gives an exact counterexample semidecision procedure and certified
two-sided approximations of the infimum.  It does **not**, by itself, give a
terminating zero-versus-positive decision procedure, eliminate the current
Fin4 hard residual, or construct a chronology from an unrealized carrier
point.  Those limitations matter for the stronger output gate in
`questions/ESCAPE_AWARE_FIN4_CERTIFICATE_SEARCH.md`.

## 1. Question and inspected interfaces

Fix a rational reward table on `Fin 4` with

\[
  |r_i(S)|\leq 1
\]

for every nonempty quitting coalition.  For an executable behavioral profile
`sigma`, write

\[
  z(\sigma)=(U(\sigma),B(\sigma))\in[-1,1]^8,
  \qquad
  F(U,B)=\max\bigl(0,\max_i(B_i-U_i)\bigr).
\]

Thus `F(z(sigma))` is literal unrestricted terminal exploitability and

\[
  \eta(r)=\inf_\sigma F(z(\sigma)).
\]

The checked interfaces used here are:

- `sSup_range_quittingTerminalPayoff_update_eq_pureTime` in
  `UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean`:
  arbitrary unilateral behavioral deviations have exactly the same supremum
  as deterministic finite quit times together with `Never`;
- `quittingBehaviorStoppingLaw` in
  `UniformEquilibrium/Quitting/Paths/BehaviorStoppingLaw.lean` and
  `quittingStoppingLawBehaviorStrategy` together with
  `quittingBehaviorStoppingLaw_stoppingLawBehaviorStrategy` in
  `UniformEquilibrium/Quitting/Terminal/StrategicallyPrecompactWatchdogProperBoundary.lean`:
  a behavioral strategy induces a complete law on `Option Nat`, and every such
  law has a canonical behavioral realization;
- `quittingTerminalSemanticCarrier`, defined as the closure of executable
  semantic pairs, and
  `exists_terminalProfile_sequence_tendsto_semanticPair` in
  `UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`;
- continuity of semantic exploitability and
  `quittingTerminalExploitabilityInf_le_semanticCarrier` in
  `UniformEquilibrium/Quitting/Root/TerminalSemanticEqualityStratum.lean`.

The closest checked result is
`exists_elementaryCompressedProfile_terminalSemantics_close` in
`UniformEquilibrium/Quitting/Terminal/TailCompression/ElementaryTailSemanticReduction.lean`,
used by
`terminalSemanticCarrier_eq_closure_finiteElementarySemanticReachable` in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticGlobalDebtBarrierCertificate.lean`.
It gives escape-complete approximation by an elementary tail cap, but not a
profile-independent finite support-cardinality bound, an explicit uniform
rate, or the nested semialgebraic lower/upper bracket below.  A narrow search
found no prior common-quantile clock theorem, no sets `A_K,N_m,R_M`, and no
existing `24/M` exploitability bracket.

## 2. Common quantile-clock compression

Let `mu_i` be the four independent stopping laws on
`Nat union {Never}` induced by an arbitrary behavioral profile.  Fix an
integer `m >= 1`.

For each player `i` and each `j=1,...,m`, include in `H_i` the first finite
date at which the finite-time cumulative mass of `mu_i` reaches `j/m`, if it
ever does.  Put

\[
  H=\bigcup_i H_i.
\]

Then `|H| <= 4m`.  Partition `Nat` into the singleton cells `{h}`, `h in H`,
and the maximal gap intervals before, between, and after these singletons.
The number of cells is at most

\[
  K_m:=8m+1.
\]

`Never` is a separate cell and is never merged with a finite date.

### Lemma 2.1 (small common gaps)

For every nonsingleton gap cell `G` and every player `i`,

\[
  \mu_i(G)\leq {1\over m}.
\]

#### Proof

If a gap carried more than `1/m`, the cumulative finite mass would cross one
of the levels `j/m` inside that gap.  The first crossing date would belong to
`H_i`, contradicting that the cell is a gap.  The initial gap is covered by
the first level; the terminal gap is covered by the last reached level (or
has total finite mass below the first level).  This also covers finite mass
strictly below one.  QED.

Map the ordered finite cells monotonically to consecutive dates
`0,...,k-1`, where `k<=K_m`, and push each `mu_i` forward.  Pad unused dates
up to `K_m-1` with zero mass.  Denote the compressed laws by `mu_i^(m)`.

This is an exact product-law construction: each marginal is pushed forward
separately, so the joint law remains the product of four complete stopping
laws.  The `Never` mass is unchanged.  Every large finite atom selected as a
quantile crossing remains a singleton, so literal equal-date ties at marked
dates are also unchanged.

### Lemma 2.2 (prescribed-payoff compression)

Couple the original and compressed clocks by applying the cell map to each
sampled original clock.  Let `E` be the event that two players' finite clocks
fall in the same nonsingleton gap.  Off `E`, the earliest-quitter coalition,
including ties and the all-`Never` outcome, is identical before and after
compression.  Moreover,

\[
  \Pr(E)
  \leq \sum_{i<j}\sum_G\mu_i(G)\mu_j(G)
  \leq {6\over m}.
\]

Indeed, for a fixed pair, `mu_i(G)<=1/m` and the disjoint gap masses of the
other player sum to at most one.  Since two terminal rewards in `[-1,1]`
differ by at most two,

\[
  \|U(\mu)-U(\mu^{(m)})\|_\infty\leq {12\over m}.       \tag{2.1}
\]

This bound deliberately counts a same-original-time event inside a gap as
bad even though it is actually preserved.

### Lemma 2.3 (unrestricted-cap compression)

For every player `i`,

\[
  |B_i(\mu)-B_i(\mu^{(m)})|\leq {12\over m}.           \tag{2.2}
\]

#### Proof

By checked pure-time extremality it is enough to compare deterministic finite
quit times and `Never`.

Given an original finite time `t`, use its compressed cell date.  A payoff
mismatch can occur only if:

1. two of the three opponents lie in one common nonsingleton gap; or
2. an opponent lies in the nonsingleton gap containing `t`.

The two probabilities are bounded respectively by `3/m` and `3/m`.
Thus every original pure-time payoff lies within `12/m` of a compressed
pure-time payoff.

Conversely, for a compressed date belonging to a genuine cell, choose an
original representative in that cell.  The same estimate applies.  Any
compressed date after the last support cell is compared with an original
date after all marked singletons.  A mismatch involving the terminal gap has
probability at most `3/m`, while opponent-pair gap collisions cost another
`3/m`.  The compressed `Never` deviation is compared with original `Never`;
only opponent-pair gap collisions remain.  Taking suprema in both directions
proves (2.2).  The reduction from behavioral deviations to this pure-time
supremum is exact, not a restricted-strategy approximation.  QED.

Combining (2.1) and (2.2), every executable semantic pair has a finite-clock
executable pair within

\[
  \delta_m:={12\over m}                                  \tag{2.3}
\]

in the coordinate sup norm.

## 3. The finite semialgebraic clock set

For `K>=1`, let `A_K(r) subset [-1,1]^8` be the semantic pairs realized by
profiles whose four stopping laws are supported on

\[
  \{0,1,\ldots,K-1,\mathsf{Never}\}.
\]

This is a compact rational semialgebraic set.

One explicit finite presentation has marginal variables

\[
  x_{i,t}\geq0,
  \qquad t\in\{0,\ldots,K-1,\mathsf{Never}\},
  \qquad \sum_t x_{i,t}=1.
\]

If occupation variables are preferred, add

\[
  s_{i,0}=1,
  \qquad s_{i,t+1}=s_{i,t}-x_{i,t},
  \qquad s_{i,K}=x_{i,\mathsf{Never}}.
\]

These are exact finite-prefix survival accounts, not free flow variables.
In the compression proof, the mass of the final unmarked finite gap is an
ordinary finite-cell mass and the genuine `Never` atom is
`x_(i,Never)`; thus the two possible forms of tail mass are not identified.

Product provenance is imposed rather than relaxed: every terminal coalition
probability is the corresponding finite sum of monomials in the four
marginals.  Hence every prescribed payoff `U_i` is a multilinear polynomial.

Against such opponents, all payoff-distinct pure deviations are the dates

\[
  0,\ldots,K-1, K, \mathsf{Never}.
\]

Here date `K` represents every finite time strictly after the support.  Write
their polynomial payoffs as `V_(i,tau)(x)`.  Exact unrestricted caps are
encoded by

\[
  B_i\geq V_{i,\tau}(x)\quad\hbox{for every }\tau,
  \qquad
  \prod_\tau(B_i-V_{i,\tau}(x))=0.                       \tag{3.1}
\]

Thus one of the finitely many inequalities is tight.  Checked pure-time
extremality upgrades (3.1) to the supremum over all behavioral deviations.
The stopping-law reconstruction theorem makes every feasible marginal tuple
an executable behavioral profile.  This proves both semialgebraicity and the
actual-data adapter.  Adding a zero-probability last date gives
`A_K subset A_(K+1)`.

## 4. A nested outer hierarchy

For `m>=1`, define the closed semialgebraic neighborhood

\[
  N_m(r)=\{z\in[-1,1]^8:
       \exists a\in A_{K_m}(r),\ \|z-a\|_\infty\leq\delta_m\}.
\]

Define

\[
  R_M(r)=\bigcap_{m=1}^M N_m(r).                         \tag{4.1}
\]

This can be retained as one finite extended semialgebraic system, with a
separate finite-clock witness for each `m<=M`; no projection is required for
verification.

### Theorem 4.1 (soundness and exact intersection)

Every executable semantic pair belongs to every `R_M(r)`, and

\[
  R_{M+1}(r)\subseteq R_M(r),
  \qquad
  \bigcap_{M=1}^\infty R_M(r)
   =\operatorname{Carrier}(r).                           \tag{4.2}
\]

#### Proof

Membership of every executable pair in `N_m` is Lemmas 2.1--2.3.  Since
`N_m` is closed, it also contains the closure of executable semantic pairs,
namely the checked terminal semantic carrier.  This proves the forward
inclusion in (4.2) and soundness.

Conversely, if `z` lies in every `R_M`, then for every `m` there is an
`a_m in A_(K_m)` with `||z-a_m||_infty<=delta_m`.  Each `a_m` is executable
and `delta_m -> 0`; hence `z` is in the closure of executable pairs.  QED.

The equality is expressly an equality with the semantic **carrier**, not
with the set of realized behavioral profiles.  A diffuse/bubble limit may be
unrealized.  Escape through later and later finite cells is retained through
the changing witnesses `a_m`; it is not identified with the exact `Never`
coordinate.

## 5. Certified bounds and convergence

The function `F` is continuous, rational semialgebraic, and `2`-Lipschitz in
the coordinate sup norm.  Define

\[
  L_M(r)=\min_{z\in R_M(r)}F(z),
  \qquad
  U_M(r)=\min_{a\in A_{K_M}(r)}F(a).                     \tag{5.1}
\]

Both minima exist on compact semialgebraic sets.

### Theorem 5.1 (sound lower certificates and quantitative convergence)

For every normalized rational four-player table,

\[
  0\leq L_M(r)\leq \eta(r)\leq U_M(r),                  \tag{5.2}
\]

`L_M` is monotone nondecreasing, and

\[
  0\leq U_M(r)-L_M(r)\leq {24\over M}.                  \tag{5.3}
\]

Consequently

\[
  \sup_M L_M(r)=\eta(r),
  \qquad
  |U_M(r)-\eta(r)|\leq {24\over M}.                     \tag{5.4}
\]

#### Proof

For an actual profile, take `E_M(sigma)=z(sigma)`.  Theorem 4.1 makes this a
feasible point of `R_M`, and

\[
  F(E_M(\sigma))=\operatorname{Expl}_r(\sigma).
\]

This is exactly the lower-bound direction required by the question.
Finite-clock profiles are actual profiles, giving the right inequality in
(5.2).

Every point of `A_(K_M)` is executable and therefore lies in every `N_m`,
`m<=M`; hence `A_(K_M) subset R_M`.  Conversely `R_M subset N_M`.  If `z`
minimizes `F` on `R_M`, choose `a in A_(K_M)` within `delta_M`.  Then

\[
  L_M=F(z)\geq F(a)-2\delta_M
      \geq U_M-{24\over M},
\]

which proves (5.3).

Alternatively, nested compactness, continuity of `F`, and (4.2) show that
`L_M` converges to the minimum of `F` on the semantic carrier.  That minimum
equals the infimum over executable pairs: one inequality is inclusion, and
the reverse follows by approximating every carrier point with the checked
executable realizing sequence and using continuity.  This proves (5.4).
QED.

### Exact certificate format

For rational `r`, the assertion `gamma <= L_M(r)` is the infeasibility of the
finite rational real-closed-field system

\[
  z\in R_M(r),\qquad F(z)<\gamma.
\]

It therefore admits exact algebraic verification by real quantifier
elimination/CAD, or by any independently checked equivalent real-algebraic
certificate.  Floating-point output is not used.  The upper witness is an
algebraic finite-clock product law; stopping-law reconstruction realizes it
behaviorally.  Rational interior approximations can be used with an explicit
arbitrarily small continuity loss if a rational executable profile is wanted.

If `eta(r)>0`, (5.4) implies that some finite level has `L_M>0`, so this is a
complete semidecision procedure for a true counterexample.  If `eta(r)=0`,
(5.2)--(5.3) give `L_M=0` and an executable finite-clock profile with
exploitability at most `24/M` at every level.

## 6. Mandatory boundary tests

### Horizon escape

No absolute quitting horizon is fixed.  The common cells are selected from
the actual profile and may occur arbitrarily late.  Later profitable pure
times are compressed to a gap cell or the after-support deviation `K_m` and
are included in the cap comparison.  Thus a finite-deadline Nash escape does
not evade soundness.

### Diffuse positive debt and bubble mass

The hierarchy converges to the closed semantic carrier, not to the realized
profile set.  It makes no realization inference from positive debt.  Bubble
mass can appear through a sequence of changing finite cells while `Never`
mass remains an exact separate coordinate.

### Product provenance

Every center `A_K` uses four marginal simplexes and their exact product
monomials.  The neighborhoods enlarge semantic coordinates only after an
actual product-law center has been supplied.  No arbitrary coalition-flow
purification is assumed.

### Unrestricted deviations

The finite deviation menu is complete only for a finite-clock opponent
profile.  The comparison to the original profile invokes the checked exact
pure-time-extremality theorem, which already quantifies over every unilateral
behavioral deviation.

### All-`Never`

`Never` is never merged with a finite tail cell.  The all-`Never` outcome and
the deviation `Never` are included exactly at every level.

## 7. What this does and does not decide

This is a complete soundness-and-convergence theorem for the proposed outer
hierarchy, with a uniform `24/M` certified bracket.  It is stronger than a
sampled finite-horizon search and directly satisfies the relaxation
soundness contract.

It is not yet a terminating algorithm that decides whether the computable
real `eta(r)` is exactly zero.  A positive value is eventually certified, and
under the mathematical hypothesis `eta(r)=0` the upper witnesses form a
terminal approximate-Nash family, but no finite stage can in general certify
that all future lower bounds remain zero.  Nor does this note prove that the
Fin4 hard residual has `eta=0` or `eta>0`.  Therefore it should remain internal
pending the required second unrestricted-strategy review before any export,
and pending a decision about whether the question's progress gate accepts the
convergent hierarchy itself or requires a further zero-test/semantic consumer.

## 8. Requested independent checks

1. Check the quantile-gap statement at finite-mass and final-gap boundaries.
2. Re-derive the `6/m`, `12/m`, and `24/m` constants, especially the reverse
   comparison for compressed after-support deviations.
3. Check that (3.1) is an exact cap graph on every zero-probability boundary
   face.
4. Check the use of closed neighborhoods in proving that every carrier point
   belongs to every `R_M`.
5. Search for a prior finite-clock density theorem that subsumes the common
   quantile construction.
