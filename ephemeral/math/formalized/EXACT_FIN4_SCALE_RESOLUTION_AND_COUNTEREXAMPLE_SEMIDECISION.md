# Exact Fin4 scale resolution and counterexample semidecision

Authors: exact-search artifact author; `CODEX_ROOT` (scope correction and
export synthesis)

Independent reviews:
[`CODEX_GODEL`](../feedback/RIGID_FIN4_EXACT_SEARCH_THEOREM__BY_CODEX_GODEL.md),
[`CODEX_FERMAT`](../feedback/RIGID_FIN4_EXACT_SEARCH_THEOREM__BY_CODEX_FERMAT.md)

## Lean formalization record

The executable interval layer is checked in
`MathUE/Interval/RationalMaxExpression.lean`,
`MathUE/Interval/RationalLowerBoxTree.lean`, and
`MathUE/Interval/RationalLowerBoxSearch.lean`.  Its main seals are
`RationalMaxExpression.evalInterval_sound`,
`RationalLowerBoxProblem.verifies_sound`, and
`RationalLowerBoxProblem.exists_search_verifies_of_feasible_objective_gt`.

The exact Fin4 analytic adapter is checked in
`Research/Quitting/FinFourSingleShellOuter.lean` and
`Research/Quitting/FinFourRationalSingleShellLower.lean`.
`finFourRationalSingleShellFeasibleValues_eq_shellImage` identifies the
rational expression problem with the real single shell,
`finFourRationalSingleShellProblemValue_eq_finFourSingleShellLower` identifies
their values, `finFourRationalSingleShellSearch_sound` proves lower-tree
soundness, and `exists_finFourRationalSingleShellSearch_of_lt_lower` proves
strict completeness.

The upper code, actual profile adapter, and completeness theorem are checked
in `Research/Quitting/FinFourRationalFiniteClockProfile.lean` and
`Research/Quitting/FinFourRationalFiniteClockProfileCompleteness.lean`.
`RationalFinFourFiniteClockProfileCode.checkedCandidateAt_sound` returns a
literal finite-clock behavioral profile with unrestricted exploitability
below the rational target, and
`exists_checkedCandidateAt_of_finiteClockStoppingLaws` proves enumeration
completeness under the strict target margin.

Theorem A and both semantic branches of Theorem B are checked in
`Research/Quitting/FinFourExactScaleResolution.lean`:

- `finFourExactScaleStep` is the total proof-free upper-first stage function;
- `exists_finFourExactScaleStep` proves termination at every positive rational
  scale of every normalized rational Fin4 reward code;
- `finFourExactScaleStep_upper_sound` and
  `finFourExactScaleStep_lower_infimum_sound` prove the exact upper and lower
  meanings;
- `finFourExactScaleStep_lower_terminalGap` and
  `finFourExactScaleStep_lower_no_uniformEquilibriumPayoff` consume lower
  output at the literal `epsilon / 8` gap;
- `exists_finFourExactScaleStep_upper_profile_of_infimum_eq_zero` produces an
  actual upper profile at every positive scale when the infimum is zero;
- `finFourExactScale_profiles_all_errors_of_infimum_eq_zero` supplies actual
  profiles at every positive real error; and
- `quittingGame_exists_uniformEquilibriumPayoff_of_finFourExactScale_infimum_eq_zero`
  selects one fixed uniform-equilibrium payoff.  The profiles may vary with
  the error; the payoff does not.

`exists_finFourExactScaleStep_lower_of_infimum_pos` is the complementary
positive-infimum lower event, and
`finFourExactScale_infimum_zero_or_lower_event` states the literal global fork
for one normalized rational table.

Reward robustness, positive scaling, normalized rational approximation, and
fair code enumeration are checked in
`Research/Quitting/TerminalExploitabilityRewardRobustness.lean`,
`Research/Quitting/FinFourRationalRewardApproximation.lean`, and
`Research/Quitting/FinFourPositiveRationalRewardApproximation.lean`.
Theorem C is the exact equivalence
`exists_finFourCounterexampleStep_iff_exists_real_infimum_pos` in
`Research/Quitting/FinFourCounterexampleSemidecision.lean`.
`finFourCounterexampleStep` is a total computable stage function which emits
only lower certificates, and `finFourCounterexampleStep_sound` supplies the
normalized table, positive infimum, terminal gap, and literal no-uniform-payoff
consumer.

Evidence seals are `M/L/A/C`: the finite searches and all semantic
translations are checked; upper output is an actual behavioral profile;
lower output reaches nonexistence; and the zero branch reaches one fixed
uniform-equilibrium payoff.  The global claim is existential recursive
enumerability.  No positive table is produced, this is not a decision
procedure for a supplied real table, and nontermination has no conclusion.

## Exact statement

Let the players be `I = {0,1,2,3}`.  Let

\[
 r:\{S\subseteq I:S\ne\varnothing\}\longrightarrow\mathbb Q^4
\]

be a rational quitting reward table satisfying `|r_i(S)| <= 1` for every
player and nonempty coalition.

For a behavioral profile `sigma`, write `U_i^r(sigma)` for player `i`'s
terminal payoff and

\[
 B_i^r(\sigma)=\sup_{\tau_i}
 U_i^r(\sigma[i\leftarrow\tau_i])
\]

for the supremum over every complete unilateral behavioral replacement.  Put

\[
 \operatorname{Expl}_r(\sigma)
 =\max_{i<4}\bigl(B_i^r(\sigma)-U_i^r(\sigma)\bigr),
 \qquad
 \eta(r)=\inf_\sigma\operatorname{Expl}_r(\sigma).
\]

### Theorem A: exact resolution at every rational scale

For every rational `epsilon > 0`, there is an explicit exact algorithm which
terminates and returns one of the following finite objects.

1. A rational interval-tree certificate proving

   \[
   \frac{\varepsilon}{4}\le \eta(r).
   \tag{A1}
   \]

   The tree can be verified using rational arithmetic alone after regenerating
   the finite expression system from the sixty reward coordinates.

2. Four rational stopping laws with a common finite clock and a separate
   Never atom.  Their independent product profile `sigma_epsilon` satisfies

   \[
   \operatorname{Expl}_r(\sigma_\varepsilon)
   <\frac{3\varepsilon}{4}<\varepsilon.
   \tag{A2}
   \]

The cap checked in both alternatives is the unrestricted behavioral cap.  It
is not a stationary, bounded-memory, or bounded-deadline surrogate.

If (A1) is returned, then for every profile some player has cap gain at least
`epsilon/4`.  The supremum defining that cap need not be attained.  For every
smaller positive value, in particular `epsilon/8`, an actual behavioral
deviation has at least that gain.  Hence (A1) supplies the checked terminal-gap
semantics needed to rule out a uniform-equilibrium payoff.

### Theorem B: the productive global fork

Run Theorem A at `epsilon_k = 2^(-k)` and stop at the first lower certificate.

- The process stops after finitely many scales if and only if `eta(r) > 0`.
- If `eta(r) = 0`, it never produces a lower certificate and emits actual
  finite-clock product profiles whose exploitabilities tend to zero.

Thus the zero-gap branch is productive but infinite.  Its emitted profiles
give terminal approximate Nash profiles at every positive error.  The checked
terminal selection theorem then supplies one fixed uniform-equilibrium payoff.
No finite initial sequence of upper profiles certifies that the process will
remain in the zero-gap branch.

### Theorem C: Fin4 counterexamples are recursively enumerable

There is an exhaustive exact semidecision procedure for a negative answer to
the Fin4 conjecture.  Enumerate all normalized rational Fin4 reward tables and
dovetail all their dyadic scale processes.  If any real Fin4 reward table has
`eta(r) > 0`, this exhaustive process eventually returns a rational reward
table and a finite certificate of a positive all-behavior lower bound.

Conversely, every returned lower certificate is sound.  Nontermination does
not prove the conjecture.

## Conjecture-facing change

This result strictly narrows
[`ESCAPE_AWARE_FIN4_CERTIFICATE_SEARCH.md`](../questions/ESCAPE_AWARE_FIN4_CERTIFICATE_SEARCH.md).
The project already had the escape-aware finite-clock hierarchy, exact
product-law centers, a supplied polynomial-certificate verifier, and the
`24/N` quantitative bracket.  It did not have a concrete complete certificate
generator, a completeness theorem for its proof traces, or a positive-gap
semidecision procedure.

Theorem A supplies the complete per-query generator and exact proof language.
Theorem C removes positive-gap semidecision from the list of missing
algorithmic layers.  This is not a solution of the Fin4 conjecture and does
not eliminate a structural atlas component.

In particular, this result does not answer
`FIN4_INERT_MACHINE_CERTIFICATE_SEARCH.md`.  If a rational strict-inert source
with positive minimum debt is supplied externally, Theorem B eventually
certifies the positive gap already implied by that hypothesis.  It neither
constructs such a source nor proves it impossible, and the interval
certificate contains no inert-source fields.

## Definitions and assumptions

### Behavioral strategies and stopping laws

Before absorption, the only public history at date `t` is that every player
has Continued at all earlier dates.  A behavioral strategy therefore induces
a probability law on

\[
 \overline{\mathbb N}=\mathbb N\cup\{\mathsf{Never}\}.
\]

Player randomizations are independent, so a behavioral profile induces the
product of the four marginal stopping laws.  The terminal coalition is the
set of players attaining the least finite stopping time.  If all four choices
are Never, terminal payoff is zero.

Against fixed opponents, the deviating player's payoff is affine in its
stopping law.  Therefore its supremum over all behavioral deviations equals
the supremum over deterministic finite dates and Never.  This observation is
used only through the checked pure-time extremality and finite-clock cap
results named below.

### The final-shell finite-clock center

For a positive integer `N`, set

\[
 T_N=8N+1,
 \qquad
 \rho_N=\frac{12}{N}.
\tag{1}
\]

A center consists of four marginal probability laws

\[
 x_i=(x_{i,0},\ldots,x_{i,T_N-1},x_{i,\infty})
\]

with nonnegative coordinates summing to one.  Add an auxiliary date `T_N`
whose prescribed mass is constrained to zero but which remains available as
a pure deviation.

For observer `i`, the center payoff is

\[
 U_i(x)=
 \sum_{t<T_N}\ \sum_{\varnothing\ne S\subseteq I}
 r_i(S)
 \prod_{j\in S}x_{j,t}
 \prod_{j\notin S}
 \left(x_{j,\infty}+\sum_{s=t+1}^{T_N-1}x_{j,s}\right).
\tag{2}
\]

For a player `i`, replace its marginal by a deterministic date
`q in {0,...,T_N}` or by Never and evaluate (2) on the extended clock.  Define

\[
 B_i(x)=\max_{q\in\{0,\ldots,T_N,\mathsf{Never}\}}
 U_i(x[i\leftarrow q]).
\tag{3}
\]

Equation (3) is the exact unrestricted cap.  Against opponents supported
strictly before `T_N`, every finite date later than `T_N` is payoff-equivalent
to `T_N`; Never remains distinct on the event that every opponent chooses
Never.

Let `C_N` be the set of semantic pairs `(U(x),B(x))` of these literal product
profiles.  Define the single-shell outer set

\[
 O_N=\left\{(u,b):\exists c\in C_N,\
 \|u-c^U\|_\infty\le\rho_N,\
 \|b-c^B\|_\infty\le\rho_N\right\}.
\tag{4}
\]

Finally put

\[
 E(u,b)=\max(0,b_0-u_0,\ldots,b_3-u_3),
 \qquad
 A_N(r)=\min_{z\in O_N}E(z).
\tag{5}
\]

The finite simplexes are compact, so `C_N` and `O_N` are compact and the
minimum in (5) is attained.

### Rational interval-tree certificates

The finite expression language contains rational constants, variables,
negation, addition, multiplication, and binary maximum.  Its variables are:

- the eight coordinates of one common point `(u,b)`;
- the four finite-clock marginal simplexes; and
- the four zero auxiliary masses.

The center payoff and cap are substituted by (2)--(3).  Equalities express
the simplex sums and auxiliary zeros.  Required-nonnegative inequalities
express nonnegative masses and the sixteen coordinatewise bounds in (4).
The root box is rational and compact: probability coordinates lie in `[0,1]`
and common semantic coordinates lie in
`[-1-rho_N,1+rho_N]`.

Natural rational interval evaluation is defined recursively.  A lower
certificate is a finite binary tree whose internal nodes split one rational
coordinate interval and whose leaves have one of three reasons:

1. the interval enclosure of a required equality omits zero;
2. the upper endpoint of a required-nonnegative expression is negative; or
3. the lower endpoint of the objective enclosure is at least `gamma`.

The verifier regenerates all expressions from `r`, evaluates each leaf using
exact rational intervals, and checks that the two children of every split
cover their parent.

## Source correspondence

The analytic and semantic foundation is checked in the following files.

- `quantileClockSupport_fin4` and `quantileClockRadius_fin4` in
  `Research/Quitting/EscapeAwareQuantileClockHierarchy.lean` give exactly
  (1).
- `hasEscapeAwareQuantileClockCompression_of_normalized` and its forward and
  reverse pure-time transport lemmas in
  `Research/Quitting/EscapeAwareQuantileClockTransport.lean` preserve Never,
  product provenance, prescribed payoff, and the unrestricted cap.
- `escapeAwareQuantileClock_fin4_normalized_quantitative_bracket` in
  `Research/Quitting/EscapeAwareQuantileClockHierarchy.lean` gives the
  `24/N` lower/upper objective gap.
- `finiteClockCenterPair_eq_terminalSemanticPair_of_satisfies` and
  `exists_finiteClockCandidate_payoff_eq_continuationBestResponseValue` in
  `Research/Quitting/FiniteClockPolynomialCenter.lean` identify the finite
  polynomial center and finite maximum with an actual profile and its cap.
- `quantileClockLowerQueryFeasible_iff` and
  `ratCast_le_quittingTerminalExploitabilityInf_normalized_of_certificate` in
  `Research/Quitting/EscapeAwareQuantileClockPolynomialLower.lean` give the
  existing supplied-certificate soundness route.
- `quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
  in
  `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`
  consumes the infinite upper stream.
- `not_exists_uniformEquilibriumPayoff_iff_exists_terminalExploitabilityGap`
  in `UniformEquilibrium/Quitting/Terminal/ExploitabilityGap.lean` gives the
  negative semantic endpoint.

The common-quantile compression, finite centers, hierarchy, quantitative
bracket, and soundness of a supplied polynomial identity were already
checked.  A prior internal note observed abstractly that real-closed-field
decidability gives a productive certificate-or-all-errors fork.  The new
content here is the explicit single-shell expression system, rational
interval-tree proof language, sound verifier, strict-margin completeness,
complete rational upper enumeration, total per-scale dovetail, and exhaustive
counterexample semidecision.

This result is not derived from a quitting-game paper.  Its additional input
is elementary exact interval subdivision on a finite continuous expression
system.

## Proof

### Lemma 1: single-shell quantitative bracket

Every actual behavioral semantic pair belongs to `O_N` by the checked common-
quantile compression.  Conversely every center in `C_N` is the semantic pair
of a literal independent finite-clock profile.

The function `E` in (5) is 2-Lipschitz in the coordinate sup norm: changing
both `u_i` and `b_i` by at most `rho` changes every difference `b_i-u_i` by at
most `2 rho`, and taking a finite maximum does not enlarge that bound.
Therefore every point of `O_N` has an actual center whose exploitability is
at most `2 rho_N` away.  It follows that

\[
 \eta(r)-\frac{24}{N}\le A_N(r)\le\eta(r).
\tag{6}
\]

The right inequality uses inclusion of every actual semantic pair in `O_N`.
The left uses actualness of the center of every point in `O_N`.  No nesting of
the outer shells is needed.

### Lemma 2: lower-tree soundness

At an equality-separation leaf there is no feasible point because zero is not
in the equality enclosure.  At an inequality-separation leaf there is no
feasible point because the entire enclosure is negative.  At a goal leaf the
objective is at least `gamma` throughout the box.

The two closed child boxes of every split cover the parent.  Induction over a
verified finite tree therefore proves that every feasible assignment in the
root box has objective at least `gamma`.  Hence

\[
 \gamma\le A_N(r)\le\eta(r).
\tag{7}
\]

### Lemma 3: strict-margin completeness of the tree language

Assume `A_N(r) > gamma`.  At every point of the compact root box at least one
of the following strict statements holds:

- a required equality is nonzero;
- a required-nonnegative expression is negative; or
- the point is feasible and its objective is strictly greater than `gamma`.

Each statement persists on a neighborhood.  Natural interval evaluation of a
fixed expression made from addition, negation, multiplication, and finite
maximum converges to point evaluation as all coordinate widths tend to zero.

The generator always bisects a coordinate having maximal width after
normalization by its root width.  There are finitely many coordinates, so on
every infinite branch every normalized coordinate width tends to zero.  If
the generated tree did not close finitely, finite branching would give an
infinite unclassified branch.  Its nested boxes converge to a point, and the
strict neighborhood at that point would classify all sufficiently late boxes,
a contradiction.  Thus breadth-first subdivision eventually returns a finite
verified tree.

### Lemma 4: complete rational upper enumeration

Enumerate pairs `(T,D)` diagonally, where `T>=1` is a finite clock bound and
`D>=1` a common denominator.  For each pair enumerate every four-tuple of
rational simplex points with denominator `D`, including the Never coordinate.
Every rational finite-clock product profile occurs.

Rational simplex points are dense in every fixed finite product simplex.
Equations (2)--(3) express exploitability as a finite maximum of continuous
polynomial functions.  Hence whenever a real finite-clock profile has
exploitability strictly below a rational target, the enumeration eventually
finds and exactly verifies a rational profile below that target.

### Proof of Theorem A

Given rational `epsilon>0`, set

\[
 N=\left\lfloor\frac{96}{\varepsilon}\right\rfloor+1,
 \qquad
 a=\frac{\varepsilon}{4},
 \qquad
 b=\frac{3\varepsilon}{4}.
\tag{8}
\]

Then

\[
 \frac{24}{N}<\frac{\varepsilon}{4}.
\tag{9}
\]

Dovetail two exact searches:

- the interval-tree generator at level `N` and goal `a`; and
- the rational profile enumeration with target `b`.

If `A_N(r)>a`, Lemma 3 makes the lower search terminate.  If
`A_N(r)<=a`, choose a minimizing outer point and one of its actual centers.
By 2-Lipschitz continuity and (9), the center has exploitability at most

\[
 a+\frac{24}{N}<\frac{\varepsilon}{2}<b.
\]

Lemma 4 makes the upper search terminate.  The equality case `A_N(r)=a`
belongs to the upper arm and retains strict approximation room.  The two cases
are exhaustive, and dovetailing prevents starvation.

### Proof of Theorem B

If `eta(r)>0`, choose `k` with `3*2^(-k)/4 < eta(r)`.  At that scale an upper
certificate is impossible, so Theorem A must return a lower certificate.  If
the process returns a lower certificate at any scale, (7) gives `eta(r)>0`.

If `eta(r)=0`, soundness excludes every positive lower certificate.  Theorem A
therefore returns an upper profile at every scale, with exploitability tending
to zero.  Given any positive terminal error, choose a sufficiently large
`k`; the corresponding actual profile meets it.  Apply the checked all-errors
terminal selection theorem.

### Lemma 5: reward robustness

For two reward tables `r,r'`, put

\[
 \delta=\max_{i,S}|r_i(S)-r'_i(S)|.
\]

For any fixed profile or deviating profile, its terminal payoff changes by at
most `delta`.  Every unilateral gain therefore changes by at most `2 delta`.
Taking the supremum over deviations, the maximum over players, and the
infimum over profiles preserves this bound, so

\[
 |\eta(r)-\eta(r')|\le2\delta.
\tag{10}
\]

### Proof of Theorem C

Suppose a normalized real table `r` has `eta(r)>0`.  Choose a normalized
rational table `r'` within `eta(r)/4` in reward sup norm.  Such rational points
are dense even at boundary faces of the normalized cube.  Equation (10) gives
`eta(r')>eta(r)/2>0`.

Normalized rational tables, dyadic scales, and individual steps of all scale
resolvers form countable effective enumerations.  Fairly dovetail them.  By
Theorem B, the process for `r'` eventually emits a finite lower certificate.
Every emitted certificate is sound by Lemma 2 and (6).

An arbitrary nonzero finite reward table can first be scaled into the
normalized cube; positive scaling preserves whether `eta` is zero.  Therefore
the same conclusion applies to every Fin4 counterexample.

## Boundary tests

The independent reviews checked the following exact boundaries.

1. **Zero minimum and unrelated local inertness.**  The rational cyclic-
   plateau table has an exact all-Never zero-debt profile.  The upper checker
   accepts it and a false positive lower goal is rejected.
2. **Late deviations.**  A table where a player profits only by tying an
   opponent at its last represented date is detected by the auxiliary
   after-support date.
3. **Never versus a late finite quit.**  These remain distinct on the
   all-opponents-Never event and occupy different certificate coordinates.
4. **Product provenance.**  A payload containing only a joint terminal law is
   rejected; all coalition terms are rebuilt from four marginal laws.
5. **Unattained semantic limits.**  A semantic-pair-only payload is not an
   upper certificate.  Upper output always contains an actual finite product
   law.
6. **Direct/formula agreement.**  All nine supplied regression tests passed
   under direct invocation.  The adversarial review additionally compared the
   generated outer formulas with independent exact finite-clock evaluation on
   one hundred seeded rational cases, with exact agreement throughout.
7. **Equality boundary.**  `A_N=a` does not require the lower tree to close;
   the strict gap from `epsilon/2` to `b` makes the upper enumeration complete.

## Adapter and consumer

The arbitrary source is simply a normalized rational Fin4 reward table and a
rational requested accuracy.  No hard-residual or inert packet is assumed.
The common-quantile theorem maps every behavioral profile into the generated
single shell, while the finite-clock reconstruction maps every center and
every upper certificate back to a literal behavioral profile.

A lower tree reaches the negative semantic endpoint: it proves a positive
infimum for unrestricted terminal exploitability and, after reducing the gap
if necessary for approximate cap attainment, supplies
`HasTerminalExploitabilityGap`.

An infinite dyadic upper stream reaches the positive semantic endpoint:
actual terminal approximate Nash profiles at every error are consumed by
`quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`.

The per-scale algorithm does not decide in finite time which global endpoint
holds.

## Lean handoff

The narrow formalization should reuse the checked finite-clock semantic and
quantile transport layers and add:

1. a final-shell Fin4 outer predicate and the sandwich (6);
2. a finite expression syntax over rational constants with `+`, negation,
   multiplication, and `max`;
3. rational interval evaluation and an enclosure theorem;
4. finite binary box trees, exact leaf verification, and coverage soundness;
5. strict-margin completeness for normalized-longest-side dyadic splitting;
6. a computable diagonal enumeration of rational finite-clock product laws;
7. continuity/density completeness of the upper enumeration;
8. the terminating per-epsilon dovetail theorem;
9. the productive dyadic fork; and
10. reward-table Lipschitz robustness and rational-table semidecision.

Suggested theorem shapes are:

```lean
theorem finFourSingleShellLower_le_exploitabilityInf ...

theorem finFourLowerIntervalTree_sound
    (certificate : FinFourLowerIntervalTree reward level gamma) :
    (gamma : ℝ) ≤ quittingTerminalExploitabilityInf realReward

theorem exists_finFourLowerTree_of_singleShellMinimum_gt ...

theorem exists_rationalFiniteClockProfile_of_singleShellMinimum_le ...

theorem finFourExactScaleResolution
    (reward : RationalFinFourRewardTable)
    (epsilon : ℚ) (hepsilon : 0 < epsilon) :
    FinFourLowerIntervalTree reward (requiredLevel epsilon) (epsilon / 4) ⊕
      RationalFiniteClockProfileCertificate reward (3 * epsilon / 4)

theorem finFourPositiveTerminalGap_semidecidable ...
```

The existing rational polynomial infeasibility certificate need not be
reconstructed from an interval tree.  The new interval-tree soundness theorem
may connect directly to the single-shell outer bound.

The reference Python package uses recursive tree assembly and verification and
does not expose full search through its command-line interface.  It should be
treated as a reference implementation of the certificate language and
generator.  A Lean implementation should use structurally finite trees and a
fair computable search rather than inherit Python recursion limits.

## Scope and nonclaims

- No positive-gap reward table or lower certificate is currently produced.
- The procedure does not terminate with a proof of `eta=0`.
- It does not prove the Fin4 conjecture or its negation.
- It does not eliminate, construct, or consume the strict inert Fin4 source.
- A positive-minimum source merely implies that its generic scale process will
  eventually certify the already implied positive gap.
- It does not produce Bellman-linked profiles, a return chronology, a
  renewable rank, or a fixed-law source transition.
- The current Python implementation is not Lean-checked and is not part of the
  trusted theorem boundary.
