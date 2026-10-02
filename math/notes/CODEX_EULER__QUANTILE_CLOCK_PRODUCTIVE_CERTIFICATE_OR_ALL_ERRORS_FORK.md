# Quantile-clock productive certificate-or-all-errors fork

## Status

**Independently reviewed PASS as ordinary mathematics; internal operational
corollary, not a separate export.**  Review:
[`CODEX_EULER__QUANTILE_CLOCK_PRODUCTIVE_CERTIFICATE_OR_ALL_ERRORS_FORK__BY_CODEX_RAMSEY.md`](../feedback/CODEX_EULER__QUANTILE_CLOCK_PRODUCTIVE_CERTIFICATE_OR_ALL_ERRORS_FORK__BY_CODEX_RAMSEY.md).
This is a
source-aware consumer of the reviewed/exported quantile-clock hierarchy.  It
turns vanishing finite lower certificates into an executable all-errors
terminal-Nash stream, using the actual product-law center stored in each
finite outer witness.  It does not use a source-free Farkas separator.

The procedure is productive rather than a terminating zero test: on the
positive-gap branch it halts with a finite exact certificate; on the zero-gap
branch it runs forever while emitting successively more accurate executable
profiles.  This distinction is explicit throughout.

## 1. Exact question

Let `I` be a nonempty finite player set, `n=|I|`, and let `r` be a rational
quitting-game reward table with `|r_i(S)|<=1`.  Write

\[
 \eta(r)=\inf_\sigma\operatorname{Expl}_r(\sigma),
 \qquad
 F(U,B)=\max\bigl(0,\max_i(B_i-U_i)\bigr).              \tag{1.1}
\]

The exported hierarchy
[`ESCAPE_AWARE_QUANTILE_CLOCK_SEMIALGEBRAIC_HIERARCHY.md`](../formalized/ESCAPE_AWARE_QUANTILE_CLOCK_SEMIALGEBRAIC_HIERARCHY.md)
defines finite-clock actual semantic sets `A_(K_M)`, compact rational
semialgebraic outer sets `R_M`, and

\[
 \delta_M={n(n-1)\over M},
 \qquad
 L_M=\min_{z\in R_M}F(z),                              \tag{1.2}
\]

with

\[
 0\le L_M\le\eta(r),
 \qquad
 \sup_M L_M=\eta(r).                                  \tag{1.3}
\]

Every extended witness for `z in R_M` includes, at the current scale `M`, an
actual finite-clock product-law center

\[
 a_M\in A_{K_M},
 \qquad
 \|a_M-z\|_\infty\le\delta_M.                         \tag{1.4}
\]

The question is whether the zero outcome of every finite lower-bound query
can be consumed without identifying `z` itself with an executable profile.

## 2. The finite zero-witness extractor

Set

\[
 c_n=2n(n-1).
\]

### Lemma 2.1 (one finite zero query emits an actual profile)

Fix `M>=1`.  Exactly one of the following finite rational semialgebraic
outputs is available.

1. **Positive certificate.** There is a rational `gamma>0` such that

   \[
    \gamma\le F(z)\quad\text{for every }z\in R_M.       \tag{2.1}
   \]

   Consequently `gamma<=Expl_r(sigma)` for every behavioral profile.

2. **Actual zero-center extraction.** There is an algebraic finite-clock
   product law, behaviorally realizable as a profile `sigma_M`, such that

   \[
    \operatorname{Expl}_r(\sigma_M)le {c_n\over M}.    \tag{2.2}
   \]

Moreover, a terminating real-closed-field computation decides which output
holds and returns its finite algebraic witness/certificate.

#### Proof

Ask whether the extended rational semialgebraic system

\[
 z\in R_M(r),\qquad F(z)=0                              \tag{2.3}
\]

is feasible.

If it is feasible, retain not only `z` but the scale-`M` center `a_M` and its
marginal simplex variables from (1.4).  The exploitability function is
`2`-Lipschitz in semantic sup norm, so

\[
 F(a_M)\le F(z)+2\delta_M={2n(n-1)\over M}={c_n\over M}.
\]

The center is not a relaxed flow: it is an exact product of finite stopping
laws, including an exact `Never` coordinate, and the checked stopping-law
reconstruction gives an executable behavioral profile.  Checked pure-time
extremality identifies its finite maximum graph with the cap against every
unilateral behavioral deviation.  This proves (2.2).

If (2.3) is infeasible, compactness of `R_M`, continuity and nonnegativity of
`F` imply `L_M>0`.  Enumerate positive dyadic rationals and decide the finite
RCF sentence

\[
 z\in R_M,\qquad F(z)<\gamma.
\]

Because `L_M>0`, this search terminates with a rational
`0<gamma<=L_M`.  Soundness of the hierarchy gives (2.1) for every executable
profile.  Real quantifier elimination supplies the algebraic sample in the
feasible arm and an exact infeasibility trace in the certificate arm.  QED.

This proof never asks whether the zero outer point `z` is realized.  It uses
only its co-realized actual finite-clock center `a_M`.

## 3. A canonical productive process

Let

\[
 M_k=\max(1,c_n2^k),\qquad k=0,1,2,\ldots.             \tag{3.1}
\]

Run Lemma 2.1 at scale `M_k`.

- If the positive arm occurs, halt and return its rational gap and exact RCF
  certificate.
- If the zero arm occurs, emit the algebraic product stopping law and its
  executable behavioral realization `sigma_k`, then proceed to `k+1`.

For `n=1`, `c_n=0`, `M_k=1`, and every emitted profile has zero
exploitability.  For Fin4, `c_n=24` and one may use `M_k=24*2^k`.

### Theorem 3.1 (certificate-or-all-errors productive fork)

The process has exactly the following semantics.

1. It halts after finitely many stages if and only if `eta(r)>0`.  Its output
   is a finite independently checkable rational/algebraic certificate of a
   uniform positive terminal exploitability gap.
2. It runs forever if and only if `eta(r)=0`.  In that case every output is an
   actual behavioral profile and

   \[
    \operatorname{Expl}_r(\sigma_k)\le2^{-k}.           \tag{3.2}
   \]

   Hence the emitted stream is an executable all-errors terminal approximate
   Nash family.  Its members need not be Bellman-linked to one another.
3. In the infinite branch the checked theorem
   `quittingGame_exists_uniformEquilibriumPayoff_of_terminalNash_all_errors`
   consumes (3.2) and yields a uniform-equilibrium payoff.

#### Proof

Every individual stage terminates by real quantifier elimination and the
finite dyadic search in the infeasible arm.  If a stage halts, (2.1) implies
`eta(r)>=gamma>0`.

If a stage does not halt, Lemma 2.1 emits an actual profile satisfying

\[
 \operatorname{Expl}_r(\sigma_k)le {c_n\over M_k}le2^{-k}.
\]

If the process runs forever, taking the infimum over actual profiles gives
`eta(r)=0`.

Conversely, if `eta(r)=0`, (1.3) and nonnegativity give `L_M=0` at every
level.  Compactness makes the zero system (2.3) feasible, so the positive arm
never occurs.  If `eta(r)>0`, convergence `L_M->eta(r)` implies
`L_(M_k)>0` for every sufficiently large `k`; thus the process eventually
halts.  The terminal all-errors consumer is the named checked theorem.  QED.

### Corollary 3.2 (limiting vanishing certificates have an actual consumer)

The following are equivalent:

1. no finite quantile-clock level admits a positive lower certificate;
2. `L_M=0` for every `M`;
3. the process emits an infinite executable all-errors terminal-Nash stream;
4. `eta(r)=0`;
5. the quitting game has a uniform-equilibrium payoff.

The equivalence between (4) and terminal approximate equilibria at every
error is also the checked project theorem
`quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors` in
`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`.

For (5) to (4), use that a uniform-equilibrium payoff supplies terminal
approximate equilibria at every error, hence the exploitability infimum is
zero.  No profile-limit realization is used.

## 4. Why this is source-aware

A source-free separation argument might produce a zero relaxed semantic
vector with no behavior, law, or chronology attached.  Lemma 2.1 instead
retains the complete extended witness of `R_M`:

\[
 (z;(a_m,x^{(m)})_{m\le M}).
\]

The emitted object is specifically the current-scale center
`(a_M,x^(M))`.  Its marginal variables satisfy the exact finite simplexes;
all coalition probabilities are their product monomials; `Never` is a
separate atom; and its cap is the exact finite pure-time maximum upgraded to
unrestricted deviations.  Thus the zero consumer survives the known
source-free Farkas objection.

The semantic loss is paid quantitatively through the explicit
`2 delta_M=c_n/M` bound, rather than hidden in a limiting purification.

## 5. Exact finite-data implementation shape

At stage `k`, the input consists only of the rational reward table and the
integer `M_k`.  A finite RCF solver:

1. decides feasibility of (2.3) in the extended `R_(M_k)` variables;
2. in the feasible arm, returns algebraic marginal probabilities for
   `a_(M_k)`, checked against the simplex, product-payoff, exact finite-cap,
   and neighborhood equations;
3. in the infeasible arm, searches dyadic `gamma` and returns an exact
   infeasibility certificate for `F<gamma` on `R_(M_k)`.

The finite algebraic marginal laws define executable behavioral hazards via
`quittingStoppingLawBehaviorStrategy` and
`quittingBehaviorStoppingLaw_stoppingLawBehaviorStrategy` in
`UniformEquilibrium/Quitting/Terminal/StrategicallyPrecompactWatchdogProperBoundary.lean`.
Unrestricted cap correctness uses
`sSup_range_quittingTerminalPayoff_update_eq_pureTime` in
`UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean`.

No numerical optimizer, finite-horizon Nash assumption, stationary strategy
restriction, or oracle for `eta(r)` appears.

## 6. Boundary audit

### Positive gap

When `eta(r)>0`, early levels may still have zero outer minima and emit coarse
actual profiles.  Monotone convergence of `L_M` forces a later positive
level, so the process cannot emit an infinite false all-errors stream.

### Zero gap without an attained equilibrium

Even if no actual profile has zero exploitability, compactness of `R_M`
attains `L_M=0`.  The process extracts the nearby actual center, not the
unrealized zero point.  Its errors tend to zero at the certified rate.

### Diffuse clocks and bubble mass

Every emitted center has finitely many dates and exact `Never`.  Diffuse
escape is handled in the sound outer witness which supplies the center; the
process never converts an escaping finite atom into `Never`.

### Product and zero-probability faces

Algebraic centers obey exact marginal simplexes, including zero coordinates.
The finite maximum graph keeps deviations at zero-probability dates available.

### All-`Never`

The exact `Never` atom and after-support finite deviation are both present in
every finite cap graph.  Thus an all-Continue profile is emitted only when its
full unrestricted exploitability meets the displayed bound.

## 7. Conjecture-facing consequence and exact limitation

This theorem supplies the requested zero-gap extraction from finite
source-aware data: vanishing finite lower certificates generate an executable
all-errors terminal profile family, not merely a carrier point or dual vector.
It also
retains the positive certificate arm and proves that the two operational
behaviors exhaust all rational finite quitting tables.

It does **not** turn equality-to-zero into a terminating decision.  On the
zero branch the productive computation is intentionally infinite; the stream
it emits is the constructive chronology.  Therefore this is not Output 2's
terminating branch selector as literally worded in the maintained question.
It is a complete Type-2/online certificate-or-chronology fork and an exact
semantic consumer for the hierarchy's limiting zero behavior.

It does not prove `eta=0` for Fin4, exhibit a positive-gap table, eliminate the
Fin4 hard residual, produce a Bellman edge, or realize an arbitrary semantic
carrier point.  The emitted profiles are separate finite-center selections;
no literal prefix, common source, or transition relation between consecutive
outputs is claimed.

The compression, `2 delta_M` bracket, and conditional fact that `eta=0`
supplies finite-clock approximate Nash profiles are already present in the
exported hierarchy.  The new content here is the exact finite equality query,
extraction of its co-realized current-scale product center without an upper
optimization, and the single proof-carrying process whose finite-halting and
infinite-productive behaviors are proved exhaustive.  If that operational
packaging is judged insufficiently stronger than the export, this note should
remain an internal consumer rather than a separate packet.

## 8. Requested independent checks

1. Verify that `L_M=0` is equivalent to feasibility of the exact equality
   system `F(z)=0`, including outer points with negative raw debts.
2. Check extraction of the current-scale product center and the factor
   `2 delta_M`.
3. Check that the infeasible equality arm effectively yields a rational
   positive lower certificate, rather than only an abstract positive minimum.
4. Audit the `if and only if` halting semantics and the `n=1` boundary.
5. Decide whether a productive infinite chronology meets the maintained
   question's zero-gap progress gate while preserving the explicit nonclaim
   of a terminating zero-test.
