# Whole-packet gate: finite-deadline Nash quarter ceiling and fixed-prefix barrier

Packet:
[FINITE_DEADLINE_NASH_QUARTER_CEILING_AND_FIXED_PREFIX_BARRIER.md](../exports/FINITE_DEADLINE_NASH_QUARTER_CEILING_AND_FIXED_PREFIX_BARRIER.md)

Gate reviewer: CODEX_EULER

Independent theorem reviewers:

- [CODEX_RAMSEY](CODEX_EULER__FINITE_DEADLINE_NASH_UNIVERSAL_QUARTER_CEILING__BY_CODEX_RAMSEY.md)
- [CODEX_MINER](CODEX_EULER__FINITE_DEADLINE_NASH_UNIVERSAL_QUARTER_CEILING__BY_CODEX_MINER.md)

## Verdict

**PASS.** The packet satisfies every item in exports/README.md. The general
finite-deadline theorem, exact third-date constant, level-59 hierarchy
consumer, asymptotic worst-table quarter limit, and fixed-prefix arbitrary
finite-tail barrier are self-contained and correctly separated. Both
independent reviews explicitly attempted to falsify the unrestricted-strategy
claims and have no remaining objection.

During assembly I made only two bounded completeness edits: I stated that the
first two scalar maxima attain equality at \(x=1\), and quantified the global
uniform-clock comparison by an integer \(L\ge1\). No theorem repair was
needed.

## Universal finite-deadline theorem

For each player, the events “all opponents Never” and “opponents' earliest
finite date is \(t\)” are disjoint and exhaustive. Finite timing Nash gives

\[
U_i=\max(V_N,V_0,\ldots,V_{K-1}),
\]

and the checked pure-time extremality theorem gives the unrestricted cap

\[
B_i=\max(U_i,L).
\]

The positive-part comparison

\[
d_i\le2Rh_t+(R-s)\sum_{u>t}h_u
\]

has the correct orientation even when the raw difference \(L-V_t\) is
negative. Summing counts \(h_u\) exactly \(u\) times. Combining the resulting
bound with \(d_i\le as\) gives

\[
\frac{d_i}{R}\le
\frac{x(K+1-(K-1)x)}{K+1+x}.
\]

The packet separates \(R=0\), nonpositive singleton reward, zero debt, and
positive debt before dividing. Zero event masses, pure Nash coordinates,
exact Never, and zero-reach hazard denominators are covered.

The scalar calculations are exact:

\[
c_1=2/3,\qquad c_2=1/2,\qquad
c_3=20-8\sqrt6<5/12,
\]

and \(c_K\le1/4+2/K\). No finite action, later pure time, or unrestricted
behavioral deviation is omitted.

## Hierarchy and worst-table consumers

The three-date realization is a literal actual finite-clock center. Its
diagonal midpoint has zero objective and distance at most
\(10-4\sqrt6\). The exact comparisons

\[
12/59>10-4\sqrt6,\qquad12/60<10-4\sqrt6
\]

and their integer-square checks are correct. Thus \(L_M=0\) through level 59;
the packet correctly infers no positivity at level 60.

For normalized Fin4, the general upper estimate applies to every equilibrium,
so \(W_K\le1/4+2/K\). Miner's independently reviewed rational table has a
unique equilibrium with debt

\[
D_K=\frac{2^{K-1}}{2^{K+1}-1}>1/4,\qquad D_K\to1/4.
\]

Therefore \(W_K\to1/4\). There is no hidden exchange of supremum, infimum, or
equilibrium selections.

## Fixed-prefix table and scope

Theorem D gives a complete normalized rational Fin4 table. The
equilibrium-specific dummy argument is correct: time zero loses surely,
neither active player can be sure at zero, and a dummy at date one then has a
positively reached loss relative to Never. The active zero-sum matrix has the
unique law \((1/4,1/4,1/2)\).

The extension preserves only the date-zero and conditional date-one hazards;
it explicitly reopens the former Never branches into the suffix. For an
arbitrary finite-support product tail with conditional player-1 payoff
\(g\in[-1,1]\), the prescribed payoff is \(1/2+g/4\). A pure time after the
whole finite suffix always pays one, including when dummies activate, hence

\[
B_1-U_1\ge1/2-g/4\ge1/4.
\]

This is a legal unrestricted lower bound. The global uniform-\(L\) comparison
has exact debt \(2/L\to0\), so the table is correctly identified as a
fixed-prefix barrier rather than a positive-gap game.

## Source, novelty, and handoff

All cited declaration names and paths were checked:

- KernelGame.mixed_nash_exists in
  UniformEquilibrium/ProofView/Concepts/Existence/NashExistenceMixed.lean;
- sSup_range_quittingTerminalPayoff_update_eq_pureTime in
  UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean;
- QuittingFiniteDeadlineNashProfile,
  quittingRootSequencePureTimeTerminalValue_late_sub_none_eq, and
  QuittingFiniteDeadlineNashProfile.semanticDebt_le_escapeCharge in
  UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFiniteDeadlineNashEscalation.lean;
  and
- quittingFiniteClockSemanticReachable_eq_range_fold,
  quittingFiniteClockSemanticReachable_isCompact,
  quittingFiniteClockSemanticReachable_mono, quantileClockSupport, and
  quantileClockRadius in
  Research/Quitting/EscapeAwareQuantileClockHierarchy.lean.

These checked results supply Nash existence, pure-time cap reduction, a
supplied deadline interface, and actual hierarchy centers. None proves the
new function \(f_K\), exact third-date maximum, quarter limit, or fixed-prefix
barrier. The no-external-paper statement is explicit.

The Lean handoff separates the generic producer, scalar/hierarchy corollary,
Miner's lower family, and the fixed-prefix table. It does not assume the
desired estimate as a structure field and retains the checked hierarchy
compression hypothesis where needed.

## Final README disposition

The packet makes a strict named change to the conjecture-facing boundary:
an arbitrary-table all-behavior producer improves the finite-step constant
and advances the hierarchy cutoff, while exact examples determine the
architecture's quarter limit and distinguish fixed-prefix suffixing from
global finite-clock reselection.

The nonclaims are complete: no terminal approximation, uniform payoff,
positive gap, level-60 lower certificate, Fin4 hard-residual closure, or
source-preserving soft-tail producer is asserted. Final verdict: **PASS**.
