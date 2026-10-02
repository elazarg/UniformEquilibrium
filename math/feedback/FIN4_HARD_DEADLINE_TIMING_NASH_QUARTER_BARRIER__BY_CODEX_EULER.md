# Whole-packet gate: normalized Fin4 hard-deadline timing-Nash quarter barrier

Packet:
[FIN4_HARD_DEADLINE_TIMING_NASH_QUARTER_BARRIER.md](../exports/FIN4_HARD_DEADLINE_TIMING_NASH_QUARTER_BARRIER.md)

Gate reviewer: CODEX_EULER

Independent theorem reviews:

- [CODEX_EULER](CODEX_MINER__FIN4_NORMALIZED_HARD_DEADLINE_NASH_NONVANISHING__BY_CODEX_EULER.md)
- [CODEX_RAMSEY](CODEX_MINER__FIN4_NORMALIZED_HARD_DEADLINE_NASH_NONVANISHING__BY_CODEX_RAMSEY.md)

## Verdict

**PASS after two bounded prose additions applied directly.** The explicit
table, every-deadline uniqueness, exact recursion and products, unrestricted
debt \(D_N>1/4\), fixed-target \(1/L\) comparison, architecture narrowing,
source audit, Lean handoff, and noncounterexample scope all pass.

I added only the zero-date base case of the uniqueness induction and an
explicit no-external-paper sentence. No mathematical repair was needed.

## Exact table and every-deadline uniqueness

Equations (3)--(4) define all fifteen nonempty Fin4 terminal rows and every
coordinate lies in \([-1,1]\). A dummy receives \(-1\) exactly when it belongs
to the first coalition and zero otherwise. At a reached current date its Quit
action therefore pays \(-1\), while Never guarantees zero.

Neither active current hazard can equal one:

- sure Quit by \(k\) makes \(j\) strictly join, after which \(k\) strictly
  waits; and
- sure Quit by \(j\) makes \(k\) strictly wait, after which \(j\) improves
  through positive Never mass or a collision with a finite atom.

Thus the current all-Continue event has positive product probability. Any
strict conditional-tail improvement splices into a strict global improvement,
so ordinary Nash forces the conditional tail to be Nash. The packet now states
the induction base explicitly: with no finite date only Never remains and the
continuation is \((0,0)\). No subgame-perfect hypothesis is used.

Given a unique tail payoff \((u,v)\), the current Quit-minus-Continue
differences are exactly

\[
\Delta_k=(1/2-u)-q(3/2-u),\qquad
\Delta_j=p(2+v)-(1+v).
\]

On \(u<1/2,v>-1\), the unique root is interior:

\[
p=\frac{1+v}{2+v},\qquad
q=\frac{1/2-u}{3/2-u}.
\]

The four pure corners are excluded by the same strict comparisons. Joining
this root to the unique Nash tail gives the unique full equilibrium.

## Recursion, products, and unrestricted debt

Indifference yields

\[
u'=\frac1{3-2u},\qquad v'=-\frac1{2+v}.
\]

The displayed closed forms

\[
u_n=\frac12\left(1-\frac1{2^{n+1}-1}\right),\qquad
v_n=-1+\frac1{n+1}
\]

satisfy the recursion and preserve the strict invariant region. The roots

\[
p_n=\frac1{n+2},\qquad q_n=\frac1{2^{n+2}-1}
\]

give the telescoping Never masses

\[
a_k^{(N)}=\frac1{N+1},\qquad
a_j^{(N)}=\frac{2^N}{2^{N+1}-1}.
\]

Finite timing Nash controls every declared date and Never. Every time after
the deadline has one common value, and its difference from Never is the solo
reward times all-opponents-Never mass. The corrected slack convention is

\[
\sigma_i=U_i-V_i^{Never}\ge0.
\]

Checked pure-time extremality gives the exact unrestricted debt

\[
d_i=\max(0,E_i s_i-\sigma_i).
\]

Player \(k\)'s supported Never action gives \(\sigma_k=0\), while the dummies
are surely Never and \(s_k=1/2\). Hence

\[
D_N=d_k=\frac{2^{N-1}}{2^{N+1}-1}>\frac14.
\]

The other three singleton rewards are negative, so their late debts vanish.
The displayed ratio proves strict decrease and the limit is \(1/4\). This is
an all-behavior result, not a finite-menu or stationary lower bound.

## The \(1/L\) comparison and \(\eta=0\)

In the comparison profile, \(j\) quits surely at date zero, \(k\) conditionally
uses the uniform clock on \(\{1,\ldots,L\}\), and both dummies Never. The
prescribed payoff is always \((1,-1,0,0)\).

Player \(k\) cannot improve because joining pays zero instead of one. Dummies
can only lose by joining. If \(j\) refuses, a time in the punishment window
pays \(-1\) except on its unique tie atom, which pays zero; after-window times
and Never pay \(-1\). Thus \(j\)'s exact best gain is \(1/L\), and pure-time
extremality exhausts arbitrary behavioral deviations.

Therefore the executable exploitability infimum is exactly zero. For every
\(\varepsilon>0\), choosing \(L\) with \(1/L\le\varepsilon\) gives a terminal
\(\varepsilon\)-Nash profile at the same exact target. The cited
quittingGame_isUniformEquilibriumPayoff_of_terminalTargetAcceptance theorem
then makes \((1,-1,0,0)\) a uniform-equilibrium payoff. The packet is explicit
that this table is not a conjecture counterexample.

## Source and novelty audit

All cited checked declarations and paths exist with the stated roles:

- QuittingFiniteDeadlineNashProfile and
  quittingRootSequencePureTimeTerminalValue_late_sub_none_eq in
  UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFiniteDeadlineNashEscalation.lean;
- sSup_range_quittingTerminalPayoff_update_eq_pureTime in
  UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean;
- KernelGame.mixed_nash_exists in
  UniformEquilibrium/ProofView/Concepts/Existence/NashExistenceMixed.lean; and
- quittingGame_isUniformEquilibriumPayoff_of_terminalTargetAcceptance in
  UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean.

The checked deadline declarations consume a supplied certificate but do not
construct or uniquely solve this timing game. The normalized Fin4 extraction,
every-deadline uniqueness, exact quarter lower barrier, and same-table
zero-infimum comparison are not duplicated by a checked declaration or prior
export. The packet now explicitly records that no external paper is used
beyond checked finite-game Nash existence.

## README significance, handoff, and nonclaims

The packet decisively removes an apparently exhaustive architecture: no
deadline-dependent choice among exact Nash equilibria of hard-zero-tail timing
games can be universally vanishing, because this table has no selection
freedom and every such debt exceeds \(1/4\). The same-table \(1/L\) family
shows that arbitrary actual finite-clock centers remain expressive; the
failure is exact Nashification.

The Lean handoff correctly separates:

1. the explicit family and unrestricted debt;
2. positive-reach tail splicing and uniqueness; and
3. the fixed-target diffuse comparison.

It does not encode uniqueness or the lower bound as structure fields.

The scope exclusions are complete: no positive all-profile gap, no
counterexample, and no obstruction to soft tails, approximate roots, changed
early hazards, diffuse punishment, non-Nash finite clocks, or another
uniform-payoff construction. This satisfies every exports/README.md gate.
Final verdict: **PASS**.
