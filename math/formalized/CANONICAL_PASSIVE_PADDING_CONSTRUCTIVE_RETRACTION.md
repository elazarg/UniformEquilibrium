# Canonical passive-padding constructive retraction

Author: `CODEX_ROOT`

Independent reviews:
[source and freshness audit](../feedback/PASSIVE_PADDING_CONSTRUCTIVE_RETRACTION__BY_NOTE_MINING_SOURCE_AUDIT.md),
[adversarial falsification](../feedback/PASSIVE_PADDING_CONSTRUCTIVE_RETRACTION__BY_NOTE_MINING_FALSIFIER.md), and
[earlier mathematical review](../feedback/CODEX_ROOT__PASSIVE_PADDING_CONSTRUCTIVE_RETRACTION__BY_CODEX_RAMSEY.md)

## Exact statement

Let \(I\) and \(J\) be finite nonempty player sets. Let \(r\) be a quitting
reward table on \(I\). For each old player \(i\), put

\[
H_i=\max\bigl(0,\{r_i(S):S\ne\varnothing\}\bigr),\qquad
L_i=\min\bigl(0,\{r_i(S):S\ne\varnothing\}\bigr),
\]

and

\[
\Omega=\max_i(H_i-L_i).
\]

Fix a penalty \(A>0\), let \(m=|J|\), and define

\[
f=\frac{A}{A+m\Omega}>0.
\]

The canonical padded reward \(r^+\) on \(I\sqcup J\) is defined as follows.

- If a nonempty terminal coalition contains an old player, delete all fresh
  labels when evaluating every old coordinate and pay every fresh coordinate
  zero.
- If it contains only fresh players, pay old player \(i\) the value \(H_i\);
  pay each participating fresh player \(-A\); and pay every other fresh
  player zero.

For a padded behavioral profile \(\sigma^+\), let \(P\sigma^+\) be its
literal old-player projection: at every live date it retains exactly the old
coordinates of the padded product root.

### Quantitative terminal retraction

If \(\varepsilon\ge0\) and \(\sigma^+\) is a terminal
\(\varepsilon\)-Nash profile of \(r^+\) against every unilateral behavioral
deviation, then

\[
\boxed{P\sigma^+\text{ is a terminal }(\varepsilon/f)\text{-Nash profile of }r.}
\tag{1}
\]

If, for a padded target \(v^+\),

\[
|U_i^+(\sigma^+)-v_i^+|\le\varepsilon\qquad(i\in I),
\]

then, for \(v_i=v^+_{\operatorname{inl}(i)}\),

\[
\boxed{|U_i(P\sigma^+)-v_i|\le\varepsilon/f\qquad(i\in I).}
\tag{2}
\]

### Exact uniform-payoff target set

Let \(\operatorname{UEPayoffs}(r)\) denote the set of uniform-equilibrium
payoffs of \(r\). Then

\[
\boxed{
\operatorname{UEPayoffs}(r^+)
=
\{(v,0):v\in\operatorname{UEPayoffs}(r)\}.
}
\tag{3}
\]

In particular, the old-coordinate restriction of every padded uniform payoff
is an old uniform payoff, and every fresh coordinate of every padded uniform
payoff is zero.

### Pointwise and infimum exploitability

Let \(E_r(\sigma)\) be maximum terminal exploitability and let

\[
\eta(r)=\inf_\sigma E_r(\sigma).
\]

Then every padded profile satisfies

\[
\boxed{f\,E_r(P\sigma^+)\le E_{r^+}(\sigma^+),}
\tag{4}
\]

and

\[
\boxed{f\,\eta(r)\le\eta(r^+)\le\eta(r).}
\tag{5}
\]

## Conjecture-facing change

The checked passive-padding theorem transported a positive terminal gap and
uniform-payoff nonexistence upward in player cardinality. It explicitly did
not provide a converse from the padded game to its old subgame.

Equations (1)--(5) close that boundary for the canonical padding. Padding is
a quantitative target-preserving retraction, not merely an upward
counterexample map. A theorem solving all \((k+1)\)-player games therefore
constructively solves every \(k\)-player game by canonical padding and
projection.

This does not reduce an arbitrary \((k+1)\)-player table to \(k\) players and
does not solve a new cardinality.

## Definitions and probability semantics

The fresh-only mass \(s(\sigma^+)\) is the infinite-horizon probability that
the first absorbing coalition is nonempty and contains only fresh players.
An old/fresh tie is old-containing and is not counted in \(s\).

The profile projection and every deviation lift retain complete behavioral
hazards at every live date. Never, private randomization, calendar dependence,
and arbitrarily late quitting are included. No cap or best-response supremum
is assumed to be attained.

## Source correspondence

The canonical reward, profile projection, old payoff coupling, old deviation
lift, aggregate fresh penalty, and fresh Never payoff are checked in
`UniformEquilibrium/Quitting/Terminal/PassivePlayerPadding.lean` and
`PassivePlayerPaddingCanonical.lean`, including:

- `quittingPassivePaddingProjectProfile`;
- `quittingTerminalPayoff_passivePadding_old`;
- `quittingTerminalPayoff_update_passivePadding_old_ge`;
- `sum_quittingTerminalPayoff_passivePadding_fresh_le`; and
- `quittingTerminalPayoff_update_passivePadding_fresh_never_eq_zero`.

The fixed-target terminal characterization is in
`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalTargetSemantics.lean`.
The generic quiet lift for a dispensable block is in
`UniformEquilibrium/Quitting/Classification/BlockDeletion.lean`.

The checked padding corollaries provide only upward gap/nonexistence
transport. No checked declaration gives (1), restriction of the same padded
target, forced-zero fresh target coordinates, (3), or (4). The numerical
relations in (4)--(5) were retained separately in
`revisit/TERMINAL_EXPLOITABILITY_PASSIVE_PLAYER_PADDING_POINTWISE_INFIMUM.md`.

## Proof

Let \(s=s(\sigma^+)\).

### Fresh-only mass

For every fresh player \(j\), deviation to literal Never gives payoff zero.
Terminal \(\varepsilon\)-Nash therefore implies

\[
-U_j^+(\sigma^+)\le\varepsilon.
\]

The aggregate fresh-payoff account gives

\[
\sum_{j\in J}U_j^+(\sigma^+)\le-As.
\]

Hence

\[
As\le\sum_{j\in J}(-U_j^+(\sigma^+))\le m\varepsilon,
\qquad
\boxed{s\le\frac{m\varepsilon}{A}.}
\tag{6}
\]

Fresh-only collisions only strengthen the aggregate inequality because every
participating fresh player receives \(-A\).

### Projection against arbitrary old deviations

For every old player \(i\), the canonical coupling gives

\[
0\le U_i^+(\sigma^+)-U_i(P\sigma^+)\le\Omega s.
\tag{7}
\]

Fix an arbitrary old behavioral strategy \(\tau_i\). Its padded lift
\(\widetilde\tau_i\) copies its entire live-history hazard, and the checked
deviation comparison gives

\[
U_i((P\sigma^+)[i\leftarrow\tau_i])
\le
U_i^+(\sigma^+[\operatorname{inl}(i)\leftarrow\widetilde\tau_i]).
\tag{8}
\]

Using padded \(\varepsilon\)-Nash, (6), and (7),

\[
\begin{aligned}
U_i((P\sigma^+)[i\leftarrow\tau_i])-U_i(P\sigma^+)
&\le\varepsilon+\Omega s\\
&\le\varepsilon\left(1+\frac{m\Omega}{A}\right)
=\frac{\varepsilon}{f}.
\end{aligned}
\]

Since \(\tau_i\) was arbitrary, this proves (1). Equation (2) follows from
(7), the padded target error, and the same bound.

### Target retraction

Let \(v^+\) be a padded uniform-equilibrium payoff. For every requested old
accuracy \(\eta>0\), use the fixed-target terminal characterization at padded
accuracy \(\varepsilon=f\eta\). Equations (1)--(2) produce an old terminal
\(\eta\)-Nash profile within \(\eta\) of the fixed restriction \(v\). The
terminal-to-uniform compiler proves that \(v\) is an old uniform payoff.

Every fresh coordinate reward is nonpositive. In every padded terminal
\(\varepsilon\)-Nash profile, Never also forces the fresh prescribed payoff
to be at least \(-\varepsilon\). Along fixed-target acceptance profiles this
forces \(v_j^+=0\) for every fresh \(j\).

Conversely, copy an old terminal approximate equilibrium and make every fresh
player Never. Old payoffs and old unilateral deviations agree exactly with
the old game. If one fresh player \(j\) deviates, its payoff is

\[
-A\Pr(j\text{ strictly preempts old absorption})\le0;
\]

ties with old quitters, old preemption, and nonabsorption pay zero. Thus the
quiet lift retains the same equilibrium error and has target \((v,0)\).
This proves (3).

### Exploitability

A profile is a terminal \(E(\sigma)\)-Nash profile by definition. Apply (1)
with \(\varepsilon=E_{r^+}(\sigma^+)\) to obtain (4). Taking infima gives the
left inequality in (5). The quiet lift has exactly the old debts and zero
fresh debt, so taking infima over quiet lifts gives the right inequality.

## Boundary tests

### Strict positivity of the penalty is essential

Let the old game have two players and rewards

\[
r(\{1\})=(1,0),\qquad
r(\{2\})=(0,1),\qquad
r(\{1,2\})=(0,0).
\]

The vector \((1,1)\) is not an old terminal payoff because every terminal
outcome, including Never, lies in the convex hull of these three vectors and
zero, whose coordinate sum is at most one.

Pad by one fresh player with \(A=0\). Let the fresh player Quit at date zero
and the old players Never quit. This is an exact terminal Nash profile with
payoff \((1,1,0)\): an old player who joins receives its singleton reward one,
and the fresh player is indifferent. Thus the padded uniform payoff
\((1,1,0)\) restricts to a vector which is not an old uniform payoff.

Hence \(A>0\) is essential even for qualitative retraction.

### Other boundaries

- If \(J=\varnothing\), padding and projection are the identity.
- The old set is assumed nonempty so the canonical endpoints are defined.
- If \(\Omega=0\), then \(f=1\) and the old baseline coupling is exact.
- The theorem is specific to the canonical padding reward, not arbitrary
  player extensions.

## Adapter and consumer

The actual-data adapter is the canonical padding constructor together with
the literal live-root projection \(P\).

The quantitative theorem consumes any padded terminal approximate
equilibrium directly. The fixed-target terminal compiler consumes its
projection and yields the same restricted uniform target. Conversely, the
checked block-dispensability lift or the explicit quiet lift produces
\((v,0)\).

## Lean handoff

Suggested file:
`UniformEquilibrium/Quitting/Terminal/PassivePlayerPaddingRetraction.lean`.

Recommended declarations:

- `freshOnlyMass_le_of_isεAsymptoticNash_passivePadding`;
- `isεAsymptoticNash_project_passivePadding`;
- `terminalTargetError_project_passivePadding`;
- `IsUniformEquilibriumPayoff.of_passivePlayerPadding_canonical`;
- `isUniformEquilibriumPayoff_passivePadding_iff`;
- `passivePadding_uniformPayoff_fresh_eq_zero`;
- `terminalExploitability_project_passivePadding`; and
- the two infimum inequalities.

The quantitative statements should first use the multiplier
\(1+m\Omega/A\), avoiding division during their main proofs. The pointwise
exploitability theorem should precede any real-infimum packaging.

## Scope and nonclaims

This theorem classifies only the canonical padded subclass. It does not
project an arbitrary larger-player game, produce a uniform payoff for an
unsolved table, or settle Fin4. Its contribution is an exact constructive
cardinality retraction and complete target-set classification for canonical
passive padding.

## Lean formalization record

The frozen export packet above had SHA-256
`e857ac3c7a6fc2a0d2379bfbde179cb2a860693f90194f47ab5f80da2c04c9e8`.
The theorem implementation landed in commit
`5d04427d7cee306b4f6744a5351b56e7ef19ab24`; its production and diagnostics
inventory, exhaustive axiom audit, and durable toolkit description were
completed in commit `4fa2cc6`.

The checked owners are:

- `UniformEquilibrium/Quitting/Boundary/FinitePlayerMax.lean`;
- `UniformEquilibrium/Quitting/Terminal/TerminalExploitability.lean`;
- `UniformEquilibrium/Quitting/Terminal/PassivePlayerPaddingRetraction.lean`;
- `UniformEquilibrium/Quitting/Terminal/`
  `PassivePlayerPaddingExploitabilityRetraction.lean`;
- `UniformEquilibrium/Quitting/Terminal/TargetTail/`
  `PassivePlayerPaddingUniformTargetRetraction.lean`; and
- `UniformEquilibrium/Diagnostics/Quitting/Regression/`
  `PassivePaddingZeroPenaltyTargetRetractionFailure.lean`.

The quantitative projection and target-error declarations are
`isεAsymptoticNash_project_passivePadding` and
`terminalTargetError_project_passivePadding`.  The exact target-set result is
`uniformEquilibriumPayoffSet_passivePadding_eq_image`, obtained from
`isUniformEquilibriumPayoff_passivePadding_iff`.  The pointwise and infimum
statements are
`retractionFactor_mul_quittingTerminalExploitability_project_le`,
`retractionFactor_mul_quittingTerminalExploitabilityInf_le_padding`, and
`quittingTerminalExploitabilityInf_padding_le`.  The zero-penalty boundary is
the literal checked conjunction
`passivePaddingZeroPenalty_uniformTargetRestriction_failure`.

Evidence seals:

- **M:** the frozen result passed the listed source and adversarial reviews;
- **L:** all displayed declarations are checked by Lean and included in the
  regenerated production axiom audit;
- **A:** every padded profile is projected through its literal live-root
  hazards, and every old-player deviation remains an arbitrary behavioral
  replacement; and
- **C:** the terminal target compiler proves restriction and zero-extension
  on the same fixed target, while the numerical exploitability definitions
  consume the pointwise comparison into both infimum inequalities.

Validation included a fresh named build of all four new theorem/regression
leaves (8,939 jobs), the trust, import-graph, documentation, proof-duplicate,
redundant-order, and experiment gates (33 registered programs), direct
compilation of the contemporaneous Literature file, and a full `lake build`
of 11,298 jobs.  Local ratchets additionally reported only pre-existing files
under ignored `math/fable/lean`; the repository and CI checkout do not include
that ignored tree.

The strict positive-penalty hypothesis remains essential for restriction.
This is an exact retraction for the specially constructed canonical padded
table, not a reduction of arbitrary larger-player reward tables and not a new
cardinality case of the quitting-game conjecture.
