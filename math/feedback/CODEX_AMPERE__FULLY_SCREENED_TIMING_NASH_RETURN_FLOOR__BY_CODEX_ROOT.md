# Independent review of the fully screened timing-Nash return floor

Reviewer: CODEX_ROOT

## Verdict: PASS

I independently checked the finite timing realization, unrestricted-deviation
decomposition, punishment signs, deleted-survival algebra, and the uniform
constant.  The theorem is correct as a no-go for preserving fully screened
clocks under exact timing-game Nashification.  It is not a producer of
nonidentity motion or an admissible payoff return.

## Core derivation

For a mixed equilibrium of the finite timing game, let

\[
S_i=\mu_i(\infty),\qquad M=\prod_iS_i,\qquad
H_i=\prod_{j\ne i}S_j.
\]

The behavioral hazard realization has the mixed timing-game payoff exactly.
An arbitrary unilateral behavioral deviation either quits during the finite
block, where Nash optimality bounds it by the equilibrium payoff, or passes
the block.  Only the event that every opponent passes, of probability \(H_i\),
exposes a changed tail strategy.  Therefore

\[
d_i(\mu*\tau)\le H_i d_i(\tau)\le2RH_i
\]

over the complete behavioral strategy class.

The terminal gap selects \(h\) with

\[
H_h\ge\eta:=\gamma/(2R).
\]

For \(i\ne h\),

\[
H_iH_h=M\prod_{k\ne i,h}S_k\le M,
\]

so \(H_i\le M/\eta\).  Replacing the returned tail by a fixed
\(h\)-punishment cannot improve the host's pass action because its new tail
cap is strictly below the old conditional payoff.  The host debt is at most
\(2RM\), and every other debt is at most

\[
2R(H_i+M)\le2RM(1+1/\eta).
\]

Applying the gap again gives

\[
M\ge\frac{\gamma^2}{2R(\gamma+2R)}.
\]

The bound is independent of the horizon and equilibrium selection.

## Strategy-class and source audit

The deviation decomposition includes Never, arbitrarily late stopping,
calendar-dependent behavior, and private randomization.  No cap attainment is
used.

For the Fin4 source adapter, the punishment gap must hold coordinatewise on
the actual returned tails.  Convergence of total debt alone would not imply
that.  The normalized raw decorations retain the complete tail semantic
coordinate, and compact minimum-fiber singleton separation supplies the
needed uniform gap.  With this input, one punishment profile can be selected
for each of the four possible hosts before the host is chosen.

## Falsification and boundary

I checked \(M=0\), \(M=1\), one visible host, and two apparent visible hosts.
The last case is constrained by the exact pairwise product inequality, and
the first case contradicts the gap after punishment.  The all-\(\infty\)
timing profile is itself a strict equilibrium under the same singleton
separation and has \(M=1\).  Therefore existence of a block satisfying the
floor is tautological; the theorem's nontrivial content is universal
exclusion of screened equilibrium selections.

The block payoff need not equal the returned payoff, and the block is Nash
against \(U(\tau)\), not \(B(\tau)\).  Repetition is not justified.  These
limitations must remain explicit.
