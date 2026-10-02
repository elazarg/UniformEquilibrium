# Review of finite-clock KKT fixed face or full timing bubble

Reviewer: `CODEX_SPINOZA`

Reviewed artifact:
`notes/CODEX_HAHN__FINITE_CLOCK_KKT_FIXED_FACE_OR_FULL_TIMING_BUBBLE.md`,
exact SHA-256
`14a31273e02bcdf81304bd8eb48437c4879a00f113da0a0e0e81ca34f199af6a`.

## Verdict

**PASS.** I found no mathematical or scope objection.

## Checks reconstructed

### Deadline arm

The identity

\[
V_{j,K_n}^{\mu_n}-U_j(\mu_n)
=\sum_s(\mu_n)_j(s)
  \bigl(V_{j,K_n}^{\mu_n}-V_{j,s}^{\mu_n}\bigr)
=\eta_n
\]

does select a literal support time \(s_n\) whose pairwise gain is at least
\(\eta_n\).  Before the first disagreement \(\ell_n\), the two pure-time
responses have identical outcomes.  Their terminal payoff difference is at
most \(2M\) on the complementary event, so the full-opponent survival floor
is exactly \(\eta_0/(2M)\).  This is a counterfactual reach floor; the note
correctly does not turn it into a prescribed source-atom floor.

### Cross-amplification arm

Applying the same factorization to the checked \(\eta_n/3\) payoff
difference gives \(\eta_0/(6M)\).  Because deterministic player \(j\) is an
opponent of \(i\), positive survival forces \(r_n\ge\ell_n\); the definition
of first disagreement gives \(s_n,t_n\ge\ell_n\).  At either pure corner the
two selected clocks therefore survive surely, and the remaining two-player
survival factor is exactly the factor in the three-opponent expression.
Thus the equality and the all-player lower bound in (14), including the
constant, are correct.

### Compactification and timing trichotomy

After a common subsequence each marked time is fixed finite, literal Never,
or a proper time escaping to infinity.  Stabilizing a bounded
\(\ell_n\), or taking \(\ell_n\to\infty\), gives the stated exhaustive split:

- all marks fixed (possible only in the cross arm);
- fixed first disagreement with a remote continuation; or
- escaping first disagreement.

For fixed \(H\), the cylinder \(\{T_k\ge H\ \forall k\}\) is clopen in the
finite product of the one-point compactification.  Weak convergence preserves
its mass, and continuity from above as \(H\to\infty\) yields the all-player
Never cylinder with the same \(\eta_0/(2M)\) or \(\eta_0/(6M)\) floor.
This conclusion is correctly attached to weak limits of the counterfactual
pure-response corners, not to the source profile.

The claimed mass \(\ge1/4\) at `(j,Never)` in the dual limit in arm A is also
valid: the marked deadline \(K_n\to\infty\), so every cofinite neighborhood
of Never eventually contains that atom, and continuity from above retains
the mass in the limit.

## Boundary stress tests

- A proper synchronized coalition can stop at dates tending to infinity
  while all marginal weak limits are Never.  This confirms that the Never
  bubble does not determine the limiting terminal payoff or coalition law;
  the note states this caveat explicitly.
- If \(\ell_n\) is bounded in the deadline arm, the exposed clock \(K_n\)
  is necessarily the escaping mark.  If \(\ell_n\to\infty\), both pure
  deadline corners survive to the cut, so no missing timing case remains.
- The controller minimizer is not assumed to be a timing-game Nash profile,
  and the packet does not feed it to the adjacent-deadline Nash consumer.

The fixed/remote/bubble classification therefore preserves the exact
source and counterfactual scope without a terminal-law, chronology, or
uniform-equilibrium overclaim.
