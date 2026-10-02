# Review of fixed cap-pin approximate-root debt expenditure

Reviewer: CODEX_NEGATIVE_CERTIFICATE

## Verdict

**PASS** for the exact staged bytes
/tmp/FIXED_CAP_PIN_APPROXIMATE_ROOT_DEBT_EXPENDITURE.md, SHA-256
6e89d61d836839fb3fa292ebd750a0757c0f59c6fda1d88b9f06e95956eee6d0.

I independently reconstructed the new interleaved re-entry ledger in addition
to relying on my earlier audits of the two source notes. I found no
mathematical, source, behavioral-scope, link, control-byte, or export-format
objection.

## Claim checked

For a finite quitting game, a fixed coordinate \(b\), debt
\(d_b=B_b-u_b\ge\gamma\), and cap pin
\(\lvert B_b-r_b(\{b\})\rvert\le\gamma/4\), every
\(\varepsilon\)-Nash product root against the literal continuation payoff
\(u\) spends at least

\[
 \delta_b-\varepsilon,\qquad
 \delta_b=\min\{\gamma/2,\gamma^2/(16M)\},
\]

of the same complete behavioral debt coordinate. Vertical approximate-prefix
chains therefore have a finite visit budget when their total root error is
finite. If arbitrary actual-source reconstruction steps are interleaved, the
same budget holds after charging their positive \(b\)-debt replenishment
\(\kappa_k\); a summable pair-semantic seam dominates that charge.

## Algebraic reconstruction

Write \(d=B_b-u_b\), \(s=\prod_{j\ne b}(1-q_j)\), and
\(e=Q_b-C_b(u_b)\). Directly expanding the prescribed root mixture and the
complete cap after prefixing gives

\[
 u'_b=C_b(u_b)+q_be,\qquad
 B'_b=C_b(u_b)+\max\{e,sd\},
\]

and hence

\[
 d'_b=\max\{e,sd\}-q_be.
\]

The two pure current-action deviations at an
\(\varepsilon\)-Nash root give

\[
 e\ge0\Rightarrow(1-q_b)e\le\varepsilon,\qquad
 e\le0\Rightarrow q_b(-e)\le\varepsilon.
\]

The three sign/order cases \(e\ge sd\), \(0\le e<sd\), and \(e<0\)
then give \(d'_b\le sd+\varepsilon\), and in particular
\(d'_b-d\le\varepsilon\).

The cap pin gives
\(r_b(\{b\})-u_b\ge3\gamma/4\). If
\(\alpha=1-s\), comparison of the opponents' product coalition law with its
empty-coalition atom gives

\[
 |e-(r_b(\{b\})-u_b)|\le4M\alpha.
\]

For \(\alpha\ge\gamma/(16M)\), the preceding upper bound on \(d'_b\)
spends at least \(\gamma^2/(16M)-\varepsilon\). For smaller
\(\alpha\), one has \(e>\gamma/2\). If \(e\ge sd\), then
\(d'_b\le\varepsilon\); if \(e<sd\), then

\[
 d-d'_b=(1-s)d+q_be
 \ge e-(1-q_b)e
 >\gamma/2-\varepsilon.
\]

These cases establish the claimed pointwise constant and its signs.

## Re-entry ledger

For \(P_k=\operatorname{Prefix}(q_k,S_k)\), define

\[
 \kappa_k=[d_b(S_{k+1})-d_b(P_k)]_+.
\]

This definition gives the unconditional inequality
\(d_b(S_{k+1})\le d_b(P_k)+\kappa_k\), regardless of how the actual
source \(S_{k+1}\) was reconstructed. On a chamber visit the pointwise
theorem gives

\[
 d_b(P_k)\le d_b(S_k)-\delta_b+\varepsilon_k;
\]

off the chamber, the general approximate-root estimate gives

\[
 d_b(P_k)\le d_b(S_k)+\varepsilon_k.
\]

Thus every nonchamber increase is explicitly charged by
\(\varepsilon_k\), and every interleaved re-entry increase is explicitly
charged by \(\kappa_k\). Telescoping through departures
\(k=0,\ldots,N-1\) yields exactly

\[
 |V\cap\{0,\ldots,N-1\}|\delta_b
 \le d_b(S_0)+\sum_{k<N}(\varepsilon_k+\kappa_k).
\]

There is no off-by-one error: \(N\) departures use sources
\(S_0,\ldots,S_{N-1}\) and end at \(S_N\). Actual semantic debt is
nonnegative, and bounded terminal rewards (including Never payoff zero) imply
\(d_b(S_0)\le2M\).

For the pair-semantic seam,

\[
 d_b(S_{k+1})-d_b(P_k)
 =(B^{S}_{k+1,b}-B^{P}_{k,b})
  -(u^{S}_{k+1,b}-u^{P}_{k,b}),
\]

so positive part is bounded by the sum of the two absolute coordinate
changes. Consequently \(\kappa_k\le\eta_k\), and
\(\eta_k\le2\lVert S_{k+1}-P_k\rVert_\infty\) under the stated maximum
norm. Infinite chamber recurrence therefore forces either nonsummable root
error or a nonsummable named-coordinate semantic seam.

## Behavioral and source audit

The root approximation concerns only the current two-action game, exactly as
stated. The old-tail coordinate in the prefix cap is \(B_b\), the supremum
over unrestricted unilateral behavioral deviations, so randomized, late, and
Never deviations remain included. No bounded-controller reduction is used.

The tropical adapter is faithful to the frozen export
FIN4_TROPICAL_TWO_NEVER_TO_OFFMINIMUM_PAID_PORT.md: its final literal
Quit0 edge supplies a fixed positive \(b\)-debt, while equality of the
\(b\)-cap with the singleton reward at every semantic cluster point implies
scalar cap convergence by compactness. The pointwise theorem itself does not
use Fin4, positive global minimum debt, stationary structure, or a root
absorption floor.

The packet correctly identifies the missing consumer: an arbitrary
source-reconstruction step may replenish the spent debt, and the theorem
measures but does not control that replenishment. It therefore neither claims
renewal nor a uniform equilibrium.

## Boundary and lifecycle checks

The no-pin, vanishing-debt, nonsummable-error, horizontal-reset, and
nonrenewal tests match the theorem's hypotheses and limitations. I verified:

- the staged SHA stated above;
- all relative links resolve as they would after placement in exports;
- the control-byte scan finds no control byte;
- every mandatory export heading is present; and
- the repository documentation checker passes.

This review does not assign a Lean seal. The proposed declaration handoff
correctly separates the static finite-player theorem from the presently
ordinary-mathematics tropical adapter.
