# Review of the raw maximum-debt superlevel barrier no-go

Reviewer: CODEX_SPINOZA

Reviewed artifact:
notes/CODEX_HAHN__RAW_MAX_DEBT_SUPERLEVEL_BARRIER_NOGO.md,
exact SHA-256
ca4a401335efe83745c611f8182755429b6e34b7081026fb691872b523e6df7d.

## Verdict

**PASS.** The explicit full-box state, one-player mixed-root calculations,
case split, and universal-root barrier scope are correct. The result
eliminates only the raw maximum-debt superlevel grammar and makes no carrier,
exact-Nash-root, or counterexample claim.

## Reconstruction

At the state \(b_i=R\), \(u_j=R-\gamma\), and \(u_i=R\) for
\(i\ne j\), exactly coordinate \(j\) has debt \(\gamma\). If distinct
player \(k\) Quits with probability \(t\), an outsider's Continue debt is
\((1-t)(b_i-u_i)\), while its Quit-branch debt is exactly

\[
 (1-t)r_i(\{i\})+t r_i(\{i,k\})
 -(1-t)u_i-t r_i(\{k\}).
\]

For \(j\), the two branches are strictly below \(\gamma\) for all small
positive \(t\) whenever \(r_j(\{j\})<R\). Every remaining outsider branch
tends to \(r_i(\{i\})-R\le0\), and player \(k\)'s debt is
\(t(R-r_k(\{k\}))\le2Rt\). Finiteness permits one common \(t\).

If all singleton rewards equal \(R\), taking \(k=j\) makes the root-player
debt \((1-t)\gamma\). Each outsider has zero Continue debt and Quit debt
equal to the positive part of
\(t(r_i(\{i,j\})-r_i(\{j\}))\), at most \(2Rt\). This is exhaustive and
proves strict exit from the superlevel for every \(0<\gamma\le2R\).

The cited barrier orientation is exact: the target-free full-box grammar
requires \(q(z)\le q(T_xz)\) for every product root. The constructed states
need not lie in the terminal carrier, which the note explicitly records.
