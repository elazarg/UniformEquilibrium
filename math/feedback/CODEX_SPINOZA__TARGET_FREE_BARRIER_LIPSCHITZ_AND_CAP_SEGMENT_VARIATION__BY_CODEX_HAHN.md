# Review of target-free barrier Lipschitz continuity and cap-segment variation

Reviewer: `CODEX_HAHN`

Reviewed SHA-256:
`b9445e1a86d641603bd3c908cd8639aeaa574866c4df9116f50c4432439c273c`.

## Verdict

**PASS.** The uniform prefix estimate proves the stated global
\(2\)-Lipschitz modulus for \(Q\). The stopping-law coupling, cap-segment
variation, exact constants, and two-sure-clock direction audit are correct.
The note correctly stops before the missing inverse capacity-pricing
estimate.

## Mathematical audit

The checked theorem
`quittingTerminalSemanticPrefix_within` is exactly nonexpansiveness in the
coordinatewise payoff/cap sup metric. Iteration preserves the same constant
for every word length. The raw objective
\(d(U,B)=\max_i(B_i-U_i)\) is \(2\)-Lipschitz in that metric. Hence the whole
family of functions \(p\mapsto d(T_wp)\) is equi-\(2\)-Lipschitz, and taking
their infimum gives

\[
 |Q(p)-Q(q)|\le2\rho(p,q).
\]

This legitimately strengthens the generic upper-semicontinuity statement;
it does not interchange an infimum and a limit.

For profiles differing in one player's stopping law by total variation
\(\delta\), maximal coupling makes every fixed prescribed or deviating payoff
differ by at most \(2M\delta\). The mover's own cap is unchanged, and the
same coupling is uniform over each outsider's unrestricted response before
taking its supremum. Thus the full semantic distance is at most
\(2M\delta\), and the barrier difference at most \(4M\delta\). The convention
is the probability total variation \(\sup_A|\mu(A)-\nu(A)|\), so these
constants are correct.

On the private segment,
\[
 \|\mu_t-\mu_s\|_{\rm TV}
 =|t-s|\|\mu_1-\mu_0\|_{\rm TV}\le|t-s|,
\]
and summing the Lipschitz estimates over any ordered partition proves total
variation at most \(4M\). At \(t_*=1-\lambda\), the cap-pin theorem has
\(g=\lambda\gamma\). Since every gain is at most \(2M\),
\(g/(16M)<1\), so \(a_0=\lambda\gamma/(16M)\), and
\[
 4M\lambda=(64M^2/\gamma)a_0.
\]
The slice constant in (18) is therefore exact.

After two sure clocks, the reviewed universal-descendant theorem gives
\(L_m\ge0\) and bounded monotonicity makes \(\sum_mL_m<\infty\).
Lipschitz continuity yields only \(L_m\le4M\delta_m\). It cannot be reversed
to price \(K_m\), and the note does not reverse it.

## Scope

The proof gives no continuity of the exact-block capacity potential and no
lower modulus for barrier displacement. The cap gain's lower bound on law
distance and the barrier's upper Lipschitz bound are correctly kept in
opposite directions. The source cap-segment estimate also does not
automatically identify the post-prefix sibling seam.
