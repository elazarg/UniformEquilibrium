# Review of fixed cap-pin coordinate debt drop

Reviewer: `CODEX_SPINOZA`

Reviewed file:
`notes/CODEX_HAHN__FIXED_CAP_PIN_COORDINATE_DEBT_DROP.md`

Reviewed SHA-256:
`a4b9e7cf7b60a2566c07eeb47a942549a5bd68715c42d8a197d1c84705198a75`

## Verdict

**PASS.**  I found no mathematical or source-correspondence objection.  The
pointwise theorem really is finite-player, does not use positive global
minimum debt, and gives the stated uniform decrease of the named coordinate
for every exact product root.  Its nonrenewal qualification is necessary and
correct.

## Claim reconstructed

For a terminal semantic pair (X=(u,B)), a fixed player (b), and
(d_b=B_b-u_b\ge\gamma>0), suppose the prescribed payoff and all rewards
have absolute value at most (M), and

\[
 |B_b-r_b(\{b\})|\le \gamma/4.
\]

Then every exact independent product Nash root (q) against (u) decreases
the literal prefixed (b)-debt by at least

\[
 \min\{\gamma/2,\gamma^2/(16M)\}.
\]

If all input semantic debts are nonnegative, exact prefix monotonicity gives
the same lower bound on total debt drop.  For the tropical source sequence,
the last mover's fixed exact-cap gain supplies the debt floor and the reviewed
cluster-point cap identity supplies the cap-to-solo pin, hence the sequential
corollary applies uniformly to every sufficiently late root selection.

## Algebra and constants

Let (c_b) be opponent Continue mass, (alpha=1-c_b), and
(s_b=r_b(\{b\})).  Against the opponents' product coalition law,

\[
 e=Q_b-C_b
   =\sum_S\pi_q(S)f(S),
\]

with (f(\varnothing)=s_b-u_b) and
(f(S)=r_b(S\cup\{b\})-r_b(S)) for nonempty (S).  The assumptions give
(s_b-u_b\ge3\gamma/4).  Both (f(\varnothing)) and every nonempty
(f(S)) have magnitude at most (2M), so replacing the nonempty mass by the
empty value costs at most (4M\alpha):

\[
 |e-(s_b-u_b)|\le4M\alpha.
\]

If (alpha\ge\gamma/(16M)), the exact checked debt action

\[
 d'_b=[c_bd_b-[e]_+]_+
\]

implies (d_b-d'_b\ge\alpha d_b\ge\gamma^2/(16M)).  Otherwise
(e>\gamma/2); exact binary complementarity forces (q_b=1), and

\[
 d_b-[c_bd_b-e]_+\ge\min\{d_b,e\}\ge\gamma/2.
\]

The signs and strictness are correct.  In particular, the second case uses
Quit-minus-Continue orientation, so positive (e) forces sure Quit rather
than sure Continue.

## Semantic and strategy-class audit

- `quittingTerminalSemanticDebt_prefix_eq_blockAct` in
  `UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean` has exactly the
  opponent-survival and positive exercise-premium formula used above.
- `quittingTerminalSemanticDebt_prefix_le` justifies summing the named
  coordinate decrease into total debt decrease when the other debts are
  nonnegative.
- The cap (B_b) is the complete behavioral best-response envelope.  No
  bounded-clock or stationary-deviation reduction is introduced in the
  pointwise proof.
- Only the current row is an independent product law; the proof does not
  claim correlated-recommendation coverage.
- The theorem does not infer a second application after prefixing.  The new
  cap is the displayed max of the immediate Quit endpoint and the
  cap-substituted Continue endpoint and need not remain near (s_b).

## Tropical adapter

The reviewed tropical export supplies, at the actual source of the final
Quit0 edge, a fixed mover (b), a fixed positive exact-cap gain, and for
every semantic cluster point (y) the identity (B_b(y)=s_b).  Since the
scalar cap sequence is bounded, having this same value at every cluster point
does imply (B_{n,b}\to s_b).  Exact cap attainment makes the edge gain equal
to (B_{n,b}-u_{n,b}=d_{n,b}).  Thus the adapter's fixed debt and cap-pin
claims are faithful to the exported packet.

The result remains one-step only: the export does not give the same cap pin
at the child, and this review does not infer renewal, a punishment-floor
path, a terminal profile, or a uniform-equilibrium payoff.

