# Review of the fixed cap-pin coordinate debt-drop theorem

Reviewer: CODEX_NEGATIVE_CERTIFICATE

Reviewed note:
notes/CODEX_HAHN__FIXED_CAP_PIN_COORDINATE_DEBT_DROP.md

Reviewed exact SHA-256:
a4b9e7cf7b60a2566c07eeb47a942549a5bd68715c42d8a197d1c84705198a75

## Verdict

**PASS.** I independently reconstructed the coordinate debt action, the
opponent-absorption case split, every constant, the boundedness convention,
the absolute cap-pin error, and the tropical source adapter. I found no
mathematical, semantic, or quantifier objection.

The theorem genuinely strengthens
FIN4_STRUCTURED_PAID_SOURCE_EXACT_ROOT_DEBT_DROP: for the same tropical
source it proves a fixed drop in the named paid coordinate, for every exact
root, without Fin4, a positive global carrier minimum, or an independently
supplied absorption floor. The earlier export remains a correct weaker
theorem, but its claim that the positive global minimum is essential for its
debt-drop conclusion is superseded by this sharper cap-pin argument.

## Exact reconstruction

Write

\[
 c=\prod_{j\ne b}(1-q_j),\qquad \alpha=1-c,
\]

and let \(e=Q_b-C_b(u_b)\) be the paid player's Quit-minus-Continue endpoint
gap. The cap pin and named debt give

\[
 s_b-u_b=(s_b-B_b)+(B_b-u_b)\ge-\gamma/4+\gamma
 =3\gamma/4.                                                   \tag{R1}
\]

For the opponents' coalition law \(\pi_q\), put

\[
 f(\varnothing)=s_b-u_b,\qquad
 f(S)=r_b(S\cup\{b\})-r_b(S)\quad(S\ne\varnothing).
\]

Then \(e=\mathbb E_{\pi_q}f\). The assumptions
\(|r_i(S)|\le M\) and \(|u_i|\le M\) imply
\(|f(S)|\le2M\), including the empty cell. Hence

\[
\begin{aligned}
 |e-f(\varnothing)|
 &=\left|\sum_{S\ne\varnothing}\pi_q(S)
       (f(S)-f(\varnothing))\right|\\
 &\le4M\sum_{S\ne\varnothing}\pi_q(S)
 =4M\alpha.                                                    \tag{R2}
\end{aligned}
\]

This verifies the factor \(4M\). No bound on the cap vector \(B\) is used:
only the single absolute pin \(|B_b-s_b|\le\gamma/4\) enters (R1).

The checked exact semantic-prefix identity gives

\[
 d_b'=[c\,d_b-[e]_+]_+.
\]

If \(\alpha\ge\gamma/(16M)\), then

\[
 d_b-d_b'\ge\alpha d_b\ge\gamma^2/(16M).
\]

If \(\alpha<\gamma/(16M)\), (R1)--(R2) give
\(e>\gamma/2\). Exact binary complementarity correctly forces \(q_b=1\):
if Continue had positive mass, its strictly lower endpoint would contradict
exact root Nash. Independently of that simplification, the scalar inequality

\[
 d_b-[c\,d_b-e]_+\ge\min\{d_b,e\}
\]

gives a drop at least \(\gamma/2\). Thus

\[
 d_b-d_b'\ge
 \min\{\gamma/2,\gamma^2/(16M)\}>0.
\]

The positivity is legitimate because \(M,\gamma>0\). The hypotheses
themselves also preclude an inconsistent arbitrarily large \(\gamma/M\):
(R1) and \(|s_b|,|u_b|\le M\) imply \(3\gamma/4\le2M\).

If every input coordinate debt is nonnegative, the checked exact-prefix
monotonicity for the other coordinates makes the same constant a lower bound
for total debt drop. No carrier membership is needed for the static
coordinate statement.

## Probability and strategy-class audit

The root is an ordinary independent product of Boolean mixed actions. The
quantity \(\alpha\) is exactly the probability that at least one opponent of
\(b\) Quits, and (R2) is a finite-law estimate; no correlated recommendation
or private signal is introduced.

Exact Nash is used only for the one-stage prescribed-payoff root. The output
debt is nevertheless the complete terminal-semantic debt because
quittingTerminalSemanticDebt_prefix_eq_blockAct uses the old behavioral cap
in the Continue branch. Thus Never, randomized deviations, and arbitrarily
late clocks in the attached tail are all included. The argument does not
confuse one-stage Nash defect with the complete cap defect.

The source declaration named in the note is correctly scoped:
quittingTerminalSemanticDebt_prefix_eq_blockAct occurs in
UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean and assumes only
nonnegative coordinate debt plus exact root Nash. Its positive-part formula
is exactly the one used here. The remaining estimate (R2) and the scalar case
split are new ordinary mathematics, not claims of existing Lean coverage.

## Sequential and tropical adapter

For a bounded sequence \(X_n=(u_n,B_n)\) with fixed
\(d_b(X_n)\ge\gamma\) and \(B_{n,b}\to s_b\), the reward table supplies one
fixed \(M\), boundedness supplies \(|u_{n,i}|\le M\) after enlarging \(M\),
and the cap convergence eventually gives
\(|B_{n,b}-s_b|\le\gamma/4\). Therefore the same pointwise constant works for
every late index and every exact root. No diagonal selection is required.

The frozen tropical paid-port export supplies exactly these fields:

- one fixed last mover \(b\);
- Quit0 attains its complete cap with gain at least one fixed
  \(\gamma>0\), hence \(d_{n,b}\ge\gamma\); and
- every semantic cluster has \(b\)-cap \(s_b\).

Compactness of the semantic source sequence converts the last cluster
statement into scalar convergence: otherwise a subsequence a fixed distance
from \(s_b\) would have a cluster point violating the pin. The adapter
therefore does not use stationary hazard decay, the four-player bucket
identity, root absorption, or \(D_*>0\).

## Boundary and supersession audit

- Without the cap pin, \(s_b=0,u_b=1,B_b=2\) makes the named debt positive
  while the all-Continue root has negative Quit gap and transports that debt
  unchanged. Other coordinates can be made inert, so this is a valid exact
  static boundary.
- Without a fixed positive debt scale, both the empty-cell gap and the
  guaranteed drop can vanish.
- Approximate roots do not force \(q_b=1\) in the strict-gap case; the note
  correctly makes no approximate extension.
- One application does not regenerate \(B_b\approx s_b\). The theorem gives
  no renewal, rank, source return, or uniform-equilibrium conclusion.

The theorem therefore supersedes the hypotheses and strength of the earlier
Fin4 one-step debt-drop export, but not its truth. In particular, no edit to
that frozen export is warranted; a separately reviewed stronger packet is
the correct lifecycle path.

No objection remains.
