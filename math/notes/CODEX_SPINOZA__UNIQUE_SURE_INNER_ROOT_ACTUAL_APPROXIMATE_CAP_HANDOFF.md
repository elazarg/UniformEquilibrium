# A unique-sure inner root gives an actual approximate-cap handoff

Author: CODEX_SPINOZA

## Status

**Exact ordinary mathematics; source-attached reduction, not Lean-checked and
not a paid-port consumer.** In the zero-inner-survival arm of the persistent
capacity spine, the finite capacity-selected roots need not have the special
Alternative-B provenance required by the existing exact-cap handoff.
Nevertheless, exact-root debt monotonicity and the positive global minimum
force all debt onto the limiting sure owner. An arbitrarily accurate cap
response at the literal finite child then produces a fixed-gain actual edge,
kills the owner's debt up to the chosen error, and exposes a distinct
full-gap debtor at the child.

This removes the merely stationary nature of the unique-sure handoff. It
does not make the first cap response attained, put the child exactly above
punishment, or turn either behavioral update into a Nash--Bellman edge.

## 1. Self-contained input

Let \(I=\operatorname{Fin}4\), let \(r\) be a bounded quitting reward table,
and suppose the contrary hard branch supplies constants

\[
 D_*>0,\qquad \Gamma>0,
\tag{1}
\]

such that every actual terminal profile has total debt at least \(D_*\) and
has some player's complete behavioral debt at least \(\Gamma\).

Let \(X_n\) be arbitrary actual continuation profiles. Let \(q_n\) be exact
independent product Nash roots against their literal prescribed payoff
\(U(X_n)\), and put

\[
 \rho_n=q_n\triangleright X_n.
\tag{2}
\]

Assume, after a subsequence, that \(q_n\to q\), where \(k\) is the unique
sure quitter:

\[
 q_k=1,\qquad q_i<1\quad(i\ne k).
\tag{3}
\]

All complete debts of the \(X_n\) are uniformly bounded; this follows from
bounded rewards and the zero payoff of Never.

The application is \(q_n=q_{K,0}\), \(X_n=X_K\) in
CODEX_SPINOZA__PERSISTENT_INNER_MARK_DELAYED_PAID_SOURCE_OR_SURE_HANDOFF.
No stationarity or cap attainment of \(X_n\) is assumed.

## 2. Debt concentrates on the sure owner

### Theorem 2.1

For every outsider \(i\ne k\),

\[
 d_i(\rho_n)\longrightarrow0.
\tag{4}
\]

Consequently

\[
 d_k(\rho_n)\ge D_*/2
\tag{5}
\]

for all sufficiently large \(n\).

### Proof

The checked exact-root prefix inequality gives

\[
 d_i(\rho_n)
 \le s_{n,i}d_i(X_n),\qquad
 s_{n,i}:=\prod_{\ell\ne i}(1-q_{n,\ell}).
\tag{6}
\]

For \(i\ne k\), the product \(s_{n,i}\) contains
\(1-q_{n,k}\to0\). Uniform boundedness of the tail debts proves (4).
Since \(\rho_n\) is an actual profile, its total debt is at least \(D_*\).
There are only three outsiders, so (4) implies (5). QED

The conclusion is stronger than finite pigeonhole on the cap-defect ledger:
the payer label is the unique sure owner \(k\). Prefixing any additional
finite word of exact payoff roots cannot increase an outsider's debt, so the
same concentration remains true at every finite outer ancestor.

## 3. Literal approximate-cap child

Fix once and for all

\[
 0<\varepsilon<\min\{D_*/4,\Gamma/4\}.
\tag{7}
\]

### Theorem 3.1

For every sufficiently large \(n\), there is an actual behavioral response
\(\beta_{n,k}\) at \(\rho_n\) and a literal child

\[
 \chi_n=\rho_n[k\leftarrow\beta_{n,k}]
\tag{8}
\]

such that

\[
 U_k(\chi_n)-U_k(\rho_n)
 \ge d_k(\rho_n)-\varepsilon
 \ge D_*/2-\varepsilon,
\tag{9}
\]

and

\[
 d_k(\chi_n)\le\varepsilon.
\tag{10}
\]

The response can be chosen to force Continue at the newly prefixed root and
then use an approximate cap response in the literal tail \(X_n\).

At the same child there is a fixed outsider label \(j\ne k\), after a
subsequence, with

\[
 d_j(\chi_n)\ge\Gamma.
\tag{11}
\]

In particular, pure-time extremality supplies at \(\chi_n\) a deterministic
finite-or-Never response for \(j\) of gain at least \(\Gamma/2\).

### Proof

Let \(Q_n\) and \(C_n(u)\) be player \(k\)'s Quit and Continue endpoints at
the root \(q_n\), with continuation coordinate \(u\). Since
\(q_{n,k}>0\) eventually and \(q_n\) is exact Nash against \(U(X_n)\), the
prescribed root payoff is the Quit endpoint:

\[
 U_k(\rho_n)=Q_n
 =\max\{Q_n,C_n(U_k(X_n))\}.
\tag{12}
\]

The complete cap of the prefixed profile is

\[
 B_k(\rho_n)=\max\{Q_n,C_n(B_k(X_n))\}.
\tag{13}
\]

By (5), (13) is strictly larger than \(Q_n\). Hence the cap endpoint in
(13) is Continue. The opponents' Continue mass

\[
 s_{n,k}=\prod_{i\ne k}(1-q_{n,i})
\tag{14}
\]

converges to a positive number by uniqueness in (3). Choose in the actual
tail \(X_n\) a behavioral response whose payoff is within
\(\varepsilon/s_{n,k}\) of \(B_k(X_n)\), force Continue at the new root, and
call the resulting complete response \(\beta_{n,k}\). Affinity of the
Continue endpoint gives (9).

Player \(k\)'s opponents are unchanged by its own update, so its complete
cap remains \(B_k(\rho_n)\). Equation (9) therefore gives (10).
Apply the terminal gap at the actual child \(\chi_n\). Some player has debt
at least \(\Gamma\); by (7) and (10), it is not \(k\). Finite pigeonhole
fixes an outsider \(j\) on a subsequence. Complete behavioral caps equal
the supremum of deterministic finite quit times and Never, so a member of
that class gains at least \(\Gamma/2\). QED

### Corollary 3.2: outer ancestry retains the paid response

Let \(P_n\) be any finite literal word of exact payoff roots prefixed outside
\(\rho_n\), and suppose its joint survival \(R_n\) has a positive lower
bound. At

\[
 \Sigma_n=P_n\triangleright\rho_n,
\tag{15}
\]

player \(k\) can copy its prescribed behavior through \(P_n\) and use
\(\beta_{n,k}\) only after reaching \(\rho_n\). The exact copied-prefix
identity gives gain

\[
 R_n\bigl(U_k(\chi_n)-U_k(\rho_n)\bigr).
\tag{16}
\]

Thus the all-summable matched-capacity word, whose outer survival tends to
\(R_\infty>0\), retains a fixed-gain delayed response even when its inner
root has zero joint Continue mass.

## 4. Exact relation to the cap-live ledger

At a unique-sure limiting inner root, the full word has vanishing joint
survival, so its terminal tail-debt term in the cap-anchored identity is
erased. The positive global minimum must therefore appear in its reached
cap-defect ledger. Theorem 2.1 identifies more than the generic fixed-payer
pigeonhole: all outsider coordinates vanish, so the surviving aggregate
payer is \(k\).

The child (8) spends that payer's debt to within \(\varepsilon\), but the
first response changes the continuation target against which the inner and
outer roots were solved. The distinct response at (11) is consequently a
second horizontal behavioral edge, not a chronological exact root. The
ledger has located and spent the payer, but it has not regenerated an exact
Nash--Bellman source.

## Sources inspected

- UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean, especially
  quittingTerminalDeviationDebt_rootThenContinuation_eq and
  quittingTerminalDeviationDebt_rootThenContinuation_le;
- UniformEquilibrium/Quitting/Root/LiteralPrefixDeviationTransport.lean;
- UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean;
- notes/CODEX_BLINDSPOT__CAP_LIVE_BOUNDARY_LEDGER_AND_HOST_ROTATION.md;
- notes/CODEX_HAHN__FINITE_NEAR_SURE_ROOT_ACTUAL_CAP_HANDOFF.md;
- notes/CODEX_SPINOZA__CAPACITY_GAP_ROOT_MATCHING_OR_PERSISTENT_INNER_MARK.md;
  and
- notes/CODEX_SPINOZA__PERSISTENT_INNER_MARK_DELAYED_PAID_SOURCE_OR_SURE_HANDOFF.md.

## Boundary and nonclaims

- The response \(\beta_{n,k}\) is \(\varepsilon\)-cap-attaining, not exactly
  cap-attaining. Nonattainment is allowed and no compactness of the complete
  strategy space is used.
- Accordingly \(U_k(\chi_n)\ge\operatorname{Pun}_k-\varepsilon\), but an
  exact punishment-floor source is not claimed.
- The theorem does not instantiate the existing exact finite-source handoff,
  whose Alternative-B input includes an attained cap response.
- The two fixed-gain behavioral edges occur at successive actual profiles;
  they are not exact roots, a return, or a renewable finite rank.
- No uniform-equilibrium payoff is claimed.

## Next exact question

Can the summable choice of cap errors \(\varepsilon_n\downarrow0\), together
with the fixed owner/outsider edge pair (9)--(11), be inserted into an
approximate Nash--Bellman chain whose total target error is summable? The
missing estimate is still the change in every nonmover's root target after
the first behavioral update; (9) controls only the mover's cap error.
