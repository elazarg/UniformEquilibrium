# A vanishing-band live cap target carries a distinct paid tail debtor

Author: CODEX_SPINOZA

## Status

**Exact ordinary mathematics; source-attached two-edge reduction, not
Lean-checked and not a Nash--Bellman return.** A vanishing-width cap-band
target in the unique-sure persistent-word branch makes the owner Continue
surely through the old exact word, reaches its literal actual suffix with a
fixed probability, and has vanishing complete owner debt. The reached suffix
therefore also has vanishing owner debt. The game-level terminal gap then
selects a fixed distinct player with a fixed pure-time-or-Never gain at that
same actual suffix. Lifting this response behind the unchanged word gives a
second literal paid edge beginning only at the tail boundary and having a
fixed unconditional gain.

This places the owner repair and a distinct full-gap response in one actual
chronology with a strict cut order. It does not make the modified word Nash
for the outsiders or return either child to the original exact source.

## 1. Input

Let \(I=\operatorname{Fin}4\), let \(r\) be a bounded quitting table in the
no-uniform-payoff branch, and fix a terminal exploitability witness
\(\Gamma>0\): every actual behavioral profile has some player whose complete
behavioral debt is at least \(\Gamma\).

Use the unique-sure persistent-word source

\[
 \Sigma_n=W_n\triangleright X_n,
 \qquad m_n=|W_n|,
\tag{1}
\]

with owner \(k\), where every row of \(W_n\) is an exact payoff Nash root
against its literal successor, and eventually

\[
 d_k(\Sigma_n)\ge D_*/2,
 \qquad
 \beta_{n,k}:=\Pr_{\Sigma_n}(T_{-k}\ge m_n)\ge\eta>0.
\tag{2}
\]

Choose \(e_n\downarrow0\) with \(0<e_n<D_*/4\). Apply the width-\(e_n\)
cap-band pushforward to player \(k\)'s source law using an
\(e_n/2\)-near-cap receiver, and call the actual target \(Y_n\).

The reviewed exact-word screen and late-receiver argument give

\[
 U_k(Y_n)-U_k(\Sigma_n)
 \ge d_k(\Sigma_n)-e_n\ge D_*/2-e_n,
 \qquad d_k(Y_n)\le e_n,
\tag{3}
\]

and player \(k\) Continues surely at every date before \(m_n\). Hence

\[
 a_n:=\Pr_{Y_n}(T_I\ge m_n)=\beta_{n,k}\ge\eta.
\tag{4}
\]

Let \(Z_n\) be the literal actual suffix of \(Y_n\) beginning at date
\(m_n\). It consists of the original opponents from \(X_n\) and the
conditional residual of the pushed owner law; it is not identified with
\(X_n\).

## 2. The reached suffix loses the owner debt

### Lemma 2.1

For every \(n\),

\[
 a_n d_k(Z_n)\le d_k(Y_n),
 \qquad
 d_k(Z_n)\le e_n/\eta\longrightarrow0.
\tag{5}
\]

### Proof

Fix any complete behavioral deviation of player \(k\) in \(Z_n\). In the
full profile, let \(k\) copy its prescribed strategy through the word and
switch to that deviation exactly at date \(m_n\). The two full profiles are
identical unless the word jointly Continues, and conditional on that event
their payoff difference is the suffix payoff difference. Therefore the
full gain is exactly \(a_n\) times the suffix gain. Take the supremum over
all suffix deviations. Equations (3)--(4) give (5). QED

No cap attainment is used in this argument.

## 3. A fixed distinct paid response behind the word

### Theorem 3.1

After a finite shift and a subsequence, there is one fixed player
\(j\ne k\) and, for every retained \(n\), a pure finite-time-or-Never
response \(Q_{r_n}\) at the literal suffix \(Z_n\) such that

\[
 U_j\bigl(Z_n[j\leftarrow Q_{r_n}]\bigr)-U_j(Z_n)
 \ge \Gamma/2.
\tag{6}
\]

Let \(\widehat Y_n\) be the full behavioral profile in which player \(j\)
copies its prescribed strategy in \(Y_n\) at every date before \(m_n\), and
uses \(Q_{r_n}\) in the suffix. Then

\[
 U_j(\widehat Y_n)-U_j(Y_n)
 \ge \eta\Gamma/2.
\tag{7}
\]

The profiles \(Y_n\) and \(\widehat Y_n\) agree literally before the tail
boundary, and both reach that boundary with probability \(a_n\ge\eta\).
Thus the first possible disagreement of the second paid edge is at date
\(m_n\), strictly after the first cap-band cut \(c_n<m_n\).

### Proof

By the terminal exploitability witness, some player has debt at least
\(\Gamma\) at each actual suffix \(Z_n\). Equation (5) makes the owner debt
strictly smaller than \(\Gamma\) eventually, so the debtor is not \(k\).
Finite pigeonhole among the three outsiders fixes one label \(j\) along a
subsequence. Behavioral pure-time extremality and the definition of a
supremum give a finite-time-or-Never response within \(\Gamma/2\) of the
cap, proving (6).

The lifted deviation copies the entire word. The exact common-prefix payoff
identity therefore makes its full gain \(a_n\) times the suffix gain. Use
(4) and (6) to obtain (7). Prefix equality and the cut ordering are
definitional. QED

One may instead choose the suffix response within any tolerance
\(\varepsilon_n\downarrow0\); its suffix gain is then at least
\(\Gamma-\varepsilon_n\), and the response child has suffix
\(j\)-debt at most \(\varepsilon_n\). This does not control player \(j\)'s
complete debt at the full parent, because deviations before \(m_n\) remain
available there.

## 4. Relation to the cap-ledger dichotomy

The modified word has an exact cap-anchored defect ledger. If its outsider
ledger has a fixed positive part, the reviewed live-target ledger dichotomy
already selects a fixed outsider response whose first disagreement lies
inside \(W_n\). If the entire ledger tends to zero, the word is an
approximate **cap--Nash** stack with vanishing total unweighted cap-root
error; Theorem 3.1 supplies the distinct paid response at its actually
reached tail.

The latter is not the ordinary approximate Nash--Bellman forward packet:
cap-root inequalities use the successor cap vector, while the exact Bellman
recursion uses the successor prescribed payoff vector. The two vectors need
not be close. Thus the exhaustive output is

\[
 \boxed{
 \text{fixed outsider paid inside the live word}
 \quad\text{or}\quad
 \text{vanishing-error cap--Nash word ending at a fixed outsider paid tail}.}
\tag{8}
\]

Both alternatives retain the same actual owner edge
\(\Sigma_n\dashrightarrow_kY_n\), and both have a fixed reach floor. Neither
is yet an executable exact or approximate payoff Nash--Bellman return.

## Sources inspected

- `notes/CODEX_SPINOZA__EXACT_WORD_FORCES_LATE_CAP_BAND_RECEIVER_AND_LIVE_TARGET.md`;
- `notes/CODEX_HAHN__LIVE_CAP_BAND_TARGET_LEDGER_DICHOTOMY.md`;
- `UniformEquilibrium/Quitting/Root/LiteralPrefixDeviationTransport.lean`;
- `UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean`;
- `UniformEquilibrium/Diagnostics/Quitting/TerminalCapNashChronology.lean`;
  and
- `Research/Quitting/PaidNonexactCapStackAccount.lean`.

## Boundary and nonclaims

- The tail \(Z_n\) is an actual conditional suffix of \(Y_n\), not the old
  tail \(X_n\) or a compactly reselected realizer.
- The second response begins at the tail boundary by construction; its
  pure clock is relative to \(Z_n\) and may be Never.
- The fixed label \(j\) is selected after the suffixes are formed. It need
  not equal a debtor or paid-row label from an earlier source packet.
- The cap--Nash alternative does not satisfy the common-continuation
  support-Nash clause of the approximate-forward-packet question.
- No punishment-floor preservation, exact-root revalidation, source return,
  renewable rank, terminal approximate Nash profile, or uniform-equilibrium
  payoff is proved.

## Next exact question

Can positive global minimum convert the vanishing-error cap--Nash word in
(8) into a prescribed-payoff Nash--Bellman word, or charge the fixed
cap/payoff continuation mismatch to the post-tail outsider edge? The exact
one-row cap/payoff regression shows that no such conversion is purely local.
