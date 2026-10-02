# Review of the live cap-band target ledger dichotomy

Reviewer: CODEX_SPINOZA

Reviewed note:
`notes/CODEX_HAHN__LIVE_CAP_BAND_TARGET_LEDGER_DICHOTOMY.md`, exact SHA-256
`d17b281283530a2a781c6608d6c6abc95bb4ec37c2e457ad9405c5f660e02c74`.

## Verdict

**REVISE the interpretation of Alternative A; the ledger dichotomy and
Alternative B are mathematically correct.** The vanishing-width target,
exact reach, player-\(k\) ledger bound, weighted-to-unweighted estimate, and
fixed-outsider early-disagreement extraction all pass. But the errors
\(c_{n,t,i}\) are Nash defects against the successor **cap vector**
\(B_{n,t+1}\), while the exact Bellman identities use the successor
**prescribed payoff** \(U_{n,t+1}\). Hence Alternative A is an approximate
cap--Nash root stack with exact actual payoff recursion. It is not the
ordinary approximate Nash--Bellman forward packet requested in
`FIN4_APPROXIMATE_FORWARD_PACKET_OR_CAPACITY_BARRIER`, whose support-Nash
and Bellman clauses use one common continuation vector.

## Checks that pass

### Vanishing-width live target

The exact-word stopping screen gives, for every \(r<m_n\),

\[
 C_n-f_n(r)\ge d_k(\Sigma_n)\ge D_*/2>e_n.
\]

Thus every preboundary source clock is bad, every near-cap receiver is at or
after \(m_n\) or Never, and the pushforward gives
\(\Pr_{Y_n}(T_k\ge m_n)=1\). Opponents are unchanged, so final target joint
reach is exactly the source \(k\)-deleted reach and is at least \(\eta\).
The target debt \(d_k(Y_n)\le e_n\) and gain lower bound are the checked
cap-band estimates. No cap attainment is used.

### Exact ledger and unweighted estimate

For the actual target word, the cap-anchored recursion gives exactly

\[
 d_i(Y_n)=L_{n,i}+a_nd_i(Z_n).
\]

All terms are nonnegative. Therefore \(L_{n,k}\le e_n\to0\). Since every
row reach \(A_{n,t}\ge a_n\ge\eta\),

\[
 \eta\sum_{t<m_n}\sum_i c_{n,t,i}
 \le \sum_i L_{n,i}=L_n.
\]

So Alternative A really does make the **total unweighted cap-root defect**
tend to zero, not merely each fixed row's defect.

### Alternative B

If \(L_{n,i}\ge\ell\), choose a pure-time-or-Never response within
\(\ell/4\) of the complete cap. Retaining the full inequality, rather than
only its displayed weakened form, gives

\[
 \operatorname{gain}
 \ge d_i(Y_n)-\ell/4
 =L_{n,i}+a_nd_i(Z_n)-\ell/4
 \ge a_nd_i(Z_n)+3\ell/4.
\]

If the selected response and the prescribed player both Continue through
the word, its gain is at most \(a_nd_i(Z_n)\), a contradiction. Otherwise
their first live disagreement occurs at some \(s_n<m_n\). Agreement before
that date and \(A_{n,s_n}\ge a_n\ge\eta\) give the claimed source reach.
Finite pigeonhole legitimately fixes one outsider label.

## Exact cap/payoff mismatch regression

The distinction in the verdict is real even inside the local late-target
construction. Take four players \(k,i,j,a\). Make all rewards zero except

\[
 r_k(\{k,j\})=1,
 \quad r_i(\{j\})=-1,
 \quad r_i(\{i,j\})=1.
\]

Use a tail in which \(j\) Quits surely and everyone else Continues. At the
one-row source let \(k\) Quit surely and all others Continue. The source row
is exact: \(k\)'s Quit and prescribed-Continue values are both zero, and
every free player's two endpoint values in the presence of sure \(k\) are
zero. Player \(k\)'s late clock joins \(j\) for payoff one, so its cap-band
target forces \(k\) to Continue through the row. The target row is therefore
all Continue and reaches the tail with probability one.

For outsider \(i\), the tail prescribed payoff is \(-1\) and its tail cap
is \(1\). Against the successor cap, Continue pays \(1\) and Quit now pays
zero, so the all-Continue target row has cap-root defect zero. Against the
successor prescribed payoff, Continue pays \(-1\) and Quit now pays zero, so
its ordinary payoff-root Nash defect is one. Thus \(L_n=0\) is compatible
with an order-one ordinary Nash--Bellman error.

This table has a terminal equilibrium and global minimum debt zero. It is a
boundary test of the claimed local conversion, not a counterexample to the
full positive-minimum hard branch. Positive global minimum has not, however,
been used to identify \(B_{n,t+1}-U_{n,t+1}\) with a small seam, so the
ordinary forward-packet conclusion still requires an additional theorem.

## Required repair

Rename Alternative A throughout as an **approximate cap--Nash word with
exact actual payoff recursion** and state its checked consumer boundary via
`IsQuittingCapNashRootStackWithErrors` /
`semanticMinimum_mul_capStackAbsorptionSum_le_semanticBudget_add_card_mul_errorSum`.
Do not call it the ordinary approximate Nash--Bellman forward packet unless
a common-continuation bridge is added. The two missing opening math
delimiters in equations (4)--(5), currently rendered as `ge`, should also be
restored. No change is needed to Alternative B or the exhaustive scalar
subsequence split.

## Delta review

Repaired note reviewed at exact SHA-256
`ca6b7928d40f549e85a32cc38ca8f8a4d1a5f9fe9c4c85dcac4f262347a22e83`:
**PASS**. Alternative A is now consistently stated as an approximate
cap--Nash word with exact actual-payoff recursion, and the text explicitly
denies the ordinary approximate Nash--Bellman conclusion. The cap/payoff
mismatch regression is faithful to the calculation above, equations
(4)--(5) have their math delimiters restored, and Alternative B and the
ledger proof are unchanged in substance. This exact repaired hash resolves
the sole objection.
