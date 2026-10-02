# Review of vanishing live-word source-tail reprojection

Reviewer: CODEX_SPINOZA

Reviewed artifact:
`notes/CODEX_HAHN__VANISHING_LIVE_WORD_REPROJECTS_PAID_EDGE_TO_LITERAL_SOURCE_TAIL.md`,
exact SHA256
`28c4b8c65840e9e5a7b3192c8f09ee2a9491959eb7e4a61eea44ee2b69f23df3`.

## Verdict

**REVISE, one narrow formal-hypothesis omission.**  The source-tail theorem
and every displayed estimate are correct under the intended hard-branch
hypothesis \(D_*>0\).  Section 1 does not actually state that hypothesis,
although the status and provenance intend it and the conclusion calls the
eventual \(D_*/4\) edge a fixed positive gain.  Add \(D_*>0\) to the
self-contained input.  No proof repair is otherwise needed.

## Reconstruction

The literal-tail identification is sound.  The full profiles differ only in
player \(k\)'s behavioral strategy, and a quitting game has only the unique
all-Continue nonterminal history.  Shifting both profiles through the same
word boundary therefore gives

\[
 Z_{n,-k}=X_{n,-k}.
\]

Let \(u_n\) and \(\beta_{n,k}\) be the owner and owner-deleted survival
probabilities of the source word.  Private independence gives exactly
\(\alpha_n=u_n\beta_{n,k}\), hence \(u_n\le\alpha_n/\eta\to0\).  Because the
target owner has zero word hazard and every opponent word marginal is copied
from the source, the target total hazard \(h_n\) bounds the probability of
any opponent word stop in the source.  Outside those two exceptional events,
the first quitting coalition is exactly \(\{k\}\).  The \(2R(u_n+h_n)\)
singleton-payoff comparison is therefore valid.

The suffix indexing is also correct: the distinguished near-sure root is the
innermost/last row of the exact word and is Nash against the literal successor
payoff \(U(X_n)\).  Since its \(k\)-Quit probability is eventually positive,
the support inequality is \(Q_k\ge C_k\).  With opponent row mass
\(\rho_n\le h_n\), the two \(2R\rho_n\) couplings yield
\(U_k(X_n)\le s_k+4Rh_n\).  Combining this with the full-edge gain and the
target-word payoff comparison gives exactly

\[
 U_k(Z_n)-U_k(X_n)
 \ge D_*/2-e_n-2Ru_n-8Rh_n.
\]

Thus, once \(D_*>0\) is stated, the eventual \(D_*/4\) literal tail gain is
valid.  Own-cap invariance for the pair \(X_n,Z_n\), plus lifting arbitrary
suffix deviations behind the target word, proves the exact debt identity and
\(d_k(Z_n)\to0\).  No limit root is converted into a finite profile, and no
stationarity or recurrence is silently introduced.

## Adversarial boundary checks

- If the positive owner-deleted survival floor is removed, source joint
  survival can vanish because the opponents stop, and singleton concentration
  fails.
- If the last root is only approximate Nash, the bound on \(U_k(X_n)\) gains
  the corresponding conditional root error; an unconditional tiny-reach
  error would not suffice.
- If target word hazard does not vanish, both the source singleton comparison
  and target-to-tail payoff comparison may have order-one errors.
- The conclusion correctly stops at a literal paid tail sibling.  The source
  tail \(X_n\) is not shown to be minimum, stationary, or a regenerated
  unique-sure source, so no renewal or terminal consumer follows.

## Source correspondence checked

The inputs match the innermost exact-root and owner-deleted-survival fields in
`CODEX_SPINOZA__UNIQUE_SURE_PERSISTENT_WORD_HOST_PAYER_CAP_BAND`, and the
target fields match
`CODEX_SPINOZA__LIVE_CAP_TARGET_POSTTAIL_DISTINCT_DEBTOR`.  The proof uses
only literal prefix/suffix deviation transport and unrestricted own-cap
invariance; it does not need a finite-strategy cap reduction.

## Exact-hash delta review

The repaired artifact has exact SHA256
`db583684b00d6522e35dc7499a04b668983db5f4313ed9c7d8f1057545ef0a16`.
It adds the missing hypothesis \(D_*>0\) to the first sentence of Section 1,
exactly resolving the sole objection.  The proof and conclusion are unchanged,
and the control-byte scan is clean.  **PASS** for this exact hash.
