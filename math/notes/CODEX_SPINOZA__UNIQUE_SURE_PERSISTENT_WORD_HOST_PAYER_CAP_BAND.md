# A unique-sure persistent word has one common host and ledger payer

Author: CODEX_SPINOZA

## Status

**Exact ordinary mathematics; branch-local source adapter, not Lean-checked
and not a paid-port consumer.** In the unique-sure arm of the all-summable
persistent-inner-mark word, the sure owner is simultaneously:

1. the only player with a positive limiting deleted-survival clock;
2. the only player with nonvanishing full-profile debt; and
3. the only player with nonvanishing cap-anchored prefix ledger.

Therefore the fixed-payer cap-band theorem necessarily lands in its
host-equals-payer arm. It produces a fixed-gain actual update at a cut
strictly before the original tail boundary (hence no later than the inner
near-sure root) and preserves the positive host-deleted clock exactly. The
nonhost-payer clock-killing regression is excluded on this branch.

The cap-band target may still make the host Quit before the inner mark. Hence
deleted reach is preserved, but actual joint reach and the exact
Nash--Bellman root ancestry after the cut are not.

## 1. Persistent unique-sure input

For every \(n\), let

\[
 \Sigma_n=W_n\triangleright X_n
\tag{1}
\]

be an actual finite word over an actual tail. Every row of \(W_n\) is an
exact product Nash root against its literal successor payoff. Write
\(q_{n,0}\) for the innermost row and \(P_n\) for the outer rows, so

\[
 W_n=P_n\triangleright q_{n,0}.
\tag{2}
\]

Assume

\[
 q_{n,0}\longrightarrow q,\qquad
 q_k=1,\qquad q_i<1\quad(i\ne k),
\tag{3}
\]

and the outer marginal hazards are summable along the diagonal construction,
with no sure outer root in the surviving branch. The chosen diagonal has
positive limiting outer joint and player-deleted survival products. Let

\[
 \alpha_n=\Pr(W_n\text{ jointly survives}),\qquad
 \beta_{n,i}=\Pr(W_n\text{ survives after deleting }i).
\tag{4}
\]

All tail debts are uniformly bounded. The hard branch has positive global
minimum total debt \(D_*>0\), so \(D(\Sigma_n)\ge D_*\).

## 2. Host and payer identification

### Theorem 2.1

There is \(\eta>0\) such that, eventually,

\[
 \beta_{n,k}\ge\eta,\qquad
 \alpha_n\longrightarrow0,\qquad
 \beta_{n,i}\longrightarrow0\quad(i\ne k).
\tag{5}
\]

Moreover,

\[
 d_i(\Sigma_n)\longrightarrow0\quad(i\ne k),
\qquad
 d_k(\Sigma_n)\ge D_*/2
\tag{6}
\]

eventually.

Let \(\Lambda_{n,i}\) be the cap-anchored reached defect ledger of the exact
word \(W_n\) over \(X_n\). Then

\[
 \Lambda_{n,i}\longrightarrow0\quad(i\ne k),
\qquad
 \Lambda_{n,k}\ge D_*/3
\tag{7}
\]

eventually. Thus the unique live host and the fixed aggregate payer are the
same player \(k\).

### Proof

Deleting \(k\) removes its near-sure Quit factor. The remaining inner
opponent-Continue product tends to
\(\prod_{i\ne k}(1-q_i)>0\), and the outer deleted-survival product has a
positive limit by summability. This gives the first assertion in (5).
Joint survival retains the factor \(1-q_{n,0,k}\to0\). If \(i\ne k\),
the \(i\)-deleted product retains that same factor, proving the other two
assertions in (5).

Coordinatewise debt monotonicity under each exact payoff root gives

\[
 d_i(\Sigma_n)
 \le \beta_{n,i}d_i(X_n).
\tag{8}
\]

Uniform boundedness and (5) prove the outsider limits in (6). The global
minimum then forces the owner bound.

The exact cap-anchored telescope is

\[
 d_i(\Sigma_n)=\Lambda_{n,i}+\alpha_n d_i(X_n).
\tag{9}
\]

Both terms are nonnegative. Equations (5), (6), and bounded tail debt prove
the outsider ledger limits. For \(k\), the transported tail term tends to
zero, so (6) gives the stated \(D_*/3\) floor after a finite shift. QED

## 3. A source-attached pre-inner cap-band cut

### Theorem 3.1

For every sufficiently large \(n\), there is a finite cut \(c_n\), an actual
one-player cap-band target

\[
 \widehat\Sigma_n
 =\Sigma_n[k\leftarrow\widehat s_{n,k}],
\tag{10}
\]

and a constant

\[
 \kappa=D_*/(8R)>0
\tag{11}
\]

such that

\[
 U_k(\widehat\Sigma_n)-U_k(\Sigma_n)\ge D_*/4,
\qquad
 d_k(\widehat\Sigma_n)\le D_*/4,
\tag{12}
\]

\[
 \Pr_{\Sigma_n}(\text{jointly survive through }c_n)\ge\kappa,
\tag{13}
\]

and the source stopping law of \(k\) has cap-band bad mass at least
\(\kappa\). Every prescribed live root before \(c_n\) is literally
unchanged.

If \(m_n=|W_n|\) is the boundary between the exact word and \(X_n\), then

\[
 c_n<m_n
\tag{14}
\]

eventually. In addition, the complete \(k\)-deleted survival of the target
and source through the inner boundary agrees exactly:

\[
 \beta_{n,k}(\widehat\Sigma_n;m_n)
 =\beta_{n,k}(\Sigma_n;m_n)\ge\eta.
\tag{15}
\]

### Proof

Apply the checked cap-band finite-cut construction at the actual source
\(\Sigma_n\), mover \(k\), and band width \(e=D_*/4\). Equation (6) gives
source debt at least \(D_*/2\), so the target gains at least \(D_*/4\) and
has remaining owner debt at most \(D_*/4\).

The checked cap-band inequalities bound both source bad mass and joint reach
through the cut below by

\[
 \frac{d_k(\Sigma_n)-e}{2R}\ge\frac{D_*}{8R}=\kappa.
\]

If \(c_n\ge m_n\) along a subsequence, survival monotonicity would make the
left side of (13) at most \(\alpha_n\to0\), a contradiction. This proves
(14). Finally, a \(k\)-deleted survival probability depends only on the
other three players. The update (10) changes only \(k\), so (15) is exact.
QED

## 4. What is and is not consumed

The theorem eliminates the nonhost-payer output of the generic cap-band
dispatch for this persistent unique-sure word. It also gives a literal
chronological position: the paid modification starts at a uniformly reached
cut before the original tail boundary, and therefore no later than the
near-sure inner root, rather than at an unrelated source. The endpoint case
\(c_n=m_n-1\) is not excluded.

It does not preserve actual joint reach to the inner root. The target may put
new host Quit mass at or immediately after \(c_n\), while (15) deletes that
very player before measuring reach. Nor does literal equality of the
prescribed roots before \(c_n\) preserve their Nash property: their
continuation payoff has changed after the cut. Therefore the target is an
actual paid sibling with retained deleted-clock ancestry, not an exact
prefix descendant or a renewable source.

This is exactly the surviving host-payer port, now with the adverse
host-mismatch branch removed. A consumer still needs either positive actual
joint reach after the cap-band update or a backward compiler from the
host-deleted packet.

## Sources inspected

- notes/CODEX_BLINDSPOT__CAP_LIVE_BOUNDARY_LEDGER_AND_HOST_ROTATION.md;
- notes/CODEX_BLINDSPOT__FIXED_LEDGER_PAYER_PREMARK_CAP_BAND_WITNESS.md;
- notes/CODEX_SPINOZA__CAPACITY_GAP_ROOT_MATCHING_OR_PERSISTENT_INNER_MARK.md;
- notes/CODEX_SPINOZA__PERSISTENT_INNER_MARK_DELAYED_PAID_SOURCE_OR_SURE_HANDOFF.md;
- notes/CODEX_SPINOZA__UNIQUE_SURE_INNER_ROOT_ACTUAL_APPROXIMATE_CAP_HANDOFF.md;
- UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean;
- UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/CapDebtBellmanReduction.lean;
  and
- UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/CapBandRedistribution.lean.

## Boundary and nonclaims

- The outer summability assumption is the literal diagonal product property
  of the maintained persistent word, not a claim about arbitrary separately
  chosen blocks.
- The host/payer equality is asymptotic and uses exact-root coordinatewise
  debt monotonicity plus the global positive minimum.
- The cap-band target preserves \(k\)-deleted reach, not ordinary joint
  reach, terminal-atom mass, or the postmark law.
- Root actions before the cut are equal as prescribed actions but are not
  asserted Nash against the changed continuation.
- No exact Nash--Bellman return, terminal approximate Nash profile,
  renewable rank, or uniform-equilibrium payoff is claimed.

## Next exact question

Can the source bad mass in the host's own stopping law and the preserved
host-deleted reach in (13)--(15) be coupled to give positive actual joint
reach after a modified cap-band update? The generic cap-band target may move
all bad mass to a receiver before the inner root, so a positive answer needs
a receiver selection compatible with the displayed inner boundary, not only
the present payoff band.
