# Vanishing live-word hazard reprojects the paid edge to the literal source tail

Author: CODEX_HAHN

## Status

**Exact ordinary mathematics; not Lean-checked and not yet a terminal
consumer.**  In the unique-sure live cap-band construction, the
vanishing-hazard arm does more than identify the target with its actual tail.
It transports the fixed owner gain to a literal unilateral replacement
between the old source tail and the new target tail.

Thus the residual in this arm is not a missing source-component equality.
There is an actual source-attached paid tail edge
\[
 X_n\ \dashrightarrow_k\ Z_n
\]
with fixed gain, target owner debt tending to zero, and the original exact
word as literal ancestry.  What is not proved is that \(X_n\) regenerates the
special unique-sure stationary source or that the paid tail edge returns.

## 1. Self-contained input

Let \(I=\operatorname{Fin}4\), let \(R>0\), let \(D_*>0\), and assume every
reward coordinate lies in \([-R,R]\).  Write
\[
 s_k=r_k(\{k\})
\]
for player \(k\)'s singleton reward.

For every \(n\), let
\[
 \Sigma_n=W_n\triangleright X_n
\tag{1}
\]
be an actual source profile.  The word \(W_n\) has length \(m_n>0\), its last
root \(q_n\) is exact Nash against the literal payoff successor \(U(X_n)\),
and
\[
 q_{n,k}\longrightarrow1.
\tag{2}
\]

Let
\[
 Y_n=\Sigma_n[k\leftarrow\widehat s_{n,k}]
       =\widehat W_n\triangleright Z_n
\tag{3}
\]
be an actual unilateral owner replacement such that:

1. player \(k\) Continues surely at every row of \(\widehat W_n\);
2. every opponent root in \(\widehat W_n\) is the corresponding opponent
   root in \(W_n\);
3. the target-word total marginal hazard
   \[
    h_n=\sum_{t<m_n}\sum_i\widehat q_{n,t,i}
   \tag{4}
   \]
   tends to zero;
4. the source joint survival through \(W_n\), denoted \(\alpha_n\), tends to
   zero, while its \(k\)-deleted survival
   \[
    \beta_{n,k}=\Pr_{\Sigma_n}(T_{-k}\ge m_n)
   \tag{5}
   \]
   is at least one fixed \(\eta>0\); and
5. the owner replacement has gain and vanishing remaining owner debt
   \[
    U_k(Y_n)-U_k(\Sigma_n)\ge D_*/2-e_n,
    \qquad d_k(Y_n)\le e_n,
    \qquad e_n\longrightarrow0.
   \tag{6}
   \]

These are precisely the unique-sure persistent-word and vanishing-width
live-target fields.  Since (3) changes only player \(k\), its literal tails
satisfy
\[
 Z_{n,-k}=X_{n,-k}.
\tag{7}
\]
Hence \(Z_n\) is already a unilateral \(k\)-replacement of \(X_n\).

## 2. The source word pays the singleton reward asymptotically

Let
\[
 u_n=\Pr_{\Sigma_n}(T_k\ge m_n)
\]
be player \(k\)'s own survival through the source word.  Independence gives
\[
 \alpha_n=u_n\beta_{n,k},
\qquad
 u_n\le\alpha_n/\eta\longrightarrow0.
\tag{8}
\]

The opponents have the same word marginals in \(\Sigma_n\) and \(Y_n\), while
the target owner has zero hazard there.  Therefore the sum of all opponent
word hazards is exactly \(h_n\).  A union bound gives
\[
 \Pr(\text{some opponent Quits inside }W_n)\le h_n.
\tag{9}
\]

Except on the union of the events in (8)--(9), player \(k\) Quits inside the
source word and no opponent Quits before or with it.  The first quitting
coalition is then exactly \(\{k\}\).  Consequently
\[
 |U_k(\Sigma_n)-s_k|
 \le2R(u_n+h_n)\longrightarrow0.
\tag{10}
\]

No root Nash property is needed for this concentration statement.

## 3. Exact Nash at the inner root screens the old tail

At the last source root \(q_n\), player \(k\)'s Quit action has positive
probability eventually by (2).  Exact root Nash therefore gives
\[
 Q_k(q_n;U(X_n))\ge C_k(q_n;U(X_n)).
\tag{11}
\]

Let
\[
 \rho_n=\sum_{i\ne k}q_{n,i}.
\]
The opponent marginals at this row are unchanged in the target word, so
\(\rho_n\le h_n\to0\).  Forcing \(k\) to Quit yields the singleton reward
unless some opponent also Quits, while forcing \(k\) to Continue yields
\(U_k(X_n)\) unless some opponent Quits.  Coupling gives
\[
 |Q_k(q_n;U(X_n))-s_k|\le2R\rho_n,
\qquad
 |C_k(q_n;U(X_n))-U_k(X_n)|\le2R\rho_n.
\tag{12}
\]

Equations (11)--(12) imply
\[
 U_k(X_n)\le s_k+4R\rho_n
 \le s_k+4Rh_n.
\tag{13}
\]

This is the only place where exact Nash ancestry is used.

## 4. The target tail is a fixed-gain literal response to the source tail

Since the target word has absorption probability at most \(h_n\),
\[
 |U_k(Y_n)-U_k(Z_n)|\le2Rh_n.
\tag{14}
\]

Combining (6), (10), (13), and (14) gives
\[
\begin{aligned}
 U_k(Z_n)-U_k(X_n)
 &\ge D_*/2-e_n-2Ru_n-8Rh_n\\
 &\longrightarrow D_*/2.
\end{aligned}
\tag{15}
\]

In particular, eventually
\[
 \boxed{U_k(Z_n)-U_k(X_n)\ge D_*/4.}
\tag{16}
\]

By (7), this is the exact payoff gain of one complete unilateral behavioral
replacement at the actual source \(X_n\).  Therefore
\[
 d_k(X_n)\ge D_*/4.
\tag{17}
\]

Moreover, changing player \(k\)'s own strategy leaves its unrestricted cap
against the opponents unchanged.  Thus
\[
 d_k(Z_n)
 =d_k(X_n)-\bigl(U_k(Z_n)-U_k(X_n)\bigr).
\tag{18}
\]
Every complete owner deviation at \(Z_n\) lifts behind the target word with
the target joint-reach factor, which tends to one by (4).  Thus
\[
 \Pr_{Y_n}(T_I\ge m_n)d_k(Z_n)\le d_k(Y_n)\le e_n,
\]
and hence
\[
 d_k(Z_n)\longrightarrow0,
\tag{19}
\]
so the literal response \(X_n\dashrightarrow_k Z_n\) is asymptotically
cap-attaining.

## 5. Consequence for the vanishing-hazard residual

The full source and target are linked by the owner response
\[
 \Sigma_n\dashrightarrow_kY_n.
\]
The vanishing target word gives
\[
 \operatorname{SemLaw}(Y_n)-\operatorname{SemLaw}(Z_n)\longrightarrow0.
\]
The theorem above now adds the exact missing source-side statement:
\[
 \boxed{
 Z_n=X_n[k\leftarrow\zeta_{n,k}],
 \qquad
 U_k(Z_n)-U_k(X_n)\ge D_*/4,
 \qquad
 d_k(Z_n)\to0.}
\tag{20}
\]

Hence deleting the word does not leave merely a signed law coordinate.  It
leaves a complete source-attached, fixed-gain, nearly cap-attaining response
at the literal old tail.

This does not itself close the generic paid-port waist.  The source \(X_n\)
need not be a global minimum, a stationary tropical source, or a regenerated
unique-sure node.  The target \(Z_n\) need not return semantically to \(X_n\),
and replacing \(k\) in the tail does not revalidate the old word after it is
placed back above the tail.  The new conclusion is nevertheless stronger
than a source-to-tail signed law seam: the tail relation is an actual
unilateral edge with a fixed payer and fixed gain.

## Sources inspected

- notes/CODEX_SPINOZA__UNIQUE_SURE_PERSISTENT_WORD_HOST_PAYER_CAP_BAND.md;
- notes/CODEX_SPINOZA__EXACT_WORD_FORCES_LATE_CAP_BAND_RECEIVER_AND_LIVE_TARGET.md;
- notes/CODEX_SPINOZA__LIVE_CAP_TARGET_POSTTAIL_DISTINCT_DEBTOR.md;
- notes/CODEX_SPINOZA__LIVE_CAP_WORD_HAZARD_OR_FULL_SEMANTIC_TAIL_REPROJECTION.md;
- UniformEquilibrium/Quitting/Root/LiteralExactPrefixStack.lean; and
- UniformEquilibrium/Quitting/Root/LiteralPrefixDeviationTransport.lean.

## Boundary tests and nonclaims

- The positive \(k\)-deleted survival floor is needed to deduce
  \(u_n\to0\) from joint source survival \(\alpha_n\to0\).
- Vanishing target-word hazard is needed to concentrate the source law on
  the singleton \(\{k\}\) and to compare the inner root endpoints with
  \(s_k\) and \(U_k(X_n)\).
- Exact Nash at the last source root is essential.  Without (11), the
  off-path source tail payoff \(U_k(X_n)\) is arbitrary after a near-sure
  Quit root, and the full-profile gain need not descend to the tails.
- The conclusion is a horizontal behavioral response edge, not an exact
  Nash--Bellman root, a source return, a finite-rank decrease, a terminal
  approximate Nash profile, or a uniform-equilibrium payoff.
