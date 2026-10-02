# Nonempty-host moving-mark minimum chord and source regeneration

Author: SOCIAL_WEIGHT_REVIEW

## Status

Ordinary-mathematics proof, not yet Lean-checked. Two independent
validations of the scope repair are recorded in
[PAIRED_HULL_REVIEW's delta](../feedback/FIN4_RESET_RIGID_ESCAPE_PRODUCT_RESTART_AND_SUPPORT_CONTRACTION__BY_PAIRED_HULL_REVIEW.md#delta-review-the-singleton-host-mismatch-is-real-and-the-precise-repair-passes)
and
[CODEX_DESCENDANT's delta](../feedback/FIN4_RESET_RIGID_ESCAPE_PRODUCT_RESTART_AND_SUPPORT_CONTRACTION__BY_CODEX_DESCENDANT.md#delta-the-minimal-singleton-host-extension-is-valid).
The marked sure-quitter host need only be nonempty. In particular, the
theorem applies when the source row is a singleton and the mover joins it to
form a pair.

This is a producer-level trichotomy. It does not turn a behavioral
replacement into a Nash--Bellman edge and does not consume its paid or
off-minimum outputs.

## 1. Data

Let \(I=\operatorname{Fin}4\), and let

\[
r:\{S\subseteq I:S\ne\varnothing\}\longrightarrow\mathbb R^I
\]

be a quitting reward table with \(\lvert r_i(S)\rvert\le M\), where \(M>0\).
For a behavioral profile \(\sigma\), write

\[
U_i(\sigma),\qquad
B_i(\sigma)=\sup_{\tau_i}U_i(\tau_i,\sigma_{-i}),
\]

\[
d_i(\sigma)=B_i(\sigma)-U_i(\sigma),
\qquad D(\sigma)=\sum_{i\in I}d_i(\sigma).
\]

The cap ranges over every behavioral replacement, including Never and
arbitrarily late randomized stopping.

Fix a supplied FinFourMinimumAtomProducer with hard residual, positive
global minimum \(D_*>0\), minimum joint semantic/law point \(x\), and source
chronology. Supply in addition:

* a fixed nonempty coalition \(K\subseteq I\);
* a fixed mover \(q\notin K\), with \(K'=K\cup\{q\}\);
* actual behavioral profiles \(X_n\) and dates \(t_n\);
* convergence of the complete semantic/law packet of \(X_n\) to \(x\);
* at date \(t_n\), conditional on reach, the pure product row \(K\);
* unconditional row reach
  \[
  L_n:=\Pr_{X_n}(\text{reach }t_n)\ge\lambda>0;
  \]
* a fixed positive joining gap
  \[
  \Delta:=r_q(K')-r_q(K)>0.
  \]

Let \(Y_n\) change only \(q\)'s action at \(t_n\) from Continue to Quit. It
retains the literal past, every other strategy, and the post-mark tail. Put

\[
R_n:=d_q(Y_n),\qquad e_n:=D(Y_n)-D_*.
\]

For fixed \(s\in(0,1)\), let \(H_n^s\) change only that action to the
\(s\)-mixture toward Quit.

## 2. The nonempty-host trichotomy

After strict common subsequence selection, one of the following holds.

### A. Positive residual

There is \(\rho>0\) such that \(R_n\ge\rho\). Against the literal opponents
of \(Y_n\), player \(q\) has a source-supported pure-time
first-disagreement row strictly before \(t_n\), with realized gain at least
\(\rho/4\). The standard reach bounds hold:

\[
\rho\le4M\,\operatorname{OwnSurvival},\qquad
\rho\le8M\,\operatorname{OppReach},
\]

\[
\rho^2\le32M^2\,\operatorname{JointReach}.
\tag{1}
\]

### B. Quantitative off-minimum endpoint

\[
R_n\longrightarrow0,\qquad e_n\ge\eta>0,
\]

and the literal update has exact gain

\[
U_q(Y_n)-U_q(X_n)=L_n\Delta\ge\lambda\Delta.
\tag{2}
\]

This is actual off-minimum response ancestry. Calling it a public paid
cap-port additionally requires the existing actual-reach paid-row selection
at \(Y_n\); that selected row may have a different observer.

### C. Minimum chord with strict support drop

\[
R_n\longrightarrow0,\qquad e_n\longrightarrow0.
\]

After one joint compactification,

\[
X_n\longrightarrow x,\qquad
Y_n\longrightarrow y,\qquad
H_n^s\longrightarrow h^s,\qquad
L_n\longrightarrow L\ge\lambda,
\]

where

\[
D(y)=D(h^s)=D_*.
\]

For every player \(i\),

\[
d_i(h^s)=(1-s)d_i(x)+s d_i(y).
\tag{3}
\]

For the mover,

\[
d_q(y)=0,\qquad
d_q(x)=L\Delta,\qquad
d_q(h^s)=(1-s)L\Delta>0.
\tag{4}
\]

Consequently

\[
\varnothing\ne\operatorname{supp}^{+}(y)
\subsetneq\operatorname{supp}^{+}(h^s),
\qquad |\operatorname{supp}^{+}(y)|\le3.
\tag{5}
\]

The limiting laws retain the marked-row identities

\[
\operatorname{Law}(y)
=\operatorname{Law}(x)+L(\delta_{K'}-\delta_K),
\]

\[
\operatorname{Law}(h^s)
=\operatorname{Law}(x)+sL(\delta_{K'}-\delta_K).
\tag{6}
\]

Both \(h^s\) and \(y\) regenerate complete same-residual minimum sources. A
paired wrapper retains the actual copied-prefix response family between
them. The target source enters the renewable tangent trace with a strict
positive-debt-support drop.

## 3. Endpoint, debt, and law identities

The profiles agree before \(t_n\). On reach, at least one member of the
nonempty host \(K\) Quits surely under both actions of \(q\). Hence the game
ends at the mark, in \(K\) for \(X_n\) and in \(K'\) for \(Y_n\). Therefore

\[
U_q(Y_n)-U_q(X_n)=L_n\Delta.
\tag{7}
\]

The opponents of \(q\) are unchanged, so \(B_q(Y_n)=B_q(X_n)\), and

\[
d_q(X_n)=L_n\Delta+R_n,\qquad d_q(Y_n)=R_n.
\tag{8}
\]

The same coupling moves exactly the unconditional mass \(L_n\) from \(K\)
to \(K'\):

\[
\operatorname{Law}(Y_n)
=\operatorname{Law}(X_n)+L_n(\delta_{K'}-\delta_K),
\tag{9}
\]

\[
\operatorname{Law}(H_n^s)
=\operatorname{Law}(X_n)+sL_n(\delta_{K'}-\delta_K).
\tag{10}
\]

Earlier absorption and Never mass are unchanged. Only \(K\ne\varnothing\),
not \(|K|=2\), is used.

## 4. Positive residual is strictly pre-mark

Suppose \(R_n\ge\rho>0\). Apply
positiveDebt_exists_actualJointReach_paidRow_mem_support to \(Y_n\), observer
\(q\), and debt floor \(\rho\). It supplies a source stopping time in the
support of \(Y_{n,q}\), a receiving stopping time, a first-disagreement row
with gain at least \(\rho/4\), and (1).

Conditional on reaching \(t_n\), the actual strategy of \(q\) in \(Y_n\)
Quits surely. A pure stopping time in its induced stopping-law support
therefore either stops earlier or stops at \(t_n\); it cannot survive past
\(t_n\) with positive source mass. If the supported source clock equals
\(t_n\), its conditional payoff is \(r_q(K')\). Every later finite clock and
Never is screened by the sure quitter in \(K\) and receives \(r_q(K)\),
which is strictly smaller. Thus no positive improvement can first disagree
at or after \(t_n\). The paid row is strictly pre-mark.

A singleton host has exactly the required sure-quitting opponent of \(q\).

## 5. The minimum squeeze

If \(R_n\) has no positive-liminf subsequence, pass to one with \(R_n\to0\).
Since \(Y_n\) is an actual carrier profile, \(e_n\ge0\). Pass again so either
\(e_n\ge\eta>0\), giving B by (7), or \(e_n\to0\).

In the latter arm jointly compactify

\[
(\operatorname{SemLaw}(Y_n),
 \operatorname{SemLaw}(H_n^s),L_n).
\]

Closedness gives carrier points \(y,h^s\), and \(D(y)=D_*\).

For \(i\ne q\), each fixed complete response payoff is affine in \(s\);
taking the supremum makes \(B_i\) convex. For \(i=q\), the cap is constant.
Prescribed payoffs are affine. Hence

\[
d_i(H_n^s)
\le(1-s)d_i(X_n)+s d_i(Y_n).
\tag{11}
\]

Summing and using global minimality,

\[
D_*\le D(H_n^s)
\le(1-s)D(X_n)+sD(Y_n)\longrightarrow D_*.
\tag{12}
\]

Thus \(D(h^s)=D_*\). In the limit, every coordinate slack in (11) is
nonnegative and their sum is zero, so each slack vanishes. This proves (3).
Equations (8) and (10) prove (4) and (6).

For \(0<s<1\), (3) implies

\[
\operatorname{supp}^{+}(h^s)
=\operatorname{supp}^{+}(x)\cup\operatorname{supp}^{+}(y).
\]

The mover belongs to the first support by (4) and not to the second. Since
\(D(y)=D_*>0\), the child support is nonempty, proving (5).

## 6. Copied prefix and unrestricted caps

The law of \(H_n^s\) has \(K'\)-mass \(sL_n\ge s\lambda\) at the moving
date. Apply supplied-family source-faithful minimum causalization to
\((H_n^s,t_n,K')\). Let \(W_n\) be the selected nonempty exact cap--Nash
word, and put

\[
A_n=W_n\star H_n^s,\qquad P_n=W_n\star Y_n.
\tag{13}
\]

Let \(c_n\) be joint survival through \(W_n\), and \(H_{i,n}\) survival of
all opponents of \(i\). Causalization gives

\[
c_n\longrightarrow1,\qquad H_{i,n}\longrightarrow1.
\tag{14}
\]

For every nonempty prescribed word \(W\), behavioral tail \(T\), and player
\(i\),

\[
\left|B_i(W\star T)
-\max\{r_i(\{i\}),B_i(T)\}\right|
\le2M(1-H_i(W)).
\tag{15}
\]

Pure stopping times, including Never, suffice for the cap. A pure time
either Quits inside \(W\), coupling on opponent survival to singleton
cash-out, or Continues through \(W\), coupling to the corresponding tail
pure time. The outcomes differ only on opponent absorption inside \(W\).
Immediate Quit and a shifted \(\varepsilon\)-optimal tail time give the
reverse estimate before \(\varepsilon\downarrow0\).

At the two positive minimum limits, the singleton moat gives

\[
B_i-r_i(\{i\})\ge D_*>0.
\]

Thus the maximum in (15) selects the tail cap asymptotically. With (14), the
payoff/law couplings give

\[
\operatorname{SemLaw}(A_n)\longrightarrow h^s,\qquad
\operatorname{SemLaw}(P_n)\longrightarrow y.
\tag{16}
\]

The common word is copied literally, and only \(q\)'s suffix changes:
\(A_n\to P_n\) is a complete one-player replacement. Exactly,

\[
U_q(P_n)-U_q(A_n)=c_n(1-s)L_n\Delta.
\tag{17}
\]

Their opponents for \(q\) are identical, so their caps agree. Exact
cap--Nash debt scaling on the source side gives

\[
d_q(A_n)=c_n\bigl((1-s)L_n\Delta+R_n\bigr).
\]

Subtracting (17) yields

\[
B_q(P_n)=B_q(A_n),\qquad d_q(P_n)=c_nR_n\longrightarrow0.
\tag{18}
\]

At the shifted mark \(|W_n|+t_n\), \(P_n\) has exact \(K'\)-mass \(c_nL_n\),
eventually at least \(\lambda/2\). Tail-reindex once and causalize this
literal target family at its shifted marks. Copying the incoming hard
residual gives complete minimum sources at \(h^s\) and \(y\). A paired
wrapper stores both causalizations, the families \(A_n,P_n\), their literal
replacement, (16)--(18), and the shifted marked mass. The standard producer
itself is not claimed to contain the incoming edge.

## 7. Rank and scope

The child at \(y\) has nonempty support of size at most three. Attach the
existing renewable minimum tangent trace there. With

\[
\rho(\mathsf{exit})=0,\qquad
\rho(\mathsf{tangent}(z))=1+|\operatorname{supp}^{+}(z)|,\qquad
\rho(\mathsf{origin})=5,
\]

entry, recursive support descent, and exit strictly lower the rank. No
constructor returns to the one-use origin phase. This is a producer rank,
not a chronology and not a rank on arbitrary outer-atlas returns.

## 8. Boundary tests

1. If \(K=\varnothing\), a later clock is not screened at \(t_n\); the
   strict-earlier proof fails. Nonemptiness is exact.
2. If \(q\in K\), the move is a leave rather than a join and the signs and law
   displacement change.
3. If \(L_n\to0\), the gain and target atom can vanish.
4. If \(D_*=0\), the singleton moat is not strict and copied-prefix caps can
   converge to singleton cash-out rather than the tail cap.
5. If the copied word is empty, (15) need not hold with the displayed
   maximum. Causalization supplies nonempty words.
6. Arbitrary earlier absorption and arbitrary tails are allowed. They cancel
   in (7)--(10) because the host absorbs surely on the reached mark.

## 9. Source audit and novelty

The proof uses the same checked ingredients as
[the moving marked-pair packet](../formalized/FIN4_MOVING_MARKED_PAIR_MINIMUM_CHORD_SUPPORT_DESCENT.md):

* positiveDebt_exists_actualJointReach_paidRow_mem_support;
* quittingTerminalSemanticDebt_responseChord_le and
  QuittingMinimumResponseChordLaw;
* nonempty_sourceFaithfulMinimumCausalization;
* minimumTerminalSemantic_singletonMargin; and
* the renewable minimum-source tangent rank.

The packet version reviewed here assumed \(|K|=2\), and its strict-earlier
dependency also stated a pure pair. The checked implementation now proves that
every step uses only \(K\ne\varnothing\), including source-supported
strict-earlier residual localization. This is the singleton-host adapter
needed by the reset-rigid positive-Never release.

## 10. Nonclaims

* No source constructs the moving nonempty-host contract from a bare minimum
  producer.
* The behavioral response edge is not a Nash--Bellman temporal edge.
* The paid and off-minimum arms remain at the universal paid-port waist.
* No uniform-equilibrium payoff or counterexample is produced.
