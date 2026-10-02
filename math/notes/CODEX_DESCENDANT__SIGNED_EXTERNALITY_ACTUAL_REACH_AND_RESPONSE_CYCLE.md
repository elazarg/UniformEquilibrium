# Signed payoff externality as an actually reached row

Identity: `CODEX_DESCENDANT`  
Status: ordinary mathematics; source-faithful causal localization and exact
Fin4 local regression; no chamber consumer

## 1. Question

In the literal two-response reduction, failure of a support drop yields either
a cap rise or a prescribed-payoff fall for one recipient.  The latter was
recorded as a signed terminal-law label and therefore forgot its causal date.

Can the payoff fall itself be localized at an actually reached row of the
literal successor, without identifying aggregate law mass with current root
absorption?

The answer is yes.  The localization is stronger than the signed-label
statement and loses no factor for the number of terminal coalitions.  It is
still not an executable strategic edge: the player whose stopping law is
changed need not benefit from the recipient's payoff increase.

## 2. Role-swapped reward localization

Let `P` and `Q` be actual behavioral profiles which differ only in player
$q$'s complete stopping strategy.  Fix another player $h$.  Assume rewards
are bounded by $M>0$ and

\[
 U_h(P)-U_h(Q)\ge a>0.
 \tag{2.1}
\]

Define an auxiliary quitting reward table $\widetilde r$ on the same players
and coalitions by copying player $h$'s original payoff coordinate into player
$q$'s auxiliary coordinate:

\[
 \widetilde r_q(S)=r_h(S).
 \tag{2.2}
\]

The other auxiliary coordinates may be copied from the same bounded
coordinate, so the auxiliary reward bound is at most $M$.  The behavioral
profiles and every survival event are unchanged.  Since `P` and `Q` have the
same opponents for $q$,

\[
 \widetilde U_q(P)-\widetilde U_q(Q)
 =U_h(P)-U_h(Q)\ge a.
 \tag{2.3}
\]

The strategy of $q$ used in `P` is a legal unilateral response against the
opponents in `Q`.  Therefore the auxiliary continuation debt of $q$ at `Q`
satisfies

\[
 \widetilde d_q(Q)\ge a.
 \tag{2.4}
\]

Apply
`positiveDebt_exists_actualJointReach_paidFirstDisagreementRow` to the
auxiliary table, source profile `Q`, observer $q$, and any $0<\Delta\le a$.
It returns two pure stopping-time strategies of $q$ and their literal first
disagreement row $t$ such that

\[
 \widetilde U_q(Q[q\leftarrow\tau^{\rm rec}])
 -\widetilde U_q(Q[q\leftarrow\tau^{\rm src}])
 \ge {\Delta\over4},
 \tag{2.5}
\]

and

\[
 \Pr_Q(\text{all players survive to }t)
 \ge {\Delta^2\over32M^2}.
 \tag{2.6}
\]

Returning to the original reward table, (2.5) is exactly

\[
 U_h(Q[q\leftarrow\tau^{\rm rec}])
 -U_h(Q[q\leftarrow\tau^{\rm src}])
 \ge {\Delta\over4}.
 \tag{2.7}
\]

Thus a unilateral payoff externality cannot remain only an aggregate
terminal-law displacement.  It has a source-attached, actually reached,
pure-time first-disagreement witness on the lower-payoff successor `Q`.
The source stopping-time witness is supported by $q$'s actual stopping law if
the support-strengthened version in `FableActualReachSupport.lean` is used.

Nothing in this argument says that (2.7) is profitable for $q$.  It is an
actual causal **externality row**, not an admissible deviation edge in the
original game.

## 3. Application to the two-response minimum branch

Use the notation of
`CODEX_DESCENDANT__TWO_BLOCK_FULL_DEBT_FORK_SEAM.md`.  In its prescribed-
payoff alternative,

\[
 U_h(x^1)-U_h(x^2)\ge D_*/18,
 \tag{3.1}
\]

where the actual profile families $X_n^1$ and $X_n^2$ differ only in the
second mover $q$.  For all sufficiently large $n$,

\[
 U_h(X_n^1)-U_h(X_n^2)\ge D_*/20.
 \tag{3.2}
\]

Taking $\Delta=D_*/20$ in Section 2 gives, on the literal successor
$X_n^2$, an externality row controlled by $q$ with

\[
 \text{recipient-payoff gain}\ge D_*/80,
 \qquad
 \text{joint reach}\ge {D_*^2\over12800M^2}.
 \tag{3.3}
\]

The same conservative-transfer choice gave

\[
 d_h(x^2)\ge d_h(x^1)+D_*/9\ge D_*/9.
 \tag{3.4}
\]

Hence, for sufficiently large $n$, applying the original payoff theorem to
observer $h$ at the **same** source profile $X_n^2$, with
$\Delta=D_*/10$, also gives a genuinely profitable $h$-row with

\[
 \text{$h$-gain}\ge D_*/40,
 \qquad
 \text{joint reach}\ge {D_*^2\over3200M^2}.
 \tag{3.5}
\]

The payoff-fall arm is therefore a co-realized two-row port on one literal
source:

* a $q$-controlled row which restores a fixed amount of $h$'s payoff; and
* an $h$-controlled row which gives $h$ a fixed profitable deviation.

Their dates may be ordered after selection, but neither row is an exact
cap--Nash root and the two replacements need not preserve each other's gain.
No near-minimum suffix or exact Bellman connector between the dates follows.

## 4. Exact Fin4 regression

The preceding port is compatible with an exact literal response cycle and a
unique all-Continue cap root.  Let the players be

\[
 q=0,\qquad h=1,\qquad k=2,\qquad \ell=3.
\]

All rewards below lie in $[0,1]$.

For player $k$, make Continue strictly dominant at every root:

\[
 r_k(S)=
 \begin{cases}
  1,&k\notin S,\\
  0,&k\in S.
 \end{cases}
 \tag{4.1}
\]

When $k\notin S$, use the same Continue-dominant rule for players $h$ and
$\ell$.  On the four coalitions of the square containing $k$, put

\[
\begin{array}{c|cccc}
S&\{k\}&\{q,k\}&\{q,h,k\}&\{h,k\}\\ \hline
r_q(S)&0&1&0&1\\
r_h(S)&1&0&1&0\\
r_\ell(S)&0&0&0&0.
\end{array}
\tag{4.2}
\]

Also put

\[
 r_\ell(\{k,\ell\})=r_\ell(\{q,k,\ell\})
 =r_\ell(\{q,h,k,\ell\})=r_\ell(\{h,k,\ell\})=1.
 \tag{4.3}
\]

Unlisted rewards on coalitions containing $k$ may be set to zero.  For player
$q$ on coalitions not containing $k$, set the singleton reward to zero and
choose values in $[0,1]$ so that, after $h$ and $\ell$ Continue, Continue
against the displayed cap one is strictly better than Quit.  For example all
such $q$-rewards may be zero except
$r_q(\{h,k\})=1$, already fixed in (4.2).

Use date zero for the displayed pure coalition.  Behind the counterfactual
all-Continue outcome attach one common tail in which $q$ quits surely at the
next date.  Consider the four literal profiles with date-zero coalitions

\[
 \{k\}\longrightarrow\{q,k\}
 \longrightarrow\{q,h,k\}
 \longrightarrow\{h,k\}
 \longrightarrow\{k\}.
 \tag{4.4}
\]

Every displayed cap vector is $(1,1,1,1)$.  Player $k$ gets cap one by
Continuing to the common tail or to the other displayed quitter; player
$\ell$ gets cap one by joining; and the alternating player among $q,h$ gets
cap one by the strict membership toggle in (4.2).  The debt vectors are

\[
\begin{array}{c|c}
\text{coalition}&(d_q,d_h,d_k,d_\ell)\\ \hline
\{k\}&(1,0,1,1)\\
\{q,k\}&(0,1,1,1)\\
\{q,h,k\}&(1,0,1,1)\\
\{h,k\}&(0,1,1,1).
\end{array}
\tag{4.5}
\]

Each arrow is a literal one-player exact best response of gain one, and the
unique zero-debt coordinate rotates.  Each arrow also lowers the other
alternating player's prescribed payoff by one, so the role-swapped
externality port of Section 2 is present at full scale.

Against cap $(1,1,1,1)$, all Continue is the unique exact product root.
Indeed, player $k$ first strictly Continues at every opponent root.  Conditional
on that, players $h$ and $\ell$ strictly Continue by the rule for coalitions
not containing $k$.  Player $q$ then strictly Continues against all other
players Continuing.  This sequential dominance argument excludes every
other product root.

The regression is not a counterexample.  At all Never, all singleton rewards
are zero, so prescribed payoffs and unrestricted caps are zero and the true
global minimum debt is zero.  It proves the narrower no-go:

\[
\begin{array}{c}
\text{literal target-to-next-source response chain}
+\text{ fixed actual-reach payoff and externality rows}\\
+\text{ unique all-Continue cap root}
\end{array}
\not\Rightarrow
\text{a chronological return or zero-support descent}
\tag{4.6}
\]

without positive-global-minimum provenance.

## 5. Exact remaining bridge

The signed terminal-law alternative is no longer merely time-forgetting.
It supplies two uniformly reached first-disagreement rows on one literal
successor.  What remains absent is a compatibility theorem which either

1. preserves one row's gain after executing the other replacement;
2. exactifies the common pre-row source without losing the externality; or
3. uses positive-global-minimum provenance to exclude the response cycle
   (4.4).

The first option is a source-matched response-curl consumer, the second is the
pre-seam root/tail-fibre problem, and the third is precisely where the local
regression has $D_*=0$.  The present theorem produces no exact root block,
charged near-return, renewable rank, or terminal approximation.

## 6. Source audit

The actual-reach input is
`positiveDebt_exists_actualJointReach_paidFirstDisagreementRow` in
`fable/lean/FableDebtActualReach.lean`; the source-support strengthening is
`positiveDebt_exists_actualJointReach_paidRow_withSupport` in
`fable/lean/FableActualReachSupport.lean`.  The proof uses only that behavioral
profiles and survival prefixes depend on the quitting actions, not on the
payoff coordinate used to evaluate their terminal outcomes.

The cap-versus-payoff split and literal target-to-next-source response chain
are in
`CODEX_DESCENDANT__TWO_BLOCK_FULL_DEBT_FORK_SEAM.md`.  The common-response
full-chord and curl machinery was inspected to ensure that no existing
declaration consumes the two rows merely from their separate gains.
