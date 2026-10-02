# Jensen normalization and a full-debt local-closure boundary

**Identity:** `SOCIAL_WEIGHT_REVIEW`  
**Status:** ordinary mathematics; exact finite table checked by exhaustive
coalition enumeration; no Fin4 consumer is claimed.

## 1. Question

Two possible splices were tested.

1. Does the Jensen clock decomposition, followed by a coherent exact
   cap--Nash prefix ray, already consume the positive-curvature branch?
2. Can the conjunction of full debt, unique all-Continue cap geometry,
   punishment normality, positive escaped social reward, and actually reached
   profitable forks be contradictory without using global minimality again?

The answer to both questions is no.  The Jensen calculation does give a
useful minimum-or-clock-escape normalization, but its second arm is the
already known fixed-tail strategic clock escape.  The table below shows that
all the listed local data, even with the numerical singleton moat at the
source's own debt level and fixed-law minimality, can coexist.

The result is a sharp no-go: a successful full-debt consumer must use the
comparison with *other terminal laws in the global carrier*.  It cannot use
only the local cap, its exact-root correspondence, the retained law, the
forks, or the social bubble.

## 2. Audit of the Jensen response

Let the notation be that of `questions/FIN4_JENSEN_CLOCK_SELECTION_AND_CAP_LEAKAGE.md`.

### 2.1 Vanishing loss

The clock selection is correct.  If

\[
 e_{n,t}=D(P_{n,t})-D_*\geq0,
 \qquad
 \varepsilon_n=\sum_t\alpha_n(t)e_{n,t}\to0,
\]

and

\[
 \sum_t\alpha_n(t)m_{n,t}\geq\mu,
\]

then for every \(0<\lambda<\mu\), the set

\[
 A_n=\{t:m_{n,t}\geq\lambda\}
\]

has

\[
 \alpha_n(A_n)\geq {\mu-\lambda\over1-\lambda}.
\]

Therefore some supported \(t_n\in A_n\) obeys

\[
 D(P_{n,t_n})-D_*
 \leq {1-\lambda\over\mu-\lambda}\,\varepsilon_n.
\]

This selects a minimum-carrying pure clock, but it does not control the debt
of the literal post-row tail.  Once a pure pair is installed, that tail is
screened from every unilateral deviation.  Thus minimum debt of the displayed
pair profile does not imply minimum debt of its counterfactual tail.

### 2.2 Exact leakage identity

Suppose \(S_n\) and \(R_n\) differ only in player \(i\)'s complete strategy,
and write

\[
 h_n=U_i(R_n)-U_i(S_n).
\]

Then \(B_i(R_n)=B_i(S_n)\), so

\[
 d_i(R_n)-d_i(S_n)=-h_n.
\]

For a second distinguished player \(o\), put

\[
 K=I\setminus\{o,i\}.
\]

Direct summation gives the exact identity

\[
 \sum_{j\in K}\bigl(d_j(R_n)-d_j(S_n)\bigr)
 =D(R_n)-D(S_n)+h_n+d_o(S_n)-d_o(R_n).
 \tag{2.1}
\]

In particular, if \(D(S_n)\to D_*\), \(d_o(R_n)\to0\), and
\(h_n\geq h>0\), global minimality gives

\[
 \liminf_n\sum_{j\in K}
 \bigl(d_j(R_n)-d_j(S_n)\bigr)\geq h.
\]

This is a lower leakage account, not the upper account needed to put the
receiving endpoint on the minimum fibre.

### 2.3 Coherent prefix normalization

For a receiving endpoint \(R_n\), let \(R_{n,k}\) be a coherent fixed-tail
exact cap--Nash prefix ray and let \(q_{n,k}\) be its joint survival product.
Then

\[
 d_j(R_{n,k})=q_{n,k}d_j(R_n),
 \qquad
 D(R_{n,k})=q_{n,k}D(R_n).
 \tag{2.2}
\]

If \(D(R_n)\leq8M\), global minimality gives

\[
 q_{n,k}\geq {D_*\over D(R_n)}\geq {D_*\over8M}.
 \tag{2.3}
\]

Consequently every fixed tail atom and every payoff difference between two
siblings carrying the same prefix word are multiplied by the same
\(q_{n,k}\) and retain the stated positive floors.  If both \(d_o(R_n)\to0\)
and \(d_i(R_n)\to0\), a diagonal whose total debt tends to \(D_*\) indeed
has two zero-debt coordinates in the limit.

The alternative in which the ray stays uniformly above \(D_*\) is not new:
it is the fixed-tail exact-prefix clock escape of
`formalized/POSITIVE_MINIMUM_EXACT_PREFIX_CLOCK_ESCAPE.md`, now carrying the
selected atom and sibling gain.  That export explicitly has no clock-escape
consumer.  Thus the Jensen response is a valid reduction, not a solution of
the positive-curvature branch.

## 3. A rational Fin4 regression

Let \(I=\{0,1,2,3\}\) and put \(A=\{0,1\}\).  Rewards not singled out below
are defined by the final catch-all clause in each coordinate.

For player \(0\), set

\[
 r_0(S)=
 \begin{cases}
 -1,&S=A,\\
 -4,&S=\{3\},\\
 -5,&S=\{0,3\},\\
 -4,&0\in S,\\
 0,&0\notin S.
 \end{cases}
 \tag{3.1}
\]

For player \(1\), use the symmetric definition

\[
 r_1(S)=
 \begin{cases}
 -1,&S=A,\\
 -4,&S=\{3\},\\
 -5,&S=\{1,3\},\\
 -4,&1\in S,\\
 0,&1\notin S.
 \end{cases}
 \tag{3.2}
\]

For player \(3\), set

\[
 r_3(S)=
 \begin{cases}
 -1,&S=A,\\
 0,&S=A\cup\{3\},\\
 -4,&S=\{2\},\\
 -5,&S=\{2,3\},\\
 -4,&3\in S,\\
 0,&3\notin S.
 \end{cases}
 \tag{3.3}
\]

For player \(2\), set

\[
 r_2(S)=
 \begin{cases}
 4,&S=A,\\
 5,&S=A\cup\{2\},\\
 1,&S=\{3\},\\
 -1,&S=\{0,2\},\\
 0,&\text{otherwise}.
 \end{cases}
 \tag{3.4}
\]

For every \(n\geq1\), let \(\sigma_n\) make players \(0,1\) Quit surely at
date \(n\), while players \(2,3\) play Never.

### Proposition 3.1 (full local packet)

The family \(\sigma_n\) has all of the following properties.

1. Its terminal law is \(\delta_A\), and

   \[
   U=(-1,-1,4,-1),
   \qquad
   B=(0,0,5,0).
   \tag{3.5}
   \]

2. Every debt is one:

   \[
   d=(1,1,1,1),
   \qquad D=4.
   \tag{3.6}
   \]

3. With singleton vector

   \[
   s=(-4,-4,0,-4),
   \]

   the full singleton-moat inequalities at level \(D=4\) hold:

   \[
   B_i-s_i\geq4\qquad(i=0,1,2,3).
   \tag{3.7}
   \]

   The complementary prescribed-payoff form also holds:

   \[
   U_i-s_i\geq D-d_i=3.
   \tag{3.8}
   \]

4. Every player is punishment normal.  Opponents can force the following
   immediate coalitions:

   \[
   \begin{array}{c|c|c}
   i&\text{forced opponent coalition}&
   (\text{Continue payoff},\text{Quit payoff})\\ \hline
   0&\{3\}&(-4,-5)\\
   1&\{3\}&(-4,-5)\\
   2&\{0\}&(0,-1)\\
   3&\{2\}&(-4,-5).
   \end{array}
   \tag{3.9}
   \]

   Hence each punishment value is at most the corresponding singleton reward.

5. All Continue is the unique exact product root against \(B\).

6. At the common reached date \(n\), every player has a full-reach legal
   complete best-response fork of gain one, and the fork kills that player's
   debt exactly.

7. The weak compactified marginal-law limit is all Never, whereas the
   time-forgetting terminal law remains \(\delta_A\).  The escaped coalition
   has strictly positive social reward

   \[
   \sum_i r_i(A)=1.
   \tag{3.10}
   \]

8. Among actual profiles whose terminal law is exactly \(\delta_A\), the
   semantic pair (3.5) is forced.  Thus it is a genuine fixed-law minimum,
   not merely one arbitrary realization of that law.

9. Nevertheless the all-Never profile has \(U=B=0\).  The table's global
   minimum is zero and the game has an exact equilibrium.

### Proof

Against \(\sigma_n\), players \(0,1\) obtain zero by continuing through the
marked date and letting the other owner Quit alone.  Player \(2\) obtains
five by joining \(A\), and player \(3\) obtains zero by joining \(A\).
No coordinate reward exceeds the displayed cap, proving (3.5)--(3.6).
Equations (3.7)--(3.8) are direct substitution, and (3.9) proves punishment
normality.

For root uniqueness, compare Quit minus Continue pointwise in the opponents'
coalition.  For player \(0\) the values, indexed by
\(C\subseteq\{1,2,3\}\), are

\[
 -4,-1,-4,-1,-4,-4,-4,-4,
\]

and player \(1\) is symmetric.  Hence both strictly Continue against every
root.  Once they Continue, player \(3\)'s two comparisons, according as
player \(2\) Continues or Quits, are \(-4\) and \(-1\); hence player \(3\)
strictly Continues.  Player \(2\) then compares singleton Quit payoff zero
with cap continuation payoff five.  Thus every exact root is all Continue.

The four best responses at date \(n\) are: players \(0,1\) leave the pair by
Continuing, while players \(2,3\) join it by Quitting.  Their respective
payoff changes are

\[
 -1\to0,quad -1\to0,quad 4\to5,quad -1\to0.
\]

All four strategies agree with the source before date \(n\), and the source
reaches that date with probability one.

For the fixed-law claim, independence and terminal law \(\delta_A\) imply
that the stopping times of players \(0,1\) are equal and finite almost
surely.  Two independent random variables which are equal almost surely are
the same deterministic time.  The other two players stop strictly later.
Each player can therefore perform the same leave/join response at that
deterministic time.  Coordinatewise reward maxima give the reverse cap
bounds, so (3.5) is forced.

Finally \(\delta_n\) converges weakly to Never for players \(0,1\), while
players \(2,3\) already play Never.  The reconstructed limit is all Never.
Every singleton reward is nonpositive, so no player can gain from all Never;
it is an exact zero-debt profile.

## 4. Consequences for the live Fin4 routes

The regression simultaneously blocks each of the following local-only
implications:

```text
full debt + singleton moat + punishment normality
  -> non-all-Continue exact cap root;

full debt + four full-reach debt-killing forks
  -> lower total debt or a chronological charged return;

positive escaped social reward + paid forks
  -> cap-compatible absorption;

fixed-law minimum + unique all-Continue cap
  -> positive global minimum or terminal obstruction.
```

It also explains why the nonnegative-costate chamber does not consume the
positive-social escape branch.  At the displayed source the one supported
finite outcome has

\[
 r(A)-s=(3,3,4,3)>0,
\]

so every nonzero nonnegative costate sees positive surplus on \(A\).  The
table lies on the sparse reward boundary, not in a closing costate chamber.

The one hypothesis deliberately absent is the real global comparison

\[
 D(x)=D_*>0.
\]

Here the same-law face has value four but another terminal law has value
zero.  Therefore a decisive consumer must turn one of the source-attached
forks, the bubble, or the cap switch into a comparison with a genuinely
different law/source while controlling all four unrestricted caps.  This is
exactly the unresolved target-side rebase.  No combination of the local
passports above can replace it.

## 5. Concrete next question

Can global minimality be used in a genuinely multi-fork way?  More precisely,
starting from one full-debt minimum source, choose one common-prefix complete
near-best-response fork for every player and form their actual stopping-law
reset cube.  Prove either:

1. one cube vertex has total debt below the source;
2. a minimum-fibre vertex has strictly smaller positive-debt support with a
   renewable source compiler; or
3. a first-order cap square yields an ancestry-preserving pair-deleted
   chronological consumer.

The regression shows that replacing global minimality by the singleton moat,
fixed-law minimality, or punishment normality makes this statement false.
