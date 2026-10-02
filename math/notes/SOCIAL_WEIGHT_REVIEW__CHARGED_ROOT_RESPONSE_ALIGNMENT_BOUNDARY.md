# Charged-root and response-curl alignment boundary

Identity: `SOCIAL_WEIGHT_REVIEW`  
Date: 2026-08-31  
Status: **ordinary mathematics proved below; not Lean-checked.**  The positive
result combines two existing ledgers on one source sequence.  The regression
is an exact Fin4 quitting table but has global minimum zero.  No Fin4 chamber
is consumed.

## 1. Question

Let actual profiles `P_n,Y_n` differ only in player `p`'s complete strategy.
Assume `P_n` converges to the positive global debt minimum, the `p`-update has
fixed gain, and `p`'s target debt vanishes.  Suppose a maximal exact root at
the cap of `Y_n` has uniformly positive absorption.

Must the nonmover whose root defect detects the cap change be the same
nonmover whose debt rises across `P_n -> Y_n`?

Such an alignment would put the temporal root defect and the horizontal
response curl in one player coordinate.  Fin4 pigeonhole alone does not give
it.

## 2. What the full source does force

Assume, eventually,

\[
 U_p(Y_n)-U_p(P_n)\ge G>0,
 \qquad d_p(Y_n)\longrightarrow0,
 \qquad D(P_n)\longrightarrow D_*>0.
\tag{2.1}
\]

Own-cap invariance and global minimality give

\[
 \sum_{j\ne p}\bigl(d_j(Y_n)-d_j(P_n)\bigr)
 \ge G-o(1).
\tag{2.2}
\]

After a subsequence, one fixed recipient `j` satisfies

\[
 d_j(Y_n)-d_j(P_n)\ge G/4.
\tag{2.3}
\]

Selecting a pure time within `G/16` of `B_j(Y_n)` and installing the same
response on both backgrounds gives the fixed response-curl bound

\[
 \begin{aligned}
 &[U_j(Y_n[j\leftarrow a_n])-U_j(Y_n)]\\
 &\quad-[U_j(P_n[j\leftarrow a_n])-U_j(P_n)]
 \ge 3G/16.
 \end{aligned}
\tag{2.4}
\]

Independently, let `x_n` be exact at `B(Y_n)` and have absorption at least
`alpha>0`.  The arbitrary-root minimum budget and Lipschitz root-defect
estimate force, after another subsequence, one fixed nonmover `k` with

\[
 |B_k(Y_n)-B_k(P_n)|\ge \alpha D_*/6.
\tag{2.5}
\]

Thus a uniformly charged arm cannot consist only of affine cap translation:
the source simultaneously carries the non-affine rectangle (2.4).  But the
two finite selections produce `j` and `k` separately.  Nothing in their
scalar sums forces `j=k`, and a large cap displacement need not create root
defect in that coordinate.

## 3. Exact Fin4 misalignment regression

Let the players be

\[
 p=0,\qquad q=1,\qquad k=2,\qquad j=3.
\]

For every nonempty coalition `S`, define rewards by

\[
 r_0(S)=
 \begin{cases}
 1,&0\in S\text{ and }2\notin S,\\
 0,&\text{otherwise},
 \end{cases}
\tag{3.1}
\]

\[
 r_1(S)=0,
\tag{3.2}
\]

\[
 r_2(S)=
 \begin{cases}
 1,&S=\{1\},\\
 0,&\text{otherwise},
 \end{cases}
\tag{3.3}
\]

and

\[
 r_3(S)=
 \begin{cases}
 1,&S=\{0,3\},\\
 0,&\text{otherwise}.
 \end{cases}
\tag{3.4}
\]

Let `P` prescribe player `1` to Quit at date one and all other players to
Never Quit.  Let `Y` replace only player `0` by Quit at date zero.

At `P`, the terminal coalition is `{1}` and

\[
 U(P)=(0,0,1,0),\qquad B(P)=(1,0,1,0),
 \qquad d(P)=(1,0,0,0).
\tag{3.5}
\]

At `Y`, the terminal coalition is `{0}` and

\[
 U(Y)=(1,0,0,0),\qquad B(Y)=(1,0,0,1),
 \qquad d(Y)=(0,0,0,1).
\tag{3.6}
\]

Thus the `p`-response gains one and kills `p`'s debt, while the entire debt
is transferred to observer `j=3`.  Installing `j`'s Quit-at-zero response
gives response curl one.

Now prefix `Y` by the pure root whose quitting coalition is `{2}`.  It is an
exact root against `B(Y)`:

- player `2` compares `r_2({2})=0` with tail cap `B_2(Y)=0`;
- every outsider compares two zero rewards at the sure `{2}` absorption.

Its absorption is one, hence maximal.  Against `B(P)`, however, player `2`
strictly prefers Continue, because its continuation cap is one while
`r_2({2})=0`.  The root-defect observer is therefore `k=2`, not the debt-rise
and response-curl observer `j=3`.

The `k` cap and prescribed payoff both move from one to zero, so its debt is
unchanged.  Conversely `j` has cap/debt rise one but sees no defect at the
sure `{2}` root.  This realizes exact root/recipient misalignment in a
literal Fin4 game, not merely in an abstract vector ledger.

The regression has an exact equilibrium: the displayed exact sure-`{2}`
prefix of `Y` has zero debt.  Hence its global minimum is zero.  It does not
refute an alignment theorem using positive global-minimum provenance or the
full hard residual.  It proves that player finiteness, source matching,
fixed gain, exact debt transfer, and a maximal charged root do not by
themselves establish alignment.

## 4. Remaining exact alternatives

The charged arm now has both of the following on one source subsequence:

1. a temporal cap-root defect/cap displacement in a fixed coordinate `k`;
2. a horizontal common-response curl in a fixed coordinate `j`.

The only missing identification is not scalar magnitude but **agency and
time**.  A useful next theorem must prove one of:

- `j=k` after a source-preserving reselection;
- a two-observer chronological splice consuming the `j != k` case; or
- a positive-minimum/hard-residual inequality excluding the exact pattern
  of Section 3.

Absent one of these, iterating the two observers only constructs a finite
horizontal debtor-transfer graph.  Recurrence of that graph is not a
Nash--Bellman chronology.

## 5. Sources and novelty boundary

The input ledgers are the generic paid-response maximal-root reduction and
the checked endpoint-debt-rise common-response construction.  The new point
is their simultaneous statement (2.4)--(2.5) and the exact Fin4 regression
showing that their observer labels need not align.

This is a no-go/refinement, not an atlas output.  It neither proves that the
misaligned pattern survives positive-minimum provenance nor supplies a
consumer when it does.
