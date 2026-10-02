# Persistent-base Nash selection need not stay on the literal minimum face

Identity: CODEX_DESCENDANT  
Date: 2026-08-31  
Status: **exact ordinary-mathematics regression and surviving reduction.**
The regression is a finite persistent-face statement, not a positive-gap
quitting-game counterexample.  It proves that induced-Nash existence and
minimality on the displayed persistent face do not by themselves give a
minimum-preserving selection.  The full global source must supply an
additional law, chronology, or replacement comparison.

## 1. Question

Suppose a positive global minimum is attained by a one-root product profile
with a sure-quitter core \(K\), \(|K|\ge2\).  Can one keep \(K\) fixed,
replace the complementary players by an exact Nash point of their induced
finite game, and arrange that the selected point remains on the same minimum
face?

This would be useful because every complementary player would then have zero
debt.  If every base member also preferred to remain a quitter, the checked
persistent-base compiler would give a uniform-equilibrium payoff; otherwise
a base member would have an exact paid leaving response.

The answer is negative from the persistent-face data alone.

## 2. A rational Fin4 face

Take players \(0,1,2,3\), persistent base

\[
K=\{0,1\},
\]

and let \(x,y\in[0,1]\) be the Quit probabilities of free players \(2,3\).
Both base members Quit surely.  The root therefore absorbs at once even
after any one player changes their entire strategy, and all four complete
behavioral debts are exactly their one-root binary regrets.

Choose the free-player Quit-minus-Continue differences

\[
g_2(y)=1-2y,
\qquad
g_3(x)=2x-1.
\tag{2.1}
\]

Choose the base members' Continue-minus-Quit differences

\[
h_0(x,y)=\frac1{10}+2(x+y),
\qquad
h_1(x,y)=\frac34-(x+y).
\tag{2.2}
\]

These four affine rows are realized by an ordinary quitting reward table.
On coalitions containing \(K\), set for player \(2\)

\[
r_2(K)=0,\quad r_2(K\cup\{2\})=1,\quad
r_2(K\cup\{3\})=0,\quad r_2(K\cup\{2,3\})=-1,
\]

and for player \(3\)

\[
r_3(K)=0,\quad r_3(K\cup\{3\})=-1,\quad
r_3(K\cup\{2\})=0,\quad r_3(K\cup\{2,3\})=1.
\]

For player \(0\), set the rewards on \(K\cup T\) equal to zero and those
on \(\{1\}\cup T\) equal to

\[
\frac1{10}+2|T|,
\qquad T\subseteq\{2,3\}.
\]

For player \(1\), set the rewards on \(K\cup T\) equal to zero and those
on \(\{0\}\cup T\) equal to

\[
\frac34-|T|.
\]

Complete unused reward coordinates arbitrarily, for example by zero.  The
displayed differences are then exactly (2.1)--(2.2).

## 3. Exact face debt

The free-player regrets are

\[
d_2(x,y)=
\begin{cases}
(1-x)(1-2y),&y\le\frac12,\\
x(2y-1),&y\ge\frac12,
\end{cases}
\]

\[
d_3(x,y)=
\begin{cases}
y(1-2x),&x\le\frac12,\\
(1-y)(2x-1),&x\ge\frac12.
\end{cases}
\tag{3.1}
\]

The base debts are

\[
d_0(x,y)=\frac1{10}+2(x+y),
\qquad
d_1(x,y)=\left(\frac34-x-y\right)_+.
\tag{3.2}
\]

Put \(s=x+y\) and \(F=d_2+d_3\).  If \(s\le3/4\), direct inspection of
the four regions cut by \(x=1/2\) and \(y=1/2\) gives

\[
F+s\ge1.
\tag{3.3}
\]

Indeed the values of \(F+s-1\) are respectively

\[
0,\qquad 2x-1,\qquad 2y-1,\qquad 2(s-1),
\]

and the last region cannot occur when \(s\le3/4\).  Therefore

\[
D(x,y)
=F+\frac1{10}+2s+\frac34-s
\ge\frac{37}{20}.
\tag{3.4}
\]

If \(s\ge3/4\), the same four-region calculation gives

\[
F+2s\ge\frac74.
\tag{3.5}
\]

In the lower-left region this is \(1+s\ge7/4\); in the two mixed regions
it is \(3x+y\ge7/4\) or \(x+3y\ge7/4\); and in the upper-right region
\(s\ge1\), so it is \(3s-1\ge2\).  Hence (3.4) again follows.

At

\[
x=y=\frac14
\tag{3.6}
\]

the four debts are

\[
d_0=\frac{11}{10},\qquad d_1=\frac14,
\qquad d_2=\frac38,\qquad d_3=\frac18,
\]

and their sum is exactly \(37/20\).  Thus (3.6) is a full-debt global
minimizer of the entire displayed persistent face.

## 4. The induced Nash selection leaves the face minimum

Equations (2.1) are the strict matching-pennies orientation.  The unique
induced product Nash point is

\[
x=y=\frac12.
\tag{4.1}
\]

Both free debts then vanish, but

\[
d_0=\frac{21}{10},\qquad d_1=0,
\qquad D=\frac{21}{10}>\frac{37}{20}.
\tag{4.2}
\]

Consequently no induced Nash point lies on the persistent-face minimum,
despite the existence of a full-debt face minimizer and exact one-root cap
screening throughout the face.

This table is not asserted to have positive global terminal minimum debt.
Unused coalitions may open an equilibrium elsewhere.  Its role is to falsify
the finite inference

\[
\text{persistent-face minimum}
\Longrightarrow
\text{minimum-preserving induced-Nash selection}.
\tag{4.3}
\]

Any proof for a genuine positive global minimum must use information not
present in the finite persistent face.

## 5. What survives at the genuine attained product minimum

At a positive global minimum the checked singleton margin makes the passive
padding row redundant.  In the explicit padded/unpadded formulas, the only
extra padded option is the own singleton payoff, and it lies strictly below
the cap.  Hence the same semantic pair and law are attained both by the
one-root-then-Never profile and by stationary repetition of that root.  The
second sure quitter screens all unilateral continuation behavior.

Now choose an induced Nash point on the complementary face.  The checked
persistent-base alternative gives exactly:

1. all base leave signs hold, and the stationary all-behavior compiler gives
   a uniform-equilibrium payoff; or
2. a base member has a strict paid leave response.

Under a terminal exploitability gap, the second response has a uniform
positive gain.  But the newly selected induced Nash profile is not a literal
descendant of the attained minimum profile.  The old law, marked atom,
through-mark ledger, and common descendant slice are not preserved by the
simultaneous free-player reselection.  The paid target is therefore the same
off-minimum paid-cap port already present in the frontier, with the minimum
stored only as external provenance.

The exact additional datum needed is one of:

- an induced Nash point whose **whole semantic pair** remains on the global
  minimum fibre;
- a literal unilateral or chronological path from the attained minimum root
  to the selected induced Nash point, with cross-coordinate cap leakage
  controlled; or
- a consumer of the resulting off-minimum paid target which does not require
  such ancestry.

The regression proves that none of these follows merely from the two-player
induced-game equations and persistent-face minimality.

## 6. Sources inspected

- `quittingPersistentBaseNashSet_nonempty` and the induced root definitions
  in `PersistentBaseInducedGame.lean`;
- `exists_uniformPayoff_of_persistentBase_inducedNash_signs` in
  `PersistentBaseNashSemanticAdapter.lean`;
- `exists_uniformPayoff_or_persistentLargeBase_pos_gap` in
  `PersistentBaseConcreteGap.lean`;
- the literal finite dispatch in `LargePersistentBaseFiniteNashDispatch.lean`;
  and
- the mixed-deletion and stationary handoff adapters in
  `LargePersistentBaseDeletionAdapter.lean` and
  `LargeBaseStationarySemanticHandoff.lean`.

The rational regression is suitable for a small exact Lean test, but it is a
guardrail rather than a conjecture-closing theorem.
