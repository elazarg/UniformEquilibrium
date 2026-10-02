# Full-debt responses pay a macroscopic signed seam but can land on an inert boundary

Identity: `CODEX_BOX_PORT`  
Date: 2026-08-31  
Status: **ordinary mathematics.  The signed-seam theorem and the exact Fin4
regression below are proved.  They do not consume the full-debt chamber.**

## 1. Question and answer

Let

\[
 x=(u,b)
\]

be a full-debt global minimum of the terminal-semantic carrier:

\[
 D(x)=D_*>0,
 \qquad d_i(x)=b_i-u_i>0\quad(i\in I).
\]

The debt-box rigidity argument says that every continuation vector in the
coordinate box

\[
 [u,b]=\{v:u_i\leq v_i\leq b_i\text{ for every }i\}
\]

has all Continue as its unique exact product root.  Suppose now that player
\(p\) executes a complete exact best response, so its own debt is killed.
Does the exact paid seam contradict the box rigidity, or force a second
chronological edge?

No.  What it forces is a **macroscopic signed semantic exit**: either another
cap rises, or another prescribed payoff falls.  If the response target stays
on the minimum fibre, it is a boundary minimum with one killed debt
coordinate.  The cap vector may remain unchanged on the upper face of the
original debt box, in which case the exact-root problem at that cap is still
uniquely all-Continue.  The target's own debt box need not be unchanged.
Thus box rigidity reinforces the inert boundary rather than consuming it.

The exact obstruction is realized by a four-player reward table in Section
5.  It has global minimum zero and is therefore not a counterexample to
uniform equilibrium.  It is a finite local regression against the proposed
splice.

## 2. Exact response and leakage identity

Assume here that \(I\) is finite and \(|I|\geq2\).  The useful statement is
most naturally made for an actual profile first.
Let \(\sigma\) be an actual profile with semantic pair

\[
 x=(u,b)=\operatorname{Sem}(\sigma),
\]

and let \(\tau_p\) be a best response attaining \(b_p\).  Put

\[
 \widehat\sigma=(\tau_p,\sigma_{-p}),
 \qquad y=(\widehat u,\widehat b)
   =\operatorname{Sem}(\widehat\sigma).
\]

The opponents of \(p\) are unchanged, so

\[
 \widehat b_p=b_p.
\]

Exact cap attainment gives

\[
 \widehat u_p=b_p,
 \qquad d_p(y)=0,
 \qquad \widehat u_p-u_p=d_p(x).
\tag{2.1}
\]

If \(x\) is a global minimum, write

\[
 F=D(y)-D_*\geq0.
\]

Since \(D(x)=D_*\), summing the coordinate debt changes and using (2.1)
gives the exact leakage identity

\[
 \boxed{
 \sum_{i\ne p}\bigl(d_i(y)-d_i(x)\bigr)
   =d_p(x)+F.}
\tag{2.2}
\]

This is a horizontal complete-response identity.  It is not absorption
charge and it does not assert that either endpoint is an exact one-stage
root.

## 3. Macroscopic signed-seam theorem

For \(i\ne p\), put

\[
 \Delta B_i=\widehat b_i-b_i,
 \qquad \Delta U_i=\widehat u_i-u_i.
\]

Then

\[
 d_i(y)-d_i(x)=\Delta B_i-\Delta U_i
 \leq (\Delta B_i)_+ +(-\Delta U_i)_+.
\]

Summing and applying (2.2) yields

\[
 \sum_{i\ne p}(\Delta B_i)_+
 +\sum_{i\ne p}(-\Delta U_i)_+
 \geq d_p(x)+F.
\tag{3.1}
\]

Consequently at least one of the following occurs:

\[
 \exists i\ne p,\qquad
 \widehat b_i-b_i
 \geq \frac{d_p(x)+F}{2(|I|-1)},
\tag{3.2}
\]

or

\[
 \exists i\ne p,\qquad
 u_i-\widehat u_i
 \geq \frac{d_p(x)+F}{2(|I|-1)}.
\tag{3.3}
\]

For Fin4 this lower bound is

\[
 \frac{d_p(x)+F}{6}.
\]

Thus an exact debt-killing response from a full-debt minimum cannot remain in
the one-sided semantic rectangle

\[
 \widehat b\leq b,
 \qquad \widehat u\geq u.
\]

It must cross one of its two signed faces by a fixed amount.  In particular,
with

\[
 \delta=\min_i d_i(x)>0,
\]

every exact response target is separated from that rectangle by at least
\(\delta/6\) in Fin4.

There is also the sharper unsigned bound

\[
 \|y-x\|_\infty\geq d_p(x),
\tag{3.4}
\]

under the usual product sup norm, because exact own-cap invariance and cap
attainment give

\[
 |\widehat u_p-u_p|=d_p(x).
\]

The signed version (3.2)--(3.3) identifies whether the toll is paid by cap
rise or prescribed-payoff loss.

### Source-attached limiting form

Exact attainment is not needed at finite rank.  Suppose one actual source
sequence \(\sigma_n\) converges semantically to the full-debt minimum \(x\),
one fixed player \(p\) is selected, and \(\widehat\sigma_n\) is obtained by an
\(\varepsilon_n\)-best response of \(p\), with
\(\varepsilon_n\to0\).  Along any common subsequence on which the response
targets converge to \(y\), own-cap invariance gives

\[
 d_p(y)=0,
 \qquad U_p(y)-U_p(x)=d_p(x),
\]

and (2.2)--(3.3) hold at the limit.  No unrelated realization is selected:
the target is the joint limit of the literal response endpoints of the same
source sequence.

Therefore the exhaustive target split is:

1. \(D(y)>D_*\): a genuine off-minimum target, still carrying the
   macroscopic signed seam;
2. \(D(y)=D_*\): a global-minimum boundary point with \(d_p(y)=0\), and
   hence a strict positive-debt-support drop relative to the full-debt
   source point.

This is a one-step boundary transition.  It is not automatically renewable:
a later response by another player may recreate positive \(p\)-debt.

### Canonical bad-mass fork: an antagonistic pure-time seam

There is a source-law strengthening when the paid response is the canonical
bad-mass fork rather than an arbitrary exact response.  Let an actual source
\(\sigma\) satisfy

\[
 D(\sigma)\leq D_*+\varepsilon,
 \qquad d_p(\sigma)\geq\Delta>0.
\]

Against the fixed opponents, write \(f_i(q)\) for player \(i\)'s payoff when
\(p\) uses pure stopping time \(q\).  The canonical construction selects a
set \(A\) of prescribed stopping-time mass \(a>0\) and one receiver \(r\)
such that

\[
 f_p(r)-f_p(q)>\frac\Delta4
 \qquad(q\in A),
\tag{3.5}
\]

and moves all mass on \(A\) to \(r\).  Let \(\tau\) be the resulting actual
profile and

\[
 g=U_p(\tau)-U_p(\sigma)>0.
\]

Own-cap invariance and global minimality give

\[
 \sum_{i\ne p}\bigl(d_i(\tau)-d_i(\sigma)\bigr)
 \geq g-\varepsilon.
\tag{3.6}
\]

Assume \(\varepsilon\leq g/2\).  Applying the positive-part argument of
(3.1) gives one of:

\[
 \exists j\ne p,\qquad
 B_j(\tau)-B_j(\sigma)
 \geq \frac{g}{4(|I|-1)},
\tag{3.7}
\]

or

\[
 \exists j\ne p,\qquad
 U_j(\sigma)-U_j(\tau)
 \geq \frac{g}{4(|I|-1)}.
\tag{3.8}
\]

In the second arm the literal mass-transfer formula is

\[
 U_j(\sigma)-U_j(\tau)
 =\int_A\bigl(f_j(q)-f_j(r)\bigr)\,d\nu(q).
\tag{3.9}
\]

Therefore some source-supported \(q\in A\) satisfies simultaneously

\[
 f_p(r)-f_p(q)>\frac\Delta4,
 \qquad
 f_j(q)-f_j(r)\geq \frac{g}{4(|I|-1)}.
\tag{3.10}
\]

The second bound is conservative: dividing by \(a\leq1\) only strengthens
it.  Positivity ensures that \(q\) and \(r\) have a finite first
disagreement even when one is Never.  Thus the payoff-loss arm yields one
source-supported pure-time switch on which the mover gains and one fixed
spectator loses at quantitative scales.

For Fin4, the spectator floor in (3.7)--(3.10) is \(g/12\).  Using the
standard fork bound \(g>\Delta^2/(16M)\), it is strictly larger than
\(\Delta^2/(192M)\).

This is still not a product Nash row.  The sign for \(j\) is a payoff effect
of changing \(p\)'s complete stopping time; it does not say that \(j\)'s
prescribed action at the first disagreement is a best response.  It is an
exact two-coordinate terminal seam suitable for a later hard-principal or
signed-atom consumer, not a chronological charge by itself.

## 4. What debt-box rigidity adds

At a full-debt global minimum the singleton moat gives

\[
 u_i-r_i(\{i\})
 \geq D_*-d_i(x)
 =\sum_{k\ne i}d_k(x)>0.
\tag{4.1}
\]

The debt-box proof then shows:

> For every \(v\in[u,b]\), all Continue is the unique exact product root
> against continuation \(v\).

Apply this to the response target.

- In the cap-rise arm (3.2), one cap coordinate leaves the upper face of the
  original box by a fixed amount.  This is a macroscopic cap seam, but not an
  exact root or chronological charge.
- In the payoff-loss arm (3.3), the complete cap may remain in \([u,b]\).
  Then debt-box rigidity says that the target cap has only the all-Continue
  exact root.  The paid horizontal response is therefore followed by a
  literally inert vertical root problem.

This is the exact logical boundary.  The first-disagreement date of the
complete response supplies only a one-player Bellman comparison.  It does not
make the other three prescribed actions a simultaneous product Nash root.
Hence it cannot be inserted into the debt-box theorem as a non-all-Continue
root.

The checked open-tube and minimum-fibre-isolation theorems strengthen this
description topologically: a sufficiently near-minimum carrier tail has only
the all-Continue exact root, while an exact absorbing root outside that tube
pays a positive excess-debt moat.  They do not turn the horizontal response
gain into that absorbing root.

## 5. Exact Fin4 regression: the cap and unique root can survive the paid seam

Let \(I=\{0,1,2,3\}\), and consider the two pure date-zero coalitions

\[
 S=\{0,1,2\},
 \qquad T=\{1,2\}.
\]

Here is one complete definition.  For player \(0\), set

\[
 r_0(A)=
 \begin{cases}
 1,&A=\{1,2\},\\
 0,&A=\{0,1,2\},\\
 -2,&A=\{0\},\\
 -1,&0\in A\text{ in every other case},\\
 0,&0\notin A\text{ in every other case}.
 \end{cases}
\tag{5.1}
\]

For player \(1\), all unlisted values are zero and

\[
\begin{aligned}
 r_1(\{1\})&=-2,&
 r_1(\{0,1,2\})&=0,&
 r_1(\{0,2\})&=1,\\
 r_1(\{1,2\})&=-1,&
 r_1(\{2\})&=1,&
 r_1(\{1,3\})&=-1,\\
 r_1(\{1,2,3\})&=-1.
\end{aligned}
\tag{5.2}
\]

For player \(2\), all unlisted values are zero and

\[
\begin{aligned}
 r_2(\{2\})&=-2,&
 r_2(\{0,1,2\})&=0,&
 r_2(\{0,1\})&=1,\\
 r_2(\{1,2\})&=0,&
 r_2(\{1\})&=1,&
 r_2(\{2,3\})&=-1.
\end{aligned}
\tag{5.3}
\]

For player \(3\), all unlisted values are zero and

\[
 r_3(\{3\})=-2,
 \qquad r_3(I)=1,
 \qquad r_3(\{1,2,3\})=1.
\tag{5.4}
\]

Thus every player's own singleton reward is \(-2\).  At continuation cap
\(b=(1,1,1,1)\), players are eliminated in the order \(0,1,2,3\):

- player \(0\) strictly prefers Continue for every pure opponent coalition;
- once player \(0\) Continues surely, player \(1\) strictly prefers
  Continue for every coalition of \(\{2,3\}\);
- once players \(0,1\) Continue surely, player \(2\) strictly prefers
  Continue for both actions of player \(3\);
- against all other players Continuing, player \(3\) strictly prefers
  Continue.

Let \(\sigma\) be the pure date-zero profile with quitting coalition \(S\).
Every unilateral deviation still leaves a nonempty quitting coalition, so
the complete behavioral caps are just the two date-zero endpoint maxima.
The displayed reward table gives

\[
 U(\sigma)=(0,0,0,0),
 \qquad B(\sigma)=(1,1,1,1),
 \qquad d(\sigma)=(1,1,1,1).
\tag{5.5}
\]

Now let player \(0\) Continue at date zero.  The target \(\tau\) has quitting
coalition \(T\).  The same table gives

\[
 U(\tau)=(1,-1,0,0),
 \qquad B(\tau)=(1,1,1,1),
 \qquad d(\tau)=(0,2,1,1).
\tag{5.6}
\]

Thus player \(0\)'s exact response gains one, kills its debt, keeps the
entire cap vector fixed, and transfers the lost debt exactly into player
\(1\)'s prescribed-payoff loss.  Total debt stays four.

The triangular inequalities in (5.1)--(5.4) prove that all Continue is the unique
product Nash root at the common continuation cap \(b\): first player \(0\)
must Continue, then player \(1\), then player \(2\), then player \(3\).
The all-Continue inequalities are strict because all singleton rewards are
\(-2<1\).

This realizes simultaneously:

\[
\begin{array}{c}
\text{full displayed debt, strict singleton separation,}\\
\text{an exact paid response with unit gain,}\\
\text{exact killed-mover debt and conservative total transfer,}\\
\text{unchanged cap on the original box's upper face, and}\\
\text{a unique all-Continue exact root at that cap.}
\end{array}
\tag{5.7}
\]

It is not a counterexample to uniform equilibrium.  Since every singleton
reward is negative, all Never is an exact equilibrium with payoff zero, so
the true global minimum debt is zero.  The example proves only that the local
box, seam, strictness, and transfer fields have no internal contradiction.
The positive-global-minimum provenance is the genuinely missing global
ingredient.

## 6. Consequence for the two-chamber programme

Debt-box rigidity plus an exact paid response yields the following honest
two-level reduction:

\[
\boxed{
\begin{array}{c}
\text{full-debt global minimum}\\
\text{and source-attached exact response}
\end{array}
\Longrightarrow
\begin{cases}
\text{off-minimum target with a macroscopic signed seam},\\
\text{or a zero-debt-coordinate boundary minimum.}
\end{cases}}
\tag{6.1}
\]

If the target cap remains inside the original debt box, the next exact-root
problem is uniquely all-Continue.  If it leaves by cap rise, one has a
macroscopic cap displacement but still no returned exact root.  The paid
first disagreement remains a horizontal behavioral edge in both cases.

Therefore none of the following follows from the combined data alone:

- positive absorption or Nash--Bellman charge;
- a second executable response preserving the first zero;
- renewable support-cardinality descent;
- a terminal approximation; or
- a contradiction to \(D_*>0\).

The next useful theorem must use the global source law or ancestry to consume
the signed cap-rise/payoff-loss seam.  Reapplying exact-root selection only
returns the already known macroscopic-exit versus all-Continue-inert split.

## 7. Narrow sources inspected

The ordinary debt-box argument and its independent audit are in:

- `gpt/DEBT.md`;
- `feedback/GPT__DEBT__BY_SOCIAL_WEIGHT_REVIEW.md`.

The checked nearby root and carrier statements are:

- `minimumTerminalSemantic_singletonMargin` in
  `TerminalSemanticAuxiliaryNashBudget.lean`;
- `exists_open_exactAllContinueTube_debtHomotopy` in
  `TerminalSemanticFinFourStrictMinimumPlateauIsolation.lean`;
- `exists_open_exactAllContinueTube_and_debtMoat_minimumFiber` in
  `TerminalSemanticFinFourMinimumFiberIsolation.lean`;
- `quittingTerminalSemanticDebt_prefix_eq_continueMass_mul_of_capNash` in
  `TerminalCapNashEndpointTransport.lean`.

The exact complete-response cap invariance and leakage framework is used in:

- `TerminalSemanticStoppingLawDebtConvexity.lean`;
- `ActualProfilePaidCapMinimumApproximation.lean`;
- `PaidCapMinimumFiberContraction.lean`.

The local cap-rise counterpart of the regression, and the reason old exact
roots cannot be reused after a paid fork, are in
`CODEX_GATE__FULL_DEBT_FORK_CAP_TRANSPORT_AND_REBASE.md`.

## 8. Next question

Can the source-attached terminal law force a favorable orientation of the
macroscopic signed seam (3.2)--(3.3), or price repeated unfavorable
prescribed-payoff losses by a finite coalition potential without treating
them as chronological absorption?
