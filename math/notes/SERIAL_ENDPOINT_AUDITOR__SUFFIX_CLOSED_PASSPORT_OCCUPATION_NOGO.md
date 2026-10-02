# Suffix-closed normalized passports give an undercharge identity, not an exact return

Author: SERIAL_ENDPOINT_AUDITOR

## Status

Closing the off-minimum decorated passport under every literal pre-mark tail
is mathematically useful, but it does not produce the missing chronology.
Marked mass/debt and paid-gain/debt densities are monotone under tail-taking.
At a debt minimizer this gives an exact occupation identity comparing root
cap defect with absorption times the selected debt level.

The identity has the wrong strategic type for the existing return compiler.
The pre-mark roots need not be exact Nash roots; their positive cap defects
are precisely allowed to pay for their absorption.  Moreover the suffix-
closed class contains a mark-now boundary with no pre-mark row at all.  A
four-player rational regression below realizes both phenomena with a strict
singleton-to-pair join, a positive pair payer, a unique all-Continue cap at
every displayed suffix, fixed marked mass/gain density, and arbitrarily small
rowwise defect spread over an arbitrarily long word.

The regression has global minimum debt zero, so it is not a counterexample to
a theorem that makes essential new use of positive global-minimum provenance.
It is an exact obstruction to deriving an admissible near-return merely from
suffix closure, compact debt minimization, and the cap-defect/absorption
recursion.

## Question

Start with a decorated source carrying a pure marked pair at a finite date,
positive marked mass and paid gain, and a fixed post-mark minimum tail.  Close
the raw class not only under arbitrary common prefixes, but also under taking
any literal all-Continue spine before the mark.  Store the first root and the
next decorated suffix so that the Bellman decomposition remains visible in
the compact closure.

Does minimizing total debt in a fixed normalized-mass/gain slice force a
cumulative defect/absorption shadowing certificate accepted by an existing
punishment-floor return compiler?

The answer from the stated data is no.  The exact output is the undercharge
account below; exactness and payoff recurrence remain independent missing
conditions.

## Sources inspected

- `quittingTerminalSemanticDebtSum_prefix_eq_continueMass_mul_add_capDefect`
  in
  `UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/CapDebtBellmanReduction.lean`.
- `QuittingPunishmentFloorFinitePrefix` and its fields `policy` and
  `exactNash` in
  `UniformEquilibrium/Quitting/Bellman/Finite/PunishmentFloorFinitePrefix.lean`.
- `QuittingPositiveCumulativeAdmissiblePayoffNearReturnFamily` and
  `quittingGame_exists_uniformEquilibriumPayoff_of_cumulativePayoffNearReturns`
  in `UniformEquilibrium/Quitting/Projective/CumulativeChargeNearReturn.lean`.
- The decorated prefix slice and its off-minimum inert arm in
  `FORCED_PAIR_REVIEW__NORMALIZED_PASSPORT_MINIMIZER_ELIMINATES_SUPPORT_ENTRY.md`.
- The bounded-depth and fixed-payer no-go in
  `ATLAS_GATEKEEPER__STRICT_PAIR_RAY_UNIQUE_CAP_CONSUMER.md`.
- The endpoint-closed horizontal no-rank result in
  `FORCED_PAIR_REVIEW__ENDPOINT_CLOSED_PASSPORT_HAS_NO_RANK.md`.

## 1. Tail-taking improves both normalized passports

Consider one actual pre-mark suffix at date \(t\).  Write

\[
D_t=D(\operatorname{Sem}(X^{(t)})),
\]

let \(q_t\) be its first product root, put

\[
c_t=\Pr_{q_t}(\text{all Continue}),
\qquad a_t=1-c_t,
\]

and let

\[
R_t=\operatorname{RootDef}(B_{t+1},q_t)\ge0
\]

be the total root Nash defect against the complete behavioral cap of the
next literal suffix.  The checked arbitrary-root debt recursion is

\[
\boxed{D_t=R_t+c_tD_{t+1}.}
\tag{1}
\]

Let \(m_t\) be the conditional mass, from suffix \(t\), of the fixed pure
pair at its marked date.  Let \(g_t\) be the payoff gain from the fixed
one-date endpoint update at that pair.  Reaching that remote row requires
the current prescribed root to realize all Continue, so literal transport
gives

\[
\boxed{m_t=c_tm_{t+1},\qquad g_t=c_tg_{t+1}.}
\tag{2}
\]

In a positive-density slice \(m_t>0\), hence \(c_t>0\).  Since all debts are
positive under the hypothetical positive minimum, (1)--(2) imply

\[
\frac{m_t}{D_t}
=\frac{c_tm_{t+1}}{R_t+c_tD_{t+1}}
\le\frac{m_{t+1}}{D_{t+1}},
\tag{3}
\]

and identically

\[
\frac{g_t}{D_t}\le\frac{g_{t+1}}{D_{t+1}}.
\tag{4}
\]

Thus the closed conditions

\[
m\ge\theta D,\qquad g\ge\psi D
\tag{5}
\]

really are inherited by every pre-mark tail.  This is the valid positive
result of the enlargement.

For compact bookkeeping, a raw datum may additionally store either a
`markNow` tag or a tuple consisting of its first product root and the next
decorated suffix.  Product roots and all other coordinates live in compact
finite-dimensional spaces, and equations (1)--(2) are closed.  Therefore the
same decomposition survives after passing to a subsequence in the decorated
closure.

## 2. What debt minimization actually forces

Let \(\overline D>0\) be the minimum whole debt on a suffix- and prefix-
closed normalized slice.  Suppose a minimizing decorated point is not in the
`markNow` arm and has a limiting first-root decomposition

\[
(D_0,m_0,g_0)
=\bigl(R+cD_1,\;cm_1,\;cg_1\bigr).
\tag{6}
\]

The next suffix belongs to the same slice by (3)--(5), so

\[
D_1\ge\overline D=D_0.
\tag{7}
\]

Consequently

\[
\boxed{0\le R=\overline D-cD_1
       \le(1-c)\overline D.}
\tag{8}
\]

This is an **upper** price on root defect, not exact Nash.  Define the excess

\[
e_t=D_t-\overline D\ge0.
\]

Then (1) is equivalently the exact normal-work identity

\[
\boxed{R_t-a_t\overline D=e_t-c_te_{t+1}.}
\tag{9}
\]

At a minimizing first state, \(e_0=0\), so

\[
R_0-a_0\overline D=-c_0e_1\le0.
\tag{10}
\]

For a finite pre-mark word let

\[
C_0=1,\qquad C_t=\prod_{s<t}c_s.
\]

If the marked row is the pure pair \(C\), put

\[
H_C=D(\operatorname{Sem}(\text{pure }C)).
\]

The pair occurs conditionally with probability one at its own row, so the
outer marked mass is \(m=C_T\).  Telescoping (1) and (9) gives

\[
\boxed{
D_0=\sum_{t<T}C_tR_t+mH_C,
}
\tag{11}
\]

\[
\boxed{
\sum_{t<T}C_ta_t=1-m,
}
\tag{12}
\]

and, when \(D_0=\overline D\),

\[
\boxed{
\sum_{t<T}C_t(R_t-a_t\overline D)
=m(\overline D-H_C)\le0.
}
\tag{13}
\]

The last sign uses suffix closure once more: the marked pure-pair point is an
admissible suffix, hence \(H_C\ge\overline D\).

Equation (13) is the maximal automatic shadowing statement.  It says that
the actual roots' cumulative cap defect is no larger than absorption priced
at \(\overline D\).  It does not say that any \(R_t\) vanishes.

## 3. Why the account does not enter the checked return compiler

A `QuittingPunishmentFloorFinitePrefix` requires, at every row,

1. exact Bellman transport of one payoff-value chronology;
2. an **exact Nash root** at that displayed value; and
3. the punishment-floor anchor.

The cumulative near-return consumer additionally requires a fixed positive
sum of exact-root absorption and prescribed payoff vectors returning
arbitrarily close at the two endpoints.

The pre-mark source chronology supplies none of these implications:

- its root cap defects are the nonnegative numbers \(R_t\), and (13) allows
  them to be of the same first order as absorption;
- exactifying one root changes the predecessor semantic/payoff point and
  breaks the literal continuation chain used by the next earlier row;
- the marked endpoint payoff is the pure-pair reward vector, with no reason
  to be close to the source prescribed payoff; and
- if the minimizing datum is `markNow`, the left sides of (11)--(13) are
  empty and there is no pre-mark charge at all.

Thus root defect in (13) is an approximation error, not admissible path
charge.  Replacing \(R_t\) by zero is exactly the missing production theorem,
not a consequence of minimizing the scalar debt.

## 4. Exact Fin4 regression

The following rational table demonstrates the obstruction without any
compactness or unattained-profile issue.  It also keeps the two important
pair labels: one pair member is already a best endpoint, while the other has
a positive paid leave.

Let the players be \(0,1,2,3\), fix an integer \(K\ge1\), and define, for
every nonempty coalition \(S\),

\[
r_0(S)=
\begin{cases}-1,&0\in S,\\0,&0\notin S,\end{cases}
\tag{14}
\]

\[
r_1(S)=
\begin{cases}
1,&0,1\in S,\\
-K,&1\in S,\ 0\notin S,\\
0,&1\notin S,
\end{cases}
\tag{15}
\]

and, for \(i=2,3\),

\[
r_i(S)=
\begin{cases}0,&i\in S,\\1,&i\notin S.\end{cases}
\tag{16}
\]

At the pure pair \(C=\{0,1\}\),

\[
U=(-1,1,1,1),qquad B=(0,1,1,1),qquad D=1.
\tag{17}
\]

Player \(1\) is a zero-defect marked owner, and its join from singleton
\(\{0\}\) to \(C\) has gain one.  Player \(0\) is a paid mover: leaving
\(C\) for \(\{1\}\) raises its payoff from \(-1\) to \(0\), also by one.

At the cap \(b=(0,1,1,1)\), all Continue is the unique exact product-root
Nash equilibrium.  Player \(0\) strictly prefers Continue to Quit.  Players
\(2,3\) also strictly prefer Continue.  Once those three coordinates are
Continue, player \(1\) gets \(-K\) from quitting alone and \(1\) from
continuing, so it too strictly Continues.

This already gives the sharp zero-length obstruction.  Fix any
\(\eta\in(0,1]\).  With marked mass and paid gain both equal to one, the
normalized slice

\[
m\ge D,\qquad g\ge D,\qquad m\ge\eta
\tag{18}
\]

contains the pure-pair point.  Prefixing it by a root of survival \(c\) gives

\[
m'=g'=c,qquad D'=c+R.
\]

Condition (18) forces \(R=0\).  Uniqueness then forces the prefix root to be
all Continue and \(c=1\).  Hence the pure pair is an exact normalized-
passport minimizer with unique all-Continue operation and **no pre-mark
chronology whatsoever**.

The same conclusion holds for a prefix word of any finite length.  If its
total survival is \(s\), with reach weights \(C_t\), then exact telescoping
gives

\[
m=g=s,
\qquad
D=s+\sum_t C_tR_t.
\]

Condition (18) forces \(\sum_tC_tR_t=0\), while \(m\ge\eta\) makes every
pre-mark reach weight positive.  Hence every \(R_t=0\).  Starting at the
innermost row, unique all-Continue exactness fixes that row and preserves the
pair semantic point; backward induction does the same at every earlier row.
Thus closing under arbitrary finite prefixes does not remove the mark-now
minimizer.  The auxiliary floor \(m\ge\eta\) plays exactly the role that the
positive global debt floor plays in the conjectural setting: it excludes a
zero-mass decoration, without adding chronology.

### Arbitrarily long defect-funded words

There is also a nontrivial long-word version.  Choose \(m_0\in(0,1)\) and a
finite stopping law for player \(0\) on dates \(0,\ldots,T\) with

\[
\Pr(T_0=T)=m_0,qquad
\Pr(T_0=t)\le m_0\quad(t<T).
\tag{19}
\]

Player \(1\) Continues before \(T\) and Quits surely at \(T\); players
\(2,3\) Never quit.  At \(T\) the marked coalition is \(C\).

The prescribed payoff and full behavioral cap are

\[
U=(-1,m_0,1,1),qquad B=(0,m_0,1,1),qquad D=1.
\tag{20}
\]

For player \(1\), a pure deadline \(t<T\) pays

\[
\Pr(T_0=t)-K\Pr(T_0>t)\le m_0,
\]

deadline \(T\) pays exactly \(m_0\), and Never or a later deadline pays
zero.  Since an arbitrary behavioral stopping rule is a mixture of pure
deadlines and Never, its cap is exactly \(m_0\).  The other three cap
coordinates in (20) follow directly from (14) and (16).

At every literal suffix \(s\le T\), let

\[
m_s=\Pr(T_0=T\mid T_0\ge s).
\]

Then

\[
D_s=1,qquad
B_s=(0,m_s,1,1),qquad
m_s=g_s,
\tag{21}
\]

and all Continue is again the unique exact root at \(B_s\).  The densities
\(m_s/D_s\) and \(g_s/D_s\) increase under tail-taking exactly as in
(3)--(4).

If \(x_s=\Pr(T_0=s\mid T_0\ge s)\), the actual first root at suffix \(s\)
has

\[
c_s=1-x_s,qquad
R_s=x_s,qquad
D_s=R_s+c_sD_{s+1}=1.
\tag{22}
\]

Thus defect pays absorption one-for-one.  Taking the earlier atoms equal to
\((1-m_0)/T\) and then letting \(T\to\infty\) makes every \(x_s\) uniformly
small while

\[
\sum_{s<T}C_sR_s
=\sum_{s<T}C_sa_s
=1-m_0
\tag{23}
\]

remains fixed.  This is precisely the unbounded-depth regime not ruled out
by a fixed-depth robust moat.  It still contains no exact pre-mark edge.

All-Never is an exact terminal Nash profile for this table, so its true
global minimum is zero.  One may put any desired actual tail after the pure
pair because it is never reached; in particular the regression can retain a
positive-debt post-mark semantic tail.  What it cannot honestly supply is
the assertion that this positive tail debt is the global minimum.  Therefore
the example isolates the only possible escape from the no-go: a successful
theorem must use positive global-minimum provenance in a way not captured by
the normalized densities or identities (1)--(13).

## 5. Verdict and next exact target

Suffix closure is worth retaining.  It proves (3)--(4) and the exact
occupation identity (13), and it rules out loss of the normalized passport
when passing to a later pre-mark spine.

It does **not** reach an existing return compiler.  The remaining theorem
would have to add genuinely strategic content, for example:

\[
\begin{array}{c}
\text{positive-global-minimum provenance}\\
+\ \text{suffix-closed normalized minimizer}\\[1mm]
\Longrightarrow\\[1mm]
\text{aggregate cap defect }o(\text{aggregate absorption})
\text{ with a payoff near-return},
\end{array}
\tag{24}
\]

or produce an exact floor-admissible replacement chronology with the same
source and endpoint payoff seam.  Neither conclusion follows from scalar
debt minimization or a normal-cone condition alone.

## 6. The positive-minimum-only datum and a falsifiable capstone

There is one concrete augmentation on which positive global minimality says
strictly more than the scalar identities above.  It has two parts.

First, retain the **empty marked corner**.  For a fixed actual post-mark tail
\(\tau\), the fifteen nonempty pure-root siblings screen off most or all of
the tail, whereas the empty root is literally the tail itself.  In the
regression above this sixteenth corner is all-Never and has debt zero.  In a
hypothetical counterexample it instead satisfies

\[
D(\operatorname{Sem}(\tau))\ge D_*>0.
\tag{25}
\]

Second, retain the **debt-leakage vector** of every actual unilateral
replacement.  If \(\sigma' = \sigma[i\leftarrow\rho_i]\) and

\[
G=U_i(\sigma')-U_i(\sigma)>0,
\]

then player \(i\)'s opponents, hence its unrestricted cap, are unchanged.
Consequently

\[
d_i(\sigma')=d_i(\sigma)-G.
\]

Writing \(e(\sigma)=D(\sigma)-D_*\), global minimality of every actual
replacement gives the exact positive-minimum constraint

\[
\boxed{
\sum_{j\ne i}\bigl(d_j(\sigma')-d_j(\sigma)\bigr)
\ge G-e(\sigma).
}
\tag{26}
\]

This is the narrow sense in which \(D_*>0\) can defeat the regression.  Its
paid pair has \(D=1\) but true \(D_*=0\), so \(e=1\) and (26) imposes no
positive leakage.  At an actual near-minimum source, by contrast, every
fixed paid gain must be transferred almost completely into the other debt
coordinates.

The vertical analogue of (26) is the signed priced-work variable

\[
W_t:=R_t-a_tD_*.
\]

For \(e_t^*=D_t-D_*\), equation (1) becomes

\[
\boxed{W_t=e_t^*-c_te_{t+1}^*.}
\tag{27}
\]

Thus a response-completed sixteen-corner state, augmented by the horizontal
leakage vectors (26) and the vertical work (27), records all automatic uses
of positive global minimality available inside this prefix/endpoint closure.
But these variables obey conservation laws:
horizontal leakage can circulate around the reviewed closed endpoint trace,
and vertical priced work telescopes.  Nonnegativity of debt controls their
divergence; it does not eliminate a divergence-free circulation.

There is also an exact provenance tradeoff.  Adding the empty corner to the
compact class immediately exposes the minimum tail, but it removes the
current nonempty marked atom.  Keeping the old mass and gain as historical
annotations makes the class compact and minimum-containing, but those marks
are no longer executable at the empty corner.  Replacing the singleton owner
by a tail best response has the same problem: it is an actual unilateral
profile and satisfies (26), but it no longer lies in the fixed common-tail
fifteen-corner cell.  This is why merely adding another scalar moment cannot
close the argument.

The narrow remaining theorem can therefore be asked without another rank or
diagnostic split.

> **Empty-corner active-passport reactivation.**  From the actual
> source-attached Fin4 hard-residual data consisting of a global-minimum
> post-mark tail, a fixed positive historical live-mass/gain passport on a
> nonempty marked sibling, and the complete response/leakage data (26),
> produce either:
>
> 1. actual profiles, with the same source provenance, whose debts converge
>    to \(D_*\) while a nonempty marked stage mass and a currently executable
>    same-stage gain remain bounded below by fixed positive constants; or
> 2. a source-matched exact punishment-floor near-return accepted by the
>    existing cumulative-charge compiler.

The first output is already consumed by the reviewed whole-source-return
concentrated-collision route; the second is a terminal output.  A theorem
with these exact two conclusions would eliminate the off-minimum inert node.
A counterexample to it that still has \(D_*>0\) and the hard-residual source
data would be a genuine obstruction at the conjecture frontier, not another
zero-minimum regression.  Equations (26)--(27) identify the full automatic
budget available to such a proof; the unproved operation is reactivating a
historical mark at the minimum empty corner without losing its source or
turning its gain into cross-coordinate circulation.
