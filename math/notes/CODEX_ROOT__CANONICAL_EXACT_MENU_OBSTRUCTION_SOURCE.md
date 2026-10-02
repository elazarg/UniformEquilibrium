# Canonical exact-menu obstruction and an explicit approximate selector

Owner: CODEX_ROOT.

## Current assessment

One complete independent mathematical review passed, with no unresolved
objection. The submission is an exact example and a mechanism-level
obstruction, not a counterexample to uniform equilibrium. Its unique exact
finite-menu equilibrium has unrestricted debt (18/49, 0, 0, 0) at every
deadline. Its explicit geometric approximate profile instead has full debt
(2^(-N), 2^(-N), 0, 0). The deadline and zero-error limits do not commute.

The exact/approximate separation was already present on another canonical
table in CODEX_HILBERT's unreviewed homotopy note, and a noncanonical version
is already proved in production Lean. The independently checked value here
is a second canonical realization, a particularly simple geometric bypass,
and the explicit order-of-limits statement. The table has a homogeneous
singleton-matrix witness and belongs to an existing solved class. It does
not eliminate a new hard-residual class or answer the arbitrary-table
approximate-selection question. Keep it as a durable research regression;
no additional export is being opened on this assessment.

The active self-contained canonical question allows approximate finite-menu
Nash laws; this submission explicitly does not refute that question.
No export or Lean-check status is claimed.

## Source and review

Original submission: `gpt/EXACT_EXAMPLE.md`.
SHA-256: `f4f258367064525d0e890be3a0b66588eb8881eb553a50bda674cbdd378a8079`.
The complete submission below is retained without alteration. The independent
report is [EXACT_EXAMPLE__BY_CODEX_FRECHET_CYCLE.md](../feedback/EXACT_EXAMPLE__BY_CODEX_FRECHET_CYCLE.md).
It verifies every-selector backward induction, the full behavioral caps,
the exact geometric equilibrium limit, and both limit orders. It also
provides the last-date zero-coordinate cases abbreviated in the submission.

For reuse, define R(t) as survival strictly before date t. If a consumer
requires strict error below e, choose 2^(-N) < e rather than merely <= e.
These are explanatory/compositional qualifications, not changes to the
preserved source. No Lean compilation of this example was performed.

## Research consequence

The active question already permits approximate menu equilibria and joint
selection of deadline and accuracy; no question correction is needed.
Use this table to test actual approximate selectors. Failure of exact
re-equilibration is not evidence against all such selectors, and a new
algorithm must be evaluated on the product of its independent marginal laws,
not a correlated empirical history. The geometric witness supplies a
concrete success target for those tests.

## Original submission

The two selection problems are genuinely different: **exact Nash at each finite deadline can fail permanently, even though vanishing-error laws on those same menus converge to an equilibrium.** In particular, “repair the pivot, then restore exact finite-menu Nash” cannot be a universal construction.

Here is an explicit counterexample in the canonical normalization, with a proof covering **every exact equilibrium at every deadline**. It does not refute the approximate producer in the question; it rules out exact re-equilibration as a way to obtain it.

## 1. A canonical table with permanently defective exact deadline equilibria

Take players \(0,1,2,3\), with pivot \(0\). First define the rewards to players \(0,1,2\), according to the active quitting set \(T\subseteq\{0,1,2\}\):

| \(T\)         | \((r_0,r_1,r_2)\) |
| ------------- | ----------------: |
| \(\{0\}\)     |       \((1,7,7)\) |
| \(\{1\}\)     |       \((7,0,7)\) |
| \(\{2\}\)     |       \((7,7,0)\) |
| \(\{0,1\}\)   |       \((6,8,7)\) |
| \(\{0,2\}\)   |       \((9,7,5)\) |
| \(\{1,2\}\)   |       \((7,5,8)\) |
| \(\{0,1,2\}\) |       \((7,6,6)\) |

For a nonempty coalition \(S\subseteq I\), these three payoffs depend only on \(T=S\cap\{0,1,2\}\); they are zero when \(T=\varnothing\). Define player \(3\)’s payoff by

$$
r_3(S)=
\begin{cases}
-1,&3\in S,\quad S\cap\{0,1,2\}\ne\varnothing,\\
1,&3\notin S,\quad S\cap\{1,2\}\ne\varnothing,\\
0,&\text{otherwise}.
\end{cases}
$$

Infinite all-Continue pays zero.

Thus

$$
\bigl(r_i(\{i\})\bigr)_{i\in I}=(1,0,0,0).
$$

Every player is punishment-normal: opponents playing Never give cap \(1\) to player \(0\) and cap \(0\) to the others, so \(P_i\le r_i(\{i\})\).

**Theorem.** For every deadline \(N\ge1\), the finite game on

$$
\{0,\ldots,N-1,\mathrm{Never}\}
$$

has exactly one Nash product law. It is

$$
\begin{array}{c|cc}
&N-1&\mathrm{Never}\\ \hline
0&2/7&5/7\\
1&4/7&3/7\\
2&1/7&6/7\\
3&0&1 .
\end{array}
\tag{1}
$$

Its unrestricted terminal debts are

$$
\boxed{\left(\frac{18}{49},0,0,0\right).}
\tag{2}
$$

Consequently, no choice of exact equilibria, no subsequence of deadlines, and no enlargement followed by exact re-equilibration makes the pivot defect tend to zero.

### Root calculation

When player \(3\) Continues, let \(q_0,q_1,q_2\) be the current Quit probabilities and \(v\) the continuation vector. Write \(\Delta_i\) for Quit payoff minus Continue payoff. Directly from the table,

$$
\boxed{
\Delta_i(q;v)
=
g_i+q_{i-1}-2q_{i+1}
-v_i(1-q_{i-1})(1-q_{i+1}),
}
\tag{3}
$$

where the active indices are taken modulo \(3\), and

$$
(g_0,g_1,g_2)=(1,0,0).
$$

Two elementary facts give the entire backward-induction argument.

### Fact A: every finite-menu Nash law has positive current all-Continue probability

First, player \(3\) cannot Quit surely.

If some active player currently Quits with positive probability \(a>0\), player \(3\)’s immediate Quit payoff is \(-a\), while Never gives a nonnegative payoff. If no active player currently Quits, player \(3\)’s sure Quit would pay player \(0\) zero, whereas joining gives player \(0\) one.

Nor can an active player Quit surely. Once one does, player \(3\) must Continue, and the following comparisons are independent of the continuation:

* If \(q_0=1\), then \(\Delta_2=q_1-2<0\), forcing \(q_2=0\). Then \(\Delta_1=1\), forcing \(q_1=1\). But this makes \(\Delta_0=-1\).
* If \(q_2=1\), the symmetric chain forces \(q_1=0\), then \(q_0=1\), then gives \(\Delta_2=-2\).
* If \(q_1=1\), \(q_2=1\) is impossible because \(\Delta_1=q_0-2<0\). Hence \(q_2<1\), so \(\Delta_0=-1+q_2<0\), forcing \(q_0=0\). But then \(\Delta_2=1\), forcing \(q_2=1\).

Thus every player Continues with positive probability.

**It follows that conditioning on current all-Continue yields an exact Nash law on the shorter menu.** Otherwise a profitable conditional replacement, multiplied by the positive probability of reaching that history, would be a profitable replacement in the original game. This justifies backward induction for arbitrary normal-form Nash laws, not merely for a chosen subgame-perfect selection.

### Fact B: the one-date equilibrium leads into a uniquely inert root region

At the zero continuation, player \(3\) must Continue. Its Quit payoff is strictly negative whenever any active player Quits with positive probability; if all active players Continue, player \(0\) strictly prefers Quit.

For the active players, the boundary conditions exclude zero coordinates, and Fact A excludes coordinates equal to one. Hence their indifference equations are

$$
1+q_2-2q_1=0,\qquad
q_0-2q_2=0,\qquad
q_1-2q_0=0.
$$

Their unique solution is

$$
q^*=\left(\frac27,\frac47,\frac17\right).
\tag{4}
$$

The corresponding payoff vector is

$$
V=\left(\frac{31}{7},\frac{19}{7},\frac{34}{7},\frac{31}{49}\right).
\tag{5}
$$

Now consider any root with continuation \(V\). Player \(3\) strictly prefers Continue: quitting gives \(-a\), while continuing gives a nonnegative current reward and the positive continuation \(V_3\) if no active player quits.

For the active players, all \(V_i>2\). There is no nonempty active support:

For a singleton support, its owner has

$$
\Delta_i=g_i-V_i<0.
$$

For support \(\{0,1\}\),

$$
\Delta_0=(1-q_1)(1-V_0)-q_1<0.
$$

For support \(\{0,2\}\), player \(2\) has

$$
\Delta_2=-2q_0-V_2(1-q_0)<0.
$$

For support \(\{1,2\}\), player \(1\) has the analogous strictly negative advantage.

Finally, if every active player Quits with positive probability, Nash requires every \(\Delta_i\ge0\). But (3) gives

$$
\sum_{i=0}^2\Delta_i
=
1-\sum_iq_i
-\sum_iV_i(1-q_{i-1})(1-q_{i+1})<0.
\tag{6}
$$

Indeed,

$$
\sum_iq_i+
2\sum_i(1-q_{i-1})(1-q_{i+1})\ge2.
\tag{7}
$$

The left side is multi-affine on the cube; at vertices with respectively \(0,1,2,3\) coordinates equal to one, its values are \(6,3,2,3\).

Therefore **all-Continue is the unique Nash root against \(V\)**.

Fact A now permits induction on the deadline. The last date must use (4); every preceding date must use all-Continue against the unchanged continuation \(V\). This proves uniqueness of (1).

### The defect does not decrease

At (1), player \(0\)’s prescribed payoff and Never payoff coincide:

$$
U_0=W_0=\frac{31}{7}.
$$

Its opponents’ joint Never probability is

$$
D_0=\frac37\frac67=\frac{18}{49}.
$$

Quitting at any date after the displayed menu therefore gives

$$
W_0+D_0=\frac{31}{7}+\frac{18}{49}.
$$

This proves the pivot debt in (2).

Every other player has own singleton reward zero, so every after-menu quitting date has exactly its Never payoff. Their finite-menu optimality already covers all unrestricted deviations. Thus (2) is the complete debt vector.

Also, for every \(1\le H\le N\),

$$
R_{p^N}(N-H)=1.
\tag{8}
$$

The exact laws never satisfy the requested early-absorption conclusion for \(\rho<1\).

## 2. Nevertheless, approximate laws on the actual menus solve this table

For the same table, define \(\sigma^N\) by making players \(1,2,3\) play Never and letting player \(0\) use

$$
\Pr(T_0=t)=2^{-(t+1)}
\quad(0\le t<N),\qquad
\Pr(T_0=\mathrm{Never})=2^{-N}.
\tag{9}
$$

This is an explicitly constructed law on its displayed menu—not an old Nash law with a renamed deadline.

Put \(x=2^{-N}\). Its payoff is

$$
U(\sigma^N)=\bigl(1-x,\,7(1-x),\,7(1-x),\,0\bigr).
\tag{10}
$$

Its **unrestricted** debts are exactly

$$
\boxed{d(\sigma^N)=(x,x,0,0).}
\tag{11}
$$

The verification is short. Player \(0\) obtains one by any finite deterministic quitting date, so its debt is \(x\).

For player \(1\), quitting at \(t<N\) gives

$$
7(1-2^{-t})+8\,2^{-(t+1)}
=
7-3\,2^{-t}.
$$

This increases with \(t\), so its best such date is \(N-1\), with value

$$
7-6x=U_1(\sigma^N)+x.
$$

Never and every after-menu date give \(U_1(\sigma^N)\).

For player \(2\), quitting at \(t<N\) gives

$$
7(1-2^{-t})+5\,2^{-(t+1)}
=
7-\frac92\,2^{-t}.
$$

Even its largest value, \(7-9x\), is below its Never payoff \(7-7x\).

Player \(3\)’s prescribed payoff is zero. Quitting simultaneously with player \(0\) pays \(-1\); all other outcomes available to a unilateral deviation pay zero. Its cap is therefore zero.

These comparisons cover all behavioral replacements by mixing deterministic stopping dates and Never, proving (11).

In particular,

$$
E_N(\sigma^N)=E_\infty(\sigma^N)=2^{-N}.
\tag{12}
$$

Moreover,

$$
R_{\sigma^N}(N-H)=2^{-(N-H)}.
\tag{13}
$$

For any supplied \(e,H,\rho,N_0\), choose \(N\) satisfying

$$
N\ge\max(H,N_0),\qquad
2^{-N}\le e,\qquad
2^{-(N-H)}<\rho.
$$

Equations (12)–(13) give the requested finite-menu producer **for this table**, and (10) gives the single limiting payoff

$$
(1,7,7,0).
$$

The construction does not begin with an unrestricted approximate equilibrium: the laws are specified in (9), and their unrestricted verification follows afterward.

## 3. The precise consequence for the research route

Define, for this fixed table,

$$
\Phi_N(e)
=
\min\left\{
E_\infty(p):
p\text{ is a product law on the }N\text{-date menu},
\ E_N(p)\le e
\right\}.
$$

For each fixed \(N\), compactness and continuity on the finite product simplex give

$$
\lim_{e\downarrow0}\Phi_N(e)=\Phi_N(0)=\frac{18}{49}.
$$

But (12) gives

$$
\inf_N\Phi_N(e)=0
\qquad\text{for every }e>0.
$$

Thus

$$
\boxed{
\inf_N\lim_{e\downarrow0}\Phi_N(e)=\frac{18}{49},
\qquad
\lim_{e\downarrow0}\inf_N\Phi_N(e)=0.
}
\tag{14}
$$

This is not merely a bad equilibrium selection: the exact equilibrium is unique at every deadline. **Exact re-equilibration destroys the useful approximations, regardless of which new deadline is chosen.**

The approximate laws also need not approach the exact equilibrium sets in strategy space. For example,

$$
\left|
p^N_0(\mathrm{Never})-\sigma^N_0(\mathrm{Never})
\right|
=
\frac57-2^{-N}.
\tag{15}
$$

So the remaining construction must work directly inside the approximate-equilibrium sets, with menu size and error chosen jointly. A finite-dimensional exactification argument cannot supply the missing renewal uniformly over deadlines.

**This does not yet take the original hard-residual problem to its endpoint.** The displayed table has zero global exploitability infimum, not a positive gap. What is proved here is the failure of the stronger exact-selection route, together with an explicit approximate producer that bypasses it. I have not constructed the corresponding repair for an arbitrary hard-residual table.
