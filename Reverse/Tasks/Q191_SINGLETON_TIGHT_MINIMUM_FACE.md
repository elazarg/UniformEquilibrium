# Singleton-tight minimum-face iteration

## Setting

Let \(I\) be a finite player set with at least two players, and let
\(r(S)\in\mathbb R^I\) be bounded quitting rewards. For a behavioral profile
\(\sigma\), write \(U(\sigma)\) for terminal payoff and \(B(\sigma)\) for the
coordinatewise best-response value. Put

\[
\mathcal K=\overline{\{(U(\sigma),B(\sigma)):\sigma
\text{ is behavioral}\}},
\qquad
d_i(u,b)=b_i-u_i,
\qquad
D(u,b)=\sum_i d_i(u,b).
\]

Assume \(p=(u,b)\in\mathcal K\) is a global minimizer with
\(D(p)=D_*>0\). Assume there is a unique debtor \(h\):

\[
d_h(p)=D_*,\qquad d_j(p)=0\quad(j\ne h),
\]

and that the owner is singleton-tight,

\[
u_h=r_h(\{h\}).
\]

At such a minimum point, every outsider satisfies the exact singleton
clearance inequality

\[
u_j-r_j(\{j\})\geq D_*\qquad(j\ne h).
\]

The set \(I\setminus\{h\}\) is nonempty. Define

\[
G=\max_{j\ne h}
\bigl[r_j(\{h,j\})-r_j(\{h\})\bigr]_+
\]

and choose

\[
0<q\leq\frac{D_*}{D_*+G}.
\]

Let \(x\) be the product row in which \(h\) Quits with probability \(q\) and
every outsider Continues surely.

## Question

Does this candidate row iterate on the same singleton-tight minimum face?
More precisely, prove or refute the following chain.

1. The row \(x\) is exact Nash against the prescribed payoff of \(p\).
   In particular, prove that singleton tightness makes \(h\) indifferent and
   that every \(j\ne h\) satisfies

   \[
   Q_j-C_j
   =(1-q)\bigl(r_j(\{j\})-u_j\bigr)
   +q\bigl(r_j(\{h,j\})-r_j(\{h\})\bigr)
   \leq0.
   \]
2. If \(p_{n+1}=T_xp_n\) and \(p_0=p\), then every \(p_n\) belongs to
   \(\mathcal K\), has total debt \(D_*\), has \(h\) as its unique debtor, and
   remains singleton-tight at \(h\).
3. The same fixed \(q>0\) therefore makes \(x\) exact Nash against every
   prescribed payoff \(u^{(n)}\).
4. The finite prefixes \(T_x^np\) converge to the semantics of the stationary
   profile which repeats \(x\).
5. The limiting outsider inequalities are

   \[
   r_j(\{h\})-r_j(\{j\})\geq D_*\qquad(j\ne h).
   \]

   If \(r_h(\{h\})\geq0\), the stationary profile is an exact terminal Nash
   profile, including against the owner's deviation to never Quit.

Here \(T_x\) is the semantic prefix operator: its prescribed coordinate is
the payoff from playing \(x\) and then using the old prescribed payoff after
unanimous Continue, while its cap coordinate permits a current pure endpoint
choice and then uses the old best-response cap.

## Acceptance criterion

An affirmative answer must prove all five steps, including arbitrary
behavioral deviations in the stationary limit; one-row complementarity alone
is insufficient. A counterexample must satisfy every displayed hypothesis,
including membership of \(p\) in the compact semantic carrier and global
minimality. It must identify the first failed step. An arbitrary algebraic
pair \((u,b)\) outside the carrier is not a counterexample.

## Answer

The implementation gives an exact structural characterization and
counterexample-regime closure. The finite-prefix claims, the carrier-wide cap
identification, and the stationary calculation against arbitrary behavioral
deviations are proved in
[`Research/Quitting/SingletonTightMinimumFaceIteration.lean`](../../Research/Quitting/SingletonTightMinimumFaceIteration.lean).

Write

\[
a_i:=r_i(\{h\}),\qquad
s_j:=r_j(\{j\}),\qquad
t_j:=r_j(\{h,j\}),\qquad
\rho:=1-q.
\]

The controlled-rate hypotheses and the limiting singleton clearance give

\[
J_j:=\rho s_j+qt_j\leq a_j\qquad(j\ne h). \tag{1}
\]

This endpoint inequality is the only game-specific premise needed for the
cap argument.

### Finite-prefix iteration

The row is exact Nash against the prescribed coordinate. For the owner, both
pure endpoints equal \(a_h=u_h\). For an outsider,

\[
Q_j-C_j
=\rho(s_j-u_j)+q(t_j-a_j)
\leq-\rho D_*+qG
\leq0.
\]

Semantic-prefix invariance keeps every iterate in \(\mathcal K\). The owner
remains singleton-tight with debt \(D_*\), every outsider debt remains zero,
and the same row is exact Nash at every iterate. Thus Steps 1--3 hold.

The exact recurrences give

\[
u_i^{(n)}\longrightarrow a_i,
\qquad
b_j^{(n)}\longrightarrow a_j\quad(j\ne h),
\qquad
b_h^{(n)}=b_h.
\]

Consequently

\[
T_x^np\longrightarrow
\left(a,\operatorname{update}(a,h,b_h)\right). \tag{2}
\]

The outsider limit also proves Step 5's inequalities

\[
a_j-s_j\geq D_*\qquad(j\ne h).
\]

### Carrier-wide washout and the owner cap

The same prefix row can start from an arbitrary carrier point
\(z=(v,c)\in\mathcal K\). Its prescribed coordinates converge to \(a\). The
owner cap becomes \(\max(a_h,c_h)\), while every outsider cap obeys

\[
y_{n+1}=\max(J_j-a_j,\rho y_n)
\]

and converges to zero by (1). Carrier closure therefore gives

\[
W_h(z):=
\left(a,\operatorname{update}(a,h,\max(a_h,c_h))\right)
\in\mathcal K. \tag{3}
\]

The debt of this washout point is
\(\max(a_h,c_h)-a_h\). Global minimality and \(D_*>0\) force

\[
b_h=a_h+D_*\leq c_h
\qquad\text{for every }(v,c)\in\mathcal K. \tag{4}
\]

Let \(\chi_h\) be the behavioral punishment value. Applying (4) to every
literal semantic pair gives \(b_h\leq\chi_h\). The general punishment lower
bound for every terminal-semantic envelope gives the reverse inequality.
Hence

\[
\boxed{b_h=\chi_h},
\qquad
\boxed{D_*=\chi_h-r_h(\{h\})}. \tag{5}
\]

This identifies the finite-prefix cap intrinsically; it is not an
unclassified tail artifact.

### Exact stationary comparison

The stationary profile repeating \(x\) has semantic pair

\[
\left(
a,
\operatorname{update}(a,h,\max(a_h,0))
\right).
\]

This formula uses the exact best-response theorem against constant opponents
and therefore covers arbitrary behavioral deviations. Punishment weak
duality together with (5) yields

\[
a_h<\chi_h\leq0.
\]

Thus \(a_h<0\), and comparison with (2) gives the sharp criterion

\[
\boxed{
T_x^np\text{ converges to the repeated stationary semantics}
\iff \chi_h=0.}
\]

Step 4 is therefore exact, but not unconditional. Its mismatch branch is
precisely \(\chi_h<0\). The stated hypotheses do not imply \(\chi_h=0\) in
the formal development, and no literal positive-minimum example with
\(\chi_h<0\) is supplied here. Accordingly, the hypotheses alone do not
yield a complete affirmative proof or a concrete refutation of the universal
stationary-convergence claim.

### Counterexample-regime closure

For `QuittingCounterexampleRegime reward`, the inequalities

\[
r_h(\{h\})<\chi_h,\qquad \chi_h\leq0
\]

feed the toggle-or-deletion dispatcher. The entire singleton-tight
positive-debt face, including the \(\chi_h=0\) endpoint, yields the following
disjunction:

1. a strict owner coalition toggle whose joined pure row has a strict
   outsider deviation; or
2. the same positive terminal exploitability gap on a nonempty, strictly
   smaller deleted-player type.

Hence this face is closed as a counterexample-regime frontier branch even
though the universal form of Step 4 is equivalent to the additional scalar
assertion \(\chi_h=0\).
