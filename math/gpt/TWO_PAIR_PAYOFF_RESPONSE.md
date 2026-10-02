I obtained a **finite-menu selection theorem on an explicit open region of canonical four-player tables**. For the rational table supplied below, it constructs profiles \(\sigma^N\) satisfying

$$
\boxed{
d_1(\sigma^N)=d_2(\sigma^N)=d_3(\sigma^N)=0,
\qquad
d_0(\sigma^N)\le \left(\frac{67}{68}\right)^N.
}
$$

Each profile is an **exact Nash equilibrium of its finite stopping menu**, and the displayed debts are against **unrestricted behavioral deviations**.

This is a complete sufficient-class result, **not a proof for arbitrary Fin4**. The mechanism avoids horizontal cap installation: independence excludes certain prescribed payoffs, and that exclusion forces the three opponents’ survival probability to contract at every exact Nash prefix.

[Full proof, explicit reward table, and scope](TWO_PAIR_PAYOFF_EXCLUSION_AND_GEOMETRIC_FINITE_MENU_SELECTION.md) · [Proof and exact-arithmetic verification package](FIN4_NONCONVEX_SELECTOR.zip)

## 1. A nonconvex payoff obstruction that actually proves UE

Write

$$
s_i=r_i(\{i\}),\qquad A=\{0,1\},\quad B=\{2,3\},
$$

and define the two mean payoff surpluses

$$
G_A(u)=\frac{u_0-s_0+u_1-s_1}{2},
\qquad
G_B(u)=\frac{u_2-s_2+u_3-s_3}{2}.
$$

**Theorem.** Suppose \(s_0+s_1\ge0\) and \(s_2+s_3\ge0\). Suppose there are \(a,b,L\ge0\), with

$$
a\le b+2L,
$$

such that the reward table satisfies

$$
\begin{aligned}
\bigl(G_A(r(A)),G_B(r(A))\bigr)&\le(a,-b),\\
\bigl(G_A(r(B)),G_B(r(B))\bigr)&\le(-b,a),\\
\bigl(G_A(r(S)),G_B(r(S))\bigr)&\le(-L,-L)
&&\text{for every other nonempty }S.
\end{aligned}
\tag{1}
$$

All vector inequalities are coordinatewise. Then the game has a uniform-equilibrium payoff.

For fixed \(a,b,L\), these are **thirty linear inequalities on the actual rewards**. Individual singleton rewards may have mixed signs; only the two displayed sums must be nonnegative.

### Independence supplies the missing inequality

For any actual profile, let

$$
x=\Pr(A),\qquad y=\Pr(B),\qquad n=\Pr(\mathrm{Never}),\qquad
z=1-x-y-n.
$$

Then

$$
\boxed{\sqrt{x}+\sqrt{y}+\sqrt n\le1},
\qquad\text{hence}\qquad
z\ge2\sqrt{xy}.
\tag{2}
$$

Here is a direct proof, including arbitrary infinite stopping laws. Group the independent clocks into \((T_0,T_2)\) and \((T_1,T_3)\). For the first pair, put

$$
a_1=\Pr(T_0<T_2),\quad b_1=\Pr(T_2<T_0),\quad
c_1=\Pr(T_0=T_2=\mathrm{Never}),
$$

and define \(a_2,b_2,c_2\) similarly for the second pair. Each triple sums to at most one. Moreover,

$$
x\le a_1a_2,\qquad y\le b_1b_2,\qquad n=c_1c_2.
$$

Cauchy–Schwarz proves (2).

The repository already contains the disjoint-pair square-root machinery. The use here is to turn that restriction into a complete reward-table criterion, retaining Never rather than allowing arbitrary correlated coalition lotteries.

From (1),

$$
\begin{aligned}
G_A(U)&\le ax-by-Lz-\frac n2(s_0+s_1),\\
G_B(U)&\le ay-bx-Lz-\frac n2(s_2+s_3).
\end{aligned}
$$

If \(x\le y\), then

$$
G_A(U)
\le ax-by-2L\sqrt{xy}
\le(a-b-2L)x-b(y-x)\le0.
$$

If \(y\le x\), the symmetric argument gives \(G_B(U)\le0\). Therefore every actual payoff—and every limit of actual payoffs—satisfies

$$
\boxed{\min\{G_A(U),G_B(U)\}\le0.}
\tag{3}
$$

### Why payoff information suffices here

At a positive global minimum \(D_*>0\) of complete total debt, the existing minimum-singleton-margin theorem gives

$$
B_i\ge s_i+D_*.
$$

Consequently,

$$
G_A(U)\ge D_*-\frac{d_0+d_1}{2}\ge\frac{D_*}{2}>0,
$$

and likewise \(G_B(U)>0\), contradicting (3). The minimum-margin theorem is exactly the one in `TerminalSemanticAuxiliaryNashBudget.lean`.

Thus the minimum debt is zero. Actual terminal approximate equilibria exist at every accuracy, and the established terminal-to-uniform selection theorem supplies one fixed uniform payoff. 

**No payoff realizer is substituted for a semantic source.** We exclude a necessary property of a hypothetical positive minimum; we do not infer incentives from a payoff representation.

The same argument extends to any finite player set with four distinguished players and two target coalitions containing opposite distinguished pairs. The remaining players’ payoff coordinates can be arbitrary. The full statement is in the proof file.

## 2. Turning the obstruction into a finite-law selector

Now specialize to

$$
s=(1,0,0,0)
$$

and impose the stronger numerical version of (1):

$$
\begin{aligned}
(G_A(r(A)),G_B(r(A)))&\le(1,-3/4),\\
(G_A(r(B)),G_B(r(B)))&\le(-3/4,1),\\
(G_A(r(S)),G_B(r(S)))&\le(-1,-1)
&&\text{otherwise}.
\end{aligned}
\tag{4}
$$

These inequalities give the uniform quantitative exclusion

$$
\boxed{\text{Every actual profile satisfies }
\min_i(U_i-s_i)\le-\frac38.}
\tag{5}
$$

To verify the constant, write \(p=\sqrt{x},q=\sqrt y,t=\sqrt n\), so \(p+q+t\le1\). Then

$$
\begin{aligned}
G_A(U)&\le2p^2+\tfrac14q^2+\tfrac12t^2-1,\\
G_B(U)&\le\tfrac14p^2+2q^2+t^2-1.
\end{aligned}
$$

For \(p\le1/2\), the first expression is at most

$$
2p^2+\tfrac12(1-p)^2-1\le-\tfrac38.
$$

For \(p\ge1/2\), the second is at most

$$
\tfrac14p^2+2(1-p)^2-1\le-\tfrac7{16}.
$$

Both final inequalities follow by checking the endpoints of the relevant convex quadratic.

The next lemma is the strategic step.

### Actual-tail opponent-forcing lemma

Suppose a canonical table satisfies, for some \(\kappa>0\),

$$
\min_i(U_i-s_i)\le-\kappa
\quad\text{for every actual profile}.
\tag{6}
$$

Assume its singleton joining gains satisfy

$$
g_j:=r_j(\{0,j\})-r_j(\{0\})\ge0
\qquad(j=1,2,3),
\tag{7}
$$

and \(g_k=g>0\) for one fixed outsider \(k\). Let \(|r_i(S)|\le M\), and let \(L_0\ge0\) bound every actual \(U_k\) from above.

Then **every exact product Nash root against every actual tail payoff** satisfies

$$
\boxed{
1-\prod_{j\ne0}(1-q_j)\ge
\alpha:=\frac{\kappa g}{4M(L_0+g+\kappa)}>0.
}
\tag{8}
$$

This bounds **opponent absorption**, not merely joint absorption.

**Proof.** Let \(a=1-\prod_{j\ne0}(1-q_j)\), and suppose \(a<\alpha\). All outsiders then have positive Continue support. Put \(t=q_0\).

Compare the root with \((t,0,0,0)\), keeping its actual continuation \(U\). Each endpoint changes by at most \(2Ma\). Exact Nash therefore implies

$$
(1-t)U_j-tg_j\ge-4Ma
\qquad(j\ne0).
\tag{9}
$$

For the fixed outsider \(k\),

$$
(1-t)(L_0+g)\ge g-4Ma>0.
$$

In particular \(t<1\). Using \(g_j\ge0\) in (9),

$$
U_j\ge-\frac{4Ma}{1-t}
\ge-\frac{4Ma(L_0+g)}{g-4Ma}>-\kappa.
$$

The pivot also has positive Continue support. Comparing its endpoints against all-Continue opponents gives

$$
U_0\ge1-4Ma>1-\kappa.
$$

Every coordinate is therefore strictly above \(s_i-\kappa\), contradicting (6). ∎

### The actual construction

Start with all-Never and repeatedly prepend an exact Nash root:

$$
\sigma^0=\mathrm{Never}^4,\qquad
q^n\in\operatorname{NE}\bigl(U(\sigma^n)\bigr),\qquad
\sigma^{n+1}=q^n::\sigma^n.
\tag{10}
$$

**Any choice of exact root works.** Finite normal-form Nash existence supplies each choice; no favorable sequence is assumed. 

At the initial source,

$$
(d_0,d_1,d_2,d_3)=(1,0,0,0).
$$

For an exact Nash prefix, the complete-cap formula gives

$$
\begin{aligned}
B_i'&=\max\{Q_i,H_i+s_i(q)B_i\},\\
U_i'&=\max\{Q_i,H_i+s_i(q)U_i\}.
\end{aligned}
$$

Hence

$$
0\le d_i'\le s_i(q)d_i.
\tag{11}
$$

This is the full-response prefix mechanism used in the attached cap-clock work, without a horizontal replacement. 

The three zero debts remain zero. Equation (8) makes the remaining debt contract:

$$
E(\sigma^N)=d_0(\sigma^N)\le(1-\alpha)^N.
\tag{12}
$$

Each \(\sigma^N\) uses only

$$
\{0,\ldots,N-1,\mathrm{Never}\}.
$$

It is exact Nash for that menu by backward induction: a menu response either quits at the new root or continues into the previous menu, whose optimal response value equals its prescribed payoff.

Thus the three required opponent laws are simply

$$
(\sigma^N_1,\sigma^N_2,\sigma^N_3).
$$

The prescribed pivot law already achieves (12), so the **exploitability-minimizing pivot-repair LP** has value no greater than (12). This directly supplies the outer selection, rather than merely solving the inner LP. The inspected LP theorem identifies that optimum with the behavioral repair infimum.

## 3. An explicit region outside product-low

The [complete rational table](FIN4_NONCONVEX_SELECTOR/TABLE.json), also displayed conventionally in the proof, satisfies (4), with

$$
M=\frac{17}{4},\qquad
(g_1,g_2,g_3)=\left(3,\frac{17}{4},\frac14\right).
$$

Taking observer \(k=2\) gives

$$
L_0=\frac74,\qquad g=\frac{17}{4},\qquad \kappa=\frac38,
$$

so

$$
\alpha=\frac1{68}.
$$

Therefore

$$
\boxed{E(\sigma^N)\le(67/68)^N},
\qquad
N\ge\left\lceil68\log(1/\varepsilon)\right\rceil
$$

suffices for unrestricted terminal \(\varepsilon\)-Nash. This bounds the number of dates, not the computational complexity of exact Nash solving.

The fixture is separated from the named premium criteria. Its pair-\(A\) reward is

$$
r(A)=(2,1,-3/4,-3/4).
$$

At \(q=(1,1,0,0)\), both active quitters receive strictly more than their singleton rewards. Thus product-low fails, and consequently so do supportwise balance and ordered premiums, which imply product-low. 

It also cannot be handled by a nonnegative linear payoff separation of the whole reward convex hull:

$$
\frac{r(A)+r(B)}2
=(9/8,1/8,1/8,1/8)
=s+\tfrac18\mathbf1.
$$

That correlated lottery strictly dominates all singleton levels. It is **not** an independently realizable terminal law: its pair masses violate (2). This is where the nonconvex restriction matters.

The exact-arithmetic checker verifies the thirty inequalities, all constants, and separation witnesses. It also rules out pure terminal equilibria and exact roots with two sure quitters for this fixture. It does **not** rule out every other existing sufficient class or the full punishment-tail sure-quitter alternative.

### The result survives perturbations

Keep the four own-singleton entries fixed and perturb **every other reward entry** by at most \(1/16\). This gives a 56-dimensional canonical box with relatively open interior.

The payoff deficit remains at least \(5/16\), all joining gains remain positive, and uniform valid constants yield

$$
\boxed{
E(\sigma^N)\le\left(\frac{909}{920}\right)^N
}
$$

throughout that box. Product-low still fails throughout, and the correlated lottery remains strictly above \(s\) in every coordinate.

## What this closes—and what it does not

For this region, the missing global selection is supplied: **actual finite opponent laws, an actual pivot law, exact finite-menu equilibrium, and vanishing unrestricted regret**, with an explicit geometric bound. There is no cap installation whose cross-player recharge remains to be controlled.

The general obstruction remains outside this region: arbitrary canonical tables need not satisfy either the payoff exclusion or the joining inequalities. The attached shifted-cap and reset-renewal problems are therefore not consumed in general.

The proofs above are ordinary mathematics; the finite fixture checks passed with exact rational arithmetic. **No new Lean theorem has been compiled.**
