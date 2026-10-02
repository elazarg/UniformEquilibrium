A counterexample-preserving perturbation is enough here: we do not have to eliminate the two-sure configuration at every original table. That distinction lets us remove **the entire zero-singleton minimum-law branch**, including the opposed three-sure reversals and the unresolved two-sure case.

The result is a stronger source reduction, not a proof of Fin4. Its conclusion is that a counterexample can be chosen so that **every sufficiently accurate actual near-minimizer has a uniformly positive probability of a singleton first coalition**.

## 1. The stronger reduction

Separate the reward table into its four own-singletons \(s_i=r_i(\{i\})\) and the other 56 coordinates \(b\). Normalize all rewards into \([-1,1]\). Write

$$
r_b(s),\qquad
\Omega_b=\max_{s\in[-1,1]^4}\eta(r_b(s)).
$$

Call a product root **screened** when at least two players quit surely at date zero. Its complete payoff/cap pair is independent of the subsequent continuation: after any unilateral deviation, another sure quitter still absorbs immediately. In particular, its exploitability is independent of all four own-singleton coordinates.

Define

$$
\theta(b)=\min_{\text{screened roots }q}E_{r_b(s)}(q).
$$

I obtain the following.

> **Screened-root separation theorem.** There is an explicit nonzero polynomial \(\Pi(b)\), a product of 24 degree-six expressions, such that
>
> $$
> \Pi(b)\ne0,\quad \Omega_b>0
> \quad\Longrightarrow\quad
> \boxed{\theta(b)>\Omega_b.}
> $$
>
> If any four-player counterexample exists, one can choose a rational \(b\in(-1,1)^{56}\) satisfying these hypotheses.

Thus a hypothetical counterexample admits a singleton fiber with one uniform strict gap

$$
E_{r_b(s)}(q)\ge \Omega_b+\gamma
$$

for **every** own-singleton choice \(s\) and **every** screened mixed root \(q\).

The uploaded membership-stretch reduction obtains this kind of strict gap for the eleven nonsingleton **pure** sure coalitions. The new reduction covers the entire union of screened mixed-root faces. It replaces the exact stretch ancestry; it does not pretend to preserve the old-table comparison used in the opposed-reversal manuscript.  

Here is the proof.

## 2. An explicit algebraic obstruction to four equal positive debts

Fix two sure players \(a,b\). Let \(c,d\) quit independently with probabilities \(x,y\in[0,1]\).

Because of screening, every complete deviation reduces exactly to Quit at zero or Continue at zero. Later finite dates and Never have the Continue payoff.

For the sure players, let

$$
G_a(x,y),\ G_b(x,y)
$$

be their expected Continue-minus-Quit gaps. Their debts are

$$
d_a=\max(0,G_a),\qquad d_b=\max(0,G_b).
$$

For optional player \(c\), let \(\Delta_c(y)\) be its Quit-minus-Continue gap. Similarly define \(\Delta_d(x)\). Then

$$
d_c=\max\bigl((1-x)\Delta_c(y),-x\Delta_c(y)\bigr),
$$

$$
d_d=\max\bigl((1-y)\Delta_d(x),-y\Delta_d(x)\bigr).
$$

Choose one of the two branches for each optional player. There are four choices. For each choice, the four expressions

$$
F_a=G_a,\quad F_b=G_b,\quad F_c,\quad F_d
$$

are bilinear in \(x,y\).

**If all actual debts equal \(m>0\), one of these four branch choices makes all four \(F_i\) equal \(m\).** This includes \(x,y=0,1\), so three-sure and four-sure roots are already covered.

Write

$$
z(x,y)=(1,x,y,xy)^{\mathsf T},\qquad F_i=\ell_i z.
$$

Notice the identity

$$
z_0z_3-z_1z_2=0.
$$

Form the \(3\times4\) matrix

$$
A=
\begin{pmatrix}
\ell_b-\ell_a\\
\ell_c-\ell_a\\
\ell_d-\ell_a
\end{pmatrix}.
$$

Its entries are linear combinations of the 56 reward coordinates \(b\), with no own-singleton dependence.

For \(j=0,1,2,3\), define its signed maximal minors

$$
w_j=(-1)^j\det A_{\widehat j},
$$

where \(A_{\widehat j}\) deletes column \(j\). Finally put

$$
P_{ab,\sigma}(b)=w_0w_3-w_1w_2.
$$

If this degree-six expression is nonzero, then \(A\) has rank three and its kernel is the line spanned by \(w\). Equal branch values would give

$$
Az(x,y)=0,
$$

so \(z=t w\) for some nonzero \(t\). But then

$$
0=z_0z_3-z_1z_2=t^2P_{ab,\sigma}(b),
$$

a contradiction.

Taking the product over six sure pairs and four optional branch choices gives

$$
\boxed{\Pi(b)=\prod_{|K|=2}\prod_{\sigma\in\{Q,C\}^2}P_{K,\sigma}(b).}
$$

Therefore \(\Pi(b)\ne0\) excludes every screened root with four equal positive debts.

### Why this is a genuine generic condition

It remains to prove that these polynomials are not identically zero; dimension counting alone would not suffice.

For any fixed pair and branch choice, use the recipient-disjoint reward coordinates to realize

$$
F_a=\tfrac14,\qquad
F_b=\tfrac12+\tfrac14xy,\qquad
F_c=\tfrac14L_\sigma(x),\qquad
F_d=\tfrac14L_\tau(y),
$$

where

$$
L_Q(t)=1-t,\qquad L_C(t)=t.
$$

These are realizable membership gaps with all rewards bounded by \(3/8\): assign each Continue/Quit endpoint pair opposite half-gap rewards.

The resulting equality matrix has kernel spanned by

$$
(1,\xi,\upsilon,-1),
\qquad \xi,\upsilon\in\{0,1\}.
$$

Its quadratic expression is

$$
-1-\xi\upsilon\ne0.
$$

Indeed, the factor is \(-1/2048\) for the \(CC\) choice and \(-1/4096\) for each other choice.

Every factor is therefore a nonzero polynomial, and so is their product. Consequently

$$
\{\Pi\ne0\}
$$

is open and dense, with rational points dense in it.

This is a polynomial in **reward-table coordinates**, not the obstruction potential on payoff annotations from route E.

## 3. Why algebraic exclusion becomes a strict global gap

The indispensable existing fact is:

> At a positive global minimum of maximum complete-deviation debt, every player’s debt equals that minimum.

This is already present as `minimumTerminalSemantic_maximumDebt_allPlayersTie` in `PositiveMaximumDebtMinimum.lean`; it is not the new contribution here.

Now choose \(s_*\) attaining \(\Omega_b>0\). Every screened root is an actual profile, so

$$
\Omega_b\le\theta(b).
$$

If equality held, a screened root attaining \(\theta(b)\) would be an actual global minimum for \(r_b(s_*)\). All four debts would equal \(\Omega_b>0\), contradicting \(\Pi(b)\ne0\). Hence

$$
\theta(b)>\Omega_b.
$$

Both extrema really are attained. The screened-root domain is a union of six compact squares, and its full regret is continuous. The singleton fiber is compact, and

$$
|\eta(r)-\eta(r')|\le2\|r-r'\|_\infty.
$$

The latter follows by bounding every prescribed and deviated payoff change before taking either supremum or infimum. It controls unrestricted deviations, not a fixed menu. 

Finally, start from any positive-gap table. After common scaling into the interior of the unit cube, sufficiently small perturbations preserve its positive gap. Perturb only \(b\) to rational coordinates with \(\Pi(b)\ne0\), and then maximize over its singleton fiber.

This proves the counterexample-preserving selection. **No sixty-coordinate maximum, signed membership stretch, or separately selected favorable root is needed.**

## 4. The resulting singleton-mass collar

Let \(\mathcal L_r\) be the joint carrier of prescribed payoffs, full caps, and terminal outcome laws:

$$
\mathcal L_r
=\overline{\{(U(p),B(p),\mu_p):p\text{ actual}\}}.
$$

Fix a minimizing point with

$$
E(U,B)=\eta(r)=m>0
$$

at a table with \(\Pi(b)\ne0\). Suppose its total singleton mass were zero.

There are two steps.

### Zero singleton mass first forces zero Never mass

Take actual profiles converging jointly to the carrier point. Let \(a_{n,i}\) be player \(i\)’s marginal Never probability, \(p_n=\prod_i a_{n,i}\), and \(u_{n,i}\) its prescribed singleton-\(i\) probability.

Independence gives

$$
u_{n,i}
\ge (1-a_{n,i})\prod_{j\ne i}a_{n,j}
\ge p_n(1-a_{n,i}).
$$

The first term counts the event that only player \(i\) ever quits.

If the limiting Never mass were positive, \(p_n\) would be bounded away from zero. Since every \(u_{n,i}\to0\), every \(a_{n,i}\to1\). Thus the limiting Never mass would actually be one.

That would make \(U=0\). But the positive-MAX-minimum singleton moat gives

$$
B_i-s_i\ge m,\qquad d_i\le m,
$$

hence \(U_i\ge s_i\). Therefore all \(s_i\le0\), making all Never an actual zero-debt profile—a contradiction.

So the minimizing law has zero Never mass as well.

### The exact product-base theorem now applies

We have zero Never mass, zero singleton masses, and strict margins \(B_i>s_i\). The existing theorem
`exists_twoSureProductRoot_realizing_jointCarrierPoint_of_strictMargin`
therefore produces one **unpadded screened root realizing the same full payoff/cap pair and the same law**. This is exactly the scope of the inspected declaration, not payoff-only compression.

That root would have four equal positive debts, contradicting \(\Pi(b)\ne0\).

We have proved

$$
\boxed{
\text{Every positive MAX-minimum law has }
\sum_i\mu(\{i\})>0.
}
$$

Compactness strengthens this to an actual-source statement. The minimum set in \(\mathcal L_r\) is compact, so its total singleton mass has a positive minimum. A sequence of near-minimizers violating half that bound would converge jointly to a minimizing point violating it. Hence there exist \(\kappa,\varepsilon_0>0\) such that

$$
\boxed{
E_r(p)\le\eta(r)+\varepsilon_0
\quad\Longrightarrow\quad
\sum_i\Pr_p(\text{first coalition}=\{i\})\ge\kappa
}
$$

for **every actual behavioral profile** \(p\).

The same argument works uniformly over all singleton choices in the fixed fiber satisfying \(\eta(r_b(s))\ge a>0\). The varying-table joint carrier has a closed graph because evaluating the same laws at nearby rewards changes payoffs and caps uniformly, while leaving the outcome law unchanged.

This is why the conclusion attaches to the uploaded common-calendar construction: every sufficiently late actual inner minimizer has the singleton-mass bound **before** calendar selection or weight transport. Its existing same-profile/same-weight conclusions survive unchanged. Along a subsequence, one fixed owner has total singleton mass at least \(\kappa/4\). No fixed stopping date or counterfactual singleton mass is being asserted. 

## 5. A quantitative consequence: the unit-cube gap is below \(1/3\)

A further full-prefix calculation strengthens the supplied \(m<1/2\) restriction.

At any positive MAX-minimum, write

$$
d_i=m,\qquad L_i=B_i-s_i\ge m.
$$

Prefix one product root with small hazards

$$
q_i(t)=t/L_i.
$$

Since every \(B_i>s_i\), all complete-cap branches remain Continue for sufficiently small \(t\). The exact prefix equations give

$$
d_i(t)
=m+t\left(1-m\sum_j\frac1{L_j}\right)+O(t^2).
$$

If the common linear coefficient were negative, every debt would decrease. Therefore

$$
\boxed{\sum_i\frac{m}{B_i-s_i}\le1.}
$$

In particular, every \(L_i>m\), so **every** positive MAX-minimum satisfies \(U_i>s_i\).

For four players with rewards in \([-1,1]\), let \(a=\max_i s_i\). All Never cannot attain a positive minimum, so \(a>m\). For an owner attaining \(a\),

$$
L_i\le1-a<1-m,
$$

while the other three margins are at most two. Consequently

$$
\frac{m}{1-m}+\frac{3m}{2}<1,
$$

which gives

$$
\boxed{\eta(r)<\frac13.}
$$

Compactness also makes the worst value over the entire unit reward cube strictly below \(1/3\). This remains a positive-error bound, not an equilibrium-existence proof.

## What has been removed—and what remains

The remaining task is no longer obliged to handle a zero-singleton minimum law, an opposed three-sure root, or a two-sure root: **counterexample existence reduces to a rational generic singleton fiber where all those possibilities are separated from the minimum by a strict gap.**

The remaining source has uniformly positive **prescribed singleton mass**. Turning that mass into a full-regret improvement still requires controlling the other players’ caps after a response. The reduction does not supply that step.

The complete proof includes the coefficient construction, the fiber-uniform compactness argument, and exact boundary tests. The checker passed all 24 nonvanishing witnesses, 144 full-debt comparisons, 576 own-singleton invariance checks, and 18 exceptional tied-root tests. These are regression checks; the universal arguments are the proofs above. No independent review or Lean build was performed.

[Full mathematical proof](screened_root_reduction/GENERIC_SCREENED_ROOT_EXCLUSION_AND_SINGLETON_MASS_COLLAR.md) · [Proof, exact checker, and recorded results](GENERIC_SCREENED_ROOT_REDUCTION.zip)
