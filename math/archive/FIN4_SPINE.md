## Result

The following stronger theorem closes **equivalent output 4**.

### Normal unique-persistent-spine theorem

Let (I) be any finite player set, let (r) be a bounded quitting reward table, and let ((v_t,x_t)_{t\ge 0}) be an exact bounded Nash–Bellman spine. Write

[
q_{t,i}:=x_{t,i}(Q).
]

Suppose there is a player (p) such that

[
\sum_{t=0}^{\infty}q_{t,p}=\infty,
\qquad
\sum_{t=0}^{\infty}q_{t,j}<\infty
\quad(j\ne p),
\tag{1}
]

and suppose (p) is punishment-normal:

[
\operatorname{Pun}_p(r)\le r_p({p}),
\tag{2}
]

where (\operatorname{Pun}_p(r)) is the full behavioral punishment value.

Then

[
\boxed{r({p})\text{ is a uniform-equilibrium payoff}.}
\tag{3}
]

Consequently, on the four-player no-uniform-payoff branch, **no exact bounded Nash–Bellman spine can have exactly one persistent player**. Indeed, the checked Fin4 hard residual makes every player punishment-normal.

This proves the requested one-persistent incompatibility.

---

## 1. A uniquely persistent spine converges to its singleton row

Put

[
R:=r({p})\in\mathbb R^I.
]

Choose (K>0) bounding every coordinate of every (v_t) and every terminal reward. Define

[
s_t:=\sum_{j\ne p}q_{t,j},
\qquad
a_t:=\prod_{j\ne p}(1-q_{t,j}),
\qquad
c_t:=1-a_t.
]

Because the outsider hazard streams are summable,

[
\sum_t s_t<\infty.
\tag{4}
]

The union bound gives

[
0\le c_t\le s_t,
\qquad
\sum_t c_t<\infty.
\tag{5}
]

Separate the Bellman expectation according to whether some outsider (j\ne p) quits at date (t). On the event that no outsider quits:

* if (p) quits, the payoff is (R);
* if (p) continues, the payoff is (v_{t+1}).

Thus there is a vector (G_t), representing the unnormalised payoff contribution of outcomes containing an outsider, such that

[
v_t
===

a_t\bigl((1-q_{t,p})v_{t+1}+q_{t,p}R\bigr)+G_t,
\tag{6}
]

with

[
|G_t|_\infty\le Kc_t.
\tag{7}
]

Writing (d_t=v_t-R), equation (6) becomes

[
d_t
===

a_t(1-q_{t,p})d_{t+1}+e_t,
\qquad
e_t:=G_t-c_tR.
\tag{8}
]

Hence

[
|e_t|_\infty\le 2Kc_t.
\tag{9}
]

Iterating from (t) to (T),

[
d_t
===

\left(\prod_{u=t}^{T-1}a_u(1-q_{u,p})\right)d_T
+
\sum_{s=t}^{T-1}
\left(\prod_{u=t}^{s-1}a_u(1-q_{u,p})\right)e_s.
\tag{10}
]

The leading product vanishes, because

[
\prod_{u=t}^{T-1}a_u(1-q_{u,p})
\le
\prod_{u=t}^{T-1}(1-q_{u,p})
\le
\exp\left(-\sum_{u=t}^{T-1}q_{u,p}\right)
\longrightarrow 0.
\tag{11}
]

Using boundedness of (d_T), then sending (T\to\infty), gives the quantitative tail estimate

[
\boxed{
|v_t-R|*\infty
\le
2K\sum*{s=t}^{\infty}c_s
\le
2K\sum_{s=t}^{\infty}s_s.
}
\tag{12}
]

In particular,

[
v_t\longrightarrow R.
\tag{13}
]

This is the key use of persistence: the owner clock kills the bounded terminal term in (10), while the summable outsider clocks make the perturbations summable.

---

## 2. Reproject late spine rows onto one actual solo root

There are infinitely many (t) with (q_{t,p}>0), by (1). For each such (t), define the actual solo product root (y_t) by

[
y_{t,p}:=x_{t,p},
\qquad
y_{t,j}:=C
\quad(j\ne p).
\tag{14}
]

Thus only the fixed owner (p) has a positive Quit probability in (y_t).

Fix an outsider (i\ne p). Let (A_{t,i}) be (i)'s payoff from quitting immediately against (y_t). Explicitly,

[
A_{t,i}
=======

(1-q_{t,p})r_i({i})
+
q_{t,p}r_i({i,p}).
\tag{15}
]

The exact Nash property of (x_t), tested against the pure deviation (Q), gives

[
U_i(x_t[i\leftarrow Q];v_{t+1})
\le
U_i(x_t;v_{t+1})
================

v_{t,i},
\tag{16}
]

where the equality is the exact Bellman identity.

Couple (x_t[i\leftarrow Q]) with (y_t[i\leftarrow Q]), keeping (p)'s action and (i)'s forced Quit action identical. They differ only if some player (j\notin{p,i}) quits. The probability of that event is at most (s_t). Since all rewards are bounded by (K),

[
\left|
U_i(x_t[i\leftarrow Q];v_{t+1})-A_{t,i}
\right|
\le 2Ks_t.
\tag{17}
]

Combining (16), (17), and (13),

[
A_{t,i}
\le
v_{t,i}+2Ks_t
\le
R_i+\eta_t,
\tag{18}
]

where

[
\eta_t:=|v_t-R|_\infty+2Ks_t
\longrightarrow 0.
\tag{19}
]

Now consider the stationary profile that repeats (y_t) forever. Because (q_{t,p}>0), (p) eventually quits with probability one. Against this stationary solo profile, an outsider (i)'s unrestricted behavioral cap is exactly

[
B_i(y_t)=\max{R_i,A_{t,i}}.
\tag{20}
]

Indeed, continuing until (p) quits gives (R_i), while quitting at any live date gives the same memoryless immediate-Quit value (A_{t,i}); arbitrary randomized stopping laws only mix these alternatives. Therefore

[
\boxed{
B_i(y_t)\le R_i+\eta_t
\qquad(i\ne p).
}
\tag{21}
]

This is a full stopping-law cap, not a one-stage or stationary-deviation cap.

---

## 3. Finite solo prefix followed by an actual punishment

Fix (\varepsilon>0). Choose a sufficiently late (t) with

[
q:=q_{t,p}>0,
\qquad
\eta_t<\frac{\varepsilon}{3}.
\tag{22}
]

By punishment-normality, choose an actual behavioral punishment profile (\pi) satisfying

[
B_p(\pi)
\le
\operatorname{Pun}_p(r)+\delta
\le
R_p+\delta,
\qquad
0<\delta<\frac{\varepsilon}{3}.
\tag{23}
]

Choose (N) sufficiently large that

[
4K(1-q)^N<\frac{\varepsilon}{3}.
\tag{24}
]

Construct the literal behavioral profile (\sigma) that:

1. repeats the solo product root (y_t) for (N) live dates;
2. conditional on surviving those dates, switches to (\pi).

Let

[
\rho:=(1-q)^N
\tag{25}
]

be the probability that (p) survives the solo prefix.

### Prescribed payoff

Whenever (p) quits during the prefix, the terminal coalition is exactly ({p}), so the payoff is (R). Only the event of reaching the punishment tail can alter the payoff. Hence

[
\boxed{
|U_i(\sigma)-R_i|\le 2K\rho
\quad\text{for every }i.
}
\tag{26}
]

Thus the target is the fixed vector (R=r({p})), independently of (\varepsilon).

### Outsider deviations

Let (i\ne p), and let (\tau_i) be any behavioral stopping law, including Never or an arbitrarily late randomized stopping time.

Compare the deviation against (\sigma) with the same deviation against the infinite stationary solo profile (y_t^\infty). Before date (N) the two environments are identical. They can differ only if (p) survives the entire prefix, an event of probability at most (\rho), even under (i)'s deviation. Therefore

[
U_i(\sigma[i\leftarrow\tau_i])
\le
U_i(y_t^\infty[i\leftarrow\tau_i])+2K\rho
\le
R_i+\eta_t+2K\rho.
\tag{27}
]

Using (26),

[
U_i(\sigma[i\leftarrow\tau_i])-U_i(\sigma)
\le
\eta_t+4K\rho
<
\frac{2\varepsilon}{3}.
\tag{28}
]

This treats all finite and infinite stopping laws simultaneously.

### The owner’s deviations

Let (\tau_p) be any behavioral stopping law for (p).

* If (p) quits during the solo prefix, its payoff is (R_p).
* If (p) reaches the tail, its continuation strategy is an arbitrary deviation against (\pi), and is therefore worth at most (R_p+\delta) by (23).

Consequently,

[
U_p(\sigma[p\leftarrow\tau_p])\le R_p+\delta.
\tag{29}
]

Together with (26),

[
U_p(\sigma[p\leftarrow\tau_p])-U_p(\sigma)
\le
\delta+2K\rho
<
\frac{\varepsilon}{2}.
\tag{30}
]

In particular, the potentially problematic deviation Never is covered: it reaches the actual punishment rather than retaining a phantom continuation value.

Thus (\sigma) is an (\varepsilon)-Nash profile against every behavioral unilateral replacement, and its payoff is (o(1))-close to the fixed vector (R). Since this works at every positive accuracy, the terminal-Nash-to-uniform consumer gives

[
(quittingGame(r)).\operatorname{IsUniformEquilibriumPayoff}(R).
\tag{31}
]

The checked solo-cap construction `quittingStationarilyGeneratedApproximateEquilibria_of_approximate_solo_caps` implements exactly this finite-prefix/punishment argument, with unrestricted time-dependent hazards, and the stationarily-generated consumer converts the resulting profiles to a uniform-equilibrium payoff.

A tempting shortcut would be to declare (y_t^\infty) itself an exact stationary equilibrium. That is not valid when (R_p<0), because (p) may prefer Never. Root Nash plus Bellman is only a local assertion; the repository contains this precise local/global warning. The punishment seam above is essential.

---

## 4. Fin4 hard-residual consequence

Assume now (I=\operatorname{Fin}4) and that no uniform-equilibrium payoff exists.

The checked Fin4 reduction supplies

[
H:\operatorname{FinFourQuantitativeFullSupportHardResidual}(r,K),
]

and in particular

[
H.\mathrm{all_punishmentNormal}:
\forall p,\
\operatorname{Pun}_p(r)\le r_p({p}).
\tag{32}
]

Suppose an exact bounded Nash–Bellman spine had exactly one persistent player (p). The theorem above, applied with (32), would make (r({p})) a uniform-equilibrium payoff, contradicting the premise. Therefore

[
\boxed{
\text{no uniform-equilibrium payoff}
\Longrightarrow
\text{no exact bounded spine has exactly one persistent player}.
}
\tag{33}
]

Equivalently, under the no-uniform-payoff hypothesis, every exact bounded spine has either

[
0\quad\text{or}\quad\text{at least }2
]

persistent labels.

This is stronger than merely excluding a particular source-selected one-persistent spine: it excludes **every** one-persistent exact bounded spine for that table.

It also respects the boundary regression. A game with an easy equilibrium may still possess a one-persistent phantom spine; the theorem merely reconstructs a uniform payoff from it when its persistent owner is punishment-normal. It does not assert that the phantom spine itself acquires a second clock.

---

## 5. Effect on the requested selector

The one-persistent alternative is now completely consumed. Hence any source-selection theorem that provides an exact bounded spine with at least one persistent coordinate automatically provides two fixed persistent labels:

[
\text{nonzero persistent set}
\quad+\quad
\text{not singleton}
\quad\Longrightarrow\quad
\exists p\ne q:
\sum_tq_{t,p}=\sum_tq_{t,q}=\infty.
\tag{34}
]

These are fixed labels on the same literal root sequence, not labels chosen blockwise.

The existing path theorem then gives every deleted-player survival limit and the joint-survival limit on every suffix from those two marginal streams.  The exact Nash–Bellman adapter supplies zero candidate debt, zero prescribed discrepancy, and zero adverse forcing, yielding the chronological debt-shadowing certificate.

Thus the boxed selector has been reduced to one sharply isolated issue:

[
\boxed{\text{select an exact source spine whose persistent set is nonempty}.}
]

The one-persistent branch is no longer live. The only remaining phantom obstruction is the genuinely zero-persistent, all-Continue-type spine.

---

## Lean status

The strategic consumers used in Step 3 and the Fin4 normality implication are already checked. The new mathematical content to formalize consists of three local adapters:

1. the quantitative singleton-tail estimate (12);
2. the solo-reprojection cap estimate (21);
3. their instantiation of `quittingStationarilyGeneratedApproximateEquilibria_of_approximate_solo_caps`.

I inspected these against repository head `28031be6ac28a56d1df72261f448c67f52e54bbb`, but the three new lemmas have not yet been entered or compiled in Lean. Under the repository’s validation discipline, this is therefore a complete mathematical proof of output 4, not yet a machine-checked closure claim. 
