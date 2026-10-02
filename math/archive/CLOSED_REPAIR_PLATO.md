The missing issue is whether an optimal repair leaves another usable repair—not whether the LP computes its optimum correctly.

I found an exact obstruction with the required finite-menu provenance: **an optimal first pivot repair can enter a positive-regret family that no sequence of exploitability-nonincreasing unilateral replacements can leave.** This includes arbitrary infinite strategies, neutral changes of the pivot’s timing, and subsequent repairs of any player.

The table itself has an explicit equilibrium. Thus this refutes the proposed monotone repair mechanism, **not** the quitting-game conjecture. I have not established the general coordinated producer.

## 1. A source-derived, inescapable repair family

Consider the following canonical four-player table. Infinite all-Continue pays zero.

| Quitting coalition \(S\) | \(r(S)\)          |
| ------------------------ | ----------------- |
| \(\{0\}\)                | \((1,3,3,1)\)     |
| \(\{1\}\)                | \((-4,0,-2,-1)\)  |
| \(\{2\}\)                | \((2,2,0,-3)\)    |
| \(\{3\}\)                | \((3,-2,-2,0)\)   |
| \(\{0,1\}\)              | \((1,0,-2,-3)\)   |
| \(\{0,2\}\)              | \((0,-1,3,0)\)    |
| \(\{0,3\}\)              | \((1,2,3,-2)\)    |
| \(\{1,2\}\)              | \((-1,-1,1,1)\)   |
| \(\{1,3\}\)              | \((4,-4,-4,4)\)   |
| \(\{2,3\}\)              | \((-4,4,1,1)\)    |
| \(\{0,1,2\}\)            | \((-3,2,2,4)\)    |
| \(\{0,1,3\}\)            | \((4,-2,-3,-2)\)  |
| \(\{0,2,3\}\)            | \((-2,0,-3,2)\)   |
| \(\{1,2,3\}\)            | \((0,-4,-2,2)\)   |
| \(\{0,1,2,3\}\)          | \((-2,17,-9,-6)\) |

Its own singleton vector is \((1,0,0,0)\). Every player is punishment-normal: opponents playing Never give player \(i\) unrestricted cap \(\max\{r_i(\{i\}),0\}=r_i(\{i\})\).

Let \(G\) be **any probability distribution on the positive finite dates**

$$
\{1,2,\ldots\}.
$$

It may have unbounded support. Define

$$
\sigma^G_0=\frac12\delta_0+\frac14G+\frac14\delta_\infty,
\qquad
\sigma^G_j=\frac12\delta_0+\frac12\delta_\infty
\quad(j=1,2,3),
$$

and write

$$
\mathcal F=\{\sigma^G:G\text{ as above}\},
\qquad z=\frac3{32}.
$$

### Theorem

This table has the following properties.

**Exact source.** The law

$$
p_i=\frac12\delta_0+\frac12\delta_\infty
\qquad(i=0,1,2,3)
$$

is exact Nash on its actual displayed menu \(\{0,\mathrm{Never}\}\), and its unrestricted debt vector is

$$
d(p)=\left(\frac18,0,0,0\right).
$$

**Complete first repair.**

$$
\inf_{\tau_0}E_r(\tau_0,p_{-0})=\frac3{32},
$$

where \(\tau_0\) ranges over every behavioral strategy. Its minimizers are **exactly** the profiles in \(\mathcal F\).

**Closure under every non-increasing unilateral repair.** If \(\sigma\in\mathcal F\), \(\tau\) differs from \(\sigma\) in only one player’s strategy, and

$$
E_r(\tau)\le E_r(\sigma),
$$

then \(\tau\in\mathcal F\). More precisely, a nonpivot cannot change its law at all; the pivot can only change \(G\).

Every profile in \(\mathcal F\) has debt vector

$$
\boxed{d(\sigma^G)=\left(\frac3{32},\frac3{32},\frac3{32},\frac1{32}\right).}
\tag{1}
$$

Nevertheless, the same table has the exact terminal equilibrium

$$
T_0=0,\qquad T_1=T_2=T_3=\infty,
$$

with payoff \((1,3,3,1)\).

Thus the obstruction concerns a **complete repair rule**, not merely a numerical implementation or a restricted deviation class.

## 2. The source and its globally optimal pivot repair

At the source \(p\), each player’s two displayed actions have the same payoff:

$$
U(p)=\left(0,1,-\frac78,-\frac18\right).
$$

This verifies exact Nash on \(\{0,\mathrm{Never}\}\).

For nonpivots, every later finite date has the Never payoff because their own singleton rewards are zero. For the pivot, every positive finite date yields

$$
0+\Pr(T_1=T_2=T_3=\infty)=\frac18.
$$

Hence the source’s unrestricted debt is exactly \((1/8,0,0,0)\).

Now replace the pivot by an arbitrary law and write

$$
u=\Pr(T_0=0),\qquad
\lambda=\Pr(0<T_0<\infty),\qquad
\nu=\Pr(T_0=\infty).
$$

Then \(u+\lambda+\nu=1\). The pivot’s full cap remains \(1/8\), while its payoff is \(\lambda/8\). Its debt is therefore

$$
D_0=\frac{1-\lambda}{8}.
$$

Let \(N_j\) denote player \(j\)’s gain from switching to Never. Direct evaluation gives

$$
N_1=-\frac{13}{8}u+2\lambda+\frac{13}{8}\nu,
\qquad
N_2=u-\frac58\lambda-\nu.
$$

These three quantities satisfy the exact identity

$$
\boxed{
\frac34D_0+\frac{2}{21}N_1+\frac{13}{84}N_2=\frac3{32}.
}
\tag{2}
$$

The weights are positive and sum to one. Every term is bounded above by unrestricted exploitability, so (2) proves

$$
E_r(\tau_0,p_{-0})\ge\frac3{32}
$$

for **every** pivot strategy.

If equality holds, every positively weighted term in (2) must equal \(3/32\). Solving those equations yields

$$
u=\frac12,\qquad \lambda=\frac14,\qquad \nu=\frac14.
\tag{3}
$$

Thus every optimal repair must belong to the displayed family.

Conversely, every law satisfying (3) is optimal. The reason arbitrary late timing is harmless here is

$$
\begin{array}{c|ccc}
j&1&2&3\\ \hline
r_j(\{0\})&3&3&1\\
r_j(\{0,j\})&0&3&-2 .
\end{array}
$$

For each nonpivot, waiting for the pivot’s remaining finite singleton outcome dominates colliding with it or preempting it for a zero singleton payoff. Consequently, for every \(G\),

$$
U(\sigma^G)
=
\left(\frac1{32},\frac{35}{32},-\frac{25}{32},-\frac3{32}\right),
$$

$$
B(\sigma^G)
=
\left(\frac18,\frac{19}{16},-\frac{11}{16},-\frac1{16}\right).
$$

This proves (1) and completes the characterization of **all** optimal first repairs.

## 3. Why even neutral retiming cannot unlock another unilateral repair

The substantial point is closure for arbitrary \(G\). Checking one finite representative would not suffice.

Fix \(\sigma^G\in\mathcal F\), and let nonpivot \(j\) replace its law by an arbitrary stopping law \(\mu\). Independently draw

$$
S\sim G,\qquad T\sim\mu.
$$

Define five probabilities:

$$
\begin{aligned}
x&=\Pr(T=0),&
n&=\Pr(T=\infty),\\
a&=\Pr(0<S<T<\infty),&
b&=\Pr(0<S=T<\infty),&
c&=\Pr(0<T<S<\infty).
\end{aligned}
$$

Because \(G\) is finite-valued almost surely,

$$
x+n+a+b+c=1.
\tag{4}
$$

These five events capture every payoff comparison needed below. In particular, no bound on the support of \(G\) or \(\mu\) is imposed.

For the updated profile, use the following quantities:

$$
D_j=B_j-U_j,
$$

the mover’s full debt;

$$
H=U_0(G,\sigma_{-0})-U_0(\sigma),
$$

the pivot’s gain from replacing its entire law by \(G\);

$$
L=\lim_{t\to\infty}U_0(Q_t,\sigma_{-0})-U_0(\sigma),
$$

the limiting gain from a sufficiently late deterministic quit; and

$$
N_i=U_i(\mathrm{Never},\sigma_{-i})-U_i(\sigma).
$$

Here \(\sigma\) denotes the updated profile in these expressions. Every one of these quantities is at most \(E_r(\sigma)\). The limit defining \(L\) exists; it is the usual late-quitting payoff, including the singleton payoff on opponent-Never outcomes.

Conditioning on the five events in (4) gives the following identities.

### Replacement by player 1

$$
\boxed{
\frac{29}{38}D_1+
\frac{51}{380}H+
\frac9{380}L+
\frac3{38}N_2
=
\frac3{32}+\frac9{76}b.
}
\tag{5}
$$

### Replacement by player 2

$$
\boxed{
\frac{91}{106}D_2+
\frac3{53}L+
\frac9{106}N_1
=
\frac3{32}+\frac{15}{848}a+\frac9{53}c.
}
\tag{6}
$$

### Replacement by player 3

$$
\boxed{
\frac7{10}L+
\frac{11}{40}N_1+
\frac1{40}N_2
=
\frac3{32}+\frac{29}{160}a+\frac{21}{128}b.
}
\tag{7}
$$

Each left-hand side is a convex combination of actual deviation gains or full debt. Each right-hand side is at least \(3/32\). Thus no nonpivot replacement reduces exploitability.

More importantly, the equality cases force the original law.

For player 1, equality in (5) gives \(b=0\), and all four positively weighted gains equal \(z\). Their payoff formulas give

$$
D_1=\frac3{16}(x+c),
\qquad
H-L=\frac54a.
$$

Hence \(x+c=1/2\), \(a=0\), and \(n=1/2\). Under these restrictions,

$$
N_2=z+\frac12c,
$$

so \(c=0\), and therefore \(x=n=1/2\).

For player 2, equality in (6) gives \(a=c=0\). Then

$$
D_2=\frac3{16}x=z
$$

forces \(x=1/2\). Substituting \(n=1/2-b\) into \(L=z\) gives

$$
L=z+\frac3{16}b,
$$

so \(b=0\) and \(n=1/2\).

For player 3, equality in (7) gives \(a=b=0\). The equalities \(L=N_1=z\) reduce to

$$
5x+3c=\frac52,\qquad
15x+7c=\frac{15}{2}.
$$

Thus \(c=0\) and \(x=n=1/2\).

In every case,

$$
a=b=c=0,\qquad x=n=\frac12.
$$

Since \(a+b+c\) is the mover’s entire positive finite stopping probability, its law is literally unchanged:

$$
\mu=\frac12\delta_0+\frac12\delta_\infty.
$$

For a pivot replacement, (2)–(3) already show that preserving \(E\le z\) forces membership in \(\mathcal F\). This proves the closure theorem.

### Infinite iteration does not fix this

Every actual stage of an exploitability-nonincreasing unilateral repair sequence remains in \(\mathcal F\). Neutral pivot moves may send some of its positive finite mass to later and later dates, but they cannot change the other three laws.

In a weak limit, the pivot retains mass \(1/2\) at date zero, and its positive finite mass can only decrease from \(1/4\). If that limiting finite mass is \(\lambda\le1/4\), its actual debt is

$$
\frac{1-\lambda}{8}\ge\frac3{32}.
$$

Thus passing to a limiting stopping law does not produce an equilibrium either.

## 4. The game has an equilibrium outside the repair family

Let the pivot Quit at date zero and all other players play Never. The payoff is

$$
r(\{0\})=(1,3,3,1).
$$

The nonpivots’ date-zero joining payoffs are respectively

$$
0,\quad 3,\quad -2,
$$

so none improves. Later deviations cannot affect the already completed game.

The pivot obtains \(1\). Against three Never opponents, quitting at any later finite date also gives \(1\), and Never gives zero.

Hence this is an exact terminal Nash profile, directly yielding the uniform payoff \((1,3,3,1)\).

**The example therefore has zero global exploitability infimum.** It is not a positive-minimum hard residual. What it shows is that canonical normalization, punishment normality, an exact finite-menu source, and globally optimal full-strategy coordinate repairs do **not** by themselves supply a renewable descent argument.

## Consequence for the current proof effort

The proposed renewal statement must allow something stronger than “repair one player without increasing the maximum debt.” Even choosing among all optimal repairs and using neutral timing changes is insufficient.

This does **not** rule out coordinated replacements, or unilateral implementations of coordinated changes with controlled temporary increases. Those remain compatible with the approximate nature of the original packet target. What remains unproved is a theorem producing such changes from the hard residual with a budget or rank that can be renewed indefinitely.

The identities and equality-case calculations above have been checked with exact rational arithmetic:

[Exact verifier](sandbox:/mnt/data/ue_repair_work/verify_closed_repair_plateau.py) · [Verification output](sandbox:/mnt/data/ue_repair_work/closed_repair_plateau_checks.json)

This is a mathematical proof with an exact-arithmetic check, not a Lean-checked result under the runbook’s proof-closure standard. 
