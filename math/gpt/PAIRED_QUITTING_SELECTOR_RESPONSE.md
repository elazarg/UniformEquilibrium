I obtained an **explicit simultaneous selector for an asymmetric open reward region outside product-low**, including canonical \((1,0,0,0)\) tables. Its finite approximants preserve all four response caps exactly.

This is a class-level result, not a solution of arbitrary Fin4. Alternating pairs themselves already occur in the repository; the result below is an explicit reward-region producer and its complete-regret calculation, not a claim to have invented that mechanism.

## 1. A reward region with simultaneous selection

Partition the players into

$$
A=\{0,2\},\qquad B=\{1,3\}.
$$

For player \(i\), write \(j\) for its partner and \(\{k,l\}\) for the other pair. Define

$$
s_i=r_i(\{i\}),\quad b_i=r_i(\{j\}),\quad
P_i=r_i(\{i,j\}),
$$

$$
a_{ik}=r_i(\{k\}),\quad a_{il}=r_i(\{l\}),\quad
d_i=r_i(\{k,l\}).
$$

Assume, independently for every player,

$$
\begin{aligned}
&\frac9{10}\le s_i\le\frac{11}{10},\\
&-\frac1{10}\le b_i,d_i\le\frac1{10},\\
&\frac{19}{10}\le P_i,a_{ik},a_{il}\le\frac{21}{10},
\end{aligned}
\tag{1}
$$

and

$$
r_i(\{i\}\cup T)\le s_i+\frac1{50}
\qquad
(\varnothing\ne T\subseteq\{k,l\}).
\tag{2}
$$

**All other reward coordinates are arbitrary.** There is no symmetry assumption. Strict versions of these inequalities describe a nonempty open subset of the sixty-dimensional reward space.

### Theorem

Every table satisfying (1)–(2) has an exact terminal behavioral Nash equilibrium, at every live suffix, with this schedule:

* At even dates, only \(A\) mixes.
* At odd dates, only \(B\) mixes.

Each player uses one fixed Quit probability

$$
\frac1{100}<q_i<\frac12
$$

on its active dates. The randomizations are independent. The same profile delivers a uniform-equilibrium payoff.

Here is the simultaneous construction.

### Four equations, solved together

For player \(i\), put \(h=q_j\) and define

$$
X_i=s_i+h(P_i-s_i),
\qquad
Y_i=\frac{X_i-hb_i}{1-h}
=s_i+\frac{h(P_i-b_i)}{1-h}.
\tag{3}
$$

These are the proposed values at its active and inactive phases. For the opposite pair, put

$$
R_i(u,v)=u(1-v)a_{ik}+(1-u)v a_{il}+uvd_i,
\quad
c(u,v)=(1-u)(1-v).
$$

The remaining Bellman equation is

$$
H_i(q):=Y_i-R_i(q_k,q_l)-c(q_k,q_l)X_i=0.
\tag{4}
$$

Let \(p\) be the partner involution. Apply Poincaré–Miranda to

$$
F_j(q)=H_{p(j)}(q)
$$

on \([1/100,1/2]^4\). The partner relabeling matters: the face coordinate in \(H_i\) is \(q_j\), not \(q_i\). The rectangular zero theorem is already available in `MathUE/Topology/RectangularPoincareMiranda.lean`.

The required face signs hold uniformly:

$$
\sup_{q_j=1/100}H_i(q)
\le-\frac{29689}{9000000}<0,
\tag{5}
$$

$$
\inf_{q_j=1/2}H_i(q)
\ge\frac{1913}{2000}>0.
\tag{6}
$$

These are finite rational calculations, not numerical optimization. For fixed \(h\), the expression is affine separately in the six reward inputs and bilinear in \((q_k,q_l)\), so extrema occur at rectangle vertices. The accompanying checker evaluates all 512 relevant rational corner values.

Consequently, **one interior vector \(q\) satisfies all four equations (4)**. No player is repaired after the others’ incentives have been established.

### Why these equations give unrestricted Nash

At player \(i\)’s active phase, forced Quit pays \(X_i\). Forced Continue followed by the prescribed continuation pays

$$
q_jb_i+(1-q_j)Y_i=X_i.
$$

Thus both actions are tied.

At its inactive phase, Continue pays \(Y_i\), by (4). Forced Quit pays at most

$$
s_i+\frac1{50}\bigl(1-c(q_k,q_l)\bigr)
\le s_i+\frac3{200}.
$$

But (1) and (3) give

$$
Y_i-s_i\ge\frac1{55}.
$$

Therefore Continue is strictly better by at least

$$
\frac1{55}-\frac3{200}=\frac7{2200}>0.
\tag{7}
$$

This verifies both actions for every player at both phases. It remains to discharge the infinite tail, rather than silently restricting deviations to stationary ones.

Against an arbitrary deviation by \(i\), its opponents’ survival through one complete period is

$$
D_i=\prod_{j\ne i}(1-q_j)\le(99/100)^3<1.
$$

The probability of reaching \(K\) periods is therefore at most \(D_i^K\), irrespective of the deviator’s stopping law. Iterating the action inequalities and letting \(K\to\infty\) controls every privately randomized, unbounded deviation, including Never.

The initial payoff is

$$
v_i=
\begin{cases}
X_i,&i\in A,\\
Y_i,&i\in B.
\end{cases}
\qquad
s_i\le v_i\le\frac{21}{10}.
\tag{8}
$$

Uniformity also follows directly. If rewards are bounded by \(M\), expected absorption time against every unilateral deviation is uniformly bounded by

$$
\frac{2}{1-(99/100)^3}.
$$

Hence finite-average deviation gains are bounded by

$$
\frac{4M}{H\bigl(1-(99/100)^3\bigr)}
$$

at horizon \(H\), while prescribed averages converge to the fixed vector \(v\).

## 2. Exact finite-law selection—not payoff-only compression

Let

$$
C=\prod_i(1-q_i).
$$

Keep \(K\ge1\) complete periods and censor every later stopping outcome to Never. Explicitly, for \(0\le m<K\),

$$
\Pr(T_i=2m)=q_i(1-q_i)^m\quad(i\in A),
$$

$$
\Pr(T_i=2m+1)=q_i(1-q_i)^m\quad(i\in B),
$$

and

$$
\Pr(T_i=\mathrm{Never})=(1-q_i)^K.
$$

Call the resulting independent finite profile \(\sigma^K\).

Then the following identities hold **exactly**:

$$
\boxed{
U_i(\sigma^K)=(1-C^K)v_i,\qquad
B_i(\sigma^K)=v_i,\qquad
d_i(\sigma^K)=C^K v_i.
}
\tag{9}
$$

In particular,

$$
E(\sigma^K)\le\frac{21}{10}(99/100)^{4K}.
\tag{10}
$$

The payoff identity follows from periodic renewal: the discarded suffix has joint probability \(C^K\) and conditional payoff \(v\).

The cap identity requires more care. A pure deviation before the cutoff has exactly its original payoff, at most \(v_i\). A late finite deviation receives \(s_i\) on the opponents’ survival event; Never receives zero there. Both are dominated by the original-game deviation that waits until the cutoff and then resumes the equilibrium continuation, because \(v_i\ge s_i\ge0\). Finally, quitting at the first active date attains \(v_i\), and truncation does not change that payoff.

Thus **every unrestricted cap stays fixed**. The finite profile’s entire incentive loss is the explicitly removed payoff \(C^K v\).

### An exact pivot best response with controlled spillover

There is also a particular repair that makes the pivot exactly optimal.

Move player \(0\)’s remaining Never mass to its last active date, \(2K-2\). Equivalently, replace only its last active hazard by \(1\). All those active dates are best-response dates against the finite opponent laws, so the repaired profile \(\widetilde\sigma^K\) satisfies

$$
d_0(\widetilde\sigma^K)=0.
$$

Other players’ caps need not stay fixed. However, for \(i\ne0\), a deviation payoff can change only when the pivot had originally selected Never and the other two opponents survive the preceding \(K-1\) periods. This event has probability at most

$$
(1-q_0)D_i^{K-1}\le(99/100)^{3K-2}.
$$

Coupling both prescribed and deviating payoffs therefore gives

$$
\boxed{
E(\widetilde\sigma^K)
\le C^K\max_i v_i+4M(99/100)^{3K-2}.
}
\tag{11}
$$

This handles the cap-increase issue for the **selected late repair**. It makes no assertion that arbitrary best-response replacements are safe.

## 3. The canonical single-pivot selection problem

Transform the terminal rewards by

$$
\widehat r_0(S)=\frac{r_0(S)}{s_0},
\qquad
\widehat r_i(S)=r_i(S)-s_i\quad(i\ne0),
\tag{12}
$$

leaving Never equal to zero. Own-singleton rewards become \((1,0,0,0)\).

The Never convention prevents treating (12) as an unrestricted affine transformation of every profile. The construction avoids that mistake: **against the infinite periodic profile, every unilateral deviation absorbs almost surely**, so affine transport is valid for precisely the prescribed and deviating payoffs needed to verify its equilibrium.

Its transformed payoff is

$$
\widehat v_0=v_0/s_0,\qquad
\widehat v_i=v_i-s_i\quad(i\ne0),
$$

with

$$
\widehat v_i\ge\widehat s_i\ge0,
\qquad
\max_i\widehat v_i\le\frac53.
$$

Apply the truncation argument directly in the transformed game. It gives

$$
\widehat B_i(\sigma^K)=\widehat v_i,
\qquad
\widehat d_i(\sigma^K)=C^K\widehat v_i,
$$

and hence

$$
\boxed{
\widehat E(\sigma^K)\le\frac53(99/100)^{4K}.
}
\tag{13}
$$

Therefore, choose the three nonpivot laws displayed above. Their optimal full-regret pivot-repair value is bounded by (13), since the displayed pivot law is a feasible competitor. This supplies the opponent selection, not merely the inner LP reduction already in the repository.

Fixing the original \(s_i=1\) and taking strict inequalities in the other coordinates gives an open region in the canonical 56-dimensional single-pivot space.

## 4. Separation and a concrete rational selector

Every table in this class fails product-low. Activate only one pair, with both hazards positive. For either active player,

$$
Q_i=s_i+q_j(P_i-s_i)>s_i.
$$

Thus the root has positive absorption and **neither active quitter is low**. The class is outside the hypothesis of the existing product-low theorem; this is not a claim that it lies outside every other known solved class.

At the symmetric reference point

$$
s_i=1,\quad b_i=d_i=0,\quad P_i=a_{ik}=a_{il}=2,
$$

with the off-phase Quit rewards bounded by \(1\), equal hazards solve

$$
q^3-6q^2+8q-1=0,
\qquad
q\approx0.13919414688829662.
$$

There is also an **entirely rational finite selector**, without pretending a rounded root is exact. Take

$$
q=\frac{139194147}{10^9},\qquad K=30.
$$

For the canonically transformed reference family, these are thirty finite atoms per player on a common sixty-date menu, plus Never.

Writing \(\eta=\max_i|H_i|\), a residual version of the proof gives

$$
E(\sigma^K)\le
C^K V+\frac{\eta}{1-C}
+\frac{\eta}{\min_i(1-D_i)}.
\tag{14}
$$

The checker evaluates this bound with exact rational arithmetic. For the displayed selector it is less than

$$
1.817\times10^{-8}<10^{-6}.
$$

That sixty-date statement concerns the reference family, not the entire surrounding reward box.

The construction also extends to **any even number of players at least four**, cycling through disjoint pairs under the corresponding pairwise reward conditions. The attached proof supplies the simultaneous-zero and all-phase incentive arguments.

## Proof and verification

[Full mathematical proof and exact-arithmetic checker](paired_quitting_selector.zip)
[Read the proof separately](PAIRED_QUITTING_SELECTOR.md)

The checks comprise 512 exact rational face evaluations, the exact rational reference-selector bound, and numerical regressions on 100 independently perturbed asymmetric tables. The numerical regressions tested unrestricted periodic caps, finite-cap identities, and the selected pivot repair; they are not the existence proof.

**This is ordinary mathematics with executable checks, not a Lean-checked result.** No Lean compilation, axiom audit, or repository change was performed. 

The remaining limitation is substantive: the pairing and reward inequalities are inputs. Nothing here yet produces such a structure—or a different simultaneous selector—from an arbitrary normalized table.
