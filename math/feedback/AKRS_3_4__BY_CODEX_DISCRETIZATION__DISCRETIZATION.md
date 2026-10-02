# Independent audit of the AGKRS discretization arm

## Claim audited

Let $I$ be finite, let all terminal rewards have absolute value at most $R$,
and let $\pi$ be a sequentially zero-perfect absorption path with no terminal
jump.  The claim is that the particular discretizations constructed in the
proof of AGKRS Proposition 4.8 are absorbing profiles $x^k$ for which every
row is $\eta_k$-perfect, with one error $\eta_k\to0$ uniform over every
calendar stage.

This is the S.3 conclusion only.  It does not assert that sequential
perfection by itself implies approximate Nash, and it does not use the
printed Theorem 3.5.

## Verdict

The claim is correct, provided the discretization uses the particular
support-preserving product witness constructed in Lemma 4.9.  The published
coordinate estimate by itself is insufficient, because an arbitrary nearby
product row could introduce a tiny positive Quit probability at a coordinate
whose singleton path mass is zero.  Such a new support action would activate
the lower perfection inequality without providing an indifference witness.

For the actual Lemma 4.9 witness, an explicit uniform bound is available.  If
$d=|I|$ and

$$
K_d=2^d(2^d-1),
$$

then, after increasing the first admissible resolution if necessary, one may
take

$$
\eta_k\le \frac{R(12+2K_d)}{k}.
$$

The numerical constant is deliberately loose.  Its useful features are that
it is independent of the block and stage, and that it tends to zero.

## 1. Exact support information in Lemma 4.9

Consider a small cell of the Proposition 4.8 partition.  Let $y$ be its
correlated one-row law, including all-Continue, and put

$$
p=1-y(\mathbf C)\le \frac1k.
$$

Lemma 4.9 constructs a product row $\xi$ with the same absorption
probability $p$.  Its proof gives more than the displayed approximation:

$$
\xi_i>0
\quad\Longleftrightarrow\quad
y(Q^i,C^{-i})>0,
\qquad
\xi_i<1.
\tag{1}
$$

Indeed, if $y(Q^i,C^{-i})=0$, the collision hypothesis forces every outcome
in which $i$ Quits to have zero $y$-mass.  The construction sets $\xi_i=0$
and applies the positive-coordinate construction to the remaining active
players.  Conversely, when all retained singleton coordinates are positive,
Step 3 of the vector-field proof forces every corresponding $\xi_i$ to be
positive.  Finally $p<1$ implies $\xi_i<1$ for every player.  Thus Continue
is always in support, and Quit is in support exactly at the positive
singleton coordinates of the cell.

The zero-coordinate reduction is compressed into one sentence in the
published proof, but it is a finite induction on the active player set; no
new hypothesis is required.

## 2. A uniform continuation-payoff bound

The proof of Theorem 4.15 states the needed uniform continuation convergence.
It can also be read directly from Proposition 4.8.

For a small cell, Lemma 4.9 gives, for every nonabsorbing action excluded and
every nonempty quitting coalition $a$,

$$
|\xi(a)-y(a)|
\le 2^d\frac1k p.
$$

Hence the total variation contribution of that cell is bounded by

$$
\sum_{a\ne\mathbf C}|\xi(a)-y(a)|
\le \frac{K_d}{k}p.
\tag{2}
$$

Large-jump cells are copied exactly.  Both implementations have exactly the
same absorption probability in every cell, so they also have the same
cell-survival weights.  From the beginning of any cell $n$, if $w_{n,m}$ is
the conditional probability of surviving to cell $m$, absorption gives

$$
\sum_{m\ge n}w_{n,m}p_m=1.
$$

Summing (2) with these weights proves, simultaneously for every starting
cell,

$$
e_k:=\sup_n
\left\|\gamma_{n+1}(x^k)-\gamma_{\mathrm{post}(n)}(\pi)\right\|_\infty
\le \frac{RK_d}{k}.
\tag{3}
$$

This weighted tail sum is the reason weak convergence near clock time one
does not cause a denominator blow-up.  A bound only on cumulative path
coordinates would not by itself prove (3).

## 3. Copied large jumps

At a copied large jump, the discretized root is literally the path's jump
root.  The no-terminal-jump hypothesis ensures that the post-jump
continuation is genuine, so sequential zero-perfectness applies to that
root.  Replacing the path continuation by the actual continuation of $x^k$
perturbs a pure endpoint by at most $e_k$ and the mixed payoff by at most
$e_k$.  Every copied large-jump row is therefore $2e_k$-perfect.

The exclusion of terminal jumps is essential here: the definition of
zero-perfectness imposes no SP.1 condition on a jump that exhausts all
remaining mass.

## 4. Endpoint estimates on a small cell

Fix a small cell.  Let $\Gamma$ be the path payoff immediately before the
cell, let $W$ be its post-cell payoff, and let $V_i,Q_i,C_i$ be player $i$'s
mixed, Quit, and Continue payoffs for the product row $\xi$ followed by $W$.
The degenerate case $p=0$ uses the all-Continue row and follows directly from
SP.2(a), so the estimates below may be read with $p>0$.
Since the conditional absorption probability of the whole cell and of
$\xi$ is $p$,

$$
|\Gamma_i-W_i|\le2Rp,
\qquad
|V_i-W_i|\le2Rp,
\tag{4}
$$

and the probability that any opponent of $i$ Quits in $\xi$ is at most $p$.
Writing $a_i=r_i(Q^i,C^{-i})$, this yields

$$
|Q_i-a_i|\le2Rp,
\qquad
|C_i-W_i|\le2Rp.
\tag{5}
$$

In particular, the upper and lower support inequalities for Continue hold
with error $4Rp$.  Continue is in support by (1).

At the cell entrance, either the path is continuous or there is a small
jump.  In the continuous case SP.2(a) gives $a_i\le\Gamma_i$.  In the
small-jump case Continue is in the jump root's support, exact SP.1 makes it
optimal, and the jump Quit endpoint is within $2Rp$ of $a_i$.  Therefore in
both cases

$$
a_i\le\Gamma_i+2Rp.
\tag{6}
$$

Equations (4)--(6) imply the no-profitable-Quit inequality

$$
Q_i\le V_i+8Rp.
\tag{7}
$$

## 5. The lower support inequality for Quit

Assume $\xi_i>0$.  By (1), the cell contains positive singleton-$i$ path
mass.  There are two exhaustive origins.

### Discrete origin

Some small jump inside the cell has positive singleton-$i$ mass.  Player $i$
therefore uses Quit at that exact jump root.  The jump cannot be terminal and
SP.1 makes its Quit endpoint equal to its mixed payoff.  If $\rho$ is the
jump's conditional absorption probability, then

$$
\rho\le\frac{p}{1-p}\le2p.
$$

The first inequality follows because the remaining mass at any point of the
cell is at least $(1-p)$ times the mass at its entrance.  The jump Quit
endpoint is consequently within $4Rp$ of $a_i$, while the payoff before that
jump is within $2Rp$ of $\Gamma_i$.  Hence

$$
\Gamma_i\le a_i+6Rp.
\tag{8}
$$

### Continuous origin

The continuous singleton-$i$ coordinate has positive increment in some
continuous component of the cell.  On such a component the sum of all
singleton coordinates grows exactly at unit speed.  Each nonnegative
coordinate measure is therefore dominated by Lebesgue measure, so each
coordinate is one-Lipschitz there.  A positive increment supplies an interior
differentiability point at which its right derivative is positive.  SP.2(b)
then gives equality between the path payoff and $a_i$ at that point.  Moving
back to the cell entrance changes payoff by at most $2Rp$, so (8) again holds,
with room to spare.

Combining (4), (5), and (8) yields

$$
Q_i\ge V_i-12Rp.
\tag{9}
$$

Thus the product row is $12Rp$-perfect against the path continuation.

## 6. Replacement by the actual tail

Replacing $W$ by the actual post-cell continuation changes the Continue
endpoint and the mixed payoff by at most $e_k$ each; the Quit endpoint is
unchanged.  Equations (7)--(9) and the Continue estimates therefore show that
every small-cell row is

$$
\left(\frac{12R}{k}+2e_k\right)\text{-perfect}.
$$

Together with (3) and the large-jump estimate, every row of $x^k$ is
$\eta_k$-perfect for

$$
\eta_k
\le \frac{R(12+2K_d)}{k}
\longrightarrow0.
$$

Proposition 4.8 constructs $x^k$ to be absorbing.  Hence these are exactly
the absorbing, uniformly sequentially approximately perfect profiles needed
for literal S.3.

## Boundary tests and nonclaims

1. **Arbitrary approximation fails.**  The numerical estimate in Lemma 4.9
   permits an arbitrary approximant to give an inactive player a tiny positive
   Quit probability.  If Quit is substantially worse for that player, the
   lower support inequality then fails by order one.  The constructed witness,
   not merely the estimate, is required.
2. **Small jumps are not exact solo comparisons.**  At a small jump, SP.1
   compares the actual root endpoint with its mixed payoff.  Translating this
   to $a_i$ costs $O(Rp)$, as accounted for above.
3. **The estimate is uniform over stages.**  This comes from the weighted
   identity $\sum_m w_{n,m}p_m=1$, not merely from weak convergence of paths.
4. **No equilibrium claim is made here.**  The conclusion is sequential
   approximate perfection and absorption, precisely S.3.  Any conversion to
   another equilibrium notion is a separate theorem.

## Sources inspected

- Ashkenazi-Golan, Krasikov, Rainer, and Solan, *Absorption paths and
  equilibria in quitting games*, published Proposition 4.8, Lemma 4.9,
  Definition 4.13, and Theorem 4.15;
- `Literature/AshkenaziGolanKrasikovRainerAndSolan2022.lean`, especially its
  transcription of the absorption-path construction and its explicit record
  that the path decoder is not yet formalized there; and
- `UniformEquilibrium/Quitting/AbsorptionPath/ContinuousPath.lean`, for the
  repository definitions of path jumps, lower right derivative, and
  sequential perfection.
