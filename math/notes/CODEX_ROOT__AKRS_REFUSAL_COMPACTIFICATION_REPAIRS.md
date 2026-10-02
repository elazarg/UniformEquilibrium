# AGKRS refusal compactification: analytic repairs

## Status

This note supplies ordinary-mathematics repairs for the two objections in
`feedback/AGKRS_3_4__BY_CODEX_ROOT.md`.  It is not a Lean-checked result.

The setting is a finite quitting game with normalized never payoff zero and
reward bound $M$.  Let $x^k$ be $arepsilon_k$-equilibria against arbitrary
unilateral behavioral deviations, where $arepsilon_k\to0$.  Complete them
at late dates by forcing one fixed positive-solo player to Quit.  Let
$\bar x^k$ be the resulting absorbing profiles and suppose their absorption
paths converge weakly to $\pi$.  The completion changes terminal mass by
$\rho_k\to0$.

## 1. Continuous support equality without an atom-free neighborhood

Fix a player $i$ and a time $t\in T(\pi)\setminus\{1\}$.  Write

$$
a_i=r_i(\{i\}),\qquad g=\gamma_t^i(\pi)-a_i.
$$

Assume $g>0$ and that the lower right derivative of the singleton-$i$
coordinate at $t$ is positive.  We derive a contradiction.

Because $t\in T(\pi)$, the path has no jump at $t$, its total accumulated mass
there is $t$, and its payoff path is continuous at $t$.  Choose $h>0$ with
$t+h<1$ such that $t+h$ is not an atom of any path coordinate and

$$
|\gamma_u^i(\pi)-\gamma_t^i(\pi)|<g/8
\quad(t\le u\le t+h).
\tag{1}
$$

Shrink $h$ further until the total absorption mass

$$
m_J=\sum_S\bigl(\pi_{t+h}(S)-\pi_t(S)\bigr)
$$

is small enough that

$$
\frac{8Mm_J}{1-t-h}<g/8.
\tag{2}
$$

This is possible even if jumps accumulate at $t$: the finite absorption
measure has no atom at $t$, so $m_J\downarrow0$ as $h\downarrow0$.

Let $J=(t,t+h]$.  Weak convergence at its atom-free endpoints gives

$$
m_J^k:=\Pr_{\bar x^k}(\text{absorption clock lies in }J)
\longrightarrow m_J.
\tag{3}
$$

For a genuine source stage $n$ whose pre-stage absorption clock lies in $J$,
let $s_n^k$ be its reach, $p_n^k$ its conditional one-stage absorption
probability, $V_n^k$ its prescribed conditional payoff, and $Q_n^k$ player
$i$'s immediate-Quit payoff.  Then

$$
s_n^k\ge1-t-h,
\qquad
p_n^k\le \frac{m_J^k}{1-t-h}.
\tag{4}
$$

When player $i$ Quits, its payoff differs from $a_i$ only if some opponent
also Quits.  That event has probability at most $p_n^k$.  Hence

$$
|Q_n^k-a_i|\le2Mp_n^k.
\tag{5}
$$

The conditional payoff $V_n^k$ is the remaining reward moment divided by
$s_n^k$.  Anchor this quotient at clock $t$, where weak convergence and
continuity give convergence to $\gamma_t^i(\pi)$.  Moving the clock within
$J$ changes its numerator by at most $Mm_J^k$ and its denominator by at most
$m_J^k$; since every denominator is at least $1-t-h$, the elementary quotient
estimate gives, for all sufficiently large $k$,

$$
|V_n^k-\gamma_t^i(\pi)|
\le \frac{4Mm_J^k}{1-t-h}+o(1)<g/4
\tag{6}
$$

uniformly over all such stages.  Equations (2), (4), (5), and (6) imply

$$
V_n^k-Q_n^k\ge g/2
\tag{7}
$$

after shrinking $h$ once more if necessary.

Apply the refusal lemma to all genuine source dates whose clocks lie in $J$.
Finite exhaustion is legitimate because each finite refusal is one unilateral
behavioral strategy.  It yields

$$
\sum_{n:\,t_n^k\in J}s_n^kq_{i,n}^k
\le \frac{2\varepsilon_k}{g}.
\tag{8}
$$

The singleton-$i$ stage mass is

$$
s_n^kq_{i,n}^k\prod_{j\ne i}(1-q_{j,n}^k)
\le s_n^kq_{i,n}^k.
$$

The artificial completion changes total mass by at most $\rho_k$.  Therefore
the completed singleton measure of $J$ is at most

$$
\frac{2\varepsilon_k}{g}+\rho_k\longrightarrow0.
\tag{9}
$$

Weak convergence at the endpoints of $J$ gives zero limiting singleton mass
in $J$.  But positive lower right derivative at $t$ implies

$$
\pi_{t+h}(\{i\})-\pi_t(\{i\})>0
$$

for every sufficiently small positive $h$, a contradiction.  Consequently

$$
\dot\pi_t(\{i\})>0\Longrightarrow\gamma_t^i(\pi)=a_i.
$$

Together with the sure-Quit deviation inequality, this proves SP.2.

### Boundary test

A continuous point may be approached by jumps of sizes $2^{-2m}$ at times
$t+2^{-m}$.  No right neighborhood is atom-free, although its total mass
tends to zero with its length.  This falsifies the wording in the original
draft and is handled exactly by (2)--(4).

## 2. Uniform sequential perfection of the AGKRS discretization

Let $\pi$ be a zero-perfect absorption path with no terminal jump.  Apply the
published Proposition 4.8 discretization at resolution $k\ge2$.  Denote its
absorbing root sequence by $x^k$, its path cells by
$[s_n^k,s_{n+1}^k]$, and its uniform continuation-payoff error by $e_k\to0$.

Large jumps, whose conditional absorption is at least $1/k$, are copied
literally.  Since no jump is terminal, SP.1 applies.  Replacing the path
continuation by the actual discretized continuation perturbs each endpoint
and the mixed value by at most $e_k$.  Every copied row is therefore
$2e_k$-perfect.

Consider a small cell and write

$$
p=\frac{s_{n+1}^k-s_n^k}{1-s_n^k}\le\frac1k.
$$

Proposition 4.8 uses the support-preserving product witness constructed in the
proof of Lemma 4.9.  Its root $\xi$ has total absorption probability $p$, and

$$
\xi_i>0
\Longrightarrow
\text{the singleton-$i$ path coordinate has positive increment in the cell}.
\tag{10}
$$

Let $w$ be the actual post-cell continuation, and let $Q_i,C_i,V_i$ be the
Quit endpoint, Continue endpoint, and mixed-row value.  Since each marginal
Quit probability and the probability of any opponent Quit are at most $p$,

$$
|Q_i-a_i|\le2Mp,
\qquad
|C_i-w_i|\le2Mp,
\qquad
|V_i-w_i|\le2Mp.
\tag{11}
$$

In particular both the upper and support inequalities for Continue hold with
error $4Mp$, because $p<1$ makes Continue a support action for every player.

It remains to compare $a_i$ with $w_i$.

At the entrance of a small cell, one of two things happens.

- At a continuous path time, SP.2(a) gives $a_i\le\gamma^i$.
- At a small jump, SP.1 says that the actual Quit endpoint is no larger than
  the jump row value.  Since the jump's conditional absorption is below
  $1/k$, both are within $O(M/k)$ of $a_i$ and the post-jump path payoff,
  respectively.

Across any subinterval of the cell, at most conditional mass $p$ is removed.
The conditional reward quotient therefore changes by at most
$4Mp/(1-p)\le8Mp$ for $k\ge2$ (the case $k=2$ can be absorbed by increasing
the constant).  The actual tail adds $e_k$.  Thus

$$
a_i\le w_i+C_1Mp+e_k
\tag{12}
$$

for a universal numerical $C_1$.

If $\xi_i>0$, (10) supplies positive singleton-$i$ mass in the cell.  This
mass has one of two origins.

- Some small jump in the cell has positive singleton-$i$ mass.  Then player
  $i$ uses Quit at that jump, and the lower support clause of SP.1 gives the
  reverse inequality between its jump row value and Quit endpoint.  Converting
  both quantities as above gives $\gamma^i\le a_i+O(M/k)$.
- The continuous singleton coordinate has positive increment.  On each
  continuous component it is Lipschitz, because all coordinates are
  nondecreasing and their sum grows at unit speed.  Positive increment gives
  a point of positive derivative, and SP.2(b) gives $\gamma^i=a_i$ there.

Transporting this comparison to the cell end and then to the actual tail
gives

$$
w_i\le a_i+C_2Mp+e_k.
\tag{13}
$$

Combining (11)--(13) proves the two Quit inequalities, including the support
lower bound when $\xi_i>0$.  Hence every small-cell row is

$$
\left(C_{I,M}/k+3e_k\right)\text{-perfect}
$$

with one constant independent of the cell and stage.  Proposition 4.8's
profile is completely absorbing, so these profiles prove S.3.

### Boundary test

The approximation estimate of Lemma 4.9 alone does not imply (10): an
arbitrary nearby product row could introduce a tiny positive Quit probability
at a zero singleton coordinate, which would activate the lower support clause
without any indifference witness.  The proof must select the
support-preserving witness constructed in Lemma 4.9.  With that selection the
problem disappears; without it the claimed sequential-perfection conclusion
is unsupported.

## 3. Consequence for the AGKRS packet

The refusal lemma, the repaired continuous argument, and the repaired
discretization prove the two steps not available from the existing
conditional source classifications:

1. a weak limit of completed ordinary vanishing-error equilibria is
   zero-perfect away from a terminal jump; and
2. a zero-perfect path without a terminal jump has completely absorbing,
   uniformly sequentially approximately perfect discretizations.

Together with the terminal-jump punishment construction in `AGKRS_3_4.md`,
these repairs yield the stated S.1/S.2/S.3 trichotomy, subject to independent
review of the quantitative quotient estimates above.

## Sources inspected

- AGKRS, *Absorption paths and equilibria in quitting games*, published
  Theorem 3.4, Proposition 4.8, Lemma 4.9, Proposition 4.11, Definition 4.13,
  Proposition 4.14, and Theorem 4.15;
- `Literature/AshkenaziGolanKrasikovRainerAndSolan2022.lean`;
- `UniformEquilibrium/Quitting/AbsorptionPath/ContinuousPath.lean`; and
- `UniformEquilibrium/Quitting/Classification/ExistenceBranches.lean`.
