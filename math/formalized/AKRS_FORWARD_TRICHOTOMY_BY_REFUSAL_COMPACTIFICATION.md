# Refusal compactification proves the corrected AGKRS forward trichotomy

Authors: external proposer; CODEX_ROOT (analytic repairs and source audit)

Independent reviews:
[AGKRS_FALSIFIER](../feedback/AGKRS_3_4__BY_AGKRS_FALSIFIER.md),
[CODEX_CAUCHY](../feedback/AGKRS_3_4__BY_CODEX_CAUCHY__CONTINUOUS.md), and
[CODEX_DISCRETIZATION](../feedback/AGKRS_3_4__BY_CODEX_DISCRETIZATION__DISCRETIZATION.md).

## Formalization record

- **M:** the exact forward trichotomy and its refusal, terminal-jump, and
  support-preserving small-cell arguments passed the independent reviews
  above.  The small-cell productization follows the published AGKRS lemma.
- **L:** the generic productization is
  `exists_agkrsSmallCellProductization`; the actual chronological path is
  sequentially perfect in `ChronologicalLimit.isSequentiallyPerfectAbsorptionPath`;
  its terminal and no-terminal consumers are
  `ChronologicalLimit.instantPunishmentEquilibriumExistence_of_terminalPathJump`
  and
  `ChronologicalLimit.wellSupportedAbsorbingSequenceExistence_of_noTerminalTotalJump`;
  and their exhaustive dispatch is
  `ChronologicalLimit.instantPunishment_or_wellSupportedAbsorbingSequenceExistence`.
- **A:** `QuittingPayoffTable.stationary_or_vanishingNeverNashFamily` starts
  from the literal arbitrary-behavior approximate-equilibrium premise, while
  `nonempty_rootSequenceAbsorbingCompletionDiagonal` and
  `nonempty_chronologicalLimit` construct the actual completed source used by
  the branch consumers.
- **C:**
  `QuittingPayoffTable.stationary_or_instantPunishment_or_sequentiallyPerfectAbsorbing`
  proves the fixed table-level S.1/S.2/S.3 disjunction, and the paper-facing
  `Literature.AshkenaziGolanKrasikovRainerAndSolan2022.theorem3_4` delegates to
  it.

The production small-cell API uses the exact cell parameter
`1 / (resolution - 1)` and the published coordinate bound with factor
`2 ^ Fintype.card ι * parameter * pathCellAbsorption`.  The formalization does
not expose every displayed auxiliary estimate below as a public theorem and
does not claim the full weak-convergence conclusion of published Proposition
4.8.  It proves the packet's exact forward trichotomy.

## Exact statement

Let $I$ be a finite player set.  At each live date every player independently
chooses Continue or Quit.  The first nonempty quitting coalition $S$ ends the
game and pays $r(S)\in\mathbb R^I$; if nobody ever Quits, the payoff is
$c\in\mathbb R^I$.  Behavioral strategies may depend on the complete public
history and may use private randomization.

Assume that for every $\varepsilon>0$ there is a behavioral profile whose
terminal expected payoff cannot be improved by more than $\varepsilon$ by
any unilateral behavioral replacement.

Then one of the following three fixed branches holds.

1. For every $\varepsilon>0$ there is a stationary behavioral
   $\varepsilon$-equilibrium.
2. For every $\varepsilon>0$ there are a player $i$, a first-date independent
   mixed row at which $i$ Quits surely, and an arbitrary behavioral punishment
   continuation whose best-reply value for $i$ is at most $\varepsilon$ above
   $i$'s min-max value, such that the row followed by that punishment is a
   behavioral $\varepsilon$-equilibrium.
3. For every $\varepsilon>0$ there is a completely absorbing independent root
   sequence which is sequentially $\varepsilon$-perfect at every live date
   against its own literal continuation payoff.

The same one of the three branches works for every tolerance.  In branch 2
the player may depend on the tolerance, as in the paper's statement.

## Definitions used in the proof

For a behavioral profile $x$, let $\theta$ be its absorption date and let

$$
s_n=\Pr_x(\theta\ge n).
$$

At a reached date $n$, write $q_{i,n}$ for player $i$'s prescribed Quit
probability, $V_{i,n}$ for its conditional prescribed payoff, $Q_{i,n}$ for
the payoff from sure Quit at that date, and $C_{i,n}$ for the payoff from sure
Continue at that date followed by the prescribed strategy.  Thus

$$
V_{i,n}=q_{i,n}Q_{i,n}+(1-q_{i,n})C_{i,n}.
\tag{1}
$$

An absorption path records, in cumulative-absorption time, the unconditional
mass assigned to each nonempty terminal coalition.  At a jump it records a
literal independent product row.  On continuous clock components only
singleton coordinates can grow.  Its conditional remaining reward vector at
clock $t$ is denoted $\gamma_t(\pi)$.

Sequential zero-perfection of a path means:

- every nonterminal jump row is an exact Nash row against the path's
  post-jump continuation payoff;
- at every continuous clock time, immediate solo Quit cannot improve; and
- a singleton coordinate with positive right derivative is indifferent
  between solo Quit and continuation.

## Proof

### 1. Normalize the payoff at Never

Subtract $c_i$ from every payoff coordinate of player $i$.  This preserves
all unilateral gains, equilibrium errors, sequential perfection, min-max
errors, stationarity, and absorption.  Hence assume $c=0$.

Put $a_i=r_i(\{i\})$.  If $a_i\le0$ for every player, all-Continue is an exact
stationary equilibrium: against all-Continue opponents, every behavioral
replacement yields a mixture of $a_i$ and zero.  This is branch 1.

Assume henceforth that $a_{i_0}>0$ for some fixed player $i_0$.

### 2. Vanishing-error equilibria are asymptotically absorbing

Let $x$ be an $\varepsilon$-equilibrium and
$h(x)=\Pr_x(\theta=\infty)$.  Let $i_0$ follow its prescribed strategy before
date $N$ and Quit surely at $N$ if play is still live.  As $N\to\infty$, the
probability of original finite absorption at or after $N$ tends to zero, as
does the probability of an opponent Quit exactly at $N$.  On original
nonabsorption, the deviation changes payoff from zero to $a_{i_0}$.  Bounded
convergence gives limiting gain $h(x)a_{i_0}$, so

$$
h(x)a_{i_0}\le\varepsilon.
\tag{2}
$$

Choose $\varepsilon_k\downarrow0$ and corresponding equilibria $x^k$.  Choose
$N_k$ so late that the original finite absorption probability at or after
$N_k$ is at most $\varepsilon_k$, and force $i_0$ to Quit there.  The resulting
profile $\bar x^k$ is absorbing, and its complete terminal law differs from
that of $x^k$ by at most

$$
\rho_k:=\varepsilon_k+\varepsilon_k/a_{i_0}\longrightarrow0.
\tag{3}
$$

The sequential compactness theorem for absorption paths supplies a
subsequence whose paths converge weakly to an absorption path $\pi$.

### 3. Global refusal lemma

Fix one profile $x$, one player $i$, a finite set of dates $B$, and
$\delta>0$.  Suppose

$$
V_{i,n}-Q_{i,n}\ge\delta\qquad(n\in B).
\tag{4}
$$

Let player $i$ force Continue at every date in $B$ and otherwise follow the
prescribed strategy.  Let $D_n$ be the modified conditional payoff minus the
prescribed conditional payoff from date $n$, and let $d_n$ be the probability
all opponents Continue at date $n$.

At an unmodified date,

$$
D_n=(1-q_{i,n})d_nD_{n+1}.
$$

At a modified date,

$$
D_n=C_{i,n}-V_{i,n}+d_nD_{n+1}.
$$

Equation (1) and (4) give

$$
C_{i,n}-V_{i,n}
=\frac{q_{i,n}}{1-q_{i,n}}(V_{i,n}-Q_{i,n})
\ge q_{i,n}\delta.
$$

Earlier forced-Continue choices can only raise the probability of reaching a
later selected date.  Backward induction therefore yields

$$
\gamma_i(x^{i,B},x^{-i})-\gamma_i(x)
\ge\delta\sum_{n\in B}s_nq_{i,n}.
\tag{5}
$$

If $x$ is an $\varepsilon$-equilibrium, the right side is at most
$\varepsilon$.  Increasing finite exhaustion gives the same conclusion for a
countable set of dates.

### 4. The limiting path is zero-perfect away from a terminal jump

#### Nonterminal jumps

Fix a jump $t$ whose post-jump accumulated mass is below one.  Absorption-path
compactness supplies matching source dates whose reach tends to $1-t>0$, whose
roots converge to the jump root, and whose continuation payoffs converge to
$\gamma_t(\pi)$.  The completion mass (3) cannot carry a positive limiting
jump, so these are genuine dates of $x^k$.

Prefixing any suffix deviation by the prescribed earlier behavior shows that
the reached suffix is an $\varepsilon_k/s_n^k$-equilibrium.  Sure Quit and sure
Continue at its first row are therefore each worth at most the prescribed
mixed value plus $o(1)$.  In the limit both endpoints are no larger than their
convex combination.  Every endpoint in the limiting row's support consequently
equals that combination.  This is the jump condition SP.1.

#### Continuous times: no profitable solo Quit

Fix $t<1$ on a continuous clock component.  Choose genuine source dates whose
pre-stage clocks tend to $t$.  Their one-stage absorption probabilities tend
to zero and their reach tends to $1-t>0$.  The sure-Quit deviation inequality
is

$$
s_n^k(Q_{i,n}^k-V_{i,n}^k)\le\varepsilon_k.
$$

The immediate-Quit value tends to $a_i$, and the conditional prescribed value
tends to $\gamma_t^i(\pi)$.  Hence

$$
a_i\le\gamma_t^i(\pi).
\tag{6}
$$

#### Continuous times: equality on positive singleton rate

Suppose instead that

$$
g:=\gamma_t^i(\pi)-a_i>0
$$

and that the singleton-$i$ coordinate has positive lower right derivative at
$t$.  Put $b=1-t>0$.  A continuous clock time has no atom at $t$: the total
left mass is at least $t$ by the absorption-path inequality and at most the
total mass $t$ at the point.  The lower right derivative supplies
$\lambda,h_0>0$ such that

$$
\pi_s(\{i\})-\pi_t(\{i\})\ge\lambda(s-t)
\qquad(t<s<t+h_0).
\tag{7}
$$

Choose a common continuity point $r$ of the finitely many coordinate
measures with

$$
t<r<\min\{t+h_0,t+b/4\},
$$

and with both $r-t$ and the total absorption mass $\mu([t,r])$ as small as
needed below.  This is continuity from above at the atom-free point $t$; it
does not assert an atom-free neighborhood, and jumps may accumulate at $t$.

Let $\mu_k$ be the total absorption measure of the completed profile and let

$$
\nu_i^k(A)=\sum_S r_i(S)\mu_{k,S}(A),
\qquad
\nu_i(A)=\sum_S r_i(S)\mu_S(A)
$$

be its signed reward measures.  Weak convergence at the continuity endpoints
gives

$$
\mu_k([t,r])\longrightarrow\mu([t,r]),
\qquad
\nu_i^k([t,1])\longrightarrow\nu_i([t,1]).
\tag{8}
$$

For a genuine source row whose pre-stage clock is $u\in[t,r]$, reach is
$s_n^k=1-u>b/2$.  If $p_n^k$ is its conditional one-stage absorption, then

$$
s_n^kp_n^k\le\mu_k([t,r]),
\qquad
|Q_{i,n}^k-a_i|\le2Mp_n^k.
\tag{9}
$$

Write $\bar V_{i,n}^k$ for its conditional prescribed value in the completed
profile.  The exact remaining-reward formula is

$$
\bar V_{i,n}^k=\frac{\nu_i^k([u,1])}{1-u},
\qquad
\gamma_t^i(\pi)=\frac{\nu_i([t,1])}{b}.
\tag{10}
$$

The numerator variation between $t$ and $u$ is at most
$M\mu_k([t,r])$.  Together with (8), $1-u>b/2$, and
$|\nu_i([t,1])|\le Mb$, the elementary quotient estimate shows, uniformly
over all such source rows,

$$
|\bar V_{i,n}^k-\gamma_t^i(\pi)|<g/8
\tag{11}
$$

after choosing $r$ sufficiently close to $t$ and then $k$ sufficiently
large.  The completion changes an event of unconditional mass at most
$\rho_k$, so the original conditional value $V_{i,n}^k$ satisfies

$$
|V_{i,n}^k-\bar V_{i,n}^k|
\le\frac{2M\rho_k}{s_n^k}<g/8.
\tag{12}
$$

Equations (9)--(12), with the interval tightened once more if necessary,
give the uniform inequality

$$
V_{i,n}^k-Q_{i,n}^k\ge g/2
\tag{13}
$$

at every genuine row with clock in $[t,r]$.  The completion clock lies beyond
$r$ for large $k$.  Applying the refusal lemma and exhausting the countable
set of those rows yields

$$
\sum_{n:\,1-s_n^k\in[t,r]}s_n^kq_{i,n}^k
\le2\varepsilon_k/g.
\tag{14}
$$

The completed singleton-$i$ mass in $[t,r]$ is at most this sum and therefore
tends to zero.  Weak convergence at the two continuity endpoints gives zero
limiting singleton mass there, contradicting (7).  Thus positive singleton
rate forces
$\gamma_t^i(\pi)=a_i$.  Together with (6), this is SP.2.

Consequently every nonterminal part of $\pi$ is sequentially zero-perfect.

### 5. A terminal jump yields branch 2

Suppose $t$ is a jump whose post-jump accumulated mass equals one.  Its
positive mass cannot come from the vanishing completion.  Let $n_k$ be
matching genuine source dates and let $\xi^k$ be their roots.  Their reach is
bounded away from zero, so their suffix equilibrium errors
$\delta_k$ tend to zero.

The limiting product row has zero all-Continue probability.  Since $I$ is
finite, one player $i$ has limiting Quit probability one.  After a subsequence
write $q_k=\xi_i^k\to1$.

Let $m_i$ be player $i$'s behavioral min-max value and choose a punishment
continuation $z^\eta$ whose best-reply value for $i$ is at most $m_i+\eta$.
Keep the opponents' current components from $\xi^k$, make $i$ Quit surely,
and follow the first row by $z^\eta$.

For any other player $j$ and any complete behavioral replacement by $j$, the
old and new outcomes can differ only when $i$ would have Continued at the
source row.  Both prescribed and deviating payoffs therefore change by at
most $2M(1-q_k)$, and

$$
\operatorname{Regret}_j^{\mathrm{new}}
\le\delta_k+4M(1-q_k).
\tag{15}
$$

For player $i$, write $Q_k$ for current sure-Quit payoff, $A_k$ for the
unconditional current contribution when $i$ Continues and some opponent
Quits, and $d_k$ for opponent all-Continue probability.  The original suffix
Nash inequality and the definition of min-max give

$$
A_k+d_km_i\le V_k+\delta_k.
$$

Under $z^\eta$, every Continue-first behavioral deviation is worth at most
$V_k+\delta_k+\eta$.  Since
$|V_k-Q_k|\le2M(1-q_k)$,

$$
\operatorname{Regret}_i^{\mathrm{new}}
\le\delta_k+\eta+2M(1-q_k).
\tag{16}
$$

Choose $\eta$ and then $k$ for any requested error.  Equations (15)--(16) give
branch 2, including its unrestricted deviation and min-max clauses.

### 6. No terminal jump yields branch 3

Assume no jump of $\pi$ absorbs all remaining mass.  Put $d=|I|$ and
$K_d=2^d(2^d-1)$.  Apply the construction in Proposition 4.8 at resolution
$k$.  It produces a completely absorbing independent root sequence.

Every jump of conditional absorption at least $1/k$ is copied literally.  In
every other cell, whose conditional absorption is $p\le1/k$, Lemma 4.9
constructs a product row $\xi$ with the same absorption probability.  Its
proof gives the essential support identity

$$
\xi_i>0\quad\Longleftrightarrow\quad
\text{the cell has positive singleton-$i$ mass},
\qquad \xi_i<1.
\tag{17}
$$

Thus it never introduces an unsupported Quit action and Continue is always
in support.  For a small cell with correlated law $y$, the construction also
gives

$$
\sum_{S\ne\varnothing}|\xi(S)-y(S)|
\le \frac{K_d}{k}p.
\tag{18}
$$

The path and product implementations have identical survival weights.  From
the entrance of any cell, those weights $w_m$ satisfy $\sum_mw_mp_m=1$.
Consequently the actual post-cell continuation payoff differs uniformly from
the path continuation by

$$
e_k\le \frac{MK_d}{k}.
\tag{19}
$$

This weighted telescope, rather than bare weak convergence near clock one,
makes the estimate uniform over all calendar rows.  A copied large jump is
therefore $2e_k$-perfect by SP.1; the no-terminal-jump hypothesis is essential
because SP.1 does not constrain a terminal jump.

At a small-cell row, let $w$ be the path post-cell continuation, let $\Gamma$
be the path payoff immediately before the cell, and let $Q_i,C_i,V_i$ be the
two endpoints and mixed value against $w$.  Put $a_i=r_i(\{i\})$.  Since every
marginal Quit probability and the probability of any opponent Quit are at
most $p$,

$$
|\Gamma_i-w_i|\le2Mp,\qquad
|Q_i-a_i|\le2Mp,\qquad
|C_i-w_i|\le2Mp,\qquad
|V_i-w_i|\le2Mp.
\tag{20}
$$

Equation (20) gives both Continue clauses with error $4Mp$.  At a continuous
cell entrance, SP.2(a) gives $a_i\le\Gamma_i$.  At a small-jump entrance,
SP.1 and the fact that its conditional mass is at most $p/(1-p)\le2p$ give
$a_i\le\Gamma_i+2Mp$.  Hence

$$
Q_i\le V_i+8Mp.
\tag{21}
$$

If $\xi_i>0$, (17) says the cell contains positive singleton-$i$ path mass.
If it comes from a small jump, SP.1 at that jump gives
$\Gamma_i\le a_i+6Mp$.  If it comes from a continuous component, singleton
coordinates are one-Lipschitz there; a positive increment has an interior
differentiability point with positive derivative, where SP.2(b) gives
equality with $a_i$, and transport back again gives
$\Gamma_i\le a_i+6Mp$.  In either case, (20) yields

$$
Q_i\ge V_i-12Mp.
\tag{22}
$$

Replacing the path continuation by the actual tail changes the Continue
endpoint and mixed payoff by at most $e_k$ each.  Equations (20)--(22) prove
every small-cell row is $(12Mp+2e_k)$-perfect.  Together with (19) and the
large-jump estimate, every row is uniformly

$$
\eta_k\text{-perfect},qquad
\eta_k\le\frac{M(12+2K_d)}{k}\longrightarrow0.
\tag{23}
$$

The constructed sequences are completely absorbing.  Selecting a sufficiently
large $k$ for each requested tolerance gives branch 3.

### 7. Exhaustion

The cases are fixed by the normalized reward table and the one limiting path:
nonpositive solo rewards give branch 1; otherwise a terminal limiting jump
gives branch 2, and absence of one gives branch 3.  Monotonicity in the error
extends each vanishing-error construction to every positive tolerance.

## Conjecture-facing change

This closes the AGKRS Theorem 3.4 forward source-closure obligation by proving
the corrected S.1/S.2/S.3 trichotomy directly.  It bypasses the need to select
and separately consume Simon's corrected stationarily-generated residual:
all source profiles enter one absorption-path compactification.

## Boundary tests and falsification attempts

1. If every normalized solo payoff is nonpositive, the construction must stop
   in branch 1; it does.
2. For one player with positive solo payoff, (2) forces absorption.  A terminal
   atom gives branch 2, while a diffuse limiting clock gives branch 3.
3. A continuous path can have jumps of size $2^{-2m}$ at clock times
   $t+2^{-m}$, with short disjoint post-jump plateaux.  Thus no atom-free
   neighborhood exists.  The small-total-mass proof in Section 4 handles this
   example.
4. Merely choosing an arbitrary product approximation in Lemma 4.9 can add a
   tiny positive Quit probability where the path singleton coordinate is
   zero, activating an unsupported lower support inequality.  The proof uses
   the lemma's constructed support-preserving witness, not merely its metric
   conclusion.
5. At a terminal product jump, zero joint Continue mass implies a sure quitter
   only because the player set is finite.  Finiteness is explicit in the
   theorem.

## Source correspondence and novelty

The branch predicates correspond to the production predicates in
`UniformEquilibrium/Quitting/Classification/ExistenceBranches.lean`, with the
arbitrary-profile S.2 equivalence checked in
`UniformEquilibrium/Quitting/Classification/InstantPunishmentEquivalence.lean`.
The paper-facing equivalences and checked general forward implication are
recorded in
`Literature/AshkenaziGolanKrasikovRainerAndSolan2022.lean`.

The published proof of Theorem 3.4 invokes Simon's old pointwise
classification.  Simon's correction adds a stationarily-generated fourth
output which the published argument does not consume.  The new content here
is the global refusal inequality (5), its use to recover SP.2(b) from ordinary
Nash profiles, and the support-preserving proof that the standard path
discretization is uniformly sequentially approximately perfect.

Proposition 4.8, Lemma 4.9, and Proposition 4.11 from the published paper are
used only in their stated absorption-path roles; the defective Theorem 3.4
proof is not used.

## Adapter and consumer

The input is the literal arbitrary-game approximate-equilibrium existence
premise.  The proof selects actual behavioral profiles at errors tending to
zero, changes only one actual player's late action by vanishing total mass,
and keeps their complete absorption laws.  No supplied residual structure is
assumed.

The outputs are exactly the three branch predicates in the archived AGKRS
forward-trichotomy question.  Branch 2 controls every unilateral behavioral
deviation through the coupling in (8)--(9).  Branch 3 is a literal completely absorbing root
sequence with its own continuation payoff at every row, rather than an
artificial Bellman annotation.

## Lean realization

The generic source-independent lemmas are in
`MathUE/PMFProduct/AGKRSSmallCellProductization.lean` and
`MathUE/Topology/OneSidedDiniFencing.lean`.  The partition, small-cell,
telescope, support, and sequential-perfection layers are the four
`UniformEquilibrium/Quitting/AbsorptionPath/AGKRS*.lean` modules.  The two
branch consumers and their exhaustive dispatch are under
`UniformEquilibrium/Quitting/Classification/Existence/`, and
`AGKRSTheorem34.lean` owns the table-level theorem.

## Scope and nonclaims

- This proves the corrected **forward trichotomy**.  It does not prove the
  printed reverse implication of Theorem 3.4.
- It does not claim that sequentially $\varepsilon$-perfect absorbing
  profiles are $\varepsilon$-Nash.  The paper's printed error-exponent theorem
  used for such a conversion is refuted in the repository.
- It does not prove that every quitting game has approximate equilibria or a
  uniform-equilibrium payoff.
- The forward theorem and the M/L/A/C chain recorded above are checked in
  Lean.  The approximate-equilibrium premise is not proved for every quitting
  game, and no fixed uniform-payoff target or all-long-finite-horizon control
  follows from this theorem.
