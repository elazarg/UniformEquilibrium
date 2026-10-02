# Finite-deadline Nash gives a universal third-date improvement and an asymptotic quarter ceiling

## Status

**Core Theorem 1.1 and the Section 8 fixed-prefix extension independently
reviewed PASS after one literal scope repair.**  For every
finite quitting table with rewards in `[-R,R]`, every exact mixed Nash
equilibrium of the hard-tail timing game with `K` finite dates has unrestricted
terminal debt bounded by an explicit scalar function `c_K R`.  At three dates
this gives the rational universal bound

\[
 d_i\le {5R\over12}<{R\over2}.                       \tag{0.1}
\]

Thus re-solving after adjoining one finite date strictly improves the reviewed
sharp two-date half bound.  The general upper bounds tend to `R/4`.  Combined
with the reviewed unique-equilibrium Fin4 regression of `CODEX_MINER`, this
shows that `R/4` is the exact asymptotic worst-table ceiling of **hard-zero-tail
exact Nash selection**.

This is not yet the source-preserving soft-tail theorem requested in the live
producer lane.  It re-solves the enlarged timing game; it does not keep a
previously selected `{0,1,Never}` Nash law fixed while appending a tail.

Core review:
[`CODEX_RAMSEY`](../feedback/CODEX_EULER__FINITE_DEADLINE_NASH_UNIVERSAL_QUARTER_CEILING__BY_CODEX_RAMSEY.md).

## 1. Exact finite-deadline statement

Let `I` be a nonempty finite player set, let `K>=1`, and suppose

\[
 |r_i(S)|\le R
\]

for every player `i` and nonempty quitting coalition `S`, where `R>=0`.
Infinite all-Continue play pays zero.  Form the finite timing game with pure
actions

\[
 \{0,1,\ldots,K-1,\mathsf{Never}\}.
\]

Select any mixed Nash equilibrium and realize its independent planned-time
laws by literal behavioral hazards, retaining the exact Never atoms.

### Theorem 1.1 (universal finite-deadline bound)

If `R=0`, every unrestricted behavioral terminal debt is zero.  If `R>0`,
then for every player `i` with positive debt there is an `x_i in (0,1]` such
that

\[
 {B_i-U_i\over R}\le
 f_K(x_i):=
 {x_i\bigl(K+1-(K-1)x_i\bigr)\over K+1+x_i}.         \tag{1.1}
\]

Players with zero debt satisfy every ensuing nonnegative bound trivially.
Consequently

\[
 B_i-U_i\le c_KR,\qquad
 c_K:=\max_{0\le x\le1}f_K(x).                       \tag{1.2}
\]

In particular,

\[
 c_1={2\over3},\qquad
 c_2={1\over2},\qquad
 c_3=20-8\sqrt6<{5\over12},                          \tag{1.3}
\]

where the weak `5/12` form is the convenient rational statement.  Moreover

\[
 c_K\le {1\over4}+{2\over K},                        \tag{1.4}
\]

so `limsup_K c_K<=1/4`.

For normalized rational Fin4 tables, the three-date profile and its diagonal
midpoint imply

\[
 L_M(r)=0\qquad(1\le M\le59)                         \tag{1.5}
\]

in the exported escape-aware quantile-clock hierarchy.  Thus level `60` is
the first universally unblocked level after this producer.

## 2. Earliest-opponent partition

Fix a player `i`.  Let

\[
 a=\Pr(\text{every opponent chooses Never})
\]

and, for `0<=t<K`, let

\[
 h_t=\Pr(\text{the opponents' earliest finite planned time is }t).
\]

Then

\[
 a+\sum_{t=0}^{K-1}h_t=1.                            \tag{2.1}
\]

Let `V_t` be the payoff from pure time `t`, let `V_N` be the payoff from
Never, and let `L` be the common payoff from any pure finite time `t>=K`.
Finite-game Nash and pure-time extremality give

\[
 U_i=\max\bigl(V_N,V_0,\ldots,V_{K-1}\bigr),
\]

\[
 B_i=\max\bigl(U_i,L\bigr),\qquad
 d_i:=B_i-U_i=\max(0,L-U_i).                         \tag{2.2}
\]

The second equality is against all randomized history-dependent behavioral
deviations, not merely the finite timing actions.

Put `s=r_i({i})`.  Late Quit and Never differ only on the all-opponents-Never
event, so

\[
 L-V_N=as.                                           \tag{2.3}
\]

If `s<=0`, then `L<=V_N<=U_i` and `d_i=0`.  Henceforth suppose `s>0`.

## 3. Every finite-date comparison

Fix `0<=t<K`.  Compare late Quit with pure Quit at `t`.

- If the opponents' earliest time is less than `t`, both deviations are
  preempted and have the same payoff.
- If it is exactly `t`, the comparison is leave versus join and is at most
  `2R`.
- If it is `u>t`, late Quit receives the opponent-only row while Quit at `t`
  receives the singleton payoff `s`; the difference is at most `R-s`.
- If all opponents choose Never, both actions receive `s`.

Therefore, using a positive part as required when the raw difference is
negative,

\[
 d_i\le\max(0,L-V_t)
 \le2Rh_t+(R-s)\sum_{u=t+1}^{K-1}h_u.                \tag{3.1}
\]

Equation (2.3) similarly gives

\[
 d_i\le as.                                          \tag{3.2}
\]

These are the only inequalities used below.

## 4. Summation and scalar bound

Assume `R>0`, put

\[
 x={s\over R}\in(0,1],\qquad \delta={d_i\over R},
 \qquad H=\sum_{t=0}^{K-1}h_t=1-a.                  \tag{4.1}
\]

Summing (3.1) over `t` gives

\[
 \begin{aligned}
 K\delta
 &\le2H+(1-x)\sum_{t=0}^{K-1}\sum_{u=t+1}^{K-1}h_u\\
 &=2H+(1-x)\sum_{u=1}^{K-1}u h_u\\
 &\le\bigl(2+(K-1)(1-x)\bigr)H\\
 &=\bigl(K+1-(K-1)x\bigr)H.                         \tag{4.2}
 \end{aligned}
\]

From (3.2), `a>=delta/x`, hence

\[
 H\le1-{\delta\over x}.                             \tag{4.3}
\]

Writing `A=K+1-(K-1)x>0`, equations (4.2)--(4.3) imply

\[
 K\delta\le A\left(1-{\delta\over x}\right),
\]

and therefore

\[
 \delta\le {Ax\over Kx+A}
 ={x(K+1-(K-1)x)\over K+1+x}=f_K(x).                \tag{4.4}
\]

This proves (1.1)--(1.2).  For `K=1`,
`f_1(x)=2x/(2+x)<=2/3`.  For `K=2`,

\[
 2x(3-x)\le3+x
 \quad\Longleftrightarrow\quad
 (1-x)(3-2x)\ge0,
\]

so `f_2(x)<=1/2`.  For `K=3`, the inequality `f_3(x)<5/12`
is equivalent to

\[
 24x^2-43x+20>0.                                    \tag{4.5}
\]

Indeed,

\[
 24x^2-43x+20
 =24\left(x-{43\over48}\right)^2+{71\over96}>0.    \tag{4.6}
\]

This proves the strict rational third-date improvement (0.1).

For completeness, the derivative of `f_3` has the sign of

\[
 16-16x-2x^2.
\]

It vanishes at the unique point `x_*=-4+2sqrt(6)` in `(0,1)` and changes
from positive to negative there.  Hence

\[
 c_3=f_3(x_*)=20-8\sqrt6<{5\over12}.                 \tag{4.7}
\]

The rational `5/12` bound is convenient for an algebraic handoff; the
radical value is the exact scalar optimum.

Finally,

\[
 f_K(x)
 ={Kx(1-x)+x(1+x)\over K+1+x}
 \le x(1-x)+{x(1+x)\over K}
 \le {1\over4}+{2\over K},                          \tag{4.8}
\]

which proves (1.4).

## 5. Exact hard-tail asymptotic barrier

Define `W_K` to be the supremum, over normalized Fin4 reward tables and over
all mixed Nash equilibria of their `K`-date hard-tail timing games, of the
realized unrestricted terminal exploitability.  Theorem 1.1 gives

\[
 W_K\le c_K\le {1\over4}+{2\over K}.                \tag{5.1}
\]

The independently reviewed table in
[`CODEX_MINER__FIN4_NORMALIZED_HARD_DEADLINE_NASH_NONVANISHING.md`](CODEX_MINER__FIN4_NORMALIZED_HARD_DEADLINE_NASH_NONVANISHING.md)
has a unique `K`-date timing Nash whose debt is

\[
 D_K={2^{K-1}\over2^{K+1}-1}>{1\over4},
 \qquad D_K\longrightarrow {1\over4}.               \tag{5.2}
\]

Thus

\[
 \lim_{K\to\infty}W_K={1\over4}.                   \tag{5.3}
\]

This is a complete minimax diagnosis of exact hard-zero-tail Nashification:
additional dates improve the worst universal bound, but this architecture
cannot cross the quarter barrier.  The same regression has non-Nash
finite-clock profiles with debt tending to zero, so finite-clock
expressiveness itself is not the obstruction.

## 6. Hierarchy consequence

For `K=3`, the literal finite-clock semantic pair belongs to every hierarchy
center of support at least three.  Its diagonal midpoint has objective zero
and sup-distance at most

\[
 {1\over2}\max_i(B_i-U_i)
 \le10-4\sqrt6.                                      \tag{6.1}
\]

For normalized Fin4, the hierarchy radius is `12/m`.  Since

\[
 {12\over59}>10-4\sqrt6.
\]

This comparison is exact: it is equivalent to
`sqrt(6)>289/118`, whose square is
`6*118^2=83544>83521=289^2`.

The same midpoint belongs to every outer neighborhood through level `59`,
proving (1.5).  At level `60`,

\[
 {12\over60}<10-4\sqrt6,
\]

because this is equivalent to `4sqrt(6)<49/5`, and
`96<2401/25` after squaring.  Therefore the exact three-date certificate no
longer applies.  No positivity at
level `60` is inferred.

## 7. Source and scope audit

Inspected checked declarations:

- `KernelGame.mixed_nash_exists` in
  `UniformEquilibrium/ProofView/Concepts/Existence/NashExistenceMixed.lean`;
- `sSup_range_quittingTerminalPayoff_update_eq_pureTime` in
  `UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean`;
- `QuittingFiniteDeadlineNashProfile`,
  `quittingRootSequencePureTimeTerminalValue_late_sub_none_eq`, and
  `QuittingFiniteDeadlineNashProfile.semanticDebt_le_escapeCharge` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFiniteDeadlineNashEscalation.lean`;
  and
- the finite-clock/hierarchy declarations in
  `Research/Quitting/EscapeAwareQuantileClockHierarchy.lean`.

The checked deadline interface bounds a supplied profile by its escape
charge; it does not derive the table-uniform summation bound (4.4).  The
closest ordinary notes construct finite timing Nash profiles and provide the
nonvanishing regression, but a narrow search found no universal `f_K`, no
third-date `5/12` producer, and no exact asymptotic worst-table quarter
statement.

No external paper is used beyond the standard finite-game Nash existence
theorem already represented by the checked declaration above.

The theorem controls arbitrary unilateral behavioral deviations through
pure-time extremality.  It is not a bounded-controller statement.  It does
not prove terminal approximation, a uniform payoff, or a source-preserving
tail append.  In particular, the still-open soft-tail question is:

> Given a previously selected hard-tail `{0,1,Never}` Nash law, can one keep
> its first two planned-time marginals fixed and append a finite actual tail
> that improves `R/2` uniformly while controlling the perturbed on-support
> deviations?

The present theorem proves a fixed improvement only after re-solving the
enlarged finite game, and proves that repeated hard-tail re-solving cannot be
the full solution.

## 8. A fixed-prefix finite-tail quarter barrier

There is also an exact normalized Fin4 obstruction to recursively improving a
**fixed** two-date Nash prefix by appending arbitrary finite actual tails.
This does not prevent one fixed improvement below `1/2`; it proves that this
source-local operation cannot converge to zero.

Take active players `1,2` and dummies `3,4`.  For every nonempty coalition
`S`, define

\[
 r_1(S)=
 \begin{cases}
 -1,&\{1,2\}\subseteq S,\\
 1,&\text{otherwise},
 \end{cases}
 \qquad r_2(S)=-r_1(S),                              \tag{8.1}
\]

and, for each dummy `d`, put

\[
 r_d(S)=\begin{cases}-1,&d\in S,\\0,&d\notin S.
 \end{cases}                                         \tag{8.2}
\]

All rewards lie in `[-1,1]`.  In the hard-tail `{0,1,Never}` game, both
dummies uniquely choose Never by the equilibrium-specific argument in the
reviewed two-date sharpness proof.  The active zero-sum matrix is still

\[
 \begin{pmatrix}-1&1&1\\1&-1&1\\1&1&0\end{pmatrix},
\]

so the unique source law of each active player is `(1/4,1/4,1/2)` and its
source payoff is `(1/2,-1/2)`.

Now preserve the active players' date-zero hazards `1/4` and conditional
date-one hazards `1/3`, and preserve the dummies' Continue actions at those
two dates.  Reinterpret the former hard-tail Never branches as survival into
an appended **arbitrary** product behavioral tail with finite support.  Thus
the two-date prefix is unchanged, but the complete planned-time laws are not:
their old Never atoms have deliberately been opened into the suffix.  The
tail may depend on the whole reward table, need not be Nash, and may activate
the dummies.  Let

\[
 g\in[-1,1]
\]

be player 1's conditional prescribed payoff in that tail.  The only event on
which the original hard-tail prescribed payoff changes is survival of both
active players through the fixed prefix, which has probability `1/4`.  Since the active
coordinates are zero-sum, the new prescribed payoff is

\[
 U_1={1\over2}+{g\over4},\qquad
 U_2=-{1\over2}-{g\over4}.                           \tag{8.3}
\]

Let player 1 deviate to a pure quit time strictly after the appended finite
tail support.  If any opponent has already quit, player 1 is absent from the
first coalition, so (8.1) pays it one.  If no opponent ever quits, player 1
eventually quits alone and again receives one.  This pure deviation therefore
has value exactly one, independently of every detail of the appended tail.
Consequently

\[
 B_1-U_1\ge1-\left({1\over2}+{g\over4}\right)
 ={1\over2}-{g\over4}\ge{1\over4}.                  \tag{8.4}
\]

Pure-time extremality makes this an unrestricted behavioral debt lower bound.
Thus no finite actual tail appended behind this fixed two-date prefix can
reduce total exploitability below `1/4`.

The obstruction is genuinely prefix-local, not a positive-gap table.  If the
two active players instead discard the fixed prefix and independently choose
uniform planned quit times on `{0,...,L-1}`, while both dummies Never, then
player 1's prescribed payoff is `1-2/L`, its best payoff is one, and every
other debt is zero.  Hence the full profile's unrestricted exploitability is
exactly

\[
 {2\over L}\longrightarrow0.                        \tag{8.5}
\]

The finite-tail barrier therefore pinpoints the missing operation: a
successful soft-tail producer must be allowed to alter/reselect the early
prefix hazards, not merely attach a bounded suffix behind the reviewed sharp
two-date prefix.
