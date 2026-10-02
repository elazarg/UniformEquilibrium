# Fin4 monodromy versus principal blockers: a regular-clock no-go and the missing semantic passport

## Status

This note answers a bounded synthesis question about `../COMP.md` and
`../FACE_ENLARGE.md`.

The strict-principal-blocker alternative does **not yet** supply either
remaining conversion in `COMP.md` from the stated data alone.  The combined
analysis leaves one narrower temporal outlet and one exact rank passport.

1. A fixed-period family whose entire root word tends to all Continue forces a
   homogeneous simplex LCP solution after normalizing its vanishing total
   clock.  Thus that regular branch is unavailable in the hard residual.  A
   non-all-Continue limit is different: with at least two limiting active
   clocks it gives an exact periodic equilibrium, but with exactly one active
   clock it retains the known exceptional-owner temporal escape.  The
   full-support direction `M p >= 0` does not remove that issue.
2. A strict principal blocker and its outside helper contain only singleton
   information.  A literal nonsingleton endpoint cycle can create an
   arbitrarily large new debt coordinate without changing the matrix, the
   blocker, the full-support direction, or any selected mover gain.  Hence the
   blocker data do not imply the no-new-support condition needed for the
   checked minimum-fiber rank drop.

The strongest positive replacement is an exact minimal passport: an actual
helper endpoint must separately certify total-debt nonincrease, no inactive
support entry, and disappearance of one old active coordinate.  Those three
facts are sufficient, by global minimality and the checked tangent-family
re-extraction theorem, and none follows from the blocker scalar alone.

These are ordinary mathematical arguments, not Lean-checked additions.  The
explicit rational separation table below is not claimed to satisfy a terminal
exploitability witness; it is a separation model for the proposed implication.

## Question

Suppose a Fin4 table supplies:

* a literal same-stage positive-gain endpoint cycle of the common-host or
  complementary-pair type from `COMP.md`;
* a quantitatively full-support singleton direction `p > 0`, `M p >= 0`; and
* on a proper face `P`, a strict blocker

  \[
  y\in\Delta(P),\qquad M_P^T y\le-\eta\mathbf 1,qquad \eta>0.
  \]

Does this force either a first-order periodic two-clock realization, or an
actual minimum-fiber endpoint with smaller positive-debt support?

The answer is no at this interface.

## 1. Regular fixed-period clocks force the homogeneous LCP branch

The following standalone statement is the main no-go.

### Theorem 1 (vanishing-clock homogeneous necessity)

Let `I` be finite and let `r` be a quitting reward table.  Put

\[
M_{ij}=r_i(\{j\})-r_i(\{i\}).
\]

Fix `K`.  For every `n` let `sigma_n` be the behavioral
profile obtained by periodically repeating `K` product roots
`x^n_0,...,x^n_{K-1}`.  Write `q^n_{k i}` for player `i`'s Quit probability in
root `k`.  Put

\[
s_n=\sum_{k<K}\sum_iq^n_{ki},
\]

and assume `s_n>0`, `s_n->0`.  If the terminal exploitability of `sigma_n`
tends to zero, then `M` has a homogeneous simplex LCP solution: there is
`q in Delta(I)` such that

\[
Mq\ge0,\qquad q_i(Mq)_i=0\quad(i\in I).                              \tag{1}
\]

#### Proof

Put

\[
a_i^n=\sum_{k<K}q^n_{ki}.
\]

After a subsequence,

\[
q_i=\lim_n a_i^n/s_n
\]

exists and belongs to the simplex.

In one period, the probability of a collision is `O(s_n^2)`, while the
probability that the unique quitter is `i` is

\[
a_i^n+O(s_n^2).
\]

The number of survived periods is geometric on the `1/s_n` scale.  Therefore
the total collision probability is `O(s_n)`, and the eventual terminal owner
law converges to `q`.  If `v` is a subsequential limit of prescribed payoffs,
then

\[
v_i=\sum_j q_j r_i(\{j\}).                                         \tag{2}
\]

The deviation that Quits at the current phase has payoff
`r_i({i})+O(s_n)`.  Vanishing exploitability gives

\[
v_i\ge r_i(\{i\}),
\]

which, by (2), is `(Mq)_i >= 0`.

If `q_i>0` and `sum_{j != i}q_j>0`, the limiting payoff from Never is

\[
L_i=\frac{\sum_{j\ne i}q_jr_i(\{j\})}{1-q_i}.
\]

Equation (2) is the convex decomposition

\[
v_i=q_i r_i(\{i\})+(1-q_i)L_i.
\]

Vanishing exploitability also gives `v_i >= L_i`.  Since `v_i` is at least
both endpoints of its own convex decomposition, both endpoints are equal.
Thus `v_i=r_i({i})`, so `(Mq)_i=0`.

If `q_i>0` and all other `q_j` vanish, (2) already gives
`v_i=r_i({i})`.  This proves complementarity in every case and hence (1).

### Theorem 2 (fixed-period compactness split with one exceptional owner)

For a fixed `K`, any sequence of `K`-periodic product profiles whose terminal
exploitability tends to zero has, after a subsequence, one of three outcomes:

1. at least two players have positive limiting Quit mass somewhere in the
   period, and the limiting word is an exact periodic terminal Nash profile;
2. exactly one player has positive limiting Quit mass in the period, leaving
   that player as the unique possible cap-discontinuous exceptional owner; or
3. every limiting root is all Continue and the normalized singleton matrix
   has a homogeneous simplex solution.

For the third arm, the total root hazard `s_n` tends to zero and Theorem 1
applies.  In the first arm every player sees a positive limiting opponent
absorption clock: an active player sees the other active player, while an
inactive player sees both.  The finite-cycle Bellman payoff and behavioral cap
are therefore continuous, and the vanishing Nash inequalities pass to the
limit.

In the second arm, the unique active player's opponents lose all limiting
absorption.  Its Never value need not be continuous: arbitrarily late opponent
clocks may retain a payoff before disappearing in the compact limit.  This is
the exact one-exceptional-owner phenomenon, so no exact-equilibrium conclusion
is asserted there.

This boundary split should be independently checked before export.

### Corollary 3 (the COMP fixed-period branch has no new hard-residual limit)

The reviewed periodic two-clock consumer in `feedback/COMP__BY_CODEX_GAUSS__TWO_CLOCK.md`
turns its data into actual terminal `O(h)`-Nash profiles.  Since the endpoint
monodromy has fixed length, Theorem 2 applies without any regular-scale
assumption on the individual hazards.

For a `FinFourQuantitativeFullSupportHardResidual`, the normal core is all
players and `ResidualHardClass.no_homogeneous` excludes exactly that branch.
Consequently the strict blocker cannot manufacture a genuinely new
all-Continue fixed-period branch inside the hard residual.  A successful
fixed-period cycle construction must either directly yield the exact
two-active limit, pass through the unique-active exceptional-owner branch, or
use the support-rank endpoint.

This is not a contradiction to the periodic consumer.  It says that the
consumer is sound, while its all-Continue fixed-period producer is
algebraically incompatible with the maintained hard branch.  The
one-exceptional-owner limit is not discharged here.

## 2. Why the full-support packet direction does not repair the no-go

Let `p>0`, `sum p_i=1`, and `Mp>=0`.  If the matrix has no homogeneous simplex
solution, then

\[
\exists i,\qquad (Mp)_i>0.                                         \tag{5}
\]

Indeed, if every coordinate vanished, full support would make `p` a
homogeneous solution.

The obstruction in (5) has a direct game meaning.  Put

\[
v_i=\sum_jp_jr_i(\{j\}).
\]

For the regular rare-singleton clock with owner proportions `p`, player `i`'s
limiting Never payoff is

\[
L_i=\frac{v_i-p_ir_i(\{i\})}{1-p_i}.
\]

Hence

\[
L_i-v_i=\frac{p_i}{1-p_i}(Mp)_i>0.                                 \tag{6}
\]

Thus the direction supplied by the full-support packet carries a fixed Never
gain; it is a feasibility direction, not a complementary clock.  The outside
helper itinerary from `FACE_ENLARGE.md` can enlarge a bad face until it reaches
the full face, but it ends at (5), not at complementarity.

## 3. Exact rational separation: blockers do not prevent support entry

The following same-table construction shows that the rank alternative also
needs additional semantic data.

Use players `0,1,2,3` and take the normalized singleton matrix

\[
M=
\begin{pmatrix}
0&3&-1&3\\
2&0&1&-3\\
2&-2&0&-1\\
-1&-2&1&0
\end{pmatrix}.                                                     \tag{7}
\]

This is the repository's rational `deadlockMatrix`.  Every principal minor
of size at least two is nonzero (respectively
`-6,2,3,2,-6,1`, `10,-3,5,8`, and `25`), and no singleton column is
nonnegative.  Therefore it has no homogeneous simplex solution.

The full-support rational vector

\[
p=(3/10,1/20,9/20,1/5)
\]

satisfies

\[
Mp=(3/10,9/20,3/10,1/20)>0.                                      \tag{8}
\]

On the face `P={1,3}`, the vector `y=(1/2,1/2)` is a strict blocker with
`eta=1`:

\[
M_P^Ty=(-1,-3/2)\le-\mathbf1.                                    \tag{9}
\]

Now choose singleton rewards with own singleton baseline zero and differences
given by (7).  On the four nonsingleton coalitions

\[
A=\{0,2\},\quad B=\{0,1,2\},\quad
C=\{0,1,2,3\},\quad D=\{0,2,3\},
\]

set the mover coordinates so that

\[
r_1(B)>r_1(A),\quad r_3(C)>r_3(B),\quad
r_1(D)>r_1(C),\quad r_3(A)>r_3(D).                                \tag{10}
\]

For instance use the values `0,1,0,1` in the relevant alternating order.
Then the pure date-zero profiles form the literal common-host cycle

\[
A\xrightarrow{1}B\xrightarrow{3}C\xrightarrow{1}D\xrightarrow{3}A,
\]

with gain one on every edge.  Players `0` and `2` Quit in every coalition, so
every selected mover's unrestricted deviation collapses to its date-zero
binary endpoint choice.

Set player `2`'s prescribed payoff equal to `2` at all four displayed
coalitions.  At `A`, if player `2` Continues the coalition is `{0}`, whose
payoff to player `2` is `M_{20}=2`; hence player `2` has zero debt there.

The reward coordinate

\[
r_2(\{0,1\})=R                                                    \tag{11}
\]

is absent from the singleton matrix, the blocker, the full-support direction,
and all four selected mover gains.  But at `B`, player `2` can Continue and
produce `{0,1}`, so

\[
d_2(B)\ge (R-2)_+.                                                \tag{12}
\]

Taking `R` arbitrarily large creates an arbitrarily large new debt coordinate
after the first endpoint update while preserving (7)--(10) literally.  Thus
even the combination

\[
\text{no homogeneous solution} + Mp>0 + \text{strict blocker}
+\text{literal common-host monodromy}
\]

does not imply no-new-support or a debt budget.

This is a separation model, not a quitting-game counterexample: it is not
claimed to satisfy a global terminal exploitability witness or positive
minimum debt.

## 4. The minimal sufficient rank passport

Let `z` be the base of a positive-minimum tangent family, let `D(z)=D_*>0`,
and let `z'` be the semantic pair of an actual source-matched helper endpoint.
Write

\[
A=\{i:d_i(z)>0\}.
\]

The following three endpoint facts are sufficient:

\[
D(z')\le D_*,                                                     \tag{13}
\]

\[
d_j(z)=0\Longrightarrow d_j(z')=0,                               \tag{14}
\]

and

\[
\exists w\in A,\qquad d_w(z')=0.                                 \tag{15}
\]

Global minimality turns (13) into equality.  Equation (14) gives
`supp_+(d(z')) subseteq A`, and (15) makes the inclusion strict.  The checked
theorem
`QuittingPositiveMinimumDebtTangentFamily.exists_reextracted_of_minimumFiber_of_supportSubset_of_vanished`
then produces a complete new tangent family based **exactly** at `z'`, with
strictly smaller positive-debt support.

For a literal profile update, (13)--(14) can be certified without separately
computing the new cap by the cap/payoff inequalities

\[
\sum_i\big[(B_i'-B_i)-(U_i'-U_i)\big]\le0,                        \tag{16}
\]

and, for every inactive `j`,

\[
B_j'-B_j\le U_j'-U_j.                                             \tag{17}
\]

Together with one owner-clearance identity, these are the minimal semantic
fields missing from a blocker-selected outside-helper update.  The scalar
blocker tax `y^T c` does not imply either (16) or (17), as (11)--(12) show.

## 5. Resulting correction to the combined programme

The valid combined conclusion is not the proposed automatic alternative

\[
\text{strict blocker}\Longrightarrow
\text{periodic realization or support drop}.
\]

It is the sharper boundary

\[
\boxed{
\begin{array}{c}
\text{fixed-period terminal approximants}
\Longrightarrow \text{exact two-active cycle, exceptional owner, or homogeneous LCP};\\
\text{hard residual}\Longrightarrow
\text{only the unique-active fixed-period escape can remain};\\
\text{rank regeneration}\Longleftarrow
\text{an actual helper endpoint satisfying (13)--(15).}
\end{array}}
\]

Accordingly, a successful use of the literal endpoint monodromy must do one of
the following genuinely new things:

* consume the unique-active exceptional-owner limit with source-matched late
  clock information;
* obtain a two-active exact zero-order cycle, which is already a
  compiler input; or
* prove the source-matched aggregate cap budget and no-entry conditions
  (13)--(15) for one blocker-selected helper endpoint.

The principal blocker is useful for choosing the candidate outside label and
quantifying a singleton/collision tax.  It is not, by itself, a producer of
either remaining semantic output.

## What remains unproved

* Theorems 1--2 have not received independent review or Lean formalization.
  The main audit point is cap continuity in the two-active limit and the exact
  isolation of the sole active player in the exceptional arm.
* No theorem here consumes the one-active-owner temporal escape while
  retaining the literal endpoint-cycle source.  This is now the only
  fixed-period temporal branch not reduced to an existing matrix or exact
  cyclic consumer.
* The strict blocker does not produce an actual helper endpoint satisfying
  (13)--(15).  Proving those endpoint facts, or constructing a counterexample
  to their production under the full hard-residual hypotheses, remains open.
* The rational table in Section 3 is deliberately only a separation model.  It
  does not refute the Fin4 conjecture and is not asserted to carry the global
  terminal exploitability witness.
* This note uses the strict-blocker statement from `FACE_ENLARGE.md` as supplied;
  it does not independently audit that note's literature-dependent
  completely-`S_0`/projective-`Q` equivalence.

## Source audit

The narrow checked source set used here is:

* `ResidualHardClass.no_homogeneous` in
  `UniformEquilibrium/Quitting/Classification/LCP/Gate.lean`;
* `FinFourQuantitativeFullSupportHardResidual` in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/FullSupportProjectiveQBarResidual.lean`;
* `normalizedSoloMatrix` and `normalizedSoloMatrix_diagonal` in
  `UniformEquilibrium/Quitting/Classification/LCP/Normalization.lean`;
* `QuittingNormalizedSingletonSourcePacket` in
  `UniformEquilibrium/Quitting/Classification/ThreePlayer/AnalyticPacket.lean`;
* the periodic two-clock audit in
  `feedback/COMP__BY_CODEX_GAUSS__TWO_CLOCK.md`; and
* `QuittingPositiveMinimumDebtTangentFamily.exists_reextracted_of_minimumFiber_of_supportSubset_of_vanished`
  in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/PositiveMinimumDebtTangentFamily.lean`.

The endpoint-cycle separation uses only the elementary first-stage semantics
of pure nonsingleton roots with two common sure quitters.

## Next requested check

Independently falsify Theorem 2, checking both the two-active cap-continuity
arm and the claim that the sole active player is the only exceptional cap
coordinate.  If it passes, the fixed-length endpoint cycle has only one
non-LCP temporal outlet: a source-matched one-active-owner escape.
