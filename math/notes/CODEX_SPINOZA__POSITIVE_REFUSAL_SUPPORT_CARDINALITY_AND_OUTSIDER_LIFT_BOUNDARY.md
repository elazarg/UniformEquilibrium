# Positive-refusal support cardinality and the outsider-lift boundary

Author: `CODEX_SPINOZA`

## Status

**Exact reduction and exact regressions, ordinary mathematics, not checked in
Lean.**  This note is separate from the frozen soft-cycle theorem.  It tests
whether the positive-clearance singleton-refusal limit can be consumed merely
by restricting to its support and invoking the checked two- or three-player
existence theorem.

The verdict is negative without a new source-preserving lift.  Small-player
existence controls every surviving player's unrestricted deviation after the
profile is lifted, but it says nothing about the deleted players' caps.  The
soft source has zero limiting debt for those outsiders only at that particular
timing law.  Two explicit four-player tables show that an exact equilibrium of
the support game can have an order-one outsider debt even though the same
outsider has zero debt along the diffuse positive-refusal source.

Thus support sizes two and three yield useful one- or two-outsider paid escape
sequences, but not a contradiction.  Full support has no deletion at all and
is exactly compatible with the checked paired-singleton hard matrix.

## Sources inspected

- `UniformEquilibrium/Quitting/Classification/PlayerDeletionLift.lean`:
  `quittingLiftDeletedProfile`,
  `quittingTerminalPayoff_liftDeletedProfile`,
  `quittingTerminalPayoff_update_liftDeletedProfile_eq_deleteDeviation`, and
  `quittingBestReplyValue_liftDeletedProfile`.
- `UniformEquilibrium/Quitting/Classification/PlayerReindex.lean`:
  `quittingGame_exists_uniformEquilibriumPayoff_of_card_eq_two` and
  `quittingGame_exists_uniformEquilibriumPayoff_of_card_eq_three`.
- `UniformEquilibrium/Quitting/Classification/TwoPlayer/Existence.lean`:
  `quittingGame_exists_uniformEquilibriumPayoff_twoPlayer` and its four
  possible output mechanisms.
- `UniformEquilibrium/Quitting/Classification/ThreePlayer/Existence.lean`:
  `quittingGame_exists_uniformEquilibriumPayoff_threePlayer`.  Its conclusion
  is existential and does not prescribe the payoff or terminal law.
- `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`:
  the terminal-approximation/uniform-payoff equivalence.
- `UniformEquilibrium/Quitting/Examples/BlockPair/FourPlayerPairedSingletonLCP.lean`
  and
  `UniformEquilibrium/Quitting/Examples/BlockPair/FourPlayerPairedSingletonResidualHard.lean`:
  the full-support matrix and its distinct stationary and period-two
  completions.
- `UniformEquilibrium/Quitting/Classification/LCP/NormalCore.lean`:
  `normalLayer`, `normalCore`, and the fixed distinct nonpositive-witness
  recursion.
- `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/NormalCorePunishmentNormal.lean`:
  `all_punishmentNormal_of_normalCore_eq_univ`.

## 1. Input from the frozen soft-cycle theorem

Let \(I=\operatorname{Fin}4\), put

\[
 s_i=r_i(\{i\}),\qquad A_{ik}=r_i(\{k\})-s_i,
\]

and suppose the period-one soft construction has reached its vanishing-hazard
limit.  It supplies one simplex weight \(\lambda\), a payoff

\[
 v=\sum_k\lambda_k r(\{k\}),
\]

and a number \(\kappa>0\) such that

\[
 (A\lambda)_i\ge\kappa,
 \qquad
 \lambda_i>0\Longrightarrow(A\lambda)_i=\kappa.       \tag{1.1}
\]

Write \(K=\operatorname{supp}\lambda\).  Then 

\[
 2\le |K|\le4.                                       \tag{1.2}
\]

At the actual soft source, every \(i\in K\) has limiting Never debt

\[
 \frac{\lambda_i\kappa}{1-\lambda_i}>0,              \tag{1.3}
\]

whereas every \(d\notin K\) has limiting unrestricted debt zero.  The latter
statement is source-specific: it uses the opponent stopping laws of the
displayed soft profiles, not only their payoff or terminal singleton mixture.

## 2. The exact support-lift adapter

Let \(J\subseteq I\) be nonempty and delete \(I\setminus J\).  Suppose that,
for every \(n\), \(\tau_n\) is a behavioral profile of the restricted game,
and let \(\widehat\tau_n\) be its canonical lift in which every deleted player
plays literal Never.

### Proposition 2.1 (what a cardinal reduction must actually prove)

Assume that

1. every surviving player's unrestricted terminal debt at \(\tau_n\) tends
   to zero;
2. every deleted player's unrestricted terminal debt at
   \(\widehat\tau_n\) tends to zero; and
3. after a subsequence, the bounded payoff vectors
   \(U(\widehat\tau_n)\) converge to one fixed vector \(u\).

Then \(u\) is a uniform-equilibrium payoff of the original game.

#### Proof

The checked deletion naturality identities preserve, exactly, the payoff and
every arbitrary behavioral deviation of a surviving player.  Hence item 1 is
also the surviving-player debt bound at the lifted profile.  Item 2 supplies
the remaining coordinates.  Thus \(\widehat\tau_n\) are unrestricted terminal
approximate Nash profiles with error tending to zero and fixed limiting
target \(u\).  The checked terminal selection theorem gives the conclusion.
\(\square\)

The small-player theorem supplies item 1 when \(|J|=2\) or \(3\), and payoff
compactness supplies item 3.  **Item 2 is the whole missing adapter.**  The
zero outsider debt at the original soft source does not establish it for the
new profiles \(\widehat\tau_n\).

Conversely, under a fixed original terminal gap \(\Gamma>0\), any lifted
restricted \(o(1)\)-equilibrium has, for all large \(n\), some deleted player
with debt at least \(\Gamma/2\).  For one deleted player its label is fixed;
for two deleted players one label is fixed after a subsequence.  This is a
genuine paid outsider sequence, but its source is the newly selected
small-player equilibrium, not the soft source in (1.1)--(1.3).

## 3. Support size two

When \(|K|=2\), the checked two-player theorem gives unrestricted terminal
approximants for the game restricted to \(K\).  Lifting them solves the two
owner coordinates exactly up to their error.  It does not solve either of
the two outsiders.

### Proposition 3.1 (exact two-support lift regression)

There is a four-player table with labels \(a,b,c,d\) and a diffuse source
whose normalized singleton weight is

\[
 \lambda=(1/2,1/2,0,0),\qquad \kappa=1/2,             \tag{3.1}
\]

such that both outsiders have zero debt at every sufficiently diffuse source,
but an exact terminal Nash equilibrium of the restricted \(\{a,b\}\)-game
has a lifted outsider debt equal to one.  Moreover, the normalized singleton
matrix has full recursive normal core.

#### Construction and verification

All unlisted rewards are zero.  Put

\[
 r_a(\{b\})=1,\qquad r_b(\{a\})=1,                  \tag{3.2}
\]

and, for \(e\in\{c,d\}\), put

\[
 r_e(\{a\})=r_e(\{b\})=1,\qquad
 r_e(\{a,e\})=r_e(\{b,e\})=2.                     \tag{3.3}
\]

Finally put

\[
 r_a(\{c\})=r_b(\{d\})=r_c(\{d\})=r_d(\{c\})=-1.   \tag{3.4}
\]

The solo rewards are zero.  Equation (3.1) follows directly:

\[
 A\lambda=(1/2,1/2,1,1).                            \tag{3.5}
\]

The fixed negative-witness map \(a\mapsto c\), \(b\mapsto d\),
\(c\mapsto d\), \(d\mapsto c\) survives every normal layer, so the recursive
normal core is all four players.  Hence this regression is compatible with
the checked counterexample-facing full-core and punishment-normality
conditions.

At the stationary source where \(a,b\) independently Quit with probability
\(h\) and \(c,d\) play Never, an outsider's Never value is

\[
 N_h=\frac{2(1-h)}{2-h}.                             \tag{3.6}
\]

If that outsider Quits at a chosen reached date, its current-row payoff is

\[
 Q_h=4h(1-h).                                        \tag{3.7}
\]

Every pure-time payoff is a convex combination of \(N_h\) and \(Q_h\).
For \(0<h\le1-1/\sqrt2\), \(Q_h\le N_h\), so Never is a cap response and
both outsider debts are exactly zero.

In the restricted game, the profile

\[
 a:\text{ Quit surely at date }0,\qquad b:\text{ Never} \tag{3.8}
\]

is an exact terminal Nash profile.  Player \(a\) always obtains zero whether
it Quits later or Never; player \(b\) obtains one and joining \(a\) gives the
unlisted pair reward zero.  After lifting (3.8), outsider \(c\) receives
\(r_c(\{a\})=1\), but Quit at date zero yields \(r_c(\{a,c\})=2\).  Its debt
is one.  The same holds for \(d\).  \(\square\)

This is not a counterexample to the Fin4 conjecture and does not say that
every restricted equilibrium lifts badly.  It proves the precise logical
point: source-wise outsider-zero debt plus unconditional two-player existence
does not imply Proposition 2.1(2).

## 4. Support size three

When \(|K|=3\), the checked AGKRS/three-player theorem gives a uniform payoff
for the restricted game.  There is now only one omitted player, so under the
original positive gap every lifted restricted approximant makes that same
outsider a fixed positive debtor.  Again, the theorem does not select a
restricted equilibrium whose timing law stays attached to the soft source.

### Proposition 4.1 (exact three-support lift regression)

There is a four-player table with \(K=\{a,b,c\}\) and

\[
 \lambda=(1/3,1/3,1/3,0),\qquad \kappa=2/3,          \tag{4.1}
\]

whose outsider \(d\) has zero debt along the diffuse \(K\)-source but debt one
at the lift of an exact terminal Nash profile of the restricted three-player
game.  Its normalized singleton matrix also has full recursive normal core.

#### Construction and verification

For distinct \(k,\ell\in K\), put

\[
 r_k(\{\ell\})=1,\qquad r_k(\{d\})=-1,
\]

and put every other reward of a player in \(K\) equal to zero.  For the
outsider put

\[
 r_d(\{a\})=-1,\qquad
 r_d(\{b\})=r_d(\{c\})=2,                            \tag{4.2}
\]

and

\[
 r_d(\{a,d\})=0,\qquad
 r_d(\{b,d\})=r_d(\{c,d\})=2,                        \tag{4.3}
\]

with its other rewards zero.  Then

\[
 A\lambda=(2/3,2/3,2/3,1),                           \tag{4.4}
\]

which proves (4.1).

Every owner in \(K\) has the fixed negative witness \(d\), and \(d\) has
the fixed negative witness \(a\).  Induction through the normal layers again
gives full recursive normal core.

Let the three owners independently Quit with probability \(h\), and let \(d\)
play Never.  Conditional on eventual opponent absorption, the three singleton
payoffs are \(-1,2,2\), while collision payoffs are zero, so Never tends to
one.  Quitting at a reached date has row payoff \(4h(1-h)^2\): a tie with
\(a\) pays zero, and a tie with either \(b\) or \(c\) pays two.  For all
sufficiently small \(h\), the pure-time envelope is therefore attained by
Never, so \(d\)'s debt is zero.

In the restricted game, let \(a\) Quit surely at date zero and let \(b,c\)
play Never.  This is exact terminal Nash: \(a\)'s every alternative pays zero,
while \(b,c\) receive one and joining gives an unlisted reward zero.  Its lift
pays \(d\) the singleton value \(-1\), whereas joining \(a\) pays zero.
Thus \(d\)'s lifted debt is one.  \(\square\)

The one-outsider case is therefore sharper only in label bookkeeping, not in
source attachment.  The exact missing theorem would have to produce
three-player terminal approximants whose lifts preserve the outsider's
pure-time obstacle envelope (or at least its cap inequality).  The existential
three-player headline does not carry this field.

## 5. Support size four

When \(|K|=4\), every coordinate satisfies

\[
 A\lambda=\kappa\mathbf1,\qquad \lambda_i>0,
 \qquad\kappa>0.                                     \tag{5.1}
\]

Equivalently \(z=\lambda/\kappa\) is a full-support standard-LCP solution for
right-hand side \(-\mathbf1\).  There is no outsider and hence no cardinal
reduction.

The checked paired-singleton matrix is the exact obstruction to treating
(5.1) itself as a cyclic compiler:

\[
 A=\begin{pmatrix}
 0&3&-1&-1\\
 3&0&-1&-1\\
 -1&-1&0&3\\
 -1&-1&3&0
 \end{pmatrix},\qquad
 \lambda=(1,1,1,1)/4,\qquad\kappa=1/4.              \tag{5.2}
\]

The repository has two completions with this same singleton matrix.  The
`stationaryCompletionReward` has an exact stationary uniform equilibrium,
whereas `boundaryReward` has no exact stationary terminal Nash profile but
has an exact period-two uniform equilibrium.  This is checked in
`stationaryCompletion_isUniformEquilibriumPayoff`,
`periodTwo_no_stationary_exactTerminalNash`, and
`periodTwo_isUniformEquilibriumPayoff` (with the combined residual statement
`periodTwo_residualHard_fullCore_nonstationary_but_uniform`).

Therefore a construction based only on the full-support LCP data and the
singleton rows cannot even determine whether period one suffices.  A generic
full-support consumer must use nonsingleton rewards and solve the conditional
endpoint inequalities; no such theorem was found in the inspected LCP
subtree.

## 6. Exact support-cardinality verdict

The three cases reduce as follows.

1. **Two owners.**  Two-player existence solves the owners, but two outsider
   cap inequalities remain.  Under a global gap, a subsequence of lifted
   restricted equilibria has a fixed paid outsider label.
2. **Three owners.**  Three-player existence solves the owners, but the unique
   outsider cap remains.  Under a global gap, that outsider is necessarily a
   fixed paid label at every sufficiently accurate lift.
3. **Four owners.**  There is no deletion.  The output is a source-attached
   full-support positive-level LCP solution, a known hard residual compatible
   with both stationary and genuinely periodic completions.

The support split therefore narrows the next theorem to one of two genuinely
source-sensitive statements:

- a **law-preserving small-player selection** whose lifted outsider caps stay
  asymptotically at their soft-source values; or
- a **two-source gluing theorem** connecting the soft source (owners paid,
  outsiders solved) to a lifted small-player equilibrium (owners solved,
  an outsider paid) while controlling the seam and all unrestricted caps.

Without one of these, the cardinal split returns to the already known
source-component nonanchoring obstruction.
