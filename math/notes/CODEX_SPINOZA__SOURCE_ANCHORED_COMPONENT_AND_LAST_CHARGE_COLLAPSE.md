# Source-anchored equilibrium components and the last-charge collapse

Identity: `CODEX_SPINOZA`

## Current status

**Ordinary mathematics; one positive finite-game anchoring theorem and one
exact obstruction.  No Fin4 consumer is claimed.**  A large subsidy on one
distinguished complete source law removes the point-anchoring defect of the
usual strategy-entry continuation: the unique top equilibrium and some
unsubsidized finite-clock equilibrium lie in one connected Nash component.
Under a positive terminal exploitability gap, the bottom equilibrium has
positive physical absorption and unfolds along its reached live history to a
finite exact Nash--Bellman block.

This still does not give a source-reprojected block.  An arbitrary-length
exact block whose terminal annotation is a prescribed source payoff has
positive charge if and only if that payoff already admits a positive-
absorption exact **one-row** root.  The last charged row proves the reverse
implication.  Hence essential components and finite-chain gluing cannot
bypass the unique-all-Continue root chamber while keeping the literal source
tail.  A rational four-player table below has two co-sourced debts of size
`3/4`, a unique all-Continue root at the source payoff, and a charged terminal
Nash sibling.  Thus even the repaired anchored component can end at a charged
exact block while no positive exact block reprojects to the original source.
The table has global minimum debt zero, so a successful theorem must use the
positive global minimum essentially.

## 1. Question

Start with the actual finite-clock source and two distinct full-gap pure-time
responses supplied by
[`FINITE_CLOCK_DOUBLE_FULL_GAP_COSOURCE.md`](../exports/FINITE_CLOCK_DOUBLE_FULL_GAP_COSOURCE.md).
Can a global variational or essential-equilibrium-component argument produce
a finite exact Nash--Bellman block which

1. ends at the literal source continuation (or at a continuation with seam
   summable relative to its charge),
2. has positive physical Quit hazard, and
3. can therefore be glued into the checked chronological consumers?

The point of this note is to distinguish two notions of anchoring which that
question cannot conflate:

* **component anchoring:** a path of auxiliary finite-game equilibria starts
  at the named actual source law;
* **chronological anchoring:** the terminal annotation of the exact block is
  the payoff of the named literal source tail.

The first can always be manufactured.  The second is equivalent to a
positive one-row root at the source payoff.

## 2. Last-charge collapse

Fix a finite player set and a quitting reward table.  Let

\[
 B=(v_0,q_0,v_1,\ldots,q_{N-1},v_N)
\tag{2.1}
\]

be a positive-length finite exact Nash--Bellman block:

\[
 v_t=F(q_t,v_{t+1}),\qquad
 q_t\text{ is exact root Nash against }v_{t+1}.
\tag{2.2}
\]

Write `Abs(q)` for one-stage absorption probability.  Total marginal hazard
is positive exactly when `Abs(q_t)>0` for at least one displayed row.

### Theorem 2.1 (a source-reprojected exact block collapses to one row)

For every payoff vector `s`, the following are equivalent.

1. There is a finite exact Nash--Bellman block with terminal annotation
   `v_N=s` and positive total marginal hazard.
2. There is a product root `q` which is exact root Nash against `s` and has
   `Abs(q)>0`.

More precisely, in any block from item 1 let `t` be the greatest index with
`Abs(q_t)>0`.  Then

\[
 q_{t+1}=\cdots=q_{N-1}=\mathsf{AllContinue},
 \qquad
 v_{t+1}=\cdots=v_N=s,
\tag{2.3}
\]

so `q_t` is already the root in item 2.

#### Proof

Zero absorption of a product root says that every marginal Quits with
probability zero, hence the root is literally all Continue.  The Bellman map
of the all-Continue root is the identity.  By maximality of `t`, every later
root has zero absorption, and backward use of this identity gives (2.3).
Exactness at row `t` now says precisely that `q_t` is exact root Nash against
`s`; its absorption is positive by definition.  Conversely, a positive root
against `s`, together with its Bellman predecessor `F(q,s)`, is a one-row
block.  \(\square\)

The same proof works with terminal annotation `T` different from the desired
source `s`: positive charge implies a positive exact root at `T`.  Therefore
the only freedom introduced by an approximate source reprojection is the
terminal seam `dist(T,s)` itself; extra exact rows do not soften the root
problem at `T`.

### Corollary 2.2 (essential components cannot cross an all-Continue moat)

Let `K` be a compact set of source payoff vectors contained in an open set
`N` on which all Continue is the unique exact product root.  There is
`rho>0` such that any positive-charge exact block whose desired source
anchor lies in `K` has terminal seam at least `rho`.

Consequently, for a sequence of such anchors, summable terminal seams permit
only finitely many positively charged exact blocks.  In particular no
equilibrium-component or finite-chain construction with literal source
ancestry and summable seams can create the two persistent clocks required by
the exact-spine consumer while all regenerated sources remain in this moat.

This corollary is already checked in stronger form as
`exists_uniform_terminal_separation_of_positiveAbsorption`,
`finite_positiveAbsorptionBlocks_of_summable_restartSeams`, and
`summable_hazardCharge_of_summable_restartSeams` in
`UniformEquilibrium/Quitting/Bellman/Finite/AllContinueBasinRestartMoat.lean`.
Theorem 2.1 isolates the elementary reason arbitrary block length cannot
repair the terminal source: strip the trailing zero-charge rows and the last
charged row sees the terminal annotation itself.

Under the Fin4 no-uniform-payoff hypothesis, the compact minimum payoff
fibre lies in exactly such a robust all-Continue basin.  Thus a global
component argument can help only by moving the terminal continuation outside
that basin.  That move is the macroscopic source seam; it is not erased by
the connectedness or index of the component.

## 3. A genuinely source-anchored finite-game component

The preceding obstruction should not be confused with the earlier point-
anchoring defect of a new-strategy homotopy.  That defect has a simple global
repair at the finite-game level.

Let `G` be a finite normal-form game with pure-action sets `A_i` and hard
payoffs in `[-M,M]`.  Fix an arbitrary mixed source profile
`sigma=(sigma_i)`.  Add for every player a distinguished pure meta-action
`b_i` whose hard payoff consequences are exactly those of independently
drawing from `sigma_i`.  Thus a mixed use of `b_i` decodes affinely to an
ordinary mixed strategy on `A_i`.

For `kappa in [0,K]`, give player `i` an additional payoff `kappa` whenever
it chooses `b_i`, with `K>2M`.  Denote the resulting auxiliary game by
`G_kappa^sigma`.

### Theorem 3.1 (unique-top source anchoring)

The Nash graph

\[
 Z=\{(\kappa,x):0\le\kappa\le K,
                 \ x\in\operatorname{NE}(G_\kappa^\sigma)\}
\tag{3.1}
\]

has a compact connected component which contains the literal point
`(K,b)` and meets the face `kappa=0`.  Every point on the bottom face decodes
to an ordinary Nash equilibrium of `G`.

#### Proof

At `kappa=K`, choosing `b_i` gains the bonus `K`, while the difference
between any two hard payoffs is at most `2M`.  Hence `b_i` is strictly
dominant for every player and `b` is the unique top-face equilibrium.

Apply the standard Nash fixed-point map continuously parameterized by
`kappa` and Browder continuation.  Some compact connected fixed-point
component meets both parameter faces.  Its top endpoint must be `(K,b)` by
uniqueness.  At `kappa=0`, replacing mass on `b_i` by the mixed law `sigma_i`
does not change any hard expected payoff against any opponent profile.
Therefore the affine decoding of a bottom equilibrium is a Nash equilibrium
of `G`.  \(\square\)

This is stronger than the usual entrant-penalty component, whose top face is
the whole old Nash set and therefore need not contain a prescribed old Nash
point.  Here the distinguished source is the unique top point.

### Corollary 3.2 (application to the finite-clock co-source)

Let `sigma` be the co-source from the exported double-full-gap theorem, with
support contained in `{0,...,H-1,Never}`.  Apply Theorem 3.1 to the finite
timing game with pure clocks `{0,...,H,Never}` and with `b_i` decoding to
`sigma_i`.

If the quitting game has a positive terminal exploitability gap, the
all-Never profile is not a bottom equilibrium: against all Never, every
finite stopping time pays the singleton reward, so the gap forces some
positive singleton reward and clock zero is already in the menu.  Hence the
decoded bottom equilibrium has positive physical absorption.

Along every positively reached live date, changing one conditional hazard
and retaining the later conditional law is another mixed law on the same
finite clock menu.  Finite-game Nash therefore gives exact one-row endpoint
Nash at that date.  Bellman recursion is the literal conditional-payoff
identity.  Truncating at the first surely absorbing row if necessary, and
choosing an arbitrary payoff-consistent off-path continuation there, unfolds
the bottom equilibrium into a positive-charge finite exact Nash--Bellman
block in the canonical reward box.

Thus the global component method really does provide:

\[
 \text{named finite co-source}
 \longrightarrow
 \text{one source-anchored auxiliary component}
 \longrightarrow
 \text{a charged exact finite-clock Nash--Bellman sibling}.
\tag{3.2}
\]

It does **not** provide a chronological arrow from the sibling back to
`sigma`.  The component parameter is an artificial action subsidy, and its
intermediate equilibria are equilibria of the subsidized games.  Replacing
the bottom block's terminal annotation by `U(sigma)` is legal exactly in the
case characterized by Theorem 2.1.

## 4. Exact rational regression

The distinction in (3.2) occurs in a four-player quitting table with a very
simple source.

Call players `0,1` active and players `2,3` passive.  For every nonempty
coalition `S`, define

\[
 r_i(S)=
 \begin{cases}
 -1,&i\in S,\\
  1,&i\notin S,
 \end{cases}
 \quad(i=0,1),
\tag{4.1}
\]

and

\[
 r_i(S)=
 \begin{cases}
 1,&i\in S,\\
 10,&i\notin S,
 \end{cases}
 \quad(i=2,3).
\tag{4.2}
\]

Let the two active players independently Quit at date zero with probability
`1/2` and otherwise use Never; let both passive players use Never.  Call this
actual finite-clock profile `sigma`.

### Proposition 4.1 (two debts but no exact source-reprojected charge)

The prescribed payoff, unrestricted cap, and debt vectors at `sigma` are

\[
 U(\sigma)=(-1/4,-1/4,15/2,15/2),
\tag{4.3}
\]

\[
 B(\sigma)=(1/2,1/2,31/4,31/4),
\qquad
 d(\sigma)=(3/4,3/4,1/4,1/4).
\tag{4.4}
\]

In particular players `0` and `1` have co-sourced attained Never responses
of gain `3/4`.

Nevertheless all Continue is the unique exact product root against the
source payoff vector `s=U(sigma)`.  Hence no positive-charge finite exact
Nash--Bellman block has terminal annotation `s`.

#### Proof

For an active player, Never earns `1` exactly when the other active player
quits at date zero, and earns zero otherwise, giving cap `1/2`.  Quitting at
date zero earns `-1`; quitting later earns
`(1/2)1+(1/2)(-1)=0`, so Never is optimal.  Direct enumeration gives the
active prescribed payoff

\[
 -(1/2)+(1/2)(1/2)=-1/4.
\]

A passive Never player receives `10` if at least one active player quits,
an event of probability `3/4`, giving `15/2`.  Quitting after date zero adds
the singleton payoff `1` on the remaining probability `1/4`, giving the cap
`31/4`.  This proves (4.3)--(4.4), including unrestricted behavioral caps
because a player's payoff is affine in its stopping law and the displayed
pure times exhaust the three possible order classes relative to date zero.

Against continuation `s`, an active player's Quit endpoint is always `-1`.
Its Continue endpoint is a convex combination of `-1/4` (no opponent quits)
and `1` (some opponent quits), hence is strictly greater than `-1` for every
opponent product root.  Thus both active players strictly Continue in every
exact root.  A passive player's Quit endpoint is always `1`, while its
Continue endpoint is a convex combination of `15/2` and `10`, hence is
strictly greater than `1`.  Both passive players also strictly Continue.
The exact-root set is therefore the singleton all-Continue root.  Theorem
2.1 excludes every positive exact block ending at `s`.  \(\square\)

### Proposition 4.2 (the anchored component still has a charged bottom)

The all-Never profile is not terminal Nash, because either passive player
can Quit and receive `1`.  Indeed, the one-row profile in which player `2`
Quits surely and every other player uses Never is an exact terminal Nash
profile: player `2` gets `1`; active outsiders get `1` and would get `-1` by
joining; passive outsider `3` gets `10` and would get `1` by joining.

Apply Theorem 3.1 to the clock menu `{0,Never}` and the source `sigma`.
Every bottom equilibrium has positive absorption, since all Never is not an
equilibrium.  Hence the source-anchored auxiliary component reaches a charged
exact finite-clock block.  Proposition 4.1 proves that no such charged block
can be reprojected to terminal annotation `U(sigma)`.  The component has
ended at a source sibling, not a chronological descendant.

This table has a terminal Nash profile, so its global minimum terminal debt
is zero.  It does not refute a theorem using the hypothetical Fin4 condition
`D_*>0`.  It proves the exact logical boundary: co-sourced full debts,
finite-clock source data, a unique-top source-anchored essential component,
and a charged exact bottom block still do not imply a source-reprojected
charged block.  Positive global minimum must exclude the unique-all-Continue
source payoff or pay the terminal displacement.

## 5. Variational and finite-chain verdict

Theorems 2.1 and 3.1 leave no hidden exact multistep advantage.

1. A variational search over arbitrary-length exact blocks ending at a fixed
   source has positive optimum charge exactly when the one-row root
   correspondence at that source already has a positive member.
2. An essential equilibrium component can be anchored to the named source by
   a strict source subsidy, but after the subsidy is removed its exact block
   is only a sibling.  The component supplies no Bellman connector from that
   sibling to the original source.
3. Moving the terminal annotation outside a unique-all-Continue moat is an
   actual semantic seam.  The checked restart-moat theorem makes summable
   seams allow only finitely many charged blocks.  The checked positive-debt
   carrier-cycle toll separately prevents stationary nonnegative rematching
   from cancelling that cost.

The finite-clock double-full-gap theorem therefore enters this lane only up
to (3.2).  It supplies the named source and makes the source profile
non-equilibrium at the top after the subsidy is removed, but it does not put a
positive root at `U(sigma)`.

### Theorem 5.1 (global-gap root or source-atom alternative)

There is nevertheless one exact use of the global gap at the original
co-source.  Suppose every actual profile has a unilateral gain at least
`Gamma>0`, and let `sigma` be any finite-clock actual source with payoff
`s=U(sigma)`.  Then at least one of the following holds.

1. There is a positive-absorption exact root against `s`, hence a literal
   zero-seam one-row block ending at the source by Theorem 2.1.
2. There are a player `k` and a nonempty terminal coalition `S` such that,
   for the terminal law `mu_sigma`,

   \[
   r_k(\{k\})\ge\Gamma,
   \qquad s_k\ge\Gamma,
   \qquad
   \mu_\sigma(S)\max\{r_k(S),0\}\ge{\Gamma\over2^{|I|}-1}.
   \tag{5.1}
   \]

   In particular, if all rewards have absolute value at most `M>0`,

   \[
   \mu_\sigma(S)\ge
   {\Gamma\over M(2^{|I|}-1)}.
   \tag{5.2}
   \]

For Fin4 the denominator is `15`.

#### Proof

At the all-Never profile, a player's unrestricted cap is
`max(0,r_i({i}))`.  The global gap therefore selects `k` with
`r_k({k})>=Gamma`.

If item 1 fails, finite root-Nash existence still supplies an exact root
against `s`.  Every root of zero absorption is all Continue, so failure of
item 1 forces all Continue itself to be exact.  Its player-`k` endpoint
inequality gives

\[
 s_k\ge r_k(\{k\})\ge\Gamma.                         \tag{5.3}
\]

Since Never pays zero,

\[
 s_k=\sum_{\varnothing\ne A\subseteq I}
       \mu_\sigma(A)r_k(A).
\]

The sum of the positive summands is at least `Gamma`.  Among the
`2^|I|-1` nonempty coalitions, one positive summand is therefore at least
the right side of (5.1).  The reward bound gives (5.2).  \(\square\)

This is the strongest source-attached finite partition obtained from the
anchored component without pretending that the component parameter is play
time.  In branch 1 the requested exact block exists.  In branch 2 the
macroscopic displacement from the source payoff to the all-Never terminal
annotation is not anonymous: it is carried by one positive terminal-law atom
at the **same finite co-source**.  Together with either of the two debts from
the exported theorem, this is valid input to the checked source-supported
paid-first-disagreement-row construction.

It is not yet a terminal consumer.  The atom player `k` need not be either
co-source debtor, the atom need not lie at either selected response cut, and
the paid-row output is not automatically an exact root.  Thus the finite
partition reaches the maintained quantitative paid-port interface but does
not make its off-minimum/inert output renewable.  This is exactly where a
claim that component continuation itself was a chronological transition
would overreach.

### Proposition 5.2 (oriented component partition)

Retain the two distinct cap candidates `e_i,e_j` at the co-source, each with
gain at least `Gamma`, and include both candidates in the unsubsidized finite
menu of Theorem 3.1.  Choose a semialgebraic path `x(t)`, `0<=t<=1`, in the
spanning component, oriented from the unique subsidized source endpoint to a
bottom equilibrium.  Decode every `x(t)` to its actual finite stopping-law
profile and evaluate **hard**, unsubsidized candidate gains

\[
 g_\ell(t)=U_\ell(e_\ell,x_{-\ell}(t))-U_\ell(x(t)),
 \qquad \ell\in\{i,j\}.
\tag{5.4}
\]

Then `g_i(0),g_j(0)>=Gamma`, while `g_i(1),g_j(1)<=0`.
Let `t_*` be the first parameter at which either gain reaches
`Gamma/2`.  At the actual profile `x(t_*)`, both unrestricted debts are at
least `Gamma/2`, and one displayed candidate has gain exactly `Gamma/2`.

Consequently the initial component segment has the following exhaustive
finite partition.

1. Some actual path source `x(t)`, `0<=t<=t_*`, has a positive exact root
   against its payoff.  Theorem 2.1 gives a literal zero-seam charged block
   ending at that source.
2. Every such payoff admits only the all-Continue exact root.  At the endpoint
   `x(t_*)`, Theorem 5.1 supplies the positive source-law atom (5.1)--(5.2),
   while the two original labelled candidates still give co-sourced debts at
   least `Gamma/2`.  Applying the checked paid-row localization to either
   debt produces an actual source-supported paid first-disagreement row at
   that same endpoint.

#### Proof

The finite expected-payoff functions in (5.4) are continuous.  The top
decodes to `sigma`, giving the two lower bounds.  The bottom is Nash in a
menu containing both candidates, giving the two upper bounds.  Continuity and
the first-hitting construction give the common half-gap endpoint.  Apply
Theorems 2.1 and 5.1 according as a positive exact root occurs or not.  In
the second arm, candidate payoff is bounded above by the unrestricted cap,
so both debts have the asserted floor; the checked positive-debt paid-row
theorem then applies.  \(\square\)

This is a genuine orientation of the **auxiliary component**, and it retains
the two candidate labels until the first half-gap crossing.  Its second arm
is still not a chronological source transition from `sigma` to `x(t_*)`.
Only the paid row produced at `x(t_*)` is literal play data.  Thus this
partition lands exactly at the maintained paid-port renewal question; it
does not solve that question by reinterpreting the component path as play.

The precise remaining positive-minimum question is:

> Can the co-source be selected so that its payoff admits a positive exact
> root, or else can the global excess debt of every co-source outside the
> minimum fibre be spent once to move its terminal annotation out of the
> all-Continue moat and then return by an accepted chronological port?

The first conclusion gives a literal zero-seam one-row block by Theorem 2.1.
The second must carry the source displacement explicitly; essential-component
index alone cannot make it summable.

## 6. Sources inspected and nonclaims

Checked declarations inspected:

* `IsQuittingNashBellmanEdge` and the finite block structure in
  `UniformEquilibrium/Quitting/Bellman/Finite/NashBellmanSpine.lean` and
  `UniformEquilibrium/Quitting/Bellman/Finite/UnboundedExactBlockHazardCapacity.lean`;
* `root_eq_allContinue_of_terminal_mem_uniqueBasin`,
  `exists_uniform_terminal_separation_of_positiveAbsorption`,
  `finite_positiveAbsorptionBlocks_of_summable_restartSeams`, and
  `summable_hazardCharge_of_summable_restartSeams` in
  `UniformEquilibrium/Quitting/Bellman/Finite/AllContinueBasinRestartMoat.lean`;
* `exists_isZeroQuittingRootNash` in
  `UniformEquilibrium/Quitting/Root/NashExistence.lean`;
* the positive-minimum exact-root basin declarations named in
  [`CODEX_SPINOZA__MINIMUM_SOURCE_EXACT_BLOCK_NORMALIZED_SEAM_FLOOR.md`](CODEX_SPINOZA__MINIMUM_SOURCE_EXACT_BLOCK_NORMALIZED_SEAM_FLOOR.md);
* `not_exists_uniformEquilibriumPayoff_iff_exists_terminalExploitabilityGap`
  in `UniformEquilibrium/Quitting/Terminal/ExploitabilityGap.lean`; and
* the checked seam consumer summarized in
  [`CHRONOLOGICAL_SHADOWING_SEAM_REDUCTION.md`](../formalized/CHRONOLOGICAL_SHADOWING_SEAM_REDUCTION.md).

The Browder continuation step is ordinary finite-game mathematics, not a
checked declaration in this repository.  No paper theorem is being used to
claim quitting-game chronology: the component theorem is explicitly kept on
the auxiliary finite-game side.

This note does not construct a uniform-equilibrium payoff, an unrestricted
terminal approximate Nash profile, a positive-gap table, or a renewable
source port.  It does not treat finite replacement/component ancestry as
temporal play.  Its exact contribution is to remove ordinary component
point-nonanchoring and then prove that the stronger chronologically anchored
exact-block target still collapses to the one-row source root problem.
