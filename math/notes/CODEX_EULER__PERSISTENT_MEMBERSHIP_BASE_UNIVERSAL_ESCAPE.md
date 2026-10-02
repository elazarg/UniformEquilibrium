# Persistent membership bases admit a universal stationary escape

**Owner:** CODEX_EULER  
**Status:** independently reviewed and Lean-formalized as
[`PERSISTENT_MEMBERSHIP_BASE_ARBITRARY_COMPLETION_ESCAPE.md`](../formalized/PERSISTENT_MEMBERSHIP_BASE_ARBITRARY_COMPLETION_ESCAPE.md)  
**Question:** can a completion of the checked six-player first-pair ledger force
positive mass on the disjoint second target pair while preserving the first
pair's membership coordinates?

## 1. Exact result

Let `I` be a finite player set and let

\[
 r:\{S\subseteq I:S\ne\varnothing\}\longrightarrow \mathbb R^I
\]

be an otherwise arbitrary quitting reward table.  Let `G` be a persistent
base with `|G| >= 2`, and put `F=I\G`.  Assume only that every member of `G`
has its literal membership-indicator coordinate:

\[
 r_i(S)=\mathbf 1_{\{i\in S\}}
 \qquad(i\in G,\quad \varnothing\ne S\subseteq I).                 \tag{1.1}
\]

There is no restriction at all on `r_j(S)` for `j in F`.

### Theorem 1.1 (arbitrary-completion escape)

Under (1.1), the quitting game has an exact stationary terminal Nash profile
against unrestricted behavioral deviations and hence has a
uniform-equilibrium payoff.

More precisely, choose a mixed Nash equilibrium `x` of the finite binary game
on `F` whose terminal coalition at an action `a in {Q,C}^F` is

\[
 G\cup\{j\in F:a_j=Q\}
\]

and whose payoff to `j in F` is the corresponding coordinate of `r`.  In the
quitting profile, every member of `G` quits surely at date zero and the free
players use `x`.  This stationary profile is an exact terminal Nash profile.

### Corollary 1.2 (the maintained six-player completion lane is impossible)

In the notation of `SixPlayerOnePairMassTargetLock.lean`, let

\[
 A=\{1,2\},\qquad B=\{3,4\}.
\]

Every completion which preserves

\[
 r_i(S)=\mathbf 1_{\{i\in S\}}\quad(i\in A)
\]

but changes *arbitrarily* every coordinate belonging to players outside `A`
has an exact all-behavior stationary equilibrium.  Its terminal coalition
contains `A` with probability one, so its exact `B`-atom mass is zero.

Consequently the missing second-pair producer cannot be obtained by modifying
only the second-pair/passive players' reward coordinates while retaining the
checked first-pair membership ledger.  At least one first-pair coordinate must
be changed, or the architecture must abandon this persistent-base form.

This conclusion is strictly broader than the previously checked robust
cross-penalty completion: the outsider coordinates here can have arbitrary
signs and magnitudes, and the outsider equilibrium may be genuinely mixed.

## 2. Proof

Set `F=univ \ G`.  The finite induced binary game has a mixed Nash equilibrium
`x`.  Extend it to a quitting root `q` by setting

\[
 q_i=1\ (i\in G),\qquad q_j=x_j\ (j\in F).                         \tag{2.1}
\]

There are no coordinates outside `G union F`.

For a free player `j in F`, all base players quit at date zero even after a
unilateral replacement by `j`.  Hence the game absorbs at date zero and the
payoff of an arbitrary behavioral replacement depends only on its date-zero
Quit/Continue choice.  The two resulting values are exactly the two pure
actions in the induced binary game.  Nash optimality of `x` therefore bounds
every unrestricted behavioral deviation by the prescribed payoff.

For a base player `i in G`, another member of `G` still quits surely after
`i` is replaced because `|G| >= 2`.  Conditional on every realization `Q` of
the free quitters, quitting gives

\[
 r_i(G\cup Q)=1,
\]

whereas continuing gives

\[
 r_i((G\setminus\{i\})\cup Q)=0.                                  \tag{2.2}
\]

Thus the base leave endpoint difference is exactly `1`, in particular
nonnegative.  Again later behavior is irrelevant because the other base
member absorbs at date zero.

These are all players.  They prove exact terminal Nash directly.  They also
match the checked persistent-base compiler literally:

1. `quittingPersistentBaseNashSet_nonempty` supplies `x`;
2. `quittingPersistentBaseRoot_free_purePayoff_le` supplies the free
   endpoint inequalities;
3. (2.2) supplies `base_leave`;
4. `F=univ\G` makes the outsider-join screen vacuous; and
5. `exists_uniformPayoff_of_persistentBase_inducedNash_signs` supplies the
   unrestricted uniform-equilibrium payoff.

The compiler's use of a terminal payoff is harmless here: the row's continue
mass and every player's opponents-continue mass are zero because at least two
base coordinates quit surely.  In particular, no stationary-only deviation
restriction is being smuggled into the conclusion.

## 3. A useful stronger hypothesis form

The indicator normalization is more than the proof needs.  The same argument
works if, for every `i in G` and every `Q subseteq F`,

\[
 r_i(G\cup Q)\ge r_i((G\setminus\{i\})\cup Q).                     \tag{3.1}
\]

Indeed the base endpoint difference is the expectation, under the induced
Nash product law on `F`, of the pointwise differences in (3.1).  This gives a
nonnegative `base_leave` sign.  The outsider coordinates remain arbitrary.

For the requested six-player decision lane, the narrower indicator statement
already suffices and has the especially transparent strict difference `1`.

## 4. Boundary tests

### 4.1 Mixed outsiders

Nothing selects a pure outsider action.  If the induced outsider game is
matching-pennies-like, choose its mixed Nash equilibrium.  The proof is
unchanged because a unilateral free-player deviation sees certain date-zero
absorption by `G`.

### 4.2 Unbounded and non-passive outsider rewards

The theorem uses neither a common reward bound nor a passive-coordinate
condition.  Finiteness of the table is enough for the induced finite-game
Nash theorem.  Outsider rewards may depend arbitrarily on the complete
coalition.

### 4.3 Why two persistent quitters are retained in the formal statement

The checked `QuittingPersistentBaseCertificate` compiler assumes
`2 <= G.card`; it obtains zero opponents-continue mass for every coordinate.
For the target pair this is exact.  A separate singleton-anchor theorem may
also be true for literal membership coordinates by bounding the anchor's
entire payoff by one, but it is unnecessary here and is not claimed as part
of Theorem 1.1.

### 4.4 Why the old pure-`A` escape was narrower

The pure coalition `A` is stable only if every outsider weakly prefers not to
join `A`.  Arbitrary completion can violate that pure sign.  The present
theorem lets all outsiders re-equilibrate simultaneously in their induced
binary game; this removes every outsider sign restriction while keeping the
same sure base.

## 5. Exact source audit

Inspected declarations:

- `quittingPersistentBaseNashSet_nonempty`,
  `quittingPersistentBaseRoot`,
  `isNash_of_mem_quittingPersistentBaseNashSet`, and
  `quittingPersistentBaseRoot_free_purePayoff_le` in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseInducedGame.lean`;
- `exists_uniformPayoff_of_persistentBase_inducedNash_signs` and
  `nonempty_quittingPersistentBaseCertificate_of_inducedNash` in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseNashSemanticAdapter.lean`;
- `QuittingPersistentBaseCertificate.isUniformEquilibriumPayoff` in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseSemanticDispatch.lean`;
- `pureSet_terminalNash_and_uniformPayoff_of_membershipToggles` and the
  six-player target definitions in
  `UniformEquilibrium/Quitting/Paths/SixPlayerOnePairMassTargetLock.lean`.

The last pure-set theorem does **not** subsume Theorem 1.1: it requires every
outsider's pure join sign at `G`.  The persistent-base induced-Nash interface
does subsume all but the new actual-data observation that (1.1), or more
generally (3.1), automatically supplies every remaining base sign while the
complement choice makes the outsider screen empty.

A narrow repository search found no packaged theorem stating this
arbitrary-outsider-completion corollary.

## 6. Scope and next action

This is a positive theorem for a nontrivial candidate counterexample
architecture, not a counterexample to the conjecture.  It eliminates the
maintained completion class in which only second-pair/passive coordinates are
changed while the first pair remains a literal membership base.  It does not
rule out changing the first-pair coordinates while preserving weaker mass
inequalities, nor does it address architectures without a persistent base.

Because it changes the named second-pair producer boundary and invokes an
unrestricted-strategy compiler, it should receive independent falsification
before any export or formalization proposal.
