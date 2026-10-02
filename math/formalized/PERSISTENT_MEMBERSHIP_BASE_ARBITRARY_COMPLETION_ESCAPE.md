# Persistent membership bases admit arbitrary-completion escape

Authors: CODEX_EULER

Independent reviews:

- [`CODEX_MINER`](../feedback/CODEX_EULER__PERSISTENT_MEMBERSHIP_BASE_UNIVERSAL_ESCAPE__BY_CODEX_MINER.md)
- [`CODEX_RAMSEY`](../feedback/CODEX_EULER__PERSISTENT_MEMBERSHIP_BASE_UNIVERSAL_ESCAPE__BY_CODEX_RAMSEY.md)

## Exact statement

Let `I` be a finite player set, let `r` be a quitting-game reward table on
the nonempty coalitions of `I`, and let `G` be a set of players with
`2 <= |G|`.  Put `F = I \ G`.  Suppose that every base player weakly prefers
to remain in every terminal coalition generated from the base and the free
players:

\[
 r_i(G\cup Q)\ge r_i((G\setminus\{i\})\cup Q)
 \qquad(i\in G,\ Q\subseteq F).                 \tag{1}
\]

Then the quitting game has an exact stationary terminal Nash profile against
arbitrary behavioral unilateral deviations.  Consequently it has a
uniform-equilibrium payoff.

In particular, (1) holds strictly when every base player's coordinate is its
literal membership indicator,

\[
 r_i(S)=\mathbf 1_{\{i\in S\}}
 \qquad(i\in G,\ \varnothing\ne S\subseteq I). \tag{2}
\]

All reward coordinates of players in `F` may be arbitrary.

For the six-player two-target architecture, take a persistent target pair
`A` as `G` and let `B` be a disjoint target pair.  Every completion preserving
(2) on `A`, while changing all coordinates of players outside `A`
arbitrarily, has such an exact equilibrium.  Every terminal coalition in the
constructed equilibrium contains `A`, so its exact `B`-atom has probability
zero.

## Conjecture-facing change

This gives a negative answer for one precisely defined universal architecture
allowed by [`questions/INCENTIVE_GADGET.md`](../questions/INCENTIVE_GADGET.md):
the missing second-pair mass cannot be forced by modifying only the
second-pair or passive-player reward coordinates while preserving a
two-player persistent membership base.  The outsiders can always
re-equilibrate in a finite induced binary game, producing a sure-exit exact
equilibrium with zero mass on the disjoint second pair.

It strictly narrows the remaining gadget search: a viable construction must
change at least one persistent-base payoff coordinate, violate the pointwise
leave inequalities (1), or abandon the persistent-base architecture.

## Definitions and assumptions

The game is the standard discrete-time quitting game.  At every live date,
each player independently chooses Quit or Continue according to its behavioral
strategy at the unique all-Continue history.  The first nonempty coalition of
quitters absorbs and receives `r(S)`; infinite all-Continue play receives
zero.  A unilateral deviation may be an arbitrary history-dependent
behavioral strategy.

Define the finite binary normal-form game on the free player set `F`.  A pure
action profile chooses a set `Q subseteq F` of free quitters and gives each
free player `j` payoff

\[
 r_j(G\cup Q).
\]

This finite game has a mixed Nash equilibrium `x`.  Define the ambient
stationary root `q` by making every member of `G` Quit surely and giving every
member of `F` its coordinate of `x`.

## Source correspondence

The induced game, its mixed-Nash existence, and its root embedding are already
checked in
`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseInducedGame.lean`,
notably:

- `quittingPersistentBaseUtility`;
- `quittingPersistentBaseRoot`;
- `quittingPersistentBaseNashSet_nonempty`; and
- `quittingPersistentBaseRoot_free_purePayoff_le`.

The existing unrestricted semantic compiler is checked in:

- `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseNashSemanticAdapter.lean`, via
  `nonempty_quittingPersistentBaseCertificate_of_inducedNash` and
  `exists_uniformPayoff_of_persistentBase_inducedNash_signs`; and
- `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseSemanticDispatch.lean`, via
  `QuittingPersistentBaseCertificate.isUniformEquilibriumPayoff`.

The new mathematical content is the arbitrary-completion adapter: choosing
`F = I \ G` makes the outside-player screen empty, the induced mixed Nash
handles every unrestricted free-player reward coordinate, and (1) supplies
the only remaining base-player sign condition.  A narrow declaration search
found the general compiler but no theorem packaging this adapter or its
six-player target-pair consequence.

## Proof

Choose a mixed Nash equilibrium `x` of the induced finite binary game and use
the stationary root `q` above.

Fix a free player `j in F` and replace its entire behavioral strategy
arbitrarily.  Every member of `G` still Quits at date zero, so absorption at
date zero has probability one.  Only `j`'s randomized date-zero action can
affect its payoff; every later prescription is irrelevant.  Conditional on
Quit or Continue at date zero, its payoffs are exactly the two pure-action
payoffs in the induced binary game against `x_{-j}`.  Mixed-Nash optimality
bounds both, and therefore bounds every randomized date-zero action.  Thus no
arbitrary behavioral deviation by a free player is profitable.

Now fix a base player `i in G` and replace its entire behavioral strategy.
Because `|G| >= 2`, another base player still Quits surely at date zero.  The
deviation therefore cannot expose a continuation.  Conditional on the
realized free-quitter set `Q`, player `i` receives

\[
 r_i(G\cup Q)
\]

if it Quits at date zero, and

\[
 r_i((G\setminus\{i\})\cup Q)
\]

if it Continues.  The second coalition is nonempty, and (1) says the
prescribed Quit action is weakly optimal pointwise in `Q`.  Averaging over
`Q` and over the deviator's randomized date-zero action proves that no
arbitrary behavioral deviation by a base player is profitable.

These are all players because `F = I \ G`.  Hence the stationary profile is
an exact terminal Nash profile against unrestricted behavioral deviations.
The checked persistent-base semantic compiler then yields its
uniform-equilibrium payoff.

Under (2), the two conditional base payoffs are respectively `1` and `0`, so
(1) holds strictly.  In the six-player specialization, every realized
coalition contains `A`; it therefore cannot equal the disjoint pair `B`, and
the exact `B`-atom has mass zero.

## Boundary tests

- The free-player equilibrium may be genuinely mixed, for example in a
  matching-pennies-type induced game.  Certain base absorption still reduces
  every free behavioral deviation to its date-zero binary action.
- The complement `F` may be empty.  The induced zero-player game has its
  unique mixed profile, and the all-base sure-Quit profile remains exact.
- Outsider rewards may be arbitrarily large, negative, or dependent on the
  full terminal coalition.  They only change the utilities and Nash point of
  the finite induced game.
- A base player may deviate to Continue forever.  Another base member still
  absorbs at date zero, so the deviation is governed exactly by (1).
- The stated compiler requires `2 <= |G|`.  The theorem deliberately makes no
  singleton-base claim; with a singleton base, a deviation can expose the
  continuation, and a separate argument would be required.
- An empty base does not satisfy the hypotheses and gives no sure-exit
  mechanism.

These tests were independently rederived in both cited falsification reviews.

## Adapter and consumer

The arbitrary source data are exactly a finite reward table and a base `G`
satisfying (1).  The finite-game Nash theorem produces the induced point; no
stationary equilibrium, target atom, or favorable outsider action is assumed.
The pointwise leave inequalities and complement identity instantiate the
checked `QuittingPersistentBaseCertificate`.  Its checked semantic consumer
produces an unrestricted uniform-equilibrium payoff.

For the incentive-gadget question, the semantic output is stronger than a
failure of one candidate profile: every reward table in the completion class
has an exact equilibrium with zero disjoint-target atom.  Thus this entire
universal gadget architecture cannot produce the required pair-mass lower
bound from low exploitability.

## Lean handoff

A narrow corollary can live beside
`PersistentBaseNashSemanticAdapter.lean`.  Its likely statement should take:

- `base : Finset ι` with `2 <= base.card`;
- `free := Finset.univ \ base`;
- either the pointwise leave inequalities (1), expressed on coalitions
  `base union Q`, or the membership-coordinate specialization (2).

The proof should:

1. choose a point using `quittingPersistentBaseNashSet_nonempty`;
2. instantiate `exists_uniformPayoff_of_persistentBase_inducedNash_signs`;
3. discharge disjointness and `base union free = univ`;
4. rewrite each base endpoint difference as the expectation of the
   pointwise leave gaps; and
5. discharge the outside-player condition vacuously.

A second small corollary may specialize to the two disjoint pairs in
`SixPlayerOnePairMassTargetLock.lean` and prove that the constructed profile's
`targetB` terminal mass is zero.  The external formalizer should reuse the
existing induced-game and persistent-base definitions rather than introduce a
new certificate structure.

## Scope and nonclaims

This is not a new uniform-equilibrium compiler, a solution of the full
incentive-gadget question, or a proof of the finite-quitting conjecture.  It
does not cover architectures that modify base-player coordinates, violate
(1), use a singleton base, or avoid a persistent sure-Quit base.  It proves
only that arbitrary completion of the complementary players cannot overcome
a two-player persistent membership/leave-safe base.

## Formalization record

The packet was split into two production modules and formalized at its full
reviewed scope:

- `PersistentBaseArbitraryCompletionEscape.lean` contains
  `QuittingPersistentBaseComplementLeaveSafe`,
  `exists_quittingPersistentBaseCertificate_of_complementLeaveSafe`,
  `QuittingPersistentBaseCertificate.isZeroAsymptoticNash`,
  `exists_exactTerminalNash_and_uniformPayoff_of_complementLeaveSafe`, and the
  literal-membership specialization
  `exists_exactTerminalNash_and_uniformPayoff_of_persistentBaseMembershipReward`;
- `PersistentBaseArbitraryCompletionSixPlayer.lean` contains
  `exists_targetA_exactTerminalNash_uniformPayoff_and_secondPairMass_zero`.

The general theorem internally selects the induced mixed Nash point. Its
stationary embedding is exact terminal Nash against the project's unrestricted
behavioral deviation class and supplies a uniform-equilibrium payoff. In the
six-player specialization, the same package additionally proves exact zero
terminal mass on the disjoint second target pair.

Evidence seals are `M`, `L`, `A`, and `C`: the mathematics received two
independent reviews; both files pass direct and named Lean builds; the source
adapter assumes only the reward table, a base of cardinality at least two, and
the displayed complement leave inequalities; and the exact behavioral Nash,
uniform-payoff, and zero-atom conclusions are checked consumers. Axiom probes
use only `propext`, `Classical.choice`, and `Quot.sound`.

The result does not cover singleton or empty bases, changes to the protected
base coordinates which violate leave safety, or architectures without a
persistent sure-Quit base. It eliminates this universal gadget architecture;
it does not solve the remaining incentive-gadget question or the finite-
quitting uniform-equilibrium conjecture.
