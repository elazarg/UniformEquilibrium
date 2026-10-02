# Independent falsification of persistent-membership-base universal escape

Reviewer: **CODEX_RAMSEY**  
Source: [`notes/CODEX_EULER__PERSISTENT_MEMBERSHIP_BASE_UNIVERSAL_ESCAPE.md`](../notes/CODEX_EULER__PERSISTENT_MEMBERSHIP_BASE_UNIVERSAL_ESCAPE.md)  
Verdict: **PASS**  
Export recommendation: **assemble a narrow packet, then require a fresh whole-packet gate**

## Claim checked

Let `I` be finite, let `G` be a finset with `2 <= G.card`, and put
`F = univ \ G`.  Suppose that for every `i in G` and every nonempty terminal
coalition `S`, player `i`'s reward is the literal membership indicator

\[
r_i(S)=\mathbf 1_{\{i\in S\}},
\]

with no restriction on any coordinate belonging to `F`.  The note chooses a
mixed Nash point of the induced binary game on `F`, makes all members of `G`
Quit surely, and claims an exact stationary terminal Nash profile against
arbitrary behavioral deviations and therefore a uniform-equilibrium payoff.
It also claims the corresponding six-player obstruction when `G=targetA`:
arbitrary changes to outsider coordinates cannot force a positive exact
`targetB` atom while retaining the `targetA` membership coordinates.

I rederived the result before comparing the other review.

## Independent proof check

### 1. Induced binary game and payoff identification

The induced action of a free player is a single Boolean Quit/Continue choice.
For a pure action profile `a` on `F`, the ambient terminal coalition is exactly

\[
G\cup\{j\in F:a_j=Q\}.
\]

This is precisely the definition of `quittingPersistentBaseUtility`, and the
identification with the ambient zero-tail root payoff is proved by
`quittingRootPayoff_principalExtend_persistentBase` and
`expectedUtility_persistentBase_eq_rootExpectedPayoff` in
`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseInducedGame.lean`.
The extension `quittingPersistentBaseRoot` makes base coordinates pure Quit,
free coordinates equal to the selected mixed point, and any coordinate
outside `base union free` pure Continue.

The finite-game Nash existence theorem applies to the subtype `F`, including
when `F` is empty.  In particular,
`quittingPersistentBaseNashSet_nonempty` has no nonemptiness assumption on the
player type; the required nonemptiness of each Boolean action set is vacuous
when there are no free players.

### 2. Arbitrary behavioral replacement by a free player

Fix `j in F` and replace its entire behavioral strategy arbitrarily.  Every
member of `G` remains a sure quitter at date zero, so absorption still occurs
at date zero with probability one.  The deviator observes no prior history;
only the distribution of its date-zero Boolean choice can affect its payoff.
All later prescriptions and private randomization after that choice are
irrelevant.

Conditional on the other free players' independent date-zero actions, the two
possible payoffs are exactly the two pure payoffs in the induced binary game.
Mixed-Nash optimality bounds both pure choices and hence every distribution on
those choices.  This is also the content of
`quittingPersistentBaseRoot_free_purePayoff_le`.  Thus the argument covers an
unrestricted behavioral replacement, not merely a stationary replacement.

### 3. Arbitrary behavioral replacement by a base player

Fix `i in G`.  Since `2 <= G.card`, choose another base member
`g in G \ {i}`.  Player `g` still Quits surely at date zero after any unilateral
replacement by `i`; consequently no continuation suffix is exposed.

For every realized free-quitter set `Q subseteq F`, the two date-zero choices
of `i` give

\[
r_i(G\cup Q)=1,
\qquad
r_i((G\setminus\{i\})\cup Q)=0.
\]

The second coalition is nonempty because it contains `g`.  Hence prescribed
sure Quit beats Continue by exactly one, pointwise in `Q`, and it also beats
every randomized date-zero choice.  Again, all later behavior is irrelevant.
This verifies both the sign and the orientation of the compiler's
`base_leave` field: `quittingRootEndpointDifference` is Quit minus Continue.

The generalized condition (3.1) in the note is also sufficient.  Its
pointwise nonnegative Quit-minus-Continue differences average under the
induced product law to the required nonnegative endpoint difference.

### 4. Coverage, the full-base boundary, and the outside screen

For `F=univ \ G`, `G` and `F` are disjoint and their union is `univ`.
Therefore the compiler's condition on players outside `G union F` is
vacuous.  If `G=univ`, then `F` is empty and the unique zero-player mixed
profile is the required induced Nash point.  The base-deviation proof remains
valid because `G.card >= 2`.  Thus the theorem includes the full-base case
without an implicit nonempty-complement assumption.

The restriction `G.card >= 2` is exactly what the named compiler needs and is
also exactly what makes every unilateral base replacement leave a sure
opponent quitter.  The note correctly does not claim the singleton-base case.

### 5. Checked unrestricted uniform-payoff consumer

`nonempty_quittingPersistentBaseCertificate_of_inducedNash` in
`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseNashSemanticAdapter.lean`
combines:

- the induced-Nash free-coordinate inequalities;
- the base leave inequalities just proved; and
- the vacuous outside join screen.

The resulting certificate has zero row Continue mass and, crucially, zero
fixed-opponents Continue mass for every player because another member of the
two-player base remains a sure quitter.  In
`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseSemanticDispatch.lean`,
`QuittingPersistentBaseCertificate.isUniformEquilibriumPayoff` uses these
facts with
`isUniformEquilibriumPayoff_of_stationaryEndpointCertificate_contracts`.
That compiler first yields exact terminal Nash in the project's unrestricted
behavioral strategy space and then the uniform-equilibrium payoff.  The
conclusion is therefore stronger than a stationary best-response calculation
and is stated correctly.

### 6. Six-player specialization

The source convention in
`UniformEquilibrium/Quitting/Paths/SixPlayerOnePairMassTargetLock.lean` is
explicit: the mathematical labels `1,...,6` are represented by `0,...,5` in
`Fin 6`, while `targetA={player1,player2}` and
`targetB={player3,player4}`.  Thus the note's mathematical notation
`A={1,2}`, `B={3,4}` agrees with the source.

At the constructed profile every terminal coalition contains `targetA`.
Since `targetA` and `targetB` are distinct two-element target pairs, the
terminal coalition cannot equal `targetB`; its exact `targetB` atom therefore
has mass zero.  No outsider reward sign, magnitude, passivity, or purity
assumption enters this conclusion.

## Attempted falsifiers

- **Mixed free equilibrium:** matching-pennies-type free-player rewards cause
  no problem; the induced finite game may be genuinely mixed, while sure base
  quitting still makes every behavioral deviation a date-zero binary choice.
- **Empty free face:** the induced player type is empty, but the checked Nash
  carrier remains nonempty and the all-base sure-Quit row is exact.
- **A base player Continues forever:** another base member absorbs at date
  zero, so the deviation receives the membership value zero and cannot expose
  a favorable tail.
- **Large or sign-indefinite outsider rewards:** these change only the finite
  induced game's utilities and its selected Nash point.  They do not disturb
  the base security argument or the compiler's contraction.

None falsifies the theorem.

## Novelty and scope

The strategic compiler itself is checked and old.  The new content is the
thin but useful architecture-level adapter: when the persistent base has
literal membership coordinates and the free set is the complete complement,
the base and outside sign screens are automatic, so **every** completion of
the outsider coordinates is solved by an induced mixed equilibrium.  The
pure-set theorem
`pureSet_terminalNash_and_uniformPayoff_of_membershipToggles` does not subsume
this arbitrary-completion statement because it requires the outsider join
signs at the fixed pure base; the present argument lets outsiders
re-equilibrate jointly.

This removes exactly the six-player completion family that preserves the
first target pair as a persistent literal membership base.  It does not rule
out changing a target-member coordinate, using a singleton base, or abandoning
the persistent-base architecture.

## Verdict and export recommendation

**PASS.** I found no mathematical, probability-semantic, boundary, or source
correspondence repair.  After completing my derivation, I compared
`feedback/CODEX_EULER__PERSISTENT_MEMBERSHIP_BASE_UNIVERSAL_ESCAPE__BY_CODEX_MINER.md`;
its independent PASS agrees, including on the empty-free boundary and the
unrestricted-deviation point.

This is now supported by two independent falsification reviews.  I recommend
assembling a narrow export packet advertised as an arbitrary-outsider-data
adapter to the existing persistent-base compiler and as a precise no-go for
the named second-pair completion architecture.  Because this feedback reviews
the theorem note rather than a final packet, the packet should still receive a
fresh whole-packet `exports/README.md` gate before placement or promotion.  It
must not be presented as a new all-behavior compiler or as a general solution
of the incentive-gadget question.
