# Robust join predecessors produce a persistent-base uniform payoff

Authors: **CODEX_ROOT**, from a producer-form observation in the conference
intake and the earlier collision-cycle screen of **CODEX_EULER**

Independent reviews:
[CODEX_ARCHIMEDES](../feedback/CODEX_ROOT__ROBUST_JOIN_PREDECESSOR_BASE_ESCAPE__BY_CODEX_ARCHIMEDES.md),
[CODEX_RAMSEY](../feedback/CODEX_ROOT__ROBUST_JOIN_PREDECESSOR_BASE_ESCAPE__BY_CODEX_RAMSEY.md)

## Exact statement

Let (I) be a nonempty finite player set and let (r) be a quitting-game
reward table. At each live date, players independently choose Quit or
Continue. The first nonempty quitting coalition absorbs with reward (r),
and infinite all-Continue play pays zero.

For distinct (e,j\in I), define the **robust join relation**

\[
 e\mathrel{\trianglerighteq_r}j
 \quad\Longleftrightarrow\quad
 \forall T\subseteq I\setminus\{e,j\},\qquad
 r_j(T\cup\{e,j\})\ge r_j(T\cup\{e\}).              \tag{1}
\]

Thus, whenever (e) is in the terminal coalition, adding (j) never hurts
(j), uniformly over every other coalition background.

### Theorem A: robust-predecessor base

Let (C\subseteq I) have at least two members. Suppose that every (j\in C)
has a distinct (e\in C) satisfying (e\trianglerighteq_r j). Then:

1. (C) satisfies the checked predicate
   `QuittingPersistentBaseComplementLeaveSafe r C`;
2. the quitting game has a stationary exact terminal Nash profile against
   every unilateral behavioral deviation; and
3. the payoff of this profile is a uniform-equilibrium payoff.

The profile makes every member of (C) Quit surely at date zero. Players in
(I\setminus C) use a mixed Nash equilibrium of the induced finite binary
game.

### Theorem B: robust cycles and the DAG obstruction

If the directed graph of \(\trianglerighteq_r\) contains a directed cycle,
then the game has an exact terminal Nash profile against all behavioral
deviations and a uniform-equilibrium payoff.

Consequently, in every finite quitting game without a uniform-equilibrium
payoff, the robust join graph is acyclic. It has a topological ordering, and
every nonempty induced subgraph has a vertex with no robust predecessor inside
that subgraph.

### Theorem C: strict reversal on any positive selected cycle

Suppose a finite quitting game has no uniform-equilibrium payoff and is
supplied with distinct cycle vertices

\[
 e_0\to e_1\to\cdots\to e_{m-1}\to e_0,qquad m\ge2,
\]

such that, for a fixed \(\gamma>0\), every selected edge (e\to j) obeys

\[
 r_j(\{e,j\})-r_j(\{e\})\ge\gamma.                  \tag{2}
\]

Then some selected edge (e\to j) and some **nonempty** background

\[
 \varnothing\ne T\subseteq I\setminus\{e,j\}
\]

satisfy the strict reversal

\[
 r_j(T\cup\{e,j\})-r_j(T\cup\{e\})<0.             \tag{3}
\]

This statement is valid for every finite player type. Fin4 is the case where
the current checked theory produces such a positive selector cycle from the
failure of uniform-payoff existence.

### Theorem D: a Fin4 table class

Let (I=\operatorname{Fin}4). Assume the following finite table condition:

\[
 \begin{aligned}
 e\ne j,\quad r_j(\{e,j\})>r_j(\{e\})
 \quad\Longrightarrow\quad
 \forall T\subseteq I\setminus\{e,j\},\quad
 r_j(T\cup\{e,j\})\ge r_j(T\cup\{e\}).
 \end{aligned}                                      \tag{4}
\]

Then the four-player quitting game has a uniform-equilibrium payoff.

Equivalently, every hypothetical Fin4 counterexample must contain a positive
singleton-collision edge that reverses strictly on a nonempty background. In
four players, this is a pair-to-triple or triple-to-grand-coalition reversal.

## Conjecture-facing change

The earlier collision-cycle screen proved only that a positive selected cycle
has a weakly nonpositive background increment somewhere. Its complementary
branch had no semantic consumer.

The present adapter consumes that branch. Weak nonnegativity on every
background produces the already checked persistent-base arbitrary-completion
architecture, and therefore exact terminal Nash against unrestricted
behavioral deviations. Negating the consumed weak condition yields the strict
sign in (3).

The net change is:

\[
 \boxed{
 \text{robust join cycle}
 \Longrightarrow
 \text{exact all-behavior terminal Nash and uniform payoff}}
\]

and, in Fin4,

\[
 \boxed{
 \text{no uniform payoff}
 \Longrightarrow
 \text{strict nonempty-background reversal on a selected positive edge}.}
\]

This removes a genuine finite table class. It does not discharge the current
full-support hard residual, because a counterexample is now forced into the
strict-reversal side.

## Definitions and assumptions

The strategy space is the full behavioral strategy space. A unilateral
deviation may replace a player's entire history-dependent randomized stopping
law, including Never and arbitrarily late quitting.

The equilibrium produced by Theorem A is stationary, but the deviator is not
restricted to stationary, first-stage, finite-support, or pure-time
strategies. No public correlation or sunspot signal is used.

The relation in (1) is deliberately weak. Equality is sufficient because a
base member prescribed to Quit need only be a best response. The relation is
stronger than the checked leave-safe base condition: it quantifies over all
backgrounds disjoint from (e,j), including backgrounds that need not arise
when the rest of the selected base Quits.

## Source correspondence

The existing semantic consumer is checked in
[PersistentBaseArbitraryCompletionEscape.lean](../../../UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseArbitraryCompletionEscape.lean):

- `QuittingPersistentBaseComplementLeaveSafe`;
- `exists_quittingPersistentBaseCertificate_of_complementLeaveSafe`;
- `QuittingPersistentBaseCertificate.isZeroAsymptoticNash`; and
- `exists_exactTerminalNash_and_uniformPayoff_of_complementLeaveSafe`.

The Fin4 source data are checked in:

- [FullSupportProjectiveQBarResidual.lean](../../../UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/FullSupportProjectiveQBarResidual.lean),
  via
  `nonempty_finFourQuantitativeFullSupportHardResidual_of_no_uniformPayoff`
  and
  `uniformPayoff_or_nonempty_finFourQuantitativeFullSupportHardResidual`;
- [PunishmentNormalAtomicCollisionHandoff.lean](../../../UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/PunishmentNormalAtomicCollisionHandoff.lean),
  via
  `FinFourQuantitativeFullSupportHardResidual.exists_fixedPointFree_terminalGap_collisionMap`;
- [FiniteSerialRelation.lean](../../../MathUE/FiniteSerialRelation.lean), via
  `Math.FiniteSerialRelation.nonempty_periodicCycle_of_serial`, if the Fin4
  corollary is implemented through a finite functional orbit rather than a
  supplied simple-cycle structure.

For the bound-free Fin4 theorem, instantiate the hard-residual producer with
the canonical `quittingRewardBound reward`; the reward-bound premise is
discharged by `abs_reward_le_quittingRewardBound reward`.

The new mathematics is exactly:

1. the finite robust-predecessor graph criterion;
2. its adapter to `QuittingPersistentBaseComplementLeaveSafe`;
3. the strict selected-cycle reversal; and
4. the Fin4 sufficient table condition (4).

The equilibrium mechanism itself is not new. It is the checked persistent-base
arbitrary-completion compiler. The precursor
[collision-cycle screen](../notes/CODEX_EULER__FIN4_COLLISION_CYCLE_FACE_SIGN_CANCELLATION.md)
had only a static weak sign conclusion and no consumer for the robust branch.

## Proof

### 1. Robust predecessors imply complement-uniform leave safety

Fix (j\in C), choose a distinct robust predecessor (e\in C), and let

\[
 Q\subseteq I\setminus C
\]

be an arbitrary complementary quitting set. Define

\[
 T=(C\setminus\{e,j\})\cup Q.                       \tag{5}
\]

Since (Q) is disjoint from (C),

\[
 T\subseteq I\setminus\{e,j\}.                     \tag{6}
\]

The two coalitions in the robust comparison are exactly

\[
 T\cup\{e,j\}=C\cup Q,
 \qquad
 T\cup\{e\}=(C\setminus\{j\})\cup Q.             \tag{7}
\]

Applying (e\trianglerighteq_r j) to (T) gives

\[
 r_j((C\setminus\{j\})\cup Q)
 \le r_j(C\cup Q).                                  \tag{8}
\]

Because (j) and (Q) were arbitrary, (8) is precisely
`QuittingPersistentBaseComplementLeaveSafe r C`. The coalition on the left is
nonempty: (e\in C\setminus\{j\}). Thus no reward at the empty coalition is
used.

### 2. The checked consumer gives unrestricted terminal Nash

The checked persistent-base theorem selects a mixed Nash equilibrium of the
finite binary game played by (I\setminus C). Embed that mixed action profile
at date zero and prescribe every member of (C) to Quit surely.

After any one player's arbitrary behavioral deviation, at least one other
member of (C) still Quits surely at date zero because (|C|\ge2). Hence
absorption occurs at date zero under the prescribed profile and every
unilateral deviation. Later behavior is irrelevant.

For a complementary player, only its date-zero binary action matters, and
finite-game Nash optimality rules out an improvement. For (j\in C),
conditional on the complementary quitter set (Q), prescribed Quit pays
(r_j(C\cup Q)), while Continue pays
(r_j((C\setminus\{j\})\cup Q)). Inequality (8) rules out improvement
pointwise in (Q), hence after averaging and after arbitrary randomization of
the deviator's date-zero action.

This proves exact terminal Nash against the full behavioral strategy class.
The checked theorem then returns its payoff as a uniform-equilibrium payoff.

### 3. Directed cycles

For a simple directed cycle

\[
 e_0\trianglerighteq_r e_1\trianglerighteq_r\cdots
 \trianglerighteq_r e_{m-1}\trianglerighteq_r e_0,
 \qquad m\ge2,
\]

take (C=\{e_0,\ldots,e_{m-1}\}). Every vertex has its preceding cycle vertex
as a distinct robust predecessor, so Theorem A applies. Any directed closed
walk contains a simple directed subcycle. Therefore absence of a uniform
payoff implies absence of every directed robust cycle, proving the DAG
conclusion.

### 4. Strict reversal

Assume the hypotheses of Theorem C. If every selected cycle edge were robust,
Theorem B would produce a uniform-equilibrium payoff, contrary to assumption.
Therefore some edge (e\to j) is not robust. Negating the universal weak
inequality in (1) gives a background (T) satisfying the strict inequality
(3). Condition (2) excludes (T=\varnothing). This proves Theorem C.

### 5. The Fin4 table class

Suppose (4) holds but the Fin4 game has no uniform-equilibrium payoff. Use
`quittingRewardBound reward` and `abs_reward_le_quittingRewardBound reward` in
the checked no-uniform-payoff hard-residual theorem. The checked collision-map
theorem then gives a fixed-point-free map (f:\operatorname{Fin}4\to
\operatorname{Fin}4) and a terminal gap \(\gamma>0\) with

\[
 r_{f(e)}(\{e,f(e)\})-r_{f(e)}(\{e\})\ge\gamma>0
\]

for every (e). Condition (4) makes every edge (e\to f(e)) robust. A
fixed-point-free map on a finite nonempty set has a directed cycle of length
at least two, so Theorem B produces a uniform-equilibrium payoff, a
contradiction. This proves Theorem D.

## Boundary tests

### Weak equality

For the zero reward table, every distinct pair is robust with equality. Every
sure-quitting base of size at least two is exact. Thus replacing `>=` by `>`
would unnecessarily weaken the result.

### Two-cycle and empty complement

For (C=\{e,j\}), the two robust inequalities are exactly the two
complement-uniform leave inequalities. Either deviator still faces the other
sure quitter. If (C=I), the complementary game is empty and the same direct
argument applies.

### Singleton base

The cardinality condition is sharp for this construction. With one base
member, that player can Continue and expose the tail. In a one-player game
with singleton reward (-1), sure Quit is not Nash, while all-Continue is.

### Arbitrary outsider rewards

No sign or support restriction is imposed on outsiders' rewards. Their
induced finite game may have no pure equilibrium; the checked construction
uses a mixed Nash equilibrium. The sure-quitting base still collapses every
behavioral deviation to its date-zero action.

### Robustness is sufficient, not necessary

A leave-safe base may fail the global robust relation on a background that
cannot arise while the other base members Quit. For a three-player base,
player (j) may dislike joining predecessor (e) when the third base player
is absent but weakly prefer joining whenever that third player is present.
The checked leave-safe condition sees only the latter backgrounds.

### Exact equilibrium need not be a pure stable coalition

The complementary players may mix. Hence a table can satisfy this theorem
without having a pure stable terminal coalition. Such a table is nevertheless
inside the already checked persistent-base arbitrary-completion architecture;
this is not a new equilibrium mechanism outside that architecture.

### Falsification audit

Two reviewers independently checked weak equality, the two-cycle boundary,
the empty complementary game, arbitrary outsider rewards requiring a mixed
completion, the singleton failure, the unrestricted deviation class, and the
strict negation used in (3). No counterexample or unresolved premise survived.

## Adapter and consumer

The actual-data adapter is finite and literal:

\[
 \text{reward table + base + robust predecessors}
 \longmapsto
 \texttt{QuittingPersistentBaseComplementLeaveSafe}.
\]

No semantic carrier, compactness selection, cap root, or independently chosen
source profile appears in this step.

The downstream consumer is the checked theorem
`exists_exactTerminalNash_and_uniformPayoff_of_complementLeaveSafe`. It
constructs one actual stationary profile, proves exact terminal Nash against
all unilateral behavioral deviations, and supplies a uniform-equilibrium
payoff.

For Theorem D, the source adapter is also checked: failure of uniform-payoff
existence produces a quantitative Fin4 hard residual, and that residual
produces the literal fixed-point-free positive collision map. The new robust
adapter consumes the map under condition (4).

## Lean handoff

The narrow implementation should live beside
`PersistentBaseArbitraryCompletionEscape.lean`. Suggested declarations are:

```lean
def QuittingRobustJoin
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (enforcer joiner : ι) : Prop :=
  enforcer ≠ joiner ∧
  ∀ background,
    background ⊆ (Finset.univ.erase enforcer).erase joiner →
    quittingSetReward reward
        (insert joiner (insert enforcer background)) joiner ≥
      quittingSetReward reward (insert enforcer background) joiner

def QuittingRobustPredecessorBase
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (base : Finset ι) : Prop :=
  2 ≤ base.card ∧
  ∀ joiner ∈ base,
    ∃ enforcer ∈ base, QuittingRobustJoin reward enforcer joiner

theorem QuittingRobustPredecessorBase.complementLeaveSafe ... :
    QuittingPersistentBaseComplementLeaveSafe reward base

theorem exists_exactTerminalNash_and_uniformPayoff_of_robustPredecessorBase ...

theorem exists_uniformPayoff_of_robustJoinCycle ...

theorem finFour_collisionMapCycle_has_strictBackgroundReversal ...

theorem finFour_exists_uniformPayoff_of_noStrictBackgroundReversal ...
```

Only the first four declarations are needed for the general consumer. A
cycle wrapper may accept a supplied simple cycle or reuse
`Math.FiniteSerialRelation.nonempty_periodicCycle_of_serial`. The Fin4 theorem
should instantiate the hard-residual bound with `quittingRewardBound reward`
and discharge it with `abs_reward_le_quittingRewardBound reward`.

No new behavioral strategy, cap, Bellman, or stopping-law infrastructure is
needed.

## Scope and nonclaims

This packet does not prove the finite-quitting conjecture or close the Fin4
hard residual. It removes the robust selected-cycle side and forces a strict
background reversal in every hypothetical Fin4 counterexample.

It does not claim that robust predecessors are necessary for a persistent
base, that every exact equilibrium is pure, or that numerical examples
satisfying the criterion evade existing checked architectures.

The general robust-predecessor adapter and strict corollaries are ordinary
mathematics in this packet. Their semantic consumer, the Fin4 no-uniform
residual producer, and the Fin4 collision-map producer are already checked in
Lean under the source files named above. The new adapter and its corollaries
are now formalized as recorded below.

## Formalization record

The packet is formalized at its full reviewed scope in two production
modules:

- `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/`
  `RobustJoinPredecessorBase.lean` contains `QuittingRobustJoin`,
  `QuittingRobustPredecessorBase`,
  `QuittingRobustPredecessorBase.complementLeaveSafe`, the exact stationary
  Nash and uniform-payoff compiler, the supplied `PeriodicCycle` adapter,
  the predecessor-free-vertex theorem for every nonempty induced subgraph,
  standard finite-DAG acyclicity, a topological order, and exclusion of every
  robust periodic cycle under nonexistence;
- `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/`
  `RobustJoinStrictBackgroundReversal.lean` contains the arbitrary-finite
  `selectedCycle_has_strictBackgroundReversal_of_no_uniformPayoff` and the
  bound-free Fin4 table theorem
  `finFour_exists_uniformPayoff_of_noStrictBackgroundReversal`.

Evidence seals:

- **M:** PASS. Two independent reviews and the final cross-audit checked the
  coalition identities, weak inequality orientation, cycle representation,
  strict negation, nonempty-background argument, and the Fin4 reward-bound
  bridge.
- **L:** PASS. Both files pass direct and named Lean builds. Representative
  axiom probes report only `propext`, `Classical.choice`, and `Quot.sound`.
- **A:** PASS. The general producer consumes a literal reward table, base,
  and robust predecessors. The Fin4 theorem internally selects the checked
  same-table hard residual and its fixed-point-free positive collision map at
  the canonical `quittingRewardBound`; no residual, bound, selector, or cycle
  is supplied by the caller.
- **C:** PASS. The robust base is consumed by the existing persistent-base
  compiler into one stationary exact terminal Nash profile against all
  behavioral deviations and its uniform-equilibrium payoff. The selected
  cycle is consumed into a strict nonempty-background reversal, and the Fin4
  no-reversal predicate is consumed into a literal uniform payoff.

The implementation permits repeated nonadjacent vertices in the supplied
periodic cycle; positivity forces adjacent vertices to be distinct. All
terminal coalitions used by the robust comparison contain the enforcer, so
the zero extension of `quittingSetReward` at the empty coalition is never
used semantically.

Nonclaims:

- robust predecessors are sufficient, not necessary, for a leave-safe base;
- the complementary mixed Nash completion need not be pure;
- the strict reversal supplies no quantitative negative margin beyond strict
  sign and no chronology or profile realizing that background;
- the Fin4 theorem solves only the displayed static reward-table class, not
  the full hard residual or the finite-quitting conjecture; and
- this restriction is not a new node in `docs/QuittingProofFrontier.json`:
  that file tracks the maintained positive-minimum chronology DAG, whereas
  the present theorem removes a separate static Fin4 table chamber.
