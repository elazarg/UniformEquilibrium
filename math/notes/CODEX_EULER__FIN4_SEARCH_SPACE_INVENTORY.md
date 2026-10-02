# CODEX_EULER — Fin4 search-space inventory

## Status

Exact finite combinatorial count and source audit, followed by alignment
theorems, 2026-08-24.  The Burnside counts below were checked both from the
conjugacy-class formula and by direct permutation-cycle enumeration.
Sections 8--9 are independently reviewed and proved in Lean.  The decoder is
`MarkedRootedLasso.twoCyclePair?_eq_none_iff_hasLongCycle`; the source-facing
capstone is
`FinFourQuantitativeFullSupportHardResidual.exists_collisionGeometry_with_alignedTwoCycleHardPair_or_long`.
The formalization is
`UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/TwoCycleLassoHardPairAlignment.lean`.
The theorem-level reviews are
`feedback/CODEX_EULER__FIN4_SEARCH_SPACE_INVENTORY__BY_CODEX_RAMSEY__SECTIONS_8_9.md`
and
`feedback/TWO_CYCLE_LASSO_HARD_PAIR_ALIGNMENT__BY_CODEX_RAMSEY__PACKET_GATE.md`.
The second review passes the mathematics and initially classified the result
below the semantic-chamber threshold for `exports/`; the user explicitly
authorized exporting this finite alignment result, and the Section 11 delta
packet gate subsequently passed. Section 12 is independently reviewed and is
packaged separately at the same user-authorized finite-alignment scope.
Section 10 remains internal ordinary mathematics. None of Sections 10--12 is
claimed to be a semantic compiler.  Section 13 audits the checked downstream
rooted-two consumer and gives a complete rational sharpness completion: even
its full numerical collision chain, together with every static full-support
hard-residual field except the terminal witness, can coexist with an exact
sure-exit equilibrium.  Thus the next step must retain additional global
witness provenance; the extracted local payoff chain is not itself compiler
data.  Sections 14--15 now retain that provenance.  The maximal form is the
source-audited composition in Theorem 15.1: the checked atomic-blocker barrier
forces a terminal-gap-sized collision join from **every** punishment-normal
singleton.  Applied to the owner-leave collision chain, this upgrades the
receiving singleton to a full terminal-gap step.  The composition is ordinary
mathematics pending independent falsification; it is not yet a compiler for
the resulting gap-collision graph.  Section 16 is independently reviewed and
exported as `exports/FIN4_LEAVE_JOIN_STATIONARY_TWO_DEBTOR_HANDOFF.md`.
Section 17 composes the reviewed linear absorption price with the checked
compact minimum fiber: any positive-charge exact conversion at the literal
Section 16 tail must begin a fixed semantic-debt distance above that fiber.
It passed independent review and is exported as
`exports/FIN4_STATIONARY_PAID_CARRIER_LINEAR_DEBT_MOAT.md`.  New Section 18
attacks the quantitative collision-premium arm of Cedar's independently
reviewed blocker seam.  A pure-pair terminal-gap toggle either gives a
full-gap pair-to-triple join, or forces the owner to leave; the checked
all-player atomic collision at the receiving singleton then supplies a third
label and enters the existing stationary two-debtor semantic handoff.  This
is ordinary mathematics pending independent falsification.  Sections 19--21
then consume the pair-to-triple arm and the solo-wall residual into either a
literal charged debt descent or the same stationary two-debtor source.
Section 22 records the final in-flight implication-mining result: the checked
singleton-base repaired paid handoff exists for every preselected owner, so
owner-coordinate mismatch is not a remaining obstruction.  It remains
internal because the paid observer, terminal law, and Bellman chronology are
not aligned and no connector or return is produced.

## Question

What is actually finite after the current `Fin 4` full-support reduction, and
what remains a continuous or behavioral search problem?  In particular,
distinguish:

1. exact utility equivalence of quitting games, using simultaneous player
   relabeling and legitimate positive affine normalizations of each player's
   *complete* outcome utility; and
2. the much coarser finite sign skeleton of the off-diagonal normalized
   singleton matrix.

The authoritative maintained obligation is
`questions/FOUR_PLAYER_SINGLETON_PACKET_DISPATCH.md`.

## Source audit

The bounded source set inspected was:

- `uniformPayoff_or_quantitative_fullSupport_fullNormalCore_of_finFour` and
  `exists_quantitative_fullSupport_fullNormalCore_of_finFour_of_no_uniformPayoff`
  in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/NormalTerminalGapConstrainedStationary.lean`;
- `QuittingNormalizedSingletonSourcePacket` in
  `UniformEquilibrium/Quitting/Classification/ThreePlayer/AnalyticPacket.lean`;
- `normalizedSoloMatrix` and the translation adapter in
  `UniformEquilibrium/Quitting/Classification/LCP/Normalization.lean`;
- `QuittingTerminalExploitabilityWitness` and
  `HasTerminalExploitabilityGap` in the terminal exploitability sources;
- `exists_fourPlayerCounterexample_fusedResidual` in
  `Research/Quitting/FourPlayerCounterexampleFusion.lean`; and
- the strict-covector tail fields in
  `UniformEquilibrium/Diagnostics/Quitting/Chronology/PositiveDebtDynamicTailWitness.lean`
  and `StrictCovectorDynamicTail.lean`.

The maintained frontier explicitly records
`fullSupportPacket_standardQ_nonhomogeneous_but_not_cyclic`: singleton/LCP
properties do not by themselves provide the missing semantic dispatch.

## 1. Exact games do not form a finite quotient

A four-player repository reward table has

\[
(2^4-1)\cdot4=15\cdot4=60
\]

real terminal coordinates.  The Never payoff is canonically zero.  On the
complete 16-outcome table (15 absorbing coalitions plus Never), a legitimate
utility normalization is

\[
u_i'(\omega)=a_i u_i(\omega)+b_i,\qquad a_i>0,
\]

for every outcome, including Never.  If both representatives are put back in
the repository convention `Never = 0`, the translation parameter disappears:
the intersection of an affine utility orbit with the zero-Never slice is just
positive scaling by `a_i`.  Thus the generic quotient of the 60-dimensional
repository space by the four positive scales has dimension 56; quotienting
further by the finite group `S_4` does not remove the continuum.

Equivalently, starting with all 64 complete-table coordinates and quotienting
by four translations and four positive scales again gives generic dimension
56.  This also explains a common trap: subtracting each player's solo payoff
from all terminal rows is strategically legitimate only if the transformed
Never payoff is retained.  The project's normalized LCP table does retain
that translated Never coordinate.  Dropping it is not an exact equivalence of
repository games.

Therefore the ambient exact-equivalence quotient has cardinality continuum,
not a finite class count.  The counterexample-side residual itself may be
empty if the conjecture is true; no checked theorem parametrizes or counts its
exact equivalence classes.

## 2. The finite singleton sign skeleton

Write

\[
M(i,j)=r_i(\{j\})-r_i(\{i\}),\qquad i\ne j.
\]

There are 12 ordered off-diagonal positions.  Positive per-player scaling
preserves their signs, and `S_4` acts by

\[
(i,j)\longmapsto (\pi i,\pi j).
\]

For a `k`-coloring of these 12 positions, Burnside's lemma uses the following
cycle counts for the induced action on ordered pairs:

| permutation type | class size | cycles on `i != j` |
|---|---:|---:|
| `1^4` | 1 | 12 |
| `2,1,1` | 6 | 7 |
| `2,2` | 3 | 6 |
| `3,1` | 8 | 4 |
| `4` | 6 | 3 |

Hence

\[
N_k=\frac{k^{12}+6k^7+3k^6+8k^4+6k^3}{24}.
\]

For the three colors `negative / zero / positive`,

\[
N_3=\frac{3^{12}+6\cdot3^7+3\cdot3^6+8\cdot3^4+6\cdot3^3}{24}
=22{,}815.
\]

For strict sign matrices, with colors `negative / positive`,

\[
N_2=\frac{2^{12}+6\cdot2^7+3\cdot2^6+8\cdot2^4+6\cdot2^3}{24}
=218.
\]

These are the exact numbers of *ambient qualitative singleton skeletons* up
to simultaneous player relabeling.  They are not counts of exact games and
not counts of skeletons satisfying the current full-support/full-normal-core
residual.  Feasibility of `M mu >= 0`, recursive normal-core membership,
punishment normality, and the semantic terminal witness depends on real
magnitudes and nonsingleton rows.  Two matrices with the same sign skeleton
can behave differently under those tests.

## 3. Continuous data left by the current theorem

Even after fixing one of the finite singleton sign skeletons, the following
data remain continuous or infinite-dimensional.

- **The reward table.**  Singleton magnitudes and four own-solo baselines
  remain real.  More decisively, the 11 nonsingleton coalitions contribute
  exactly
  \[
  (6\text{ pairs}+4\text{ triples}+1\text{ grand coalition})\cdot4=44
  \]
  real payoff coordinates.  The singleton sign matrix records none of them.
- **Packet data.**  Full support leaves a mass vector in the open
  three-simplex (`mu_i>0`, `sum mu_i=1`).  Its target is pinned to the four
  own-solo payoffs, but the inequalities `M mu >= 0` depend on the actual
  magnitudes.  The theorem supplies a real coordinate floor depending on a
  reward bound and the terminal gap; it does not select from finitely many
  masses.
- **Terminal exploitability.**  `terminalGap` is a positive real.  The field
  `HasTerminalExploitabilityGap reward terminalGap` quantifies over every
  behavioral profile and an unrestricted unilateral behavioral deviation;
  it is not a finite witness table.
- **Punishment data.**  The four punishment values are real values derived
  from behavioral minmax problems.  Punishment-normality is a predicate, not
  a finite label replacing these values or their implementing strategies.
- **Semantic/tail data.**  The fused residual contains terminal semantic
  carrier/minimum data, an infinite exact debt tail, its root sequence and
  value/debt limits, a real covector and positive margin satisfying a unit
  normalization, a natural cutoff, summable absorption, and suffix-survival
  data.  None is determined by the singleton sign orbit.
- **Returned-block and preemption data.**  The terminal gap enters real
  inequalities involving nonsingleton rewards and punishment continuations.
  The ambient returned-block obstruction is quantified over arbitrary real
  bounds/blocks rather than encoded by a finite graph.

## 4. Exact conclusion

No current theorem reduces unrestricted behavioral equivalence of four-player
quitting games, or even the checked no-uniform residual, to a finite
enumeration.  What is finite is a hierarchy of necessary qualitative screens:
the 22,815 ternary singleton-sign orbits (218 on the strict stratum), finite
support/principal-set labels, and related finite graphs.  The current
full-support theorem eliminates packet-support rank as a live invariant, and
the sign-barrier theorem proves that continuing to enumerate singleton signs
alone cannot close the residual.

Thus an exhaustive search over 22,815 or 218 cases would be exhaustive only
for the indicated singleton sign skeleton.  It would leave the exact reward
magnitudes, all 44 nonsingleton coordinates, packet mass, terminal gap,
punishments, and unrestricted behavioral/semantic chronology untouched.

## 5. The theorem-distinguished residual count

The preceding orbit counts are not the answer to the narrower question
"how many cases survive the current theorems?"  For that question, the
checked LCP gate and its strategic consumers give the following exact ledger.

| gate regime | checked counterexample-facing status |
|---|---|
| `AllPlayersAbnormal` | eliminated by `exists_uniformEquilibriumPayoff_of_allPlayersAbnormal` |
| `HomogeneousMatrixBranch` | eliminated by `exists_uniformEquilibriumPayoff_of_homogeneousMatrixBranch` |
| `OrdinaryNonQMatrixBranch` | eliminated by `exists_uniformEquilibriumPayoff_of_ordinaryNonQMatrixBranch` |
| `ProjectiveQBarMatrixBranch` | eliminated by `exists_uniformEquilibriumPayoff_of_projectiveQBar_snell` |
| `ResidualHardClass` | survives, strengthened below |

Thus the five alternatives of `faithful_q_nonQ_lcp_matrix_gate` leave exactly
**one checked LCP residual regime**, not five and not 22,815.  In `Fin 4`,
`nonempty_finFourQuantitativeFullSupportHardResidual_of_no_uniformPayoff`
intersects that regime with a terminal exploitability witness, full recursive
normal core, all-player punishment normality, and a quantitatively full-support
singleton packet.  `exists_fourPlayerCounterexample_fusedResidual` further
intersects it with the positive semantic minimum, collision/preemption/lasso,
ambient returned-block, and strict-covector-tail necessary conditions.

These are intersections, not additional disjunctive skeletons.  Their selected
players, coalitions, packet, lasso, and tail witnesses are existential and need
not be unique.  Taking their possible finite labels as a Cartesian product
would therefore not produce a theorem-defined partition or a meaningful
candidate count.

There is one useful but currently ordinary-mathematical refinement in the
owned singleton-dispatch notebook.  Its reviewed Section 37 observes that an
all-punishment-normal nonprojective principal witness in the `Fin 4` residual
can have cardinality only two or three: a singleton zero-diagonal principal is
projective Q, while the full principal is projective Q by the checked
counterexample restriction.  At this coarse level the single checked residual
has **two reviewed principal-cardinality subcases**.  This is not yet a checked
Lean declaration and neither subcase eliminates its continuous principal
matrix magnitudes, right-hand-side certificates, or any nonsingleton/semantic
data.  It should not be advertised as a two-case reduction of exact games.

Accordingly the defensible counts are:

1. **one** maintained, checked counterexample-facing residual package;
2. **two** reviewed but unformalized coarse principal-cardinality arms inside
   it (`card = 2` or `card = 3`); and
3. **no well-defined finite count** of complete residual game/certificate
   candidates under the current declarations.

## 6. The old `(a←b)(c,d,e)` shorthand and the seventeen geometries

The old two-page classification uses `(a←b)(c,d,e)` (up to reversal of the
arrow convention) for the one-tail-edge/three-cycle lasso.  In the maintained
notation this is `OneStepToThreeCycle`, or shape `(tail,cycle)=(1,3)`:

\[
q\longrightarrow a\longrightarrow b\longrightarrow d\longrightarrow a.
\]

Its collision marker can be `a`, `b`, or `d`, giving three marked geometries.
The complete maintained classification is the inductive type
`Math.FiniteSerialRelation.MarkedRootedLasso` in
`MathUE/FiniteSerialRelation.lean`:

| maintained shape | marked collider positions | count |
|---|---|---:|
| rooted 2-cycle `(0,2)` | next, outside | 2 |
| rooted 3-cycle `(0,3)` | first, second, outside | 3 |
| rooted 4-cycle `(0,4)` | first, second, third | 3 |
| one step to 2-cycle `(1,2)` | entry, other, outside | 3 |
| one step to 3-cycle `(1,3)` | entry, second, third | 3 |
| two steps to 2-cycle `(2,2)` | first, entry, other | 3 |

Thus the exact marked proof-dispatch count is

\[
2+3+3+3+3+3=17.
\]

`exists_collisionAnchoredPreemptionGeometry_of_card_eq_four` produces one of
these constructors from a terminal exploitability witness.  The shorthand is
therefore a member of this seventeen-way dispatch, not one of the five LCP
regimes in Section 5.

## 7. Re-audit of the seventeen after the current reductions

The current advances add strong *orthogonal* restrictions but do not identify
or eliminate a constructor of `MarkedRootedLasso`.

- Quantitative full packet support removes every proper packet-support branch.
  It does not place the packet's selected reciprocal-synergy pair on the
  independently selected lasso.  Indeed
  `exists_normal_packetPair_not_mutuallyPreempting` explicitly records this
  limitation.
- Full recursive normal core removes normal-core support as a branch label.
  It does not change the strict-margin preemption edges or the relative
  position of the collision marker.
- All-player punishment normality similarly removes the normal/abnormal player
  split, but gives no equality between owner, collider, tail, or cycle roles.
- The projective-Q-bar consumer removes the Q-bar branch and leaves
  `ResidualHardClass`.  Its nonprojective principal witness is existential and
  is not linked to the selected lasso or collider.
- `exists_fourPlayerCounterexample_fusedResidual` places the packet, immediate
  collision, marked lasso, full core, punishment-normal hard class,
  returned-block gap, positive semantic minimum, and strict-covector tail in
  one same-table package.  Its proof obtains these witnesses independently;
  no field identifies the packet pair, principal witness, collision marker,
  or tail labels.
- The aligned collision-repair results apply uniformly when the collider is
  the first vertex after the root, but they give a residual
  owner-optimality/spectator-no-join test rather than eliminating those six
  aligned constructors.  The universal realization theorem proves that every
  one of the seventeen marked geometries is possible at payoff-table level;
  its examples are not counterexamples, so this is a boundary test rather than
  compatibility with the full semantic residual.

This absence of a reduction is also visible syntactically: outside the finite
relation definition, the only maintained uses of `MarkedRootedLasso` are its
producer in `Collision/PreemptionGeometry.lean` and its inclusion as a field
of `FourPlayerCounterexampleFusion.lean`.  No checked theorem case-analyzes its
seventeen constructors into fewer counterexample-facing cases.

Therefore the exact **current proof-dispatch count is still 17**.  The newer
theorems collapse auxiliary coordinates of a would-be case table to one value
(`support=univ`, `normalCore=univ`, every player punishment-normal, non-Q-bar
hard side), so crossing those statuses with the marked geometry gives
`17 x 1 = 17`, not a larger product and not a smaller geometry count.

This is not a partition of full reward tables.  A single table may have many
collision certificates, surplus preemption edges, and many selectable simple
lassos, and hence may realize several of the seventeen constructors.  The
number 17 counts canonical witness forms that a proof may dispatch after
choosing one collision-anchored lasso.  No checked theorem currently selects a
unique form or asserts disjointness.

Every one of the seventeen still needs continuous certificates: actual reward
magnitudes and terminal gap, the 44 nonsingleton payoff coordinates, a
full-support packet mass, punishment values/strategies, a non-Q-bar principal
certificate, collision-repair endpoint and spectator inequalities, and the
semantic carrier/tail/covector data.  Consequently there are exactly 17 finite
marked proof cases, but no finite count of complete game or semantic
certificate candidates.

## 8. New internal alignment: every two-cycle lasso supplies the hard pair

Status: independently reviewed and proved in Lean at the exact scope below.

The sharper principal dispatch in
`FullSupportHardPrincipalDispatch.lean` changes the alignment question.  The
eight marked constructors whose lasso cycle has length two do not merely
coexist with some abstract hard principal: their two cycle vertices themselves
form a nonprojective principal.

### Lemma 8.1 (mutually negative pair is nonprojective)

Let `M` be zero diagonal, let `u != v`, and suppose

\[
M(u,v)<0,\qquad M(v,u)<0.
\]

Then the principal matrix on `{u,v}` is not projective Q.

Proof.  Use the projective right-hand side `q=(-1,-1)`.  Write `c>=0` for
cemetery mass and `x,y>=0` for the singleton masses of `u,v`.  Residual
nonnegativity says

\[
-c+M(u,v)y\ge0,\qquad -c+M(v,u)x\ge0.
\]

Every term on each left side is nonpositive.  The first inequality forces
`c=y=0`, and the second forces `c=x=0`, contradicting `c+x+y=1`.  No
complementarity clause is needed.  Hence this `q` has no projective solution.
\(\square\)

### Proposition 8.2 (cycle-pair alignment)

Let `residual` be a
`FinFourQuantitativeFullSupportHardResidual reward bound`, and let a marked
rooted lasso be selected for the strict relation

```text
QuittingSoloPreempts reward residual.witness.terminalGap.
```

If its cycle has length two, let `P` be its two cycle vertices.  Then

```text
Nonempty (FinFourHardCardTwoCrossing residual P).
```

Proof.  In each of the eight relevant `MarkedRootedLasso` constructors the
stored lasso contains both edges between the two cycle vertices.  The checked
preemption/matrix dictionary converts them to

\[
M(u,v)\le-\gamma<0,\qquad M(v,u)\le-\gamma<0,
\]

where `gamma=residual.witness.terminalGap>0`.  Lemma 8.1 makes the literal
two-coordinate principal nonprojective.  Its cardinality is two, so apply the
checked
`FinFourQuantitativeFullSupportHardResidual.cardTwoCrossing` to this same
set `P`.  The resulting outside helpers are therefore aligned to the actual
lasso cycle pair, not merely selected elsewhere on the same table.
\(\square\)

The eight constructors covered are

```text
rootedTwo_next, rootedTwo_outside,
oneToTwo_entry, oneToTwo_other, oneToTwo_outside,
twoToTwo_first, twoToTwo_entry, twoToTwo_other.
```

This gives the following honest finite reduction of the *alignment* problem:

\[
17
\quad\leadsto\quad
\underbrace{8}_{\text{same cycle pair enters card-two crossing}}
\;\cup\;
\underbrace{9}_{\text{cycle length three or four, principal still unaligned}}.
\]

It does not eliminate the eight semantic geometries.  It merges their LCP
treatment into one named checked output.  If one counts the newly available
coarse proof arms, this is one aligned two-cycle arm plus nine still-marked
long-cycle arms, i.e. ten arms; if one counts marked semantic witnesses, the
count remains seventeen.

There is one completely aligned constructor.  In `rootedTwo_next`, the lasso
root is the collision owner and the next vertex is the collider.  Thus the
hard pair is literally `{collision.owner, collision.collider}`.  The card-two
crossing theorem supplies, for the two harmed receiver rows, positive helpers
among the other two players.  Up to relabeling those two outsiders, their
incidence has only two coarse forms: the helpers coincide or they are distinct.
The helper choices are existential and possibly nonunique, so even these two
forms are proof branches, not a disjoint partition of tables.

### Long-cycle remainder

- For a selected three-cycle, if its literal three-vertex principal is
  nonprojective, the checked card-three theorem applies to that same cycle and
  yields `externalHelper` or `cyclicBoundary`.  If the cycle principal is
  projective, the hard principal remains elsewhere; strict preemption alone
  does not choose between these cases.
- For a selected four-cycle, the cycle principal is the full matrix.  On the
  full-core residual that full principal is standard Q and hence projective.
  Therefore its nonprojective witness is necessarily a proper two- or
  three-coordinate subset of the cycle, with no checked relation to the
  collision marker.

The strict-toggle semantic arms in
`StrictToggleLargeBasePaidChain.lean` cannot be cross-identified here: their
selected toggle cycle is produced separately from the preemption lasso.  The
same-table theorem contains both, but no equality of their labels, base, or
free set.

## 9. Exact boundary calibrations for the missing alignment

Two existing matrices isolate what the new proposition does and does not buy.

1. The paired-singleton matrix
   
   \[
   \begin{pmatrix}
   0&3&-1&-1\\
   3&0&-1&-1\\
   -1&-1&0&3\\
   -1&-1&3&0
   \end{pmatrix}
   \]
   
   has full normal core, is standard Q with no homogeneous solution, and
   fails projective Q-bar on a two-coordinate principal.  Uniform weights
   have strictly positive row averages.  After adding a common singleton
   baseline `1`, target `1` gives a literal full-support normalized packet and
   every player is punishment-normal by
   `quittingPunishmentValue_le_max_solo`.  Choosing owner `0`, the strict
   two-cycle `0<->2` realizes `rootedTwo_next`; choosing a collision marker
   `1` while retaining that lasso realizes `rootedTwo_outside`.  Suitable pair
   rewards make both collision gains exactly one.  Thus the same table-level
   finite system can realize both marked rooted-two constructors while the
   hard pair is exactly the cycle pair.

2. `FourPointCrossedRowsNoCyclicSign.fullCoreMatrix` has a full-support packet,
   full normal core, standard Q, and no homogeneous solution.  Its strict
   graph contains
   
   \[
   3\to2\to1\to0\to2,
   \]
   
   a one-step/three-cycle lasso.  By setting the three pair-payoff coordinates
   for collision owner `3` one unit above the corresponding singleton rows,
   the same finite table realizes all three marker positions `2,1,0`.  The
   remaining missing algebraic field is precisely projective-Q-bar failure;
   the checked barrier does not supply it.

Neither calibration has the positive-minimum semantic tail of a hypothetical
counterexample.  Supplying that field would amount to entering the genuine
conjecture-facing source.  The calibrations therefore show sharpness of the
finite algebraic alignment only; they do not prove consistency of any marked
geometry with the complete counterexample residual.

## 10. One-step/three-cycle packet alignment

Status: ordinary proof, self-audited, not yet independently reviewed.

The old `(a←b)(c,d,e)` row admits a stronger exact reduction than the generic
seventeen-case inventory.  Write its four distinct labels as

\[
q\to a\to b\to d\to a,
\]

and put `M=normalizedSoloMatrix reward`.  Let `mu` be the quantitatively
full-support packet mass.  Then

\[
\mu_j>0\quad(j=q,a,b,d),
\qquad
\sum_j\mu_j M(i,j)\ge0\quad(i=q,a,b,d).
\tag{10.1}
\]

The lasso edges give

\[
M(a,q),M(b,a),M(d,b),M(a,d)\le-\gamma<0.
\tag{10.2}
\]

### Lemma 10.1 (row completion)

If one row of a zero-diagonal four-coordinate matrix has known negative
entries in two distinct non-diagonal columns and has a positive full-support
weighted average, or merely a nonnegative average with either negative term
present, then its only remaining off-diagonal entry is strictly positive.

Indeed, if that last entry were nonpositive, every weighted term would be
nonpositive and one of the two negative terms would have positive weight, so
the average would be negative.

Applying the lemma to row `a` in (10.2) gives the forced internal reverse edge

\[
M(a,b)>0.                                             \tag{10.3}
\]

Applying the same argument to rows `b` and `d`, each of which has one known
negative cycle predecessor, gives

\[
M(b,q)>0\ \lor\ M(b,d)>0,
\qquad
M(d,q)>0\ \lor\ M(d,a)>0.                            \tag{10.4}
\]

### Proposition 10.2 (exact source-aligned trichotomy)

For every one-step/three-cycle lasso in the full-support residual, exactly the
following exhaustive alternatives are sufficient as a proof dispatch:

1. **owner-external helper:** `M(b,q)>0` or `M(d,q)>0`.  On the literal cycle
   principal `C={a,b,d}`, the collision owner/tail root `q` is the unique
   outsider and positively compensates a row harmed by its cycle predecessor.
   Thus the fields of `FinFourHardCardThreeExternalHelper reward C` are
   present on the actual lasso labels (whether or not `C` is the selected hard
   principal).
2. **projective internal cycle:** both outside-helper inequalities fail, all
   three reverse cycle entries are positive by (10.3)--(10.4), and the cycle
   determinant is nonnegative.  The strict three-by-three classification says
   that determinant zero is the homogeneous projective branch, while positive
   determinant is the standard-Q/no-homogeneous projective branch.
3. **hard internal cycle:** both outside-helper inequalities fail and the
   cycle determinant is negative.  The strict orientation and the checked
   three-by-three classification then give neither a homogeneous solution nor
   standard Q.  Hence `C` itself is a nonprojective three-coordinate principal,
   aligned to the lasso cycle.  In particular the maintained
   `FinFourHardCardThreeCyclicBoundary` output can be strengthened from
   determinant `<=0` to determinant `<0` in this source-aligned chamber.

Proof.  If either first disjunct in (10.4) holds, use the corresponding cycle
edge as `harmed_by_owner` and `q` as the unique outsider/helper.  Otherwise
(10.4) supplies `M(b,d)>0` and `M(d,a)>0`; together with (10.3) and the three
negative cycle entries, this is one of the two strict cyclic orientations
after relabeling `C` by `Fin 3`.  Split the real cycle determinant into
negative, zero, or positive.  The exact results
`directedCycleMatrix_hasHomogeneous_iff` and
`standardQ_and_noHomogeneous_iff_cycleDeterminant_pos_of_forward/reverse`
give the last two conclusions. \(\square\)

This is a genuine alignment of the old three-marker row: the outside helper in
arm 1 is the collision owner `q`, while the principal in arm 3 is the literal
three-cycle.  What it still does not use is the collider marker.  The three
possible markers `a,b,d` therefore remain distinct for collision semantics,
even though their packet/LCP trichotomy is common.

The semantic strict-toggle alternatives from Fermat's proof-mining note remain
separate: no checked theorem identifies this preemption cycle `C` with the
large-, singleton-, or empty-base toggle cycle selected by
`StrictToggleLargeBasePaidChain.lean`.

## 11. Semantic consequence in the fully aligned `rootedTwo_next` case

Status: independently reviewed ordinary proof; see
`feedback/CODEX_EULER__FIN4_SEARCH_SPACE_INVENTORY__BY_CODEX_RAMSEY__SECTION_11.md`.
Unlike Proposition 8.2, this statement uses an actual nonsingleton terminal
row.  It still ends at a quantitative toggle alternative, not at an
all-behavior compiler.

Let

```text
witness : QuittingTerminalExploitabilityWitness reward
certificate : QuittingImmediateSingletonCollision
  reward witness.terminalGap
```

and abbreviate

```text
o = certificate.owner,
c = certificate.collider,
gamma = witness.terminalGap,
P = {o,c}.
```

Assume that the marked geometry is `rootedTwo_next`.  Besides identifying its
marker with `c`, this supplies both strict preemption edges

```text
QuittingSoloPreempts reward gamma o c,
QuittingSoloPreempts reward gamma c o.              (11.1)
```

### Theorem 11.1 (aligned pair exit-or-outside-join)

At least one of the following holds:

1. the collision owner is quantitatively underpaid at the pair relative to
   its own solo row,

   ```text
   reward(P)(o) + 2*gamma <= reward({o})(o);          (11.2)
   ```

2. an actual outsider joins the owner--collider pair by the full terminal
   gap,

   ```text
   exists s, s notin P and
     reward(P)(s) + gamma <= reward(insert s P)(s).  (11.3)
   ```

#### Proof

Apply the checked terminal-witness toggle theorem

```text
witness.exists_leave_or_join_gain P.
```

In its leave arm, choose the selected member `m in P`.  Since `P={o,c}`, the
member is `o` or `c`.

It cannot be `c`.  Such a leave would say

```text
reward(P)(c) + gamma <= reward({o})(c),               (11.4)
```

whereas the collision certificate says

```text
reward({o})(c) + gamma <= reward(P)(c).               (11.5)
```

Adding (11.4)--(11.5) gives `2*gamma<=0`, contrary to
`witness.terminalGap_pos`.

Therefore `m=o`, and its leave inequality is

```text
reward(P)(o) + gamma <= reward({c})(o).               (11.6)
```

The reverse edge `c -> o` in (11.1) is exactly

```text
reward({c})(o) + gamma <= reward({o})(o).             (11.7)
```

Combining (11.6)--(11.7) proves (11.2).  In the join arm of
`exists_leave_or_join_gain`, the selected player is outside `P` and its
inequality is literally (11.3).  This proves the alternative.  QED.

### Corollary 11.2 (intersection with the aligned hard pair)

Under the hypotheses of Proposition 8.2, there are helpers `h_o,h_c` outside
`P` such that

```text
reward({o})(o) < reward({h_o})(o),
reward({c})(c) < reward({h_c})(c),                    (11.8)
```

and simultaneously either (11.2) or (11.3) holds.  Indeed, Proposition 8.2
identifies `P` with the nonprojective principal and the checked
`cardTwoCrossing` output supplies (11.8), after possibly swapping its `first`
and `second` labels.

If the joiner `s` in (11.3) is different from both displayed helpers, then
the two helpers coincide: `Fin 4 \ P` has exactly two elements, and all three
labels lie in that complement.  This is only a finite incidence observation;
helper choices can be nonunique.

### Exact scope

Theorem 11.1 is more than singleton-matrix alignment: (11.3) contains an
actual triple reward, while (11.2) retains the pair reward and a quantitative
two-gap comparison.  It is nevertheless a repackaging of one checked
terminal toggle after excluding the collider-leave arm.  Neither branch is a
Bellman root, chronological connector, sure-exit certificate, or
uniform-equilibrium compiler.  In particular:

- (11.2) does not say that the owner can cause its solo row from the pair;
- (11.3) is a profitable immediate join and therefore an obstruction to the
  sure pair, not a stable repair row;
- (11.8) concerns singleton payoff effects and does not determine either
  nonsingleton comparison; and
- no current checked declaration consumes this alternative into the missing
  semantic endpoint.

Thus this closes the first same-label semantic calculation for
`rootedTwo_next`, but it does not yet meet the chamber-closure threshold by
itself.

## 12. Exact length-three lasso/principal incidence

Status: ordinary proof, independently reviewed.  This is the complete finite
alignment pass for all six marked constructors whose
periodic cycle has length three.  It produces same-label card-three/card-two
finite data, but no semantic compiler or invariant decrease.

Let `residual` be a
`FinFourQuantitativeFullSupportHardResidual reward bound`, put

```text
M = normalizedSoloMatrix reward,
gamma = residual.witness.terminalGap,
```

and let a selected marked preemption lasso have literal directed three-cycle

```text
a -> b -> d -> a.                                    (12.1)
```

Write `C={a,b,d}` and let `x` be the unique player outside `C`.  The three
cycle edges give

```text
M(b,a)<=-gamma<0,
M(d,b)<=-gamma<0,
M(a,d)<=-gamma<0.                                    (12.2)
```

Choose any hard principal supplied by the reviewed proper-principal
dispatch:

```text
K.card=2 or K.card=3,
not IsProjectiveQMatrix(principalMatrix M K).         (12.3)
```

### Lemma 12.1 (row completion on the literal cycle)

If no cycle row is positively helped by the unique outsider,

```text
M(a,x)<=0, M(b,x)<=0, M(d,x)<=0,                     (12.4)
```

then all three reverse internal entries are strictly positive:

```text
M(a,b)>0, M(b,d)>0, M(d,a)>0.                        (12.5)
```

For example, packet feasibility and full pinning give

```text
0 <= sum_j residual.packet.mass(j)*M(a,j).
```

The diagonal term is zero, the `d` term is strictly negative by (12.2) and
has positive mass, and the `x` term is nonpositive by (12.4).  If `M(a,b)`
were nonpositive, the sum would be strictly negative.  Thus `M(a,b)>0`.
The other two rows are identical after rotation.

### Theorem 12.2 (three-cycle incidence trichotomy)

Exactly one of the following three proof arms may be selected exhaustively.

1. **Literal-cycle outside helper.**  Some `i in C` has `M(i,x)>0`.  Taking
   the predecessor of `i` in (12.1) as the negative owner produces the exact
   same-label fields

   ```text
   Nonempty (FinFourHardCardThreeExternalHelper reward C),
   ```

   with its `outsider` field equal to `x`.

2. **Literal hard cycle.**  There is no outside helper and the determinant of
   the labelled principal on `C` is negative.  Then

   ```text
   not IsProjectiveQMatrix(principalMatrix M C),
   ```

   so `C` itself is a card-three hard principal.  Moreover the same literal
   labels satisfy

   ```text
   Nonempty (FinFourHardCardThreeCyclicBoundary reward C)
   ```

   with the stronger strict inequality `cycleDeterminant<0`.

3. **Outsider-containing hard principal.**  There is no outside helper and
   the determinant of the labelled principal on `C` is nonnegative.  Then
   `C` is projective Q, and every `K` satisfying (12.3) contains `x`.  More
   precisely,

   ```text
   K.card=2 -> K={x,y} for exactly one y in C,
   K.card=3 -> K contains x and exactly two labels of C. (12.6)
   ```

#### Proof

First split on whether `M(i,x)>0` for some `i in C`.  In that case the cycle
predecessor column in row `i` is strictly negative by (12.2), while the
unique complement is `{x}`.  These are exactly the fields of
`FinFourHardCardThreeExternalHelper reward C`, proving arm 1.

Otherwise (12.4) holds and Lemma 12.1 gives (12.5).  After relabelling `C` by
`Fin 3`, (12.2) and (12.5) form one of the two strict directed-cycle
orientations in `ThreeByThreeZeroDiagonalQ`.

If its determinant is negative, it is nonzero, so
`directedCycleMatrix_hasHomogeneous_iff` excludes a homogeneous solution.
The equivalence

```text
standardQ and noHomogeneous <-> 0<cycleDeterminant
```

excludes standard Q.  The checked projective split

```text
projectiveQ <-> standardQ or homogeneous
```

therefore excludes projective Q.  The literal principal `C` is hard and its
strict orientation plus negative determinant gives arm 2.

If instead the determinant is nonnegative, split once more into zero or
positive.  At zero, the homogeneous equivalence makes `C` projective Q.  At
positive determinant, the standard-Q equivalence makes `C` projective Q.

It remains to prove the incidence claim for an arbitrary hard `K` in (12.3).
If `K.card=3` and `x notin K`, then `K=C`, contradicting projectivity of `C`.
Hence `x in K`, and the remaining two elements lie in `C`.

Suppose `K.card=2` and `x notin K`.  Then `K` is a pair inside `C`.  For every
pair inside the strict orientation (12.2), (12.5), one reciprocal entry is
strictly negative and the other is strictly positive.  But a nonprojective
zero-diagonal two-coordinate principal must have both reciprocal entries
strictly negative: exclusion of projective Q excludes the homogeneous branch,
and the two-column negative-entry lemma forces the sole off-diagonal entry in
each column to be negative.  This contradiction proves `x in K`.  Cardinality
then gives the first line of (12.6).  QED.

### Corollary 12.3 (owner/collider role alignment)

The six constructors reduce without enumerating arbitrary annotations:

- In `oneToThree_entry`, `oneToThree_second`, and `oneToThree_third`, the
  lasso root/collision owner is exactly `x`.  Thus arm 1 uses the collision
  owner as the literal external helper; arm 2 makes the cycle containing the
  collider hard; and every hard principal in arm 3 contains the collision
  owner.
- In `rootedThree_outside`, the collider is exactly `x`.  Thus arm 1 uses the
  collider as the literal external helper, while every hard principal in arm
  3 contains the collider.  Arm 2 contains the collision owner but not the
  collider.
- In `rootedThree_first` and `rootedThree_second`, both collision owner and
  collider lie in `C`.  Arm 2 therefore makes one principal containing both
  roles hard.  In arms 1 and 3 the unique outsider is the remaining fourth
  label; no stronger collider incidence follows.

In arm 3, applying the already checked consumer to `K` gives
`FinFourHardCardTwoCrossing residual K` when `K.card=2`, or the existing
card-three external-helper/cyclic-boundary dispatch when `K.card=3`.  The new
content is that this selected principal necessarily contains the literal
cycle outsider—and hence the owner or collider in the two constructors just
identified.

### Finite-pass conclusion and stopping point

This is the smallest theorem-driven incidence dispatch found for length-three
cycles:

```text
literal external helper
or literal hard cyclic principal
or every hard principal contains the literal outsider. (12.7)
```

It merges the three collider positions within each lasso shape only where the
constructor equations genuinely identify a role.  It does not enumerate
free annotations or treat these arms as disjoint classes of reward tables.

No current checked consumer turns any arm of (12.7) into an unrestricted
behavioral strategy, contradiction, or well-founded semantic decrease.
`FinFourHardCardThreeExternalHelper`,
`FinFourHardCardThreeCyclicBoundary`, and `FinFourHardCardTwoCrossing` are
finite residual structures.  The owner/collider incidence in Corollary 12.3
does not add the pair/triple payoff inequalities required by collision repair
or stationary compilers.  Accordingly the finite alignment pass stops here;
any further case subdivision without new semantic data would only enumerate
annotations.

## 13. Rooted-two semantic consumer and exact sharpness completion

Status: source-audited checked downstream theorem plus an ordinary exact
rational boundary calculation.  This section deliberately does not claim a
new positive consumer.

### 13.1 The checked consumer already present in the repository

The bounded source audit after Section 11 found the stronger declaration

```text
FinFourQuantitativeFullSupportHardResidual.
  rootedTwoNext_sharedHelper_or_ownerLeaveCollisionChain_or_hardHelperJoin
```

in

```text
UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/
  TwoCycleLassoArmConsumers.lean.
```

It imports the reviewed terminal-gap dispatch and the exact finite
collision-repair screen.  In the owner-leave arm, full packet support gives
positive mass to the collider.  Since the owner strictly prefers the
collider singleton to the owner--collider pair, failure of every exact
collision repair forces a player `s` distinct from both selected labels with

```text
r_{c}(s) < r_{c,s}(s).                              (13.1)
```

Applying the terminal witness at `{c,s}` then gives

```text
r_{c,s}(c) + gamma <= r_s(c),                       (13.2a)
```

or a gap-sized join by an outsider of `{c,s}`.  The leaving member cannot be
`s`, because that would contradict (13.1).  The checked output retains the
two-gap owner deficit from Section 11 and records that `s` is one of the two
hard-pair helpers when those helpers are distinct.

This is a genuine use of nonsingleton rewards and unrestricted collision-
repair semantics.  Its exact residual is nevertheless

```text
shared helper
or owner-leave collision chain
or gap-sized join by a hard helper.                 (13.2b)
```

The source explicitly does not turn these data into a chronology or a
uniform-equilibrium compiler.

### Proposition 13.2 (the extracted collision chain is not compiler data)

There is a complete rational reward table on `Fin 4` with all of the
following properties simultaneously.

1. Its normalized singleton matrix has full normal core, is standard `Q`,
   has no homogeneous simplex solution, and is not projective `Q-bar`.
2. It has a normalized singleton source packet of full support, with all
   punishment floors below the packet target and with the quantitative mass
   floor required at bound `20` and margin `1`.
3. Labels `o=0,c=2` carry the exact immediate collision and two-cycle
   preemption data at margin one.
4. The owner-leave arm, the spectator collision join, and the second
   gap-sized collider leave in (13.1)--(13.2a) all hold numerically.
5. Nevertheless the grand coalition is a sure-exit set and therefore gives
   an exact terminal Nash equilibrium against every behavioral deviation.

Consequently the numerical fields of the owner-leave collision-chain output,
even on top of the complete static full-support hard-residual data, do not by
themselves imply a contradiction or feed an all-behavior compiler other than
one supplied by additional rows.  The missing hypothesis in this completion
is precisely the global terminal exploitability witness.

#### Table

Use the following payoff vectors, with coalition strings denoting their
members:

```text
0:(1,3,-1,4)       1:(4,1,3,-1)       01:(1,1,20,2)
2:(0,2,1,2)        02:(-1,4,1,5)      12:(10,3,1,0)
012:(1,4,1,3)      3:(4,-2,0,1)       03:(1,0,-2,1)
13:(7,1,2,1)       013:(1,1,0,1)      23:(3,-1,1,1)
023:(1,1,1,1)      123:(6,-2,5,1)     0123:(10,10,10,10).
```                                                        (13.3)

This changes only four entries of the reviewed table in Proposition 25.2 of
`notes/CODEX_EULER__FOUR_PLAYER_SINGLETON_PACKET_DISPATCH.md`; no singleton
entry changes.  Hence its normalized singleton matrix is still

```text
M = [ 0  3 -1  3
      2  0  1 -3
     -2  2  0 -1
      3 -2  1  0 ].                                  (13.4)
```

The determinant/degree calculation reviewed for Proposition 25.1 therefore
still proves the full normal core, standard-`Q`, nonhomogeneous, and
nonprojective-`Q-bar` assertions.

#### Full-support packet and floors

Take

```text
mu=(1,2,1,1)/5,             v=(1,1,1,1).
```

Every own singleton payoff is one, so full support pins every target
coordinate.  Direct multiplication gives

```text
M mu = (8,0,1,0)/5,
```

and therefore the singleton mixture dominates `v`.  To bound the punishment
values, let opponents `2,3,0,1` respectively quit surely against players
`0,1,2,3`.  The Continue/Join endpoint pairs are

```text
(0,-1), (-2,1), (-1,1), (-1,1),
```

so the unrestricted punishment cap is at most one in every coordinate.
Finally

```text
min_i mu_i = 1/5 >= 1/121
  = 1 / (1 + (2*20/1)*3),
```

which is the quantitative packet floor at the displayed bound and margin.

#### Aligned collision chain

At `o=0,c=2`, the singleton and pair entries in (13.3) give

```text
r_o(o)=1,       r_c(o)=-1,      r_c(c)=1,
r_c({o,c})=1,   r_o(c)=0,       r_o({o,c})=-1.
```

Thus the immediate collision certificate and both preemption directions hold
at margin one:

```text
r_c(o)+1 <= r_c({o,c}),
r_c(o)+1 <= r_c(c),
r_o(c)+1 <= r_o(o).
```

The terminal owner leave is exact,

```text
r_o({o,c})+1 = r_o(c),
```

and combining it with reverse preemption gives the two-gap deficit
`r_o({o,c})+2=r_o(o)`.  Player `s=1`, which is a shared positive singleton
helper for rows `o` and `c`, satisfies

```text
r_colliderSingleton(s)=r_2(1)=2 < 3=r_{1,2}(1).
```

At that enlarged pair the collider has the required second gap toggle:

```text
r_{1,2}(2)+1 = 2 <= 3=r_1(2).
```

The other two possible gap joins at the original pair have deliberately been
closed:

```text
r_{0,2}(1)=r_{0,1,2}(1)=4,
r_{0,2}(3)=5>1=r_{0,2,3}(3).
```

So this completion realizes the owner-leave collision-chain arm rather than
using the original pair-join escape.

#### Exact all-behavior boundary

The grand-coalition payoff is ten in every coordinate.  Removing players
`0,1,2,3` yields the payoff coordinates

```text
r_{1,2,3}(0)=6,
r_{0,2,3}(1)=1,
r_{0,1,3}(2)=0,
r_{0,1,2}(3)=3,
```

all at most ten.  There is no outsider to the grand coalition.  Hence it is
an `IsQuittingSureExitSet`, and

```text
isUniformEquilibriumPayoff_setReward_of_isQuittingSureExitSet
```

gives an exact uniform-equilibrium payoff against unrestricted behavioral
deviations.

### Consequence and stopping point

The checked theorem of Section 13.1 is the maximal direct implication found
from the owner-underpayment arm.  Proposition 13.2 rules out discarding its
source provenance and treating its finite reward inequalities as a semantic
certificate.  Reapplying `witness.exists_leave_or_join_gain` to successive
coalitions only reconstructs a directed walk in the coalition cube; without
a common payoff potential, source-matched Bellman object, or named cycle
compiler this is the already-known static toggle route, not an invariant
decrease.

Accordingly the finite pass stops here.  A genuine next theorem must use some
global consequence of the same terminal witness that the sure-exit completion
(13.3) violates, and must preserve it through the collision chain.  Neither
the hard helper labels nor the local nonsingleton gaps currently provide that
preservation.

## 14. Gap-preserving punished-singleton promotion

Status: complete ordinary proof, source-audited, awaiting independent
falsification.  Unlike Proposition 13.2, the statement retains the terminal
exploitability witness and uses an actual accuracy-dependent punishment
continuation.  Its output is still a local paid toggle, not a completed
stationary or chronological compiler.

### 14.1 Exact-block lemma

Let `I` be finite, let `reward` be a quitting reward table, and let `witness`
be a `QuittingTerminalExploitabilityWitness reward` with terminal gap
`gamma>0`.  Fix distinct labels `a,b`.  Assume

```text
P_b <= r_b(b),                                      (14.1)
r_{a,b}(a) <= r_b(a),                               (14.2)
```

where `P_b=quittingPunishmentValue reward b`.  Then there is a label
`j notin {a,b}` such that

```text
r_{b,j}(j) >= r_b(j)+gamma.                         (14.3)
```

Equivalently, the following all-behavior alternative holds before imposing
the terminal witness:

```text
some outsider has join gain at least gamma,
or an accuracy-dependent one-stage punished singleton-b root is a terminal
epsilon-Nash profile for some epsilon<gamma.        (14.4)
```

The second arm is an actual behavioral profile, not a finite-controller
test.

#### Proof

For `j notin {a,b}`, write

```text
d_j=max(r_{b,j}(j)-r_b(j),0),
Delta=max({0} union {d_j : j notin {a,b}}).         (14.5)
```

Suppose `Delta<gamma`.  Choose `eta>0` with

```text
max(Delta,eta)<gamma.                               (14.6)
```

By

```text
quittingPunishmentValue_eq_stationaryPunishmentValue
exists_quittingStationaryPunishmentRoot_lt_add
```

there is a stationary row `y` whose unrestricted stationary unilateral cap
for `b` is strictly below `P_b+eta`.  Form the literal one-stage punished
profile whose date-zero root is the pure singleton `{b}` and whose continuation
after unanimous Continue is the stationary row `y`.  This is the rate-zero
specialization of

```text
quittingOneStagePunishedProfile reward
  (quittingCollisionRepairRoot a b 0) y.
```

The prescribed date-zero row absorbs surely, so its payoff is exactly
`r_b`.  The unilateral caps are exhaustive and elementary.

- Player `a` can only choose between continuing into the prescribed
  singleton payoff `r_b(a)` and tying at date zero for `r_{a,b}(a)`.
  Assumption (14.2) makes its gain nonpositive.
- Any `j notin {a,b}` can only continue for `r_b(j)` or tie for
  `r_{b,j}(j)`.  Its full behavioral gain is therefore exactly `d_j`, at most
  `Delta`.
- Player `b` can Quit as prescribed or Continue at date zero and then replace
  its entire future behavioral strategy against `y_-b`.  The latter payoff is
  below `P_b+eta<=r_b(b)+eta` by (14.1).  Its gain is therefore below `eta`.

The statements for `a` and the other outsiders cover arbitrary behavioral
strategies because the prescribed blocker Quits surely at date zero: only the
deviator's date-zero action can affect the terminal coalition.  The statement
for `b` uses the unrestricted stationary unilateral cap, which already
optimizes over every later stopping law.  Hence the whole profile is a
terminal `max(Delta,eta)`-Nash profile.  By (14.6) this error is strictly below
`gamma`, contradicting

```text
witness.not_isεAsymptoticNash_of_lt_terminalGap.
```

Therefore `Delta>=gamma`; since `gamma>0` and the finite maximum is attained,
one outsider satisfies (14.3).  This also shows that if there is no outsider,
the hypotheses themselves contradict the terminal witness.  QED.

### 14.2 Application to the rooted-two owner-leave chain

Let

```text
chain : FinFourRootedTwoNextOwnerLeaveCollisionChain residual certificate
```

and abbreviate its collider by `c` and its selected spectator by `s`.  Full
packet support gives positive mass to `s`; packet pinning and the punishment
floor give

```text
P_s <= packet.target(s)=r_s(s).                    (14.7)
```

The chain's `second_gap_toggle` has two arms.

1. An outsider of `{c,s}` joins that pair with gain at least `gamma`; this is
   already a gap-sized pair-to-triple toggle.
2. The collider leaves the pair with

   ```text
   r_{c,s}(c)+gamma <= r_s(c).                      (14.8)
   ```

   Apply the exact-block lemma with `a=c,b=s`.  It produces
   `t notin {c,s}` with

   ```text
   r_{s,t}(t) >= r_s(t)+gamma.                      (14.9)
   ```

Thus every owner-leave collision chain has the exact same-table alternative

```text
gap-sized outsider join at {c,s},
or gap-sized collider leave {c,s}->{s} followed by a gap-sized outsider
join {s}->{s,t}.                                    (14.10)
```

The formerly merely strict relation
`r_c(s)<r_{c,s}(s)` is not used to manufacture the new constant; the full
`gamma` comes from the terminal witness and the source-matched punishment
floor at the receiving singleton.

### 14.3 Scope and next exact question

Equation (14.10) is a genuine nonsingleton, all-behavior reduction.  If the
paid singleton join were absent, the proof would construct a legal one-stage
punished profile below the fixed terminal gap.  It is therefore stronger than
reapplying the static leave-or-join toggle lemma.

It does **not** yet close the rooted-two chamber.  Iterating the paid
leave/join alternative can still form a nonbacktracking cycle of singleton and
pair rows, or can enter a pair-to-triple join.  No monotone payoff potential is
present, and the interval-core stationary compiler additionally requires its
blocker bands uniformly over every background.  The next concrete question is
whether the hard-helper/full-normal-core data force one such uniform band on
the cycle generated by (14.10), or whether an exact same-table regression can
satisfy all of those fields while violating every candidate band.

## 15. Maximal source audit: every punishment-normal singleton has a gap collision

Status: complete ordinary composition of checked declarations, independently
reviewed PASS in
[`CODEX_RAMSEY`, Section 15](../feedback/CODEX_EULER__FIN4_SEARCH_SPACE_INVENTORY__BY_CODEX_RAMSEY__SECTION_15.md).
This supersedes Theorem 14.1 as the source-facing statement.  Section 14
remains a self-contained direct proof of the needed special case.

### Theorem 15.1 (punishment-normal atomic collision)

Let `witness : QuittingTerminalExploitabilityWitness reward`, put
`gamma=witness.terminalGap`, and fix a player `b`.  If

```text
quittingPunishmentValue reward b <= r_b(b),         (15.1)
```

then there is `j!=b` with

```text
r_{b,j}(j) >= r_b(j)+gamma.                         (15.2)
```

Thus `(b,j)` is a terminal-gap collision row in the collider coordinate.  No
preselected collision owner, hard principal, or lasso incidence is needed.

#### Proof by the checked atomic-blocker barrier

Take the pure product root

```text
q=quittingPureSetRoot {b}=quittingInstantRoot b.
```

The owner `b` Quits surely.  Directly expanding the definitions at this root
gives

```text
quittingAtomicBlockerBalance reward q b
  =r_b(b)-quittingPunishmentValue reward b >=0,     (15.3)
```

and, for every `j!=b`,

```text
quittingForcedOwnerOutsiderCoordinateDefect reward q b j
  =max(0,r_{b,j}(j)-r_b(j)).                        (15.4)
```

The checked declaration

```text
QuittingTerminalExploitabilityWitness.
  terminalGap_le_atomicBlockerBarrier
```

in

```text
UniformEquilibrium/Quitting/Boundary/Repair/
  AtomicBlockerPaidGeometry.lean
```

therefore reduces to

```text
gamma <= quittingForcedOwnerOutsiderDefect reward q b.  (15.5)
```

Here the second barrier arm `max(0,-balance)` vanishes by (15.3).  The same
checked file proves that a positive lower bound on the finite outsider defect
is attained by one outsider's pure Boolean endpoint:

```text
exists_outsider_pureEndpoint_gain_ge_of_le_forcedOwnerOutsiderDefect.
```

At the pure singleton root, the Continue endpoint equals the prescribed
payoff `r_b(j)`.  Since `gamma>0`, the attaining action cannot be Continue;
it is Quit, whose payoff is `r_{b,j}(j)`.  This proves (15.2).  QED.

This proof is exactly the one-stage punished-block logic expanded in Section
14, but it uses the already checked unrestricted-deviation theorem rather than
reproving its cap estimate.

### Corollary 15.2 (four gap collisions in the maintained residual)

For a `FinFourQuantitativeFullSupportHardResidual`, packet support is `univ`.
For every `b`, positive mass pins

```text
packet.target(b)=r_b(b),
```

and `packet.punishment_le_target` gives (15.1).  Hence there is a map, after
finite choice,

```text
next : Fin 4 -> Fin 4
```

with `next(b)!=b` and

```text
r_{b,next(b)}(next(b)) >=
  r_b(next(b))+gamma.                               (15.6)
```

for every `b`.  The selected directed graph has a cycle of length two, three,
or four.  This last finite observation is only bookkeeping; the substantive
new source data are the four same-table nonsingleton inequalities (15.6).

### Corollary 15.3 (gap-preserving owner-leave chain)

Let `chain` be the owner-leave collision chain of Section 13, with collider
`c` and spectator `s`.  Corollary 15.2 supplies `t!=s` with

```text
r_{s,t}(t) >= r_s(t)+gamma.                         (15.7)
```

If the chain's second toggle is the collider-leave arm, then

```text
r_{c,s}(c)+gamma <= r_s(c).                         (15.8)
```

Consequently `t!=c`: taking `t=c` in (15.7) would give the reverse inequality
`r_s(c)+gamma<=r_{c,s}(c)`, contradicting `gamma>0` and (15.8).  Thus the
leave arm yields a genuinely outside label `t notin {c,s}` and the paid
two-step path

```text
{c,s} --c leaves by gamma--> {s}
      --t joins by gamma--> {s,t}.                  (15.9)
```

In the other arm, the chain already has a gap-sized outsider join from
`{c,s}` to a triple.  Therefore the exact rooted-two owner-chain residual is
reduced to

```text
gap-sized pair-to-triple join,
or a gap-sized leave followed by a gap-sized join by a different label.
                                                               (15.10)
```

### Subsumption and scope audit

The atomic-blocker barrier is strictly stronger than the direct
punished-singleton estimate in Theorem 14.1 and supplies all-behavior control
for an arbitrary forced-owner row.  The new content here is the narrow
same-table composition with the full-support packet's punishment-normality
and then with `FinFourRootedTwoNextOwnerLeaveCollisionChain`.  A narrow search
of the singleton-packet collision subtree found no existing declaration of
Theorem 15.1 or Corollaries 15.2--15.3.

This is meaningful semantic progress over the earlier incidence theorem: the
full residual now carries a terminal-gap collision out of every singleton,
and the owner-leave branch preserves the same quantitative gap through a
source-matched punished block.  It still does not turn the selected collision
cycle into a stationary endpoint certificate.  In particular, (15.6) is one
background per owner; the interval-core compiler requires uniform
blocker/continuation band inequalities over all backgrounds.  No chronology,
near-return, or monotone rank is asserted.

## 16. Constrained stationary localization of the leave--join arm

Status: complete ordinary theorem, source-audited, independently reviewed
PASS in
[`CODEX_RAMSEY`, Section 16](../feedback/CODEX_EULER__FIN4_SEARCH_SPACE_INVENTORY__BY_CODEX_RAMSEY__SECTION_16.md).
This section is the first post-alignment result whose output is an actual
stationary behavioral profile rather than another coalition incidence.  It
localizes unrestricted debt to two labels and retains a quantitative
nonsingleton terminal atom.  It is not yet an exact cyclic block or a payoff
return.

### 16.1 Exact finite data

Let the player type be `Fin 4`, let `reward` be bounded by `M`, and let
`witness : QuittingTerminalExploitabilityWitness reward`.  Write

```text
gamma = witness.terminalGap > 0.
```

Fix four distinct labels `c,s,t,o`.  Assume the two signs furnished by the
collider-leave arm of Corollary 15.3:

```text
r_{c,s}(c)+gamma <= r_s(c),                         (16.1)
r_s(t)+gamma <= r_{s,t}(t).                         (16.2)
```

Consider the finite two-player binary game of `c` and `t` in which `s` is
forced to Quit and `o` is forced to Continue.  Choose any mixed Nash
equilibrium, write its Quit probabilities as `x` for `c` and `y` for `t`,
and let `q` be the four-player product row

```text
q_s=1, q_o=0, q_c=x, q_t=y.                         (16.3)
```

Such `(x,y)` exists by the finite bimatrix Nash theorem.  Let `sigma` be the
stationary profile repeating `q`, and let `(U,B)=Sem(sigma)` be its literal
terminal-semantic pair.

### Theorem 16.1 (quantitative two-debtor stationary handoff)

Put

```text
alpha = gamma/(gamma+2M).
```

Then:

1. `0<alpha<=1` and `y>=alpha`;
2. the terminal law of `sigma` has total mass `y` on coalitions containing
   `{s,t}` and no other label except possibly `c`; consequently one of the
   two literal atoms `{s,t}` or `{c,s,t}` has mass at least `alpha/2`;
3. `B_c=U_c` and `B_t=U_t`, where `B` is the unrestricted behavioral
   best-response envelope, and hence

   ```text
   P_c<=U_c,  P_t<=U_t;                              (16.4)
   ```

4. there is `w in {s,o}` with

   ```text
   B_w-U_w >= gamma;                                 (16.5)
   ```

   in particular the positive-debt support of this actual carrier pair is a
   nonempty subset of `{s,o}` and has cardinality at most two; and
5. for such a `w`, the stationary pure-time decoder supplies a literal

   ```text
   Nonempty (QuittingPaidFirstDisagreementRow reward sigma w gamma).
                                                               (16.6)
   ```

Thus the gap leave--join chain enters an actual stationary source with a
fixed nonsingleton atom, two solved unrestricted coordinates, and a paid row
whose observer is outside those solved coordinates.

### 16.2 Hazard lower bound

Let `Delta_c(y)` be `c`'s date-zero payoff from Quit minus Continue in the
constrained game.  Since `s` quits surely and `o` continues surely,

```text
Delta_c(0)=r_{c,s}(c)-r_s(c) <= -gamma,              (16.7)
Delta_c(1)=r_{c,s,t}(c)-r_{s,t}(c) <= 2M.            (16.8)
```

Independence makes the endpoint difference affine in `t`'s marginal:

```text
Delta_c(y)=(1-y)Delta_c(0)+y Delta_c(1)
          <= -(1-y)gamma+2My.                       (16.9)
```

If `x>0`, the Nash support inequality gives `Delta_c(y)>=0`; hence

```text
y >= gamma/(gamma+2M)=alpha.                        (16.10)
```

If `x=0`, then `c` certainly Continues.  Player `t`'s endpoint difference is
exactly

```text
r_{s,t}(t)-r_s(t) >= gamma>0,
```

so Nash optimality forces `y=1`, and (16.10) again follows.  The bounded
difference in (16.2) gives `gamma<=2M`, so the denominator is positive and
`0<alpha<=1`.

Because `s` quits surely and `o` continues surely, absorption occurs at date
zero and the only terminal coalitions on the event `t` Quits are

```text
{s,t}       with mass (1-x)y,
{c,s,t}     with mass xy.                           (16.11)
```

Their sum is `y>=alpha`; one has mass at least `alpha/2`.

### 16.3 Unrestricted debt and floors

Any behavioral deviation of `c` or `t` still faces the surely quitting
player `s` at date zero.  The game therefore absorbs before a later history
can be reached, and the deviator's value depends only on its date-zero
Boolean marginal.  The constrained mixed-Nash inequalities control every
such marginal.  Thus each of `c,t` obtains its full stationary unilateral
cap, proving

```text
B_c=U_c, B_t=U_t.                                   (16.12)
```

The checked general inequality

```text
quittingPunishmentValue_le_stationaryUnilateralCap
```

then gives (16.4).

Apply `witness.terminalExploitability` to the literal stationary profile
`sigma`.  Its selected deviation gains at least `gamma`.  Equations (16.12)
exclude `c` and `t`, so the selected player `w` lies in `{s,o}` and satisfies
(16.5).  This proves the debt-support assertion using the actual
all-behavior cap, not a stationary regret surrogate.

Finally the checked declaration

```text
exists_oriented_quitNow_never_gap_of_stationary_cap_debt
```

is stated with `quittingStationaryUnilateralCap`.  First rewrite the envelope
coordinate in (16.5) using the checked identity

```text
quittingTerminalSemanticPair_stationary_envelope_eq_cap.
```

The oriented theorem then turns (16.5) into a difference of at least `gamma` between
immediate Quit and Never against `sigma`.  The checked paid-row decoder

```text
exists_quittingPaidFirstDisagreementRow_of_pureTimePayoff_sub
```

then gives (16.6), with the original opponents, terminal law, and observer.

### 16.4 Source adapter and scope

In Corollary 15.3 take `c` to be the collider, `s` the chain spectator, and
`t` the guaranteed third-label joiner.  The remaining Fin4 label is `o`, so
all hypotheses above are literal fields or consequences of the reviewed
rooted-two handoff.  The finite Nash selection introduces no public
randomization: `x` and `y` are the private independent date-zero marginals of
`c` and `t`.

This theorem is not subsumed by the checked
`exists_largeBasePaidStationaryHandoff`.  That result solves the full
three-free-player game around a singleton sure owner and localizes debt after
an owner replacement; it does not retain the leave--join labels or a fixed
pair/triple atom.  Conversely Theorem 16.1 solves only the two selected free
players.  The fourth label `o` may still have debt or lie below punishment,
and the sure owner `s` may have debt.  Therefore (16.6) is a paid-row source,
not an exact Nash--Bellman edge, floor-safe stack, payoff return, or uniform
equilibrium.  The precise next question is whether the fixed atom in (16.11)
and the two-coordinate debt support can enter the checked full-replacement
rank descent or paid-return consumer without assuming a connector to the
minimum plateau.

## 17. A paid stationary source cannot be locally exactified below the minimum-fiber moat

This section does not infer floor safety for the Section 16 source.  Instead
it gives the exact alternative needed before any floor-edge claim is legal:
either that actual semantic source is uniformly off the global minimum, or
its literal tail admits no charged exact root at all.

### 17.1 Data and the uniform linear minimum tube

Assume the literal `Fin 4` reward table has no uniform-equilibrium payoff.
Let `M>=0` bound every reward coordinate.  The checked minimum-fiber theorem

```text
exists_finFour_minimumFiberIsolation_and_debtMoat_of_no_uniformPayoff
```

supplies a carrier minimizer `X_*`; write

```text
D_* = D(X_*),
M_* = {X in Carrier : D(X)=D_*},
K   = {X.1 : X in M_*}.                              (17.1)
```

The carrier and `M_*` are compact, hence so is `K`.  The same checked theorem
gives one uniform `delta_*>0` with

```text
X.1_i-r_i({i}) >= delta_*                            (17.2)
```

for every `X in M_*` and every player, and all-Continue is the unique exact
product root against every tail in `K`.

Apply the independently reviewed theorem in
`exports/STRICT_ALLCONTINUE_BASIN_LINEAR_ABSORPTION_DEFECT.md` to `K`.  There
are an open set `N` containing `K` and `c_*>0` such that for every tail
`V in N` and every product root `q`,

```text
c_* A(q) <= Def(V,q).                                (17.3)
```

Here `A` is literal one-row absorption and `Def` is total one-stage root Nash
defect.

### Theorem 17.1 (linear carrier moat)

There is `eta_*>0` such that every terminal-semantic carrier pair `X`
satisfies the following exact alternative:

```text
D(X) >= D_*+eta_*                                   (17.4)
```

or else `X.1 in N`, and therefore every `epsilon`-Nash product root against
the literal tail `X.1` satisfies

```text
A(q) <= 4*epsilon/c_*.                               (17.5)
```

In particular, in the second arm every exact root is all-Continue.  Its
Bellman successor is exactly `X.1` and its charge is zero.

#### Proof

Let

```text
Outside = Carrier intersect fst^(-1)(N^c).           (17.6)
```

This set is compact.  It contains no point of `M_*`, since `K subset N`.
If it is empty, take `eta_*=1`.  Otherwise total semantic debt attains its
minimum `D_out` on `Outside`.  Global minimality gives `D_*<=D_out`, and
equality would put the minimizing outside point in `M_*`, contradicting
`K subset N`.  Thus `D_*<D_out`; take

```text
eta_*=(D_out-D_*)/2>0.                               (17.7)
```

If (17.4) fails, then `D(X)<D_*+eta_*<D_out`, so `X` cannot lie in
`Outside`; hence `X.1 in N`.  Equation (17.3) and the checked estimate

```text
Def(X.1,q) <= card(Fin 4)*epsilon = 4*epsilon
```

give (17.5).  At `epsilon=0`, absorption is zero.  For independent Boolean
marginals that means every Quit probability is zero, so the root is exactly
all-Continue and its successor equals its tail.  QED.

### Corollary 17.2 (the Section 16 paid-source conversion barrier)

Let `sigma` be the actual stationary profile produced in Theorem 16.1 and
put

```text
X_sigma = quittingTerminalSemanticPair reward sigma = (U,B).
```

This is a literal member of the terminal-semantic carrier.  It retains all
of the reviewed Section 16 outputs: the pair-or-triple atom of mass at least
`alpha/2`, zero debt and punishment floors for `c,t`, a debtor
`w in {s,o}` with `B_w-U_w>=gamma`, and the source-matched paid row.

At least one of the following barrier arms holds:

1. **Off-minimum source:**

   ```text
   D(X_sigma) >= D_*+eta_*;                          (17.8)
   ```

2. **Locally frozen source:** every exact product root at the literal tail
   `U` is all-Continue, and every `epsilon`-root has charge at most
   `4*epsilon/c_*`.

Consequently, a positive-charge exact Nash--Bellman edge whose continuation
tail is the literal paid-source payoff `U` can exist only in arm 1.  If `U`
is punishment-floor safe, arm 2 has only the zero-charge identity
floor-admissible edge.  If `U` is not floor safe, no punishment-floor edge
with that literal tail is admissible in the first place.  Thus floor clipping
or replacing `U` by the cap `B` is a genuinely nonsemantic change of tail;
the paid row alone does not authorize it.

### 17.3 Successor-linked approximate nonlocality

The independently reviewed Proposition 3 in
`notes/CODEX_RAMSEY__STRICT_ALLCONTINUE_BASIN_LINEAR_DEFECT.md` strengthens
the second arm for actual approximate Bellman paths.  After shrinking `N`
to a bounded neighborhood of `K`, choose `C>0` bounding both the reward table
and every payoff coordinate in `N`, and choose its collar radius `rho>0`.  If

```text
V_t = Succ(V_(t+1),q_t),
dist_infinity(V_L,K)<rho/2,
E=sum_(t<L) epsilon_t < c_* rho/(16C),               (17.9)
```

where each `q_t` is an `epsilon_t`-root against `V_(t+1)`, then every tail
lies in `N` and

```text
sum_(t<L) A(q_t) <= 4E/c_*,
max_(t<=L)||V_t-V_L||_infinity <= 8CE/c_* < rho/2.   (17.10)
```

Thus an arbitrarily long approximate conversion ending at the minimum fiber
cannot hide a fixed charge or a fixed-size nonlocal payoff excursion while
its aggregate error tends to zero.  This is orientation-sensitive: it does
not exclude one incoming edge whose continuation tail is outside `N`.

### 17.4 Scope and exact remaining obligation

Theorem 17.1 is a quantitative obstruction, not a paid-row consumer.  It does
not compare `D(X_sigma)` numerically with `D_*+eta_*`, produce a descending
edge from the off-minimum arm, or make `U` floor safe.  It also does not assign
semantic debt to an arbitrary payoff-only Bellman tail.  Its exact frontier
change is that a local positive-charge exactification of the accepted paid
source is impossible: any such conversion must first supply the independently
missing off-minimum carrier excursion (17.8), and any approximate substitute
must spend a nonvanishing aggregate root-error budget or enter from outside
the minimum tube.

## 18. A quantitative blocker premium enters the stationary handoff or a full-gap triple join

This section consumes one of the two arms of the independently reviewed
Proposition 6 in
`notes/CODEX_CEDAR__FOUR_PLAYER_CONJECTURE_CAPSTONE.md`.  Its point is not a
new incidence classification.  The pure pair itself is an unrestricted
behavioral test profile, so the common terminal gap prices its only remaining
membership toggles.  One of those toggles feeds the already checked
leave--join stationary construction.

### 18.1 General same-table dispatch

Let the player type be literally `Fin 4`, let `reward` be a quitting reward
table, and let

```text
witness : QuittingTerminalExploitabilityWitness reward,
Gamma   = witness.terminalGap > 0.                    (18.1)
```

Assume every player is punishment-normal.  Let `M>=0` bound every reward
coordinate in absolute value.  Fix distinct players `k,i` and a number
`kappa>0` such that

```text
r({k})_i+kappa <= r({k,i})_i.                         (18.2)
```

Thus `i` has a quantitative incentive to join the singleton exit of `k`.

### Theorem 18.1 (premium-to-semantic-handoff dispatch)

Under the preceding hypotheses, at least one of the following holds.

1. **Full-gap pair-to-triple join.**  There is
   `j notin {k,i}` such that

   ```text
   r({k,i})_j+Gamma <= r({k,i,j})_j.                  (18.3)
   ```

2. **Actual stationary two-debtor handoff.**  There are labels `t,o`, with
   `k,i,t,o` pairwise distinct, and

   ```text
   Nonempty (
     FinFourLeaveJoinStationaryTwoDebtorHandoff
       reward witness M k i t o).                    (18.4)
   ```

In arm 2 the checked handoff retains all of its literal outputs: an actual
stationary behavioral source, a terminal pair-or-triple atom of fixed mass,
zero unrestricted debt and punishment floors for the two solved players,
debt supported on at most the other two labels, and a source-matched paid
first-disagreement row.

#### Proof

Apply the checked quantitative membership-toggle theorem

```text
QuittingTerminalExploitabilityWitness.exists_leave_or_join_gain
```

to the pure exit set `S={k,i}`.  It gives either a member `m in S` with

```text
r(S)_m+Gamma <= r(S\{m})_m,                           (18.5)
```

or an outsider satisfying (18.3).

The member in (18.5) cannot be `i`.  If it were, then `S\{i}={k}` and
(18.5) would say

```text
r({k,i})_i+Gamma <= r({k})_i,
```

contradicting (18.2) and `kappa,Gamma>0`.  Hence the member is `k`, and

```text
r({k,i})_k+Gamma <= r({i})_k.                         (18.6)
```

Punishment normality of `i` and the checked theorem

```text
QuittingTerminalExploitabilityWitness.
  exists_atomicCollision_gain_of_normal
```

give `t!=i` with

```text
r({i})_t+Gamma <= r({i,t})_t.                         (18.7)
```

Moreover `t!=k`.  Substituting `t=k` in (18.7) and combining with (18.6)
would give

```text
r({k,i})_k+Gamma <= r({i})_k,
r({i})_k+Gamma <= r({k,i})_k,
```

contradicting `Gamma>0`.  Since the player type is `Fin 4`, choose the unique
remaining label `o`; then `k,i,t,o` are pairwise distinct.

Equations (18.6)--(18.7) are exactly the hypotheses of the checked constructor

```text
nonempty_finFourLeaveJoinStationaryTwoDebtorHandoff
```

with leaver `k`, sure spectator `i`, joiner `t`, and fourth label `o`.
Applying it with the supplied reward bound proves (18.4).  This exhausts the
leave-or-join alternative.  QED.

### Corollary 18.2 (the zero-drop blocker capstone has only three outputs)

Apply Theorem 18.1 to the quantitative pair-premium arm of Proposition 6,
where

```text
kappa = g_a/2 > 0.                                   (18.8)
```

The zero-semantic-debt-drop branch of the fixed-charge chronology therefore
has the following exhaustive refinement:

1. the one-coordinate source-anchored repayment of Proposition 6;
2. a full-terminal-gap pair-to-triple join (18.3); or
3. the actual stationary two-debtor handoff (18.4).

The third arm is already accepted by an unrestricted-deviation semantic
consumer.  Thus the quantitative pair premium is no longer itself a live
residual; only its pair-to-triple toggle subarm remains outside the checked
stationary handoff.

### 18.2 Probability, source, and scope audit

The pair test uses the pure stationary profile in which exactly `k,i` Quit
surely at date zero.  Any unilateral behavioral deviation is bounded by its
membership toggle because absorption occurs immediately; this is already
built into `exists_leave_or_join_gain`.  No stationary-regret surrogate or
public correlation is used.  The stationary handoff in arm 2 solves its two
free coordinates against every behavioral deviation because its sure
spectator absorbs at date zero.

The source is not an assumed pair certificate.  Proposition 6 produces
(18.2), with `kappa=g_a/2`, from the actual zero-drop blocker gate on the same
no-uniform reward table.  All-player normality and the same witness are fields
of the checked Fin4 residual.  The second collision (18.7) therefore retains
the same `Gamma`; no gap is reselected.

This theorem does not consume the pair-to-triple join, turn the stationary
paid row into a payoff near-return, or close the one-coordinate repayment
arm.  It also does not claim that (18.2) alone is an equilibrium compiler.
Its strict frontier change is narrower and exact: the entire quantitative
pair-premium arm now either enters the accepted stationary semantic handoff
or reaches one full-gap triple-join chamber.

## 19. A full-gap pair-to-triple join has an actual pair-base two-debtor source

Section 18 left one static reward-table arm.  This section consumes that arm
without another incidence classification.  Keep the joining pair as two sure
quitters and solve the complete induced game on the two remaining players.
The original join inequality forces a quantitative amount of free-player
hazard in every induced Nash point.  Two sure quitters make the free-player
Nash conditions valid against unrestricted behavioral deviations.

### 19.1 Exact data

Let the player type be literally `Fin 4`.  Let `reward`, `witness`, `Gamma`,
and `M` be as in (18.1), with

```text
0 <= M,
|reward(A)_h| <= M                                    (19.1)
```

for every nonempty terminal coalition and coordinate.  Fix four pairwise
distinct labels `k,i,j,o`.  Assume the full-gap pair join

```text
reward({k,i})_j + Gamma <= reward({k,i,j})_j.          (19.2)
```

Put

```text
base = {k,i},       free = {j,o},
alpha = Gamma/(Gamma+2M).                             (19.3)
```

The inequality (19.2) and (19.1) imply `Gamma<=2M`; hence the denominator in
(19.3) is positive and `0<alpha<=1`.

### Theorem 19.1 (pair-base join stationary two-debtor handoff)

Choose any

```text
point in quittingPersistentBaseNashSet reward base free
```

and let `q=quittingPersistentBaseRoot base free point`.  Thus `k,i` Quit
surely, `j,o` use the selected independent Nash marginals, and there is no
outside player.  Let `sigma` be the corresponding stationary behavioral
profile and let

```text
X=(U,B)=quittingTerminalSemanticPair reward sigma.
```

Then all of the following hold.

1. The two free coordinates are solved with their unrestricted caps and lie
   above punishment:

   ```text
   B_j=U_j,  B_o=U_o,
   P_j<=U_j, P_o<=U_o.                                (19.4)
   ```

2. The free-player absorption probability is quantitatively positive:

   ```text
   1-(1-q_j(Quit))(1-q_o(Quit)) >= alpha.             (19.5)
   ```

3. The three terminal atoms which strictly contain the base have masses

   ```text
   mu({k,i,j})   = q_j(Quit)(1-q_o(Quit)),
   mu({k,i,o})   = (1-q_j(Quit))q_o(Quit),
   mu({k,i,j,o}) = q_j(Quit)q_o(Quit).                (19.6)
   ```

   Their sum is the left side of (19.5), so at least one has mass at least

   ```text
   alpha/3 = Gamma/[3(Gamma+2M)].                     (19.7)
   ```

4. Every positive unrestricted debt coordinate belongs to the sure base:

   ```text
   {h : B_h-U_h>0} subset {k,i}.                      (19.8)
   ```

   In particular there is a debtor `w in {k,i}` with

   ```text
   Gamma <= B_w-U_w.                                  (19.9)
   ```

5. The stationary pure-time decoder supplies a literal source-matched row

   ```text
   Nonempty (QuittingPaidFirstDisagreementRow
     reward sigma w Gamma).                           (19.10)
   ```

Thus (19.2) enters an actual stationary behavioral source with a fixed
nonsingleton atom, two unrestrictedly solved players, at most two debtors,
and a paid row whose observer is one of the two sure base labels.

#### Proof

Nonemptiness of the complete induced Nash set is the checked theorem

```text
quittingPersistentBaseNashSet_nonempty.
```

Write

```text
x=q_j(Quit),       y=q_o(Quit),
Delta_j(y)=QuitEndpoint_j-ContinueEndpoint_j.         (19.11)
```

When `o` Continues, (19.2) says `Delta_j(0)>=Gamma`.  When `o` Quits,
boundedness gives `Delta_j(1)>=-2M`.  Independence and endpoint affineness
therefore give

```text
Delta_j(y)
  =(1-y)Delta_j(0)+y Delta_j(1)
  >= (1-y)Gamma-2My.                                 (19.12)
```

If `x=1`, the left side of (19.5) is one.  If `x<1`, Continue has positive
probability in `j`'s induced mixed law.  Exact Nash support gives
`Delta_j(y)<=0`; (19.12) then yields

```text
y >= Gamma/(Gamma+2M)=alpha.                         (19.13)
```

The left side of (19.5) is at least `y`, proving (19.5).  Since both base
players Quit surely, the row absorbs at date zero.  Expanding the independent
two-coordinate law gives (19.6), and the three masses sum to (19.5); the
largest is at least one third of their sum, proving (19.7).

For either free player, even after an arbitrary unilateral behavioral
deviation the two base players still Quit at date zero.  No later history is
reachable, so the full behavioral best-response value is the maximum of the
two date-zero forced-action endpoints.  Membership of `point` in the complete
induced Nash set says the selected marginal attains this maximum.  Hence the
stationary prescribed payoff equals the unrestricted cap in each free
coordinate.  The checked punishment upper leg then proves (19.4), and (19.8)
follows.

Apply `witness.terminalExploitability` to the literal stationary profile
`sigma`.  The selected deviation improves one coordinate by at least
`Gamma`; bounding that deviation by the stationary unilateral cap and
rewriting the terminal-semantic envelope via

```text
quittingTerminalSemanticPair_stationary_envelope_eq_cap
```

gives a coordinate with debt at least `Gamma`.  Equations (19.4) and
`Gamma>0` force that debtor into `{k,i}`, proving (19.9).  Finally rewrite
its debt as stationary cap minus prescribed payoff, apply

```text
exists_oriented_quitNow_never_gap_of_stationary_cap_debt
```

and then

```text
exists_quittingPaidFirstDisagreementRow_of_pureTimePayoff_sub.
```

This gives (19.10) with the original source and opponents.  QED.

### Corollary 19.2 (the pair-premium arm is entirely semantic)

Combine Theorem 19.1 with Theorem 18.1.  Every quantitative pair premium
from Proposition 6 has at least one of the following semantic outcomes:

1. the checked singleton-base leave--join stationary two-debtor handoff
   (18.4); or
2. the pair-base stationary two-debtor handoff (19.4)--(19.10).

Consequently the complete zero-drop blocker split is now:

1. Proposition 6's source-anchored one-coordinate exact repayment; or
2. an actual stationary source with a fixed nonsingleton atom, two solved
   unrestricted coordinates, at most two debtors, and a source-matched paid
   first-disagreement row.

The formerly static full-gap pair-to-triple chamber is no longer left as an
untyped reward-table toggle.

### 19.2 Scope and next obstruction

This is a producer from same-table no-uniform data, not a supplied-profile
verifier.  The mixed point is selected from the full induced Nash set, and
all behavioral-cap assertions follow from literal date-zero absorption by
two opponents.  No public correlation or bounded-controller restriction is
used.

The theorem still does not produce an exact Nash--Bellman edge: either sure
base player may prefer to Continue, and either base coordinate may lie below
punishment.  The heavy triple/grand atom is a behavioral terminal-law atom,
not Bellman charge.  Therefore Corollary 19.2 enters the paid-source lane but
does not yet give payoff near-return, minimum-fiber descent, or a uniform
equilibrium.  The remaining exact semantic question is now common to both
stationary handoffs: can a fixed nonsingleton atom plus two-coordinate debt
support force a floor-admissible charged edge, or must every such conversion
pay the reviewed off-minimum carrier/debt-error toll?

## 20. Every minimum debtor has a source-native fixed-law reset dispatch

The common conversion problem admits one unconditional semantic reduction
which does not depend on the accidental labels of either stationary handoff.
Use a two-player sure base to build an actual complete-law target which resets
any chosen minimum debtor, then apply the checked fixed-law reset-face theorem.
This produces either an exact charged cap edge with strict semantic-debt
contraction or the precise all-Continue reset/circulation wall.

### 20.1 Pair-base reset target

Let `reward` be a quitting table on literal `Fin 4` with terminal witness
`witness`.  Let

```text
X_*=(U_*,B_*) in quittingTerminalSemanticCarrier reward
```

be a global minimizer of total debt, with

```text
D_*=D(X_*)>0.                                         (20.1)
```

Choose a debtor `e` with `d_e(X_*)>0`.  Choose three further labels `b,c,f`
so that `e,b,c,f` are pairwise distinct, and put

```text
base={b,c},       free={e,f}.                         (20.2)
```

Select any exact point of

```text
quittingPersistentBaseNashSet reward base free,
```

let `sigma` be its ambient stationary profile, let

```text
T=quittingTerminalSemanticPair reward sigma,
lambda=quittingTerminalOutcomeMass reward sigma.      (20.3)
```

The same all-behavior argument as in Section 19 gives

```text
(T,lambda) in quittingTerminalSemanticLawCarrier reward,
d_e(T)=0.                                              (20.4)
```

Moreover `b` Quits surely in every terminal realization.  Hence the complete
law has unit opponent incidence

```text
Incidence_e,b(lambda)=1.                               (20.5)
```

In particular it is strictly positive.  Notice that this target is produced
for the chosen minimum debtor `e`; no label alignment with a previously
selected paid row is assumed.

### Theorem 20.1 (minimum-debtor fixed-law reset alternative)

For every choice above there is a returned pair `R` such that

```text
(R,lambda) in quittingTerminalSemanticLawCarrier reward,
d_e(R)=0,
D_* <= D(R) <= D(T),                                  (20.6)
```

and the lost minimum debt of `e` is transferred to the other coordinates:

```text
d_e(X_*) <= sum_(h!=e) (d_h(R)-d_h(X_*)).             (20.7)
```

The law `lambda` contains a positive-mass terminal coalition `A` with
`b in A` and a strict terminal-witness membership toggle at `A`.  In addition,
at least one of the following holds.

1. **Exact charged cap contraction.**  There is an exact product root `q` at
   the literal cap tail `R.2` such that

   ```text
   0<A(q),        0<ContinueMass(q),
   R'=Prefix(q,R),
   D(R')<D(R),        d_e(R')=0,                      (20.8)
   (R', PrefixLaw(q,lambda)) lies in the law carrier,
   Incidence_e,b(PrefixLaw(q,lambda))>0.
   ```

   The same cap-Nash root gives a literal exact punishment-floor Bellman edge

   ```text
   R.2  ->  W,       W=Succ(R.2,q).                   (20.9)
   ```

   Here `R.2` is an actual carrier cap, while `W` is its exact Bellman
   successor annotation.  This is the semantic direction of the checked
   admissible charged relation (`src=tail`, `tgt=current`); behavioral
   chronology reads the same edge in reverse, from `W` to continuation
   `R.2`.  Box and floor propagation keep both annotations in the reward box
   and above the behavioral punishment floor.  Thus this arm couples an exact
   floor-safe charged edge with positive survival to a strict contraction of
   the actual semantic prefix `R'`.  It does not identify `W` with `R'.2`.

2. **All-Continue fixed-law reset wall.**  The all-Continue root is exact at
   `R.2` and fixes `R` under semantic prefixing.  Equations (20.6)--(20.7),
   the complete law `lambda`, its positive incidence, and its supported strict
   nonsingleton toggle all remain attached to the same returned reset point.

#### Proof

The induced Nash set in (20.2) is nonempty by
`quittingPersistentBaseNashSet_nonempty`.  Because two opponents Quit surely,
an arbitrary deviation by either free player is resolved at date zero.  The
induced Nash endpoint inequalities therefore attain the full unrestricted
stationary caps, proving (20.4).  Sure quitting by `b`, sure date-zero
absorption, and `b!=e` prove (20.5) by expanding the outcome law.

Now apply the checked declaration

```text
QuittingTerminalExploitabilityWitness.exists_fixedLawResetDispatch
```

with source `X_*`, target `T`, law `lambda`, reset owner `e`, and incidence
label `b`.  Global minimality, (20.1), (20.4), and (20.5) are exactly its
hypotheses.  Its returned packet gives (20.6)--(20.8), the transfer inequality,
and the supported strict toggle.

In the absorbing arm, exact cap-Nash gives the Bellman successor

```text
W=quittingRootSuccessorPayoff reward R.2 q.
```

The carrier cap `R.2` dominates punishment, and the checked exact-floor
successor inequality puts `W` above punishment; boundedness is preserved by
the successor formula.  Separately, carrier closure puts the literal semantic
prefix `R'=Prefix(q,R)` in the semantic carrier and the reset-excursion
account gives its strict debt contraction.  These two outputs share the same
root and cap tail, but in general
`R'.2 != quittingRootSuccessorPayoff reward R.2 q`; no such identification is
used.  This proves (20.8)--(20.9).  The other arm is literally the
all-Continue alternative stored by the checked dispatch.  QED.

### 20.2 Frontier consequence and exact limitation

Theorem 20.1 is a producer from the actual positive minimum, not a verifier
for a supplied reset packet.  It proves that failure to obtain an exact
floor-safe charged cap edge with strict semantic-prefix debt contraction has
a very specific residual: a reset point retaining a complete unit-incidence
law, a supported strict nonsingleton toggle, and an exact all-Continue cap
self-loop after one positive minimum debt coordinate has been erased and
transferred elsewhere.

This does not yet contradict global minimality: the contracted prefix in arm
1 may still have debt strictly above `D_*`.  Nor does (20.7) make the
all-Continue arm a support-rank descent, because previously zero coordinates
may acquire debt.  The reviewed flat-circulation theorem explains precisely
what additional tangent/no-entry information turns such transfers into rank
descent or a paid exit; Theorem 20.1 does not manufacture that infinitesimal
information.  It also does not identify the supported law atom with the paid
atom of Sections 16 or 19.  The remaining capstone is therefore the
all-Continue fixed-law reset wall, not arbitrary failure of floor-safe root
selection.

## 21. The zero-drop blocker gate has no static join or root-selection residual

The independently reviewed source-native wall dispatch in Proposition 9 of
`notes/CODEX_CEDAR__FOUR_PLAYER_CONJECTURE_CAPSTONE.md` eliminates the
all-Continue/changed-solo selection wall from the zero-drop carrier gate.  Its
only non-descent outputs are the full-terminal-gap triple join and the
singleton-base stationary two-debtor handoff.  Theorem 19.1 above converts the
former, on the same reward table, to a pair-base stationary two-debtor source.
Thus these two reviewed reductions compose without another incidence split.

### Corollary 21.1 (zero-drop carrier descent or stationary two-debtor source)

Let `reward` be a quitting table on literal `Fin 4` with terminal witness of
gap `Gamma>0`, positive global minimum semantic debt, and all four players
punishment-normal.  Fix `M>=0` with

```text
|reward(A)_h|<=M
```

for every nonempty terminal coalition `A` and player `h`.  Start with a
literal zero-drop carrier gate of Proposition
5 in `notes/CODEX_CEDAR__FOUR_PLAYER_CONJECTURE_CAPSTONE.md`, including the
maximizing-blocker reselection of its Proposition 6.  Then at least one of the
following holds.

1. **Literal charged semantic descent.**  After finitely many exact carrier
   prefixes there are a literal carrier pair `W`, an exact product root `z` at
   `W.1`, and constants `omega>0`, `D=D(W)>0` such that

   ```text
   A(z)>=omega,
   Prefix(z,W) is a literal floor-safe semantic carrier pair,
   D(Prefix(z,W))<=D(W)-omega*D.                       (21.1)
   ```

2. **Actual stationary two-debtor source.**  The same reward table has a
   stationary profile and its literal semantic pair/law such that:

   ```text
   two distinct coordinates are solved against all behavioral deviations,
   those two coordinates lie above punishment and have debt zero,
   all debt is supported on the complementary two labels,
   a fixed nonsingleton terminal coalition has positive mass and a strict
     terminal-witness reward toggle,
   one of the two remaining debtors has debt at least Gamma and admits a
     source-matched paid first-disagreement row.        (21.2)
   ```

   More precisely, this is either the checked
   `FinFourLeaveJoinStationaryTwoDebtorHandoff` or the pair-base source of
   Theorem 19.1, whose selected triple/grand atom has mass at least

   ```text
   Gamma/[3*(Gamma+2*M)].                              (21.3)
   ```

#### Proof

Apply the reviewed source-native wall dispatch.  Its first output is exactly
(21.1).  Its third output is the checked singleton-base handoff in (21.2).
In its second output there are distinct `k,i,j` satisfying

```text
r_{ki}(j)+Gamma<=r_{kij}(j).                          (21.4)
```

Apply Theorem 19.1 to (21.4).  It selects a Nash point of the full two-free-
player induced game behind the sure base `{k,i}`.  The theorem's unrestricted
deviation argument, floor inequalities, atom estimate, terminal-debtor
localization, and pure-time decoder give (21.2)--(21.3).  These cases exhaust
the source-native wall dispatch.  QED.

### 21.2 Chronology, invariant, and remaining obstruction

The first alternative is genuinely chronological: each intermediate object
is a literal semantic carrier prefix, and (21.1) is a strict decrease of the
literal all-behavior semantic-debt invariant along an exact positively charged
edge.  The second alternative is a same-table producer.  In the triple-join
subcase Theorem 19.1 reselects an induced stationary Nash point; it does **not**
claim that this point is reached from the terminating wall by an exact Bellman
path.  Keeping these two provenance modes separate is essential.

Consequently the zero-drop blocker branch has no remaining static triple-join
chamber and no remaining all-Continue/solo-root selection chamber.  Its exact
residual is a common semantic one: convert an actual stationary source with a
fixed nonsingleton atom, two unrestrictedly solved coordinates, and at most two
debtors into a floor-admissible charged connector or a return/descent.  Neither
Corollary 21.1 nor its inputs produce that connector, iterate (21.1) across a
change of support, identify terminal-law mass with Bellman absorption, or prove
a payoff near-return or uniform equilibrium.

## 22. The singleton-owner paid handoff can be aligned with any prescribed label

The large-base construction first used the singleton-base handoff only after
selecting an owner from a paid two-plus-two cell.  That provenance can obscure
a stronger checked quantifier already available on the same table.  The
terminal witness itself supplies the compact owner-floor gap for **every**
prescribed owner when the free set is its full complement.  Thus the handoff's
owner may be aligned in advance with a collision owner, a hard-principal
member, or a selected minimum debtor.  The paid observer still cannot be
prescribed.

### Theorem 22.1 (universal owner-aligned stationary paid handoff)

Let `reward` be a finite quitting reward table with

```text
witness : QuittingTerminalExploitabilityWitness reward.
```

For every player `d`, put

```text
F_d = univ.erase d.
```

There is `delta_d>0` such that **every** induced Nash point

```text
z in quittingPersistentBaseNashSet reward {d} F_d
```

has

```text
delta_d <= quittingSingletonBaseOwnerFloorExcess
  reward d (quittingPersistentBaseRoot {d} F_d z),    (22.1)
```

and carries

```text
Nonempty (
  QuittingSingletonBaseStationaryHandoff
    reward d F_d z delta_d witness.terminalGap).      (22.2)
```

In particular, before repair the sure-`d` stationary source has zero
unrestricted behavioral debt on all three players in `F_d`, lies above their
punishment floors, and has owner debt at least `delta_d`.  Replacing `d` by
Always Continue attains its old cap and produces a paid
first-disagreement row of gain `witness.terminalGap` observed by some

```text
j_d in F_d, hence j_d != d.                           (22.3)
```

The repaired source is either floor safe in every coordinate or has an
explicit free coordinate below punishment, exactly as recorded in the
handoff structure.

#### Proof

Fix `d`.  Apply the checked theorem

```text
QuittingTerminalExploitabilityWitness.exists_pos_ownerFloorExcess_gap
```

with owner `d`, free set `F_d`, and the literal identity
`F_d=univ.erase d`.  This gives `delta_d>0` and (22.1) uniformly over the
complete compact induced Nash carrier.  For any `z` in that carrier, apply

```text
exists_singletonBaseStationaryHandoff
```

with the same complement identity, `witness`, `delta_d>0`, and (22.1).  This
is exactly (22.2).  The unrestricted source semantics, repair equalities,
outside-debtor membership, floor disjunction, and paid row in (22.3) are
fields of the returned handoff.  QED.

### Corollary 22.2 (what alignment is genuinely removed)

In the no-uniform `Fin 4` residual, Theorem 22.1 can be instantiated with any
label already selected by another same-table theorem.  For example, one may
take `d` to be:

- the owner or collider of a marked collision lasso;
- either member of a nonprojective hard pair;
- the unique outsider of a hard triple; or
- any chosen positive-debt coordinate of a minimum semantic carrier.

No relabeling or coincidence argument is needed to obtain a stationary paid
source whose repaired coordinate is that chosen `d`: after fixing `d`, invoke
`quittingPersistentBaseNashSet_nonempty reward {d} F_d`, choose a point `z`,
and apply Theorem 22.1 to that point.

This is only an **owner-coordinate alignment theorem**.  It does not prescribe
the returned observer `j_d`, align the induced Nash point or terminal law with
an earlier carrier, make the repaired source floor safe, or turn the paid row
into an exact Bellman edge.  In particular, applying the theorem for all four
owners does not connect the four resulting stationary profiles: they are
separate same-table reselections.  Finiteness of the owner/observer map is not
a chronology and supplies no return.  The live conjecture-facing obligation
therefore remains the common paid-source connector stated after Corollary
21.1, now with owner mismatch removed as a possible explanation for failure.

### Sources inspected for Section 22

- `QuittingTerminalExploitabilityWitness.exists_pos_ownerFloorExcess_gap` and
  `exists_singletonBaseStationaryHandoff` in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/LargeBaseStationarySemanticHandoff.lean`;
- `quittingPersistentBaseNashSet_nonempty` in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseInducedGame.lean`;
- the full-support/full-normal residual statement in
  `questions/FOUR_PLAYER_SINGLETON_PACKET_DISPATCH.md`.

Status: ordinary checked-theorem composition, independently reviewed PASS in
`feedback/CODEX_EULER__FIN4_SEARCH_SPACE_INVENTORY__BY_CODEX_RAMSEY__SECTION_22.md`.
It is not proposed for standalone export because it produces no connector,
return, contradiction, or well-founded decrease beyond the existing handoff.
