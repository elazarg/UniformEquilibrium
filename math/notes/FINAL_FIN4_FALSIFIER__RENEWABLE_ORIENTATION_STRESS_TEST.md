# Stress test of the final Fin4 renewable-orientation question

Author: `FINAL_FIN4_FALSIFIER`

## Status

I did not prove any of the required outputs and did not construct a Fin4
positive-gap table.  In particular, I found no finite potential forced by
spectator recharge, and no contradiction between the strict normalized inert
passport and the currently available positive-minimum data.

The stress test does isolate two points which a proposed solution must cross.

1. Target-law regeneration does not by itself define a transition whose tail
   is the incoming source point.  The regenerated point is the endpoint
   cluster `Y`, while the paid edge starts at a separately selected minimum
   cluster `X`.  Both have debt `D_*`, but the current interfaces do not assert
   `X = source.point.1`.
2. Even after hypothetically adding that anchoring, exact mover-debt
   subtraction plus spectator recharge admits closed debt circulation.  It
   does not force a scalar, support, or lexicographic rank.

Thus the question in
`questions/FIN4_RENEWABLE_ORIENTATION_OR_COUNTEREXAMPLE.md` is honestly
breakthrough-level.  Its stronger atom-alternative premise is real extra
data, but it still needs a chronological or no-new-support theorem; it is not
already a hidden finite-rank proof.

## Question checked

Under a hypothetical Fin4 terminal exploitability witness, consume both:

* the equality arm, consisting of a paid minimum-to-minimum three-role edge,
  its actual endpoint law, and full minimum-source regeneration at that law;
* the strict normalized arm, consisting of an off-minimum decorated passport
  whose exact cap--Nash correspondence is uniquely all Continue.

An answer must give terminal approximants, a checked return or chronological
shadowing object, a point below `D_*`, a renewable well-founded source rank,
or an actual all-behavior positive-gap table.

## Sources inspected

* `QuittingMarkedPairMinimumReturnActualizer` and
  `exists_minimumReturnActualizer_and_threeRoleLimitChord` in
  `Research/Quitting/NormalizedPassportMinimumReturn.lean`.
* `FinFourNormalizedReturnThreeRoleOrStrictInert` and
  `FinFourOwnerCompressedMinimumReturnForcedPairPacket.nonempty_normalizedReturnThreeRole_or_strictInert`
  in `Research/Quitting/FinFourProducerAtlas/NormalizedReturn.lean`.
* `HasQuittingStoppingLawVanishingDebtAtomAlternative` and
  `hasVanishingDebtAtomAlternative_of_endpointDebtRise` in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/VanishingDebtAtomAlternative.lean`.
* `FinFourQuantitativeFullSupportHardResidual` in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/FullSupportProjectiveQBarResidual.lean`.
* `FinFourMinimumAtomProducer` in
  `Research/Quitting/FinFourProducerAtlas/Source.lean`.
* The reviewed mathematical packets
  `exports/PAID_NONSINGLETON_CYCLE_SPECTATOR_RECHARGE_AND_ATOM_DISPATCH.md`,
  `exports/FIN4_STRICT_ENDPOINT_NORMALIZED_RETURN_PACKET_OR_INERT.md`, and
  `exports/FIN4_THREE_ROLE_MINIMUM_TARGET_LAW_SOURCE_REGENERATION.md`.

No literature theorem is used.

## 1. Regeneration is exact at the target law but not anchored at the input

In the equality arm, an actualizer supplies source and endpoint profiles

\[
 \sigma_n,\qquad \tau_n=\sigma_n[m\leftarrow\theta_n],
\]

with semantic limits

\[
 \operatorname{Sem}(\sigma_n)\to X,
 \qquad
 (\operatorname{Sem}(\tau_n),\operatorname{Law}(\tau_n))\to(Y,\nu),
\]

and

\[
 D(X)=D(Y)=D_*.
\]

The endpoint-law theorem correctly regenerates a complete
`FinFourMinimumAtomProducer` at `(Y,nu)`.  This fixes the former law-realization
gap.  But the actual normalized-return declarations only show that the whole
debts of the selected source profiles tend to `D_*`.  They do not show

\[
 X=\mathsf{source.point}.1.
\tag{1}
\]

The selected profiles are descendants of compactly selected forced-pair
profiles, and the source ranks and finite prefix words are retained, but their
semantic cluster may be another point of the minimum fibre.

Consequently the construction currently yields

\[
 \mathsf{source}
 \rightsquigarrow
 (X\stackrel{\rm paid}{\longrightarrow}Y)
 \rightsquigarrow
 \mathsf{next}(Y,\nu),
\tag{2}

not an actual directed edge

\[
 \mathsf{source.point}.1\longrightarrow Y.
\tag{3}

This is more than loss of a terminal law: the law is now restored exactly.
What remains missing is orientation of the new chronology relative to the
old paid edge.

## 2. Spectator recharge alone admits exact finite circulation

Suppose, more strongly than the checked interface, that every regenerated
source were anchored so that its paid edge really started at the incoming
minimum point.  The numerical debt information still would not force a
well-founded rank.

Fix `a>0` and consider four debt vectors of total debt `a`:

\[
 v_0=(a,0,0,0),\quad
 v_1=(0,a,0,0),\quad
 v_2=(0,0,a,0),\quad
 v_3=(0,0,0,a).
\tag{4}

On the transition `v_k -> v_(k+1 mod 4)`, declare player `k` to be the mover
and player `k+1` the recharged spectator.  Then, exactly,

\[
 \Delta d_k=-a,
 \qquad
 \Delta d_{k+1}=a,
 \qquad
 \sum_i\Delta d_i=0.
\tag{5}

Every edge has complete mover-debt subtraction and a fixed spectator rise,
yet the fourth edge returns to the initial vector.  In particular:

* total debt is constant;
* support cardinality is constant;
* supports rotate rather than include one another; and
* no function of the debt vector alone can strictly decrease on every edge.

The same observation applies to a finite label rank once the player/atom
labels return: appending those labels to (4) gives a literal finite directed
cycle.  This is an abstract numerical obstruction, not a quitting-game
counterexample.  It proves only that the recharge inequalities cannot be the
missing potential without an additional orientation condition.

The useful conditions which would break (4) are exactly the ones already
identified by the project:

\[
 \text{no support entry},\qquad
 \text{one fixed monotone receiving coordinate},\qquad
 \text{or chronological expenditure of the recharge.}
\tag{6}

None follows from the spectator average.

## 3. The vanishing-debt atom alternative has no implicit orientation

For one source/endpoint edge, the checked predicate is the disjunction

\[
 \begin{array}{l}
 \text{a prescribed terminal payoff-difference atom},\\
 \text{or a pure-time rectangle atom whose endpoint observer debt is small.}
 \end{array}
\tag{7}

The endpoint-rise decoder is strong in three ways: the charge is fixed, the
source and complete mover replacement are literal, and in the rectangle arm
the same pure-time response both carries the atom and leaves observer debt at
most the prescribed error.

It nevertheless does not assert that the response endpoint:

* lies on the minimum fibre;
* creates no debt at a previously inactive coordinate;
* is the entrance of the regenerated chronology at `(Y,nu)`; or
* is an exact punishment-floor Bellman edge.

The response changes the observer's complete strategy.  Its own cap is
unchanged, but the other three unrestricted caps may change.  Thus the
vanishing observer debt in (7) does not imply a minimum-fibre support drop.

There is a clean conditional boundary.  If one could additionally show for
the rectangle response endpoints `R_n` that

\[
 D(\operatorname{Sem}(R_n))\to D_*
\tag{8}

and that no coordinate outside the incoming positive-debt support acquires
positive limiting debt, then the checked minimum-fibre support machinery
would give a strict support drop whenever the recharged observer was active.
Condition (8) and no-new-entry are precisely the absent cross-coordinate cap
control; they are not consequences of the atom decoder.

## 4. “Full support” in the hard residual does not repair the rank

`FinFourQuantitativeFullSupportHardResidual.packet_support_eq_univ` concerns
the support of the normalized singleton source packet.  It does not state
that every coordinate of the selected minimum semantic debt vector is
positive.

Therefore one cannot argue that killing the recharged observer's debt
automatically lowers support merely because the hard residual is called
“full support.”  A response endpoint may kill one active coordinate while
activating a previously zero-debt coordinate, exactly as in (4).

## 5. Strict inert compatibility test

The strict normalized minimizer carries two logically different kinds of
data:

* a cap vector whose exact product-root Nash set is `{allContinue}`; and
* a limiting historical marked mass/gain passport in a compact prefix-orbit
  closure.

The unique-root assertion sees only the current cap vector.  The historical
passport sees a remote marked suffix and its comparison sibling.  The
existing exact Fin4 root-game regressions show that unique all Continue is
compatible with strict same-stage improvement cycles and with approximate
roots whose absorption is first order while Nash defect is smaller order.
Those regressions have `D_*=0`, so they do not refute the present question,
but they do rule out a local contradiction which ignores positive-minimum
provenance.

The positive-minimum provenance currently supplies the vertical toll: a
successor-linked path retaining the passport cannot leave the linear basin
with vanishing aggregate defect.  The uncovered regime

\[
 H_n\to\infty,qquad
 \max_t\operatorname{Def}_{n,t}\to0,qquad
 \liminf_n\sum_t\operatorname{Def}_{n,t}>0
\tag{9}

is consistent with every inspected identity.  The sum in (9) is unsigned
root Nash work.  I found no identity converting it into one player's signed
prescribed-payoff charge or into an admissible near-return.

An actual realization of the strict inert passport with `D_*>0` would already
come from a positive-gap table and therefore amount to the negative answer
requested by the question.  I found no such table.

## 6. Verdict

No proof or counterexample emerged from this stress test.  The following
implications remain unsupported:

\[
 \text{spectator recharge + target-law regeneration}
 \Longrightarrow
 \text{finite potential},
\]

and

\[
 \text{strict inert passport + positive minimum}
 \Longrightarrow
 \text{contradiction or signed return}.
\]

The final question has not accidentally assumed its conclusion, and its two
arms are not already incompatible at their public interfaces.  A valid next
argument must use one genuinely new bridge:

1. source-anchor the paid edge through regeneration and orient all possible
   recharge cycles;
2. prove minimum preservation plus no-new-entry for the common-response
   endpoint;
3. convert diffuse vertical normal work into a signed executable lasso; or
4. construct the actual positive-gap Fin4 table.

Anything weaker remains a diagnostic rather than one of the required
outputs.
