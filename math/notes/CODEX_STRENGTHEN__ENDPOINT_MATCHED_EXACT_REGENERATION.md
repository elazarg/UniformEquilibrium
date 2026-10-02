# Endpoint-matched exact Nash--Bellman regeneration: a Fin4 no-go and the surviving port

Author: `CODEX_STRENGTHEN`

Status: **SHARP GENERIC NO-GO / PRECISE POSITIVE-MINIMUM RESIDUAL; INTERNAL, NOT FOR EXPORT.**

This note continues
[`CODEX_STRENGTHEN__FIN4_FINITE_HAZARD_CAPACITY_RESIDUAL.md`](CODEX_STRENGTHEN__FIN4_FINITE_HAZARD_CAPACITY_RESIDUAL.md).

## Outcome

The existing full-replacement regeneration is exact at the level of the
**child semantic limit**:

```text
regeneration.next.point.1 = endpoint.cluster.
```

It is not exact at the level needed to carry finite Nash--Bellman capacity
through the parent-to-child transition.  Its exact cap--Nash words are built
over actual endpoint profiles converging to that child, and the words have
Continue product tending to one.  They neither start at the parent cap nor
end literally at the child cap.  In fact their total marginal-hazard charge
tends to zero.

Three natural repairs do not fill this field:

1. the common-response compiler gives one asymptotically optimal behavioral
   response for each nonmover, not one simultaneous exact Nash root or a
   Bellman predecessor hitting a prescribed cap;
2. a positive lower-bound constrained root with a strictly
   Continue-preferred coordinate has strictly positive unrestricted Nash
   defect, equal to its lower-face normal work; and
3. the arbitrary-endpoint Nash--Bellman factory fixes the terminal endpoint
   but leaves the other endpoint uncontrolled.

There is a sharp Fin4 counterexample to any generic repair based only on
actuality, one-player best-response replacement, common total debt, and
common exact cap responses.  In the constant terminal-reward table `-1`, two
actual one-date profiles have the same positive total semantic debt and
differ only by replacing one mover with its exact best response.  Their caps
are distinct interior vectors, and **no finite exact Nash--Bellman block
connects them in either direction**.  Thus a game-specific use of the
positive global-minimum geometry is indispensable.

The counterexample does not have positive global minimum debt: its global
minimum is zero.  It therefore refutes a universal cap-response/reset
compiler, not the still-open positive-minimum Fin4 port.

All calculations below are ordinary mathematics.  Checked declarations are
identified explicitly.

## 1. The exact endpoint field

Write a finite exact Nash--Bellman block in the standard order

\[
 B=(v_0,x_0,v_1,\ldots,x_{n-1},v_n),
 \qquad v_t=F_{x_t}(v_{t+1}),
\]

where `x_t` is exact Nash against `v_(t+1)`.  In the charged-relation
orientation used by
`quittingPunishmentFloorAdmissibleChargedRelation`, this is a path

\[
 v_n\longrightarrow v_{n-1}\longrightarrow\cdots\longrightarrow v_0.
\]

Consequently an escape-return transition from a parent cap `b_parent` to a
regenerated child cap `b_child` must supply, in the required orientation,

\[
 v_n=b_{\rm parent},\qquad v_0=b_{\rm child}.                 \tag{1}
\]

If the intended transition has the opposite orientation, the equalities in
(1) must be reversed; an exact predecessor edge cannot simply be traversed
backwards.

For carrying the charged-relation potential, equality of the **cap payoff
coordinate** is enough.  The simplex component of a tail state is ignored by
`IsQuittingNashBellmanEdge` and can be chosen to match the adjacent root.
Equality of complete profiles or terminal laws is stronger than the capacity
interface needs.  Source-faithful recursive use, however, additionally needs
an actual child profile/law chronology attached to `b_child`.

The current regeneration supplies exactly the latter source datum:

- `FinFourFullReplacementSourceRegeneration.next` is a complete
  same-residual child source;
- `next_semantic_eq_cluster` identifies its full semantic pair with the
  selected full-replacement cluster; and
- `chronology_profile_eq` preserves the literal replacement endpoint profile
  subsequence.

It does not supply (1).  The profiles in the chronology merely converge to
the child point.  The roots at rank `n` form an exact cap--Nash stack over the
rank-`n` actual profile; they are not a single finite path whose endpoint is
the limiting child cap, and no endpoint is the old parent cap.

This is not a presentational omission.  The potential inequality applies to
a genuine path with equal adjacent states.  Convergence of both sides to a
common cap cannot be substituted without an upper-semicontinuity theorem for
the capacity, and no such theorem holds for a general compact closed-edge
relation.

## 2. Exact Fin4 same-debt best-response seam with no Nash--Bellman bridge

Let the player set be `Fin 4`.  Give every player payoff `-1` at every
nonempty terminal quitter set:

\[
 r(S)_i=-1\qquad(S\ne\varnothing,\ i\in\operatorname{Fin}4). \tag{2}
\]

Nonabsorption has the usual terminal payoff zero.  Fix a mover `m`.

### 2.1 Two actual profiles

At date zero, let every player Quit independently with probability `1/4` and,
conditional on no one quitting, let everyone Continue forever.  Call this
profile `P`.

Let `Q` be the full replacement of the mover's complete strategy by Never;
the three outsiders still Quit at date zero with probability `1/4` and then
Continue forever.  Thus `P` and `Q` differ in exactly one player's behavioral
strategy.

Against either profile, Never is a best response.  Quitting only turns a
no-opponent-exit path, whose payoff is zero, into terminal payoff `-1`.
Therefore the behavioral cap is minus the probability that at least one
opponent exits.

For `P`, every player has opponent-Continue probability `(3/4)^3=27/64`.
Hence

\[
 U_i(P)=-\left(1-(3/4)^4\right)=-175/256,
 \qquad B_i(P)=-\left(1-(3/4)^3\right)=-37/64=-148/256,
\]

and

\[
 d_i(P)=27/256,
 \qquad D(P)=4(27/256)=27/64.                              \tag{3}
\]

For `Q`, joint Continue probability is `(3/4)^3=27/64`, so every prescribed
payoff is `-37/64`.  The mover's opponents have not changed, hence

\[
 B_m(Q)=-37/64,qquad d_m(Q)=0.                            \tag{4}
\]

Each outsider sees the mover Continue surely and the two other outsiders
Continue with probability `(3/4)^2=9/16`.  Thus

\[
 B_i(Q)=-\left(1-9/16\right)=-7/16,
 \qquad d_i(Q)=(-7/16)-(-37/64)=9/64                       \tag{5}
\]

for `i != m`.  Consequently

\[
 D(Q)=3(9/64)=27/64=D(P).                                  \tag{6}
\]

This is the literal full-replacement ledger: the mover's debt `27/256` is
killed exactly and each of three nonmovers receives `9/256`.

The response information is stronger than the existing common-response
compiler.  Never is an **exact attained common best response** at both `P`
and `Q` for every nonmover, and it computes the cap displacement exactly.
The mover's cap is unchanged exactly.  Nevertheless there is no exact
Nash--Bellman bridge.

### 2.2 Classification of exact roots

Let `v` be any continuation vector with

\[
 -1<v_i\le 0\quad\text{for every }i.                       \tag{7}
\]

At a product root `x`, write

\[
 c_{-i}=\prod_{j\ne i}(1-x_j).
\]

Player `i`'s Quit endpoint is `-1`.  Its Continue endpoint is

\[
 -1+(1+v_i)c_{-i},
\]

because continuation `v_i` is reached only if every opponent Continues.
The Quit-minus-Continue slope is therefore

\[
 -(1+v_i)c_{-i}\le0.                                      \tag{8}
\]

Under (7), if `x_i>0`, exact Nash complementarity forces `c_(-i)=0`; hence
some other player Quits surely.  Apply the same argument to that sure quitter:
there must be a second sure quitter.  It follows that every exact root is of
one of two types:

- all players Continue, in which case `F_x(v)=v`; or
- at least two players Quit surely, in which case absorption is certain and
  `F_x(v)=(-1,-1,-1,-1)`.

At the constant tail `(-1,-1,-1,-1)`, every root again has successor payoff
`(-1,-1,-1,-1)`.  Induction on the length of a finite exact block proves:

> Starting from any tail satisfying (7), every outward exact Nash--Bellman
> value is either the original tail itself or the constant vector `-1`.

Both cap vectors in (3)--(5) satisfy (7), and they are distinct.  Hence there
is no finite exact Nash--Bellman block from `B(P)` to `B(Q)` and none from
`B(Q)` to `B(P)`.

The example lies in the canonical reward cube.  It is also
punishment-floor admissible: the punishment value is `-1`, since opponents
can force an immediate terminal outcome and every terminal reward equals
`-1`.

The global semantic debt minimum of this game is zero (for example at
all-Never, or at a sure collision).  Thus the example establishes the sharp
logical boundary:

> Actuality + one-player exact best-response replacement + equal positive
> total debt + exact common cap responses do not imply endpoint-matched exact
> Nash--Bellman reachability.  Any theorem for the renewable Fin4 source must
> use additional positive **global-minimum** structure.

## 3. Why the three proposed adapters fail

### 3.1 Common cap responses

`FullReplacementCluster.nonempty_commonPureTimeResponseCompiler` selects,
separately for every nonmover, a pure-time response whose regret tends to zero
at both sides of the horizontal seam.  Its theorem
`capDifference_sub_responseDifference_tendsto_zero` identifies that
coordinate's cap displacement asymptotically.

This is a coordinatewise horizontal identity.  It supplies neither

\[
 v_{\rm current}=F_x(v_{\rm tail})
\]

for one common product root `x`, nor exact Nash complementarity of that root.
The Fin4 example in Section 2 has zero regret and exact response attainment on
both sides, so strengthening `tends to zero` to `equals zero` still does not
produce the missing block.

There is a second, independent splice issue.  The checked
`exists_terminalSemantic_commonWitness_noncompositionality` shows that the
same terminal semantic pair, the same first-stage joint survival, and a common
exact pure-time witness can coexist with different deleted clocks and
different values after one common splice.  Thus a response witness is not a
chronological state identifier.

### 3.2 Lower-bound constrained roots

`exists_quittingLowerBoundConstrainedRoot` and
`exists_actual_quittingLowerBoundConstrainedPrefix` give exact equilibrium
only in the restricted boxes `[lower_i,1]`.  The checked identity

```text
constrainedRootCoordinateNashDefect_eq_normalWork
```

says that the unrestricted coordinate Nash defect is

\[
 lower_i\max\{-\Delta_i,0\}.                               \tag{9}
\]

Consequently:

> If `lower_i>0` and the endpoint difference `Delta_i<0`, a lower-bound
> constrained root is not an exact unrestricted Nash root.

Indeed `constrainedRoot_quitProbability_eq_lower_of_gap_neg` makes the floor
bind, (9) is strictly positive, and
`isZeroQuittingRootNash_iff_coordinateNashDefect_eq_zero` contradicts exact
Nash.  Equivalently,
`lowerFaceRemoval_payoffGain_eq_normalWork` displays the profitable removal
of that forced Quit mass.

If all normal work vanishes, the constrained root may be unrestricted exact,
but then the constraint has not supplied a positively paid reset against a
Continue-preferred coordinate.  It also leaves the Bellman current value
determined by the chosen root rather than hitting the prescribed parent cap.

### 3.3 Arbitrary-endpoint chains and finite reset blocks

`exists_finiteEndpointExactQuittingNashBellmanChain` starts from an arbitrary
bounded terminal payoff and iterates exact predecessors for any chosen finite
length.  This gives literal equality at the **terminal** endpoint.  It does
not prescribe the initial value of the chain and does not realize that value
as an actual terminal-semantic source.

The Section 2 example proves that this is not a missing selection lemma: for
the displayed actual cap endpoints, no choice of cutoff or exact predecessor
selection can hit the other endpoint.

The zero-length factory and all-Continue self-tail give an exact endpoint
match but zero charge.  More generally, a positive-charge exact self-return
would already be a positive admissible cycle.  The checked theorem
`quittingGame_exists_uniformPayoff_of_positive_admissible_cycle` consumes it
directly; in a finite-capacity branch it is impossible.  Thus a charged
"reset loop" is not a harmless seam: if it exists, it closes the branch.

The finite stopping-law splice theorem does not change this conclusion.
`exists_finiteSpliceCutoffs_mixtureNash_markedEvent_of_capTight` transports an
already supplied terminal approximate-Nash certificate while retaining a
marked law event.  Its own statement explicitly produces no rowwise
Nash--Bellman roots and assumes the uncapped Nash errors already tend to zero.

Finally, preserving the literal positive actual row cannot work.  For a
`QuittingLiteralPositiveActualRowPacket`, the checked declarations

- `not_exists_literalNashBellmanEmbedding`, and
- `gain_le_nashError_of_literal_root_tail`

show respectively that no exact edge preserves its source payoff, actual
root, and shifted-tail payoff, and that an approximate repair on that fixed
root--tail fiber pays Nash error at least the retained actual gain.  A viable
repair must change the root or the tail, which returns to the target-hitting
problem above.

## 4. Compactness boundary: bounded-length near-returns would already close

There is one useful positive compactness statement.

### Proposition (bounded-length positive near-return compiler)

Let `K` be a compact payoff box.  Suppose `B_n` are exact Nash--Bellman blocks
in `K`, their lengths are bounded by one fixed `L`, both endpoint payoff
vectors tend to the same `v`, and their absorption charges are bounded below
by one `kappa>0`.  Then there is a positive-charge exact Nash--Bellman cycle at
`v`.

**Proof.**  Pass to a subsequence of one fixed length.  Compactness gives
convergence of every intermediate payoff and root.  The exact edge graph is
closed by `isClosed_quittingNashBellmanEdgeGraph`, so every limiting row is
exact.  Continuity of root absorption preserves the lower charge bound.  The
two limiting endpoints are both `v`, giving the claimed cycle.  The unused
simplex coordinate at the terminal state can be chosen to match the first
root.  Repeating the word gives unbounded finite charge; in the
punishment-floor relation the checked positive-cycle compiler gives a uniform
payoff directly.  QED.

Therefore, under finite exact-block capacity, any positive-charge sequence
whose endpoints coalesce must escape this proposition by unbounded length and
diffuse charge.  The same conclusion follows under no uniform payoff when the
blocks and their limit are punishment-floor admissible, by the checked
positive-cycle consumer.  Compactness of individual edges cannot compress
such a sequence into a finite endpoint-matched block.

The checked fixed-label reprojection regression exhibits the strategic
version of the same boundary:
`QuittingReprojectionFixedLabelLimit.not_isZeroQuittingRootNash` says that its
positive-charge limiting root is quantitatively outside the exact cap--Nash
correspondence.  A separate Nashification step is genuinely required.

## 5. The existing regenerated causal stacks have vanishing charge

The source-faithful chronology contains

```text
continueProduct_tendsto_one :
  quittingCapNashStackContinueProduct (roots n) -> 1.
```

Positive global minimum debt makes every row's Continue mass positive.  The
checked logarithmic estimate

```text
capNashStack_absorptionSum_le_neg_log_continueProduct
```

therefore gives

\[
 A_n:=\sum_t a(x_{n,t})
 \le -\log c_n\longrightarrow0.                            \tag{10}
\]

For every coordinate,
`quitProbability_le_quittingRootAbsorptionMass` gives
`x_(n,t,i)<=a(x_(n,t))`.  Since there are four players,

\[
 H_n:=\sum_{t,i}x_{n,t,i}\le4A_n\longrightarrow0.          \tag{11}
\]

Thus the exact stacks already present in
`QuittingSourceFaithfulMinimumCausalChronology` are asymptotically
zero-charge even for the stronger marginal-hazard capacity.  They preserve
atom provenance through arbitrarily deep prefix access; they cannot provide
the fixed `kappa` transition required by the finite-capacity rank.

This is stronger than saying merely that their endpoints are not literally
matched: the displayed exact chronology has no macroscopic charge to spend.

## 6. Strongest surviving positive-minimum port

The exact source-regeneration half is complete.  For a recursive
full-replacement child, the only missing mathematical object is now the
following cap port in one declared orientation.

> **Endpoint-matched charged regeneration packet.**  Supply a finite exact
> punishment-floor Nash--Bellman block whose relation source is the parent
> history cap, whose relation target is exactly
> `regeneration.next.point.1.2`, and whose charge is at least one game-wide
> `kappa>0`.  Attach the already checked child source and chronology at that
> target cap.

If the charged escape-return construction naturally has the reverse
orientation, the packet must state and use that reverse orientation; no
inverse-edge principle is available.

Together with a uniform debt escape-return gap, this packet would make the
ceiling potential rank from the preceding note terminate recursion.  If the
same endpoint is returned with positive charge, the positive-cycle consumer
closes immediately instead.

Section 2 proves that the packet cannot be derived from the following data
alone:

- actual source and target profiles;
- one-player exact best-response replacement;
- equality of total semantic debt;
- exact cap invariance for the mover;
- exact common best responses for every nonmover; or
- boundedness and punishment-floor admissibility.

What remains genuinely open is whether **positive global-minimum provenance,
the Fin4 tangent identities, and the retained atom** force either this exact
packet or an already solved-game disjunct.  No current declaration supplies
that implication.

An approximate alternative is logically separate.  If successive positive
exact blocks can be selected with summable cap-vector seams, they concatenate
to the approximate spine consumed by the existing persistent-label theorems.
The common-response compiler does not itself bound those cap-vector seams,
and the present source-faithful causal stacks have charge tending to zero by
(11).

## 7. Declaration-level handoff

The following wrappers are mathematically justified and genuinely missing:

1. `QuittingSourceFaithfulMinimumCausalChronology.marginalHazardSum_tendsto_zero`:
   derive (10)--(11) from `continueProduct_tendsto_one`, positive debt infimum,
   the logarithmic absorption bound, and the finite-player factor.
2. `not_isZeroQuittingRootNash_of_lower_pos_of_endpointDifference_neg`:
   package the constrained-root normal-work obstruction from Section 3.2.
3. `exists_positive_admissible_cycle_of_boundedLength_exactBlocks_tendsto_sameEndpoint`:
   the fixed-length compactness proposition in Section 4.
4. A small checked regression formalizing Section 2, preferably with fields
   for the two actual profiles, their exact same total debt, the literal mover
   replacement and exact common Never responses, followed by
   `not_exists_finiteExactNashBellmanBlock_between_caps` in both orientations.

The actual positive-minimum theorem must remain conditional on an
`EndpointMatchedChargedRegenerationPacket` or prove a game-specific producer
for that packet.  No target-hitting theorem should be stated from the current
common-response or constrained-root interfaces.

## 8. One next obligation

Use the extra global-minimum identities, not merely equality of total debt,
to prove or refute this disjunction at one actual renewable endpoint:

> either the game already has a uniform-equilibrium payoff, or there is a
> finite exact Nash--Bellman block of fixed positive charge whose terminal cap
> is the parent history cap and whose current cap is exactly the regenerated
> child's cap.

The Section 2 table is the first falsification test: any proposed proof step
which uses only one-player full replacement, common debt, or common responses
must fail on it.  The proof must identify precisely where positive
global-minimum provenance excludes that table.

## 9. Narrow source audit

Files/declarations inspected for this note:

- `math/SOURCES.md`, `math/GOAL.md`, and the relevant rows of
  `docs/TOOLKIT.md`;
- `math/exports/UNBOUNDED_FINITE_HAZARD_CAPACITY_COMPILER.md`;
- `Research/Quitting/FinFourProducerAtlas/CanonicalPairFullReplacementSourceRegeneration.lean`;
- `Research/Quitting/FinFourProducerAtlas/CanonicalPairEndpointSourceRegeneration.lean`;
- `Research/Quitting/SourceFaithfulMinimumLawCausalization.lean`;
- `Research/Quitting/StoppingLawMinimumFiberCommonResponseCompiler.lean`;
- `Research/Quitting/ConstrainedRootExistence.lean`;
- `Research/Quitting/ConstrainedRootNormalWork.lean`;
- `UniformEquilibrium/Quitting/Bellman/Finite/NashBellmanSpine.lean`;
- `UniformEquilibrium/Quitting/Bellman/Finite/EndpointNashBellmanFactory.lean`;
- `UniformEquilibrium/Quitting/Bellman/Finite/PunishmentFloorAdmissibleChargedRelation.lean`;
- `UniformEquilibrium/Quitting/Bellman/Finite/PositiveAdmissibleCycle.lean`;
- `UniformEquilibrium/Diagnostics/Quitting/TerminalCapNashChronology.lean`;
- `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticLiteralSourceReturnNoGo.lean`;
- `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticCommonWitnessNoncompositionality.lean`;
- `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticResetReprojectionFixedLabel.lean`; and
- `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/TerminalSemanticStoppingLawFiniteSpliceNashification.lean`.

No Lean theorem, export, feedback file, shared index, or author-owned note was
edited.
