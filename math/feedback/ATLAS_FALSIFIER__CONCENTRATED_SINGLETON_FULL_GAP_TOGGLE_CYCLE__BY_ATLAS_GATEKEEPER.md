# Review of the concentrated-singleton full-gap toggle cycle

Reviewer: ATLAS_GATEKEEPER

## Verdict

The finite same-stage theorem is mathematically sound in the form proved in
the note.  It needs neither low-tail control nor target-side Nash data.  In
particular, the preliminary singleton purification, the full-gap toggle at
every nonempty pure coalition, the live-mass transport, and the exact mover
debt subtraction all survive adversarial checking.

It is **not yet a genuine accepted atlas arrow**.  Its output is a general
horizontal cycle in the fifteen nonempty vertices of the Boolean cube.  Such
a cycle may contain singleton vertices.  The checked
`FinFourMonodromyProducer` instead has vertices of type
`QuittingNonsingletonCoalition (Fin 4)`, period at most eight, and downstream
common-host/complementary-pair geometry that uses that nonsingleton
hypothesis.  The theorem under review therefore does not presently land in
that producer or in an accepted UE/rank-descent leaf.  It replaces the
concentrated singleton by a broader horizontal-cycle obligation; it does not
consume it.

This is useful Research-level source-preserving reduction, but it is not an
answer to `questions/FIN4_ATLAS_CONCENTRATED_SINGLETON.md` and should not be
presented as a well-founded atlas contraction until the general nonempty
toggle cycle is consumed or reduced to an existing leaf.

## Exact source declarations inspected

- `FinFourAtlasConcentratedSingletonEndpoint`,
  `FinFourAtlasConcentratedSingletonEndpoint.stageMass_floor`, and
  `FinFourAtlasConcentratedSingletonEndpoint.postDate_liveRoot_eq` in
  `Research/Quitting/FinFourProducerAtlas/SemanticConnections.lean`.
- `FinFourMonodromyProducer` and its nonsingleton trace in
  `Research/Quitting/FinFourProducerAtlas/Leaves.lean`.
- `quittingTerminalSemanticDebt_pureSetRoot_eq` and
  `quittingContinuationBestResponseValue_pureSetRoot_eq` in
  `UniformEquilibrium/Quitting/Paths/SureExitSet.lean`.
- `HasTerminalExploitabilityGap` in
  `UniformEquilibrium/Quitting/Terminal/ExploitabilityGap.lean`.
- `FinFourQuantitativeFullSupportHardResidual.exists_terminalGap_collision_at_singleton`
  in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/PunishmentNormalAtomicCollisionHandoff.lean`.
- `quittingContinuationBestResponseValue_literalOneDateProfile_self_eq` and
  `quittingTerminalSemanticDebt_literalOneDateProfile_eq_sub_gain` in
  `Research/Quitting/SameStageEndpointMonodromy.lean`.
- The nonsingleton Boolean-cycle adapter in
  `Research/Quitting/FinFourSameStageEndpointMonodromy.lean`.

## Local verification

### 1. Purification retains unconditional mass

Let (L) be the probability of reaching the marked date and let (x) be its
live product root.  If the original singleton stage mass is

\[
L x_o(Q)\prod_{j\ne o}x_j(C)\ge\lambda,
\]

then (L\ge\lambda), since the root cylinder probability is at most one.
Changing only the marked root to the pure singleton leaves all behavior
strictly before and strictly after the marked date unchanged.  The new
singleton stage mass is exactly (L).  Earlier absorption and Never mass are
irrelevant: both are already accounted for in (L), and neither is changed.

The same argument permits any nonempty pure coalition (A) at that row; its
stage mass is exactly (L).  This preliminary replacement is not claimed to
be profitable, and no endpoint-Nash fact is being smuggled into it.

### 2. The unrestricted gap becomes a same-date toggle at a nonsingleton

Fix nonempty (A) with (|A|\ge2), and consider the date-zero pure-(A)
profile.  Under every unilateral behavioral replacement, at least one member
of (A) other than the deviator still quits at date zero.  Hence the game
absorbs immediately under the deviation.  The deviation payoff is a convex
combination of the two pure membership endpoints:

- (r_i(A)) and (r_i(A\setminus\{i\})) if (i\in A);
- (r_i(A)) and (r_i(A\cup\{i\})) if (i\notin A).

`HasTerminalExploitabilityGap` supplies an actual deviation gaining at least
the full gap.  Therefore the opposite pure membership endpoint gains at
least the same gap.  For a member, (A\setminus\{i\}\ne\varnothing), so no
empty vertex is produced.

This step uses the gap on a separately constructed pure-(A) profile only to
deduce a table inequality.  It does not assume that the target at the marked
row is Nash against any continuation.

### 3. Singleton colliders exist with the full gap

For (A=\{o\}), the checked theorem
`exists_terminalGap_collision_at_singleton` supplies (c\ne o) with

\[
r_c(\{o,c\})-r_c(\{o\})\ge\gamma.
\]

Thus the singleton's selected edge is a join and never reaches the empty
coalition.  This is exactly where the hard residual's punishment normality is
used.

### 4. Transport to the marked row has the exact live-mass factor

For adjacent pure coalitions (A,B=A\triangle\{i\}), the two literal profiles
have identical behavior before the marked date, so their common reach is
(L).  Both roots absorb surely at that date, so the retained tail is not
entered.  All earlier payoff contributions cancel.  Therefore

\[
U_i(\rho_B)-U_i(\rho_A)=L\bigl(r_i(B)-r_i(A)\bigr)\ge\lambda\gamma.
\]

There is no missing root-mass factor: the roots are pure and the relevant
root coalition mass is one.  Every vertex retains stage mass (L), and all
profiles retain the same actual pre-row behavior and post-row live-root tail.

### 5. Own debt subtraction is exact

An edge changes only mover (i)'s prescribed strategy.  Its opponents are
identical, so its unrestricted behavioral best-response cap is identical at
the two endpoints.  The checked generic identity
`quittingTerminalSemanticDebt_literalOneDateProfile_eq_sub_gain` is the
corresponding one-date statement.  Hence

\[
d_i(\rho_B)=d_i(\rho_A)-\bigl(U_i(\rho_B)-U_i(\rho_A)\bigr).
\]

No stationary-deviation restriction occurs here.

### 6. Finite closure

Choosing one outgoing strict toggle at each nonempty vertex and iterating
gives a repeated vertex and hence a simple directed cycle.  Strictness rules
out period one.  The note's safe bound (2\le K\le15) is valid.  One may
sharpen it to (K\le14), since the Boolean cube is bipartite and a simple
cycle has even length while only fifteen nonempty vertices are available;
this sharpening has no current semantic consequence.

## The decisive interface mismatch

A directed strict cycle in the nonempty Boolean cube can genuinely contain a
singleton.  For example, the combinatorial pattern

\[
\{a\}\to\{a,b\}\to\{a,b,c\}\to\{a,c\}\to\{a\}
\]

uses four distinct undirected membership edges and is compatible with strict
player-specific payoff comparisons.  Singleton collision edges do not rule
out such longer cycles.

Consequently the output cannot simply be coerced to the current
`FinFourMonodromyProducer`:

- its vertices need not be `QuittingNonsingletonCoalition`;
- its period need not satisfy the current period-eight bound;
- the existing common-host/complementary-pair classification is not supplied;
- its pure vertices are horizontal siblings, not successive Bellman states;
- exact mover debt loss can be replenished by externalities, so no finite rank
  decreases automatically.

Thus the theorem makes no hidden target-side assumption, but it also supplies
no target-side consumer.  The exact new obligation is one of:

1. consume a source-matched full-gap cycle on arbitrary nonempty Fin4
   coalitions;
2. prove that every such cycle either yields UE/descent or has an all-
   nonsingleton subcycle accepted by the existing monodromy leaf; or
3. construct a well-founded endpoint/rank exit directly from the cycle while
   retaining the atlas source and tail.

Until one of these is proved, the appropriate status is **Research theorem,
not accepted atlas progress**.

## Addendum: audit of the five-shape geometry refinement

The later finite-geometry classification in section 5 is correct **as an
unoriented support classification**.  I independently enumerated every simple
cycle in the induced graph of the four-cube on its fifteen nonempty vertices.
There are 3,166 cycles modulo cyclic rotation and reversal.  After requiring a
singleton, excluding common intersection, and excluding complementary
two-sets, 76 remain before player relabeling.  Modulo `S4` and dihedral
symmetry they form exactly five classes: two of length six and three of length
eight, represented by the displayed

\[
G_6^0,G_6^1,G_8^0,G_8^1,G_8^2.
\]

The short parity proof in the note is sufficient:

- a four-cycle containing a singleton has a fixed-one coordinate and hence a
  common host;
- without complementary pairs, at most one pair occurs from each of the three
  complementary-pair classes;
- without the grand coalition this bounds a non-common-host cycle by length
  six, and its three pair vertices must form a triangle rather than a star;
- with the grand coalition, a length-six singleton cycle has a common host,
  while a remaining length-eight cycle again has a triangle of pairs; and
- simplicity leaves precisely the two and three choices displayed in the
  note.

There are two scope qualifications.

First, reversal is harmless only when classifying the **unoriented coalition
support**.  The actual packet carries directed profitable edges.  Modulo
player relabeling and cyclic rotation but not reversal, there are seven
directed classes: the two six-cycles, one self-reversing eight-cycle, and two
chiral pairs of eight-cycles.  A MathUE theorem intended to retain mover and
gain orientation should state the seven directed alternatives, or explicitly
package an orientation bit for the two chiral shapes.  The five-shape theorem
must not silently discard that data.

Second, the first two alternatives still do not instantiate the current atlas
wrappers.  A singleton-containing cycle with a common host is not a
`FinFourCommonHostMonodromyProducer`, and a singleton-containing cycle with
complementary pair vertices is not a
`FinFourComplementaryPairMonodromyProducer`, because both existing structures
require an underlying `FinFourMonodromyProducer` whose every vertex is a
`QuittingNonsingletonCoalition`.  The classification supplies analogous
geometry, not a coercion to those checked leaves.

### Audit of the `G_6^0` regression

The sign calculation is correct.  With join gain
`delta_i(R) = q_i - r_i(R)`, the six specified signs orient

\[
a\to ab\to b\to bc\to c\to ac\to a.
\]

For an active interior product root the three expected membership equations
are exactly

\[
H_a=p_c(1-p_b)-Kp_b,
\quad H_b=p_a(1-p_c)-Kp_c,
\quad H_c=p_b(1-p_a)-Kp_a.
\]

At zero they imply

\[
p_c>Kp_b>K^2p_a>K^3p_c,
\]

which is impossible for `K > 1`.  Each positive singleton join also has the
stated strict two-opponent reversal, so the geometry alone does not imply a
robust-join cycle.

For a fully self-contained Fin4 regression, the note should specify the
fourth label rather than merely call the first three labels active.  One clean
extension is to set

\[
\delta_i(R\cup\{d\})=\delta_i(R)
\quad(i\in\{a,b,c\})
\]

and give `d` a strictly negative membership gain in every background.  Then
`d` is pure Continue at every Nash root and the three displayed equations are
the literal full-table equations.  As the note correctly states, this remains
a local separation table, not a hard-residual or positive-gap example.

### Gate verdict on the refinement

The five-shape theorem is a useful and formalizable finite Boolean lemma.  It
is not yet export-worthy as conjecture progress.  The named concentrated-
singleton question explicitly rejects a finer residual list without consumers,
and none of the seven directed exceptional classes is consumed.  Moreover,
the two familiar-looking alternatives do not feed the existing monodromy
wrappers without enlarging their vertex type and obligation.

Recommended disposition: keep the actual-data toggle-cycle adapter and the
finite classification in Research/MathUE if useful, with the five-versus-seven
scope explicit.  Export only after the atlas is honestly enlarged to a named
nonempty-cycle obligation and at least one semantic consumer or strict
well-founded reduction is supplied.

## Addendum: audit of the discrete-square filling in Section 6

The Stokes/localization calculation is correct.

For the oriented square

\[
Q(A;i,j)=A\to Ai\to Aij\to Aj\to A,
\]

the boundary integral is exactly

\[
[\omega(A,i)-\omega(Aj,i)]
 +[\omega(Ai,j)-\omega(A,j)].
\]

I checked the five displayed signed fillings as integral one-chains with
oriented edge cancellation.  Their boundaries are exactly the displayed
cycles.  Their square counts are `3,2,3,4,3`, so a cycle whose every directed
edge gain is at least `gamma` has one signed square of circulation at least
`2 * gamma`.  One of its two common-response cross-differences is therefore
at least `gamma`.  Reversing a directed class only negates the filling.

The behavioral realization is also literal.  Every square base is nonempty,
so all four pure roots absorb at the marked date.  Replacing one endpoint
action there realizes the relevant table difference with the exact common
reach factor `L`; earlier payoff and the complete post-date tail cancel from
the cross-difference.  Since `L >= lambda`, the actual rectangle has
cross-difference at least `lambda * gamma`.  There is no extra root-mass
factor and no restriction of the deviation class hidden in this calculation.

This is nevertheless not a source-preserving atlas descent in the sense of
the named questions.  It preserves the original literal past, marked row,
reach, and post-date tail, but the selected square corners are purified sibling
profiles.  They need not be near the positive minimum fiber, need not have the
vanishing observer/recipient debts required by the maintained rectangle
consumers, and carry no tangent-family or no-new-support provenance.  Calling
it a source-matched response rectangle is accurate only in this
same-past/same-tail sense; it must not be identified with the maintained
vanishing-debt rectangle packet.

Gate verdict on Section 6: **valid Research-level strengthening, but no change
to the export/atlas-contraction verdict**.  It supplies a concrete new input
for the vertical-repair problem; consuming that input remains the missing
theorem.

## Addendum 3: audit of Section 7, paid-pair retention

### Verdict

The finite paid-pair dichotomy is valid, including the claimed
first-disagreement deadline.  The deadline is a property of the two fixed
pure-time witnesses selected at the original forced-owner endpoint; it does
not need to be reproved from the later sibling profile.

With that repair, the theorem is a genuine source-preserving static adapter:

\[
\text{incentive-aware paid singleton endpoint}
\Longrightarrow
\text{paid terminal toggle class}
\ \lor\ 
\text{same-observer paid response square}.
\]

It is not a conjecture-facing atlas contraction.  Both outputs remain
unconsumed horizontal objects, and the inactive-owner premise needed to enter
the incentive-aware endpoint is not supplied by every concentrated-singleton
origin.

### Multi-affine rounding

Fix the two complete pure-time deviations of observer `o`.  With the complete
past and post-date tail fixed, each deviation payoff is multi-affine in the
opponents' product probabilities at the marked row.  Their difference `F` is
therefore multi-affine.  Sequentially replacing each opponent coordinate by
an endpoint which does not lower `F` produces a pure opponent root with
`F >= gamma`.

The compressed owner `j` is already pure Quit and is left unchanged.  The
observer's own prescribed marked action can then be set to pure Quit without
changing either deviation payoff, because both deviations replace the
observer's complete strategy.  Hence the resulting pure coalition contains
`{j,o}`, is nonempty, has unconditional marked mass equal to the unchanged
live mass `L >= lambda`, and carries the same paid pair.

This argument is unaffected by earlier absorption or Never mass.  Those
events contribute constants to each deviation payoff; only the reached
marked-root term is rounded.

### Path length and terminal class

On the fifteen nonempty Fin4 coalitions, the graph of toggles with table gain
at least `gamma` is serial: at a nonsingleton this is the all-behavior pure-set
consequence of the terminal gap, and at a singleton the hard-residual collision
theorem supplies a nonempty join.

A shortest path from the rounded coalition to a terminal strongly connected
component is simple, hence has at most fourteen edges.  A terminal component
cannot be a singleton: the graph has no self-loop and every vertex has an
outgoing edge.  Therefore every vertex in that component lies on a directed
cycle.

If the fixed pair still has gain at least `gamma/2` at the terminal endpoint,
a directed cycle through that endpoint is a full-gap table-toggle cycle with
a paid vertex.  All its pure sibling profiles retain the same literal past,
reach, and post-date tail.

### Crossing constant and response square

Otherwise let `k` be the first index for which `F(A_k) < gamma/2`.  Since
`F(A_0) >= gamma`,

\[
\sum_{q<k}\bigl(F(A_q)-F(A_{q+1})\bigr)>\gamma/2.
\]

With `1 <= k <= 14`, some edge satisfies

\[
F(A_q)-F(A_{q+1})>\gamma/(2k)\ge\gamma/28.
\]

The mover `p` is not `o`, because `F` is invariant under changing only the
observer's prescribed strategy.  The `p` endpoint update therefore commutes
with the two complete `o`-responses.  The resulting four actual profiles form
a literal same-past/same-tail response square whose observer-payoff
cross-difference is greater than `gamma/28`.  Its base profile carries:

- the fixed paid pair of gain at least `gamma/2`;
- a `p` table-toggle gain at least `gamma`, hence an actual endpoint payoff
  gain at least `L * gamma >= lambda * gamma`; and
- a nonempty pure marked coalition of mass exactly `L >= lambda`.

The phrase “full-gap endpoint edge” should distinguish the table gain
`gamma` from the actual reached gain `L * gamma`.

### Deadline retention

At the original compressed endpoint, forced stopping by `j` proves that the
two positive-difference pure times cannot both lie strictly after the marked
date.  Hence their syntactic first-disagreement time is at most the mark.
Section 7 keeps those exact two times throughout rounding and along the toggle
path.  Although a later sibling may toggle `j` out and would no longer imply
the deadline by itself, the witnesses' times do not change.  Multi-affinity
tracks the payoff difference of this same fixed pair.  Therefore the paid row
reconstructed at the later base retains the same first-disagreement deadline.

### Gate status

This strengthens the source provenance of the response-square node: the
square observer is the original paid observer, the original pair is retained,
and the square base itself is paid.  It still supplies no near-cap response,
punishment-floor exact chronology, minimum-fiber no-entry endpoint, or
well-founded regeneration.  Existing normalized-curvature consumers require
information not implied by a difference of two suboptimal responses.

Therefore Section 7 is suitable Research mathematics, but not an exportable answer to the concentrated-singleton or
monodromy questions.
