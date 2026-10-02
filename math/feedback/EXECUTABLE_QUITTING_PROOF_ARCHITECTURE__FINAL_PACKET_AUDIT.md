# Final falsification audit of the executable proof-architecture packet

Reviewer: `ARCHITECTURE_PACKET_AUDIT`

Target:
`notes/CODEX_ROOT__EXECUTABLE_QUITTING_PROOF_ARCHITECTURE_PACKET.md`

## Verdict

**Repair required before export.**  The packet preserves the sound central
mathematics of the three audited source notes, and I found no counterexample
to its tight-fusion theorem, two-sorted trace/control grammar, unrestricted
deviation semantics, or the four obstruction mechanisms.  After the generic
architecture problem is separated from the Fin4 instantiation problem, this
is the right scope for a complete answer to the generic problem.

The current exact file is not yet final.  Consolidation introduced four
mathematical/proof defects and several equation/scope inconsistencies.  All
are local and have clear repairs; none requires a new idea.  I recommend a
second exact-packet review after they are corrected, because the packet makes
an unrestricted-behavioral-strategy claim.

## Required repairs

### 1. The triangular decoder proof assumes its limiting decoder exists

Section 4 says that `D` is “the limit of the limiting columns” and immediately
uses it.  Existence of that limit is part of the theorem and must be proved.

Let

```text
delta_N = sup_m sum_{n >= N} c_{m,n}.
```

For fixed `N < L`, the finite row-wise telescope gives

```text
d(M_{m,N}, M_{m,L}) <= delta_N.
```

Passing to the outer limit using fixed-column convergence gives

```text
d(M_N, M_L) <= delta_N.
```

Since `delta_N` tends to zero, the limiting columns are Cauchy and define
`D`.  Only then is the displayed three-term estimate for `d(D_m,D)` valid.
This step was present in the prior independent audit but was omitted from the
consolidated proof.

### 2. The rank-one example is ill-typed unless the player set is specialized

Section 8 writes `mu(0)` for `mu in S`, but the standing

```text
S = Delta(K)^I
```

is a profile space.  The expression is meaningful only for one stopping law,
not for a general multi-player profile.  State explicitly:

```text
Take the one-player case, so S = Delta(K).
```

The rest of the example then works literally.  Alternatively choose and name
one coordinate, but the one-player specialization is the cleaner theorem and
matches the source proof.

### 3. The maximal-root section incorrectly calls every prelimit output
all-Never

For `z > 0`, the unique maximal root is all Continue, so prefixing leaves the
displayed source `mu^z` behind one all-Continue date.  Player 2 still quits at
the shifted date with probability `z`.  The output is not all-Never.

The correct sentence is:

```text
For z > 0 the output is the delayed source profile; as z tends to zero,
these output traces converge to all-Never, where player 2's payoff and cap
are zero.
```

The limiting maximal-root output still has player 1 quit surely and gives
player 2 payoff and cap one.  Thus the nonclosedness and unit discrepancy are
unchanged.

### 4. The Late-limit formula needs a singleton-player convention

The standing player set is finite and nonempty, so it includes one-player
games.  Equations (5)--(6) use the minimum opponent stopping time and the first
opponent coalition, which are undefined when there is no opponent.

Either state those displayed formulas for `I \ {i}` nonempty and handle the
singleton case separately,

```text
V_i(n) = r_i({i}),   V_i(infinity) = 0,
```

or explicitly define the empty-opponent convention.  The late/Never split and
all later arguments remain valid.

## Equation and terminology corrections

### 5. Two suffix references point to the maximal-root equations

At the end of Section 10, “in (21) its unconditioned weight is only
`p -> 0`” is wrong: (21) is the cap vector in the maximal-root example.
This should refer to the approximating sources in (24), without suggesting
that the conditional target itself has weight `p`.

Boundary test 3 likewise says that (20) proves positive-reach continuity and
(21) proves zero-reach failure.  The correct references are:

- (23) for fixed-positive-reach continuity; and
- (24), together with the graph-closure calculation, for failure at zero
  reach.

### 6. The rank discrepancy is `l1` distance two, not TV distance two

The packet defines its main metric using full `l1`.  Later it explicitly
defines total variation as half `l1`.  Therefore the rank example has

```text
l1 distance = 2,
TV distance = 1.
```

Exact statement D currently calls it “total-variation distance (2)”.  Replace
this with “`l1` distance two (equivalently, total-variation distance one).”

### 7. The result and obstruction counts are inconsistent

The exact statement says “the following five results” but labels six items,
A through F.  They are two positive architecture results and four boundaries:
late-mass nonattainment, rank discontinuity, maximal-root nonclosedness, and
vanishing-reach suffixing.

The Adapter and consumer section later refers to “the two counterexamples.”
It should say “the four boundary examples,” or identify exactly which two it
means.  The Conjecture-facing change lists three universal shortcuts and
omits the rank/trace shortcut; either add it or say explicitly that rank is
treated as an internal trace/control boundary rather than one of that list.

### 8. Elementary varying root parameters should appear in the extraction

Part A permits varying finite product roots.  They lie in compact cubes, so no
new hypothesis is needed, but Section 2's proof should say that the diagonal
subsequence also makes every persistent varying finite prefix/root parameter
converge.  At present it mentions only law coordinates.  Section 6 contains
the corresponding argument for the enlarged grammar; copying the sentence
to the elementary proof makes Part A complete on its own.

## Export-surface repairs

### 9. The inline mathematics is not delimited as Markdown mathematics

The packet repeatedly uses text such as `(\mathsf S)`, `(\varepsilon)`, and
`(r_i(\varnothing)=0)` rather than `\(...\)`.  A renderer will display raw
LaTeX commands.  This is not a mathematical objection, but a final export
should restore inline math delimiters throughout.

### 10. The independent-review field is still a placeholder

The export must replace

```text
Independent reviews: to be inserted after final packet review.
```

with actual review links.  Because the packet explicitly establishes caps
against unrestricted behavioral deviations, the export policy requires two
independent reviews and an explicit falsification attempt.  This audit is one
such falsification attempt, conditional on the repairs above.

### 11. The generic and Fin4 questions must actually be separated

The packet is a complete answer to the generic architecture problem only
after that problem no longer conjunctively asks for the construction-specific
Fin4 instantiation.  The current text correctly treats Fin4 production as
open.  The maintained question must have the same boundary before export.

## Claims independently confirmed

Subject to the repairs above, the following core claims are valid.

### Unrestricted behavioral semantics

Before absorption there is only one live public history at each date.  A
behavioral hazard sequence therefore induces one stopping law on finite dates
plus Never, and the displayed survival-ratio hazards execute every such law.
Players' behavioral randomizations are independent in the standard quitting
game.

Against fixed opponents, any unilateral behavioral replacement has expected
payoff affine in its stopping law.  Its cap is exactly the supremum over all
finite deterministic stopping dates and Never.  Thus the packet does not
silently restrict deviations to stationary, finite-horizon, or bounded-clock
strategies.

The finite-deadline limit is genuinely distinct from Never when opponents may
all play Never: the former yields the deviator's singleton reward, while the
latter yields the standard zero nonabsorption payoff.  The split compact test
space records this correctly without declaring Late executable.

### Elementary tight fusion

Finite-coordinate plus Never-coordinate convergence and eventual finite-tail
tightness give total-variation convergence on the countable stopping-time
space.  The prefix, replacement, concatenation, and fixed-positive-reach
suffix estimates are correct.  Topological induction therefore reconstructs
actual limiting executions of every fixed elementary diagram.  Restriction
compatibility and one common execution sequence give one shared root
controller rather than a controller selected independently for every depth.

Total-variation convergence controls prescribed payoffs and the complete
behavioral caps.  Vanishing debt and one payoff limit therefore give an exact
terminal Nash profile, and the cited checked theorem gives the stated
uniform-equilibrium payoff under the standard zero nonabsorption convention.

### Closed selection and moving optimization

Ambient closedness of the witness domain retains feasibility, the compiler
modulus retains the actual output, the typed legal-edge theorem retains the
named operation, and closed ancestry retains provenance.  Closed graph alone
does not preserve a moving optimum; comparison transport is precisely the
extra condition used in the competitor argument.  A convergent nonzero error
gives only limiting approximate optimality at that error, as stated.

### Ranked control

Natural-rank induction is a valid pointwise consumer after one actual node has
been reconstructed.  It proves termination only along the dispatch-selected
chain.  The one-player rank-one example, once typed correctly, proves that
the selected child map need not commute with a compact limit.

The stronger trace-visible certificate is sufficient: stabilize the finite
tag and child rank, converge the compact witnesses, use the child's trace-safe
compiler to obtain an actual convergent child, then invoke closedness of the
complete tagged relation and recurse at the lower rank.

### Coherent diagonal

The union of increasing finite diagrams has countably many persistent
occurrences.  Diagonal compact extraction, followed by finite topological
induction in each diagram, gives compatible legal limiting executions.  The
decoder step is complete once repair 1 is inserted.  The theorem does not
assert a producer of its tight common execution sequence.

### Clock/tester example

The payoffs and caps are correct.  If the tester plays Never and the clock is
uniform on `n` finite dates, the payoff is `(-1,0)`, the clock cap is zero,
and the tester cap is `1/n`.  The semantic limit `U=(-1,0), B=(0,0)` is not
attained by an actual profile: clock payoff `-1` forces an almost-sure finite
clock with some positive atom, which the tester can hit.

The capacity identity

```text
Late mass <= Never error + sum of finite-coordinate errors
```

is exact.  With total finite budget one half, every actual recovery stays at
least one half away in the clock payoff.  This is a genuine noncompactness
boundary, not a positive-gap counterexample.

### Maximal exact-root example

For the rational table in (20), the cap is `(z,0)`.  Player 2 always strictly
prefers Continue at the cap root, hence `x_2=0`.  Player 1 then must Continue
for `z>0` and is indifferent at `z=0`.  The exact root sets in (22) and their
unique absorption maximizers are correct.

After repair 3, the outputs exhibit the claimed unit discontinuity.  At the
limit, every exact `epsilon`-maximal root has `x_1 >= 1-epsilon`, so the
approximate-maximality strengthening is also correct.  Its scope remains
same-source, absorption-objective, and exact-root.

### Vanishing-reach suffix example

The total-variation conditioning estimate (23) is valid.  At positive limiting
reach it forces the literal suffix.  At zero depth-one reach a one-player law
must be `delta_0`.  Conversely, the delayed and `p`-scaled construction (24)
produces every target law in the fibre over `delta_0`.  This proves the exact
graph-closure equality.

Protected finite prefixing, concatenation, and legal suffixing preserve zero
Never mass, so they cannot recover `delta_infinity` from `delta_0`.  The
one-player quitting table gives the stated conditional payoff/debt separation.
The self-loop at `delta_infinity` blocks only law-intrinsic strict ranks, not
external proof-relevant phase ranks.

## Source and novelty check

The cited declaration names and files resolve:

- `StoppingLaw.toScalarHazard` and
  `StoppingLaw.stoppingLaw_toScalarHazard`;
- `quittingRootSequenceHazardTerminalValue_eq_expect_stoppingLaw`;
- `quittingGame_isUniformEquilibriumPayoff_of_terminalNash_exact` and the
  all-error terminal selection theorem;
- `quittingTerminalSemanticPair_eq_of_opponentTight_lawLimit`; and
- the checked clock/tester nonattainment module.

The packet correctly distinguishes the checked underlying clock/tester
nonattainment from its new split-Late and summable-capacity packaging.  No
paper theorem is used.  The generic grammar, diagonal theorem, rank/trace
separation, maximal-root table, and exact suffix closure remain ordinary
mathematics proposed for formalization.

## Readiness after repair

After repairs 1--11 and actual separation of the generic question from the
Fin4 instantiation, I would accept the packet as a complete ordinary-
mathematics answer to the generic executable-architecture problem.

It should be exported with the following exact headline:

```text
A sufficient two-sorted executable architecture is proved for supplied tight
common execution data. Four exact examples show why tightness, trace-safe
rank, same-source maximal-root continuity, and positive-reach provenance
cannot be omitted. Producing the required adapters from the Fin4 residual
remains open.
```

That headline is both significant and honest.  It must not be shortened to
“a compact state for every quitting construction” or “Fin4 reconstruction is
solved.”

## Addendum: audit of the proposed universal adapter exclusion

I also inspected `meta/ADAPTERS_COMPLETE.md`, which proposes to strengthen the
packet with an acceptable-negative answer excluding `CW`, `SD`, and bounded
trace-visible `Rank` for one online maximal-root construction.

### The displayed four-player table does not prove its stated cap-root claim

As currently written, that note defines players `a,b,c,d`, gives only player
`c` a nonzero reward, and considers the constrained root

```text
x(q) = (q,0,0,0),  0 <= q <= 1/2.
```

Its relation `q t = 0` is exactly the relation on which prefixing preserves
the full prescribed-payoff/cap pair.  It is **not** the exact cap-root
relation.

At the source cap, players `a,b,d` are payoff-indifferent.  For player `c`,
Quit gives zero, while Continue gives `(1-q)t >= 0`; since the displayed root
sets `x_c=0`, the exact complementarity inequalities hold.  Therefore every
`q in [0,1/2]` is an exact cap root for every `t`.  The absorption-maximal
exact root is always `q=1/2`; it does not jump at zero.

Thus `ADAPTERS_COMPLETE.md` cannot be used in its current form to strengthen
the final packet.  Calling (29) an “exact same-source root relation” is the
decisive error.

### A clean exact constrained-root repair works

There is, however, a direct repair using the active two-player table already
checked in the packet's maximal-root section.

Take active players `a,b` with

```text
r({a})   on (a,b) = (0, 1),
r({b})   on (a,b) = (1,-1),
r({a,b}) on (a,b) = (0,-1).
```

Extend to players `a,b,c,d` as follows.  For `a,b`, use these rewards according
to the intersection of the quitting coalition with `{a,b}`; assign zero when
that intersection is empty.  For each passive player `c,d`, give payoff `-1`
iff that player belongs to the quitting coalition, and zero otherwise.

Let `a,c,d` play Never and let

```text
mu_b = t delta_0 + (1-t) delta_infinity.
```

On the constrained root face

```text
x(q)=(q,0,0,0),  0 <= q <= 1/2,
```

the exact cap-root calculation is:

- each passive player strictly prefers Continue: Quit gives `-1`, Continue
  gives zero;
- player `b` strictly prefers Continue: Quit gives `-1`, while Continue gives
  `q >= 0`;
- player `a` has Quit value zero and Continue value `t`.

Because `q < 1`, player `a`'s Continue complementarity inequality always
holds.  Its Quit complementarity inequality holds iff `q=0` or `t=0`.
Consequently the **full exact constrained-face cap-root relation** is

```text
q t = 0.
```

The face-absorption maximizer is `q=0` for `t>0` and `q=1/2` at `t=0`.
Continuation reach is always at least one half.  The selected root and its
literal prefixed child therefore have the desired nonclosed graph without
source switching, vanishing reach, or a stationary-only cap calculation.

This repairs the mathematical example, provided the result is named exactly:

```text
same-source absorption-maximal exact cap root on the displayed constrained
face
```

It is not a theorem about the globally absorption-maximal exact root over the
whole cube unless an additional argument excludes roots off that face.

### The compact-output invariant also needs trace-safe terminal consumers

The proposed `Rank` constructor states an explicit terminal consumer but does
not require that consumer to be continuous or implemented by `CW`/`SD`.
Without that requirement, the ranked closure theorem is false already at rank
zero: the terminal consumer could itself output the discontinuous maximal
selector.

Require every trace-visible terminal consumer, just like every visible child
and backward compiler, to be a trace-safe `CW` or `SD` map.  Then the compact-
output induction is valid:

- `CW` outputs are continuous images of compact witness relations;
- `SD` outputs are continuous images of compact inverse-limit codes;
- finite composition uses closed fiber products;
- finite closed cases use finite unions; and
- bounded rank uses finite induction on compact tagged terminal and successor
  relations with trace-safe terminal and backward outputs.

For a compact proof space `E`, the parent projection

```text
p : E -> [0,1]
```

is a quotient map.  If the selected face root `q` is trace-visible and unique,
the continuous output satisfies

```text
o = q_max composed with p.
```

Hence `q_max` would be continuous, contradicting the repaired jump.  Extra
compact witnesses, summable codes, finite rank tags, terminal certificates,
and trace-safe backward consumers cannot alter this conclusion.

A pointwise ranked producer run only after one source has been reconstructed
is not excluded—and does not realize the specified online construction, in
which the selected root and child must occur in every sufficiently deep finite
trace.

### Effect on export readiness

With the repaired active/passive table, the constrained-face qualifier, and
trace-safe terminal consumers added to the adapter-class definition, the
universal exclusion is a valid complete negative answer for one precisely
specified construction and one precisely specified adapter class.  It is
stronger export justification than the narrow no-go examples alone.

Without those repairs, `ADAPTERS_COMPLETE.md` must not be cited by the final
packet or generic question as an exact-cap-root impossibility theorem.
