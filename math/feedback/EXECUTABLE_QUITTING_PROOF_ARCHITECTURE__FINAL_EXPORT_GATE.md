# Final export-gate audit of the executable quitting proof architecture

Reviewer: `ARCHITECTURE_FINAL_EXPORT_GATE`

Candidate:
`notes/CODEX_ROOT__EXECUTABLE_QUITTING_PROOF_ARCHITECTURE_PACKET.md`

Related questions:

- `questions/QUITTING_COMPOSITIONALLY_SUFFICIENT_STATE.md`;
- `questions/FIN4_RECURRENT_COMPONENT_CONSUMER_OR_MODEL.md`.

Late additional target:
`meta/ADAPTERS_COMPLETE.md`.

## Verdict

**The architecture mathematics is accepted, but the current export candidate
is rejected.  A corrected version of the new adapter impossibility theorem
would change the verdict after one fresh review.**

The candidate is a sound and useful generic architecture theorem, and its
unrestricted-strategy and three substantive no-go calculations survive the
falsification attempts below.  The new Fin4 question is also a legitimate,
sharper open question.  But moving the construction-specific obligation into
a second question does not turn the generic theorem into one of the results
accepted by `exports/README.md`.

The candidate remains a supplied-program verifier and reconstruction theorem.
Its decisive input—a common tight restriction-compatible sequence whose
non-elementary operations already carry the required legal adapter
certificates—is not produced from arbitrary game data or from the established
Fin4 source.  The export policy expressly excludes a supplied-certificate
verifier or conditional statement whose source hypothesis remains open.

Nor do the no-go examples independently cross the gate.  They refute three
universal implementation shortcuts, but none eliminates a terminal Fin4
component, supplies a consumer, or rules out all trace and ranked repairs
allowed by the maintained questions.

Accordingly, the candidate should remain the canonical record in `notes/` or
`meta/`, not enter `exports/` yet.

`ADAPTERS_COMPLETE.md` attempts to supply the missing complete negative
answer.  Its closure argument is sound, but its displayed four-player table
does not realize the relation it calls the exact cap-root relation.  The
theorem is therefore false as presently written.  A small replacement table,
spelled out below, repairs the mathematics and would meet the named
acceptable-negative clause; it must be incorporated and independently
reviewed before promotion.

## Is the scope split genuine or gate gaming?

The **mathematical decomposition is genuine**.  There are now two distinct
tasks:

1. prove that a certified stopping-law program has one executable coherent
   diagonal; and
2. certify the actual non-elementary edges of the source-preserving Fin4
   residual.

The candidate completes the first task, while
`FIN4_RECURRENT_COMPONENT_CONSUMER_OR_MODEL.md` asks the second in the right
source-attached form.  This is a useful organizational improvement.

It does not by itself satisfy the export gate for two independent reasons.

First, the literal generic question has not actually been split: its current
text still says “Then instantiate the grammar on the non-elementary operations
needed by the finite quitting-game construction” and demands one of four
terminal outputs.  The candidate expressly does not do that.  Adding a second
Fin4 question duplicates that conjunct rather than removing it from the first
question.

Second, even if the generic question were rewritten to stop after the
coherent-diagonal theorem, using that rewrite alone to justify export would
waive the substantive export criterion.  The theorem is conditional on the
hard construction-facing data and has no actual-data Fin4 adapter.  Question
placement cannot convert a class expressly listed as nonqualifying in
`exports/README.md` into conjecture-facing progress.

So the split is not intellectually artificial, but treating it as sufficient
for export would be gate gaming.

## Exact mathematical content that passes

Subject to the stated assumptions, the following claims are correct ordinary
mathematics.

1. Actual stopping laws on `Nat union {Never}` are equivalent to behavioral
   hazard strategies on the unique live history.
2. Total-variation convergence controls the prescribed payoff and the full
   unrestricted unilateral cap.
3. Per-port eventual tightness, fixed positive suffix reach, and one common
   restriction-compatible execution sequence reconstruct one actual coherent
   diagonal for the elementary grammar.
4. Closed selection with a typed legal compiler, comparison transport for
   moving optimization, summable decoding with fixed-column convergence, and
   complete closed finite branches preserve trace execution.
5. A natural-valued rank is valid pointwise after reconstruction, while a
   trace-visible ranked child requires its own closed selected-child
   certificate.
6. Vanishing root debt and one payoff limit then give an exact terminal Nash
   profile and hence a uniform-equilibrium payoff through the named checked
   consumer.
7. The clock/tester, rank-one, maximal-root, and vanishing-reach examples have
   the stated narrow conclusions.

These results solve the generic reconstruction subproblem.  They do not
strictly reduce the set of remaining Fin4 game cases: both uniform escape and
minimum return remain unconsumed.

## Explicit unrestricted-strategy falsification

The packet's cap claim is genuinely about every ordinary behavioral
deviation, not only stationary or bounded-horizon deviations.

Before absorption, the only observed live history at date `t` is that every
player has Continued at dates below `t`.  A behavioral strategy for player
`i` therefore specifies one hazard at every such date and induces a law

`mu_i` on `Nat union {Never}`.

Conversely, the conditional hazards

`mu_i(t) / mu_i({t,t+1,...,Never})`

when the denominator is positive execute that law.  Against fixed opponents,
conditioning on the deviator's stopping time gives

`U_i(rho_i,mu_-i) = sum_t rho_i(t) V_i^mu(t)`.

Thus randomizing over dates, using date-dependent hazards, choosing Never,
and placing mass beyond every preassigned horizon cannot exceed

`sup_{t in Nat union {Never}} V_i^mu(t)`.

The late-finite limit is checked separately rather than silently identified
with Never.  If all opponents may Never, deadlines tending to infinity give
the solo payoff on that event, whereas Never gives the all-Never payoff zero.
Adjoining the separate Late point compactifies the test menu without adding a
legal action.  The supremum over legal finite dates and Never equals the
maximum over the split compact test space.

For two opponent packets `mu_-i` and `nu_-i`, coupling their product laws
gives a bound uniform in the chosen pure deadline.  Taking the supremum
therefore preserves the same total-variation bound.  This validates the cap
continuity used by tight fusion and the terminal-Nash limit.

The claim does not cover public correlation devices, sunspots, or correlated
multi-player deviations.  None belongs to the ordinary unilateral behavioral
strategy class stated in the packet.

**Result of falsification:** no strategy-class gap found.

## Explicit no-go falsification

### Clock/tester nonattainment

For the table

`r({c})=(-1,0)`, `r({a})=(0,0)`, `r({c,a})=(0,1)`,

let `a` Never stop and let `c` be uniform on the first `n` dates.  Then the
payoff is `(-1,0)`, the clock cap is zero by Never, and the tester cap is
exactly `1/n`, attained by matching one clock atom.

Any actual profile with clock payoff `-1` must terminate at `{c}` almost
surely.  Its clock law is then a probability law on a countable set of finite
dates and has a positive atom; the tester can match it and obtain positive
payoff.  Hence the limiting semantic pair with tester cap zero is unattained.

If all finite atoms are at most `2^(-t-2)`, the clock stops finitely with
probability at most one half, so its payoff is at least `-1/2`.  The fixed
one-half recovery obstruction is exact.

This core example is already represented in checked Lean.  The recovery-
capacity formulation is the packet's added mathematics.  It is not a Fin4
counterexample and its global minimum debt is zero.

### Rank-one discontinuity

For

`F(mu)=delta_0` if `mu(0)>0`, and `F(mu)=delta_Never` otherwise,

the laws

`mu_m = m^(-1) delta_0 + (1-m^(-1)) delta_Never`

converge in total variation to `delta_Never`, but their children remain
`delta_0`, at `l1` distance two from the limiting child.  Complete replacement
makes every child actual; singleton terminal and outcome types provide the
terminal consumer and backward map.  Strict rank therefore does not imply
trace closure.

This does not obstruct post-limit rank induction or a bounded ranked trace
whose complete selected-child relation is closed.

### Maximal exact-root nonclosure

For

`r({1})=(0,1)`, `r({2})=(1,-1)`, `r({1,2})=(0,-1)`,

take player 1 Never and player 2 quitting at date zero with probability `z`.
The cap is `(z,0)`.  At a cap root player 2 strictly prefers Continue, so
`x_2=0`.  Player 1 strictly prefers Continue when `z>0` and is indifferent
when `z=0`.  Hence the exact-root sets are

`{(0,0)}` for `z>0`, and `[0,1] x {0}` for `z=0`.

Absorption maximization selects `(0,0)` before the limit and `(1,0)` at the
limit.  Player 2's prefixed payoff and cap jump from zero to one.  At the
limiting source, epsilon-maximality within exact roots forces
`x_1 >= 1-epsilon`, so vanishing maximality error does not repair the trace
jump.

The counterexample is exact.  Its scope is also narrow: it does not invalidate
the existing pointwise canonical Fin4 maximal ray, approximate root
equations, a restricted continuous chamber, a different objective, or a
source-faithful decoder.

### Vanishing-reach suffix closure

For arbitrary target law `tau`, let `L_1 tau` delay every finite date by one
and retain Never, and put

`mu_p=(1-p)delta_0+p L_1 tau`.

Then `mu_p -> delta_0` in total variation, its depth-one reach is `p`, and its
conditional suffix is exactly `tau`.  Conversely, positive limiting reach
makes conditioning continuous, while zero depth-one reach forces the limiting
one-player source to be `delta_0`.  This proves the exact arbitrary-fibre
closure formula.

Starting from protected source `delta_0`, finite prefixing, concatenation, and
legal positive-reach suffixing preserve zero Never mass, so they cannot
produce `delta_Never`.  The one-player quitting/zero-Never table gives the
unit payoff and debt separation.  The literal self-loop at `delta_Never`
rules out a rank depending only on the law.

Again, this does not rule out an external phase rank, retained off-path
provenance, a reach-weighted consumer, or a summable decoder.  Therefore it is
not the acceptable complete negative answer to either maintained question.

**Result of falsification:** all no-go computations pass, and their explicit
nonclaims are necessary.

## Audit of `ADAPTERS_COMPLETE.md`

### The displayed table does not prove its headline

The note defines

`r_a=r_b=r_d=0`

and

`r_c(S)=1` exactly when `b in S` and `a notin S`.

At source `sigma_t` its cap computation `B_c=t` is correct.  On the displayed
root face `x(q)=(q,0,0,0)`, however, **every** `q` is an exact cap root for
every `t`:

- players `a,b,d` are indifferent because all of their rewards and caps are
  zero;
- player `c` is prescribed Continue at the root;
- `c`'s immediate-Quit payoff is zero; and
- `c`'s Continue payoff is `(1-q)t >= 0`.

Thus `c` is best-responding by Continue, with strict preference whenever
`q<1` and `t>0`.  There is no cap-root restriction `qt=0`.

Equation (28) instead says that prefixing preserves the displayed
payoff/cap pair exactly.  Consequently relation (29) is a
**semantic-pair-preserving prefix relation**, not the exact cap-root relation.
Renaming it repairs the local algebra, but not the claimed theorem about
maximal exact cap roots.  The resulting discontinuous optimizer would be an
artificial semantic-preservation selector with no established role in the
Fin4 construction and would not be conjecture-facing enough for export.

Therefore the current `ADAPTERS_COMPLETE.md` cannot be used in an export
packet.

### A valid replacement table

There is a direct four-player repair.  Let the players be `a,b,c,d`.  For a
nonempty coalition `S`, let `A=S intersect {a,b}` and define the active
rewards by

`r_a=0` on `A={a}` or `{a,b}`, `r_a=1` on `A={b}`, and `r_a=0` on
`A=empty`;

`r_b=1` on `A={a}`, `r_b=-1` on `A={b}` or `{a,b}`, and `r_b=0` on
`A=empty`.

For each passive player `p in {c,d}`, put

`r_p(S)=-1` if `p in S`, and `r_p(S)=0` otherwise.

Take the source

`mu_a=mu_c=mu_d=delta_Never`,

`mu_b=t delta_0+(1-t)delta_Never`.

Its cap vector is `(t,0,0,0)`.  On the constrained root face

`x(q)=(q,0,0,0)`, with `0 <= q <= 1/2`,

the exact cap-root relation is precisely

`t q=0`.

Indeed:

- player `a` has immediate-Quit value zero and Continue value `t`, so a
  positive Quit probability is exact exactly when `t=0`;
- player `b` has immediate-Quit value `-1` and Continue value zero, hence
  strictly Continues;
- each passive player has immediate-Quit value `-1` and Continue value zero,
  hence strictly Continues.

Therefore constrained absorption maximization selects

`q_max(t)=0` for `t>0`, and `q_max(0)=1/2`.

The selector graph is nonclosed.  Its prefixed-child trace also has a fixed
jump: for `t_n downarrow 0`, the selected children use `q=0` and converge to
the all-Never source, where player `b` has payoff and cap zero; the required
child at `t=0` uses `q=1/2`, where player `b`'s payoff and unrestricted cap
are both `1/2`.  Continuation reach is always at least `1/2`.

The cap statement is again fully behavioral.  Against the prefixed opponent
`a`, player `b` obtains `q` by Never.  Quitting at the prefixed date gives
`-1`; quitting later gives `2q-1 <= 0`.  Hence its cap is exactly `q`.

This corrected example is one actual four-player exact cap-root
bifurcation, not a semantic-preservation proxy.

### The adapter-class impossibility survives with the repaired table

The closed-output invariant in `ADAPTERS_COMPLETE.md` is valid for its stated
grammar:

- `CW` outputs are continuous images of compact witnessed relations;
- a uniformly summable `SD` decoder is continuous on its compact inverse-
  limit code;
- bounded trace-visible rank gives a finite union of compact terminal and
  successor output relations; and
- finite composition and finite closed case splits preserve compactness.

If such an adapter realized the corrected online constrained-maximal-root
operation exactly, projection to `(t,q)` would yield the nonclosed graph of
`q_max` as a compact set, a contradiction.  Arbitrary additional compact
witnesses do not help because projection of a compact proof space is compact.
The same argument includes every trace-safe bounded-rank terminal consumer
and backward map.

Pointwise selection after reconstructing one fixed `t` remains possible, but
it does not realize the specified online construction in which the selected
root and child are visible before the compact limit.  This is the necessary
scope boundary.

### Export consequence of the repair

Unlike the original generic warnings, the repaired theorem matches the
literal acceptable-negative clause of
`QUITTING_COMPOSITIONALLY_SUFFICIENT_STATE.md`:

- it fixes one exact four-player source-attached construction;
- it fixes the `CW`/uniformly summable `SD`/finite-case/bounded-trace-rank
  adapter class;
- it excludes closed or summably decoded trace realization; and
- it excludes the specified bounded renewable ranked enlargement including
  its terminal and backward consumers.

Because the negative answer was an explicit accepted output of the maintained
question, this would qualify under the rule that question placement is the
conference's relevance decision.  The conjecture-facing contribution is a
no-go for a universal exact optimized-root trace language, not progress on
either terminal Fin4 component.

The current file still fails because it proves the wrong root relation.  The
correct table and exact computations must replace Section 9, the scope must
say **constrained** maximal absorption on the displayed face, and an
independent reviewer must recheck the replacement before an export packet is
assembled.

There is one further interface repair needed in `ADAPTERS_COMPLETE.md`.
Section 5 calls the terminal consumer merely “explicit,” but the ranked
closure proof takes its image to be compact.  For a trace-visible rank, the
outcome carrier must be compact Hausdorff and the terminal consumer must be a
continuous trace-safe `CW` or `SD` map, just like every visible backward map.
Otherwise a rank-zero terminal consumer could itself output the discontinuous
selector and the closed-output invariant would be false.  This repair matches
the stronger terminal-output condition already stated in the canonical
grammar and must appear in the corrected theorem surface.

## Export-category audit

The candidate is not:

- a complete answer to the current generic question, which still contains
  the Fin4-instantiation conjunct;
- an arbitrary-game producer;
- a direct route from established Fin4 data to a semantic endpoint;
- a positive-gap counterexample;
- a special-case existence theorem with an actual-data adapter; or
- an impossibility theorem eliminating either terminal Fin4 component.

It is closest to a reduction, but it proves only sufficiency of a supplied
certificate language.  It neither proves that the current Fin4 operations
inhabit that language nor proves that every possible completion may be put in
that language.  Therefore it does not strictly narrow the mathematical Fin4
obligation in the sense required by the export policy.

The exact no-gos remove unsafe inference rules, not cases of the conjecture.
They should guide review of later producers but do not independently satisfy
the “decisively removes a purportedly exhaustive conjecture route” clause.

## Packet-quality issues if it later becomes eligible

The following are not the reason for rejection, but must be corrected before
any eventual promotion:

1. “The following five results” precedes six results, A--F.
2. `Independent reviews` is still a placeholder rather than links to the
   final audits.
3. Boundary test 3 cites formulae (20) and (21) for positive-reach continuity;
   the relevant formulae are (23) and (24).
4. The source audit should say plainly that the clock/tester nonattainment
   core is already formalized and identify only the recovery-capacity
   strengthening as new.
5. The Lean handoff is an implementation outline, not yet a narrow theorem-
   declaration map.

## What would change the verdict

Attach the generic theorem to one established source-facing object.
Specifically, prove for either uniform escape or minimum return that every
non-elementary transition used in its consumer has one of the certified
adapter forms, construct the required common tight execution sequence, and
obtain a terminal profile, charged return, or consumed renewable exit.  A
packet containing that adapter plus this grammar as its reconstruction engine
would qualify.

An exact negative packet would also qualify if, for one specified remaining
Fin4 operation, it excluded both the trace adapters and the specified external
ranked repair while retaining the actual source data.  The present generic
counterexamples do not do that.
