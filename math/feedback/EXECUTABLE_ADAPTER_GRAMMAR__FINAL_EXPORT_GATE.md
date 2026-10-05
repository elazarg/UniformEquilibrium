# Final export-gate audit: executable adapter grammar

Reviewer: `ARCHITECTURE_EXPORT_GATE`

Exact candidate reviewed:
`formalized/EXECUTABLE_ADAPTER_GRAMMAR_AND_CONSTRAINED_ROOT_NO_GO.md`

Additional comparison target:
`meta/EXECUTABLE_COMPLETE.md`

## Verdict

**Return for literal mathematical repair; do not copy the current file to
`exports/`.**

The central negative result is correct and export-worthy.  The rational Fin4
table really has the stated unrestricted caps, its exact root relation on the
displayed compact face is exactly `t q = 0`, the greatest constrained-face
root has a nonclosed graph, the continuation reach is uniformly at least one
half, and the literal prefixed child exposes the same discontinuity in both
payoff and unrestricted cap.  The compact-output argument genuinely excludes
compact-witness adapters, decoders of the declared uniformly summable form,
and bounded trace-visible ranked adapters whose terminal and backward maps are
trace-safe.

This is a complete accepted-negative answer in principle to
`questions/QUITTING_COMPOSITIONALLY_SUFFICIENT_STATE.md`.  That conclusion is
not gate gaming after the scope split: the generic question explicitly
accepts one exact construction-level impossibility theorem, while
`questions/FIN4_RECURRENT_COMPONENT_CONSUMER_OR_MODEL.md` separately retains
the open positive-minimum Fin4 instantiation.

The exact packet nevertheless overstates its positive grammar theorem in four
places.  Two are decisive: the summable decoder is not anchored at the named
source, and `PostRank` is placed in the trace grammar over which projective
compactness is asserted.  Thus the present file does not yet prove its own
source-faithful projective-realization statement.  The remaining two defects
are omitted compactness hypotheses/constructor data.  They have short direct
repairs, but the export gate requires those repairs to occur in the packet
before promotion.

The newer `meta/EXECUTABLE_COMPLETE.md` contains the right two-sorted
trace/control normal form and may be used to repair the positive theorem.  Its
pointwise-rank impossibility is valid only for the newly defined *coherent
maximal-root-return* outcome.  It is not an impossibility theorem for
pointwise optimized-root selection in general and should not be presented as
one.

## 1. Exact falsification of the unrestricted-strategy claim

The packet models one player's ordinary behavioral strategy by a probability
law on

\[
\overline{\mathbb N}=\mathbb N_0\cup\{\infty\}.
\]

This is correct for the standard quitting game.  Before absorption, the only
live public history at date `n` is the string of `n` all-Continue outcomes.
Consequently a behavioral strategy is a sequence of live-history hazards and
induces one first-quitting-time law.  Conversely, the displayed survival-ratio
hazards realize every probability law, including an arbitrary Never mass.

Under the game's ordinary independent behavioral randomization, players'
stopping times have the product law.  For a fixed unilateral replacement
`tau_i`, changing only the opponents changes the product law by at most the
sum of their `l1` distances; pushforward to the first-time/coalition outcome
law is contractive.  Therefore

\[
\sup_{\tau_i}
\|\Lambda_i(\sigma,\tau_i)-
  \Lambda_i(\sigma',\tau_i)\|_1
\leq
\sum_{j\ne i}\|\mu_j-\mu'_j\|_1.
\]

For rewards bounded in absolute value by `R`, duality gives the packet's
payoff estimate.  Taking the supremum over all replacement laws gives the same
estimate for the complete behavioral cap.  Thus the proof includes randomized
calendar-dependent stopping, arbitrarily late pure dates, and Never.  It does
not include public correlation/sunspots or coalitional deviations, and the
packet does not claim either.

I tried the natural falsifier in which a randomized behavioral strategy uses
history-dependent mixing not representable by one stopping law.  It fails:
there is no branching live public history in a quitting game.  The hazard at
each all-Continue history determines exactly the law above.

The prefix estimate and the positive-reach suffix estimate are also correct.
With `l1` rather than half-`l1` total variation, the constants are coarse but
valid.

## 2. Full audit of the Fin4 table

Let the players be `a,b,c,d`.  For every nonempty coalition `S`, the packet
defines

\[
r_a(S)=1
\quad\Longleftrightarrow\quad
b\in S\text{ and }a\notin S,
\]

and otherwise `r_a(S)=0`;

\[
r_b(S)=
\begin{cases}
-1,&b\in S,\\
1,&a\in S,\ b\notin S,\\
0,&a,b\notin S;
\end{cases}
\]

and for `p=c,d`,

\[
r_p(S)=-1\quad\Longleftrightarrow\quad p\in S,
\]

with zero otherwise.  Nonabsorption pays zero.

In `sigma_t`, players `a,c,d` play Never and player `b` quits at date one
with probability `t` and otherwise Never.  Directly,

\[
U(\sigma_t)=(t,-t,0,0).
\]

The full behavioral caps are

\[
B(\sigma_t)=(t,0,0,0).
\]

The coordinate checks are exhaustive:

- `a` earns one only if `b` quits before `a`; that event has probability at
  most `t`, and Never (or any date after date one) attains `t`;
- `b` obtains zero by Never, whereas every finite first quit by `b` pays
  `-1`;
- `c` and `d` obtain zero by Never, and any quit before or with absorption
  pays `-1`; quitting after `b` has already absorbed cannot alter the outcome.

Randomization is a convex combination of these stopping-time values, so it
cannot improve them.

Now restrict the root to

\[
x(q)=(q,0,0,0),\qquad 0\leq q\leq\tfrac12.
\]

The root Quit/Continue comparisons against the exact continuation cap are:

\[
\begin{array}{c|cc}
 & Q & C\\ \hline
a&0&t\\
b&-1&q\\
c&-1&0\\
d&-1&0.
\end{array}
\]

Thus `b,c,d` strictly Continue.  Player `a` can mix with positive Quit mass
only if `0 >= t`; because `q<1`, its Continue inequality is automatic.  Hence

\[
x(q)\text{ is an exact cap root on the face}
\quad\Longleftrightarrow\quad tq=0.
\]

The greatest face coordinate is therefore

\[
q^{\max}(t)=
\begin{cases}
0,&t>0,\\
1/2,&t=0.
\end{cases}
\]

Its graph is not closed.  Every selected child has literal continuation reach

\[
1-q^{\max}(t)\geq1/2.
\]

For the literal child obtained by prefixing `sigma_t`, player `b` has

\[
U_b(P_q\sigma_t)=q-(1-q)t,
\qquad
B_b(P_q\sigma_t)=q.
\]

For the cap, continuing at the new root and then playing Never earns one on
the event that `a` quits there, hence `q`.  Quitting at the root pays `-1`.
After joint continuation, every finite quit by `b` pays `-1`, while Never
retains the payoff already generated by `a`'s root action.  No randomized or
late stopping rule does better.  Therefore the child semantic trace jumps
from limit zero along `t>0` to `1/2` at `t=0`, exactly as claimed.

This calculation also falsifies the earlier erroneous interpretation of a
relation such as `tq=0` as mere semantic-pair preservation: here it is the
actual exact cap-root relation on the displayed face.

## 3. Audit of the compact-output invariant

For a compact parent port, the following argument is valid under the packet's
intended contracts.

- A `CW` output relation is the image of a closed subset of a compact
  parent/witness product under a continuous map, so it is compact.
- An `SD` output is continuous on a compact inverse-limit code when the
  actual-profile and visible-label tails have uniform summable budgets.
- Finite composition is a closed fiber product, and a genuinely finite closed
  tagged case split is a finite union of compact images.
- A bounded trace-visible rank has only finitely many ranks.  If terminal and
  successor certificate carriers are compact, the branch relations are
  closed, terminal consumers and backward compilers are continuous, and the
  parent coordinate is retained, induction makes every complete outcome
  relation compact.

Consequently projection to `(t,q)` is closed.  Exactness and uniqueness force
that projection to equal the nonclosed graph of `q^max`, a contradiction.
Adding arbitrary extra *compact* proof witnesses cannot help, since their
existential projection remains compact.

I tried four standard escapes.

1. Choosing `q=0` continuously works but is not maximal at `t=0`.
2. Choosing `q=1/2` at the limit works pointwise but does not give the limit
   of the trace-visible prelimit children.
3. A search counter `n` compactified by `n -> infinity` merely forces the
   `q=0` branch into the closed fiber at `t=0`.
4. Continuous approximate selectors can converge pointwise to the jump, but
   they have no uniform summable visible-output tail.  If a declared decoder
   does have such a tail and claims zero-error exact maximality at the limit,
   its output is continuous and the same contradiction returns.

Thus the no-go is exact for the declared trace-visible adapter class.  It does
not exclude recording the whole closed exact-root relation, using a nonmaximal
root, restricting the source domain away from the jump, or making a
discontinuous choice only after one source has been reconstructed.

## 4. Decisive defect: the `SD` ancestry is not source-anchored

The current `SD` constructor supplies profiles

\[
\sigma_0,\sigma_1,\ldots
\]

and finite legal macros only from `sigma_n` to `sigma_(n+1)`.  It never
requires

\[
\sigma_0=s(x)
\]

and never supplies a legal initial macro from the named source `s(x)` to
`sigma_0`.

Equation (10) nevertheless places `s(x)` next to the unrelated chain and
concludes that the decoded descendant has literal ancestry from that source.
That conclusion is false under the displayed definition: the same summable
chain can be paired with any source label.

Require either `sigma_0(z|0)=s(x)` for every complete code, or a retained
compact finite certificate from `s(x)` to `sigma_0`.  Endpoint equalities of
every path certificate must be closed code coordinates.  Only then is the
projected inverse-limit ancestry source-faithful.

This is not cosmetic; exact source ancestry is one of both the packet's main
claims and the named question's requirements.

## 5. Decisive defect: `PostRank` is simultaneously inside and outside the trace

Section 2 defines

```text
G ::= CW | SD | Case | Rank | PostRank | composition.
```

Section 6 correctly states that `PostRank` is a pointwise control operation
available only after one actual limiting node has been reconstructed and is
not trace-visible.  Section 7 then quantifies over an arbitrary grammar term
`G`, declares every truncated execution space compact, and proves legality of
every limiting visible edge only from `CW`, `SD`, and bounded trace-visible
`Rank` closure.

Those statements are incompatible.  A discontinuous pointwise selected child
inside `E_n` need not survive compact trace limits; indeed the packet's own
maximal-root example supplies such a discontinuity.

Use a two-sorted syntax:

```text
TraceG ::= CW | SD | Case | TraceRank_K | composition
Control ::= PostRank applied after projective reconstruction.
```

The projective theorem must quantify only over `TraceG`.  Pointwise control is
then proved separately by ordinary natural-number induction at the single
reconstructed actual node.

This repair is exactly the distinction adopted in
`meta/EXECUTABLE_COMPLETE.md`.

## 6. Two further positive-theorem omissions

### Compact rank witnesses

The packet declares the terminal certificate carrier compact, but writes

\[
S_{k\ell}\subseteq X_k\times W_{k\ell}\times X_\ell
\]

without explicitly declaring every `W_(k,l)` compact metrizable.  Closedness
of `S_(k,l)` is otherwise insufficient for compactness of the fiber product
used in the ranked closure theorem.  Add this hypothesis literally.

### Case and numerical annotations

`Case` occurs in the grammar but has no constructor definition.  It must use
a finite tag space, closed branch relations covering the parent, and
trace-safe branch compilers; open strict predicates by themselves do not
give a compact branch relation.

Likewise, a summable increment budget does not compactify an unbounded initial
real annotation: constant sequences of arbitrary real value have zero
increment.  Every numerical annotation appearing in an execution space must
start in a fixed compact carrier or be prescribed convergent exogenous data.
Only then does the claim that every `E_n` is compact follow.

These are genuine theorem-surface hypotheses, not implementation details.

## 7. Assessment of `meta/EXECUTABLE_COMPLETE.md`

The normal-form theorem in the newer note is the cleaner way to repair the
trace grammar.  In particular, it excludes pointwise rank from trace syntax
and shows that certified bounded trace rank is a finite union of finite
compositions of compact executable adapters.  Its coherent-diagonal theorem
then follows by countable compact extraction and induction through each finite
diagram.  Subject to retaining explicit source ancestry in the decoder, I
found this positive architecture sound.

The newer two-player table is also correct.  With

\[
r(\{1\})=(0,1),\quad
r(\{2\})=(1,-1),\quad
r(\{1,2\})=(0,-1),
\]

and source `mu^z=(Never, z delta_0+(1-z) Never)`, one has

\[
B(\mu^z)=(z,0).
\]

The exact roots are `(0,0)` for `z>0` and `(q,0)`, `0<=q<=1`, for `z=0`.
The absorption maximizer therefore jumps from `q=0` to `q=1`.  At the limit,
an `epsilon`-maximal root has `q>=1-epsilon`, so its depth-one reach is at most
`epsilon` and its player-two payoff and cap are `q`.  Hence no limiting output
can simultaneously have fixed reach `alpha>epsilon` or strategic trace error
`eta<1-epsilon`.

Theorem 3's pointwise-rank clause is therefore mathematically valid **for the
declared outcome type**: an induction whose every terminal/backward branch is
claimed to return an `(epsilon,eta,alpha)` coherent maximal-root return cannot
produce an inhabitant, because the displayed inequalities prove that type
empty.

This must not be renamed as a general pointwise-rank impossibility.  Once the
limiting source is reconstructed, pointwise control may select the actual
maximal root `q=1`; in this very table that root gives an exact terminal Nash
profile.  The no-go applies only if the rank is required to preserve the
specific positive-reach/trace-close return objective.  A rank allowed to exit
through another genuine consumer is not excluded.

This strengthened coherent-return boundary is useful but is not necessary to
validate the present constrained-face trace no-go.  If integrated, it should
be a separately named theorem with the nonclaim above, not evidence that the
current `PostRank` syntax is trace-safe.

## 8. Match to the named question

After repairing the positive theorem, the packet meets the acceptable
negative clause of
`QUITTING_COMPOSITIONALLY_SUFFICIENT_STATE.md`:

- the construction is the exact online constrained-face maximal-root
  construction `M` on the whole compact source family;
- the adapter class is precisely compact-witness, declared uniformly
  summable decoder, finite closed composition/case, and bounded trace-visible
  rank with terminal and backward consumers;
- the source is one fixed actual source followed by a compact family of
  literal unilateral replacements;
- reach is uniformly at least one half;
- the suffix is the exact displayed source;
- caps quantify over all behavioral replacements; and
- the compact-output invariant excludes closed realization, decoded exact
  realization, and the specified trace-visible rank enlargement.

The result does **not** answer the separate Fin4 residual-program question.
Its table has an easy equilibrium and is not an instance of the supplied
positive-minimum forced-pair residual.  The packet states this correctly.

## 9. Source and novelty audit

The cited declarations exist and support the translations claimed:

- `StoppingLaw.toScalarHazard` and
  `StoppingLaw.stoppingLaw_toScalarHazard` in
  `MathUE/Probability/StoppingLawReconstruction.lean` provide the law-to-hazard
  realization;
- `quittingStoppingLawBehaviorStrategy` and
  `quittingBehaviorStoppingLaw_stoppingLawBehaviorStrategy` in
  `UniformEquilibrium/Quitting/Terminal/StrategicallyPrecompactWatchdogProperBoundary.lean`
  provide the quitting behavioral compiler;
- `quittingRootSequenceHazardTerminalValue_eq_expect_stoppingLaw` in
  `UniformEquilibrium/Quitting/Paths/BehaviorStoppingPayoff.lean` identifies
  the stopping-law expectation with the root-sequence terminal value;
- `IsεQuittingRootNash` in
  `UniformEquilibrium/Quitting/Root/FirstBranch.lean` is the exact root-Nash
  notion used in the finite table calculation.

The packet currently cites
`quittingGame_isUniformEquilibriumPayoff_of_terminalNash_exact` while speaking
about a sequence with vanishing debt and one payoff limit.  The matching
declaration is
`quittingGame_isUniformEquilibriumPayoff_of_terminalNash_tendsto` in
`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`.
Either cite that theorem or change the sentence to a single exact terminal
Nash profile.

I found no existing checked declaration proving the compact-witness grammar,
the source-faithful summable decoder, the bounded trace-rank closure theorem,
the projective realization theorem, or this nonclosed constrained optimizer.
The existing maximal-prefix rays are pointwise Research constructions and do
not duplicate the universal trace-visible no-go.  No external literature
theorem is invoked.

## 10. Packet-format and final repair list

Before promotion, the exact packet must:

1. anchor every `SD` chain at the named source;
2. split trace grammar from post-limit pointwise rank and restrict the
   projective theorem to the former;
3. declare every ranked successor witness carrier compact;
4. define `Case` and compactly anchor every numerical annotation;
5. replace both headline uses of unqualified `maximal-root` by
   `constrained-face absorption-maximal exact-root`;
6. qualify decoder universality as the declared uniformly summable `SD`
   class;
7. cite the terminal-Nash convergence consumer rather than the exact-profile
   consumer;
8. replace the independent-review placeholder with links to at least two
   substantive reviews, including this explicit falsification audit; and
9. use a stable export filename without the agent prefix, for example
   `EXECUTABLE_ADAPTER_GRAMMAR_AND_CONSTRAINED_ROOT_NO_GO.md`.

The previous independent root/closure audit is
`feedback/ADAPTERS_COMPLETE__ROOT_AND_CLOSURE_AUDIT.md`.  The packet may also
cite the independent full-mathematics audit
`feedback/EXECUTABLE_ADAPTER_GRAMMAR__FINAL_MATH_AUDIT.md` after its objections
have been repaired.  Those objections are not waived by listing the review.

## Final disposition

The corrected constrained-root no-go is genuine conjecture-facing progress
and should not be lost.  The current exact export wrapper is not yet a complete
proof of the positive architecture it states.  Apply the nine literal repairs
above (or replace the positive layer by the cleaner two-sorted normal form),
then perform one diff-level recheck.  No new review of the finite reward-table
calculation is needed unless that table or its constrained face changes.

---

## Addendum after the 30 August literal repairs

I re-read the complete current candidate after the author applied the four
grammar repairs and the three wrapper repairs identified above.  The following
changes are present and mathematically correct:

1. `sigma_0(z|_0)=s(x)` now anchors every complete `SD` code at the named
   source, and equation (10) retains that equality in the ancestry object;
2. the syntax is now explicitly two-sorted: `TraceG` excludes `PostRank`, and
   the projective theorem quantifies only over `TraceG`;
3. every successor witness carrier `W_(k,l)` is explicitly compact
   metrizable;
4. `Case` is defined using a finite tag set, compact branch witnesses, closed
   tagged relations covering the parent, and continuous branch compilers;
5. numerical annotations have a compact base carrier (or prescribed compact
   exogenous closure) in addition to summable increments;
6. the headline construction is identified as a constrained-face
   absorption-maximal exact-root construction;
7. decoder universality is restricted to the declared uniformly summable
   `SD` class; and
8. the terminal convergence source now cites
   `quittingGame_isUniformEquilibriumPayoff_of_terminalNash_tendsto`.

These repairs discharge every objection to the table, the unrestricted-cap
calculation, the compact-output invariant, and the trace/control separation.
No objection from the earlier snapshot survives in those arguments.

### Two remaining theorem-surface defects found by the literal recheck

The exact current file is nevertheless **not yet a final export packet**.
There are two small but mathematical completeness defects, not merely prose
preferences.

#### A. `SD` is anchored where it exists, but it is not total over its parent

`CW` explicitly requires `pi_X(R)=X`, `Case` requires its branches to cover
`X`, and `Rank` has its completeness equation.  `SD` currently requires only

```text
Z_n subset X times W_0 times ... times W_(n-1)
```

and surjective bonding maps `Z_(n+1) -> Z_n`.  It does not require
`Z_0 -> X`—equivalently the complete-code projection `Z_infinity -> X`—to be
surjective.  Thus an empty code system, or a code system supported on a proper
closed subset of the parent, satisfies the displayed constructor while not
providing an adapter for the other parent points.

Add

\[
Z_0=X
\]

under the evident identification, or explicitly require

\[
\pi_X(Z_\infty)=X.
\]

With the compact nonempty fibers and surjective bonding maps, this makes the
decoder a total edge exactly like the other constructors.  If partial
adapters are intended instead, their domain must replace `X` as the parent
port everywhere; the current theorem says neither.

#### B. The projective system is not defined for the stated finite term

Section 7 presently begins with one grammar term `G : TraceG` and then uses
execution spaces `E_n` “truncated at visible depth `n`”, with
`n -> infinity`.  But the displayed `TraceG` syntax builds finite expressions
(finite composition, finite case, and bounded rank); no recursive or
countable grammar term, unfolding operation, or depth restriction is defined.
For one finite term, sufficiently large truncations are just the whole finite
term, so the claimed countable projective theorem is either trivial or
ill-typed relative to the intended increasing executions.

Use the already correct formulation from `meta/EXECUTABLE_COMPLETE.md`:

\[
P_1\preceq P_2\preceq\cdots
\]

is an increasing restriction-compatible sequence of finite rooted
`TraceG` diagrams, and `E_m` is one execution of `P_m` whose restriction to
every earlier `P_k` is an execution of that same named diagram.  Then take the
countable union of named edge occurrences and run the diagonal proof.  This is
also the formulation literally requested by the maintained question.

The proof already written applies after that change; no new compactness idea
is needed.

### Remaining export mechanics

The exact-statement line still says “every bounded ranked enlargement” where
the proved class is “every bounded **trace-visible** ranked enlargement.”  Add
that word in the exact statement.  Otherwise the headline can be read as
including the `PostRank` class that the scope section correctly excludes.

The independent-review field remains a placeholder.  It must name the two
reviews required for the unrestricted-strategy claim, for example the root
and closure audit and this explicit falsification audit (plus the full math
audit if desired), after every objection named by those reviews is repaired.

There are also two stray display delimiters in the current file: one after
`P'=(R,C)` and one immediately before `e_m in E_(n_m)`.  They are rendering
errors only, but should be removed in the export copy.

### Updated gate verdict

**Mathematical core: pass.  Exact current packet: repair required.**

After adding `SD` totality, stating the projective theorem for an increasing
sequence of finite named diagrams, narrowing the exact-statement rank phrase,
and filling the review metadata, I would approve promotion without another
review of the reward table or no-go calculation.  A final diff check of those
four edits is sufficient.

---

## Final diff recheck and approval

The author subsequently applied the four remaining edits.  I checked the
current file literally rather than relying on the prior snapshot.

- The decoder now has `Z_0=X`, and the bonding maps are continuous and
  surjective.  Hence the inverse-limit projection is total over the parent;
  together with `sigma_0=s(x)`, the decoder is both total and source-anchored.
- The projective theorem now starts with an increasing
  restriction-compatible sequence

  \[
  P_1\preceq P_2\preceq\cdots
  \]

  of finite rooted `TraceG` diagrams.  Shared occurrences retain their syntax
  and source-port names, and each restricted execution is an execution of the
  same earlier diagram.  This supplies the countable projective object used
  by the diagonal proof and matches the maintained question's quantifiers.
- The exact statement now says “bounded trace-visible ranked enlargement,”
  agreeing with the two-sorted syntax and the final nonclaims.
- The independent-review field now links the mathematical audit, this export
  and falsification audit, and the comparison audit.

I also re-inspected the two display locations I had described as containing
stray delimiters.  The displays around `P'=(R,C)` and equation (16) are
properly paired in the current file.  The earlier observation resulted from a
truncated multi-range command output and is withdrawn; no delimiter should be
deleted at either location.

The repaired theorem surfaces preserve the already verified unrestricted
strategy semantics, exact Fin4 cap/root calculation, positive reach and
literal provenance, compact-output invariant, and accepted-negative match.
No unresolved mathematical objection remains.

### Final gate verdict

**APPROVE FOR EXPORT.**

Use the stable filename
`EXECUTABLE_ADAPTER_GRAMMAR_AND_CONSTRAINED_ROOT_NO_GO.md`.  This approval is
for the exact current mathematical content: the generic executable grammar
and projective theorem, plus the constrained-face trace-visible optimizer
no-go.  It does not approve any claim that pointwise rank is generally
impossible, any globally maximal-root no-go over the full cube, or any
consumption of the positive-minimum Fin4 residual.
