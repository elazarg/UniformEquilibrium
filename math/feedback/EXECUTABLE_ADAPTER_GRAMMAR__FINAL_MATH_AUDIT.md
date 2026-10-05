# Final mathematical audit of the executable adapter grammar

Reviewer: `ARCHITECTURE_PACKET_AUDIT`

Primary target:
`formalized/EXECUTABLE_ADAPTER_GRAMMAR_AND_CONSTRAINED_ROOT_NO_GO.md`

Comparison target:
`meta/EXECUTABLE_COMPLETE.md`

## Verdict

**Repair required before export.**  The repaired Fin4 constrained-root
counterexample is correct, including its caps against every behavioral
replacement, its exact cap-root relation, the uniform reach floor, and the
closed-output exclusion for compact witnesses, uniformly summable decoders,
and bounded trace-visible rank.  It is a legitimate accepted negative answer
for the precisely specified online construction and adapter class.

The abstract positive grammar still has four interface gaps.  Two are
substantive: the summable decoder does not anchor its first macro to the named
source, and `PostRank` is included in the trace grammar even though the
projective theorem relies on excluding it.  The other two are compactness and
constructor-definition omissions.  All have direct repairs and do not affect
the Fin4 calculation.

I would approve the packet after the required changes below and one literal
recheck.  The alternative `EXECUTABLE_COMPLETE.md` does not presently
supersede it; its normal-form idea is useful, but it has its own terminal-rank
and no-go presentation gaps recorded in the comparison section.

## Required repair 1: anchor every decoded path at the named source

The `SD` constructor supplies profiles

```text
sigma_0, sigma_1, ...
```

and legal macros only from `sigma_n` to `sigma_(n+1)`.  Nothing in the current
definition says that `sigma_0` equals the named input source `s(x)`, or that a
legal initial macro runs from `s(x)` to `sigma_0`.

Nevertheless (10) places `s(x)` beside that path and the prose concludes that
the decoded output has an ancestry from the exact initial source.  This does
not follow.  An arbitrary unrelated summable chain could currently be labelled
with any `s(x)`.

Add one of the following exact requirements:

```text
sigma_0(z|0) = s(x)
```

for every complete code, or a retained finite legal certificate

```text
gamma_initial : s(x) -> sigma_0(z|0).
```

Every finite path certificate must be a compact/closed code coordinate, and
its endpoints must equal the displayed profiles.  With that anchor, (10) is a
genuine source-faithful inverse-limit ancestry and its projection is closed.

Without this repair the positive grammar does not meet its own provenance
claim or the maintained question's source-regeneration requirement.

## Required repair 2: separate `PostRank` from the trace grammar

Section 2 puts `PostRank` inside

```text
G ::= CW | SD | Case | Rank | PostRank | composition.
```

Section 6 then correctly says that a pointwise ranked producer may run only
after one actual limiting node has been reconstructed and is not trace-visible.
Section 7 nevertheless quantifies over an arbitrary grammar term `G` and
claims every limiting visible edge is legal using only `CW`, `SD`, and bounded
trace-visible `Rank` closure.

These statements are inconsistent.  A discontinuous pointwise child inside
`E_n` destroys compact trace closure, exactly as the architecture's rank-one
example shows.

Use a two-sorted syntax:

```text
TraceG ::= CW | SD | Case | Rank | composition
Control ::= PostRank applied after projective reconstruction.
```

State the projective theorem only for `TraceG`.  Section 6 may remain as a
separate post-limit consumer.  This also makes the scope of the negative
theorem exact: it excludes bounded trace-visible `Rank`, while pointwise rank
can select `q_max(t)` after one fixed `t` is reconstructed but cannot realize
the online trace-visible construction.

## Required repair 3: make every ranked witness carrier compact

For rank `k`, the terminal certificate carrier `C_k` is compact, but the
successor relation is written

```text
S_(k,l) subset X_k times W_(k,l) times X_l
```

without declaring `W_(k,l)` compact.  Closedness of `S_(k,l)` alone does not
make it compact, so the fiber product used in (15) need not be compact and the
closed-output invariant need not follow.

Declare every `W_(k,l)` compact metrizable.  Then each successor relation is
a closed subset of a compact product, and the induction proving compactness of
`O_k` is valid.  The repaired requirements on compact `Y_k`, continuous
trace-safe terminal consumers, trace-safe backward maps, and retention of the
parent coordinate in `O_k` are otherwise sufficient.

## Required repair 4: compactly anchor numerical annotations and define Case

Section 7 says every truncated execution space `E_n` is compact, but then
allows a “noncompact numerical annotation” to be covered merely by a summable
successive-difference budget.  Such a budget does not bound its starting
value: the family of constant real sequences has zero successive difference
and arbitrary initial value.

Require each base annotation to lie in a fixed compact carrier, or to be
prescribed convergent exogenous data.  A summable increment budget then keeps
the decoded annotation in a compact bounded region.  This is particularly
important for the recorded LawMin error.

The syntax also names `Case` but never gives its constructor.  Add the short
definition used implicitly later: a finite tag set; a closed tagged relation
on each branch; branch relations covering the parent port; and a trace-safe
branch compiler.  The child is the finite disjoint union of the compact branch
ports.  Branch overlap at a boundary is allowed; an open strict test alone is
not a branch certificate.

With these additions, finite composition by closed fiber product and finite
case union preserve compactness as claimed.

## Minor clarification to the positive theorem

The sentence “weak convergence of pure dates `delta_n -> delta_infinity`”
should name the usual one-point compactification topology.  It is not true in
the discrete topology on the displayed set.  The actual theorem uses `l1` and
does not depend on this contextual sentence.

The pointwise-rank proof should be stated as ordinary induction on arbitrary
actual nodes, not literally as the compact ranked theorem on a singleton
parent space unless all descendant certificate spaces also satisfy the compact
trace hypotheses.  No compactness is needed for the pointwise result.

## Independent verification of the actual-law layer

Every probability law on finite stopping dates plus Never is executed by the
displayed hazard ratios.  Before absorption, the only live public history is
the all-Continue history, so this captures every ordinary behavioral strategy
of one player.  Independent behavioral randomization across players gives the
product stopping-time law.

For fixed opponents, a complete unilateral behavioral replacement is an
arbitrary law on this countable stopping-time space.  The first-time/coalition
outcome law is a pushforward of the product.  Keeping the deviator's law fixed
and changing the opponents gives (1) by the product `l1` inequality and
pushforward contraction.  Bounded reward expectation gives (2), uniformly in
the replacement.  Taking the supremum preserves the same bound.  The cap is
therefore the full behavioral cap, including Never, randomized laws, and mass
at arbitrarily late dates.

The prefix formula and estimate (3) are correct.  Conditioning a restriction
of mass at least `rho` gives the coarse `2/rho` bound (4).  Complete
replacement and finite concatenation are actual behavioral operations.

## Independent verification of `CW`, repaired `SD`, and `Rank`

A closed relation in the compact parent/witness product is compact.  Its
continuous actual compiler yields a compact child port.  Retaining the
witness in the child trace avoids assuming a continuous selector.  If a
unique selected value is claimed, the resulting selected graph must indeed be
closed.

For `SD`, the inverse limit of nonempty compact finite code spaces with the
displayed restrictions is compact.  The uniform summable bound makes the
actual profiles uniformly Cauchy in the complete `l1` probability-law space;
their limit is actual and the decoder is continuous.  The reach estimate (9)
is correct.  Once repair 1 anchors the chain, compact inverse-limit provenance
gives a literal displayed infinite ancestry from the exact source.

For `Rank`, after repair 3, the terminal graph is a continuous image of a
compact relation.  The successor fiber product with `O_l` is compact, the
continuous backward output retains the parent coordinate, and finite union
over lower ranks preserves compactness.  Completeness of branches gives
totality.  Thus every `O_k` is a compact closed total outcome relation.

The pointwise theorem remains separate: natural-number induction consumes a
terminal certificate or a lower-rank child and applies the backward map.  It
proves no trace continuity.

## Projective compactness after the repairs

For the trace-only syntax, every finite truncated execution space is assembled
from compact ports by closed fiber products and finite disjoint unions.  It is
therefore compact.  A common sequence of executions at growing depths admits
a diagonal subsequence converging at every fixed depth.  Continuity of the
restriction maps gives a compatible inverse-limit execution.

Each `SD` track has one inverse-limit code, rather than one independently
chosen decoder at every depth.  Closed legal relations, anchored provenance,
positive reach budgets, and compact ranked outputs keep every limiting visible
edge legal.  Equations (1)--(2) pass all unrestricted unilateral comparisons
to the limit.

The fixed singleton initial port is not an obstacle to the negative example:
the compact source family `t -> sigma_t` is produced from `sigma_0` by one
compact-witness complete-replacement edge whose witness is `t in [0,1]`.

## Independent verification of the Fin4 obstruction

The reward table (21) is rational and fully defined on every nonempty
coalition.  At the source (22), only player `b` may quit.  Therefore

```text
U(sigma_t) = (t,-t,0,0).
```

The full behavioral caps are exactly

```text
B(sigma_t) = (t,0,0,0).
```

Player `a` can earn one only when `b` quits first without `a`, an event of
probability at most `t`, and Never attains it.  Player `b` earns zero by Never
and `-1` upon every finite unilateral first quit because all opponents Never.
For a passive player, Never gives zero; any finite quit pays `-1` if it occurs
before or with `b`, and zero only if `b` has already absorbed.  No randomized
behavioral replacement improves these endpoint bounds.

On the face

```text
x(q)=(q,0,0,0),  0 <= q <= 1/2,
```

the root comparisons are:

```text
c,d: Quit=-1, Continue=0;
b:   Quit=-1, Continue=q;
a:   Quit=0,  Continue=t.
```

The exact complementarity inequalities therefore hold iff `q t=0`.  The
greatest constrained-face exact root is `q=0` for `t>0` and `q=1/2` for
`t=0`.  Its graph is not closed, while continuation reach is at least one
half and every child prefixes the literal source `sigma_t`.

For the child, direct all-behavior calculation gives

```text
U_b(P_q sigma_t) = q-(1-q)t,
B_b(P_q sigma_t) = q.
```

Never after continuing at the prefixed root attains `q`.  Quitting at the
root gives `-1`; quitting later gives `q-(1-q)=2q-1 <= 0`, and randomization
cannot exceed the best pure stopping law.  Hence the cap identity includes
every behavioral deviation.  Along `t downarrow 0` the selected prelimit
children converge to payoff/cap zero for `b`, whereas the required child at
zero has both equal to one half.

## Verification of the closed-output no-go

After repairs 2--4, every trace-visible output relation in the declared class
is compact:

- `CW` by compact witnessed relation and continuous output;
- `SD` by compact inverse-limit code and continuous decoder;
- finite composition by closed fiber product;
- finite cases by finite compact union; and
- bounded trace-visible rank by the `O_k` induction.

The parent projection of a compact proof space onto `[0,1]` is a quotient map.
Exactness and uniqueness force every visible output to be

```text
q = q_max(t).
```

A continuous output through a quotient parent projection would make `q_max`
continuous, contradicting its jump.  Equivalently, projection of the complete
compact output relation to `(t,q)` would be the nonclosed graph of `q_max`.
Arbitrary extra compact witnesses and valid terminal/backward rank data do not
help.

This excludes the precisely specified **constrained-face**
absorption-maximal exact cap-root operation.  It does not claim nonclosedness
of the globally maximal root over the full cube.  A pointwise selector after
one fixed `t` has been reconstructed remains valid control, but does not
realize the online construction in which `q` and the child are visible before
the compact limit.

Thus the negative theorem meets the maintained generic question's acceptable
negative clause once the adapter syntax is repaired as above.

## Equation and scope audit

All numbered equations (1)--(31) in the primary target are unique and their
references are consistent.  In particular:

- (21) is the reward table;
- (23)--(24) are source payoff and cap;
- (25) is the reach floor;
- (26)--(28) are the exact root relation and its maximizer; and
- (29)--(31) are the child discontinuity and semantic coordinates.

The table is consistently described as a constrained-face maximization, not
as global absorption maximization.  The source family is the entire compact
parent port, not one existentially selected parameter.  The approximate-root
nonclaim is also correct: an actually approximate finite-accuracy output may
remain possible, while a summable decoder required to expose the exact
discontinuous selector at its limit remains impossible.

The review placeholder must be replaced by actual links before export.  Since
the packet explicitly audits unrestricted behavioral deviations, two
independent reviews and a falsification attempt are required by the export
policy.

## Comparison with `meta/EXECUTABLE_COMPLETE.md`

The alternative note contains one useful strengthening: Theorem 1 proposes a
normal-form elimination of every certified trace expression into one compact
witness/closed-domain/continuous-compiler adapter.  Composition, product,
finite cases, and summable decoding support that reduction.  Once terminal
outputs are added to the trace-safe `TraceRank` hypotheses, the finite rank-
and-tag skeleton argument also supports it.  This could simplify a later Lean
implementation.

It does not presently supersede the primary candidate for four reasons.

1. Its `TraceRank` clause requires selected children and backward maps to be
   trace-safe but omits the same requirement for visible terminal outputs.
   A rank-zero discontinuous terminal consumer defeats normal-form closure.
2. Its decoder normal form relies on a closed ancestry relation but, like any
   decoder, must ensure that relation semantically connects the exact input to
   the decoded output rather than merely contains the macro limits.
3. Section 8 says every prelimit source gives a coherent return with
   `epsilon=eta=0` under a definition whose source is specifically `mu^0` and
   whose reference trace is `y_infinity`.  Literally this is false:
   `y^z` differs from `y_infinity` in player 2's payoff by `z`.  The intended
   statement is an analogous source-relative prelimit return, or has
   `eta=z` against the fixed limiting reference.
4. Theorem 3's pointwise-rank arm proves only that rank cannot produce an
   inhabitant of an explicitly empty coherent-return type.  It correctly does
   not exclude a rank which exits through the exact terminal Nash consumer
   constructed in Section 7.  It is therefore a useful objective-specific
   boundary, not the broader adapter-class exclusion furnished by the
   repaired Fin4 online selector.

Theorem 2's coherent diagonal is mathematically credible once Theorem 1's
normal form carries all terminal, ancestry, compact-witness, and triangular-
decoder data.  The positive two-player terminal-Nash calculation in Section 7
is correct.  The alternative is best mined for the normal-form theorem after
repair, not substituted wholesale for the current export candidate.

## Final disposition

The Fin4 negative result and its full-behavioral proof are accepted.  The
candidate is not ready to enter `exports/` until required repairs 1--4 are
made.  After those repairs, the exact packet will be a complete ordinary-
mathematics answer in the maintained generic question's accepted-negative
sense, while leaving the separate source-preserving Fin4 consumer problem
open.

## Final literal recheck after repair

I re-read the exact revised file
`formalized/EXECUTABLE_ADAPTER_GRAMMAR_AND_CONSTRAINED_ROOT_NO_GO.md`.
All four required repairs and both minor clarifications are now present, and
the mathematical verdict is **pass**.

1. The trace syntax is now genuinely two-sorted.  `TraceG` contains only
   `CW`, `SD`, `Case`, bounded trace-visible `Rank`, and composition.
   `PostRank` is explicitly a control applied only after reconstruction and is
   excluded from the projective theorem.  This removes the previous
   trace-closure contradiction.
2. The `SD` chain is anchored by the exact equality
   `sigma_0(z|_0) = s(x)`.  Each subsequent certificate starts at the
   displayed `sigma_n` and ends at the displayed `sigma_(n+1)`, and the packet
   explicitly retains those certificates as code coordinates.  This is
   sufficient: every decoded point has one literal macro ancestry beginning
   at the named parent source, not merely at a semantically equivalent or
   independently chosen source.  The compact inverse-limit image therefore
   gives the claimed closed provenance relation.
3. `Case` is now fully specified by a finite tag set, compact witness spaces,
   closed tagged relations covering the parent, and continuous trace-safe
   branch compilers, with the child formed as their finite disjoint union.
   These data are sufficient.  Overlap is harmless because the tag is
   retained; an uncovered or merely open branch would not have been
   sufficient, and neither is allowed.
4. Every successor witness carrier `W_(k,l)` is declared compact metrizable.
   The fiber products in the ranked closure proof are therefore compact.
5. Every decoded numerical annotation now has a compact carrier or a
   prescribed exogenous compact closure in addition to its summable increment
   budget.  The projective execution spaces no longer contain the former
   unbounded constant-sequence loophole.
6. The topology behind `delta_n -> delta_infinity` is identified as the usual
   one-point compactification, and the post-limit rank argument is correctly
   stated as ordinary induction rather than as an application of the compact
   trace theorem.

I also rechecked the interfaces between these repaired clauses.  The `SD`
source equality has the correct tuple type `Sigma_I^m`; its source coordinate
is already part of every complete code `z=(x,w_0,w_1,...)`; and the endpoint
matching of the retained macro certificates makes equation (10) a genuine
ancestry rather than a decorative source label.  The `Case` constructor feeds
compact branch ports into the same composition rule used by the projective
theorem, so it introduces no hidden selector or nonclosed boundary test.

The probability and strategy calculations, equations (1)--(31), the full
behavioral cap semantics, the exact constrained-root relation `t*q=0`, the
uniform reach floor, and the compact-output no-go are unchanged and remain
correct.  The final scope is exact: the no-go excludes the specified online
constrained-face maximal selector for the declared compact/summable/bounded-
trace grammar; it does not exclude nonmaximal roots, approximate selectors,
or pointwise selection after reconstruction.

There is no remaining mathematical objection.  The only residual item visible
in the file is editorial/export metadata: the placeholder “Independent
reviews: to be inserted after final packet review” must be replaced by the
actual review record when the packet is assembled.  Subject to that ordinary
gate bookkeeping, the exact revised packet is ready as a complete answer to
the generic architecture problem in its accepted negative sense.  It remains
correctly separate from, and does not solve, the Fin4 uniform-equilibrium
instantiation.

## Gate-surface recheck: SD totality and projective diagrams

I performed a final diff-level mathematical recheck after the two last
theorem-surface repairs.  The verdict remains **pass**, now without the two
implicit interface assumptions noted by the gate.

The decoder now has `Z_0 = X` and surjective bonding maps

```text
r_(n+1,n) : Z_(n+1) -> Z_n.
```

Together with compactness, this makes the inverse-limit projection onto the
parent total: every `x in X = Z_0` extends to at least one compatible complete
code.  The already checked equality `sigma_0(x)=s(x)` then anchors every such
extension at the exact named source.  Thus SD now has both properties needed
of an adapter—literal ancestry and total availability over its parent—not
merely a correct decoder on whatever codes happened to exist.  This addition
does not alter continuity, reach, annotation, or unrestricted-cap arguments.

The projective theorem is now stated for an increasing restriction-compatible
sequence

```text
P_1 <= P_2 <= ...
```

of finite rooted `TraceG` diagrams, with shared occurrences retaining their
syntax and source-port identities.  This is the correct object.  Each
execution space `E_n` is compact by the finite grammar construction, and the
specified diagram restrictions induce continuous maps `E_(n+1) -> E_n`.
For a cofinally growing sequence of executions, restriction to each fixed
`P_d`, compactness, diagonal extraction, and continuity of restriction give
one compatible family.  There is no longer any appeal to an undefined
unbounded “visible depth” of one finite grammar term.  Surjectivity of the
global execution restrictions is not needed for this argument: the supplied
cofinal executions provide the points being restricted, and continuity is
enough to pass compatibility to their limits.

The nested-execution special case is also correct: literal restriction
compatibility directly supplies the inverse-limit family, so no subsequence
is required.

I found no new dependency or quantifier problem introduced by either repair.
The headline now retains the constrained-face qualifier and declared-SD
scope, and the three independent review links are present.  The exact revised
packet is mathematically ready for export as the accepted negative answer to
the generic architecture question, with its stated nonclaim about the Fin4
uniform-equilibrium problem unchanged.
