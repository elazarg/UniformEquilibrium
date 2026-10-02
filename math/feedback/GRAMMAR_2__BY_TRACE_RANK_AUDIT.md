# Trace-rank audit of `GRAMMAR_2.md`

## Post-edit re-audit of `GRAMMAR.md`

### Verdict

The edited Sections 5--8 repair the substantive objection in the original
audit.  The rank-tagged counterexample in Section 6 is now correctly typed at
the node level, and clauses 3, 5, and 7 of the new `TraceRank(K)` definition
put terminal legality, successor-tag legality, the selected child, and every
trace-visible output into full closed tagged relations.  Under the note's
standing convention that all varying auxiliary witnesses lie in their
declared compact metric spaces, these hypotheses suffice for Theorem 6.

Consequently the rank-one counterexample below no longer instantiates
`TraceRank(1)`: its tag-`a` full successor relation contains exactly the
parents with `mu(0) > 0`, so it is not closed at `delta_infinity`.  Making its
closure contain the limiting tag-`a` tuple would make tag `a` legal at the
limit and would thereby supply exactly the limiting execution that the old
example withheld.

With the repaired Theorem 6, the rank step in Theorem 7 is also valid.  The
common execution sequence and input tightness reconstruct the root once;
countable diagonal extraction handles the recorded compact witnesses and
finite tags; closed full branch relations preserve each fixed ranked
evaluation; and restriction compatibility makes the limiting finite
executions share that root.  Thus the conclusion is genuinely one root
controller supporting a compatible family of actual executions, not one
independently selected controller per diagram.

I found no remaining mathematical counterexample to the ranked or
one-controller claims under the intended complete-certificate reading.  The
following small clarifications would make the repaired proof literal.

1. In Section 6, define `Outcome(P_mu)` and `Outcome(C_nu)` to be the
   singleton type and record the unique backward map
   `Outcome(C_{F(mu)}) -> Outcome(P_mu)`.  The rank tags fix the earlier node
   inconsistency; this one sentence makes every field of (44) explicit.
2. In the proof of Theorem 6, produce convergence of the selected children by
   their `TraceEdge` certificate **before** invoking closedness of a full
   tagged relation that contains the child coordinate.  Concretely, from
   `(x_m,b,w_m,y_m) in R_{k,b,ell}`, first obtain
   `y_m -> y=G(x,w)` from the closed trace-edge domain and modulus, and then
   pass `(x_m,b,w_m,y_m)` to the closed-relation limit.  The present prose
   states these two valid steps in the opposite order.
3. Say explicitly that a “complete tagged terminal relation” includes every
   varying terminal witness, and that these witnesses use compact carriers.
   Otherwise a hidden noncompact witness could escape even when its
   unprojected graph is closed.  The global compact-auxiliary convention at
   the start of the note appears intended to supply this fact.
4. Add the compact `TraceRank` branch-witness spaces to the witness list in
   Theorem 7's extraction paragraph.  They are required by clause 5 and are
   covered by the broad hypothesis that compact witnesses are recorded, but
   are currently omitted from that displayed bookkeeping list.
5. Read decoder hypothesis 7 of Theorem 7 as importing the fixed-inner-column
   convergence requirement stated after (40).  If triangular decoders are
   meant to be allowed directly by that theorem, it would be clearer to name
   this condition again in hypothesis 7; uniform seam tails alone do not
   identify the outer decoder limit.
6. Hypothesis 8 can be presented as a conclusion of the common diagonal
   extraction rather than an assumption about “the extracted subsequence.”
   Finiteness of each recorded tag set is what supplies the stabilization.

Subject to these literalizations, the repaired proof is sound: finite tags
and bounded rank reduce every visible evaluation to finitely many closed,
trace-safe compositions; no uniform rank bound across all later diagram
occurrences is needed because Theorem 7 proves convergence one fixed finite
`P_k` at a time.

### Post-edit proof check for Theorem 6

Fix a convergent sequence of rank-`k` executions.  Pass to a subsequence with
one successor tag `b` and child rank `ell < k`.  Compactness gives convergence
of the complete recorded branch-witness bundle.  The `TraceEdge` certificate
for the selected child gives an actual limiting child and convergence of the
child source ports.  Closedness of the full tagged successor relation then
preserves branch legality, including the parent, tag, witnesses, rank, and
child.  Apply the induction hypothesis at `ell`.  A terminal subsequence is
handled in the same way by the full closed terminal relation and any
trace-visible terminal compiler.  Since ranks strictly decrease in
`{0,...,K}`, at most `K` successor steps occur.

This proves exactly the finite-rank trace closure that failed in the earlier
draft.  It also explains why closedness of the untagged rank stratum alone was
insufficient.

### Post-edit proof check for Theorem 7

For the countable union of finite diagrams, enumerate every persistent
witness and discrete tag.  Successive compact/finite extraction followed by
the usual diagonal subsequence gives simultaneous convergence or
stabilization.  For a fixed finite `P_k`, topological induction applies the
elementary tight-fusion theorem, Lemmas 1--2, Theorem 3, closed finite cases,
and the repaired Theorem 6.  Therefore every limiting edge is legal and every
source port is actual.  Because the finite executions before the limit are
literal restrictions of the same `E_m`, shared witness and source coordinates
have the same limits; hence the limiting executions restrict as in (56).
The root was reconstructed once from the common root sequence, so all of them
use the same stopping law and its canonical behavioral compiler.

The original negative audit is retained below as the falsification record for
the earlier `GRAMMAR_2.md`.  Its counterexample is now a useful test showing
that the strengthened full tagged-relation clause is doing essential work.

## Status and verdict

This review checks Sections 5--8: the pointwise `RankProducer`, the rank-one
counterexample, `TraceRank(K)`, and the coherent executable diagonal.  The
conclusions are ordinary mathematics, not Lean-checked declarations.

Theorem 4 is a sound pointwise well-founded-recursion theorem once “recursive
execution” means the successor selected by the supplied `dispatch` datum.
Section 6 also identifies the right obstruction: an actual lower-rank child at
each source need not vary continuously or have a closed graph.

Theorem 6 is false for the displayed definition of `TraceRank(K)`.  The
definition requires closed terminal predicates, but it never requires a
successor-branch predicate, the tagged dispatch graph, or the full
parent-to-child branch relation to be closed.  A branch tag can be constant on
the approximating sequence and cease to be a legal tag at the limit.  The
proof sentence “Closedness preserves the chosen branch at the limit” therefore
uses a missing hypothesis.

The same rank-one example below satisfies all nine hypotheses listed for
Theorem 7 (with the non-rank clauses vacuous) and has no limiting execution
whose child trace is the limit of the finite child traces.  Thus the complete
coherent-diagonal and one-controller-execution conclusion is also false as
stated.  Tight fusion still reconstructs one actual **root** controller; what
fails is the claim that this controller supports a legal limiting execution of
every admitted `TraceRank` occurrence.

The minimal repair is to require the complete relation for every recorded
terminal or successor tag to be closed, including parent node, tag, child
rank, branch witness, selected child, and every trace-visible evaluated
output.  Merely requiring the child compiler, considered away from the branch
test, to be a `TraceEdge` is insufficient.

## Claim audited

The intended ranked part of the grammar makes three successively stronger
claims.

1. Supplied terminal consumers, strictly lower selected children, and backward
   outcome maps produce an outcome at each individual node.
2. If ranks are bounded and each selected child is produced by a trace edge,
   the whole ranked evaluation commutes with stopping-law limits.
3. Consequently a common restriction-compatible sequence of executions of
   increasing finite diagrams has one projective limiting execution from one
   limiting root controller.

The first claim survives.  The second and third fail for the literal
`TraceRank(K)` certificate.

## 1. Pointwise `RankProducer`: valid but narrowly scoped

Theorem 4 follows by strong induction on `rho(N)`.  A terminal branch is
consumed at `N`; a successor branch invokes the induction hypothesis at its
strictly lower-rank child and applies the supplied backward map.  A strictly
decreasing sequence of natural numbers starting at `rho(N)` has at most
`rho(N)` transitions.

Two scope qualifications should be made explicit.

* The bound applies to the recursion selected by `dispatch`.  The data do not
  say that every otherwise legal `Exec` transition decreases rank.
* Corollary 5 is correct for the directed graph of **selected dispatch
  successors**.  If “component” means a component of a larger legal-transition
  graph, it need not be acyclic.  The final “renewable exit” wording should
  retain the selected-dispatch qualification.

This is supplied-object verification.  Neither Theorem 4 nor Corollary 5
produces `rho`, `dispatch`, a terminal certificate, an actual child, or a
backward outcome map from arbitrary quitting-game data.

## 2. Section 6 has the right example, with one typing repair

The discontinuous selector

$$
F(\mu)=
\begin{cases}
\delta_0,&\mu(0)>0,\\
\delta_\infty,&\mu(0)=0
\end{cases}
$$

correctly proves that pointwise actual construction plus rank decrease does
not imply trace closure.  To make it literally instantiate (41)--(44), the
nodes should be rank-tagged copies rather than saying both that “every source
has rank 1” and that a child source has rank 0.  For example, take

$$
\mathcal N
=
\{P_\mu:\mu\in\mathsf S\}
\sqcup
\{C_\nu:\nu\in\mathsf S\},
\qquad
\rho(P_\mu)=1,
\quad
\rho(C_\nu)=0.
$$

Dispatch `P_mu` to `C_{F(mu)}`, and give every `C_nu` the singleton terminal
outcome.  The actual `Exec` certificate can be complete replacement of the
sole player's stopping law.  This makes the example fully typed without
changing its calculation.

## 3. Exact counterexample to Theorem 6

Use the rank-tagged node space just displayed.  Equip it with the following
literal `TraceRank(1)` data.

* The rank-one node relation is all
  `\{P_mu : mu in S\}` and the rank-zero node relation is all
  `\{C_nu : nu in S\}`.  Both relations are closed.
* Rank zero has one terminal tag, valid everywhere.  Its terminal predicate is
  closed and its outcome may be the constant singleton trace.
* Rank one has two recorded successor tags `a` and `b`, both selecting child
  rank zero.
* On tag `a`, the selected-child trace edge is the constant map
  `P_mu -> C_{delta_0}`.  On tag `b`, it is the constant map
  `P_mu -> C_{delta_infinity}`.  Each constant map is a `ClosedSelect`
  instance with a singleton witness space and hence is a `TraceEdge`.
* The dispatcher uses tag `a` when `mu(0) > 0` and tag `b` when `mu(0) = 0`.

This satisfies the six displayed requirements in Section 7: the node strata
are closed; the tags are finite and recorded; the only terminal predicate is
closed; both successors lower rank; both selected children are trace edges;
and the terminal output is constant.  What is not closed is the unrequested
tag-`a` branch predicate.

Now set

$$
\mu_m
=
\frac1m\delta_0
+
\left(1-\frac1m\right)\delta_\infty,
\qquad
\mu_m\longrightarrow\mu_\infty:=\delta_\infty.
$$

Every finite execution records tag `a` and child `C_{delta_0}`.  Thus every
subsequence with stabilized tag has the same child-trace limit
`C_{delta_0}`.  At the limiting parent `P_{delta_infinity}`, however, the only
legal dispatch tag is `b`, whose child is `C_{delta_infinity}`.  The two child
laws have total-variation `l1` distance two.  No legal limiting ranked
execution realizes the trace limit.

The induction in Theorem 6 cannot start its recursive call on the stabilized
tag: although the tag is constant along the sequence, its branch is not legal
at the limiting node.  Closedness of the untagged rank-one node stratum says
nothing about this.

## 4. Consequent counterexample to Theorem 7

Take every `P_m` to be the same one-edge rooted `TraceRank(1)` diagram above,
or extend it only by irrelevant constant edges.  Let `E_m` be its execution at
root `mu_m`.

All hypotheses listed under Theorem 7 hold under their literal wording.

* The common-execution and restriction conditions hold because the diagram is
  fixed.
* The root laws have all finite-coordinate and Never-coordinate limits.  They
  are uniformly tight: all finite mass is at date zero.
* There are no suffix, `LawMin`, or decoder occurrences.
* The syntax and port names are fixed.
* The successor tag is constantly `a` along the entire sequence.
* The visible rank is the fixed bounded rank one, and the construction meets
  the displayed `TraceRank(1)` definition.

Theorem 7 would have to produce an actual execution at root
`delta_infinity` whose child trace is `delta_0`, because the finite child
traces are identically `delta_0`.  No such execution is legal.  Its only legal
selected child is `delta_infinity`.

Therefore the root reconstruction and the full executable-diagonal claim must
be separated:

* tight fusion does reconstruct the single actual root law
  `delta_infinity`, hence a single canonical behavioral controller; but
* the allowed ranked edge does not commute with that reconstruction, so there
  is no compatible limiting execution of the claimed grammar.

This is enough to falsify Theorem 7 as a whole.  It does not falsify the
narrower statement that all successfully reconstructed finite diagrams share
one root once every edge relation has independently been proved trace-safe.

## 5. Repair that makes the rank induction work

For every rank `k`, terminal tag `b`, successor tag `b`, and child rank
`ell < k`, require closed full branch relations of the form

$$
R^{\mathrm{term}}_{k,b}
\subseteq
X_k\times W^{\mathrm{term}}_{k,b}\times Y_{k,b},
$$

and

$$
R^{\mathrm{succ}}_{k,b,\ell}
\subseteq
X_k\times W^{\mathrm{succ}}_{k,b,\ell}\times X_\ell.
$$

Here the witness spaces are compact, and the relations must include all facts
needed for that recorded tag to remain a legal branch.  Any terminal consumer,
backward compiler, or evaluated rank outcome that is exposed as a downstream
port must also occur in this closed relation or be produced by a separately
certified `TraceEdge`.

With finitely many tags and bounded rank, pass to a subsequence with a fixed
tag and child rank.  Compactness gives a convergent branch witness; closedness
of the **full tagged branch relation** keeps the tag legal at the limit; the
child trace edge commutes; and induction applies at the lower rank.  This is
the missing argument in Theorem 6.

For a deterministic dispatcher, the same condition can be phrased as a closed
graph for the complete tagged dispatch.  A multivalued closed branch relation
is more flexible: at a boundary it may retain the approximating branch even
if another branch is also legal.

After replacing `TraceRank(K)` by this strengthened definition, the rank part
of Theorem 7 has the intended finite-depth proof.  The theorem should also say
whether the evaluated rank outcome is part of `Tr_P`.  If it is, its terminal
and backward transport are mandatory trace edges; if it is not, the ranked
construction cannot be advertised as a compositional trace-output edge.

## 6. Strongest surviving statement

The following boundary survives this audit.

1. Pointwise `RankProducer` data give a finite selected execution and an
   outcome after one actual limiting node has already been reconstructed.
2. Pointwise rank data alone have no limit-commutation consequence; Section 6
   gives the right rank-one obstruction after the node typing is repaired.
3. Bounded rank plus trace-safe child maps is still insufficient unless the
   complete tagged branch relations are closed.
4. Bounded rank, finite recorded tags, closed full branch relations, and
   trace-safe terminal/child/backward outputs do yield finite-rank trace
   closure by induction.
5. Under that repair, the common restriction-compatible tight-fusion setup
   does preserve one reconstructed root controller across all finite
   diagrams.  No rank or grammar theorem here produces the required
   executions from arbitrary quitting-game data.

## Requested author check

Decide whether a successor tag's legality predicate was intended to be part
of its `TraceEdge` domain.  If so, put that requirement in the definition of
`TraceRank(K)` and formulate the full tagged relation explicitly; the tag-`a`
edge above is then rejected because its intended domain `mu(0) > 0` is not
closed.  Re-run the proof with the complete tagged relation rather than the
untagged rank stratum as the closed set.

## Sources inspected

* `meta/GRAMMAR_2.md`, especially Theorems 4, 6, and 7;
* `meta/EXECUTABLE_COMPACT_STATE.md`, especially Theorem 1 and its definition
  of a rooted elementary program;
* `feedback/GRAMMAR__BY_DIAGONAL_AUDIT.md`; and
* `feedback/EXECUTABLE_ADAPTERS__BY_DIAGONAL_AUDIT.md`.

`meta/GRAMMAR.md` was not present in the conference directory during this
audit.  The earlier audit of that note was available and was used only to
identify the claimed repair boundary; the counterexample and verdict above
are checked directly against `GRAMMAR_2.md`.
