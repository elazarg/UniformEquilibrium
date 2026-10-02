# Adversarial review of the Fin5 face-cyclic seed

Reviewer: `CODEX_RAMSEY`

Source reviewed:
[`CHATGPT_EXTERNAL__FIN5_FACE_CYCLIC_SEED.md`](../notes/CHATGPT_EXTERNAL__FIN5_FACE_CYCLIC_SEED.md)

Repository head audited: `29a172f34a919f925bd1109a55c75c9a55d4078c`

## Verdict

**PASS for the supplied five-root Green estimate; FAIL as an arbitrary-game
producer under the currently reviewed quiet-face fields.**  The constants

\[
 |u_i^t-v_i^t|\le 5\delta/\rho,
 \qquad
 D_i^t\le {5\over\rho_i}
   \left(\varepsilon+{5\delta\over\rho}\right)
\]

are correct.  They are a short adapter to the checked tail-stability and
opponent-Green declarations, not a new source theorem.

The note is also correct that the codimension-one extraction can select the
empty cell and that five reached face families need not be cyclically
compatible.  The audit below strengthens both points with exact Fin5
separation tables.  There is one useful repair: neither the contraction atom
for player `i` nor its phase needs to be the atom/phase selected on `i`'s own
quiet face.  A finite set-cover condition suffices.  Its uncovered residual,
however, has no checked same-source consumer.

The result should remain internal.  Formalization is reasonable only as a
generalized supplied-cycle adapter after the producer is useful; it is not an
export-quality contraction of the Fin5 conjecture.

## 1. Conditional Green estimate

Write

\[
 e_i^t=|u_i^t-v_i^t|,
 \qquad
 \beta_t=\Pr_{x^t}(\text{all Continue}).
\]

The affine Bellman identity gives

\[
 e_i^t\le\delta+\beta_t e_i^{t+1}.
\]

One nonempty full-root atom of mass at least `rho` at any phase makes the
five-phase survival product at most `1-rho`.  A five-step iteration therefore
gives

\[
 e_i^t\le 5\delta+(1-\rho)e_i^t,
\]

hence `e_i^t <= 5 delta/rho` for every coordinate and rotation.  The checked
`isεQuittingRootEndpointNash_of_tail_close`, together with endpoint/root-Nash
equivalence, transfers local error to

\[
 \eta_0=\varepsilon+5\delta/\rho.
\]

For actual cyclic chronology, the checked one-step account
`quittingRootSequenceTerminalDebt_le_actualCoordinateDefect_add` gives

\[
 D_i^t\le\eta_0+m_{i,t}D_i^{t+1}.
\]

If one phase contains a full-root atom `A` with `A.Nonempty`, `i notin A`, and
mass at least `rho_i`, then forcing `i` to Continue does not remove that
event.  Consequently `m_{i,t} <= 1-rho_i`.  Iterating once around the word
and using periodicity gives exactly

\[
 D_i^t\le 5\eta_0+(1-\rho_i)D_i^t.
\]

There is no missing factor two.  This controls unrestricted behavioral debt,
not merely periodic deviations.  The exact compiler invocation at zero error
is also valid when the playerwise opponent-cycle products are strictly below
one.

The quantitative consequence `alpha >= a rho/5`, and hence
`alpha >= a^2/(320M)` under `rho >= a/(64M)`, follows immediately by applying
the definition of the ambient infimum to the constructed cyclic profile.

## 2. The quietness and own-phase hypotheses are stronger than necessary

For player `i`, contraction needs only

\[
 \exists t,A,\qquad A\ne\varnothing,quad i\notin A,quad
 p_{x^t}(A)\ge\rho_i>0.                         \tag{R}
\]

It does **not** require `t=i` or `x_i^i=Continue` surely.  Since the displayed
full atom already contains the factor that `i` Continues, replacing `i` by
pure Continue weakly increases its mass.  Thus (R) implies the same opponent
contraction.  This yields the same five-phase estimate, with one possibly
different phase chosen for each player.

Suppose the quiet-face extraction chooses cells `A_t`, some empty.  Let

\[
 C=\bigcap_{t:A_t\ne\varnothing} A_t
\]

(with `C=I` if every selected cell is empty).  Every player outside `C` is
covered by a selected nonempty atom, so the cyclic Green consumer works for
those coordinates.  It works for all players exactly when `C` is empty.

The uncovered residual has a precise shape:

- every `i in C` has `A_i=empty`, because a nonempty own-face cell excludes
  its omitted owner;
- hence each such `i` has the empty-cell solo/continuation premium on its own
  reached face; and
- every selected nonempty cell on every other face contains every member of
  `C`.

This is a common-participant/solo-premium pattern, but it is not a checked
consumer.  The solo comparison is at `i`'s reached face, while the atoms
containing `i` and their join gains belong to other omitted owners at other
reached sources.  No common continuation, punishment floor, cap root,
Bellman edge, or chronology aligns them.  The Fin4 solo-wall and
singleton/pair-base consumers require precisely such additional fields; the
acyclic solo-preemption theorem requires global singleton/pair sign data.

## 3. Exact empty-cell separation

The reviewed quiet-face fields do not force any nonempty atom at the selected
row.  Let `I=Fin 5` and define the rational reward table

\[
 r_i(S)=\begin{cases}|S|,&i\in S,\\0,&i\notin S.\end{cases}              \tag{E}
\]

For each omitted player `t`, let `J=I\setminus\{t\}`.  In the deleted game,
use the two-date profile:

- at date zero every member of `J` Continues;
- conditional on survival, at date one every member of `J` Quits.

This is an exact unrestricted terminal Nash profile of the deleted game.
Waiting pays each survivor `4`; quitting at date zero pays `1`; at date one
quitting pays `4`, whereas continuing leaves a coalition excluding that
player and pays `0`.

In the quiet ambient lift, omitted `t` receives zero.  Quitting at date zero
gives its singleton payoff `1`.  Thus the full outward gain is carried by
the empty first-row cell of mass one.  The row itself is literally
all-Continue and has no nonempty root atom at all.

Table (E) has the exact all-Quit equilibrium, so it is not a counterexample to
the conjecture.  It is an exact separation of interfaces: the local data used
by codimension-one extraction, including actual reached provenance and exact
survivor equilibrium, cannot imply a nonempty source atom.  Global positive
minimum would have to supply a genuinely new implication, not a strengthening
of the reviewed row argument.

The empty branch also has no source-native compiler from its stated fields.
It says only `r_t({t})-v_t>0`.  The sign of the singleton itself, punishment
floor, and every survivor payoff on a coalition containing `t` are free.
Those latter rows can be perturbed without changing the quiet source or
`t`'s displayed gain, while making any proposed positive activation of `t`
create arbitrary survivor regret.  This is the operational reason the
checked macroscopic-repair estimate gives a cost rather than a consumer.

## 4. Five reached families do not produce cyclic scalar annotations

A second exact table separates the alignment issue even when nonempty atoms
collectively cover all players.  Put

\[
 r_i(S)=1
 \quad\text{iff}\quad
 (S=\{i\})\ \text{or}\ (|S|=4\text{ and }i\in S),                    \tag{A}
\]

and put every other coordinate equal to zero.  Fix `p=1/2`.  On face `t`, set
`a=t+1 mod 5` and use this deleted-game profile:

- at date zero only `a` Quits, with probability `p`;
- conditional on survival, all four survivors Quit at date one.

It is an exact unrestricted terminal Nash profile.  Player `a` is indifferent
between its singleton payoff `1` and the size-four tail payoff `1`.  Every
other survivor obtains `1-p` both by Continue and by immediate Quit.  At date
one, quitting pays `1` and unilateral Continue pays `0`.

The omitted player `t` receives zero in the quiet lift and gains `1-p=1/2`
by immediate Quit.  The positive cell is again only the empty cell: its gain
is `1`, while the nonempty cell `{a}` has mass `p` and join gain zero.
Nevertheless `{a}` is a genuine nonempty root atom of mass `1/2`.  Across the
five phases these singleton atoms have empty common intersection, so they
cover every player for the generalized Green contraction.

Now periodically repeat the five date-zero roots.  For a fixed player `i`,
write phase `i-1` for the phase on which `i` is the active mixer.  The unique
cyclic Bellman value satisfies

\[
 u_i^{i-1}=p+(1-p)u_i^i,
 \qquad
 u_i^i=(1-p)^4u_i^{i-1}.
\]

At `p=1/2`,

\[
 u_i^{i-1}={16\over31},\qquad u_i^i={1\over31}.
\]

Thus at its active phase player `i` has Quit endpoint `1` and Continue
endpoint `1/31`.  The mixed root has coordinate Nash defect

\[
 {1\over2}\left(1-{1\over31}\right)={15\over31}>0.                 \tag{B}
\]

Because the five-phase survival product is `1/32<1`, the cyclic Bellman
annotation is unique.  Hence no alternative exact scalar annotation repairs
(B).  We have five exact, finitely reached, same-table quiet-face root
families and a uniform nonempty atom cover, but no exact cyclic root-Nash
system.

This proves that coordinatewise endpoint dependence does not align the five
sources.  What is missing is a relation between each locally selected tail
coordinate and the actual periodic continuation produced by the other four
roots.  The finite affine-interval theorem can certify that failure, but it
does not produce compatibility.

## 5. Scalar feasibility and source audit

`finiteAffineIntervalFeasible_iff` has exactly the endpoint/cross-product
content stated in the note.  Once a cyclic scalar problem is cut, its rows may
indeed include face endpoint inequalities, box bounds, and closing-seam
inequalities.  Nothing in the checked theorem removes the latter two row
types.  The note is right not to reinterpret every certificate as two literal
face rows.

The checked declarations used by the valid consumer are:

- `quittingRootSequenceTerminalDebt_le_actualCoordinateDefect_add` and the
  opponent-Green telescope in `Quitting/Root/TerminalDebtGreenAccount.lean`;
- `isεQuittingRootEndpointNash_of_tail_close` in
  `Quitting/Root/TailStability.lean`;
- `isεQuittingRootNash_iff_coordinateNashDefect_le` in
  `Quitting/Root/NashDefect.lean`; and
- `isZeroAsymptoticNash_quittingCyclicBehaviorProfile_of_certificate` in
  `Quitting/Cycles/PeriodicCompiler.lean`.

No checked declaration found in the named deletion, Green, periodic, or solo
subtrees turns an empty selected face cell into a nonempty actual atom, aligns
five reached tail coordinates, or consumes the common-intersection residual.

## 6. Recommendation

Retain the note as an honest supplied-verifier draft.  If an adapter is
formalized, state the more general condition (R), not own-face quietness.
The conjecture-facing producer now has two independent obligations:

1. eliminate or consume the common-intersection/empty-cell residual; and
2. align the reached continuation thresholds with the unique cyclic Bellman
   values (or consume the affine seam/box obstruction).

The examples (E) and (A) show that neither obligation follows from the
currently reviewed quiet-face data.  Export is not recommended.
