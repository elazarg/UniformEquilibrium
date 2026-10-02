# Zero-debt atom-preserving pure-time selection

Identity: `CODEX_ROOT`

Status: ordinary mathematics; not checked in Lean; not a chamber consumer.

## Question

Let `sigma_n` be one source-attached sequence of actual quitting profiles,
let `o` be fixed, and suppose

\[
d_o(\sigma_n)\longrightarrow0.
\]

Assume one fixed terminal coalition `S` retains positive mass:

\[
\Pr_{\sigma_n}(S)\longrightarrow m>0.
\]

Can one choose one pure stopping-time completion of `o` which retains both
the atom and the vanishing unrestricted debt?  Yes.  The selection uses the
two mixture identities simultaneously; it does not first select a large atom
and then infer strategic quality.

## Lemma 1: abstract cap-and-exposure selection

Let `pi` be a probability law on a finite or countable set `Q`.  Let

\[
0\le A(q)\le1,\qquad V(q)\le B,
\]

and put

\[
m=\mathbb E_\pi A,
\qquad
d=B-\mathbb E_\pi V
  =\mathbb E_\pi(B-V).
\]

For every `epsilon > 0`, there is a point in the positive `pi`-support such
that

\[
B-V(q)\le\epsilon,
\qquad
A(q)\ge m-\frac d\epsilon.
\tag{1}
\]

The second inequality is useful when its right side is positive.

### Proof

Put

\[
G=\{q:B-V(q)\le\epsilon\}.
\]

Markov's inequality gives

\[
\pi(G^c)\le d/\epsilon.
\]

Since `A <= 1`,

\[
\mathbb E[A1_G]
\ge m-\pi(G^c)
\ge m-d/\epsilon.
\]

Some point of the positive support in `G` has `A(q)` at least the last
quantity.  This proves (1).  When `d=0`, the same proof says that every
positive-support point is cap-attaining and one of them has exposure at
least `m`.

## Lemma 2: quitting-game form

Let `pi` be player `o`'s complete stopping-time law in an actual behavioral
profile `sigma`.  For `q in N union {Never}`, let `sigma[q]` replace only
`o` by the pure stopping time `q`.  For a fixed terminal coalition `S`, set

\[
V(q)=U_o(\sigma[q]),
\qquad
A(q)=\Pr_{\sigma[q]}(S).
\]

Pure-time extremality and the stopping-law mixture identity give

\[
B_o(\sigma)=\sup_qV(q),
\qquad
U_o(\sigma)=\mathbb E_\pi V,
\qquad
\Pr_\sigma(S)=\mathbb E_\pi A.
\tag{2}
\]

Changing only `o` leaves its unrestricted cap unchanged.  Lemma 1 therefore
gives a pure completion `q` such that

\[
d_o(\sigma[q])\le\epsilon,
\qquad
\Pr_{\sigma[q]}(S)
\ge \Pr_\sigma(S)-\frac{d_o(\sigma)}\epsilon.
\tag{3}
\]

This holds for an arbitrary coalition `S`; `o` need not belong to `S`.

For a sequence with `d_o(sigma_n) -> 0`, choose positive `epsilon_n -> 0`
with

\[
d_o(\sigma_n)/\epsilon_n\longrightarrow0
\]

(for example, use the square root when the debt is positive and a harmless
vanishing fallback when it is zero).  Then there are actual targets
`tau_n=sigma_n[q_n]` with

\[
d_o(\tau_n)\longrightarrow0,
\qquad
\liminf_n\Pr_{\tau_n}(S)\ge m.
\tag{4}
\]

The opponents are literally unchanged, and

\[
B_o(\tau_n)=B_o(\sigma_n)
\]

exactly.  Thus this construction retains atom exposure and owner cap
tightness on the same actual completion.

## Lemma 3: finite-time versus escaping-time split

After passing to a subsequence, the selected pure times have exactly one of
two forms.

1. They are one fixed finite time `q`.
2. They escape to `Never` in the one-point compactification (including the
   literal-Never subsequence).

In the first case, terminal coalition `S` occurs no later than `q`.  If
`o in S`, it can occur only at `q`; if `o notin S`, it occurs strictly before
`q`.  Hence a further finite pigeonhole selection gives one fixed actual
date with a positive stage-mass floor and still

\[
d_o(\tau_n)\to0.
\tag{5}
\]

This branch also removes almost all compactness ambiguity.  After taking
limits of the finitely many roots through date `q`, prescribed payoffs are
continuous.  For every player `i != o`, every unilateral deviation is
preempted by `o`'s sure Quit at `q`; hence `i`'s unrestricted cap is the
maximum of finitely many deadline values and is continuous as well.  Only
the selected owner's cap can still jump: an `o`-deviation removes the sure
deadline and may inspect an escaping opponent tail.  Thus the bounded branch
reduces possible cap leakage to one named coordinate, rather than all four.

The second case is an honest timing-boundary branch.  No bounded marked row
follows from (4) alone.

## Application to reset rigidity

At a reset-rigid minimum point, the returned owner has zero debt and the
retained law has a positive finite atom (indeed a positive opponent-incidence
atom).  Apply Lemma 2 to the same realizing sequence.  This produces an
actual source-attached family with:

- one pure stopping-time owner;
- the same owner cap asymptotically and vanishing owner debt;
- a fixed positive terminal atom; and
- all opponents unchanged.

The bounded-time branch additionally supplies a fixed reached row.  The
escaping-time branch isolates the remaining bubble/deletion boundary.

This removes one possible alignment objection: in the reset chamber, atom
retention and owner near-optimality can be selected simultaneously.  It does
**not** control the other three caps.  A compact target cluster can lie
strictly above the global minimum, and even a minimum-level target need not
preserve any other zero-debt coordinate.  Therefore this is a useful reset
source refinement, not a solution of
`questions/FIN4_RESET_RIGID_CHAMBER_CONSUMER.md`.

## Existing-source audit

The ingredients inspected were:

- pure-time extremality and the stopping-law mixture interfaces in
  `UniformEquilibrium/Quitting/Terminal/BehavioralPureTimeBestResponse.lean`
  and `BehaviorStoppingLaw.lean`;
- `formalized/FIN4_MINIMUM_SINGLETON_CLOCK_COMPRESSION.md`;
- `notes/CODEX_ROOT__INCENTIVE_AWARE_SINGLETON_CLOCK_COMPRESSION.md`;
- `notes/STRENGTHENER__JOINT_EXPOSURE_INCENTIVE_SELECTION.md`; and
- the off-diagonal rectangle selection in
  `StoppingLaw/OffDiagonal/AtomRectangleSequenceAlternative.lean`.

The existing conference results select singleton exposure plus incentive, or
an atom arising from a tangent rectangle.  I did not find the elementary
arbitrary-terminal-event statement (3)--(5) packaged at the reset-rigid
source.  Before export it would need a narrow duplicate audit and an
independent check of the exact stopping-law event-mixture identity.

## Next question

In the fixed-finite-time branch, can the positive bounded row and vanishing
owner debt be converted into a minimum-level unilateral transition while
bounding the other three cap changes?  In the escaping branch, does bounded
exact-block capacity force literal Never deletion or an all-player escape
account with a consumed sign?
