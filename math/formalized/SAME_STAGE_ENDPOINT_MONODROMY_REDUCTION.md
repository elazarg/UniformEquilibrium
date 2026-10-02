# Same-stage endpoint monodromy reduction

Authors: Codex Root (assembly of the mathematical argument in `COMP.md`)

Independent reviews:
[Codex Monodromy](../feedback/COMP__BY_CODEX_MONODROMY.md) and
[Codex Poincare](../feedback/COMP__BY_CODEX_POINCARE.md)

## Exact statement

Let `I` be a nonempty finite player set of cardinality `n`, and let `r` be a
quitting-game reward table. All strategies below are behavioral strategies in
the standard quitting game: before absorption the only public history is the
number of preceding all-Continue stages, and a unilateral replacement may be
arbitrary and history-dependent.

Let `z_*` be a global minimizer of total terminal-semantic debt, and assume

\[
D_*:=D(z_*)>0.
\]

Fix an actual behavioral profile `sigma`, a date `t`, and a nonsingleton
coalition `S` whose unconditional terminal mass at exactly date `t` is at
least `lambda > 0`. Let `z^+` be the terminal-semantic pair of the literal
tail beginning at date `t+1`, and put

\[
E:=D(z^+)-D_*.
\]

Assume the low-tail inequality

\[
E<\frac{\lambda D_*}{2}. \tag{1}
\]

At date `t`, a **same-stage endpoint update** by player `p` is the following
literal one-date behavioral override. Against the current profile `rho`,
choose a pure action `a` maximizing `p`'s one-row payoff at the unique live
all-Continue history of date `t` against the literal continuation payoff, and
define

\[
\widehat\rho_p(s,h)=
\begin{cases}
\operatorname{pure}(a),&s=t,\\
\rho_p(s,h),&s\ne t,
\end{cases}
\qquad
\widehat\rho_j=\rho_j\quad(j\ne p).
\]

Thus every player's complete behavior is retained before and after date `t`,
and every opponent's complete strategy is retained everywhere. Route the
marked coalition through the same Boolean coordinate update.

Then, after at most `n` preliminary endpoint updates and at most

\[
N=2^n-n-1
\]

further strict endpoint updates, one obtains one of the following.

1. **Concentrated singleton:** an actual behavioral profile having, at the
   same date, a singleton terminal atom of mass at least `lambda`.

2. **Literal closed endpoint cycle:** actual behavioral profiles

   \[
   \rho_0\longrightarrow\rho_1\longrightarrow\cdots
   \longrightarrow\rho_K=\rho_0,
   \qquad 2\le K\le N, \tag{2}
   \]

   with one common literal past and one common literal post-`t` tail. Every
   arrow changes one pure root coordinate to that player's best pure endpoint
   and has actual terminal-payoff gain

   \[
   g_k\ge \frac{\lambda D_*}{2n}>0. \tag{3}
   \]

   The routed coalition at every vertex is nonsingleton and has stage mass at
   least `lambda`.

For the mover `p_k` of edge `k`, the unrestricted terminal debt satisfies

\[
d_{p_k}(\rho_{k+1})=d_{p_k}(\rho_k)-g_k. \tag{4}
\]

Consequently, for every player `i`, the closed word has the exact circulation
account

\[
\sum_{k:p_k=i}g_k
=
\sum_{k:p_k\ne i}
\bigl(d_i(\rho_{k+1})-d_i(\rho_k)\bigr). \tag{5}
\]

For `I = Fin 4`, every minimal cycle in the second arm has `K <= 8`, the gain
floor is `lambda D_*/8`, and its quitting coalitions satisfy

\[
\bigcap_{k<K}S_k\ne\varnothing
\quad\text{or}\quad
\exists k,\ell<K:\ |S_k|=|S_\ell|=2
\ \text{and}\ S_\ell=S_k^c. \tag{6}
\]

Thus every Fin4 cycle has either a common quitter or two complementary-pair
vertices.

## Conjecture-facing change

`TerminalSemanticLiveWeightedCollisionTransfer.lean` deliberately stopped
after one reached collision update because iterating the update could have
lost the source profile or detached the routed atom. This theorem closes that
local regeneration gap in the low-tail nonsingleton arm: the operation can be
iterated on literal profiles and terminates in a concentrated singleton or a
finite source-closed cycle. On Fin4, the latter has only the two geometries in
(6).

This is a strict reduction of the nonsingleton minimum-law collision branch
retained by `Research/Quitting/NonsingletonMinimumLawLinearTransfer.lean`.
The remaining obligation is no longer arbitrary source regeneration. It is
to consume a common-host or complementary-pair horizontal cycle into an
ordered Nash--Bellman chronology, or into a checked well-founded exit.

## Definitions and assumptions

The terminal payoff `U_i(sigma)` includes payoff zero on infinite
all-Continue play. The behavioral cap `B_i(sigma)` is the supremum over every
unilateral behavioral replacement, and

\[
d_i(\sigma)=B_i(\sigma)-U_i(\sigma),\qquad
D(\sigma)=\sum_i d_i(\sigma).
\]

The stage mass is unconditional: it includes the probability of reaching
date `t` and the product-root probability of exactly the displayed coalition
quitting there. No conditioning, correlation, public randomization, or
bounded-deviation restriction is introduced.

The preliminary moves merely make all four/currently `n` root coordinates
pure. They are not claimed to be paid edges. The cycle consists only of the
later strictly profitable best-endpoint moves.

## Source correspondence

The following facts are already checked in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticLiveWeightedCollisionTransfer.lean`.

- `quittingLiveWeightedCollisionTransfer_tailEscape_or_exists_endpointGain`
  gives, at every actual nonsingleton row, either

  \[
  L E\ge mD_*/2
  \]

  or an actual endpoint gain at least `m D_*/(2n)`.
- `quittingStageCoalitionMass_le_stagePureEndpointRouted` proves that the same
  endpoint update retains a nonempty routed atom and does not decrease its
  unconditional stage mass.
- `quittingTerminalSemanticDebt_stageBestEndpoint_eq_sub_gain` proves the
  exact mover-debt identity (4) against the unrestricted behavioral cap.

The checked endpoint theorem is stated using
`quittingStagePureEndpointBehaviorDeviation`, which canonicalizes the mover's
off-path behavior. The literal one-date override used here has exactly the
same live-root sequence as that checked deviation. Since a quitting game has
only the all-Continue live history before absorption, the two deviations have
the same terminal law, terminal payoffs, marked stage mass, and mover gain.
The new formalization therefore needs one local live-root congruence lemma (or
may state the finite iteration directly for the canonical family). No
strategy-class restriction is involved.

The minimum-law causal source and sharp nonsingleton anti-diffusion adapter
are checked in
`Research/Quitting/NonsingletonMinimumLawLinearTransfer.lean`. The new
mathematics here is finite literal iteration and the Fin4 cycle geometry; it
is not a restatement of the one-row transfer theorem.

In the checked proof of
`QuittingMinimumLawCausalSuffixAtom.nonempty_tailEscape_or_routedTransferSubsequence`,
the routed-transfer arm is selected only after `TailRow` is eventually false.
With the stage scale `lambda = mu^2/8`, that negation is precisely the
low-tail inequality `E < lambda * D_*/2` used here. The currently public
`RoutedTransferSubsequence` structure does not retain this inequality as a
field. The formalization should expose it, or compose this theorem inside the
existing `hnotTail` proof branch. This is a public-interface omission, not a
new mathematical hypothesis.

No external literature theorem is used in the new finite iteration or Fin4
classification. A narrow repository search found no existing theorem with
this literal same-stage closed-cycle conclusion.

## Proof

### Same-row invariance

A same-stage endpoint update changes only one coordinate of the product root
at date `t`. Hence the probability of reaching `t`, the pre-`t` history, and
the complete tail after `t` remain literally unchanged. The checked routed
cylinder factorization says that forcing the selected coordinate divides the
old root-cylinder mass by the probability of its former action, a number at
most one. Therefore the routed stage mass does not decrease.

As long as the routed coalition is nonsingleton, every iterated state still
has stage mass `m >= lambda`, the same live mass `L <= 1`, and the same tail
excess `E`. By (1),

\[
LE\le E<\lambda D_*/2\le mD_*/2.
\]

The tail arm of the checked transfer theorem is therefore impossible. Some
player has a legal same-row endpoint gain satisfying (3). Equation (4) is
the checked fixed-opponents own-strategy identity.

### Finite literal regeneration

Sequentially replace each of the `n` root coordinates by a currently best
pure endpoint. Purity of an already treated coordinate is not undone when a
different coordinate is treated. Routing cannot make a nonsingleton
coalition empty; if it becomes a singleton, the first conclusion holds.

Otherwise the resulting root is a pure nonsingleton coalition. There are
exactly `N = 2^n-n-1` such roots. At every later state choose the strictly
profitable endpoint supplied above. A positive gain cannot retain the current
pure bit, so every strict update traverses one Boolean-cube edge. Unless a
singleton is reached, `N+1` successive visited roots contain a repetition.

After the preliminary phase, every profile equals the original complete
behavior profile at every date other than `t`; at date `t` it is indexed only
by the pure action profile used there. Hence repetition of that pure root is
equality of complete behavioral profiles, not merely equality of terminal
laws, payoffs, or semantic pairs. The minimal repeated segment is the literal
cycle (2).

Telescoping every debt coordinate around that cycle and separating the edges
on which player `i` is the mover proves (5).

### Fin4 geometry

If `K = 2`, the two vertices differ by one cube coordinate and have nonempty
intersection, so (6) holds immediately. Suppose `K > 2`. Minimality of the
repeated segment makes its vertices distinct except for the closing endpoint;
its underlying undirected cube walk is therefore a simple cycle of length at
least four. The induced four-cube graph on subsets of cardinality at least two
is bipartite. Its odd side consists of the four triples, so this simple cycle
is even and has length at most eight. Thus safely

\[
K\in\{2,4,6,8\}.
\]

Assume that the cycle contains no complementary pair vertices. Its pair
vertices form an intersecting family of edges of `K_4`; such a family is
contained in a star or a triangle. In the star case, every adjacent triple
and the full coalition contain the star center, so that player lies in every
cycle vertex.

In the triangle case the three pairs share one triple. Each pair needs two
distinct neighbors in a simple lifted cycle, which would force that common
triple to have cycle degree three or force a repeated full/triple vertex.
This is impossible. Hence only the star survives, proving (6).

## Boundary tests

- The collision assumption is essential for nonempty routing. A pair may be
  routed to a singleton, which is intentionally the first output.
- Positivity of `lambda` and `D_*` is essential for a uniform strict gain.
- The low-tail inequality is exactly what excludes the checked tail-excess
  arm. The theorem makes no claim when it fails.
- Fixing both the literal past and tail is essential. Equality of roots does
  not determine arbitrary behavioral profiles outside the canonical
  same-stage family.
- A common-host Fin4 boundary cycle is

  \[
  01,012,02,023,03,013,01.
  \]

- A complementary-pair boundary cycle is

  \[
  01,013,0123,123,23,023,02,012,01.
  \]

  It has empty total intersection and contains the complementary pairs `01`
  and `23`.

An independent exhaustive enumeration found 37 undirected simple cycles in
the induced Fin4 graph and no counterexample to (6).

## Adapter and consumer

The checked minimum-law causalization and anti-diffusion modules produce
actual reached nonsingleton rows. The checked live-weighted transfer splits
such a row into tail excess or endpoint gain. This result consumes the
low-tail gain arm without reselecting its source.

Its outputs do not yet have a final semantic consumer. The concentrated
singleton joins the maintained singleton residual. The finite cycle joins
the open first-order chronological-realization obligation. The strict change
is that the latter now has a literal regenerated source, a fixed gain floor,
length at most eight, and one of two Fin4 passports.

## Lean handoff

Suggested declarations are:

```lean
theorem exists_sameStage_singletonDrop_or_closedUniformGainCycle

theorem finFour_sameStageClosedEndpointGainCycle_commonHost_or_complementaryPair

theorem finFour_sameStageClosedEndpointGainCycle_length_le_eight
```

The first theorem should be polymorphic in the finite player type, with gain
`lambda * Dmin / (2 * Fintype.card iota)`. Define the post-preliminary finite
profile family by overriding every player's strategy at exactly the marked
date (at all histories of that date) and retaining the original strategy at
every other date. Prove that its live-root word agrees with the existing
canonical stage-endpoint deviation. Do not quotient arbitrary behavioral
profiles by live-root equality.

The Fin4 classification is a finite theorem about `Finset (Fin 4)` and may be
proved either by the star/triangle argument or checked finite enumeration.

## Scope and nonclaims

This result does not construct a chronological successor word, an admissible
punishment-floor edge, a terminal approximate equilibrium, or a uniform
payoff. The horizontal cycle consists of sibling profiles over one tail. It
does not imply the first-order periodic Bellman realization required by the
periodic two-clock consumer. It also makes no claim that a tail-excess limit
is behaviorally attained or executable.

## Formalization record

The useful finite literal content is formalized in Research modules (outside
the production umbrellas):

- `Research/Quitting/SameStageEndpointMonodromy.lean` contains the literal
  one-date override and pure-root family, the best-endpoint gain/debt bridge
  `quittingLiteralSameStage_bestEndpoint_gain_and_debt`, the local dispatch
  `quittingLiteralSameStage_dispatch`, the source-row and live-mass
  dispatchers `exists_quittingSameStage_terminalRoute_or_closedSegment_of_sourceRow`
  and `exists_quittingSameStage_terminalRoute_or_closedSegment_of_liveMass`,
  strict edge/toggle facts, the period lower bound, per-offset full edge
  certificates, literal profile updates, and
  `dispatchedClosedSegment_player_circulation`.
- `Research/Quitting/SameStageEndpointPurification.lean` contains the
  arbitrary-profile initial adapter and the explicit bounded path
  `quittingPartialPurification_exists_path_result`, its complete-assignment
  wrapper `quittingPartialPurification_exists_total_or_singleton`, and the
  composition `quittingPartialPurification_then_sameStage_dispatch`.  Every
  preliminary path edge carries its best-endpoint action certificate.
- `Research/Quitting/FinFourSameStageEndpointMonodromy.lean` contains the
  Fin4 code adapter, `finFourTrace_period_le_eight_and_geometry`, the exact
  complement bridge `finFour_disjoint_card_two_eq_complement` and
  `finFourTrace_common_or_complementary_exact`, the specialized per-offset
  `/8` gain certificate `finFourTrace_offset_gain_certificate`, the all-offset
  mass floor `finFourTrace_stageMass_ge_liveMass`, and the composed theorem
  `quittingPartialPurification_then_finFourSameStage_dispatch`.

Evidence seals:

- **M:** PASS. The packet retains its reviewed mathematical statement,
  boundary tests, and nonclaims.
- **L:** PASS. The three Research modules pass direct Lean checks and the
  named `lake build` checks; no trust constructs are used in the new files.
- **A:** PASS at the supplied-data boundary. The purification theorem starts
  from an arbitrary behavioral profile and marked nonsingleton row, while the
  dispatchers consume the resulting literal family and retain the edge,
  mass, gain, and debt certificates.
- **C:** The finite reduction itself is the named consumer of the open
  same-stage regeneration obligation. No chronological Nash--Bellman
  consumer, residual contraction, or uniform-equilibrium theorem is claimed;
  those are explicit packet nonclaims.

The result is formalized in `Research`, not integrated production. The
formalization checks the packet's finite literal reduction and Fin4 geometry;
it does not promote a horizontal endpoint cycle to a chronological strategy.
