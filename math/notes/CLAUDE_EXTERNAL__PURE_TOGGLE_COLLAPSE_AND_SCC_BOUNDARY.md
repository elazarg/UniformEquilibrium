# Pure-toggle collapse and the SCC boundary

Source: Claude

## Current status

The central collapse is correct: after the `COMP.md` purification reaches a
pure nonsingleton root, the tail is semantically irrelevant and every
same-stage endpoint update is exactly an improving membership toggle in the
finite coalition game.  This materially simplifies the interpretation of the
monodromy.

The proposed condensation/SCC construction is a useful finite normal form but
is not yet a well-founded semantic exit.  In particular, it does not by itself
produce a minimum-fiber support drop or a uniform-equilibrium payoff.  The
claimed choice-free Fin4 trichotomy also does not pass from an individual
simple cycle to an arbitrary terminal SCC.

## Exact collapse

For a coalition `A`, let `sigma_A` be the stationary pure-set profile.  With
the convention `r_i(emptyset)=0`, the checked theorem
`quittingTerminalSemanticDebt_pureSetRoot_eq` gives

\[
d_i(\sigma_A)
=\max\{r_i(A\cup\{i\}),r_i(A\setminus\{i\})\}-r_i(A)
=\bigl(r_i(A\mathbin\triangle\{i\})-r_i(A)\bigr)_+.
\]

For a pure nonsingleton root placed at a reached date above an arbitrary tail,
the same formula applies: after any unilateral behavioral replacement, at
least one other prescribed quitter remains, so absorption still occurs at
that date.  Thus the past contributes only a common reach factor and the tail
is never visited.

If player `p` makes a strict best-endpoint update

\[
A\longrightarrow A\mathbin\triangle\{p\},
\qquad
g=r_p(A\mathbin\triangle\{p\})-r_p(A)>0,
\]

then

\[
g=d_p(\sigma_A),
\qquad
d_p(\sigma_{A\triangle\{p\}})=0.
\]

Consequently, after the preliminary purification in `COMP.md`, the literal
endpoint cycle is a better-reply cycle of the finite membership game
`A |-> r(A)`.  The low-tail inequality and routed collision mass are needed
to justify the earlier reached-row dispatch, but not to analyze the resulting
pure nonsingleton cycle.

If `D_*` is the positive global minimum of total semantic debt, every pure-set
profile is an actual profile and therefore

\[
D_*\le
\sum_i\bigl(r_i(A\triangle\{i\})-r_i(A)\bigr)_+
\qquad(A\subseteq I).
\]

In particular, some improving toggle at every vertex has gain at least
`D_*/|I|`.  Under a terminal exploitability witness, the repository already
checks the corresponding uniform toggle instability directly in
`UniformEquilibrium/Quitting/Classification/TerminalExploitabilityToggles.lean`.

## Terminal SCC normal form

Orient the Boolean cube by the strict improving toggles

\[
A\to A\triangle\{i\}
\iff r_i(A\triangle\{i\})>r_i(A).
\]

If the game has no sure-exit set, every vertex has an outgoing edge.  The
condensation is a finite DAG and therefore has a terminal strongly connected
component.  Such a component is closed under every improving toggle and is a
stronger finite recurrent object than one selected minimal cycle.

This is a finite normalization, not yet a semantic rank exit:

* there may be several terminal SCCs;
* an improving path can stay inside a nonterminal SCC unless an outgoing edge
  is deliberately selected;
* arrival at a terminal SCC does not lower terminal debt or positive-debt
  support; and
* no existing compiler consumes an arbitrary terminal toggle SCC.

## Failure of the choice-free Fin4 trichotomy

The common-host/complementary-pair dichotomy is valid for each minimal simple
cycle.  It need not hold for the union forming a terminal SCC.  For example,
consider the two directed cycles

\[
12\to123\to13\to134\to1234\to124\to12
\]

and

\[
13\to134\to1234\to234\to23\to123\to13.
\]

Their union is strongly connected, has empty intersection, and its pair
vertices are `12`, `13`, and `23`, so it contains no complementary pair.  A
quitting reward table can orient the remaining boundary cube edges inward,
because each Boolean edge compares one player's rewards at its two endpoints.
Thus an empty frozen set for a terminal SCC does not imply that the SCC itself
has a complementary-pair passport, even though each displayed simple cycle
has a common host.

## Persistent-host output

If a selected cycle has a common host `h`, solving the finite induced game of
the remaining players while `h` quits surely produces an actual stationary
profile whose only possible positive debt is `h`'s.  This is a useful
singleton-debtor source, but it is not a minimum-fiber support decrease:

* the profile is reselected rather than obtained as a minimum-fiber endpoint;
* its total debt may be strictly larger than `D_*`;
* the construction is available for an arbitrary chosen persistent singleton
  base and does not itself use the SCC recurrence; and
* the maintained singleton-debtor branch is not yet consumed.

A genuine rank exit still requires an actual endpoint on the minimum fiber,
no entry of a previously inactive debt coordinate, and disappearance of at
least one previously active coordinate.

## Chronological consequence

The pure cycle cannot itself be read as an ordered chronology: every
nonsingleton pure root absorbs immediately, so no play path reaches the next
vertex.  The elementary estimate

\[
\Pr(\{1,2\})\ge\Pr(\{1\}),\Pr(\{2\})
\Longrightarrow q_1,q_2\ge\tfrac12
\Longrightarrow \Pr(\text{all Continue})\le\tfrac14
\]

shows that retaining dominant fixed-scale pair collisions through `K` dates
costs survival at most `4^{-K}`.

This rules out a literal fixed-mass temporal reading.  It does not rule out a
mixed small-clock realization in which nonsingleton mass vanishes with the
scale.  Producing such an approximate chronology, or proving that its failure
gives a minimum-fiber rank exit, remains open.

## Resulting question

Consume a terminal recurrent class of the Fin4 membership-toggle graph --
possibly a union of differently hosted cycles -- into one of:

1. terminal approximate equilibria or an admissible charged return;
2. an actual minimum-fiber endpoint with strict positive-debt support loss; or
3. a smaller executable residual carrying enough source provenance to repeat
   the argument.

