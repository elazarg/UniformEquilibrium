# Sufficient-state boundary

The state problem separates into three questions:

1. what information is sufficient for exact legal updates;
2. which topology makes those updates stable and compact; and
3. whether the resulting transition system has a global terminal or recurrent
   consumer.

The first question has a sharp answer for unilateral replacement. The second
has a sharp obstruction for calendar suffixes. The third remains open.

## Exact information classification

Let \(\mathcal K_k\) retain the labelled terminal-coalition law after every
pure stopping-time intervention on at most \(k\) players.

For \(n\) players:

\[
\begin{array}{c|c}
\text{task}&\text{least order established in this hierarchy}\\ \hline
\text{current prescribed payoff}&0\\
\text{current unrestricted behavioral caps}&1\\
\text{one update of an order-}k\text{ state}&k+1\\
\text{recursive unilateral replacement}&n-1.
\end{array}
\]

The order-\((n-1)\) state is losslessly equivalent, on actual profiles with
\(n\ge2\), to the tuple of labelled marginal stopping laws. Replacement is
coordinate overwrite. For four players, order \(3\) is the first
replacement-closed order.

Lower orders fail by deterministic finite-clock examples: \(k+1\) early
blockers can hide one player's clock from every order-\(k\) query, while one
replacement followed by one order-\(k\) query removes the blockers and exposes
that clock.

The complete theorem and proof are in `MARKOV_COMPLETE.md`.

## Chronological information lower bound

Current terminal payoff and cap data are not enough for suffixing. More
strongly, even the law of the terminal payoff vector under every current
unilateral behavioral replacement can identify two positive-reach profiles
whose one-step literal suffixes have different prescribed payoffs.

Thus an exact state supporting labelled suffix-then-replacement programs must
retain chronological response information. A four-player probe table shows
that it must determine at least one full scalar tower

\[
\left(
U_2\bigl((S_n\sigma)[3\leftarrow Q_3^0]\bigr)
\right)_{n\ge0},
\]

which in that table is exactly one player's calendar hazard stream.

This is a necessary observable, not a characterization of the minimal full
state. The proof is in `SUFFIX_INFORMATION_OBSTRUCTION.md`.

## Compactness obstruction

The same probe gives the exact incompatibility

\[
\boxed{
\begin{array}{c}
\text{one common continuity modulus for every labelled suffix depth}\\
+\ \text{a state image containing all isolated late-clock profiles}\\
+\ \text{sequential compactness}
\end{array}
\quad\Longrightarrow\quad\bot.}
\]

The depth-uniform quantifier is essential. A product or pointwise topology can
be compact and make every fixed suffix continuous; the family of all suffixes
is then not equicontinuous. A supremum-type topology makes the whole suffix
family uniformly stable but is not totally bounded.

Likewise, no one finite abstraction at fixed positive accuracy can control
all calendar suffix probes simultaneously. This does not rule out a finite
approximation chosen for one source, one depth bound, or one fixed finite
program.

## Positive-reach versus off-path suffixes

Marginal stopping laws determine the suffix at depth \(h\) whenever every
player has positive survival probability to \(h\), by coordinatewise
conditioning. With a common survival floor \(\eta>0\), this operation has an
explicit stability modulus depending on \(\eta\).

If a player reaches \(h\) with probability zero, its stopping law forgets its
prescribed actions after that history. Recovering an arbitrary literal
off-path suffix requires the full hazard policy or an equivalent
suffix-indexed response tower.

## Two compatible topology regimes

The results do not conflict:

\[
\begin{array}{c|c|c|c}
\text{regime}&\text{exact updates}&\text{suffix stability}&\text{compact}\\ \hline
\text{operational TV/sup}
&\text{replacement}
&\text{uniform static probes}
&\text{no}\\
\text{pointwise response graph}
&\text{fixed operations}
&\text{each fixed positive-reach suffix}
&\text{yes}.
\end{array}
\]

Every actual profile admits a rational finite-clock approximation uniform over
all static pure interventions in the operational metric. This is a
sourcewise finite-support approximation, not a finite global net.

A compact split-clock response graph can retain Never, finite-time escape,
joint escaping ties, and every fixed pure-intervention response. Fixed actual
replacement laws extend by dominated convergence. Moving replacement laws,
zero-survival suffixes, and executable realization of arbitrary boundary
transitions require additional coherence.

The topology and approximation statements are collected in
`STATE_TOPOLOGIES_AND_APPROXIMATION.md`.

## Surviving synthesis problem

The exact replacement state does not itself prove uniform equilibrium. The
compactness no-go does not rule out a sufficient architecture with weaker,
program-dependent continuity. Viable designs include:

- a projective state with a modulus for each fixed finite program;
- a positive-reach state plus a separate vanishing-survival dispatch;
- a compact semantic core with a noncompact source-attached chronological
  passport;
- an inverse system of finite-depth states with a diagonal controller;
- an absorption-clock quotient with a separate chronological realization
  theorem; or
- a noncompact exact operational state with a compact or well-founded
  projection.

For any such design, the remaining theorem must do more than close the update
formulas. It must prove that every trajectory either:

1. reaches terminal approximate Nash states;
2. contains a positive admissible return;
3. exits through a renewable well-founded rank; or
4. yields an exact positive exploitability-gap certificate.

No such global consumer follows from the information and topology results
alone.

There is a generic consumer for an already constructed compact system of
typed chronological edges: an invariant occupation with positive admissible
mean charge yields a fixed-target near-return, while finite ranks and
separation functionals can certify exits.  The result and its exact hypotheses
are in `CHRONOLOGICAL_OCCUPATION_DUALITY.md`.  The missing Fin4 producer is
stated in `FIN4_NEUTRAL_CHRONOLOGY.md`.  Arbitrary source operations cannot be
used as chronological edges; `RECURRENCE_ARCHITECTURE_OBSTRUCTION.md` gives an
exact counterexample.

The forward controller architecture in CONTROLLER_VS_TESTER.md avoids the
all-depth suffix requirement. It gives an exact finite-dimensional tester
ledger, finite-window semantic approximation, and complete barrier duality.
Its remaining problem is precisely to prove that its target-free value
\(\eta(r)\) vanishes for every four-player table, or to produce one positive
barrier. Thus it solves the representation problem for one legal program
language without solving the sign problem.
