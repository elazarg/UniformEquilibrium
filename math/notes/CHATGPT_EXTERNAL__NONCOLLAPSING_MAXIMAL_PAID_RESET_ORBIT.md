# Noncollapsing maximal paid/reset orbit

Author: `CHATGPT_EXTERNAL`
Packet audit: `CODEX_ROOT`
Status: `MATH_REVIEWED`

Independent review:
[`FIN4_HARD__BY_CODEX_ROOT.md`](../feedback/FIN4_HARD__BY_CODEX_ROOT.md)

## Exact question

Let a finite quitting game have a positive global minimum $D_*>0$ of total
terminal-semantic debt.  Suppose an actual behavioral profile carries:

- a positive paid first-disagreement certificate for an observer;
- a reset coordinate of zero unrestricted terminal debt;
- a positive opponent-incidence coordinate in its actual terminal law; and
- the same global minimum used by the fixed-law reset dispatcher.

Iterate the maximum-absorption exact cap--Nash root whenever that root has
positive absorption.  Does the resulting family retain enough quantitative
paid, law, and reset data to remain a renewable actual-source obstruction?

## Result

At every finite stage there is an exact alternative:

1. all Continue is the unique exact root at the current behavioral cap; or
2. prefixing the maximum-absorption exact root gives another actual paid/reset
   source with the same global minimum, the same zero-debt reset coordinate,
   positive reset incidence, and a fresh fixed-law reset dispatch.

If the second alternative occurs forever, let $S_n$ denote the actual
source, $z_n$ its terminal-semantic pair, and

\[
\Delta_n=D(z_n)>0.
\]

Let $x_n$ be its maximum-absorption exact cap--Nash root, $c_n$ the joint
all-Continue probability of $x_n$, and $\beta_n$ the probability that all
opponents of the paid observer Continue at $x_n$.  Then

\[
0<c_n<1,\qquad \beta_n\ge c_n,
\]

and the canonical descendant satisfies

\[
\Delta_{n+1}=c_n\Delta_n.
\tag{1}
\]

The stored paid lower bound may be chosen in either of two canonical ways:

\[
g_{n+1}=c_ng_n,
\tag{2a}
\]

which is already sufficient for every conclusion below, or in the sharper
form

\[
g_{n+1}=\beta_ng_n.
\tag{2b}
\]

Equation (2b) concerns the chosen certificate scalar.  It does not assert that
this scalar equals the entire underlying pure-time payoff difference unless
the parent scalar was itself chosen to be that exact difference.

Put

\[
\kappa:=\frac{D_*}{\Delta_0}>0.
\]

Since every $S_N$ is an actual behavioral profile, global minimality and
(1) give

\[
\prod_{n<N}c_n=\frac{\Delta_N}{\Delta_0}\ge\kappa.
\tag{3}
\]

Consequently the paid certificates never collapse:

\[
g_N\ge g_0\prod_{n<N}c_n\ge\kappa g_0>0.
\tag{4}
\]

If a fixed terminal coalition has mass \(\mu>0\) in the original suffix law,
then its inherited mass after $N$ prefixes is exactly

\[
\mu\prod_{n<N}c_n,
\]

and hence is at least \(\kappa\mu\).  Finally,

\[
\sum_{n=0}^{\infty}(1-c_n)\le-\log\kappa<\infty.
\tag{5}
\]

Thus maximal paid/reset regeneration has the exhaustive normal form

```text
finite arrival at a unique-all-Continue cap
or
an infinite family of literal actual sources carrying
  * summable prefix absorption,
  * a uniformly positive paid certificate,
  * a uniformly positive inherited atom,
  * the same global minimum,
  * zero reset debt and positive reset incidence, and
  * a fresh fixed-law reset dispatch at every finite stage.
```

## Local no-go for immediate cap-root production

The paid row and atom do not by themselves exclude the first alternative.
Take players $0,1,2,3$ and cap $b_i=2$.  For
$i\in\{0,2,3\}$, define

\[
r_i(S)=
\begin{cases}
2,&i\notin S,\\
0,&i\in S.
\end{cases}
\]

For player $1$, define

\[
r_1(S)=
\begin{cases}
2,&1\notin S,\\
2,&\{0,1,2\}\subseteq S,\\
1,&S=\{1\},\\
0,&\text{otherwise}.
\end{cases}
\]

Let everyone Continue at date zero, let $0$ and $2$ Quit at date one, and
let the remaining players Never Quit.  The terminal law is the point mass at
$\{0,2\}$, the unrestricted cap is $(2,2,2,2)$, and player $1$'s
pure-time payoffs at dates zero and one are respectively $1$ and $2$.

Nevertheless, at cap $b$, each of $0,2,3$ obtains $2$ by Continue and
$0$ by Quit against every root.  They therefore Continue surely in every
exact root.  Player $1$ then compares Continue payoff $2$ with singleton
Quit payoff $1$, so player $1$ also Continues surely.  All Continue is the
unique exact cap--Nash root.

The table has a singleton cash-out terminal Nash profile and therefore is not
a positive-gap counterexample.  It proves only that cap data, a later paid
row, and a positive atom cannot locally refute unique all Continue: the cap
root game has forgotten the row's chronology.

## Proof

If all Continue is not the unique exact root, the maximum-absorption exact
root has positive absorption.  Positive global minimum debt and exact
cap--Nash debt scaling exclude zero continuation, giving $0<c_n<1$.

Exact cap--Nash prefixing gives (1).  Shifting the two pure-time witnesses
through the new root multiplies their payoff difference by the observer's
opponent survival \(\beta_n\).  Since joint survival also requires the
observer to Continue, \(\beta_n\ge c_n\).  Re-extracting the paid row with
certificate \(c_ng_n\), or with \(\beta_ng_n\), proves (2a) or (2b).

Literal law prefixing multiplies every inherited suffix atom by $c_n$.
Coordinate debt scaling preserves the reset coordinate's zero debt, and
positive joint continuation preserves positive opponent incidence.  The
terminal exploitability witness can therefore invoke the fixed-law reset
dispatcher again at the descendant's actual semantic/law point.  This proves
renewability at every finite stage.

Iterating (1) and using $D(z_N)\ge D_*$ proves (3).  Equations (2a) and
$\beta_n\ge c_n$, or directly (2b), prove (4).  For $0<c_n\le1$,

\[
1-c_n\le-\log c_n.
\]

Summing through $N$, using (3), and passing to the supremum proves (5).

## Conjecture-facing change

This closes the source-provenance defect of repeatedly applying the maximal
one-step theorem.  The surviving infinite branch is not merely a sequence of
decreasing real debts: it is a renewable family of actual sources whose paid
certificate and causal atom remain at a fixed positive scale.

It does **not** answer
[`FIN4_PAID_RESET_REGENERATION_RANK.md`](../questions/FIN4_PAID_RESET_REGENERATION_RANK.md).
There is still no well-founded rank, positive admissible return, terminal
approximation, or contradiction.  The family is built by outward prefixing,
so the marked suffix moves to later dates and can disappear from a literal
behavioral limit despite its noncollapsing semantic mass.

The remaining consumer is therefore

```text
noncollapsing maximal paid/reset orbit with a causal suffix atom
  -> positive cumulative admissible-payoff near-return
     or terminal approximate Nash profiles,
```

or a genuinely global consumer of the eventual unique-all-Continue cap.

## Sources checked

- `QuittingPaidCapLiftedSource.MaximalOneStepPaidResetRegeneration` and
  `maximalOneStepPaidResetRegeneration_or_uniqueAllContinue` in
  `Research/Quitting/PaidCapMaximalOneStepRegeneration.lean` provide the
  checked one-step actual-source regeneration.
- `sourceMaximalRegeneration_or_repairedMaximalRegeneration_or_doubleUnique`
  in `Research/Quitting/FinFourPaidCapMaximalDoubleRegeneration.lean` provides
  the checked double-port application.
- `quittingTerminalSemanticDebtSum_maximalCapSemanticPrefixOrbit_eq`,
  `quittingStageCoalitionMass_maximalCapSemanticPrefixProfile_add`, and
  `quittingTerminalPayoff_maximalCapSemanticPrefixProfile_sub_eq` in
  `Research/Quitting/MaximalCapSemanticPrefixOrbit.lean` provide the checked
  scaling identities.
- `QuittingPaidCapLiftedSource.pureTimePayoff_sub_shift`,
  `.shifted_gain_le`, and `.absorption_summable` in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/
  PaidCapLiftedSummablePort.lean` provide the generic checked paid-row and
  summability account.

The exact recursive wrapper exposing the descendant gain equation is not yet
a named checked theorem.

## Lean handoff

The smallest useful strengthening of the existing one-step structure is

```lean
descendant_debt_eq :
  descendant.initialDebt =
    quittingStationaryContinueMass maximalRoot * source.initialDebt

descendant_gain_eq :
  descendant.gain =
    quittingStationaryContinueMass maximalRoot * source.gain
```

This conservative version matches the construction already used in
`PaidCapMaximalOneStepRegeneration.lean` and suffices for (3)--(5).  A sharper
variant may use
`quittingStationaryFixedOpponentsContinueMass maximalRoot source.observer`
in `descendant_gain_eq`, provided the descendant row is re-extracted with that
certificate scalar.

A recursive theorem should then return either a finite stage with
`HasUniqueAllContinueAtCap` or a sequence of regeneration records satisfying
the displayed equations.  Atom scaling is derivable from
`descendant_profile` and literal law prefixing and need not be duplicated as
an independent axiom-like field.

## Checks and open objections

- The deviations are unrestricted behavioral deviations; the paid witnesses
  happen to be deterministic pure stopping times selected from the exact
  behavioral cap semantics.
- `Never` is permitted as either pure-time witness and is preserved by the
  shift operation.
- Every finite iterate is an actual behavioral profile.  No carrier point is
  substituted for it.
- “Renewable reset provenance” means a fresh fixed-law reset dispatch exists
  at every iterate.  It does not mean that the dispatch's returned point is
  the next chronological suffix.
- The infinite family is not one forward chronological play: each successor
  is obtained by prefixing outward.  Compact recurrence cannot be inferred
  without a new realization theorem.
- The local example is a no-go for a local implication, not a quitting-game
  counterexample.

## Feedback wanted

1. Can the noncollapsing orbit be converted into one positive admissible
   near-return without moving the causal suffix atom to infinity?
2. Is there a finite renewable rank on the paid/reset dispatches, rather than
   merely the strictly decreasing real debt?
3. Can the terminal exploitability witness rule out unique all Continue using
   information absent from the local countermodel?
