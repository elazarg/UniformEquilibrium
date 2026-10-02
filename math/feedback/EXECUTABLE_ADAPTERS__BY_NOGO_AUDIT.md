# No-go audit of `EXECUTABLE_ADAPTERS.md`, Section 3

Reviewer: `NOGO_AUDIT`

## Status and verdict

**The two-player calculation passes.  Theorem 8 needs a scope repair.**

As ordinary mathematics, the example proves all of the following:

1. the exact-root correspondence has closed graph, but its
   maximum-absorption subcorrespondence does not;
2. the defect occurs on actual stopping-law profiles with one common finite
   support and total-variation convergence;
3. retaining the limiting selected root violates maximality; and
4. replacing it by the unique legal maximal root at the limiting source
   creates a unit jump in both player 2's prescribed payoff and unrestricted
   behavioral cap.

This is enough to refute a **bare, exact, same-source maximal-root edge whose
entire output trace must be sequentially closed**.  It is not, without a
definition of `adapter`, a theorem that every possible construction using a
maximal root is impossible.  In particular, it does not rule out pointwise
discontinuous selection, approximate-root edges, restricted source classes,
or a different direct robustness certificate.

The calculations below were checked against the project definitions but are
not a new Lean-checked theorem.

## Claim audited

For players 1 and 2, take

\[
r(\{1\})=(0,1),\qquad
r(\{2\})=(1,-1),\qquad
r(\{1,2\})=(0,-1),
\]

and zero payoff on nonabsorption.  For $0\le z\le 1$, let player 1 Never
Quit and let player 2 Quit at date zero with probability $z$, otherwise
Never Quit.  Write this actual stopping-law source as

\[
\mu^z_1=\delta_\infty,
\qquad
\mu^z_2=z\delta_0+(1-z)\delta_\infty.
\]

The edge under review prefixes the same continuation by an exact root that
maximizes one-stage absorption among all exact roots against the continuation
cap.

## 1. Actuality, support, and convergence

The laws are literal actual profiles: at the initial live history, player 1
continues surely and player 2 quits with probability $z$; after survival,
both continue surely.  Equivalently, they are reconstructed by
`quittingStoppingLawProfile`, whose exact stopping-law accessor is
`quittingBehaviorStoppingLaw_stoppingLawProfile`
(`Research/Quitting/FiniteClockTerminalSemantics.lean`).

All coordinates are supported on the common two-point set
$\{0,\infty\}$.  In the document's summed $\ell^1$ metric,

\[
d(\mu^z,\mu^0)=2z.
\]

Thus finite support, uniform tightness, and convergence as $z\downarrow0$
are all exact.

## 2. Independent cap calculation

The cap here is the supremum over complete unilateral behavioral strategies,
not a stationary or root-only cap; this is
`quittingContinuationBestResponseValue`
(`UniformEquilibrium/Quitting/Root/FirstBranch.lean`).

Against player 2's prescribed clock, player 1's only consequential choice is
whether to Continue at date zero.  If player 2 quits there, the realized
coalition is then $\{2\}$, paying player 1 one.  If the root survives,
player 2 Never Quits, and every later player-1 stop and Never itself pay zero.
Quitting at date zero also pays zero whether or not player 2 joins.  Hence no
behavioral strategy exceeds $z$, and Continue at date zero attains it:

\[
B_1(\mu^z)=z.
\]

Against player 1's Never law, every finite stop by player 2 produces
$\{2\}$ and payoff $-1$, while Never gives zero.  Therefore

\[
B_2(\mu^z)=0.
\]

So the document's cap vector

\[
B(\mu^z)=(z,0)
\]

is correct.  For reference, the prescribed payoff is

\[
U(\mu^z)=(z,-z).
\]

## 3. Independent exact-root calculation

Let $x_i$ be player $i$'s root Quit probability.  Against
$B(\mu^z)=(z,0)$, player 2 receives $-1$ from Quit whether player 1 quits
or continues.  From Continue, player 2 receives one if player 1 quits and
zero otherwise.  Thus

\[
Q_2=-1,\qquad C_2=x_1,
\]

so Continue is strictly optimal for every $x_1\in[0,1]$, and every exact
root has $x_2=0$.

With $x_2=0$, player 1 has

\[
Q_1=0,\qquad C_1=z.
\]

It follows that the exact-root correspondence is exactly

\[
F(\mu^z)=
\begin{cases}
\{(0,0)\},&z>0,\\
[0,1]\times\{0\},&z=0.
\end{cases}
\]

This agrees with `IsεQuittingRootNash`
(`UniformEquilibrium/Quitting/Root/FirstBranch.lean`).  Since
`quittingRootAbsorptionMass`
(`UniformEquilibrium/Quitting/Stationary/LiveMass.lean`) is

\[
a(x)=1-(1-x_1)(1-x_2),
\]

the maximum-absorption roots are uniquely

\[
x^z=(0,0)\quad(z>0),
\qquad
x^0=(1,0).
\]

Consequently the sequence of recorded legal pairs
$(\mu^z,x^z)$ converges to $(\mu^0,(0,0))$, which is outside the recorded
maximal-root relation.  There is no subsequence escape because all positive-
$z$ roots are unique.

This also verifies the failure of comparison lift: the limiting competitor
$(1,0)\in F(\mu^0)$ cannot be approached by any member of
$F(\mu^z)=\{(0,0)\}$ for $z>0$.

## 4. Independent output and semantic-jump calculation

For $z>0$, prefixing by $(0,0)$ merely shifts the continuation clock one
date.  The output laws are

\[
\nu^z_1=\delta_\infty,
\qquad
\nu^z_2=z\delta_1+(1-z)\delta_\infty.
\]

Thus $d(\nu^z,\nu^\infty)=2z$, where both coordinates of
$\nu^\infty$ are Never.  Moreover

\[
U(\nu^z)=(z,-z),\qquad B(\nu^z)=(z,0),
\]

and both vectors converge to zero.

At the limiting source, the only legal maximal-root prefix is

\[
\bar\nu=T_{(1,0)}\mu^0.
\]

Player 1 quits surely at the new root and player 2 continues, so absorption
is immediate at $\{1\}$.  Therefore

\[
U(\bar\nu)=(0,1).
\]

Player 2 can attain one by continuing at the root, while every root Quit
gives $-1$; no terminal reward for player 2 exceeds one.  Hence

\[
B(\bar\nu)=(0,1).
\]

It follows exactly that

\[
|U_2(\bar\nu)-U_2(\nu^\infty)|=1,
\qquad
|B_2(\bar\nu)-B_2(\nu^\infty)|=1.
\]

The player-1 stopping-law distance is

\[
\|\delta_0-\delta_\infty\|_1=2.
\]

These output computations are also consistent with the literal splicing
identity `quittingTerminalSemanticPair_rootThenContinuation`
(`UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`).

## 5. The precise no-go that follows

Define the bare recorded relation

\[
\mathcal M=
\{(\mu,x,T_x\mu):
x\in F(\mu),\ a(x)=\max_{y\in F(\mu)}a(y)\}.
\]

Then Section 3 proves the following exact statement:

> The relation $\mathcal M$ is not sequentially closed for source total
> variation, Euclidean root convergence, and output total variation.  At the
> displayed missing limit, every exact same-source repair back into
> $\mathcal M$ has player-2 payoff error and player-2 cap error equal to one.

This statement remains true if the root coordinate is omitted, because both
the positive-$z$ maximal successor and the zero-source maximal successor are
unique in this example.  Recording the roots makes the failed legality
visible; it cannot repair it.

Accordingly, Theorem 8 is valid if its two informal requirements mean:

1. a limiting execution must still be a legal **exact maximal-root prefix of
   the exact limiting source**; and
2. reconstruction error is measured against the converged output trace and
   must vanish in each prescribed-payoff and unrestricted-cap coordinate.

## 6. Scope that the example does not prove

The current words "there is no universal adapter" are broader than the
formal relation-level conclusion unless `adapter`, `closed-limit semantics`,
and `recovery budget` are defined as above.

### Pointwise selection is not impossible

For every fixed cap there exists a maximum-absorption exact root.  The project
already records this in `exists_maximalAbsorption_isZeroQuittingRootNash` and
defines the pointwise choice `quittingMaximalAbsorptionCapRoot`
(`Research/Quitting/CausalTailEscapeMaxAbsorptionCore.lean`).  Section 3 shows
that such a selector cannot have the demanded universal limit coherence; it
does not refute its pointwise existence or actual one-step compilation.

### Approximate-root adapters evade this obstruction

At the positive-$z$ source, the root $(1,0)$ has maximum possible
absorption and is a $z$-approximate root Nash action: player 1 can gain
exactly $z$ by switching from Quit to Continue, and player 2 already strictly
continues.  Thus the constant root choice

\[
x^z=(1,0)\quad(0\le z\le1)
\]

is continuous and has root error $z=d(\mu^z,\mu^0)/2$.  It is not an exact
root for $z>0$, so it does not contradict the precise no-go.  It does show
that Theorem 8 must not be cited against grammars allowing vanishing
approximate Nash error.

### Full comparison lift is sufficient, not necessary

Proposition 2's comparison-lift hypothesis is a clean sufficient condition
for argmax closure.  The example proves that it is not automatic for the
exact-root correspondence.  It does not prove that every robust optimization
adapter must establish full comparison lift.  A direct proof that the
maximizer graph is closed, or an objective-specific lower-semicontinuity
certificate for the optimal value, can also justify a particular occurrence.

Thus the sentence "maximal roots are admissible only with a
comparison-transport certificate" should be read as a rule of this chosen
grammar, not as a mathematical necessity theorem.

### Restricted domains and larger macros remain open

The counterexample does not rule out an exact maximal-root adapter on a
restricted source class whose maximizer graph is closed.  Nor does it rule
out a larger construction that uses a maximal root internally but does not
require the bare intermediate root/prefix trace to survive as a closed port.
Such a macro would need its own actuality and continuity theorem; Section 3
neither supplies nor refutes one.

Merely adding the selected root as ordinary compact data does not help on the
full source space, as the calculation shows.  Adding discrete state that
separates the $z>0$ branch from $z=0$, however, changes the topology or
domain and is outside the stated bare-edge theorem.

### No Fin4 positive-minimum no-go follows

Here

\[
B(\mu^z)-U(\mu^z)=(0,z),
\]

so the debt tends to zero, and $\mu^0$ is already an exact all-behavior
terminal Nash profile with payoff zero.  The example has no positive-minimum
hard-residual hypothesis and no Fin4 source provenance.  It therefore does
not show that the maximal selector used by a particular current Fin4 packet
fails on that packet's restricted source class.  The document's final
nonclaim on this point is correct.

## 7. Recommended repair to Theorem 8

Replace the undefined global impossibility wording by the relation-level
statement in Section 5, followed by a corollary of the following form:

> No adapter defined on all actual sources can both (i) expose an exact
> maximum-absorption root and its literal same-source prefix as a trace port,
> and (ii) make that legal trace port sequentially closed under raw source
> total variation with vanishing prescribed-payoff and unrestricted-cap
> reconstruction error.

Then state explicitly that this does not exclude discontinuous pointwise
choice, approximate roots, restricted domains, or alternative direct
closedness certificates.  Similarly, replace "the comparison-lift hypothesis
cannot be dropped" by "some additional robustness hypothesis cannot be
omitted from a universal argmax-closure theorem; comparison lift is one
sufficient choice."

## Sources and declarations inspected

- `meta/EXECUTABLE_ADAPTERS.md`, especially Proposition 2 and Section 3.
- `docs/FRONTIER.md`, canonical maximal-prefix-ray route.
- `docs/TOOLKIT.md`, canonical maximal-prefix-ray return or strict-stall row.
- `quittingContinuationBestResponseValue` and `IsεQuittingRootNash`
  (`UniformEquilibrium/Quitting/Root/FirstBranch.lean`).
- `quittingRootAbsorptionMass`
  (`UniformEquilibrium/Quitting/Stationary/LiveMass.lean`).
- `quittingTerminalSemanticPair`, `quittingTerminalSemanticPrefix`, and
  `quittingTerminalSemanticPair_rootThenContinuation`
  (`UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`).
- `quittingStoppingLawProfile` and
  `quittingBehaviorStoppingLaw_stoppingLawProfile`
  (`Research/Quitting/FiniteClockTerminalSemantics.lean`).
- `exists_maximalAbsorption_isZeroQuittingRootNash`,
  `quittingMaximalAbsorptionCapRoot_exactNash`, and
  `quittingMaximalAbsorptionCapRoot_maximal`
  (`Research/Quitting/CausalTailEscapeMaxAbsorptionCore.lean`).
- `quittingMaximalCapSemanticRoot_exactNash` and
  `quittingMaximalCapSemanticRoot_maximal`
  (`Research/Quitting/MaximalCapSemanticPrefixOrbit.lean`).

No literature claim was used.

## Concrete next question for the author

Does the intended adapter contract require every intermediate maximal-root
prefix port to converge as a legal same-source edge, or only the final
observable output of a larger macro?  The example decisively refutes the
first contract.  The second needs a separately stated trace/quotient semantics
before Theorem 8 can be assessed against it.
