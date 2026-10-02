# A late cap reset renews the escaping-cap-clock source

Author: `CODEX_HAHN`

## Status

**Exact ordinary mathematics; source-renewal theorem, not a terminal
consumer.**  The infinite-reset arm of the nested terminal-cap-child
genealogy does not merely enter an unstructured quantitative-debt descendant.
A sufficiently late reset child is itself a new actual source with an attained
Quit0 complete cap, a uniform debt floor, a singleton cap pin, and an exact
singleton-wall gap.  An arbitrary exact root at that child spends a fixed
amount of debt and absorption.  If its joint survival is positive, the same
escaping exact-cap-clock construction restarts literally with the reset
observer as its new owner.

What renews is the cap-clock/source packet.  The total-debt drop is not a
renewable rank: horizontal installation of the next cap child may replenish
other debt coordinates.  Repeated renewal can therefore cycle among player
labels.

## Question

Does the uniform exact-root debt expenditure at a late front reset lose the
nested source passport, or can the reset child seed the same construction
again?

## Input

Let `I = Fin 4`.  Rewards and prescribed payoffs lie in `[-M,M]`, with
`M>0`.  Assume a terminal exploitability gap `Gamma>0`: every actual profile
has some complete behavioral deviation of gain at least `Gamma`.

Use the positive-survival nested genealogy

\[
 \tau^{n+1}=q^n::\tau^n,
 \qquad
 \zeta^{n+1}=\bar q^n::\zeta^n,
\tag{1}
\]

where `q^n` is exact root Nash against the literal payoff of `tau^n`, and
`bar q^n` is obtained by forcing the current cap owner `b` to Continue.  The
owner uses its exact deterministic deadline `n` in `zeta^n`, so

\[
 d_b(\zeta^n)=0.
\tag{2}
\]

Assume the marginal root hazards are summable.  Hence

\[
 \prod_{n\ge R}\Pr_{\bar q^n}(\text{all Continue})\longrightarrow1
 \quad\text{as }R\to\infty.
\tag{3}
\]

## 1. Select the observer after the hazard tail is small

Choose `R` so large that the tail product in (3) is at least `1/2`.  The
terminal gap at the actual finite child `zeta^R` is attained by a pure time:
player `b` Quits surely by date `R`, so every outsider response after `R` is
outcome-equivalent to Never.  Since `b` has zero debt, select an outsider
`j != b` and an attained response with gain at least `Gamma`.

Copy that response through every later barred root and use it in the fixed
suffix `zeta^R`.  Literal root-then-continuation factorization gives

\[
 d_j(\zeta^N)\ge
 \left(\prod_{n=R}^{N-1}\Pr_{\bar q^n}(\text{all Continue})\right)\Gamma
 \ge \Gamma/2
 \qquad(N\ge R).
\tag{4}
\]

Put

\[
 \delta:=\Gamma/2.
\tag{5}
\]

Choose pure-time caps for `j` coherently along the nested children.  At every
new root the cap either resets to Quit0 or shifts an old cap by one date.
This note concerns the arm with infinitely many resets.

## 2. A late reset is a uniformly pinned actual source

At a reset from depth `n` to `n+1`, literal Quit0 attains `j`'s complete cap
at `zeta^(n+1)`.  Therefore

\[
 B_j(\zeta^{n+1})
   =Q_j((\bar q^n)_{-j}),
 \qquad
 d_j(\zeta^{n+1})\ge\delta.
\tag{6}
\]

The barred outsider hazards tend to zero.  Coupling their product law with
all Continue gives

\[
 \left|Q_j((\bar q^n)_{-j})-r_j(\{j\})\right|
 \le 2M\Pr_{\bar q^n}(\text{some opponent of }j\text{ Quits})
 \longrightarrow0.
\tag{7}
\]

At every sufficiently late reset, consequently,

\[
 \left|B_j(\zeta^{n+1})-r_j(\{j\})\right|\le\delta/4.
\tag{8}
\]

This is the exact fixed-cap pin, now at the literal child rather than at a
compact limit.  Combining (6)--(8) also gives the direct singleton-wall
separation

\[
 U_j(\zeta^{n+1})
 =B_j(\zeta^{n+1})-d_j(\zeta^{n+1})
 \le r_j(\{j\})-3\delta/4.
\tag{9}
\]

No holonomy limit is needed for (8)--(9).  The signed-holonomy theorem
explains why repeated front resets force this sign, while the attained cap
identity makes it quantitative at the finite source.

## 3. Every exact first root spends fixed debt and absorption

Fix one sufficiently late reset and abbreviate its actual child by

\[
 y:=\operatorname{Sem}(\zeta^{n+1}).
\]

Let `x` be any exact independent product Nash root against `U(y)`, and let
`y' = T_x y` be the semantic pair of the literal prefix
`x :: zeta^(n+1)`.

The fixed cap-pin debt-expenditure theorem applied with debt floor `delta`
gives

\[
 D(y)-D(y')\ge
 c_0:=\min\{\delta/2,\delta^2/(16M)\}>0.
\tag{10}
\]

It also gives a uniform absorption floor.  Let `a` be the probability that
some opponent of `j` Quits at `x`.

* If `a >= delta/(16M)`, joint absorption is at least that number.
* Otherwise endpoint stability and (8) make Quit strictly better than
  Continue for `j`.  Exact root Nash then forces `j` to Quit surely, so joint
  absorption is one.

Thus

\[
 \operatorname{Abs}(x)\ge
 a_0:=\min\{1,\delta/(16M)\}>0.
\tag{11}
\]

Every other debt coordinate weakly decreases under the exact prefix, so the
loss in (10) cannot be offset by cap leakage.  Global minimality, when
available, implies

\[
 D(y)\ge D_*+c_0.
\tag{12}
\]

## 4. Positive survival literally restarts the cap-clock construction

Suppose first that `x` has positive joint Continue probability.  Since Quit0
attains `j`'s complete cap at the tail source, the exact cap-transport
calculation applies without stationarity:

* Continue at the new root and then Quit0 at the old source is `j`'s attained
  complete cap at `x :: zeta^(n+1)`;
* this is the deterministic deadline-one clock; and
* its new debt is the old debt multiplied by the opponents-Continue mass.

Choose another exact root against the new literal prescribed payoff.  If it
also has positive survival, the deadline shifts to two.  Continuing
recursively gives exactly the same source data as the original
positive-survival construction, now with owner `j` and base source
`zeta^(n+1)`.

If every recursively selected root has positive survival, checked bounded
finite exact-block capacity again makes the whole marginal-hazard series
summable and leaves the new actual source at positive far-end reach.  Its
terminal cap children are again nested literal profiles.  Thus the
infinite-reset output is closed under source renewal:

\[
 \boxed{
 \text{late reset of owner }b\text{ to observer }j
 \Longrightarrow
 \text{new escaping-cap-clock source with owner }j.}
\tag{13}
\]

The proof of this restart uses only:

1. an actual behavioral source profile;
2. an attained Quit0 complete cap for the named owner;
3. positive owner debt;
4. exact product-root Nash existence against each literal successor payoff;
5. positive survival of the selected roots;
6. the fixed game-level terminal gap; and
7. under no uniform payoff, bounded finite exact-block hazard capacity.

The original stationary tropical formula, law collar, and original owner
label are not used after the new source (6) has been obtained.

## 5. The zero-survival exception

If an exact selected root has zero joint survival, the positive-survival
clock transport stops at that finite root.

If two players Quit surely there, every unilateral deviation still leaves a
sure opponent quitter.  Exact root Nash then screens the tail for the full
behavioral deviation class and gives a terminal Nash profile.

Otherwise there is exactly one sure quitter `k`.  At the actual prefix
`x :: zeta^(n+1)`, every non-`k` debt coordinate is zero because a sure
opponent screens its tail.  The terminal gap is therefore carried by `k`,
whose cap response changes its own current strategy and can expose the
literal finite child tail.  This is the finite-source unique-sure/singleton
handoff, not the positive-survival cap-clock arm.  No stationary repetition
or limiting-root identification is asserted here.

## 6. Why renewal is not yet a well-founded descent

Equation (10) is a strict total-debt decrease on the exact vertical prefix.
But the next renewed source in (13) is a horizontal cap child of a later
prefix, not the target of that first exact edge.  Installing the old owner's
deadline can raise other players' caps and total debt.  Therefore `D`, debt
support, and the owner label need not decrease across the complete
owner-to-owner transition.

There are only four possible owners, and every infinite-reset transition has
`j != b`.  Finiteness only gives an owner-label cycle.  It does not identify
the semantic source states or convert the horizontal cap updates into
Nash--Bellman edges.  The renewed transition system may therefore remain a
nonterminal strongly connected component.

The uniform constants in (4), (10), and (11) are significant: by selecting
the terminal-gap observer only after the hazard tail product exceeds `1/2`,
every infinite-reset renewal has the same debt floor `Gamma/2` and the same
game-level expenditure constants.  What remains missing is extension-
compatible composition of those fixed expenditures across the horizontal
cap-child seams.

## Boundary tests

### A cap child is not stationary

The restarted source `zeta^(n+1)` is terminal under its prescribed play, but
the other players retain the old counterfactual tail.  The restart theorem
does not call it stationary or finite-clock complete semantics.  Exact cap
transport for the named owner uses only its attained Quit0 response and the
literal positive-survival prefix.

### Packet renewal is weaker than rank renewal

The new source has the same kind of cap-clock seed, but no theorem preserves
the preceding debt decrease after the horizontal cap update.  Calling (13) a
renewable debt descent would be false.

### The observer must be selected late

Fixing the terminal-gap observer at the first child only gives the floor
`C_infinity Gamma`, which can be arbitrarily small between separate renewed
rays.  Selecting an observer at a late child after the tail product is at
least `1/2` is what gives the uniform floor `Gamma/2`.  This does not reselect
the observer within that ray after `R`; one label and one response are then
transported through all later children.

### A unique sure root is not automatically stationary

The zero-survival prefix has an actual finite child tail.  Repeating its root
stationarily would discard that tail and is not used.  The conclusion in the
unique-sure case is only a finite-source handoff.

## Source correspondence

The nested genealogy and fixed-observer transport are in
`CODEX_SPINOZA__NESTED_TERMINAL_CAP_CHILD_FIXED_DEBTOR_TRANSPORT`, reviewed at
SHA-256
`6d813418986400654a0c93fd8e54469b9d965fd61fdefee848cf7c9803c9e956`.
The reset/shift classification and signed reset consequence are in
`CODEX_SPINOZA__SIGNED_CAP_CHILD_HOLONOMY_AND_RESET_DICHOTOMY`, reviewed at
SHA-256
`29e0bc853b0ff979e3295655a78ef7df83711de22f5ecceb9cb7bc94ee172ed7`.

The exact cap-pin debt theorem is the reviewed export
`FIXED_CAP_PIN_APPROXIMATE_ROOT_DEBT_EXPENDITURE`.  The bounded-capacity input
is
`finFour_hasBoundedFiniteExactNashBellmanHazardCapacity_of_no_uniformPayoff`
in
`UniformEquilibrium/Diagnostics/Quitting/FinFourUnboundedExactBlockHazardCapacity.lean`.
The two-sure tail screen is
`quittingTerminalSemanticPrefix_congr_of_twoSureQuitters` in
`UniformEquilibrium/Diagnostics/Quitting/TwoSureProductRootTailScreen.lean`.

## Scope and nonclaims

This note proves a renewable escaping-cap-clock source in the infinite-reset
positive-survival arm and a fixed exact debt/absorption expenditure at every
renewal seed.  It does not consume the eventual-shifted-cap arm.

It does not concatenate successive renewed rays into one chronology, preserve
the vertical debt drop across the horizontal cap seam, produce a decreasing
finite rank, or prove a uniform-equilibrium payoff.

## Next exact question

Does an infinite cycle of renewed owners force a source-compatible return
because every transition carries the same singleton-wall gap and exact
absorption expenditure, or can the horizontal cap children replenish that
expenditure indefinitely while remaining in the bounded semantic carrier?

