# Sharp singleton clock compression and the Fin4 minimum-law adapter

Authors: ChatGPT External, STRENGTHENER, Codex Root

Independent reviews:
[adversarial review](../feedback/FIN4_MINIMUM_SINGLETON_CLOCK_COMPRESSION__BY_ATLAS_FALSIFIER.md),
[strengthening review](../feedback/FIN4_MINIMUM_SINGLETON_CLOCK_COMPRESSION__BY_STRENGTHENER.md),
[export-gate audit](../feedback/FIN4_MINIMUM_SINGLETON_CLOCK_COMPRESSION__BY_ATLAS_GATEKEEPER.md)

## Exact statement

### Theorem A: sharp anchored one-date singleton compression

Let $I$ be a finite player set, let $r$ be a quitting-game reward table,
let $\sigma$ be an arbitrary behavioral profile, fix a player $j$, and fix
an anchor date $a\in\mathbb N$.

On the unique live history at date $t$, write

\[
q_i(t)=\Pr_\sigma(i\text{ Quits}),
\qquad c_i(t)=1-q_i(t).
\]

For $t\ge a$, define

\[
\alpha_{a,t}
=\left(\prod_{r=a}^{t-1}c_j(r)\right)q_j(t)
\tag{1}
\]

and

\[
\beta_{a,t}
=\left(\prod_{r<a}\prod_{i\in I}c_i(r)\right)
 \left(\prod_{r=a}^{t}\prod_{i\ne j}c_i(r)\right).
\tag{2}
\]

Put

\[
A_a=\sum_{t\ge a}\alpha_{a,t}
\tag{3}
\]

and let $m_a$ be the total source mass of singleton-$j$ terminals at or
after the anchor:

\[
m_a
=\sum_{t\ge a}
  \Pr_\sigma(\text{terminal at }t\text{ is }\{j\}).
\tag{4}
\]

Then

\[
0\le A_a\le1,
\qquad
m_a=\sum_{t\ge a}\alpha_{a,t}\beta_{a,t}.
\tag{5}
\]

Assume $m_a>0$, and let $t_0\ge a$ be the least date with
$\alpha_{a,t_0}>0$.  Let $\tau$ be the literal one-date profile obtained
from $\sigma$ by changing only $j$'s action at date $t_0$ to Quit surely.
Then:

1. $0<A_a\le1$, and
   \[
   \Pr_\tau(\text{terminal at }t_0\text{ is }\{j\})
   =\beta_{a,t_0}
   \ge \frac{m_a}{A_a}
   \ge m_a.
   \tag{6}
   \]
2. In the source profile, $j$ already Continues surely at every live row
   $r$ with $a\le r<t_0$.
3. Every opponent's complete behavioral strategy is unchanged.
4. The complete profile $\tau$ equals $\sigma$ at every date other than
   $t_0$; in particular, their complete live-root tails agree literally at
   every date strictly after $t_0$.
5. The unrestricted behavioral best-response cap of $j$ is unchanged:
   \[
   B_j(\tau)=B_j(\sigma),
   \tag{7}
   \]
   because $j$'s opponents are unchanged.

For $a=0$, $m_0$ is the complete terminal-law mass of $\{j\}$.  Thus one
literal one-date unilateral replacement exposes singleton stage mass at least
the entire singleton mass of the source profile.

### Theorem B: cofinal Fin4 minimum-law compression

Let

```text
source : FinFourMinimumAtomProducer reward bound
```

and suppose the selected terminal coalition is a singleton.  Let $j$ be its
unique player and put

\[
\mu
=\texttt{source.point.2 (some source.atom.terminal)}>0.
\tag{8}
\]

Unpack the causal chronology retained by `source.atom` into actual suffix
profiles $\sigma_n$ and exact source cap-root words $R_n$, and put

\[
\Sigma_n=R_n\triangleright\sigma_n,
\qquad
a_n=|R_n|=n+1.
\tag{9}
\]

For every fixed $0<\lambda<\mu$ and every requested depth $N$, there are
$n\ge N$, a date $t_n\ge a_n$, and an actual behavioral profile
$\tau_n$ such that:

1. `source` retains the original minimum point, law, singleton atom,
   suffix $\sigma_n$, root word $R_n$, and the exact proof that $R_n$ is
   a cap--Nash stack over the **original** suffix $\sigma_n$.
2. $\tau_n$ is obtained from the literally prefixed source $\Sigma_n$ by
   changing only player $j$'s action at the single date $t_n$ to Quit
   surely.
3. The target has a literal singleton stage of fixed mass
   \[
   \lambda<
   \Pr_{\tau_n}(\text{terminal at }t_n\text{ is }\{j\}).
   \tag{10}
   \]
4. The target and source root words agree at every date other than $t_n$,
   hence in particular throughout the prefix before $a_n$ and throughout
   the complete live-root tail strictly after $t_n$.
5. All opponents of $j$ are unchanged, so $B_j(\tau_n)=B_j(\Sigma_n)$.

The root word copied into $\tau_n$ is literal.  The exact cap--Nash
certificate in item 1 remains a source-side certificate: changing the suffix
can change the other players' caps, so no target-side cap--Nash assertion is
made.

Taking $\lambda=\mu/2$ gives a canonical strong fixed floor.  Taking
$\lambda=\mu^2/8$ gives the scale already shared by the two existing
concentrated-singleton atlas origins.

## Conjecture-facing change

This proves accepted answer 1 of
[`FIN4_ATLAS_DIFFUSE_MINIMUM_SINGLETON.md`](../questions/FIN4_ATLAS_DIFFUSE_MINIMUM_SINGLETON.md).
The source-preserving Fin4 atlas currently retains a separate
`minimumLawSingleton` node because the selected singleton mass may diffuse
through arbitrarily late dates with every original date atom small.  Theorem B
shows that owner-clock diffusion is always removable by one legal one-date
unilateral replacement.

Consequently the directed atlas may replace

```text
minimum-law singleton
```

by

```text
cofinal fixed-resolution concentrated-singleton endpoints.
```

At the level of directed obligations, the minimum-law singleton node therefore
merges into the concentrated-singleton node.  The remaining directed Fin4
obligations are concentrated singleton, quantitative tail escape, and
monodromy.

This is a strict atlas contraction, not a proof of the quitting-game
conjecture.  In particular, it does not consume
[`FIN4_ATLAS_CONCENTRATED_SINGLETON.md`](../questions/FIN4_ATLAS_CONCENTRATED_SINGLETON.md).

## Definitions, probability mode, and agency

The game is the standard discrete-time quitting game.  Before absorption there
is one live public history at each date.  Every player's behavioral action at
that history is an independent PMF on Continue/Quit.  Infinite continuation
is allowed.

The coefficients $\alpha_{a,t}$ form the finite-stop part of $j$'s
conditional post-anchor stopping law; owner Never mass is the possible missing
mass in $A_a\le1$.  The factor $\beta_{a,t}$ includes:

- the complete joint probability of reaching the anchor under the source;
- every opponent's survival from the anchor through date $t$; and
- no artificial conditioning or renormalization.

The target is an actual behavioral profile.  It replaces only $j$'s complete
strategy, and in fact differs from it at only one date.  No public correlating
device, reselected carrier point, stationary restriction, finite-support
restriction, or bounded-deviation assumption is used.

The theorem makes no equilibrium assertion about the target.  Its reference
to unrestricted behavioral caps in (7) is exact only because a player's cap
depends on its opponents' strategies, which are literally unchanged.

## Proof

### 1. Exact source disintegration

The partial sums of the owner masses telescope:

\[
\sum_{t=a}^{T}\alpha_{a,t}
=1-\prod_{r=a}^{T}c_j(r)\le1.
\]

Thus (3) exists as a nonnegative series and $0\le A_a\le1$.

At a date $t\ge a$, a singleton-$j$ terminal requires:

- every player to Continue before $a$;
- $j$ to Continue from $a$ through $t-1$ and Quit at $t$; and
- every opponent to Continue from $a$ through $t$.

Product behavioral randomization therefore gives

\[
\Pr_\sigma(\{j\}\text{ at }t)
=\alpha_{a,t}\beta_{a,t}.
\]

Summing the disjoint terminal dates proves (5).

### 2. The first supported owner date

Since $m_a>0$ and every summand in (5) is nonnegative, some
$\alpha_{a,t}$ is positive.  The positive support is a nonempty subset of
$\mathbb N$, so it has a least member $t_0$.  In particular $A_a>0$.

The opponent-survival factors $\beta_{a,t}$ are nonincreasing in $t$.
Every positive $\alpha_{a,t}$ occurs at a date $t\ge t_0$, hence

\[
m_a
=\sum_{t\ge a}\alpha_{a,t}\beta_{a,t}
\le \beta_{a,t_0}\sum_{t\ge a}\alpha_{a,t}
=\beta_{a,t_0}A_a.
\]

Division by $A_a>0$, followed by $A_a\le1$, gives (6).

There is no hidden interval modification.  Starting at $a$, an induction
shows that $j$'s conditional survival remains one before $t_0$: if it is
one at $r<t_0$, then $\alpha_{a,r}=0$ forces $q_j(r)=0$, hence
$c_j(r)=1$.  Thus $j$ already plays pure Continue on every intervening
live row.

Changing only its action at $t_0$ to pure Quit exposes singleton stage mass
exactly $\beta_{a,t_0}$.  The literal one-date definition gives all profile
and tail equalities.  Since no opponent changes, the set of payoff values of
all unilateral behavioral deviations by $j$ is identical, proving (7).

### 3. Composition with the minimum-law source

Let

\[
m_n=\Pr_{\sigma_n}(Q=\{j\}),
\qquad
P_n=\operatorname{ContinueProduct}(R_n).
\]

Joint semantic/law convergence gives $m_n\to\mu$.  Exact source cap-stack
debt scaling, convergence of both source and prefixed debts to the same
positive minimum, gives $P_n\to1$.  This is precisely the checked theorem
`QuittingNonsingletonMinimumLawTransfer.tendsto_capNashStackContinueProduct_one`;
despite its namespace, its statement has no nonsingleton-cardinality premise.

Exact stage transport through a literal root stack and time disintegration
give

\[
\sum_{t\ge a_n}
 \Pr_{\Sigma_n}(\{j\}\text{ at }t)
=P_nm_n\longrightarrow\mu.
\tag{11}
\]

Given $0<\lambda<\mu$ and $N$, choose $n\ge N$ with the left side of
(11) greater than $\lambda$.  Apply Theorem A to $\Sigma_n$ at anchor
$a_n$.  Its literal one-date target has stage mass at least the whole
quantity in (11), hence strictly greater than $\lambda$, and has all the
claimed provenance.

## Boundary tests

### Diffuse owner clock

Let the owner choose uniformly among $N$ dates and let every opponent Never
Quit.  Every original singleton stage mass is $1/N$, while the first-date
one-shot compression exposes singleton mass one.  Thus the theorem genuinely
removes owner-clock diffusion rather than assuming an original large atom.

### Sharpness of $m_a/A_a$

In a two-player chronology, let the opponent survive through the owner's first
possible post-anchor date with probability $c$, and let the owner's entire
conditional finite-stop mass $A$ occur at that date.  Then

\[
m_a=Ac,
\qquad
\beta_{a,t_0}=c=m_a/A_a.
\]

Taking $A=1$ gives equality $\beta_{a,t_0}=m_a$.  No universal
source-level lower bound strictly larger than $m_a$ is possible.

### Never mass and gaps

Positive owner Never mass merely makes $A_a<1$, strengthening the quotient
bound.  Gaps in the finite stopping support cause no problem because
$\mathbb N$ is well ordered.  Zero probability of reaching the anchor forces
$m_a=0$ and is excluded by the theorem's premise.

### Limit sharpness

For an individual source profile, the exposed mass is at least its complete
anchored singleton mass.  In the atlas family these actual masses may approach
$\mu$ from below, so a fixed $\lambda<\mu$ is guaranteed cofinally while a
uniform floor exactly equal to the limiting $\mu$ is not.

## Source correspondence and freshness

The proof uses the following checked declarations:

- `quittingHazardStopMass_eq_survival_mul_stop`,
  `hasSum_quittingHazardStopMass`, and
  `quittingBehaviorStoppingLaw_some_toReal` in
  `UniformEquilibrium/Quitting/Paths/BehaviorStoppingLaw.lean`;
- `quittingStageCoalitionMass` and
  `quittingTerminalOutcomeMass_eq_timeDisintegration` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPlateauTimeDisintegration.lean`;
- `quittingLiteralOneDateProfile` and
  `quittingProfileLiveRoot_literalOneDateProfile_tail_eq` in
  `Research/Quitting/SameStageEndpointMonodromy.lean`;
- `quittingStageCoalitionMass_literalRootStack_add_length` and
  `QuittingMinimumLawCausalSuffixAtom` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticLawCarrierCausalization.lean`;
- `QuittingNonsingletonMinimumLawTransfer.tendsto_capNashStackContinueProduct_one`
  in `Research/Quitting/NonsingletonMinimumLawLinearTransfer.lean`; and
- `FinFourMinimumAtomProducer` and the current atlas endpoint types in
  `Research/Quitting/FinFourProducerAtlas/Source.lean` and
  `Research/Quitting/FinFourProducerAtlas/SemanticConnections.lean`.

Nearby stopping-law ledgers, pure-time deviations, Continue-prefix access, and
nonsingleton anti-diffusion do not state this result.  The new content is the
first-supported-date domination, its sharp one-date actual-profile output,
and its cofinal composition with the minimum-law cap-stack source.  No paper
result is invoked.

## Adapter and endpoint interface

The result is itself an arbitrary-source adapter for the atlas
`minimumLawSingleton` constructor.  It outputs the actual fixed-resolution
profile, singleton, marked date, reference source, and literal tail equality
required by the concentrated-singleton question.

The current `FinFourAtlasConcentratedSingletonEndpoint` universally projects
a `FinFourLowTailRow`, because its two existing origins both arise from the
nonsingleton low-tail construction.  Clock compression does not produce that
row and must not fabricate it.

The safe Lean design is additive:

1. retain the current strong endpoint and both old origins unchanged;
2. add a broader common concentrated-singleton endpoint core containing an
   actual reference profile, target profile, stage, singleton, positive mass
   floor, and literal post-date live-root equality;
3. map each old endpoint into the broader core while retaining its old origin
   as provenance; and
4. add an owner-compressed origin retaining the full minimum-law causal
   chronology and the source-side exact cap-stack certificate.

Current source search finds no downstream mathematical consumer of the old
endpoint's universal `.low` projection.  The directed node occurs additionally
in `SemanticCoverage.lean`, so the atlas normalization can be extended without
discarding an existing consumer theorem.

## Lean handoff

A narrow implementation order is:

1. Define the anchored owner finite-stop mass $A_a$ and post-anchor
   singleton mass $m_a$, or express them with the existing stopping-law and
   stage-mass series.
2. Select the least positive owner stop mass with `Nat.find`.
3. Prove the division-free estimate
   \[
   m_a\le A_a\beta_{a,t_0},
   \]
   then derive (6).
4. Use `quittingLiteralOneDateProfile` and
   `quittingProfileLiveRoot_literalOneDateProfile_tail_eq`; do not create a
   new interval-splice primitive.
5. Prove the post-anchor stack identity by summing
   `quittingStageCoalitionMass_literalRootStack_add_length`.
6. Compose joint-law convergence with
   `tendsto_capNashStackContinueProduct_one` to obtain the cofinal adapter.
7. Introduce the additive broad endpoint core and map the three origins into
   it without asserting a low-tail field or target-side stack exactness.

Suggested declarations:

```lean
theorem exists_literalOneDate_singletonStageMass_ge_tailSingletonMass ...

theorem FinFourMinimumAtomProducer.exists_cofinal_ownerCompressedSingleton ...
```

The formal proof must derive the target profile and inequalities from the
source data; it must not place them in an assumed certificate structure and
project them back out.

## Scope and nonclaims

- The compressed target generally has a different terminal law and semantic
  pair from the minimum point.  It retains a pointer to that source and its
  actual chronology, not equality with it.
- The target copied prefix need not be cap--Nash against its changed suffix.
- No debt, local-Nash, punishment-floor, low-tail, return, or recurrence-path
  property is asserted for the target.
- No restriction on arbitrary behavioral deviations is needed for the mass
  construction, but the theorem does not bound their gains.
- The result transfers the minimum-law singleton node to the
  concentrated-singleton obligation.  It does not prove terminal
  approximants, a uniform-equilibrium payoff, or the finite-quitting
  conjecture.

## Formalization record

The maintained checked realization is Research-only and is reachable through
`Research/Quitting/FinFourExhaustiveProducerAtlas.lean`.

1. `Research/Quitting/AnchoredSingletonClockCompression.lean` defines
   `quittingAnchoredOwnerFiniteStopMass`,
   `quittingAnchoredSingletonExposureMass`,
   `quittingAnchoredOwnerFiniteStopTotal`,
   `quittingAnchoredSingletonTailMass`, and
   `quittingAnchoredSingletonQuitProfile`.  The exact factorization and
   disintegration are
   `quittingStageCoalitionMass_singleton_eq_anchoredOwner_mul_exposure` and
   `quittingAnchoredSingletonTailMass_eq_tsum_mul`.
   `exists_least_positive_quittingAnchoredOwnerFiniteStopMass` selects the
   least supported owner date, and
   `quittingProfileLiveRoot_eq_pure_false_before_anchoredOwnerSupport` proves
   that the source owner already Continues surely at every intervening live
   row.  The declarations
   `quittingStageCoalitionMass_anchoredSingletonQuitProfile_eq_exposure`,
   `quittingAnchoredSingletonTailMass_div_total_le_exposure`, and
   `quittingAnchoredSingletonTailMass_le_exposure` give respectively the exact
   target singleton mass, the normalized `m / A` bound, and the no-loss bound
   from the complete anchored source singleton tail to the target stage.
   `quittingAnchoredSingletonQuitProfile_at_of_ne`,
   `quittingAnchoredSingletonQuitProfile_opponent_eq`,
   `quittingAnchoredSingletonQuitProfile_liveRoot_tail_eq`, and
   `quittingAnchoredSingletonQuitProfile_owner_cap_eq` expose the exact
   off-date, opponent, post-date-tail, and unrestricted owner-cap equalities.
   `exists_quittingAnchoredSingletonClockCompression` packages the sharp
   arbitrary-profile theorem, while
   `tsum_quittingStageCoalitionMass_literalRootStack_postAnchor` gives exact
   transport of the summed post-anchor singleton mass through a literal finite
   root stack.
2. `Research/Quitting/FinFourProducerAtlas/MinimumSingletonClockCompression.lean`
   defines `FinFourMinimumAtomChronology`,
   `FinFourOwnerCompressedSingletonEndpoint`, and the canonical
   `FinFourOwnerCompressedSingletonProducer`.
   `FinFourMinimumAtomChronology.prefixedTailMass_eq_continueProduct_mul_terminalMass`
   and `FinFourMinimumAtomChronology.tendsto_prefixedTailMass` compose the
   retained minimum-law cap-stack source with the generic theorem.  The exact
   quantifier order of
   `FinFourMinimumAtomProducer.exists_commonChronology_cofinal_ownerCompressedSingleton`
   is
   ```text
   exists chronology, for every lambda with 0 < lambda < mu,
     for every depth, Nonempty endpoint.
   ```
   Thus one actual profile/root chronology is selected before both the
   resolution and depth quantifiers.  The declaration
   `FinFourMinimumAtomProducer.nonempty_ownerCompressedSingletonProducer`
   specializes this one chronology to
   `FinFourMinimumAtomProducer.minimumSingletonClockResolution = mu^2 / 8`
   and retains endpoints cofinally in the requested depth.  The endpoint
   accessors expose its unmodified suffix and root stack, literal reference
   and one-date target, marked stage, singleton, strict mass floor, pure-
   Continue interval, exact off-date/prefix/post-date live-root equalities,
   unchanged opponents, and exact owner-cap equality.  Its
   `FinFourOwnerCompressedSingletonEndpoint.rootStack_nash` certificate is
   explicitly source-side: it is over the unmodified suffix, not the changed
   target.
3. `Research/Quitting/FinFourProducerAtlas/SemanticConnections.lean` leaves
   `FinFourAtlasConcentratedSingletonEndpoint` and its two old origins
   unchanged.  It adds `FinFourAtlasWeakConcentratedSingletonOrigin` and
   `FinFourAtlasWeakConcentratedSingletonCore`.  The owner-clock origin stores
   the full cofinal `FinFourOwnerCompressedSingletonProducer` together with
   one selected depth-zero endpoint; it does not discard the common
   chronology after selecting that endpoint.  The weak core exposes only the
   common reference profile, target profile, marked stage, literal singleton,
   `mu^2 / 8` mass floor, literal post-date live-root equality, and derived
   semantic-tail equality.  The common mass theorem
   `FinFourAtlasWeakConcentratedSingletonCore.resolution_le_stageMass` is weak
   because that is the shared conclusion of the old reached routes; the new
   owner-clock route itself retains a strict floor.

   The same module defines the three-constructor
   `FinFourAtlasClockCompressedDirectedNode` and proves
   `FinFourProducerResidual.nonempty_clockCompressedDirectedNode`.  All six
   source-indexed residual constructors map forward to weak concentrated
   singleton, quantitative tail escape, or monodromy.  The
   `minimumSingleton` case calls the actual canonical producer and selects its
   base endpoint; every other branch retains its original source and producer
   data.
4. `Research/Quitting/FinFourProducerAtlas/SemanticCoverage.lean` proves
   `uniformPayoff_or_nonempty_finFourAtlasClockCompressedDirectedNode` for an
   arbitrary bounded Fin4 reward table.  The existing uniform-payoff arm is
   unchanged, and only the six-leaf residual arm is passed through the checked
   three-node adapter.

Evidence seals:

- **M:** PASS.  The sharp weighted-domination proof, boundary tests, source
  correspondence, cofinal composition, and additive-endpoint design were
  retained after the independent reviews linked at the head of this packet.
- **L:** PASS.  The two new modules and the two additive semantic modules are
  checked Lean and reachable through the reader atlas and `Research` umbrella.
  Direct module checks, named reader and umbrella builds, the full build,
  trust scan, import-graph check, documentation check, proof-duplicate check,
  derivable-telescope check, axiom-audit freshness check, and source-format
  checks passed at promotion.
- **A:** PASS.  The generic capstone starts from an arbitrary actual profile,
  owner, anchor, and positive anchored singleton-tail mass.  The Fin4 capstone
  starts from arbitrary bounded reward data and returns the existing
  uniform-payoff arm or one actual source-indexed three-node residual.  No
  date, owner stop atom, chronology, endpoint, minimum point, or atlas residual
  is supplied to those respective adapters.
- **C:** ABSENT.  No weak concentrated core, tail escape, or monodromy node is
  consumed by a checked completion theorem.

The three-node map is one-way producer normalization, not an equivalence or a
claim that the nodes are unique or mutually exclusive.  The compressed target
is not asserted to have the source minimum's terminal law or semantic pair,
to be cap--Nash, near-minimal, or reprojected to the terminal-semantic carrier.
No target debt, local-Nash, punishment-floor, low-tail, return, recurrence,
regeneration, terminal-approximation, completion-closure, or uniform-payoff
consumer is proved.  In particular, the source-side exact cap-stack
certificate is not transported across the changed suffix.

The mathematical provenance is the packet assembled by ChatGPT External,
STRENGTHENER, and Codex Root, together with the independent ATLAS_FALSIFIER,
STRENGTHENER, and ATLAS_GATEKEEPER reviews linked at the head of the packet.
No external paper theorem is imported.
