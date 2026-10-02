# Finite source-faithful chronological quotients: the residual-height obstruction

**Identity:** CODEX_STRENGTHEN  
**Date:** 2026-08-30--31  
**Status:** ordinary mathematics based on the named checked declarations.
There is no finite source-faithful, charge-reflecting quotient of an exact
Fin4 hard spine with infinitely many positive stages.  If there are only
finitely many positive stages, the spine is eventually the literal
all-Continue phantom, so a finite path presentation exists but has no
terminal consumer.  The minimal faithful lift retains an algebraic
continuation, an actual tail-source port, and a real residual-charge height.
The height can be made compact and closed on one uniformly summable shift
hull, but it gives a Zeno approach to the nonterminal phantom, not a finite
rank or return.  The checked finite-forward-packet compiler does bypass a
finite quotient, but the law-tight saturation hull supplies only
debt-budgeted exact forward packets.  Same-law replacements either preserve
the displayed cap, in which case they cannot recharge the budget, or break
the packet's exact Bellman seam.  Approximate support errors can pay an
unbounded charge only through a nonsummable aggregate error budget; the
positive terminal-debt minimum does not control a packet lacking semantic
cap provenance.  On the actual positive-debt tail, a boundary-calibrated
remaining-capacity account dominates the owner's exact debt and converges to
it; finite contact forces the checked zero-source face.  A compact one-ray
regression shows that contact need occur only at the all-Continue boundary,
so joint/scalarized minimization does not select a finite source.
For the newly checked Fin4 law-tight source, global minimality collapses the
entire saturation hull exactly to the fixed-law global-minimum fibre; every
hull prefix is all Continue and has zero hazard.  Thus bounded exact-block
capacity cannot consume the strict chambers without a new off-fibre
chronological port.  Section 15 proves a sharp obstruction to that missing
port: a law-tight near-minimum literal attachment with fixed marginal-hazard
charge cannot have a vanishing cumulative cap-Nash seam.  Exact endpoint
matching is impossible, and even an endpoint mismatch tending to zero must
obey a positive horizon-times-mismatch lower bound.  Sections 15.6--15.8
convert the entire forced seam, without a horizon loss, into one uniformly
reached paid first disagreement lying inside the literal block.  The existing
paid-cap port forgets this block location and may be inert at the minimum
fibre, so the missing consumer is now exactly a cut/ancestry-preserving
paid-row port.  Section 16 records the independently reviewed strengthening
that global source minimality eliminates the singleton/Never chamber,
leaving only full debt support and reset-rigid same-law return.
Section 17 shows that the reset owner's coordinate ledger necessarily
vanishes along a near-return, so the macroscopic paid seam cannot be aligned
to that owner or to the retained premium atom with the current fields; an
independent owner-paid row of asymptotic gain `D_*` exists, but it sits on a
zero-hazard all-Continue prefix and does not spend capacity.  Its strongest
form is a literal owner-toggle pair with identical opponents, exact common
owner cap, exact own-debt subtraction, a minimum-law all-Continue endpoint,
and a pure-singleton-prefix semantic limit.  The existing strong singleton
and paid-cap adapters can accept projections of this pair but erase the
two-endpoint coupling; the forced-pair interfaces do not accept it.

This continues
[`CODEX_STRENGTHEN__FIN4_CAPACITY_POTENTIAL_STATIC_TOPOLOGY_SEPARATION.md`](CODEX_STRENGTHEN__FIN4_CAPACITY_POTENTIAL_STATIC_TOPOLOGY_SEPARATION.md).
It does not prove the Fin4 conjecture and does not manufacture a source
regeneration.

## 1. Question and source audit

Fix a Fin4 reward table and, under the hypothetical no-uniform-payoff branch,
one canonical exact Nash--Bellman spine

\[
 v_n=F_{x_n}(v_{n+1}),qquad
 x_n\text{ exact root Nash against }v_{n+1}.
\]

Write

\[
 q_{n,i}=\Pr_{x_n}(i\text{ Quits}),qquad
 h_n=\sum_iq_{n,i},qquad s_n=(v_n,x_n).
\]

The intended quotient should be finite, should let its successor transitions
compose as actual source operations, and should retain enough quantitative
information that a positive quotient loop is a genuinely positive exact
chronological loop rather than a horizontal label cycle.

### Checked declarations

I used only the following source neighborhood.

* `IsQuittingNashBellmanEdge`,
  `isClosed_quittingNashBellmanEdgeGraph`,
  `exists_bounded_exact_quittingNashBellmanSpine`, and
  `exists_exact_quittingNashBellmanSpine` in
  `UniformEquilibrium/Quitting/Bellman/Finite/NashBellmanSpine.lean`.
  The edge orientation is current annotation to tail annotation; the current
  root is exact Nash against the tail value.
* `IsCanonicalExactQuittingNashBellmanSpine` and
  `canonicalPhantom_isExactQuittingNashBellmanSpine` in
  `UniformEquilibrium/Quitting/Bellman/Finite/NashBellmanClockReduction.lean`.
  The constant reward-bound/all-Continue phantom is a checked exact spine for
  every reward table.
* `all_marginalQuitHazards_summable_of_no_uniformPayoff` in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/FullSupportHardNashBellmanSpine.lean`.
  Under no Fin4 uniform payoff, every marginal stream of every supplied
  canonical exact spine is summable.
* `QuittingFiniteExactNashBellmanBlock`,
  `HasBoundedFiniteExactNashBellmanHazardCapacity`, and
  `hasBoundedFiniteExactNashBellmanHazardCapacity_iff` in
  `UniformEquilibrium/Quitting/Bellman/Finite/UnboundedExactBlockHazardCapacity.lean`,
  together with
  `finFour_hasBoundedFiniteExactNashBellmanHazardCapacity_of_no_uniformPayoff`
  in
  `UniformEquilibrium/Diagnostics/Quitting/FinFourUnboundedExactBlockHazardCapacity.lean`.
* `quittingRootSequenceProfile_eq_shift` in
  `UniformEquilibrium/Quitting/Cycles/PhaseSwitchProfile.lean`.  It identifies
  the actual behavioral source generated by a shifted root path.
* `QuittingFiniteForwardPacket` and
  `quittingGame_exists_uniformEquilibriumPayoff_of_finiteForwardPackets` in
  `UniformEquilibrium/Quitting/Projective/FiniteForwardProjectiveLasso.lean`,
  and `QuittingPunishmentFloorFinitePrefix.toForwardPacket` plus
  `quittingGame_uniformPayoff_or_bounded_floorPrefixCharge` in
  `UniformEquilibrium/Quitting/Bellman/Finite/PunishmentFloorFinitePrefix.lean`.
  Packet policy is exact forward Bellman transport, local Nash is only
  support-approximate, and packet charge is joint absorption mass rather than
  total marginal hazard.
* `quittingTerminalSemanticPrefix_envelope_eq_rootSuccessorPayoff_of_capNash`
  and `quittingTerminalSemanticDebt_prefix_eq_continueMass_mul_of_capNash` in
  `UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`;
  `quittingPunishmentValue_le_terminalSemanticEnvelope` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticAtomicSupportBoundary.lean`;
  and the literal-chain bounds
  `sum_quittingRootAbsorptionMass_le_hullDebtDrop_div_minimum` and
  `sum_quittingRootAbsorptionMass_le_initialHullDebtExcess_div_minimum` in
  `UniformEquilibrium/Diagnostics/Quitting/LawTightCapNashMinimumFace.lean`.
* `sum_quittingRootAbsorptionMass_le_card_div_mul_sum_error` in
  `UniformEquilibrium/Quitting/Root/StrictAllContinueBasinLinearAbsorptionDefect.lean`.
  This checked local strict-basin estimate controls aggregate absorption by
  the **sum** of declared errors; it does not turn one constant per-stage
  error into a horizon-free capacity bound.
* `minimumTerminalSemantic_singletonMargin` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticAuxiliaryNashBudget.lean`,
  `FinFourSingletonStageStrongConcentratedPacket.nonempty_of_singleton_stageMass`
  and `FinFourSingletonStageStrongConcentratedPacket.consumerResult` in the
  two `Research/Quitting/FinFourProducerAtlas/StrongConcentratedPacket*.lean`
  files, `QuittingPaidCapLiftedSource` and
  `exists_quittingPaidFirstDisagreementRow_of_pureTimePayoff_sub` in the
  stopping-law endpoint diagnostics, and the source-dependent forced-pair
  structures in `Research/Quitting/FinFourProducerAtlas/ForcedPair.lean` and
  `MinimumReturnForcedPair.lean`.  These are the checked interface boundaries
  used in Sections 16--17; the literal two-profile bundle there is ordinary
  mathematics, not a named checked declaration.
* The audited ordinary-mathematics interfaces in `arch/GRAMMAR.md`,
  `arch/EXECUTABLE_COMPACT_STATE.md`, `arch/EXECUTABLE_COMPLETE.md`, and
  `exports/EXECUTABLE_ADAPTER_GRAMMAR_AND_CONSTRAINED_ROOT_NO_GO.md`.
  In particular, an executable trace successor needs a closed selected edge
  or decoder; a finite tag, strict real decrease, or nonclosed optimizer is
  not a compiler.

The no-go below is different from the exported maximal-root no-go.  No
optimized selector is used: the exact Bellman edge relation is already
closed.  The obstruction is the attempted finite collapse of infinitely many
positive but summable chronological tolls.

## 2. The actual enriched tail state

For each `n`, let

\[
 \sigma_n:=\text{the actual root-sequence profile generated by }
 (x_n,x_{n+1},\ldots).
\]

Let `lambda_n` be its complete terminal-coalition law and let
`(U_n,B_n)` be its actual terminal semantic pair: prescribed terminal payoff
and unrestricted behavioral cap.  Define the displayed enriched node

\[
 Z_n=(v_n,x_n;\sigma_n,\lambda_n,U_n,B_n).
\tag{2.1}
\]

There are two distinct exact statements at each step:

1. **algebraic edge:** `s_n -> s_{n+1}` is an exact Nash--Bellman edge; and
2. **actual composition:** prefixing the named actual tail `sigma_{n+1}` by
   the product root `x_n` gives `sigma_n`.

They run in opposite construction directions.  Bellman chronology is
current-to-tail, while the elementary behavioral compiler builds
current-from-tail by prefixing.  Following the chronology forward therefore
requires either a retained continuation port `sigma_{n+1}` or a certified
positive-reach suffix operation.  A semantic label on `sigma_n` is not such a
port.

The algebraic continuation also cannot silently be replaced by the actual
semantic coordinates.  The root `x_n` is checked exact against `v_{n+1}`;
the spine theorem does not assert

\[
 v_{n+1}=U_{n+1}\quad\text{or}\quad v_{n+1}=B_{n+1}.
\tag{2.2}
\]

The canonical phantom exposes this boundary mismatch: its algebraic value is
the reward bound, while its actual source is all Never, whose payoff is zero
and whose unrestricted cap is the solo-clipped vector
`max(r_i({i}),0)`.  Thus adding actual law and cap data does not eliminate the
need to retain the algebraic continuation value.

### Proposition 2.1 (late actual-source convergence)

Under the no-uniform-payoff hypothesis,

\[
 \sigma_n\longrightarrow\sigma^{\mathrm{Never}}
 \quad\text{in total variation},                         \tag{2.3}
\]

and hence `lambda_n`, `U_n`, and `B_n` converge to the all-Never semantic
data.  Also `x_n` tends to all Continue and `v_n` converges to a vector `b`.

#### Proof

All marginal series are summable.  For player `i`, the probability of ever
quitting in the tail from `n` is bounded by

\[
 1-\prod_{k\ge n}(1-q_{k,i})
 \le \sum_{k\ge n}q_{k,i}\longrightarrow0.
\]

The `ell^1` distance of that stopping-time law from `delta_infinity` is twice
its finite-time mass, proving (2.3).  The terminal law, payoff, and complete
unilateral cap are total-variation continuous by the executable-state
estimates.

Summability gives `q_{n,i}->0`, hence `x_n->all Continue`.  If `R` is the
reward bound and `alpha_n` is the joint absorption probability, exact Bellman
recursion gives

\[
 \|v_n-v_{n+1}\|_\infty\le2R\alpha_n\le2R h_n.
\]

The right side is summable, so `(v_n)` is Cauchy.  QED.

There is also a useful executable positive fact.  The one-step joint
all-Continue reach satisfies

\[
 c_n=\prod_i(1-q_{n,i})\ge1-h_n\longrightarrow1.
\tag{2.4}
\]

Thus after one finite threshold every forward tail extraction has, for
example, reach at least `1/2`.  The **infinite** late tail system can therefore
be represented by positive-reach suffix edges.  This does not make its state
set finite.

## 3. The global capacity potential

On the canonical Nash--Bellman box define the capacity potential from the
preceding note:

\[
 \Phi(s)=\sup\{\text{total hazard of a finite exact path beginning at }s\}.
\tag{3.1}
\]

Bounded exact-block capacity makes `Phi` finite and gives, for every exact
edge `s->t`,

\[
 \Phi(s)\ge h(s)+\Phi(t).                               \tag{3.2}
\]

Along the selected spine, `Phi_n:=Phi(s_n)` is nonincreasing and is strictly
decreasing whenever `h_n>0`.  It therefore converges to some real limit.
Nothing in the checked capacity theorem says that `Phi` is continuous or
that this limit equals `Phi` of the phantom limit state.

For the selected spine itself there is a sharper source-attached height:

\[
 \Psi_n:=\sum_{k\ge n}h_k.                              \tag{3.3}
\]

It obeys the exact conservation law

\[
 \Psi_n=h_n+\Psi_{n+1},\qquad \Psi_n\downarrow0.         \tag{3.4}
\]

`Phi` is a global supremum over all exact continuations; `Psi` is the exact
remaining charge of this named actual chronology.  The distinction matters
for compactness below.

## 4. Three meanings of a finite quotient

Let `Q` be finite and let `pi_n in Q` label the enriched nodes `Z_n`.

1. A **mere label quotient** records only the transition
   `pi_n -> pi_{n+1}`.  It has no splicing content.
2. A **charge-reflecting quotient** assigns every used transition
   `(a,b)` a toll `eta(a,b)>=0` such that

   \[
   h_n\ge\eta(\pi_n,\pi_{n+1}),
   \qquad h_n>0\Longrightarrow
   \eta(\pi_n,\pi_{n+1})>0.                              \tag{4.1}
   \]

   Exact factorization of `h_n` through the finite transition set is a
   special case.
3. A **splice-sound quotient** supplies an actual endpoint-matched reset:
   whenever `pi_a=pi_b`, the literal exact block from `Z_a` to `Z_b` may be
   repeated as an actual source-faithful exact Nash--Bellman block.  This is
   the strength needed to turn a quotient loop into a capacity contradiction.

A quotient is **Phi-exact** when some `phi:Q->R` satisfies

\[
 \Phi(s_n)=\phi(\pi_n)\quad\text{for every }n.            \tag{4.2}
\]

These definitions separate the common hidden step: equality of a support,
face, coalition, law class, or finite branch tag does not supply the reset in
item 3.

## 5. Finite quotient dichotomy

### Theorem 5.1 (infinite positive support forbids every useful finite quotient)

If `h_n>0` for infinitely many `n`, then the selected spine has:

1. no finite Phi-exact quotient;
2. no finite charge-reflecting quotient; and
3. no finite splice-sound quotient.

#### Proof

Choose prefix indices immediately after successive positive stages.  Since
`Q` is finite, two such indices `a<b` have the same label and the intervening
charge

\[
 H[a,b]=\sum_{n=a}^{b-1}h_n
\]

is positive.

If the quotient is Phi-exact, summing (3.2) gives

\[
 \phi(\pi_a)=\Phi(s_a)
 \ge H[a,b]+\Phi(s_b)
 =H[a,b]+\phi(\pi_b),
\]

contradicting `pi_a=pi_b`.

For a charge-reflecting quotient, infinitely many positive stages use only
finitely many transition labels.  One positive-toll transition recurs
infinitely often.  Its fixed positive toll makes `sum h_n` diverge,
contradicting the checked marginal summability.

For a splice-sound quotient, repeat the positive exact block from `a` to `b`.
This creates finite exact blocks of arbitrarily large total hazard,
contradicting bounded exact-block capacity.  QED.

Thus a finite mere label quotient may certainly exist, but any positive loop
in it is horizontal: the endpoint seam or remaining-capacity height has been
forgotten, so the loop cannot be renewed.

### Theorem 5.2 (finite positive support is exactly the phantom exit)

If `h_n>0` only finitely often, then from some `N` onward

\[
 x_n=\text{all Continue},\qquad v_n=v_N,qquad
 \sigma_n=\sigma^{\mathrm{Never}}.                       \tag{5.1}
\]

Hence the chosen path has a finite literal presentation: retain every node
before `N` and one zero-charge phantom state afterward.

#### Proof

For `n>=N`, nonnegativity and `h_n=0` force every marginal Quit probability
to be zero.  The all-Continue Bellman update is the identity, so all later
values agree.  The generated tail source is all Never.  QED.

This finite presentation does not meet the finite-automaton consumer.  Its
last state is a zero-charge self-loop, not a terminal Nash certificate.  In
the no-uniform-payoff branch it cannot be declared terminal merely because it
is all Never: an exact terminal Nash profile would feed the checked
terminal-to-uniform consumer and contradict the branch hypothesis.

Combining Theorems 5.1--5.2 gives the promised exhaustive answer for every
checked canonical exact hard spine:

\[
\boxed{
\begin{array}{c}
\text{infinitely many positive stages: no finite useful quotient;}\\
\text{finitely many positive stages: finite presentation ending at a}\\
\text{nonterminal all-Continue/all-Never phantom.}
\end{array}}
\tag{5.2}
\]

## 6. Why the global `Phi` is not automatically an executable coordinate

The supremum potential has the right order inequality, but compactness of the
edge relation does not make `Phi` continuous.  The following smallest useful
regression is independent of quitting games.

Let

\[
 K=\{o\}\cup\{p_{m,k}:m\ge1,\ 0\le k\le m\}
 \subset\mathbb R^2,
\]

where

\[
 o=(0,0),\qquad p_{m,k}=(1/m,k/m^2).
\]

Put

\[
 h(p_{m,k})=1/m\ (k<m),\qquad h(p_{m,m})=h(o)=0.
\]

The directed edges are

\[
 p_{m,k}\to p_{m,k+1}\ (k<m),qquad
 p_{m,m}\to p_{m,m},qquad o\to o.
\tag{6.1}
\]

Then `K` is compact, `h` is continuous, the edge graph is closed and serial,
and every finite path has charge at most one.  Nevertheless

\[
 \Phi(p_{m,0})=1\quad\text{for every }m,qquad \Phi(o)=0,
\]

while `p_{m,0}->o`.  Thus the graph of the canonical supremum potential is
not closed.

This is not the nonclosed optimized-root example from the executable export.
Here the transition graph and toll are already closed and continuous; taking
the supremum over arbitrarily long finite futures creates the discontinuity.
Consequently, writing `Phi` into a compact trace requires a separate closed
graph, decoder, or defect theorem.  The capacity inequality alone does not
provide one.

The same regression shows why exact remaining charge is nonlocal on a family
without a uniform tail budget.  Let `z^m` be the infinite path that traverses
the `m`-chain and then stays at `p_{m,m}`.  Coordinatewise in path space,

\[
 z^m\longrightarrow(o,o,o,\ldots),
\]

but the total charges are one, while the limiting path has charge zero.  The
graph of “exact total future charge” is therefore not closed on the full
compact path space.

## 7. Exact `Psi`: closed balance versus ghost capacity

There are two different ways to adjoin a residual coordinate.

### 7.1 The local balance relation

On `K x [0,C]`, put

\[
 (s,\psi)\ \widetilde E\ (t,\psi')
 \quad\Longleftrightarrow\quad
 sEt\ \text{ and }\ \psi=h(s)+\psi'.                    \tag{7.1}
\]

If `E` is closed and `h` continuous, this relation is closed on a compact
space.  It makes every positive toll exactly visible.

But (7.1) alone does not say that `psi` is the actual remaining charge.  On a
zero-charge self-loop it permits

\[
 (o,\psi)\widetilde E(o,\psi)
\]

for every `psi in [0,C]`.  These are **ghost budgets**.  The desired least
solution is selected by the nonlocal transversality condition

\[
 \psi_n\longrightarrow0.                                  \tag{7.2}
\]

The chain regression in Section 6 proves that exact selection by (7.2) is not
closed on arbitrary bounded-capacity path families.

### 7.2 Uniform-tail theorem

There is a sharp positive repair.

#### Theorem 7.1 (compact exact residual-charge lift)

Let `X` be a compact shift-invariant family of infinite paths in a compact
closed charged graph.  Suppose the family has a uniform tail modulus:

\[
 \sup_{z\in X}\sum_{k\ge N}h(z_k)\longrightarrow0.
\tag{7.3}
\]

Then

\[
 \Psi(z)=\sum_{k\ge0}h(z_k)                                \tag{7.4}
\]

is continuous on `X`, its graph is compact, and

\[
 \Psi(z)=h(z_0)+\Psi(Sz).                                  \tag{7.5}
\]

The enriched shift system `(z,Psi(z))->(Sz,Psi(Sz))` is therefore a compact
closed Markov state with exact charge visibility.

#### Proof

The finite partial sums in (7.4) are continuous.  Condition (7.3) makes them
converge uniformly to `Psi`, so `Psi` is continuous.  Compactness of its graph
and (7.5) are immediate.  QED.

For the shift hull of one fixed hard spine, (7.3) holds:

\[
 \sup_{n\ge0}\sum_{k\ge N}h_{n+k}
 \le\sum_{j\ge N}h_j\longrightarrow0.                    \tag{7.6}
\]

Together with Proposition 2.1 and the late reach floor (2.4), this yields a
genuine positive construction: the tail-orbit closure, enriched by actual
source law, semantic pair, algebraic value/root, and exact `Psi`, is compact;
its late successor shift is executable on a fixed positive-reach domain; and
the charge balance is closed.

This construction is infinite-state.  It gives neither a return nor a
well-founded rank.  If positive stages occur infinitely often, `Psi` strictly
decreases infinitely many times and tends to zero.  Its omega-limit is the
all-Continue/all-Never phantom.  If positive stages stop, that phantom is
reached literally.  Thus both branches have the same terminal boundary.

### 7.3 Uniform barrier, but no consumer

Condition (7.3) gives a finite-depth barrier statement: for every
`epsilon>0`, there is one `N` such that

\[
 \Psi(S^N z)\le\epsilon\qquad(z\in X).                    \tag{7.7}
\]

It does not give a terminal statement at that barrier.  Sending
`epsilon->0` reaches the phantom, whose actual terminal debt can remain
positive.  Resetting from small `Psi` to a new source with large residual
charge is not a return inside the same capacity account; it is a regeneration
and needs its own source rank, ancestry, and backward consumer.

## 8. The eventual phantom and the terminal-gap passport

### Proposition 8.1 (terminal gap does not eliminate the algebraic phantom)

A terminal exploitability gap, positive terminal debt, and the exact actual
cap of the all-Never source do not contradict an eventual canonical phantom.

Indeed, `canonicalPhantom_isExactQuittingNashBellmanSpine` constructs the
algebraic phantom for **every** reward table.  At its actual all-Never source,

\[
 U_i=0,qquad B_i=\max\{r_i(\{i\}),0\}.                  \tag{8.1}
\]

A terminal gap says that some unrestricted deviation improves on `U`; it
therefore confirms that the source is nonterminal.  It does not refute the
one-stage statement that all Continue is exact against the separate algebraic
continuation `b`, nor does it select a positive exact successor.  Positive
global minimum is also compatible with (8.1): it only gives a positive lower
bound on the debt `B-U`.

Thus the phantom exit can be consumed only by an additional bridge, such as
`b=U` plus exact root Nash, `B=U`, or a separate delayed-switch/punishment
certificate.  None follows from the canonical-spine and terminal-gap fields.

### Proposition 8.1A (a retained atom does not eliminate the forward saturation phantom)

There is a second, easily conflated all-Continue boundary.  Let `P` be a
positive-debt minimum point of a law-tight saturation hull which retains a
positive finite terminal-law atom.  The checked theorems
`quittingLawTightCapNashSaturationMinimumFace_rootNash_iff_allContinue` and
`quittingLawTightCapNashSaturationMinimumFace_allContinue_prefix_eq` imply
that

1. all Continue is the unique exact root Nash against the cap of `P`; and
2. prefixing `P` by all Continue fixes its semantic pair **and its complete
   terminal-outcome law**.

Consequently the constant sequence

\[
 P\xrightarrow{\mathrm{allC}}P
  \xrightarrow{\mathrm{allC}}P\xrightarrow{\mathrm{allC}}\cdots
\tag{8.1A}
\]

is an exact forward cap--Nash chain with zero charge, positive semantic debt,
and the retained positive atom at every displayed node.  Terminal
exploitability is compatible with this chain: it is exactly what the positive
debt records.

This does not contradict Theorem 8.2.  In (8.1A), the atom belongs to the
external continuation port stored in `P`; all-Continue prefixing simply leaves
that port untouched.  By contrast, Theorem 8.2 concerns successive **shifted
tails of one displayed root chronology**.  If all its displayed roots are
eventually all Continue, its actual post-shift law is all Never and has no
positive nonempty atom.  Thus an atom rules out the phantom only with the
same-witness assertion that the atom lies in, and is renewed through, each
actual post-shift tail.  Bare source attachment at the initial node or
same-law retention under added prefixes is insufficient.

### Theorem 8.2 (a renewable retained atom eliminates the phantom in finite time)

Let `lambda_n` be the terminal law of the actual tail source `sigma_n`.  For
every nonempty coalition `A`,

\[
 \lambda_n(A)
 \le \lambda_n(2^I\setminus\{\varnothing\})
 \le \Psi_n.                                               \tag{8.2}
\]

Consequently, for every `m>0`, only finitely many tail sources can retain a
nonempty atom of mass at least `m`.  In particular, there is no infinite
source-faithful successor chain satisfying

\[
 \lambda_n(A_n)\ge m>0
\]

at every node, even if the atom label `A_n` is allowed to vary.

#### Proof

Absorption in the tail implies that at least one player Quits at a finite
time.  By the union bound and the hazard estimate,

\[
 \Pr(\text{tail absorbs})
 \le\sum_i\Pr(T_i<\infty)
 \le\sum_i\sum_{k\ge n}q_{k,i}=\Psi_n.
\]

Every nonempty atom is bounded by total absorption mass.  Since
`Psi_n->0`, the claim follows.  QED.

This is the exact finite barrier supplied by a retained atom.  If a source
passport renewed one fixed positive mass floor through every literal
successor, it would contradict the checked hard-spine summability and hence
eliminate the no-uniform-payoff branch.  The present law-tight saturation
passport is weaker: it retains an atom inside one same-law hull/prefix
construction.  It does not assert a uniform atom floor for every shifted
tail source.  The atom can remain at an early calendar date and disappear
when the chronology shifts past it.

At the first loss of the atom floor, terminal gap supplies exploitability,
not a terminal outcome.  A complete proof still needs a consumer for that
loss: terminal approximants, a charged regenerated source, or a genuine
finite source rank.

## 9. Minimal faithful state

The preceding results identify two independent fields which no finite
semantic label can replace.

1. **Continuation port.**  Retain the algebraic value `v_n` and the named
   actual tail source `sigma_n` (or an equivalent complete remaining root
   program).  The actual terminal law determines `U_n` and `B_n`, but it does
   not determine the algebraic boundary value against which `x_n` is Nash.
   Forward source composition also needs the tail port or a positive-reach
   suffix certificate.
2. **Residual height.**  Retain `Psi_n`, or another exact source-attached
   height satisfying `Psi_n=h_n+Psi_{n+1}` and the zero-tail condition.  The
   global `Phi` orders edges but is not automatically a closed trace
   coordinate.  A Boolean “positive” tag or a finite height bin loses
   arbitrarily small Zeno tolls.

A minimal paper-level node is therefore

\[
 \mathcal N_n=(v_n,x_n;\sigma_n,\lambda_n,U_n,B_n;\Psi_n),
\tag{9.1}
\]

with a proof-relevant edge containing both the exact Nash--Bellman equation
and the literal prefix/suffix ancestry certificate.  Some displayed semantic
coordinates are mathematically determined by `sigma_n`, but retaining them
is useful for closed unrestricted-deviation transport.  The essential new
information beyond the actual law is `(v_n,Psi_n)`.

Finite support/face/coalition labels may form a finite base `Q`, but (9.1) is
an infinite-height cover of that base.  Repetition in `Q` is harmless because
the lifted residual height has changed; identifying the heights is exactly
the false splice.

## 10. Strongest surviving theorem and next obligation

The checked canonical exact spine does admit a compact, closed,
source-faithful **infinite** lift after one late threshold.  It does not admit
a useful finite quotient.  The two honest exits are now precise.

1. **Renewable atom exit.**  Produce an actual-source exact spine or
   regeneration chain in which a nonempty terminal atom has one uniform mass
   floor at every successor.  Theorem 8.2 then gives a finite contradiction.
   What is missing is cross-tail ancestry/renewal, not another same-law atom
   lemma.
2. **Residual-barrier exit.**  Use the compact `Psi` lift and attach a consumer
   to the first small-residual barrier.  `Psi` itself only reaches the
   nonterminal phantom.  A reset to a macroscopic residual must carry an
   external finite rank or a paid ancestry account; otherwise it merely
   restarts capacity and recreates the original gap.

Equivalently, the remaining source theorem must say that before the retained
atom disappears into the `Psi=0` phantom boundary, one obtains a terminal
certificate or a source-faithful charged regeneration whose reset is paid by
a genuinely well-founded source field.  Neither bounded capacity, the global
supremum potential, terminal gap, nor finite semantic labels supplies that
field.

## 11. Honest status

| Result | Status |
|---|---|
| Finite quotient dichotomy, Theorems 5.1--5.2 | Proved here, ordinary mathematics |
| Global `Phi` discontinuity regression | Proved here, abstract compact charged graph |
| Compact exact-`Psi` lift under a uniform tail modulus | Proved here, ordinary mathematics |
| Application to one fixed hard-spine shift hull | Proved from checked marginal summability plus ordinary TV estimates |
| Terminal gap does not eliminate phantom | Checked phantom theorem plus direct semantic calculation |
| Positive atom plus positive debt eliminates forward saturation all-Continue fixed point | **False**; Proposition 8.1A gives the checked fixed-point no-go |
| Renewable retained-atom finite barrier | Proved here, ordinary probability |
| Current saturation passport renews the atom through all tails | **Not proved and not claimed** |
| Literal exact saturation prefix is a forward packet | Proved here from named checked adapters |
| Strict saturation yields arbitrary packet charge | **False**; checked debt telescope gives a uniform bound |
| Horizon-free approximate debt capacity at fixed local error | **False from the ledger alone**; (12.9)--(12.10) |
| Boundary-calibrated capacity dominates owner debt and finite contact forces zero source | Proved here, ordinary mathematics on the checked positive tail |
| Scalarized/joint compact minimization forces finite contact | **False for the checked scalar interface**; compact one-ray regression (13.5) |
| Global-minimum law-tight hull equals the fixed-law global-minimum fibre | Proved here from the checked hull definition and exact debt scaling |
| Saturation prefixes can spend bounded exact-block capacity in the Fin4 source | **False**; every hull exact root is all Continue and every prefix charge is zero |
| Terminal/small-`Psi` consumer or paid regeneration rank | **Open** |

## 12. The finite-forward-packet bypass

The checked `QuittingFiniteForwardPacket` compiler is an important bypass:
it needs no finite quotient and no return selected in advance.  For every
positive support error and every nonnegative target, it asks for one finite
forward path in a fixed compact payoff carrier satisfying

\[
 B_{t+1}=F_{r_t}(B_t),                                  \tag{12.1}
\]

support-local approximate Nash against `B_t`, a punishment floor, and joint
absorption charge `sum alpha_t` at least the target.  Compact charged closing
then finds a near return inside that supplied packet and compiles a uniform
payoff.  The packet's `alpha_t` is joint absorption mass; it is not the total
marginal hazard `h_t` used in Sections 1--10.

### 12.1 Exact saturation prefixes really do have the packet orientation

Let

\[
 P_t=((U_t,B_t),\lambda_t),\qquad 0\le t\le N,
\]

be a literal law-tight saturation prefix chain, and suppose `r_t` is exact
root Nash against `B_t` and

\[
 P_{t+1}=
 \bigl(\operatorname{SemPrefix}_{r_t}(U_t,B_t),
       \operatorname{LawPrefix}_{r_t}(\lambda_t)\bigr).
\tag{12.2}
\]

Then the cap coordinate is in precisely the forward-packet orientation:

\[
 B_{t+1}=F_{r_t}(B_t).                                  \tag{12.3}
\]

This is
`quittingTerminalSemanticPrefix_envelope_eq_rootSuccessorPayoff_of_capNash`.
Moreover, joint-carrier membership projects to terminal-semantic carrier
membership; hence every `B_t` lies in the canonical reward cube and
`B_0` lies above the behavioral punishment floor by
`quittingPunishmentValue_le_terminalSemanticEnvelope`.  Exact root Nash
implies support-approximate Nash at every positive declared tolerance.
Therefore `(B_t,r_t)_{t<N}` packages, by ordinary field assembly, as a
`QuittingPunishmentFloorFinitePrefix` and then as a
`QuittingFiniteForwardPacket`.

This adapter is genuine, but it cannot supply arbitrary charge.  If `D_* > 0`
is the hull-minimum total semantic debt, the checked telescope gives

\[
 \sum_{t<N}\alpha_t
 \le \frac{D(P_0)-D(P_N)}{D_*}
 \le \frac{D(P_0)-D_*}{D_*}.                            \tag{12.4}
\]

Compactness of the hull gives a finite `D_max`, so even allowing the initial
hull point to depend on the target yields the uniform bound

\[
 \sum_{t<N}\alpha_t\le\frac{D_{\max}-D_*}{D_*}.         \tag{12.5}
\]

This is also consistent with the stronger checked no-uniform-payoff
alternative `quittingGame_uniformPayoff_or_bounded_floorPrefixCharge`: in the
no-uniform-payoff branch **all** exact punishment-floor forward prefixes,
not merely saturation prefixes, have one common finite joint-charge bound.

### 12.2 Same-law replacement does not recharge a packet

The saturation hull is closed under a debt-nonincreasing replacement inside
one law fibre.  Such a replacement is not automatically a packet edge.  If it
changes the displayed cap from the exact prefix cap `F_{r_t}(B_t)` to some
other cap, equation (12.1) fails at that seam.  The forward packet permits
support error, but its Bellman policy equality is exact.

Suppose instead that an interleaved replacement is packet-compatible: it
preserves the prefix cap, lies in the same law fibre, and has no larger total
debt.  Write `P_t^+` for the literal prefix and `P_{t+1}` for the replacement.
Exact scaling and replacement monotonicity give

\[
 D(P_t^+)=(1-\alpha_t)D(P_t),\qquad
 D(P_{t+1})\le D(P_t^+).
\]

Therefore

\[
 D_*\alpha_t\le D(P_t)-D(P_{t+1}),                     \tag{12.6}
\]

and summing again gives (12.4).  Thus a replacement has an exhaustive
alternative:

* change the cap and lose the exact forward-packet seam; or
* preserve the cap and remain inside the same finite debt budget.

Closure of the saturation hull supplies no third case and no finite ancestry
for an arbitrary closure point.

### 12.3 Why there is no horizon-free approximate-capacity bound

The forward compiler deliberately weakens only the Nash condition.  Let a
root be support-approximately Nash at error `epsilon` against a cap `B`.
Coordinatewise, if `Q_i,C_i` are its Quit and Continue endpoints and
`F_i` their prescribed mixture, support complementarity gives

\[
 0\le \max(Q_i,C_i)-F_i\le\epsilon.                    \tag{12.7}
\]

For a semantic pair `P=(U,B)`, the literal semantic prefix consequently has
total debt

\[
 D(P^+)=(1-\alpha)D(P)+E,qquad
 0\le E\le |I|\epsilon.                                \tag{12.8}
\]

Here the first term is the exact linear difference
`F_r(B)-F_r(U)`, and `E` is the sum of the max-versus-mixture defects in
(12.7).  If, in addition, every next packet cap is realized by a same-law
semantic replacement with no debt increase, then

\[
 D_*\sum_{t<N}\alpha_t
 \le D(P_0)-D(P_N)+|I|\sum_{t<N}\epsilon_t.             \tag{12.9}
\]

Thus an approximate capacity barrier survives only with a uniformly bounded
**aggregate** error budget.  It does not survive a fixed per-stage error over
an arbitrarily long packet.  The scalar recurrence

\[
 D_t=D_*,\qquad
 \alpha_t=\epsilon/D_*,\qquad
 E_t=\epsilon
\tag{12.10}
\]

for `0 < epsilon <= D_*` satisfies (12.8) at equality and has charge
`N epsilon/D_*`.  This is an algebraic regression, not a quitting-game
counterexample, but it proves that the debt ledger alone cannot remove the
last term in (12.9).  The checked strict-basin theorem
`sum_quittingRootAbsorptionMass_le_card_div_mul_sum_error` has exactly the
same architecture: it bounds aggregate absorption by aggregate declared
error, hence grows like `N epsilon` for a constant local error.

There is an even earlier provenance obstruction.  Under approximate support
Nash, the semantic successor cap is `max(Q_i,C_i)`, while the packet insists
that its next value is the mixture `F_i`.  Unless the defect in (12.7) is zero,
the packet value is generally **not** the unrestricted cap of the literal
prefixed source.  The terminal semantic carrier is not closed under arbitrary
coordinatewise cap lowering.  Therefore positive `D_*` cannot be applied to
an arbitrary `QuittingFiniteForwardPacket` at all: the packet structure stores
values, roots, and inequalities, but no actual semantic pair, law, or cap
provenance.

### 12.4 Sharp verdict and new obligation

Strict saturation does not currently produce the arbitrarily charged packet
family:

1. pure exact prefix chains are valid packets but satisfy the uniform debt
   capacity (12.5);
2. cap-changing same-law replacements break exact packet policy;
3. cap-preserving replacements cannot recharge debt; and
4. merely declaring positive support error does not turn the saturation hull
   into an approximate path producer or realize the lowered mixture caps.

The forward-packet bypass remains a real route, but its missing producer is
now exact: for every `epsilon>0` and charge target, construct a finite exact
Bellman cap path `B_{t+1}=F_{r_t}(B_t)` in one fixed compact punishment-floor
carrier, with support error `epsilon` and arbitrary accumulated **joint**
absorption.  If semantic provenance is retained, its cap-lowering seams must
be literal carrier realizations; (12.9) shows that the construction must spend
an aggregate error budget growing with the target.  If provenance is not
retained, neither positive terminal debt nor law-tight atom saturation
constrains the packet.  Supplying this family immediately invokes the checked
finite-forward-packet compiler and eliminates the need for a finite quotient
or a `Psi` return theorem.

## 13. Bounded capacity versus positive exact debt at one source

### 13.1 Checked declarations and the genuine mismatch

I inspected the following additional declarations for the bounded-capacity
boundary question.

* `finitePrefix_charge_le_admissiblePotential_source`,
  `exists_finitePrefix_source_remainingCapacity_lt`, and
  `exists_finitePrefix_source_forbids_incoming_charge` in
  `Diagnostics/Quitting/Capacity/NearMaximizerRebase.lean` select literal
  finite-prefix sources with arbitrarily small admissible remaining capacity.
  They do not select those sources from the positive dynamic-debt tail.
* `killedDebtReference_step` in
  `Diagnostics/Quitting/Debt/KilledTailPotential.lean` gives the exact scalar
  recursion on that tail.
* `absorption_add_killedRemainingCapacity_succ_le`,
  `killedDebtSource_add_capacityDebtAccount_succ_le`, and
  `killedCapacityDebtAccount_isKilledExcessive` in
  `Diagnostics/Quitting/Debt/KilledCapacityPotential.lean` give a canonical
  excessive account, but explicitly do not compare its value to exact debt.
* `zeroFace_or_succ_zeroFace_of_boundaryMismatch_le` and
  `zeroFace_recurrence_of_eventual_boundaryMismatch_le` in
  `Diagnostics/Quitting/Debt/Source/DynamicAlternative.lean` consume a
  boundary-mismatch nonexpansion premise; they do not derive it.
* `summable_killedCapacityDissipation` and
  `killedCapacityDissipation_tendsto_zero` in
  `Diagnostics/Quitting/Debt/BoundaryMismatchAlternative.lean` give only
  asymptotic vanishing, not a finite zero-source date.

Thus the near-maximizer source and positive-debt source are selected by
different compactness arguments.  Joint minimization is not already present
in these declarations.

### 13.2 A source-attached calibrated account

The existing positive tail nevertheless supports a sharper exact account.
Fix the limit owner.  Write

\[
 d_t=(\text{seam.tail }t).2(\text{owner}),\qquad
 s_t=\text{killedDebtSource}(\text{owner},t),
\]

\[
 c_t=\text{killedDebtSurvival}(t),\qquad
 a_t=1-c_t,
\]

and let `r_t` be `killedRemainingCapacity t`.  Put

\[
 d_\infty=\text{seam.limit.debt(owner)},\qquad
 r_\infty=\lim_t r_t,
\]

and let

\[
 \kappa=\text{quittingPositiveSingletonDebtCap(reward,owner)}.
\]

The limit `r_infinity` exists because `r_t` is nonnegative and antitone:
the checked capacity inequality says `a_t+r_{t+1}<=r_t`.  The positive-tail
fields give `d_t -> d_infinity` and
`d_infinity >= terminalGap > 0`.  Define the boundary-calibrated account

\[
 \overline A_t=d_\infty+\kappa(r_t-r_\infty).           \tag{13.1}
\]

**Theorem 13.1 (ordinary mathematics, source-attached).**  On the actual
positive-debt tail, for the limit owner:

1. `overline A_t >= 0` and `overline A_t -> d_infinity`;
2. `s_t+overline A_{t+1} <= overline A_t`, hence
   `s_t+c_t overline A_{t+1} <= overline A_t`;
3. `d_t <= overline A_t` for every finite `t`;
4. `overline A_t-d_t -> 0`; and
5. if equality `d_t=overline A_t` occurs at a finite date, then `c_t=1` and
   `s_t=0`, so the current obstruction flow lies in the checked playerwise
   zero-source exposed face.

**Proof.**  The checked seam cap and capacity inequalities give

\[
 0\le s_t\le\kappa a_t,
 \qquad a_t+r_{t+1}\le r_t.
\]

Therefore

\[
 \overline A_t-\overline A_{t+1}
   =\kappa(r_t-r_{t+1})\ge\kappa a_t\ge s_t,           \tag{13.2}
\]

which proves the stronger additive inequality.  Let

\[
 g_t=\overline A_t-d_t,
 \qquad
 \Delta_t=\overline A_t-s_t-c_t\overline A_{t+1}\ge0.
\]

Using the checked exact recursion `d_t=s_t+c_t d_{t+1}` gives

\[
 g_t=\Delta_t+c_tg_{t+1}.                              \tag{13.3}
\]

Iterating (13.3) from fixed `t` to `N` gives a nonnegative partial sum plus
`(product of c_j) g_N`.  Because `0<=c_j<=1` and `g_N->0`, letting `N->infinity`
proves `g_t>=0`.  The same two component limits prove `g_t->0`.

If `g_t=0`, (13.3) and nonnegativity of both terms give `Delta_t=0`.  But

\[
 \Delta_t=
 (\overline A_t-s_t-\overline A_{t+1})
 +(1-c_t)\overline A_{t+1},                            \tag{13.4}
\]

and both summands are nonnegative.  Since
`overline A_{t+1}>=d_infinity>0`, (13.4) forces `c_t=1`.  Hence `a_t=0`, and
`0<=s_t<=kappa a_t` forces `s_t=0`.  The checked theorem
`tailDebtSourceObstructionFlow_mem_zeroFace_iff` now gives zero-face
membership.  This proves the theorem.

This is the strongest same-source comparison I can obtain: the calibration
adds the exact positive harmonic boundary that the original capacity account
omits.  It tightly bounds debt asymptotically, and exact contact has the
desired finite zero-face consequence.  It does **not** produce finite contact.

### 13.3 Minimal compact regression against finite contact or scalarization

The failure of finite contact is not a defect of the proof.  Consider the
compact one-ray system with states `x_t` for `t` natural and its limit
`x_infinity`, with edges `x_t -> x_{t+1}` and the boundary self-loop.  Set

\[
 a_t=2^{-(t+2)},\quad c_t=1-a_t,\quad
 r_t=2^{-(t+1)},\quad d_t=1,\quad s_t=a_t,
 \quad\kappa=1,                                       \tag{13.5}
\]

and at the limit set `a=s=r=0`, `c=d=1`.  Then, exactly,

\[
 d_t=s_t+c_td_{t+1},\qquad a_t+r_{t+1}=r_t.            \tag{13.6}
\]

With prefix potential `Phi_t=1-r_t`, one also has
`Phi_t+a_t=Phi_{t+1}`; all data extend continuously to the compact boundary.
The global debt minimum is the positive value one.

The original account `kappa r_t` neither dominates nor meets debt and tends
to zero.  No fixed finite scalar multiple `lambda r_t` dominates debt on all
late states.  The calibrated account is

\[
 \overline A_t=1+r_t,
\]

so its gap is `g_t=r_t>0` at every finite date and tends to zero.  Its killed
dissipation is the strictly positive quantity

\[
 \Delta_t=a_t(1+r_{t+1}).                              \tag{13.7}
\]

Every finite source is therefore outside the zero-source face; equality and
zero source occur only at the all-Continue boundary self-loop.

This also defeats the proposed scalarized selection.  For every
`lambda>0`, the objective `d+lambda r` has its unique minimum at
`x_infinity`; on finite truncations its minimizer is the moving last state.
Lexicographic minimization of debt followed by remaining capacity behaves the
same way.  Compactness attains only the already-known zero-source boundary
phantom, not a literal finite-prefix source.  This is an abstract compact
killed-capacity regression, not a claimed quitting-game counterexample; it
shows that the checked debt recursion, capacity inequalities, continuity,
positive minimum, and scalar/joint minimization alone cannot yield finite
contact.

### 13.4 Exact surviving source consequence and residual

The positive-minimum source can be augmented canonically by (13.1), giving a
same-state upper bound on exact debt whose gap vanishes and whose finite
contact immediately forces the checked zero-source face.  This is a genuine
source consequence and a plausible small Lean wrapper around the named
declarations plus monotone convergence.

What does **not** follow is a date of contact, a nonexpanding window for the
uncalibrated mismatch, or attachment of a near-maximal literal-prefix source
to this same positive-debt chronology.  Any further finite zero-face theorem
must add a non-asymptotic ingredient that excludes the regression (13.5), for
example discreteness of positive source values, an attained finite source
maximum, or an actual return identifying one finite state with its calibrated
boundary.  Joint/scalarized compact minimization by itself supplies none of
these.

## 14. The global-minimum law-tight hull is already a neutral fibre

### 14.1 Stable checked boundary versus in-flight work

The source boundary changed after Sections 12--13.  The following are now
committed checked declarations:

* commit `a6d9376`,
  `LawTightCapNashSaturationHull.lean`: the smallest closed exact-prefix and
  downward same-law invariant;
* commit `351bd82`, `LawTightCapNashMinimumFace.lean`: compact minimum level
  set, unique all-Continue exact cap root on a positive minimum, and exact
  finite-chain absorption budgets;
* commit `331ae50`, `TerminalSemanticSingletonNeverCapTightness.lean` and
  `SingletonCapBindingCollision.lean`: singleton/Never cap tightness and the
  binding-collision edge; and
* commit `fe12b32`, `LawTightCapNashStrictMinimum.lean` and
  `FinFourLawTightCapNashStrictMinimum.lean`: the stable production theorem
  `finFour_noUniformPayoff_exists_lawTightStrictMinimumChamber` and its three
  chambers.

The occupation analysis in
`CODEX_SOURCE_GATE__FIN4_NEUTRAL_CHAMBER_CALIBRATED_OCCUPATION_COLLAPSE.md`
and the cap-pencil construction reviewed in
`feedback/WITNESS_1__BY_CODEX_STRENGTHEN.md` are conference mathematics, not
checked declarations.  I use neither as a premise below.

### 14.2 Exact hull-collapse theorem

The checked Fin4 producer begins at more than an arbitrary positive hull
origin: its origin is already a **global** terminal-semantic debt minimizer.
That makes the law-tight hull much smaller than the generic definition
suggests.

Let `z_0=(X_0,mu_0)` belong to the joint terminal-semantic/law carrier.  Put

\[
 D_0=D(X_0)>0
\]

and assume

\[
 D_0\le D(X)
 \quad\hbox{for every terminal-semantic carrier point }X.       \tag{14.1}
\]

Define the fixed-law global-minimum fibre

\[
 \mathcal F(z_0)=
 \{(X,\mu): (X,\mu)\text{ is in the joint carrier},\
              \mu=\mu_0,\ D(X)=D_0\}.                         \tag{14.2}
\]

**Theorem 14.1 (ordinary mathematics from the checked definitions).**
Under (14.1),

\[
 \boxed{
 \operatorname{Hull}_{\mathrm{law\mbox{-}tight}}(z_0)
   =\mathcal F(z_0).}                                           \tag{14.3}
\]

Consequently:

1. every hull point has the same complete time-forgetting terminal law as
   the origin and the same total debt `D_0`;
2. every exact cap--Nash root at every hull point is all Continue;
3. exact cap prefixing fixes every hull point literally, in both its semantic
   and law coordinates;
4. every finite literal exact-prefix chain inside the hull is constant and
   has zero joint absorption and zero marginal-hazard charge; and
5. the minimum face of any hull minimizer is the whole hull.

**Proof.**  First show that `F(z_0)` is one of the closed invariants appearing
in the defining intersection of the hull.  Closedness follows from
closedness of the joint carrier and continuity of debt and both projections.
It contains `z_0`.

Let `(X,mu_0)` lie in the fibre and let `r` be exact cap--Nash against the cap
of `X`.  Checked exact debt scaling gives

\[
 D(P_rX)=c(r)D_0,                                               \tag{14.4}
\]

where `0<=c(r)<=1` is joint Continue mass.  The prefixed joint point is in
the carrier, so global minimality gives `D_0<=D(P_rX)`.  Since `D_0>0`,
(14.4) forces `c(r)=1`, hence `r` is all Continue.  The checked all-Continue
semantic prefix identity, together with the elementary law-prefix identity,
then fixes `(X,mu_0)`.  Thus the fibre is exact-prefix invariant.

For downward same-law replacement, suppose `(Y,mu_0)` is in the joint
carrier and `D(Y)<=D(X)=D_0`.  Global minimality supplies the reverse
inequality, hence `D(Y)=D_0`; the replacement stays in the fibre.  Therefore
minimality of the defining intersection gives

\[
 \operatorname{Hull}(z_0)\subseteq\mathcal F(z_0).              \tag{14.5}
\]

Conversely, take `(Y,mu_0)` in the fibre.  The origin is in the hull, the law
is literally the same, and `D(Y)=D_0=D(X_0)`.  The checked downward same-law
closure applied once at the origin puts `(Y,mu_0)` in the hull.  This proves
the reverse inclusion and (14.3).  Items 1--5 follow from the same scaling
argument and the checked all-Continue prefix identity.

This theorem also sharpens the retained-atom conclusion: the finite atom is
not merely bounded below by the debt-weighted cone.  Its complete law
coordinate is exactly the original law at every hull point.

### 14.3 Fin4 source consequence

The proof of the committed declaration
`finFour_noUniformPayoff_exists_lawTightStrictMinimumChamber` obtains its
origin from
`exists_finFourHardResidual_minimumLaw_causalSuffixAtom`.  The latter stores
joint-carrier membership, global minimality, positive debt infimum, equality
of origin debt with that infimum, and the same-point causal atom.  Hence
Theorem 14.1 applies to the actual no-uniform-payoff source chosen in the
committed proof.

The current public conclusion of
`finFour_noUniformPayoff_exists_lawTightStrictMinimumChamber` does not expose
the origin's global-minimum proof in every arm, even though its proof has it.
A strengthened wrapper should retain that field and conclude:

> a hypothetical Fin4 counterexample supplies a compact fixed-law
> global-minimum fibre carrying one fixed positive finite atom; every point of
> that fibre is cap-neutral, and any selected point has full debt support, a
> reset-rigid same-law certificate, or a singleton/Never binding cycle.

This is a genuine source strengthening.  It also changes the capacity
interpretation: the saturation hull does not contain an off-minimum charged
prefix region in this adapter.  Its exact-prefix hazard capacity is exactly
zero.

### 14.4 Why bounded exact-block capacity supplies no further hull event

The checked no-uniform-payoff theorem
`finFour_hasBoundedFiniteExactNashBellmanHazardCapacity_of_no_uniformPayoff`
controls all finite exact Nash--Bellman blocks in the canonical payoff box.
On the hull-generated cap-prefix subrelation, Theorem 14.1 is much stronger:
every available prefix has zero charge.  Thus one cannot obtain a chamber
consumer or a decreasing rank by spending the global block-capacity account
on saturation edges; there is nothing to spend.

The three committed chamber fields do not alter this conclusion.

* Full debt support is a static coordinate property of a neutral fibre
  point.
* The reset-rigid return is a downward same-law replacement.  By (14.3) it is
  horizontal motion inside the same global-minimum fibre, not a chronological
  edge.
* The singleton/Never binding cycle is a finite graph of payoff inequalities
  at one cap.  Its edges are not exact Bellman-successor edges.

Finite chamber labels can therefore repeat without consuming any exact-block
hazard.  Pigeonhole, support rank, and collision-cycle period do not create a
well-founded chronological rank.

There is one exact finite obstruction:

> Any positive-charge exact block claimed to be generated solely by the
> law-tight hull operations is impossible.  Such a block must use at least
> one new operation: a cap root against an off-fibre tail, a law-changing
> seam, or an ancestry-preserving source regeneration not present in the
> hull definition.

There is a stronger cap-level formulation which does not require the
intermediate states to carry laws.

**Theorem 14.2 (exact terminal-cap obstruction).**  Let `z` be any point of
the hull in Theorem 14.1 and let `B` be its displayed cap.  Every finite exact
Nash--Bellman block whose terminal continuation value is exactly `B` is the
constant all-Continue block at `B`; in particular its total marginal hazard
is zero.

This finite backward-induction consumer is **already checked**, rather than a
new theorem: instantiate
`quittingAnchoredPath_backward_rigidity_of_unique_allContinue` from
`Quitting/Bellman/Finite/AllContinueBasinRigidity.lean` with the singleton
basin `{B}`.  Theorem 14.1 supplies uniqueness of the exact cap root at `B`;
the checked zero-error equivalence
`isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash` supplies the
endpoint-Nash form expected by the anchored-path theorem.  Its companion
`quittingAnchoredPath_root_eq_allContinue_and_absorption_eq_zero` gives zero
absorption root by root.  Thus the last nonterminal root is all Continue,
Bellman equality makes the preceding displayed value again `B`, and the
checked induction repeats through the whole block.  The terminal block
annotation's unused root label is irrelevant.

Thus even an off-fibre excursion cannot return **exactly** to the chamber cap
through a positive exact Nash--Bellman block.  A proposed renewal must spend
an approximate seam, change the chronological semantics, or return only near
the fibre.  The checked bounded exact-block capacity does not price such a
nonexact attachment automatically.

If such new blocks could be concatenated and each paid a fixed hazard
`kappa>0`, the checked bounded-capacity theorem would of course bound their
number.  The present source supplies neither the first such block nor a
literal concatenation port, so this conditional counting statement is not a
consumer.

### 14.5 Sharp regression and residual

The explicit rational construction audited in
`feedback/WITNESS_1__BY_CODEX_STRENGTHEN.md` supplies the relevant Zeno
boundary: exact fully mixed cap roots can generate an outward prefix tower
whose scale and total hazard are summable and whose caps converge to a
unique-all-Continue limit.  Its chronological edges point from deeper
prefixed caps back toward earlier caps, and it supplies no semantic carrier
seed.  It therefore does not contradict Theorem 14.1; it shows why a cap-only
Zeno mechanism cannot manufacture the missing off-fibre chronological port.

The bounded-capacity residual is now exact.  Starting from the checked
fixed-law global-minimum fibre, produce one of:

1. a direct terminal consumer for one of the three neutral chambers; or
2. a literal source-faithful chronological edge leaving the fibre and a
   controlled nonexact or near-return seam whose composition preserves
   ancestry and whose error is paid.

Only after (2) exists does bounded exact-block capacity provide a finite
repeatability obstruction.  Neither scalar minimization, law-tight
saturation, the minimum-face absorption budget, nor the chamber trichotomy
itself supplies either edge.

### 14.6 Declaration-level handoff and novelty

A narrow repository search found the generic hull definition, one-step
same-law closure, atom cone, selected minimum face, and absorption budgets,
but no theorem identifying the hull of a global-minimum origin with its
fixed-law minimum fibre.  Suggested declarations are:

```text
quittingLawTightCapNashSaturationHull_eq_sameLaw_globalMinimumFiber
quittingLawTightCapNashSaturationHull_root_eq_allContinue_of_origin_globalMinimum
quittingLawTightCapNashSaturationHull_prefixChain_eq_constant_of_origin_globalMinimum
finFour_noUniformPayoff_exists_fixedLawGlobalMinimumNeutralFiber_chamber
```

Do **not** add a duplicate generic finite-block rigidity theorem: the required
consumer is already
`quittingAnchoredPath_backward_rigidity_of_unique_allContinue` (with its
root/absorption corollary) in
`Quitting/Bellman/Finite/AllContinueBasinRigidity.lean`.  At most, add a short
adapter from the global-minimum-fibre package to that checked theorem if a
single declaration is useful downstream.

The generic theorem should assume joint-carrier membership, global
minimality of `origin.1`, and strict positivity of its debt sum.  The Fin4
wrapper should expose the `hsourceMinimum` and positive-infimum fields already
present inside the proof of
`finFour_noUniformPayoff_exists_lawTightStrictMinimumChamber`, then package
Theorem 14.1 together with the committed chamber disjunction.  No new
strategy-class or uniform-payoff claim is involved.

## 15. Near-minimum charged attachment forces a macroscopic cap seam

### 15.1 Checked account and the source-faithful orientation

The missing operation at the end of Section 14 was a literal off-fibre
chronological port: attach a finite exact Nash--Bellman block to an actual
near-minimum tail, preserving the block's positive hazard and returning near
the law-tight chamber.  There is a sharp obstruction already latent in two
checked files.

* `quittingTerminalSemanticDebtSum_prefix_eq_continueMass_mul_add_capDefect`
  in
  `UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/CapDebtBellmanReduction.lean`
  states, for **every** product root `r` and actual terminal-semantic tail
  `X`,

  \[
    D(P_rX)=c(r)D(X)+E_B(r;X),                                  \tag{15.1}
  \]

  where `E_B` is the total one-row Nash defect evaluated against the
  unrestricted behavioral cap `B(X)`.  No Nash hypothesis is used.
* `semanticMinimum_mul_capStackAbsorptionSum_le_semanticBudget_add_defectSum`
  and its rowwise-error specialization in
  `Research/Quitting/PaidNonexactCapStackAccount.lean` iterate (15.1) on a
  literal executable root word.  Every suffix cap is recomputed from the
  actual suffix; this is ancestry-safe and not an algebraic horizontal
  cycle.

Write `D_*>0` for the global carrier minimum, `w=(r_0,...,r_{L-1})`
for a root word attached literally above an actual terminal profile `tau`,

\[
 A(w)=\sum_{t<L}\bigl(1-c(r_t)\bigr),\qquad
 E(w;\tau)=\sum_{t<L}E_B(r_t;X_{t+1}),
\]

where `X_{t+1}` is the actual semantic pair of the literal suffix below row
`t`.  The checked account is exactly

\[
 \boxed{D_*A(w)\le D(\tau)-D_*+E(w;\tau).}                      \tag{15.2}
\]

This is stronger than an appeal to bounded exact-block capacity: it applies
to arbitrary nonexact root words and prices the nonexact seam explicitly.

### 15.2 Law-tight near-return no-go

**Theorem 15.1 (ordinary adapter to the checked account).**  Let
`z=(X,mu)` be any point of the global-minimum fibre in Theorem 14.1, so
`D(X)=D_*>0`.  Let `tau_n` be actual terminal profiles whose joint
semantic/law points converge to `z`, and let `w_n` be arbitrary finite root
words attached literally above `tau_n`.  Then

\[
 D_*A(w_n)\le D(\tau_n)-D_*+E(w_n;\tau_n).                     \tag{15.3}
\]

Consequently:

1. if `E(w_n;tau_n) -> 0`, then `A(w_n) -> 0`;
2. if `liminf A(w_n)>=kappa>0`, then
   `liminf E(w_n;tau_n)>=D_* kappa`;
3. if every row is exact cap--Nash except one seam row which is
   `epsilon_n`-Nash, then fixed absorption `kappa` forces
   `liminf epsilon_n >= D_* kappa / |I|`; and
4. if all rows are exact cap--Nash, no fixed positive absorption can be
   attached to a tail converging to `z` at all.

**Proof.**  Equation (15.3) is the checked theorem just cited.  Joint
convergence gives `D(tau_n)->D_*` by continuity.  Items 1--2 follow by taking
limits.  For item 3, the checked bound
`quittingRootTotalNashDefect_le_card_mul_of_isεQuittingRootNash` gives
`E(w_n;tau_n)<=|I| epsilon_n`; exact rows contribute zero.  Item 4 is the
zero-defect specialization.  Notice that no compactness selection, law
closure, or bounded-capacity hypothesis is hidden in the proof.  The law
coordinate is used only to state the source-faithful return to the actual
fixed-law chamber; semantic convergence alone is sufficient for (15.3).

The same-law form is quantitative.  If an actual terminal point has exactly
the chamber law `mu`, then the checked
`terminalSemanticLawCarrier_prescribed_eq_of_sameLaw` makes its prescribed
payoff exactly `X.1`.  Hence

\[
 0\le D(\tau)-D_*
   =\sum_i\bigl(B_i(\tau)-B_i(X)\bigr)
   \le\sum_i|B_i(\tau)-B_i(X)|.                               \tag{15.4}
\]

Thus (15.2) has a literal cap-seam bound on a fixed law fibre.  With merely
convergent laws, the checked reward-moment identity
`terminalSemanticLawCarrier_rewardMoment` supplies the corresponding
vanishing prescribed-payoff term (or the usual reward-bound times total
variation estimate).

### 15.3 Exact algebraic block versus actual suffix caps

Let `(v_t,r_t)_{t<L}` with terminal value `v_L` be a finite exact
Nash--Bellman block in the checked orientation:

\[
 v_t=F_{r_t}(v_{t+1}),\qquad r_t\text{ exact Nash against }v_{t+1}.
\]

Attach the same root word literally above an actual terminal profile `tau`.
Let `C_{t+1}` be the unrestricted behavioral cap of the actual literal suffix
below row `t`, and put

\[
 \delta_t=\max_i|C_{t+1,i}-v_{t+1,i}|,
 \qquad H=\sum_{t<L}\sum_i q_{t,i}.                            \tag{15.5}
\]

The checked tail-stability theorem
`isεQuittingRootEndpointNash_of_tail_close`, followed by the zero-error
endpoint/root-Nash equivalence, gives

\[
 E(w;\tau)\le |I|\sum_{t<L}\delta_t.                          \tag{15.6}
\]

Also `H<=|I|A(w)`, since every marginal Quit probability is at most the
joint absorption probability of its row.  Combining (15.2), (15.5), and
(15.6) gives the source-faithful attachment inequality

\[
 \boxed{
   \frac{D_*}{|I|}H
     \le D(\tau)-D_*+|I|\sum_{t<L}\delta_t.}                  \tag{15.7}
\]

This identifies the exact missing field in any proposed endpoint adapter:
one must control the **sum of all actual-suffix cap mismatches**, not only the
terminal endpoint mismatch.

There is nevertheless a useful terminal-only corollary.  The cap component
of semantic prefixing is an autonomous coordinatewise nonexpansive map.
Equivalently, compare the exact block cap recursion to the actual suffix-cap
recursion row by row; the maximum of the two endpoint values is
one-Lipschitz in that player's tail coordinate.  Therefore, if

\[
 \max_i|B_i(\tau)-v_{L,i}|\le\delta,
\]

then every `delta_t<=delta`.  Equation (15.7) yields

\[
 \boxed{
   L\delta\ge {D_*H\over |I|^2}
                 -{D(\tau)-D_*\over |I|}.}                   \tag{15.8}
\]

The nonexpansiveness used here is the cap projection of the checked
`quittingTerminalSemanticPrefix_within` / autonomous-cap recursion; it can
also be proved directly from the endpoint maximum formula.

Consequences for a fixed charge `H>=kappa` and a law-tight near-minimum
terminal sequence are exact:

* an **exact** endpoint match (`delta=0`) is impossible;
* bounded-depth matches with `delta->0` are impossible; and
* every vanishing endpoint mismatch satisfies
  `liminf L_n delta_n >= D_* kappa/|I|^2`.

Thus a fixed-charge block can approach the chamber only ballistically: its
horizon must diverge at least on the reciprocal endpoint-mismatch scale.  A
uniformly summable triangular seam budget cannot attach it.

### 15.4 What this changes in the bounded-capacity branch

This closes the particular residual proposed at the end of Section 14 in
the negative.  The desired port cannot simultaneously be:

1. literal and source-faithful (actual suffix caps at every row);
2. law-tight/semantic-near-returning to the positive global-minimum fibre;
3. of fixed positive exact-block marginal-hazard charge; and
4. exact, or nonexact with vanishing cumulative cap-Nash seam.

Bounded exact-block hazard capacity supplies no escape from (15.7).  It
prices only exact algebraic blocks; after attachment, either their charge
collapses or a macroscopic cap-defect/mismatch account appears.  Repeating a
positive-charge near-return would accumulate that account rather than spend
the checked exact-block capacity.

The live question should therefore not ask for a better exact endpoint
matcher or a summably small seam.  It must instead do one of the following:

* consume the macroscopic reached cap-defect forced by (15.7) as an actual
  unrestricted-response event;
* use a return notion weaker than joint semantic/law near-return and explain
  how its uncontrolled debt excess is paid; or
* produce a genuinely different chronology whose charge is not the literal
  marginal hazard of the attached root word.

The first is the narrowest surviving target.  The checked finite-word ledger
already selects a positive cap-defect coordinate when its weighted aggregate
is positive, but, as `docs/FRONTIER.md` records, no source-facing screening or
downstream consumer turns that coordinate into a paid prescribed edge,
return, terminal approximation, or uniform-equilibrium conclusion.

### 15.5 Declaration-level handoff

Most of the mathematics is already checked.  The genuinely missing wrappers
are the adapters, not a new debt telescope:

```text
lawTightNearMinimum_capStackAbsorption_tendsto_zero_of_defectSum_tendsto_zero
lawTightNearMinimum_fixedHazard_forces_capDefectSum_liminf
exactNashBellmanBlock_literalAttachment_hazard_le_terminalExcess_add_capMismatchSum
exactNashBellmanBlock_terminalMismatch_mul_horizon_ge_of_fixedHazard
```

The last two wrappers should use the checked block orientation, construct the
literal root list in chronological order, invoke tail stability against every
actual suffix cap, and convert joint absorption to marginal hazard with the
finite-cardinality factor.  No theorem should call the single endpoint
distance the whole seam unless it also proves the autonomous cap
nonexpansiveness induction.

### 15.6 The whole forced seam localizes to one paid first disagreement

The final sentence of Section 15.4 can be sharpened.  Selecting merely one
positive coordinate of one positive ledger row loses a factor equal to the
word length.  That loss is unnecessary: the **whole coordinate ledger** is
the payoff gap of one finite-block hybrid strategy, and stopping-law
extremality turns that aggregate gap into one paid first disagreement.

For a literal word `w=(r_0,...,r_{L-1})` above an actual terminal profile,
write `X_t` for its actual suffix semantic pair and

\[
 s_t=\prod_{k<t}c(r_k),\qquad
 e_{t,i}=\operatorname{Defect}_i(r_t;B(X_{t+1})).              \tag{15.9}
\]

Define the coordinate and total weighted ledgers

\[
 \Lambda_i=\sum_{t<L}s_t e_{t,i},
 \qquad
 \Lambda=\sum_i\Lambda_i.                                   \tag{15.10}
\]

All terms are nonnegative.  Finite sum interchange and the definition in
`FiniteWordWeightedCapDefectLedger.lean` give

\[
 \Lambda=
 \operatorname{quittingFiniteWordWeightedCapDefectLedger}(w,\tau).
                                                                    \tag{15.11}
\]

**Theorem 15.2 (finite-block paid-row extraction; ordinary mathematics).**
Assume the player type is nonempty and `Lambda>0`.  On the literal behavioral
profile generated by `w` and `tau`, there are a player `i` and a
`QuittingPaidFirstDisagreementRow` with

\[
 \operatorname{gain}\ge {\Lambda\over 2|I|},
 \qquad
 \operatorname{row.start}<L.                                 \tag{15.12}
\]

Consequently its checked division-free estimate gives

\[
 \operatorname{row.liveMass}
 \ge {\Lambda\over4|I|R},                                    \tag{15.13}
\]

where `R=quittingRewardBound reward`.  Thus the selected disagreement is
not only chronologically inside the charged block; it is reached with a
horizon-independent positive opponent-survival floor whenever `Lambda` has
one.

**Proof.**  Select `i` with
`Lambda_i >= Lambda/|I|`.  Fix a small
`eta<Lambda_i/4`.  Against the actual opponents below the terminal cut,
behavioral pure-time extremality supplies a relative pure time whose payoff
is within `eta` of the suffix cap `B(X_L)_i`.

Now form one legal hybrid strategy for player `i`: through dates `<L` it uses
exactly the displayed marginals of `w`, conditional on reaching date `L` it
uses that one selected tail pure time.  Opponents are never changed.  Hence
the cap coordinate of every suffix is still the actual cap `B(X_t)_i`.
Iterating the **coordinate** form of
`quittingTerminalSemanticDebt_prefix_eq_continueMass_mul_add_capDefect`
therefore gives

\[
 B(X_0)_i-U_i(\text{hybrid})
   =\Lambda_i+s_L\bigl(B(X_L)_i-U_i(\text{selected tail time})\bigr)
   \ge\Lambda_i.                                             \tag{15.14}
\]

Choose a pure time against the complete literal opponents within `eta` of
the full cap `B(X_0)_i`.  The stopping-law payoff identity says that the
hybrid payoff is the average of the same pure-time payoff function under the
hybrid stopping law.  The usual support-bracketing argument therefore
selects one pure time in the hybrid support such that receiving pure time
minus source pure time is at least

\[
 \Lambda_i-\eta>\Lambda_i/2.                                 \tag{15.15}
\]

The hybrid stopping law is supported only on displayed block dates `<L`
and on the single selected tail time.  If both selected witnesses were at or
after `L`, the source witness would be that selected tail time, while the
receiving witness would be another tail pure time.  After factoring common
opponent survival to the cut, their payoff difference is at most `eta`, by
the tail-time choice.  This contradicts (15.15).  Hence at least one witness
is before `L`, so their first disagreement satisfies `start<L`.

Apply
`exists_quittingPaidFirstDisagreementRow_of_pureTimePayoff_sub` with any
fixed gain at most `Lambda_i/2`; taking `Lambda/(2|I|)` proves (15.12).
Finally (15.13) is `gain_le_liveMass` rearranged.  If `R=0`, positive gain is
already impossible; under the displayed positive ledger the bound therefore
has a positive denominator.  QED.

This proof is source-faithful in the needed sense: both witnesses are tested
against the opponents of the literal root word, the first disagreement is
inside that word, and no horizontal saturation edge is reinterpreted as
chronology.  The source witness is supported by the explicitly constructed
hybrid stopping law, not necessarily by the original player's complete tail
strategy.  A theorem requiring original-strategy support must retain this
distinction.

### 15.7 Fixed marginal hazard gives a uniform paid block row

Let

\[
 P=\prod_{t<L}c(r_t),\qquad
 H=\sum_{t<L}\sum_i q_{t,i}.
\]

The checked exact total ledger identity and global minimality give

\[
 \Lambda=D(X_0)-P D(X_L)\ge D_*-P D(X_L).                    \tag{15.16}
\]

The elementary product estimate gives `P<=exp(-H)`.  Hence, for a sequence
of literal blocks whose terminal debts tend to `D_*` and whose marginal
hazards obey `H>=kappa>0`,

\[
 \liminf\Lambda
 \ge D_*(1-e^{-\kappa})>0.                                  \tag{15.17}
\]

For all sufficiently late blocks Theorem 15.2 therefore supplies a paid
first-disagreement row inside the block with, for example,

\[
 \operatorname{gain}\ge
 {D_*(1-e^{-\kappa})\over4|I|},
 \qquad
 \operatorname{liveMass}\ge
 {D_*(1-e^{-\kappa})\over8|I|R}.                             \tag{15.18}
\]

This is the strongest direct consumer of the forced macroscopic seam I can
justify.  It is substantially sharper than selecting one positive ledger
row: there is no factor `L`, and the first-disagreement chronology is kept.

### 15.8 Why this still does not close a chamber or a finite rank

The checked
`paidFirstDisagreement_capPortTrichotomy` accepts the row from Theorem 15.2,
but its output is only charged near-return, quantitative debt descent, or
inert stall.  Under a terminal exploitability gap the charged near-return
would already give a uniform-equilibrium payoff and is therefore impossible
on the no-UE branch.  Near the minimum fibre the checked cap-lift absorption
budget collapses to zero; at the exact minimum,
`QuittingActualProfileTerminalGapPaidCapPort.inertStall_of_minimumFiber`
shows that a paid row can coexist with the literal inert arm.  Thus positive
payoff gain is not itself positive exact-prefix hazard.

There is, however, a stronger **existing orientation consumer** than the
cap-port trichotomy.  In the proof of Theorem 15.2 the receiving pure time was
chosen within an arbitrary `eta>0` of the full unrestricted cap.  Choose
`eta` small enough that, for the fixed extracted gain `g`,

\[
 \eta< {\gamma g\over2R},                                   \tag{15.20}
\]

where `gamma` is the checked terminal exploitability gap.  The declarations
in `TerminalSemanticPaidFirstDisagreementOrientation.lean` then give the
following exhaustive strategic dispatch at the same block-internal row.

* If the receiving witness is later, then from the profile in which the
  observer uses the earlier source pure time, switching to the receiving
  pure time is one legal behavioral deviation of gain at least `g`.
* If the receiving witness is earlier, then from the profile in which the
  observer uses that earlier receiving time, some fixed outsider has a
  one-row pure-endpoint behavioral deviation at `row.start` of gain at least
  `gamma*g/(2R)`.

Thus (15.18) can be upgraded to a **uniform block-internal legal strategic
deviation**, with an explicit owner/outsider orientation and no horizon
loss.  This is the strongest presently available answer to whether the first
disagreement can be consumed: it reaches the checked live atomic outsider
leaf in the earlier-receiving arm.

It still does not give a terminal approximation, paid reset, or uniform
equilibrium.  Both source profiles above replace the observer by a selected
pure stopping time; neither is asserted to be an approximate equilibrium or
to lie on the global-minimum fibre.  The orientation file itself explicitly
stops before reset-cube or chronological re-entry.  Terminal exploitability
is compatible with, and indeed supplies, legal deviations of this form.

Nor does the localized row force a smaller debt-support or chamber label.
The coordinate recursion

\[
 d'_i=c\,d_i+e_i                                           \tag{15.19}
\]

allows all coordinates to remain positive while one `e_i` is macroscopic.
The first-disagreement action orientation also need not agree with the zero
debt owner or the positive-incidence labels in a reset-rigid chamber.
Consequently neither support inclusion nor a Boolean coalition rank drops
from (15.18).

The exact remaining field is now narrower: a consumer must preserve
`row.start<L` and its common literal block ancestry when passing from the
paid row to an admissible port, or must show that the inert stall is
incompatible with this block-internal uniform reach.  The existing cap-port
construction forgets that cut/location field.  Without such an adapter,
(15.18) is a quantitative source theorem, not a UE conclusion.

Suggested Lean handoff:

```text
quittingFiniteWordCoordinateWeightedCapDefectLedger
quittingFiniteWordCoordinateDebt_eq_weightedLedger_add
nonempty_paidFirstDisagreementRow_before_length_of_weightedLedger_pos
fixedMarginalHazard_nearMinimum_exists_uniformlyReached_paidRow_before_length
fixedMarginalHazard_nearMinimum_exists_blockInternalStrategicDispatch
```

The proof should reuse
`quittingTerminalPayoff_update_eq_expect_stoppingLaw_pureTime`,
`sSup_range_quittingTerminalPayoff_update_eq_pureTime`, and
`exists_quittingPaidFirstDisagreementRow_of_pureTimePayoff_sub`.  It should
not replace the hybrid source support by original-strategy support.

## 16. Global source minimality removes the singleton/Never chamber

An independent audit requested after Section 15 gives one immediate
strengthening of the newly checked chamber source.  The full review is
[`CODEX_SOURCE_GATE__GLOBAL_MINIMUM_EXCLUDES_SINGLETON_NEVER_CHAMBER__BY_CODEX_STRENGTHEN.md`](../feedback/CODEX_SOURCE_GATE__GLOBAL_MINIMUM_EXCLUDES_SINGLETON_NEVER_CHAMBER__BY_CODEX_STRENGTHEN.md).

Because the actual Fin4 hull origin is a globally minimum positive semantic
pair and belongs to its hull, every hull minimizer `z` has

\[
 D(z)=D(origin)=D_*>0                                      \tag{16.1}
\]

and is itself a global semantic minimizer.  The checked
`minimumTerminalSemantic_singletonMargin` gives the dimension-free moat

\[
 D_*\le z.cap_i-r_i(\{i\})\qquad\forall i.                  \tag{16.2}
\]

The `cap_binding` field of
`QuittingSingletonNeverBindingCycleChamber` makes the right side zero at its
owner, contradicting (16.2).  In fact (16.2) holds on the whole minimum face;
Theorem 14.1 upgrades it to every point of this actual hull.

Therefore the actual Fin4 strict trichotomy contracts to the mutually
exclusive two-arm alternative

\[
 \boxed{\text{full debt support}\quad\lor\quad
        \text{reset-rigid same-law return}.}                 \tag{16.3}
\]

Reset-rigid survives: zero semantic debt means `cap=prescribed` at its owner,
whereas (16.2) says this common value lies strictly above the singleton
reward.  The reset dispatch contains no singleton cap-binding equality.
Thus Sections 15.6--15.8 should now be aimed only at the full-debt and
reset-rigid branches.

## 17. Reset-rigid aligned atom versus the block-internal paid row

This section tests the reset-specific retained-law result in
[`CODEX_ROOT__RESET_RIGID_GLOBAL_MOAT_ALIGNED_LAW_SURPLUS.md`](CODEX_ROOT__RESET_RIGID_GLOBAL_MOAT_ALIGNED_LAW_SURPLUS.md)
against Theorem 15.2.  The aligned-law theorem is valid and useful, but its
owner/atom labels do **not** align with the macroscopic ledger extraction.
There is a sharp coordinate reason.

### 17.1 The reset owner carries asymptotically zero seam ledger

Let `o` be the reset-rigid owner at the globally minimum returned point
`X`, so

\[
 d_o(X)=0.                                                   \tag{17.1}
\]

For any literal word with whole semantic pair `X_0`, terminal pair `X_L`,
and joint survival `P`, the coordinate telescope used in Theorem 15.2 is

\[
 d_o(X_0)=\Lambda_o+P d_o(X_L).                              \tag{17.2}
\]

Therefore, along an actual same-chronology near-return with both endpoints
converging to the returned reset point,

\[
 0\le\Lambda_o
   =d_o(X_0)-P d_o(X_L)\longrightarrow0.                    \tag{17.3}
\]

If the terminal endpoint is literally `X`, then
`Lambda_o=d_o(X_0)`; if both endpoints are literally `X`, then
`Lambda_o=0` exactly.  Consequently a uniform positive total ledger in the
reset near-return is necessarily carried asymptotically by players other
than the reset owner.  The pigeonholed observer in Theorem 15.2 cannot be
forced to equal `o`; the proposed owner alignment is not merely absent from
the proof but is opposed by the exact coordinate account.

### 17.2 The retained atom is not the first-disagreement event

The aligned-law finite branch supplies one terminal atom `S` with

\[
 \mu(S)>0,qquad S\ne\{o\},qquad
 \mu(S)\bigl(r_o(S)-r_o(\{o\})\bigr)\ge D_*/30              \tag{17.4}
\]

in Fin4, together with a strict toggle on `S`.  These fields live in the
terminal, time-forgetting law and in the **owner's** payoff coordinate.
By contrast, Theorem 15.2 selects:

1. a coordinate `i` maximizing a weighted cap-defect ledger;
2. a near-best tail pure time for player `i`; and
3. a first disagreement strictly before the terminal cut.

The ledger contains no terminal-law label.  When `i ne o`, (17.4) gives no
payoff inequality for `i`.  Moreover the first-disagreement coalition at a
prefix row is determined by that row's product marginals and the two
hypothetical pure-time witnesses; `S` is an outcome of the retained suffix
law.  Positive mass of `S` does not assert positive conditional mass at the
selected prefix row, and changing either pure-time witness can change the
terminal coalition distribution.  Thus multiplying the two positive lower
bounds is invalid: they are not probabilities of two events in one retained
coupling.

There are three currently independent labels:

* the zero-debt reset owner `o`;
* an opponent `j in S`, and a possibly different strict-toggle player on
  `S`; and
* the paid ledger observer `i`, followed in the earlier orientation by an
  arbitrarily selected outsider.

No checked field identifies any two of these labels.

### 17.3 A strong owner-paid row survives, but it has zero capacity charge

The global moat nevertheless gives a separate, sharp owner-aligned paid row.
Take actual joint-carrier approximants to the returned reset point.  Prepend
one literal all-Continue row.  For all sufficiently accurate approximants,
the strict singleton moat makes every tail cap dominate its singleton
reward, so this prefix preserves the semantic pair and terminal law.

For the owner `o`, the prescribed payoff is the stopping-law average of its
pure-time deviations.  Support bracketing chooses a pure time in the owner's
prescribed stopping-law support with payoff at least the prescribed average.
After shifting it through the prepended row, compare it with Quit at the new
date zero.  The latter pays exactly `r_o({o})`, while the former has payoff
tending to

\[
 X^u_o=X^B_o\ge r_o(\{o\})+D_*.                              \tag{17.5}
\]

Hence, for every `epsilon>0`, sufficiently accurate approximants carry an
owner-labelled `QuittingPaidFirstDisagreementRow` with

\[
 row.start=0,qquad row.liveMass=1,qquad
 row.receivingEarlier=false,qquad gain\ge D_*-\epsilon.     \tag{17.6}
\]

The receiving time may be chosen in the original owner's stopping-law
support.  The checked later-receiving orientation turns (17.6) into a legal
owner deviation of the same gain from the Quit-now pure profile.

This does **not** consume bounded exact-block capacity.  The prepended root
is all Continue, exact cap--Nash, and has zero hazard and zero coordinate
Nash defect.  The paid comparison uses the unplayed Quit-now witness against
the strictly better Continue/tail witness; it is not a played-action mistake
and contributes zero to the cap-defect ledger.  It also does not identify
the receiving witness with atom `S`: a high pure-time expected payoff can be
funded by other terminal outcomes even while (17.4) holds.

### 17.4 Exact missing alignment field

To combine (17.4) with the block-internal seam one needs genuinely new
same-witness data, not another scalar inequality.  A sufficient port would
retain:

1. an actual realizing profile and a marked occurrence of the exact atom
   `S` with the product floor (17.4);
2. a finite cut and a conditional law showing that this marked occurrence
   survives to the selected first-disagreement row under both witnesses;
3. identification of the paid observer or oriented outsider with the owner
   or a named toggle player of `S`; and
4. a cap/reset re-entry after the local deviation.

The current global-minimum hull, reset dispatch, aligned-law surplus, and
weighted seam ledger provide these four items separately but not jointly.
The strongest honest combined conclusion is therefore a dichotomy of
certificates—an owner/atom terminal-law certificate and an independently
labelled block-internal strategic deviation—not an atom-anchored paid reset.

### 17.5 The strongest literal profile-pair form

The owner-paid row above is the pure-time shadow of a cleaner literal pair.
Let `sigma_n` be actual profiles whose joint semantic/law data converge to
the reset-rigid returned point `(X,mu)`, and put

\[
 A_n=(\text{at date }0:\ o\text{ Quits, every }j\ne o\text{ Continues};
          \text{ then }\sigma_n),
 \qquad
 B_n=(\text{at date }0:\ \text{all Continue};
          \text{ then }\sigma_n).                         \tag{17.7}
\]

Thus `A_n` and `B_n` differ only in player `o`'s date-zero action.  Every
opponent strategy is literally identical, including the complete tail.  If
`s_o=r_o({o})`, then their unrestricted owner caps are exactly equal:

\[
 C_o(A_n)=C_o(B_n)=\max\{s_o,C_o(\sigma_n)\}.              \tag{17.8}
\]

The global singleton moat at `X` and semantic convergence imply, for every
player and all sufficiently large `n`, that the tail cap strictly dominates
that player's singleton reward.  Hence the all-Continue prefix is then
semantically inert:

\[
 \operatorname{Sem}(B_n)=\operatorname{Sem}(\sigma_n),
 \qquad \operatorname{Law}(B_n)=\operatorname{Law}(\sigma_n). \tag{17.9}
\]

The second equality is exact, not merely asymptotic: the terminal law forgets
the one-unit time shift.  In particular the `B_n` joint data retain the
shifted minimum law and converge to `(X,mu)`.

The first profile absorbs at date zero, so

\[
 U(A_n)=r(\{o\}),\qquad \operatorname{Law}(A_n)=\delta_{\{o\}}. \tag{17.10}
\]

Combining (17.8)--(17.10) gives the exact own-debt subtraction identity

\[
 \begin{aligned}
 d_o(A_n)-d_o(B_n)
   &=U_o(B_n)-U_o(A_n)\\
   &=U_o(\sigma_n)-s_o
     \longrightarrow X^u_o-s_o
      =X^C_o-s_o\ge D_* .                                 \tag{17.11}
 \end{aligned}
\]

Here the reset equality is `X^u_o=X^C_o`, while `d_o(B_n)->0`.
This is stronger than the statement that two pure times differ: it retains
one literal profitable behavioral replacement, identical opponents, exact
cap equality, the minimum-law endpoint `B_n`, and exact coordinate-debt
subtraction simultaneously.

There is also a precise semantic limit for the other endpoint.  Continuity of
one-root prefixing gives

\[
 \operatorname{Sem}(A_n)\longrightarrow
 Y:=\operatorname{Prefix}_{\{o\}}(X),                     \tag{17.12}
\]

where

\[
 Y^u_i=r_i(\{o\}),\qquad
 Y^C_o=\max\{r_o(\{o\}),X^C_o\}=X^C_o,                   \tag{17.13}
\]

and, for `j ne o`,

\[
 Y^C_j=\max\{r_j(\{o\}),r_j(\{o,j\})\}.                  \tag{17.14}
\]

Thus `A_n` converges to the pure-singleton-root-over-`X` pair, with the
owner cap genuinely inherited from the tail.  Global minimality only gives
`D(Y)>=D_*`; it does **not** give the strict inequality `D(Y)>D_*`.

These statements are ordinary mathematics assembled from the checked
one-root semantic equations, terminal-law shift invariance, and
`minimumTerminalSemantic_singletonMargin`.  The exact bundled profile-pair
adapter itself is not yet a named declaration.

### 17.6 Exact audit against the three current interfaces

#### Strong concentrated singleton packet: yes, but it forgets the pair

At stage zero, `A_n` has terminal coalition `{o}` with mass exactly one.
Therefore for every `0<lambda<=1`,
`FinFourSingletonStageStrongConcentratedPacket.nonempty_of_singleton_stageMass`
directly constructs a strong concentrated packet from `A_n`.  Its packet
owner must, however, be some player distinct from `o`.  The checked
`FinFourSingletonStageStrongConcentratedPacket.consumerResult` then returns
the Continue-routing strategic arm or a
`QuittingConcentratedCollisionMinimumResidual`.

This adapter discards every special field of (17.7)--(17.11): it stores no
comparison profile `B_n`, common-owner-cap equality, minimum-law endpoint,
or reset-aligned atom.  Its selected packet owner is not the reset owner;
its target is obtained by best-endpoint routing that different player at the
singleton row, hence is `{o}` or `{o,j}`, not the all-Continue/tail profile
`B_n`.  Thus the pair **does inhabit** the strong-packet producer, but only
through a generic singleton mass-one injection available over any tail.  The
consumer remains exactly its already recorded two-arm residual.

#### Paid-cap port: yes after pure-time bracketing, but no pair-preserving port

The pair by itself is a profitable unrestricted behavioral replacement, not
literally a `QuittingPaidFirstDisagreementRow`, whose two witnesses must be
deterministic pure times.  Apply the checked stopping-law support bracketing
to player `o`'s strategy in `B_n`: choose a tail pure time whose deviation
payoff is at least `U_o(B_n)`.  Against the common opponent profile, compare
that shifted time with date-zero Quit.  For any fixed `g<D_*` and all late
`n`, `exists_quittingPaidFirstDisagreementRow_of_pureTimePayoff_sub` yields a
row with

\[
 observer=o,\quad start=0,\quad liveMass=1,\quad
 receivingEarlier=false,\quad gain\ge g.                  \tag{17.15}
\]

Using `A_n` (or equivalently `B_n`, since the observer's prescribed strategy
does not enter pure-time deviation payoffs) as the realizing profile, this
does instantiate `QuittingPaidCapLiftedSource` and hence its summable cap
port.  But the source structure stores only one realizing profile plus the
decoded row.  It stores neither the literal target `B_n` nor (17.8), (17.9),
or the common tail.  Its checked trichotomy is only charged near-return,
quantitative debt descent, or inert stall.  The endpoint debt of `A_n`
converges to `D(Y)>=D_*`, with no strict excess guaranteed; if `D(Y)=D_*`,
the inert minimum-fibre arm remains possible.  Using `B_n` instead makes the
initial debt converge to `D_*` and the cap-lifted absorption budget collapse.

The stronger
`PaidFirstDisagreementAdmissiblePayoffNearReturnConsumer` is not directly
inhabited.  It requires a mover in the base positive-debt support, whereas
the reset owner satisfies `d_o(X)=0`; it separately requires
`observer ne mover`, whereas the pair's gain is owner-against-owner; and it
requires a tangent/full-replacement cluster with a strict total-debt
separation.  The pair supplies none of the tangent scale, selected cluster,
or strict `D(Y)>D_*` field.

#### Forced-pair interfaces: no

`FinFourWeakCoreForcedPairPacket` and
`FinFourOwnerCompressedMinimumReturnForcedPairSource` are dependent on a
`FinFourMinimumAtomProducer`.  Their singleton is the source-retained atom
at the source's fixed causal date, their distinct table-selected owner has a
terminal-gap join inequality, their routed target is the literal pair
`{o,j}`, and the minimum-return version retains cofinal ranks, a resolution
below the source atom mass, and a fixed positive-defect payer.

The singleton in `A_n` is an artificially prepended sure atom, not the named
retained source atom in that fixed chronology.  The comparison endpoint
`B_n` is the all-Continue/tail minimum-law profile, not a forced pair.  The
literal profile pair provides no fixed joiner `j`, no join-gap inequality,
no payer-defect floor, no cofinal source ranks, and no identification with the
reset-aligned terminal atom `S`.  Even when some retained source atom happens
to be a singleton, equality of its label with the artificial date-zero event
and the required same-chronology ancestry do not follow.  Hence (17.7) does
**not** instantiate either forced-pair interface.

The exact new adapter worth formalizing is therefore not another singleton
packet.  It is a **minimum-return owner-toggle pair** bundling `A_n`, `B_n`,
opponent equality, owner-cap equality, `B_n` semantic/law return, (17.11),
and the limit (17.12).  A useful consumer must retain both endpoints; sending
this data through the current strong-packet or paid-cap structures erases the
property that makes the pair new.
