# Positive-minimum carrier cycles pay a linear semantic-seam toll

Authors: SOCIAL_WEIGHT_REVIEW

Independent reviews:
[PAIRED_HULL_REVIEW](../feedback/SOCIAL_WEIGHT_REVIEW__OFF_MINIMUM_PURE_CLOCK_RESPONSE_CYCLE_TEMPORAL_ATTACK__BY_PAIRED_HULL_REVIEW.md),
[CODEX_DESCENDANT](../feedback/POSITIVE_MINIMUM_CARRIER_CYCLE_SEAM_TOLL__BY_CODEX_DESCENDANT.md)

## Exact statement

Let \(I\) be a nonempty finite player set and let

\[
r:\{S\subseteq I:S\ne\varnothing\}\longrightarrow\mathbb R^I
\]

be a quitting-game reward table. For a terminal-semantic pair
\(z=(U,B)\), define

\[
d_i(z)=B_i-U_i,
\qquad
D(z)=\sum_{i\in I}d_i(z).
\tag{1}
\]

Assume that the terminal-semantic carrier \(\mathcal K_r\) has a positive
global debt floor

\[
D(z)\ge D_*>0
\qquad(z\in\mathcal K_r).
\tag{2}
\]

Fix an integer \(L>0\), carrier points

\[
z^0,\ldots,z^{L-1}\in\mathcal K_r,
\qquad z^L=z^0,
\tag{3}
\]

and product roots \(q_0,\ldots,q_{L-1}\). Root \(q_k\) is evaluated against
the displayed unrestricted cap \(B(z^k)\). Put

\[
c_k=\Pr_{q_k}(\text{all Continue}),
\qquad
a_k=1-c_k,
\tag{4}
\]

and let

\[
w^k=\operatorname{Prefix}_r(q_k,z^k)
\tag{5}
\]

be the terminal-semantic pair obtained by prefixing \(q_k\) to \(z^k\).
Write \(N_k\) for the total one-row Nash defect of \(q_k\) against
\(B(z^k)\):

\[
N_k=
\sum_{i\in I}
\left(
\max\{Q_i(q_k;B(z^k)),C_i(q_k;B(z^k))\}
-S_i(q_k;B(z^k))
\right).
\tag{6}
\]

Here \(Q_i,C_i,S_i\) are respectively player \(i\)'s pure-Quit endpoint,
pure-Continue endpoint, and prescribed mixed-root payoff. Thus \(N_k\ge0\),
and \(N_k=0\) when \(q_k\) is an exact Nash root.

Define the signed total-debt rebase seam

\[
s_k=D(z^{k+1})-D(w^k).
\tag{7}
\]

Then

\[
\boxed{
\sum_{k<L}s_k
=\sum_{k<L}\bigl(a_kD(z^k)-N_k\bigr).}
\tag{8}
\]

In particular, if every \(q_k\) is an exact Nash root, then

\[
\boxed{
\sum_{k<L}s_k
=\sum_{k<L}a_kD(z^k)
\ge D_*\sum_{k<L}a_k.}
\tag{9}
\]

Write the two-coordinate semantic seam as

\[
e^k_U=U(z^{k+1})-U(w^k),
\qquad
e^k_B=B(z^{k+1})-B(w^k),
\tag{10}
\]

and put

\[
E_k=\sum_{i\in I}
\bigl(|e^k_{U,i}|+|e^k_{B,i}|\bigr).
\tag{11}
\]

For exact roots,

\[
\boxed{
\sum_{k<L}E_k\ge D_*\sum_{k<L}a_k.}
\tag{12}
\]

If \(I=\operatorname{Fin}4\) and the semantic-pair norm is the maximum of
the eight payoff/cap coordinate errors, then

\[
\boxed{
\sum_{k<L}\|z^{k+1}-w^k\|_\infty
\ge {D_*\over8}\sum_{k<L}a_k.}
\tag{13}
\]

There is also an approximate form. If \(\eta_k\ge0\) and \(q_k\) is an
ordinary \(\eta_k\)-Nash root, then

\[
N_k\le |I|\eta_k,
\]

and hence

\[
\boxed{
\sum_{k<L}E_k
\ge
D_*\sum_{k<L}a_k-|I|\sum_{k<L}\eta_k.}
\tag{14}
\]

Consequently, if total root Nash defect is little-oh of total absorption,
the full payoff/cap rebase seam cannot be little-oh of total absorption.

The result is unchanged by stationary randomized rematching of the phase
sources. Let \(\beta_0,\ldots,\beta_{L-1}\ge0\) sum to one, and let
\(\lambda_{k\ell}\ge0\) be a coupling whose row and column marginals are
both \(\beta\):

\[
\sum_{\ell<L}\lambda_{k\ell}=\beta_k,
\qquad
\sum_{k<L}\lambda_{k\ell}=\beta_\ell.
\tag{14a}
\]

Root \(q_k\) remains attached to its original source \(z^k\), and
\(w^k=\operatorname{Prefix}_r(q_k,z^k)\) remains literal. For a possible
rebase target \(z^\ell\), put

\[
s_{k\ell}=D(z^\ell)-D(w^k)
\tag{14b}
\]

and define \(E_{k\ell}\) from the full payoff/cap coordinate difference
\(z^\ell-w^k\), as in (10)--(11). Then

\[
\boxed{
\sum_{k,\ell<L}\lambda_{k\ell}s_{k\ell}
=
\sum_{k<L}\beta_k\bigl(a_kD(z^k)-N_k\bigr).}
\tag{14c}
\]

For exact roots,

\[
\sum_{k,\ell<L}\lambda_{k\ell}E_{k\ell}
\ge
D_*\sum_{k<L}\beta_ka_k.
\tag{14d}
\]

On Fin4,

\[
\sum_{k,\ell<L}\lambda_{k\ell}
  \|z^\ell-w^k\|_\infty
\ge
{D_*\over8}\sum_{k<L}\beta_ka_k.
\tag{14e}
\]

For ordinary \(\eta_k\)-Nash roots, the right side of (14d) is replaced by

\[
D_*\sum_{k<L}\beta_ka_k
-|I|\sum_{k<L}\beta_k\eta_k.
\tag{14f}
\]

A permutation of equally weighted phase sources is the special case
\(\lambda_{k\ell}=L^{-1}\mathbf1_{\{\ell=\pi(k)\}}\). Thus neither
deterministic phase reordering nor a stationary convex rematching of the
same carrier-source distribution can evade the toll.

The open-chain form is equally exact. For carrier points
\(z^0,\ldots,z^L\), without the cyclic equality, one has

\[
\boxed{
\sum_{k<L}\bigl(D(z^{k+1})-D(w^k)\bigr)
=D(z^L)-D(z^0)
+\sum_{k<L}\bigl(a_kD(z^k)-N_k\bigr).}
\tag{15}
\]

For exact roots, if \(E_0=D(z^0)-D_*\), then

\[
\sum_{k<L}\bigl(D(z^{k+1})-D(w^k)\bigr)
\ge D_*\sum_{k<L}a_k-E_0.
\tag{16}
\]

Thus an off-minimum source can spend its initial excess once on exact-root
absorption. Renewing charge after that excess is exhausted requires a
positive signed rebase seam.

## Conjecture-facing change

The maintained approximate-forward-packet or capacity-barrier question
allows, as one possible answer, finitely many source-faithful moves across
different tails whose payoff and cap seams cancel while positive exact-root
charge survives.

Equations (9)--(13) rule out that alternative when the displayed phase
sources are actual terminal-semantic carrier points and every root is tested
against its actual unrestricted cap. Exact vector cancellation is impossible
as soon as one phase has positive absorption. Even asymptotic cancellation at
error \(o(\sum a_k)\) is impossible when total Nash defect is
\(o(\sum a_k)\). Equations (14a)--(14f) show that reordering the phases or
randomizing their stationary matching does not help.

Therefore a forward-packet construction must instead do at least one of the
following:

1. pay the macroscopic semantic seam through an accepted chronological
   ledger;
2. turn the seam into a renewable finite-rank transition;
3. leave the actual carrier-cap chart by constructing new Bellman
   annotations; or
4. reach a terminal consumer.

This is a no-go for one proposed route, not a construction of a forward
packet and not a consumer of bounded capacity.

## Definitions and assumptions

At each live date every player independently randomizes between Continue and
Quit. Before absorption the public history is only the number of preceding
all-Continue dates. An unrestricted unilateral behavioral deviation may use
any randomized stopping law on

\[
\overline{\mathbb N}=\mathbb N\cup\{\mathrm{Never}\}.
\]

For an actual behavioral profile \(\sigma\), its terminal-semantic pair is

\[
z(\sigma)=\bigl(U(\sigma),B(\sigma)\bigr),
\]

where

\[
B_i(\sigma)=\sup_{\tau_i}U_i(\sigma[i\leftarrow\tau_i])
\]

ranges over every behavioral replacement. The carrier is the closure of
these semantic pairs. In particular, every carrier point has nonnegative
debt coordinates. Assumption (2) is exactly the positive-global-minimum
counterexample regime.

The product roots \(q_k\) are one-row independent action profiles. They may
be mixed and need not be induced by the source profile. What is essential is
that their Nash condition is evaluated against the actual cap coordinate
\(B(z^k)\), not against a newly invented annotation.

A support-\(\eta_k\) Nash root with \(\eta_k\ge0\) is, in particular, an
ordinary \(\eta_k\)-Nash root. Thus (14) applies to the support-local error
mode used by finite forward packets whenever the other source hypotheses are
present.

Every repeated copy of a phase must include its own actual rebase seam from
the prefixed carrier point to the next displayed carrier source. One may not
multiply a phase's absorption charge while counting its rebase seam only
once.

The stationary coupling theorem is algebraic and does not introduce public
correlation into the quitting game. It says that even if a proposed
construction externally randomizes or frequency-mixes which displayed
carrier source follows each prefixed phase, cancellation is impossible when
the incoming and outgoing phase frequencies have the same marginal
\(\beta\). It makes no claim for nonstationary marginals or newly introduced
noncarrier annotations.

## Source correspondence

For an arbitrary product root and semantic pair, the checked identity

~~~text
quittingTerminalSemanticDebtSum_prefix_eq_continueMass_mul_add_capDefect
~~~

in

~~~text
UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/
CapDebtBellmanReduction.lean
~~~

is exactly

\[
D(\operatorname{Prefix}_r(q,z))
=c(q)D(z)+N(q;B(z)).
\tag{17}
\]

The nonnegativity and exact-Nash characterization of \(N\), and the estimate

\[
N(q;B)\le |I|\eta
\]

for an ordinary \(\eta\)-Nash root, are in

~~~text
UniformEquilibrium/Quitting/Root/NashDefect.lean
~~~

as

~~~text
quittingRootTotalNashDefect_nonneg
isZeroQuittingRootNash_iff_totalNashDefect_eq_zero
quittingRootTotalNashDefect_le_card_mul_of_isεQuittingRootNash
~~~

The support-local-to-ordinary implication is

~~~text
isQuittingRootEndpointNash_of_supportApproxNash
isεQuittingRootEndpointNash_iff_isεQuittingRootNash
~~~

in, respectively,

~~~text
UniformEquilibrium/Quitting/Paths/SupportWitnessClockCollapse.lean
UniformEquilibrium/Quitting/Root/SuccessorCertificate.lean
~~~

Prefix closure of the carrier is

~~~text
quittingTerminalSemanticPrefix_mem_carrier
~~~

in

~~~text
UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean
~~~

The general survival-weighted finite-chain seam algebra is checked in

~~~text
UniformEquilibrium/Quitting/Debt/Dynamic/
TerminalSemanticSignedSeamTelescope.lean
~~~

The new content is the unweighted cyclic specialization (8), its exact
positive-minimum lower bound, the sharp Fin4 factor \(1/8\), and the direct
exclusion of aggregate source-attached response-seam cancellation. The
stationary-coupling extension (14c) rules out permutation and convex
phase-rematching loopholes. No external paper result is used.

## Proof

The checked prefix identity (17) applied at phase \(k\) gives

\[
D(w^k)=c_kD(z^k)+N_k.
\tag{18}
\]

Therefore

\[
\begin{aligned}
\sum_{k<L}s_k
&=\sum_{k<L}D(z^{k+1})-
  \sum_{k<L}\bigl(c_kD(z^k)+N_k\bigr)\\
&=\sum_{k<L}D(z^k)-
  \sum_{k<L}\bigl(c_kD(z^k)+N_k\bigr)\\
&=\sum_{k<L}\bigl((1-c_k)D(z^k)-N_k\bigr),
\end{aligned}
\]

which is (8). Exact Nash gives \(N_k=0\); (2) then gives (9).

By (10),

\[
s_k=\sum_{i\in I}(e^k_{B,i}-e^k_{U,i}).
\tag{19}
\]

Thus

\[
|s_k|\le E_k.
\]

Since the sum in (9) is nonnegative,

\[
\sum_{k<L}E_k
\ge\sum_{k<L}|s_k|
\ge\left|\sum_{k<L}s_k\right|
=\sum_{k<L}s_k
\ge D_*\sum_{k<L}a_k,
\]

which is (12). On Fin4,

\[
E_k\le8\|z^{k+1}-w^k\|_\infty,
\]

so (13) follows.

For an ordinary \(\eta_k\)-Nash root, the checked total-defect estimate gives
\(N_k\le |I|\eta_k\). Substitute this into (8) and repeat the preceding
triangle-inequality argument to obtain (14).

For the stationary coupling, use the two marginal identities in (14a):

\[
\begin{aligned}
\sum_{k,\ell<L}\lambda_{k\ell}
  \bigl(D(z^\ell)-D(w^k)\bigr)
&=
\sum_{\ell<L}\beta_\ell D(z^\ell)
-\sum_{k<L}\beta_kD(w^k)\\
&=
\sum_{k<L}\beta_k
  \bigl(D(z^k)-D(w^k)\bigr)\\
&=
\sum_{k<L}\beta_k
  \bigl(a_kD(z^k)-N_k\bigr).
\end{aligned}
\]

This proves (14c). The same triangle-inequality argument, now weighted by
\(\lambda_{k\ell}\), proves (14d)--(14f). The permutation statement follows
by inserting its deterministic coupling.

Without cyclicity,

\[
\sum_{k<L}\bigl(D(z^{k+1})-D(z^k)\bigr)
=D(z^L)-D(z^0).
\]

Adding

\[
\sum_{k<L}\bigl(D(z^k)-D(w^k)\bigr)
=\sum_{k<L}\bigl(a_kD(z^k)-N_k\bigr)
\]

proves (15). For exact roots, use \(D(z^L)\ge D_*\),
\(D(z^0)=D_*+E_0\), and \(D(z^k)\ge D_*\) to obtain (16).

## Boundary tests

### Positivity is essential

In the all-zero reward table, the all-Never semantic pair has \(U=B=0\).
Every product root is exact, every prefix has the same semantic pair, and a
positive-absorption one-phase cycle has zero seam. No positive lower bound is
possible when \(D_*=0\).

### Exact sign test

For any finite player set, give every player reward \(1\) at every nonempty
quitting coalition. At the all-Never profile,

\[
U=0,
\qquad B=\mathbf1,
\qquad D=|I|.
\]

Let one player Quit surely in the prefix root and let all other players
Continue surely. The root is exact against \(B=\mathbf1\), has absorption
one, and its prefix has \(U=B=\mathbf1\), hence zero debt. The one-phase
rebase seam is therefore

\[
s=|I|=aD,
\]

with the sign in (8). This game itself has global minimum zero; the example
checks the algebra rather than assumption (2).

### The approximate correction cannot be omitted

Take two players. Let player \(1\) plan to Quit at date \(1\), player \(0\)
Never Quit, and choose rewards so that player \(0\) receives zero from
\(\{1\}\) and from its singleton \(\{0\}\), but receives one from
\(\{0,1\}\). Give player \(1\) zero in every coalition. The resulting
actual profile has player-\(0\) payoff zero and cap one, attained by joining
at date \(1\).

At a new prefix date, let player \(0\) Quit with probability \(h\) and player
\(1\) Continue surely. Against the displayed cap, Continue pays one and Quit
pays zero. The root absorption and total Nash defect are both \(h\). The
prefix retains total debt one, so rebasing to the same source has zero debt
seam:

\[
0=aD-N=h-h.
\]

Thus the \(-\sum N_k\) term in (8), and hence the correction in (14), is
necessary. The table is again only a boundary test; it has zero global
minimum.

### Fresh Bellman annotations lie outside the theorem

A periodic normalized-motion compiler may build new Bellman payoff vectors
from a root word. Those vectors need not be the unrestricted caps of actual
carrier points. Such a compiler does not satisfy the source condition in
(3)--(6), so the theorem does not rule it out.

### Phase reordering and convex mixing

Changing the cyclic order cannot change the scalar debt account: a
permutation only reorders the same target debts. More generally, (14c)
shows that fractional rematching cannot help when its source and target
marginals agree. The equal-marginal hypothesis is essential. If target
weights are changed, their change in average debt is an endpoint term rather
than a cancellation, exactly as in the open-chain formula (15).

## Adapter and consumer

The adapter is direct. Any proposed source-faithful finite cancellation uses
actual behavioral profiles or their carrier limits as phase sources. Their
cap coordinates are unrestricted behavioral caps, and arbitrary product
prefixing remains inside the carrier. Therefore those sources, their
selected roots, and their proposed next-source rebases instantiate (3)--(11).

If the roots are exact and some absorption survives, (12) contradicts exact
payoff-and-cap seam cancellation. If roots are approximate with total Nash
defect \(o(\sum a_k)\), (14) contradicts semantic seam
\(o(\sum a_k)\). Hence the source-attached cancellation alternative in the
maintained forward-packet question is eliminated.

The same adapter covers a finite recurrent phase controller with stationary
frequency \(\beta\): its empirical transition frequencies supply
\(\lambda\), and (14d) forces a positive average semantic seam per unit of
exact-root charge. This observation does not itself construct such a
controller or turn the seam into chronological charge.

There is no downstream terminal consumer in this packet. The surviving
routes are to pay the forced seam through an existing chronological ledger,
turn it into a finite rank, or abandon source caps and construct a new
floor-admissible Bellman chart.

## Lean handoff

The narrowest formalization is a finite cyclic theorem over \(\operatorname{Fin}L\):

~~~text
terminalSemanticCarrierCycle_sum_signedDebtRebase_eq
~~~

with fields for the carrier point, product root, prefixed point, and cyclic
successor. Its conclusion should first be the exact identity (8). Separate
corollaries should state:

~~~text
terminalSemanticCarrierCycle_exactRoot_seam_ge
terminalSemanticCarrierCycle_finFour_supNorm_seam_ge
terminalSemanticCarrierCycle_approxRoot_seam_ge
terminalSemanticCarrierStationaryCoupling_seam_ge
terminalSemanticCarrierChain_exactRoot_debtBattery
~~~

The proof needs only the declarations named in Source correspondence,
finite-sum reindexing, and the triangle inequality. Exact tests should
include the all-zero boundary, the constant-one sign test, and the
two-player \(aD-N=0\) approximate-root example.

The formalization must keep the cap argument of each root definitionally
equal to the second coordinate of its displayed source. Replacing it by an
arbitrary Bellman annotation would change the theorem.

## Scope and nonclaims

* The theorem does not construct an approximate forward packet.
* It does not consume bounded exact-block capacity.
* It does not turn the forced semantic seam into chronological charge.
* It does not apply to periodic Bellman values selected outside the actual
  terminal-semantic carrier.
* It does not cover a coupling whose source and target marginals differ;
  that mismatch is an endpoint-debt term governed by the open-chain formula.
* It does not rule out approximate roots whose total Nash defect is of the
  same first order as their total absorption.
* It does not temporalize any horizontal best-response cycle.
* It gives no uniform-equilibrium payoff and no positive-gap table.

## Formalization record

This packet was integrated in production Lean by commit
`2f27896475c0c7f6165e52c925bd8aafa97aaa7e`.

The module
`UniformEquilibrium/Quitting/Debt/Dynamic/TerminalSemanticCarrierCycleSeamToll.lean`
contains the following checked surface.

- `QuittingTerminalSemanticCarrierCycle.sum_signedDebtRebase_eq_sum_netAbsorptionCharge`
  is the exact cyclic signed-debt identity for an arbitrary supplied finite
  phase type and successor permutation.
- `debtFloor_mul_sum_absorptionMass_le_sum_semanticL1Rebase_of_exactRoot`,
  `debtFloor_mul_sum_absorptionMass_sub_error_le_sum_semanticL1Rebase`, and
  `finFour_debtFloor_div_eight_mul_sum_absorptionMass_le_sum_semanticSupRebase`
  give the exact-root, approximate-root, and Fin4 factor-`1/8` tolls.
- `QuittingTerminalSemanticCarrierCycle.StationaryCoupling.sum_coupledSignedDebtRebase_eq_sum_weight_mul_netAbsorptionCharge`
  is the equal-marginal coupling identity. Its exact, approximate, and Fin4
  weighted toll corollaries retain the same constants.
- `QuittingTerminalSemanticCarrierOpenChain.sum_signedDebtRebase_eq_endpointDebt_sub_initialDebt_add_charge`
  and
  `QuittingTerminalSemanticCarrierOpenChain.debtFloor_mul_sum_absorptionMass_sub_initialExcess_le_sum_signedDebtRebase`
  give the open-chain endpoint identity and one-use initial-excess battery.

Evidence seals:

- **M:** PASS. The signed identities, constants, arbitrary finite successor
  permutation, stationary coupling, and open-chain battery match the reviewed
  packet mathematics.
- **L:** PASS. The declarations are checked with warnings as errors, reachable
  from the production umbrella, and covered by the generated axiom audit.
- **A:** absent. No declaration constructs the supplied carrier cycle, roots,
  stationary coupling, debt floor, or open chain from actual source data.
- **C:** absent. No declaration converts the forced seam into chronological
  charge, a renewable transition, a terminal consumer, or an equilibrium.

The illustrative zero-minimum sign and approximate-correction examples in the
packet were audit tests, not separate regression theorems. The formalization
does not construct an approximate forward packet, consume bounded capacity,
apply to Bellman annotations outside the terminal-semantic carrier, cover
unequal coupling marginals, temporalize a horizontal cycle, or prove a Nash
profile or uniform-equilibrium payoff.
