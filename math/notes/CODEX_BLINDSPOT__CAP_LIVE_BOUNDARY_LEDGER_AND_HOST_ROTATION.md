# Cap-live boundaries: exact debt ledger and the failure of host rotation

Author: `CODEX_BLINDSPOT`

## Status

Active mathematical note, 2026-09-03.  The exact cap-anchored compiler,
deleted-clock geometry, serial-composition test, and fixed-payer consequence
below are proved in ordinary mathematics.  Their principal identities are
already checked in more general project declarations.  The application to
the current actual-Zeno source is a no-go for a direct terminal compiler, not
a proof of the uniform-equilibrium conjecture.

The main correction to the preceding live-tail audit is:

> A positive player-deleted clock identifies sensitivity to replacing a
> suffix cap, but it is not the minimal state for the debt of one actual
> profile.  If the reference continuation is anchored at the actual suffix
> cap, every tail-debt coordinate is multiplied by **joint** survival.  What
> remains is the nonnegative chronological ledger of root Nash defects
> evaluated against complete suffix caps.

Consequently, at zero joint survival no tail-cap seam survives in the exact
cap-anchored debt recursion.  The entire obstruction is the prefix cap-defect
ledger.  Two simultaneous hosts are impossible; rotating hosts does not
average the ledger; and two distinct hosts in serial depth cannot erase the
outer ledger.  The exact outsider regression realizes this obstruction with
ledger exactly one.

No frozen note, Lean file, export, question, or shared index was edited.

## 1. Exact multi-player cap-live state

Fix a finite nonempty player set `I`, a bounded quitting reward table `r`, an
actual terminal behavioral profile `tau`, and a finite word

\[
 W=(x_0,\ldots,x_{L-1}).
\]

Let `sigma_t` be the actual suffix beginning at row `t`, so
`sigma_L=tau` and `sigma_0=W star tau`.  Write

\[
 u_t=U(\sigma_t),\qquad b_t=B(\sigma_t),qquad
 d_{t,k}=b_{t,k}-u_{t,k}.                              \tag{1.1}
\]

Here `B` is the complete unilateral behavioral cap.  Put

\[
 a_t=\Pr_{x_t}(\text{all players Continue})            \tag{1.2}
\]

and define the complete-suffix cap defect

\[
 c_{t,k}:=operatorname{NashDefect}_k(r,b_{t+1},x_t)\ge0. \tag{1.3}
\]

Finally let

\[
 A_0=1,\qquad A_t=\prod_{s<t}a_s,
 \qquad \alpha(W)=A_L.                                \tag{1.4}
\]

The minimal playerwise prefix tag is the reached defect ledger

\[
                 \Lambda_k(W,\tau)
                   :=\sum_{t<L}A_t c_{t,k}.             \tag{1.5}
\]

It retains the player label, the actual complete suffix cap at which the
defect is evaluated, and the on-path joint reach of the row.  A payoff-level
root defect at an independently chosen target is not a substitute.

## 2. Exact cap-anchored compiler

### Theorem 2.1: playerwise debt identity

For every player `k`,

\[
 d_{0,k}=\Lambda_k(W,\tau)+\alpha(W)d_{L,k}.            \tag{2.1}
\]

Summing over players gives

\[
 D(\sigma_0)=\Lambda(W,\tau)+\alpha(W)D(\tau),
 \qquad
 \Lambda=\sum_k\Lambda_k.                             \tag{2.2}
\]

### Proof

At one row, the prefixed unrestricted cap equals the maximum of the two pure
root endpoints evaluated at the actual suffix cap `b_{t+1}`.  Subtracting the
prescribed root payoff evaluated at `u_{t+1}` gives the exact autonomous
cap--debt recursion

\[
 d_{t,k}=a_t d_{t+1,k}+c_{t,k}.                        \tag{2.3}
\]

Iterate (2.3).  The coefficient of `c_{t,k}` is the joint survival through
all earlier rows, and the terminal coefficient is the full joint survival.
This is (2.1); summation is (2.2).  `□`

### Equivalent cap-diagonal reference

Let the actual tail pair be `(u,b)` and let `Phi_W` be the algebraic semantic
prefix map.  Define the cap-anchored reference

\[
                         Q=\Phi_W(b,b).                 \tag{2.4}
\]

The actual prefixed cap and `Q.2` are identical, because a fixed prefix's
complete cap depends only on the suffix cap.  Its prescribed payoff differs
from `Q.1` by exactly `alpha(W)(u-b)`.  Therefore

\[
 d_k(W\star\tau)
   =\bigl(Q.2_k-Q.1_k\bigr)+\alpha(W)(b_k-u_k).         \tag{2.5}
\]

The first term in (2.5) is exactly `Lambda_k(W,tau)`.  This explains why the
host-cap seam in a payoff-anchored comparison disappears after cap anchoring:
the actual suffix cap is not being replaced.

### Corollary 2.2: necessary and sufficient zero-joint compiler

Let `(W_n,tau_n)` be actual finite word/tail data with bounded rewards and

\[
                         \alpha(W_n)\longrightarrow0.  \tag{2.6}
\]

Then the full profiles `W_n star tau_n` have terminal exploitability tending
to zero if and only if

\[
                         \Lambda_k(W_n,\tau_n)\to0      \tag{2.7}
\]

for every player `k`.  Equivalently, because `I` is finite and all ledger
terms are nonnegative, `Lambda(W_n,tau_n)->0`.

Indeed, terminal tail debts are uniformly bounded, so (2.1) makes (2.6)--
(2.7) sufficient.  Conversely, (2.1) and nonnegativity give
`Lambda_k<=d_{0,k}`, making (2.7) necessary.  After passing to a subsequence
of the bounded full payoff vectors, these profiles converge to one fixed
uniform-equilibrium payoff.

This is the minimal multi-player tag at a cap-live zero-joint boundary.  No
player-deleted tail seam is needed once the actual cap is retained; every
player's reached local cap defect is needed.

## 3. Exact cap--Nash specialization

If every row is exact Nash against the complete cap of its actual suffix,
then every `c_{t,k}=0`.  Thus

\[
 d_k(W\star\tau)=\alpha(W)d_k(\tau)                    \tag{3.1}
\]

for every player.  A sequence of exact cap--Nash words with joint survival
tending to zero is therefore already a terminal approximate-Nash compiler,
regardless of a positive-debt tail.

This is checked as
`quittingTerminalDeviationDebt_capNashRootStack_eq` and
`quittingTerminalDebtSum_capNashRootStack_eq` in
`UniformEquilibrium/Diagnostics/Quitting/TerminalCapNashChronology.lean`.
The one-row identity (2.3) is
`quittingTerminalSemanticDebt_prefix_eq_continueMass_mul_add_capDefect` in
`UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/CapDebtBellmanReduction.lean`.

Thus the project already knows how to compile a zero-joint cap-live word when
the word is cap--Nash.  Under the contrary no-uniform-payoff hypothesis, such
words cannot have joint survival tending to zero.  This is the strategic
content behind the maintained bounded-capacity/all-summable exact-spine
branch; a new host label does not evade it.

## 4. Deleted-clock geometry

For a word `W`, let

\[
 \beta_k(W)=\Pr(W\text{ survives after deleting player }k).
\]

For distinct players `i` and `j`, the checked product inequality is

\[
                         \beta_i(W)\beta_j(W)\le\alpha(W). \tag{4.1}
\]

It follows immediately that if `alpha(W_n)->0`, two distinct deleted clocks
cannot both have positive lower bounds on the same subsequence.  After a
common compact subsequence on which all finitely many `beta_k` converge, at
most one limit can be positive.

This recovers the unique positive-host geometry without Fin4-specific
counting.  `FinFourActualZenoPositiveHost.other_tendsto_zero` is the checked
source-attached specialization.

The roles of the two clocks must not be conflated:

- `beta_k` is the Lipschitz coefficient for changing player `k`'s suffix cap
  behind a fixed word;
- `alpha` is the coefficient of actual suffix debt in (2.1), because cap and
  prescribed payoff are changed together through the cap-anchored reference;
- `Lambda_k` records deviations created inside the prefix itself.

The current positive-host output controls the first clock but not the third
quantity.

## 5. Do two hosts or host rotation compile?

### 5.1 Two live hosts on the same rows: impossible

If `beta_i>=eta_i>0` and `beta_j>=eta_j>0` for `i!=j`, (4.1) gives
`alpha>=eta_i eta_j`.  Such a two-host boundary cannot coexist with joint
survival tending to zero.

### 5.2 Host rotation across ranks: no averaging

A rank-dependent host can alternate, but the player set is finite, so a
strict subsequence freezes one host.  More importantly, approximate Nash is
a maximum over players at each profile, not an average over ranks.  If the
unique live label or a nonhost carries a ledger bounded below on every rank,
rotation does not decrease exploitability.

The exact criterion is (2.7), which is label-free: every playerwise ledger
must vanish on the same sequence.  A schedule in which different ledgers are
large on different ranks fails just as surely as a fixed bad ledger.

### 5.3 Distinct hosts in serial depth: tail erasure, not debt erasure

Let `W_n` be an outer word and `V_n` an inner word.  Exact concatenation gives

\[
 \beta_k(W_n{+}{+}V_n)=\beta_k(W_n)\beta_k(V_n),        \tag{5.1}
\]

so if `W_n` has unique host `h`, `V_n` has unique host `g!=h`, and all their
nonhost deleted clocks vanish, every deleted clock of the concatenation
vanishes.  Thus two distinct serial hosts do erase sensitivity to the deepest
tail cap.

But their cap-defect ledgers satisfy

\[
 \Lambda_k(W_n{+}{+}V_n,\tau_n)
  =\Lambda_k(W_n,V_n\star\tau_n)
   +\alpha(W_n)\Lambda_k(V_n,\tau_n).                  \tag{5.2}
\]

The outer ledger is nonnegative and unscaled.  If it is bounded below, no
inner host can remove it.  If the outer ledger tends to zero and
`alpha(W_n)->0`, the outer word already compiles any bounded suffix by
Corollary 2.2; the second host adds no new Nash mechanism.

Therefore two-host serial composition is conditionally sound but not a new
UE compiler from clock labels alone.  It would become useful only with a new
source-faithful operation that pays, cancels, or regenerates from the outer
ledger.  The current packets provide no literal outer-to-inner attachment in
any case.

## 6. Exact obstruction on the current actual-Zeno rows

The checked aggregate form of (2.2) is
`quittingTerminalSemanticDebtSum_literalRootStack_eq_weightedLedger_add` in
`Research/Quitting/FiniteWordWeightedCapDefectLedger.lean`.

For the current actual-Zeno source:

1. combined joint survival tends to zero;
2. every actual suffix debt is uniformly bounded;
3. the retained minimum terminal-semantic debt `D_*` is strictly positive
   under the contrary no-uniform-payoff hypothesis; and
4. every actual full semantic pair has total debt at least `D_*` by global
   minimality.

Consequently

\[
 \liminf_n\Lambda(W_n,\tau_n)\ge D_*>0.                \tag{6.1}
\]

For a finite-rank statement, once
`alpha(W_n) D(tau_n)<=D_*/2`, the checked theorem
`half_minimum_le_weightedLedger_of_prefixSurvival_le` gives

\[
                         \Lambda(W_n,\tau_n)\ge D_*/2. \tag{6.2}
\]

So the direct cap-live compiler does not merely lack a declared field on the
current source: its necessary ledger condition is false by a uniform positive
margin in the counterexample chamber.

`nonempty_reachedPositiveCapDefect_of_prefixSurvival_le` and
`QuittingFiniteWordReachedPositiveCapDefect.exists_positiveCoordinateNashDefect`
already extract a reached positive cap-defect row from this ledger.  They do
not choose a quantitative prescribed action, retain a fixed payer over the
whole sequence, or attach the row to a downstream paid consumer.

### Fixed aggregate payer

Decompose the total ledger playerwise as in (1.5).  From (6.2) and `|I|=4`,
some player satisfies

\[
                         \Lambda_k(W_n,\tau_n)\ge D_*/8 \tag{6.3}

at every sufficiently late rank.  Finite pigeonhole yields one fixed player
`k_*` and a strict subsequence on which (6.3) holds.  This is an aggregate
chronological statement; it does not give one row with uniform defect because
the charge may diffuse over increasing word length.

The pair `(positive host h, fixed aggregate payer k_*)`, with the cases
`k_*=h` and `k_*!=h`, is a more faithful next finite label than two hosts.
It records the obstruction that must actually be consumed.

## 7. Mandatory exact outsider regression

Let players be `0,1,2,3`, with host `0`, and define every reward coordinate
to be zero except

\[
                         r_1(\{1,2\})=1.               \tag{7.1}
\]

The original premark root has player `0` Quit surely and all others Continue.
It has

\[
 \alpha=0,\qquad \beta_0=1,
 \qquad \beta_1=\beta_2=\beta_3=0.                    \tag{7.2}
\]

Clear the host to Continue.  At the marked row let player `2` Quit surely
and all others Continue, followed by the all-Continue tail.  The marked
coalition `{2}` has mass one, the host's marked defect is zero, nonhost
behavior is unchanged by the host selection, and the actual postmark tail is
diagonal at zero.

At the marked row the complete suffix cap is zero.  Player `1`'s prescribed
Continue action pays zero, while Quit produces `{1,2}` and pays one.  Hence

\[
 c_{\mathrm{marked},1}=1,
 \qquad A_{\mathrm{marked}}=1,
 \qquad \Lambda_1=1.                                  \tag{7.3}
\]

The terminal tail debt and final joint-survival term are zero, so (2.1)
gives full player-1 debt exactly one.  The example therefore passes all the
host/tail clock tests and fails exactly the ledger test.  Relabeling or
rotating the construction does not change its unit maximum exploitability.

## 8. Proved, checked, and unproved

### Proved here in ordinary mathematics

- The exact playerwise ledger identity (2.1) and cap-diagonal form (2.5).
- The necessary-and-sufficient zero-joint compiler, Corollary 2.2.
- The two-host impossibility (4.1), rotation no-go, and serial ledger formula
  (5.2).
- The fixed aggregate payer consequence (6.3).
- The exact ledger calculation (7.3).

### Existing checked mathematics

- The one-row cap--debt recursion and exact cap--Nash specialization.
- The finite aggregate weighted ledger, append formula, half-minimum lower
  bound, and reached positive-defect extraction.
- Joint/deleted survival append identities in
  `Research/Quitting/CombinedDeletedSurvivalWord.lean`.
- `mul_opponentSurvival_le_jointSurvival_of_ne` in
  `UniformEquilibrium/Quitting/Root/LiteralRootStackSurvival.lean`.
- The actual-Zeno joint-zero and positive-host source fields.

### Not proved

- The fixed aggregate payer produces a single uniformly paid row or action.
- The payer can be attached to the current strategic-singleton/collision
  consumers while retaining the same source chronology.
- A source-faithful second host block can be appended to the first.
- Host/payer case analysis closes either current producer output.

## 9. Next concrete question

Use the already positive aggregate ledger instead of searching for a second
host:

> On the fixed-host actual-Zeno subsequence, freeze a player `k_*` with
> playerwise reached cap-defect ledger at least `D_*/8`.  Prove either that a
> source-supported cap-band/quantile selection converts this diffuse ledger
> into one paid chronological deviation accepted by an existing consumer, or
> that diffusion itself supplies a nonsummable approximate Nash--Bellman
> spine with one fixed label.

The split `k_*=host` versus `k_*!=host` should be retained.  Equation (7.3)
shows why a theorem inspecting only the host defect cannot cover the second
case.

## 10. Sources inspected

- `UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/CapDebtBellmanReduction.lean`.
- `UniformEquilibrium/Diagnostics/Quitting/TerminalCapNashEndpointTransport.lean`.
- `UniformEquilibrium/Diagnostics/Quitting/TerminalCapNashChronology.lean`.
- `UniformEquilibrium/Quitting/Root/LiteralRootStackSurvival.lean`.
- `Research/Quitting/CombinedDeletedSurvivalWord.lean`.
- `Research/Quitting/FiniteWordWeightedCapDefectLedger.lean`.
- `Research/Quitting/FinFourProducerAtlas/ActualZenoDeletedSurvivalSource.lean`.
- `Research/Quitting/FinFourProducerAtlas/ActualZenoHostCompression.lean`.
- `Research/Quitting/FinFourProducerAtlas/FullyScreenedFiniteClockClearing.lean`.
- The frozen companion notes on finite jump--flow words and live diagonal
  completion.
