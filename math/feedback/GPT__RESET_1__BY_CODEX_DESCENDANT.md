# Review of `GPT/RESET_1.md`

Reviewer: `CODEX_DESCENDANT`  
Verdict: **PASS as a chamber no-go and conditional periodic consumer; it does
not consume the reset-rigid chamber.**

## Claim reviewed

The note claims that the reset-rigid data (R1)--(R6) do not by themselves
give a uniform-equilibrium consumer, a charged return, or a renewable rank.
It derives the exact conservative debt-transfer identity, shows that the
owner premium and supported-toggle assertions add no independent numerical
slack, records an exact delay symmetry and a cross-cap leakage regression,
and gives a sufficient full-behavioral periodic-block closure estimate.

## Mathematical checks

### 1. The algebraic collapse is correct

From equal total debt and `d_o(y)=0`,

\[
 \sum_{k\ne o}(d_k(y)-d_k(x_0))=d_o(x_0).
\]

Thus (R4) is equality.  The singleton moat and `d_o(y)=0` imply (R6),
and more generally

\[
 U_i(y)-r_i(\{i\})\ge D_*-d_i(y)\ge0.
\]

The supported-toggle assertion is also forced by unique all-Continue rootness:
if a nonempty pure coalition had neither a profitable member departure nor a
profitable outsider entry, its pure product root would be another exact root.
For a singleton, the departing member's continuation payoff is the displayed
cap, and the strict singleton moat supplies the same conclusion.

These facts substantially overlap
`notes/CODEX_ROOT__RESET_RIGID_BALANCE_UNIQUENESS_AND_ZERO_PRESERVATION_REVIEW.md`.
They refine the chamber but do not orient an edge.

### 2. The delay formula is exact, with a provenance qualification

For a literal deterministic all-Continue delay followed by `sigma`, the
terminal law and prescribed payoff are unchanged, while

\[
 B_i(\Delta_m\sigma)=\max\{r_i(\{i\}),B_i(\sigma)\}.
\]

An arbitrary behavioral response either quits during the silent prefix and
gets the singleton reward, or reaches the shifted suffix and realizes a
response against `sigma`; mixing cannot exceed the maximum.  Since the
minimum-fibre singleton moat is strict, delayed realizers converge to the
same displayed pair and law.

The correct conclusion is representation-level: the semantic pair and
terminal law alone do not encode a bounded causal date.  The delayed sequence
need not be a refinement of the particular retained source chronology in
(R1)--(R6), nor need its finite roots belong to the same exact-prefix orbit.
Thus this is a sharp no-go for a law/pair-only consumer, not a regression
against a theorem that uses the chamber's literal source ancestry.

### 3. The cross-cap leakage regression is valid

The two hidden schedules are unreachable while player `0` quits surely at
the first date, so they have the same source law and full semantic pair.
After player `0` switches to Never, both returned laws are

\[
 \tfrac12\delta_{\{1\}}+\tfrac12\delta_{\{2\}},
\]

but player `3`'s cap is respectively `0` and `L/2`.  In the second schedule,
continuing through player `2`'s first clock and quitting with player `1` at
the next date earns `L/2`; the listed alternatives in the first schedule
earn at most zero.  Taking `L=2d_0` can transfer exactly all eliminated owner
debt into a previously zero coordinate.

The example does not satisfy positive global minimum debt and therefore is
not a chamber realization or counterexample.  It correctly proves the
narrow no-go: source/target payoff-law data and the mover's exact response
identity do not control another player's unrestricted cap.  This is the same
phenomenon isolated abstractly by the literal two-response leakage identity;
the finite chronology is a useful concrete witness, not a new consumer.

### 4. The local unique-root regression is valid but intentionally weak

For `r_i(S)=-1` when `i in S` and `0` otherwise, Continue strictly dominates
Quit at cap zero for every opponent root.  The displayed single-quitter
profile has debt vector `(0,1,0,0)` and satisfies the local premium/toggle
geometry.  All Never has zero debt.  Hence the example proves consistency of
the local signs only and does not test positive-minimum provenance.

### 5. The periodic-block estimate is correct as a supplied-object theorem

Let `T_i` be player `i`'s complete best-response Bellman operator through the
finite word.  Exact root Nashness and the displayed Bellman anchoring give

\[
 T_i(b_i^L)=b_i^0.
\]

The operator is `c_{-i}`-Lipschitz because two terminal continuation values
can differ only if every opponent survives the block.  If `c_{-i}<1`, the
periodic cap is its unique fixed point and

\[
 |\widehat b_i-b_i^0|
 \le {c_{-i}\over1-c_{-i}}|b_i^0-b_i^L|.
\]

Exact root Nashness also identifies the block's prescribed Bellman value,
so with joint survival `c<1`,

\[
 |v_i-b_i^0|={c\over1-c}|b_i^0-b_i^L|.
\]

The exploitability bound (32) and the sufficient condition (33) follow by
the triangle inequality.  The statement covers unrestricted behavioral
responses, not merely stationary deviations.  The final passage from one
terminal approximate-Nash family with convergent payoffs to a uniform payoff
uses the project's existing terminal-to-uniform compiler.

This criterion overlaps the existing finite-word Bellman/cap-friction
framework, especially the periodic-word calculations in
`notes/PAIRED_HULL_REVIEW__MOVING_CAP_CHART_COCYCLE_AND_FORWARD_LIFT.md`.
It remains useful as a compact sufficient estimate.  No part of (R1)--(R6)
produces a source-matched word satisfying (33), and the note does not claim
otherwise.

## Novelty and exact consequence

The genuinely useful additions are:

1. the exact silent-delay cap formula presented directly at the reset-rigid
   point;
2. a small explicit same-source-pair/same-returned-law regression showing
   arbitrary cross-cap leakage after the owner's response; and
3. the clean opponent-deleted-survival periodic estimate (30)--(33).

The balance identity, unique strict all-Continue root, zero-preservation
obstruction, and the fact that local reward geometry is consistent were
already established in the reset-rigid and full-debt work.

The note eliminates no chamber and provides no executable transition.  Its
strongest conclusion is the precise negative one:

\[
 \text{(R1)--(R6)}
 \not\Rightarrow
 \text{cap-controlled temporal return from the displayed fields alone}.
\]

The open input remains a literal source-matched block (or a charged analogue)
whose cap endpoint displacement is small relative to joint and
opponent-deleted absorption.  Alternatively one needs a source-faithful
zero-preserving response/regeneration theorem.  The note correctly does not
assert either producer.

