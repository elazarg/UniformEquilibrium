# Cap-anchored zero-joint ledger and host-rotation boundary

Authors: `CODEX_BLINDSPOT`

Independent reviews:
[CODEX_HAHN](../feedback/CODEX_BLINDSPOT__CAP_LIVE_BOUNDARY_LEDGER_AND_HOST_ROTATION__BY_CODEX_HAHN.md),
[CODEX_SPINOZA](../feedback/CODEX_BLINDSPOT__CAP_LIVE_BOUNDARY_LEDGER_AND_HOST_ROTATION__BY_CODEX_SPINOZA.md)

## Exact statement

Let `I` be a finite nonempty player set, let `r` be a bounded quitting reward
table, let `tau` be an actual terminal behavioral profile, and let

\[
                         W=(x_0,\ldots,x_{L-1})
\]

be a finite word of independent product roots.  Write
`sigma_t=(x_t,...,x_{L-1}) star tau`, with `sigma_L=tau`.  Let

\[
 u_t=U(\sigma_t),\qquad b_t=B(\sigma_t),\qquad
 d_{t,k}=b_{t,k}-u_{t,k},
\]

where `B_k` is player `k`'s complete unilateral behavioral-deviation cap.
Put

\[
 a_t=\Pr_{x_t}(\text{all players Continue}),\qquad
 A_0=1,\qquad A_t=\prod_{s<t}a_s,
\]

and define the complete-suffix cap defect and its reached ledger by

\[
 c_{t,k}=\operatorname{NashDefect}_k(r,b_{t+1},x_t),\qquad
 \Lambda_k(W,\tau)=\sum_{t<L}A_tc_{t,k}.
\]

Then, playerwise,

\[
 d_{0,k}=\Lambda_k(W,\tau)+\alpha(W)d_{L,k},
 \qquad \alpha(W)=A_L.                                \tag{1}
\]

All terms in every `Lambda_k` are nonnegative.  Consequently, for any
sequence `(W_n,tau_n)` with uniformly bounded rewards and
`alpha(W_n) -> 0`, the full profiles `W_n star tau_n` have terminal
exploitability tending to zero if and only if

\[
                         \Lambda_k(W_n,\tau_n)\to0
                         \quad\text{for every }k.      \tag{2}
\]

For a word `W`, define the player-deleted survival clock

\[
 \beta_k(W)=\Pr(W\text{ survives after deleting player }k).
\]

For distinct players `i` and `j`, one has

\[
                         \beta_i(W)\beta_j(W)\le\alpha(W). \tag{3}
\]

Thus at most one deleted clock can have a positive subsequential limit when
joint survival tends to zero.  For finite words `W,V`, the exact append laws
are

\[
 \beta_k(W{+}{+}V)=\beta_k(W)\beta_k(V),               \tag{4}
\]

\[
 \Lambda_k(W{+}{+}V,\tau)
  =\Lambda_k(W,V\star\tau)+\alpha(W)\Lambda_k(V,\tau). \tag{5}
\]

Hence two serial blocks with different unique live deleted clocks can erase
sensitivity to the deepest tail, but cannot erase a nonzero outer ledger.
Rotation of the host label across ranks also cannot average exploitability:
finiteness fixes a host on a subsequence, while (2) requires every ledger
coordinate to vanish on the same profiles.

In the four-player no-uniform-payoff chamber, let `D_*>0` be the global
minimum of total terminal semantic debt, and suppose actual source profiles
decompose as `sigma_n=W_n star tau_n` with `alpha(W_n)->0`.  Then

\[
 \liminf_n\sum_k\Lambda_k(W_n,\tau_n)\ge D_*.
\]

In particular, eventually the total ledger is at least `D_*/2`; on a strict
subsequence there is one fixed player `p` such that

\[
                         \Lambda_p(W_n,\tau_n)\ge D_*/8. \tag{6}
\]

This is a fixed aggregate payer, not a uniformly defective single row.

## Conjecture-facing change

This result narrows the cap-live and host-rotation part of
[`FIN4_TWO_PERSISTENT_EXACT_SPINE_SELECTION`](../questions/FIN4_TWO_PERSISTENT_EXACT_SPINE_SELECTION.md).
A zero-joint cap-live boundary has an exact necessary-and-sufficient compiler
tag: the playerwise reached cap-defect ledger.  Positive player-deleted
survival is not an additional tail-debt seam when the reference continuation
is anchored at the actual suffix cap.

On the current no-uniform-payoff actual-Zeno source, the direct compiler's
necessary condition is false by a uniform positive margin.  Adding or
rotating a second host does not repair it, because concatenation leaves the
outer ledger unscaled.  The remaining source obligation is therefore to
consume the fixed aggregate payer (6): pay, transport, or renew that ledger
along one executable chronology.

## Definitions and assumptions

At every date the prescribed root is a product distribution over each
player's Quit/Continue action.  The profile `tau`, and hence every
`W star tau`, is an actual behavioral profile with perfect observation of
past public actions.  Terminal payoff is the expected reward at the first
nonempty Quit coalition, with the project's convention on nonabsorption.

`U_k(sigma)` is prescribed terminal payoff.  `B_k(sigma)` is the supremum
over all unilateral behavioral deviations of player `k`, including Never and
arbitrarily late stopping; the other players retain their complete strategies.
Thus `d_k=B_k-U_k` is unrestricted terminal deviation debt, not a
finite-controller or pure-time proxy.  No public correlating device and no
independent reselection of continuations is introduced.

The four-player consequence assumes the maintained global-minimum source:
every actual semantic pair has total debt at least `D_*`, the tail debts are
uniformly bounded, and the displayed premark joint survival tends to zero.

## Source correspondence

The one-row form of (1) is
`quittingTerminalSemanticDebt_prefix_eq_continueMass_mul_add_capDefect` in
`UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/CapDebtBellmanReduction.lean`.
The checked aggregate finite-word identity, append law, and finite-rank
minimum lower bound are respectively
`quittingTerminalSemanticDebtSum_literalRootStack_eq_weightedLedger_add`,
`quittingFiniteWordWeightedCapDefectLedger_append`, and
`half_minimum_le_weightedLedger_of_prefixSurvival_le` in
`Research/Quitting/FiniteWordWeightedCapDefectLedger.lean`.

The survival laws are
`quittingLiteralRootStackJointSurvival_append` and
`quittingLiteralRootStackOpponentSurvival_append` in
`Research/Quitting/CombinedDeletedSurvivalWord.lean`, and
`mul_opponentSurvival_le_jointSurvival_of_ne` in
`UniformEquilibrium/Quitting/Root/LiteralRootStackSurvival.lean`.
The zero-ledger specialization is also represented by
`quittingTerminalDeviationDebt_capNashRootStack_eq` and
`quittingTerminalDebtSum_capNashRootStack_eq` in
`UniformEquilibrium/Diagnostics/Quitting/TerminalCapNashChronology.lean`.

The new ordinary-mathematics content is the playerwise cap-anchored
interpretation, the iff boundary (2), the host-rotation/serial-host no-go, and
the fixed-payer extraction.  The complete reviewed source is
[`CODEX_BLINDSPOT__CAP_LIVE_BOUNDARY_LEDGER_AND_HOST_ROTATION`](../notes/CODEX_BLINDSPOT__CAP_LIVE_BOUNDARY_LEDGER_AND_HOST_ROTATION.md).

## Proof

At one root, player `k`'s complete cap is the maximum of its pure Quit and
Continue endpoints, both evaluated at the actual suffix cap `b_{t+1}`.
Insert the prescribed mixture evaluated at the same cap.  The maximum minus
that mixture is exactly `c_{t,k}`.  Replacing the suffix cap in the prescribed
mixture by the actual suffix payoff changes only the all-Continue branch, by
`a_t(b_{t+1,k}-u_{t+1,k})`.  Therefore

\[
                         d_{t,k}=c_{t,k}+a_td_{t+1,k}.
\]

Iteration proves (1).  Equivalently, prefix the diagonal suffix pair
`(b_L,b_L)`: the complete prefixed cap is unchanged, while prescribed payoff
changes by `alpha(W)(u_L-b_L)`.  The remaining cap-diagonal debt is precisely
the ledger.

When `alpha(W_n)->0`, bounded rewards uniformly bound every tail debt.  If all
ledgers vanish, (1) makes all full debts vanish.  Conversely,
`0<=Lambda_k<=d_{0,k}` by (1), so vanishing full exploitability forces every
ledger coordinate to vanish.  This proves (2).  Compactness of the bounded
payoff cube gives a fixed limiting payoff on a subsequence.

For (3), expand both deleted clocks into per-date Continue factors.  Every
factor appearing in joint survival occurs at least as often in
`beta_i beta_j`; the extra product consists of Continue probabilities and is
at most one.  Thus `beta_i beta_j<=alpha`.  This forbids two positive deleted
clock limits.  Direct factorization proves (4).

Split the chronological sum defining the ledger of `W++V` at the join.
Every inner reached weight contains the full outer joint-survival factor,
whereas every outer term is unchanged.  This proves (5), and nonnegativity
shows that no inner block can cancel an outer ledger.

Finally, sum (1) over the four players.  Global minimality gives
`D(sigma_n)>=D_*`; bounded tail debt and `alpha_n->0` make the transported tail
term at most `D_*/2` eventually.  Hence the total ledger is at least `D_*/2`.
At every such rank one of four players pays at least `D_*/8`; finite
pigeonhole fixes that player on a strict subsequence, proving (6).

## Boundary tests

Positive test: if every row is exact Nash against the complete cap of its
actual suffix, then every `c_{t,k}=0`, so (1) reduces to
`d_{0,k}=alpha(W)d_{L,k}`.  Any such word sequence with joint survival tending
to zero is a terminal approximate-Nash compiler even when its tails have
positive debt.

Negative two-profile regression: take players `0,1,2,3`, call player `0` the
host, and set every reward coordinate to zero except

\[
                         r_1(\{1,2\})=1.
\]

On the **original premark word**, player `0` Quits surely and all other
players Continue.  Then `alpha=0`, `beta_0=1`, and
`beta_1=beta_2=beta_3=0`.

On a **separate host-cleared endpoint word**, player `0` instead Continues;
at the marked row player `2` Quits surely, all others Continue, and the tail
is all-Continue.  Against the zero suffix cap, player `1` gets zero by its
prescribed Continue and one by joining player `2`.  Hence the reached marked
defect and ledger satisfy

\[
                         c_{\mathrm{marked},1}=\Lambda_1=1.
\]

These are two different profiles.  The example does not assert that one
unchanged word simultaneously has `beta_0=1` and `Lambda_1=1`.  It shows that
the maintained two-profile host/tail fields do not control the endpoint
ledger.

## Adapter and consumer

Adapter: any literal finite root word followed by its actual complete
behavioral suffix supplies `(a_t,A_t,c_{t,k})` directly; no semantic pair is
independently chosen.  The maintained actual-Zeno premark decomposition is
such an adapter, and it supplies the positive ledger conclusion (6).

Consumer: if this adapter additionally supplies vanishing playerwise ledgers,
(2) produces terminal approximate Nash profiles against unrestricted
behavioral deviations.  The checked terminal-to-uniform selection is
`quittingGame_exists_uniformEquilibriumPayoff_of_terminalNash_all_errors` in
`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`.

Explicit nonconsumer: the current no-uniform-payoff actual-Zeno source has a
ledger bounded away from zero, so it does **not** enter that consumer.  The
fixed payer (6) is a narrowed source obligation, not a paid chronological
edge, a restart, or a uniform-equilibrium construction.

## Lean handoff

Formalize only the new playerwise wrapper and boundary statements around the
existing checked recursions:

- a playerwise finite-word reached-cap-defect ledger and its exact telescope;
- the `alpha_n -> 0` iff between maximal terminal debt and coordinatewise
  ledger convergence, using the existing uniform reward bound;
- the playerwise append formula and the two-positive-deleted-clock
  impossibility;
- the Fin4 fixed-payer subsequence corollary from the existing aggregate
  half-minimum theorem; and
- the two distinct profile computations in the regression.

Do not encode vanishing ledger, source renewal, or a consumer attachment as a
structure field.  Reuse the complete behavioral cap and terminal semantic
debt already present in the named files.

## Scope and nonclaims

This packet does not prove the finite-quitting uniform-equilibrium conjecture.
It does not convert the fixed aggregate payer into one uniformly defective
row, preserve a paid deviation through the host interface, attach an inner
block to an actual successor, or construct a renewable chronology.  Deleted
survival remains useful for measuring suffix-cap sensitivity; the theorem
only says that it is not the tail coefficient in the cap-anchored debt
telescope.  The result concerns terminal behavioral exploitability and its
checked terminal-to-uniform consumer, not discounted equilibrium or a
bounded-controller approximation.
