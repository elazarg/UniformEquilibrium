# Positive-joint live-tail extraction and the cap-live boundary

Author: `CODEX_BLINDSPOT`

Independent reviews:
[CODEX_HAHN](../feedback/CODEX_BLINDSPOT__POSITIVE_SURVIVAL_LIVE_DIAGONAL_TAIL_COMPLETION__BY_CODEX_HAHN.md),
[CODEX_SPINOZA](../feedback/CODEX_BLINDSPOT__POSITIVE_SURVIVAL_LIVE_DIAGONAL_TAIL_COMPLETION__BY_CODEX_SPINOZA.md).

Reviewed source:
[`CODEX_BLINDSPOT__POSITIVE_SURVIVAL_LIVE_DIAGONAL_TAIL_COMPLETION.md`](../notes/CODEX_BLINDSPOT__POSITIVE_SURVIVAL_LIVE_DIAGONAL_TAIL_COMPLETION.md),
SHA-256
`3d1977ca5493e75a51dd1647b4617118db549d029e81fe8bccca3a30fc7f11f7`.

## Exact statement

Fix a finite nonempty player set `I` and a quitting reward table `r` with
`|r_k(S)| <= M`.  For each `n`, let `W_n` be a finite literal product-root
word, let `tau_n` be an actual behavioral tail, and let

\[
 \sigma_n=W_n\star\tau_n,
 \quad \alpha_n=\Pr(W_n\text{ jointly survives}),
 \quad \beta_{n,k}=\Pr(W_n\text{ survives after deleting }k).
\]

All Nash conditions below quantify over complete behavioral deviations,
including Never and arbitrarily late stopping.

### Positive-joint extraction

If `sigma_n` is terminal `epsilon_n`-Nash, `alpha_n>0`, and

\[
                       \epsilon_n/\alpha_n\longrightarrow0,       \tag{1}
\]

then `tau_n` is terminal `(epsilon_n/alpha_n)`-Nash.  Some subsequence of
the actual tail semantic pairs converges to a diagonal point `(y,y)` of the
terminal-semantic carrier, and `y` is a uniform-equilibrium payoff.  In
particular, (1) follows from `epsilon_n->0` and
`alpha_n->alpha_infty>0`.

### Growing-prefix splice

Let `Phi_W` be the finite terminal-semantic prefix map.  For declared tail
vectors `y_n`, define

\[
 Q_n=\Phi_{W_n}(y_n,y_n),\qquad
 z_n=Q_n.1,\qquad
 \delta_{n,k}=Q_n.2_k-Q_n.1_k.                         \tag{2}
\]

Write the actual tail pair as `P_n=(u_n,b_n)`.  If, for every player `k`,

\[
 z_n\to z,\quad \delta_{n,k}\to0,\quad
 \alpha_n|u_{n,k}-y_{n,k}|\to0,\quad
 \beta_{n,k}(b_{n,k}-y_{n,k})_+\to0,                  \tag{3}
\]

then the literal splices `sigma_n` have payoffs converging to `z` and
terminal exploitability tending to zero.  Therefore `z` is a uniform-
equilibrium payoff.

If joint survival has a positive floor, (3) forces the actual tails
themselves to approach a diagonal semantic pair.  If instead joint survival
tends to zero and exactly one player-deleted clock stays live, only that
player's cap seam in (3) survives; all bounded payoff seams and all other
tail-cap seams are erased.  This clock observation does not imply that the
prefix debt `delta` vanishes.

## Conjecture-facing change

This packet closes the semantic question at a genuinely positive-joint Zeno
boundary: positive reach plus vanishing full-profile Nash error already
extracts an actual diagonal tail and is already consumed by checked project
theorems.  It also gives the exact finite-dimensional sufficient conditions
for the reverse growing-prefix splice.

It separates that solved case from the current Fin4 `positiveHost` output.
The latter has zero limiting joint reach and only one positive player-deleted
clock.  Its missing obligations are complete prefix-debt control and the one
surviving host-cap seam.  This narrows the terminal-consumer side of
[`FIN4_TWO_PERSISTENT_EXACT_SPINE_SELECTION.md`](../questions/FIN4_TWO_PERSISTENT_EXACT_SPINE_SELECTION.md)
without claiming that the maintained positive-host packet is consumed.

## Definitions and assumptions

The terminal semantic pair of a behavior profile is `(u,b)`, where `u` is
its prescribed terminal payoff and `b_k` is the supremum payoff available to
player `k` over all unilateral behavioral replacements.  Its playerwise debt
is `b_k-u_k`.

The word `W_n` is literal and uses independent product roots.  Joint survival
`alpha_n` is the probability that every prescribed player Continues through
the word.  Deleted survival `beta_{n,k}` is the probability that all opponents
of `k` Continue; hence `alpha_n<=beta_{n,k}`.

The reference pair `Q_n` in (2) is algebraic and need not be declared
executable.  Its debt `delta` records every root-Nash or mesh defect of the
prefix.  When `W_n` carries an exact Nash--Bellman chain terminating at
`y_n`, exact diagonal prefixing makes `delta=0`.  Finite flow meshes may
instead be covered by an independently proved bound `delta->0`.

## Source correspondence

The exact copy-prefix deviation and payoff identity are in
`UniformEquilibrium/Quitting/Root/LiteralPrefixDeviationTransport.lean`.
The unrestricted-cap contraction used in the splice is the algebra behind
`abs_quittingContinuationBestResponseValue_literalRootStack_sub_le` in
`UniformEquilibrium/Quitting/Root/CommonPrefixCapStability.lean`.
Terminal semantic pairs, their compact carrier, and literal root prefixing
are in `UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`.

The positive-joint conclusion is already checked source-natively:

- `QuittingPositiveJointPrefixReachSource.punishment_nash_of_joint_pos` and
  `punishmentNashError_tendsto_zero` in
  `UniformEquilibrium/Quitting/Classification/Existence/PositiveJointPrefixReachEndpoint.lean`;
- `QuittingPositiveJointPrefixReachPunishmentEndpoint.debt_eq_zero`,
  `payoff_eq_envelope`, and `exists_realizers` in the same file; and
- `QuittingPositiveJointPrefixReachPunishmentEndpoint.isUniformEquilibriumPayoff`
  in `PositiveJointEndpointUniformPayoff.lean`.

The general checked consumer is
`isUniformEquilibriumPayoff_iff_diagonal_mem_terminalSemanticCarrier` in
`UniformPayoffTerminalSemanticCarrier.lean`.

The zero-joint source and host-only fields tested here are in
`Research/Quitting/FinFourProducerAtlas/ActualZenoDeletedSurvivalSource.lean`
and `ActualZenoHostCompression.lean`.

## Proof

For any tail deviation `d` of player `k`, let the corresponding full-profile
deviation copy the prescribed marginal through `W_n` and switch to `d` when
the suffix is reached.  The exact gain identity is

\[
 U_k(\sigma_n[k\leftarrow\operatorname{copy}(W_n,d)])-U_k(\sigma_n)
 =\alpha_n\bigl(U_k(\tau_n[k\leftarrow d])-U_k(\tau_n)\bigr). \tag{4}
\]

Full `epsilon_n`-Nash and division by `alpha_n>0` prove the tail bound.
Compactify the actual tail semantic pairs.  Condition (1) makes every limit
debt nonpositive; carrier membership makes it nonnegative.  The limit is
therefore diagonal, and the checked diagonal-carrier consumer gives a
uniform-equilibrium payoff.

For the reverse splice, changing only the prescribed suffix payoff gives

\[
 |U_k(\sigma_n)-z_{n,k}|
   =\alpha_n|u_{n,k}-y_{n,k}|.                         \tag{5}
\]

One root's cap is the maximum of a tail-independent Quit endpoint and a
Continue endpoint in which the suffix cap has coefficient equal to opponent
survival.  Iterating monotonicity and the one-sided Lipschitz inequality for
`max` yields

\[
 B_k(\sigma_n)-Q_n.2_k
   \le\beta_{n,k}(b_{n,k}-y_{n,k})_+.                  \tag{6}
\]

Subtracting (5) from (6),

\[
 B_k(\sigma_n)-U_k(\sigma_n)
 \le\delta_{n,k}
   +\beta_{n,k}(b_{n,k}-y_{n,k})_+
   +\alpha_n|u_{n,k}-y_{n,k}|.                         \tag{7}
\]

Conditions (3), finiteness of the player set, and fixed-target terminal
acceptance prove the growing-prefix claim.

If `alpha_n>=a>0`, then every `beta_{n,k}>=a`.  Equations (3) force
`u_n-y_n->0`.  Since actual caps satisfy `b_n>=u_n`, the cap condition kills
the positive part of `b_n-y_n` while payoff convergence controls the negative
part.  Thus the actual tail pairs approach the diagonal.

## Boundary tests

- **Exact Nash chain:** if every retained root is exact Nash at its displayed
  successor, `Q_n` is diagonal and `delta=0` exactly.
- **Positive joint reach:** the sharp input is the ratio
  `epsilon_n/alpha_n`, not positivity of reach without a rate.
- **Host-only reach:** if `alpha_n->0`, `beta_{n,h}` has a positive floor,
  and every nonhost deleted clock tends to zero, bounded tail terms leave
  only the host term in (7).  Prefix debt `delta` remains separate.
- **Positive minimum tail:** the current normalized source has checked
  limiting tail-debt sum equal to the retained strictly positive minimum
  under the contrary hypothesis, so its postmark limit is not diagonal.

For the exact Fin4 falsifier, let host be player `0` and set every reward to
zero except

\[
                         r_1(\{1,2\})=1.               \tag{8}
\]

At an original premark root let player `0` Quit surely and all others
Continue.  Then `alpha=0`, `beta_0=1`, and all other deleted survivals are
zero.  In the host-cleared endpoint force player `0` to Continue, let player
`2` Quit surely at the marked row, and use the all-Continue postmark tail.
The marked coalition `{2}` has mass one; the host's marked defect is zero;
the postmark semantic pair is diagonal at zero; and nonhost behavior is
unchanged by selecting the host endpoint.  Nevertheless player `1` gains
exactly one by Quitting at the marked row, producing `{1,2}`.  Thus the
advertised host clock, marked mass, local host defect, and actual diagonal
tail do not imply a terminal consumer.

## Adapter and consumer

For positive-joint extraction, the adapter is an actual literal decomposition
`sigma_n=W_n star tau_n`, a full-profile behavioral Nash error, and the ratio
(1).  Its output is an actual tail sequence with vanishing behavioral Nash
error.  Compactification and the checked diagonal-carrier theorem are the
consumer.

For the reverse direction, the adapter is an actual word/tail sequence plus
the algebraic reference tags `(y_n,Q_n,z_n,delta_n)` and the transmitted
seams in (3).  Equation (7) produces actual terminal approximate Nash
profiles; fixed-target terminal acceptance is the consumer.

The current positive-host packet does not provide this adapter.  In
particular, its arbitrary `newWord` has no complete Nash certificate,
`delta->0` is absent, and the host-cap seam is absent.  This packet does not
fill those fields by assumption.

## Lean handoff

The positive-joint extraction is already checked and should be referenced,
not duplicated.  The narrow new formal target is a finite-word one-sided
semantic splice theorem with conclusion (7).  Reuse:

- `quittingTerminalPayoff_literalRootStackProfile_sub_eq_jointSurvival_mul`;
- `quittingFiniteRootWordCap` and its one-root Lipschitz proof;
- `quittingTerminalSemanticPair_rootThenContinuation`; and
- the existing diagonal-carrier consumer.

Regression tests should include positive joint reach, the exact-Nash
`delta=0` specialization, one surviving deleted clock, and the Fin4 outsider
table (8).  Do not encode current host consumption or arbitrary-game
production as a structure field.

## Scope and nonclaims

This result does not prove that an arbitrary finite quitting game supplies
the growing-prefix tags, that the present positive-host or fully screened
packets have vanishing prefix debt, or that the host-cap seam is controlled.
It proves no regeneration, renewable rank, infinite APS fixed point, or full
conjecture result.
